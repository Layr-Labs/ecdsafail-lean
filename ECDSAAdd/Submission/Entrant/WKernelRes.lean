import ECDSAAdd.Submission.Entrant.WKernel
import ECDSAAdd.Arithmetic.MappedKernelPhysical
import ECDSAAdd.Baselines.SlotCompressed

/-! Support, physicality and syntax-slot bounds of the narrowed kernel; copies
of `MappedCompressedStageSupport`, `CompactWalkPhysical`, `MappedKernelPhysical`,
`SlotSignedInteger`, `SlotCodec` and `SlotCompressed` over the new passes. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.W
open ECDSAAdd.Arithmetic Secp256k1 MappedCompressed CompressedAllocation RecordedQuantum

section Support
attribute [local irreducible] wires compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
  NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse

private theorem base_integer_mem (q : Nat) (h : q < 515 ∨ (770 ≤ q ∧ q < 1798)) :
    base q∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold omitted; omega

private theorem tick_layout_support (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout base i).wires.toFinset⊆slots.toFinset := by
  have width := compactSkywalkTick_width_bounds i hi
  have view : (compactSkywalkTickLayout base i).wires =
      ([skywalkPoolPreviousId i,1028+i,i+compactSkywalkTickPreWidth i,i,770]++
      List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
      List.range' 771 (compactSkywalkTickPreWidth i-1)++
      List.range' 1540 (compactSkywalkTickPreWidth i-1)).map base := by
    change base (skywalkPoolPreviousId i)::base (1028+i)::
      base (i+compactSkywalkTickPreWidth i)::base i::base 770::
      ((compactSkywalkTickLayout base i).ah++(compactSkywalkTickLayout base i).bh++
      wireBlock base 1540 (compactSkywalkTickPreWidth i-1)) = _
    rw [compactSkywalkTick_ah base i hi,compactSkywalkTick_bh base i hi]
    simp [wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [List.mem_toFinset,view] at hq
  obtain ⟨old,h,rfl⟩ := List.mem_map.mp hq
  apply base_integer_mem
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  by_cases hz : i=0
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; omega

theorem ticks_support (i : Nat) (hi : i < 512) :
    wires (compactSkywalkTick base i)⊆slots.toFinset ∧
    wires (compactSkywalkReverseTick base i)⊆slots.toFinset :=
  ⟨(compactSkywalkTick_support base i hi base_pool_nodup).trans (tick_layout_support i hi),
   (compactSkywalkReverseTick_support base i hi base_pool_nodup).trans (tick_layout_support i hi)⟩

private theorem base_codec_support (start : Nat) (hs : start+3 ≤ 512) :
    wires (compressedHistoryEncode base start)⊆slots.toFinset ∧
    wires (compressedHistoryDecode base start)⊆slots.toFinset := by
  have lift (P : Program) (he : P=compressedHistoryEncode base start ∨
      P=compressedHistoryDecode base start) : wires P⊆slots.toFinset := by
    intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above start hs P he q hq
    have region := compressedHistoryId_region start hs u
    apply base_integer_mem
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

private theorem delayed_codec_support (i : Nat) (hi : i < 512) :
    wires (compressedPackAfter base i)⊆slots.toFinset ∧
    wires (compressedDecodeBefore base i)⊆slots.toFinset := by
  cases h : compressedPackDue i
  · simp [compressedPackAfter,compressedDecodeBefore,h,wires]
  · have due := compressedPackDue_true i h
    have support := base_codec_support (i-3) (by omega)
    simpa only [compressedPackAfter,compressedDecodeBefore,h,if_true] using support

theorem integer_support (i n : Nat) (h : i+n ≤ 512) :
    wires (compressedCompactForward base i n)⊆slots.toFinset ∧
    wires (compressedCompactReverse base i n)⊆slots.toFinset := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,compressedCompactReverse,wires]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := ticks_support i (by omega)
    have codec := delayed_codec_support i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,wires_append,
      Finset.union_subset_iff,and_assoc]
    exact ⟨tick.1,codec.1,rest.1,rest.2,codec.2,tick.2⟩

private theorem native_prefix_slots :
    (NativeFirstDirect.prefixSites base).toFinset⊆slots.toFinset := by
  intro q hq
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      apply slot_mem
      · unfold live; omega
      · unfold omitted; omega
    | apply slot_mem
      · unfold live; omega
      · unfold omitted; omega

theorem kernel_support (divide : Bool) : wires (kernel divide)⊆slots.toFinset := by
  have native := NativeFirstDirect.prefix_support base
  have integer := integer_support 1 511 (by omega)
  simp only [kernel,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨native.1.trans native_prefix_slots,integer.1,clear_support,
    LaneA.laneSegment_support divide,clear_support,integer.2,
    (NativeFirstKnown.inverse_support base).trans native_prefix_slots⟩

private theorem zero_sites :
    (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255)).toFinset⊆slots.toFinset := by
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,wireBlock,
    List.mem_map,List.mem_range'_1] at hq
  rcases hq with rfl|rfl|(h|h)
  · exact slot_mem 2411 (by unfold live; omega) (by unfold omitted; omega)
  · exact slot_mem 2313 (by unfold live; omega) (by unfold omitted; omega)
  all_goals obtain ⟨old,ho,rfl⟩ := h; apply base_integer_mem; omega

theorem controlled_support (divide : Bool) : wires (controlled divide)⊆slots.toFinset := by
  have z := (directZeroDivisor_wires (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411)).trans zero_sites
  rw [wires_append,Finset.union_subset_iff] at z
  simp only [controlled,directZeroControlled,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨z.1,kernel_support divide,z.2⟩

end Support

section Physical

theorem compactTicks_physical (w : Nat → Wire) (i : Nat) (hi : i<512)
    (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (compactSkywalkTick w i) ∧ GatePhysical (compactSkywalkReverseTick w i) := by
  have bounds := compactSkywalkTick_width_bounds i hi
  have n := narrowTicks_physical (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)
    (compactSkywalkTick_valid w i hi hn) (by omega)
    (by rw [compactSkywalkTick_half w i hi,wireBlock_length]; omega)
  have val := compactSkywalkTick_release_valid w i hi hn
  have a := compactSigns_physical (compactSkywalkTickARelease w i) val.1
  have b := compactSigns_physical (compactSkywalkTickBRelease w i) val.2
  simp only [compactSkywalkTick,compactSkywalkTickCleanup,compactSkywalkReverseTick,
    compactSkywalkReverseExpand,gatePhysical_append]
  exact ⟨⟨n.1,a.1,b.1⟩,⟨⟨b.2,a.2⟩,n.2⟩⟩

theorem compressedLoops_physical (w : Nat → Wire) (i n : Nat) (hi : i+n≤512)
    (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (compressedCompactForward w i n) ∧ GatePhysical (compressedCompactReverse w i n) := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,compressedCompactReverse,GatePhysical]
  | succ n ih =>
    have tick := compactTicks_physical w i (by omega) hn
    have tail := ih (i+1) (by omega)
    have codec := transcriptCodec_physical (compressedHistoryMap w (i-3))
    have pack : GatePhysical (compressedPackAfter w i) := by
      unfold compressedPackAfter
      split
      · exact codec.1
      · simp [GatePhysical]
    have unpack : GatePhysical (compressedDecodeBefore w i) := by
      unfold compressedDecodeBefore
      split
      · exact codec.2
      · simp [GatePhysical]
    simp only [compressedCompactForward,compressedCompactReverse,gatePhysical_append]
    exact ⟨⟨⟨tick.1,pack⟩,tail.1⟩,⟨⟨tail.2,unpack⟩,tick.2⟩⟩

theorem kernel_physical (divide : Bool) : GatePhysical (kernel divide) := by
  have first := (NativeFirstDirect.programs_physical base base_pool_nodup).1
  have loops := compressedLoops_physical base 1 511 (by decide) base_pool_nodup
  have last := NativeFirstKnown.inverse_physical base base_pool_nodup
  have field := LaneA.laneSegment_physical divide
  simp only [kernel,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨first,loops.1⟩,mappedClear_physical⟩,field⟩,mappedClear_physical⟩,loops.2⟩,last⟩

theorem controlled_physical (divide : Bool) : GatePhysical (controlled divide) := by
  apply directZero_physical _ _ _ _ _ _ (kernel_physical divide)
  decide +kernel

end Physical

section Slots
open Challenge Baselines
attribute [local irreducible] renameProgram NativeFirstDirect.forward NativeFirstKnown.inverse
  compressedCompactForward compressedCompactReverse LaneA.laneSegment
  kernel ZeroSeededConstantCompare.program maskedConstant

theorem compactTick_gateSlots_le (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    gateSlots (compactSkywalkTick w i) ≤ 6000 ∧
    gateSlots (compactSkywalkReverseTick w i) ≤ 6000 := by
  have h := narrowTick_gateSlots_le (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)
  have hb := compactSkywalkTick_width_bounds i hi
  rw [compactSkywalkTick_ah w i hi, compactSkywalkTick_half w i hi,
    compactSkywalkTick_b w i hi, wireBlock_length, wireBlock_length, wireBlock_length] at h
  have hc : gateSlots (compactSkywalkTickCleanup w i) ≤ 516 := by
    simp only [compactSkywalkTickCleanup,compactSkywalkTickARelease,compactSkywalkTickBRelease,
      compactSkywalkSignRelease,compactSkywalkSignWord,gateSlots_append,signComplement_gateSlots,
      List.length_drop,compactSkywalkTick_half w i hi,compactSkywalkTick_b w i hi,wireBlock_length]
    omega
  have he : gateSlots (compactSkywalkReverseExpand w i) = gateSlots (compactSkywalkTickCleanup w i) := by
    simp only [compactSkywalkReverseExpand,compactSkywalkTickCleanup,compactSkywalkSignExpand,
      compactSkywalkSignRelease,gateSlots_append,signComplement_gateSlots]; omega
  simp only [compactSkywalkTick,compactSkywalkReverseTick,gateSlots_append]
  omega

theorem compactLoops_gateSlots_le (w : Nat → Wire) (i n : Nat) (hn : i+n ≤ 512) :
    gateSlots (compressedCompactForward w i n) ≤ n*6200 ∧
    gateSlots (compressedCompactReverse w i n) ≤ n*6200 := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse,
      gateSlots_nil,Nat.zero_mul,Nat.le_refl,and_self]
  | succ n ih =>
    have h := compactTick_gateSlots_le w i (by omega)
    have hc := scheduledCodec_gateSlots_le w i
    have ht := ih (i+1) (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,gateSlots_append,
      Nat.succ_mul]
    omega

theorem kernel_gateSlots_le (divide : Bool) :
    gateSlots (kernel divide) ≤ 20500000 := by
  have hn := nativeFirst_gateSlots_le MappedCompressed.base
  have hi := compactLoops_gateSlots_le MappedCompressed.base 1 511 (by omega)
  have hf := LaneA.laneSegment_gateSlots_le divide
  have hc : gateSlots (skywalkArithmeticClear MappedCompressed.base) = 3 := rfl
  rw [kernel]
  simp only [gateSlots_append, hc]
  omega

theorem controlled_gateSlots_le (divide : Bool) :
    gateSlots (controlled divide) ≤ 20600000 := by
  have hk := kernel_gateSlots_le divide
  have hz := zeroCompare_gateSlots_le (wireBlock MappedCompressed.base 770 256)
    (wireBlock MappedCompressed.base 0 255) (MappedCompressed.base 2313) (MappedCompressed.base 2411)
  have hm := maskedConstant_gateSlots_le (MappedCompressed.base 2411) (wireBlock MappedCompressed.base 770 256) 1
  simp only [wireBlock_length] at hz hm
  simp only [controlled,directZeroControlled,directZeroDivisorEnter,directZeroDivisorLeave,
    gateSlots_append]; omega

end Slots

end ECDSAAdd.Entrant.W
