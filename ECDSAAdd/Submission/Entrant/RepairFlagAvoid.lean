import ECDSAAdd.Submission.Entrant.FlagMerge

/-! The bare kernel does not use the old control-repair flag. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed MappedCompressed.LaneA CompressedAllocation Secp256k1
open ControlledPointLayout CompressedPointDialog
attribute [local irreducible] wires OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
  compressedHistoryEncode compressedHistoryDecode compactSkywalkTick compactSkywalkReverseTick
  NativeFirstDirect.forward NativeFirstKnown.inverse PenultimateMapped.replay laneKernel

def repairFlag_badIdx (q : Nat) : Prop := q=2411
def repairFlag_goodW (q : Wire) : Prop := q≠base 2411
def repairFlag_Avoid (P : Program) : Prop := ∀q∈wires P,repairFlag_goodW q

theorem repairFlag_avoid_append {P Q : Program} : repairFlag_Avoid (P ++ Q) ↔ repairFlag_Avoid P ∧ repairFlag_Avoid Q := by
  simp only [repairFlag_Avoid, wires_append, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · intro h q hq; rcases hq with hq | hq
    · exact h.1 q hq
    · exact h.2 q hq

theorem repairFlag_avoid_sub {P Q : Program} (h : wires P ⊆ wires Q) (hq : repairFlag_Avoid Q) : repairFlag_Avoid P :=
  fun q hp => hq q (h hp)

theorem repairFlag_avoid_nil : repairFlag_Avoid [] := by intro q hq; simp [wires] at hq

theorem repairFlag_base_good (q : Nat) (h : ¬ repairFlag_badIdx q) : repairFlag_goodW (base q) := by
  show q+16 ≠ 2411+16
  unfold repairFlag_badIdx at h; omega

theorem repairFlag_bad_not_zero (q : Nat) (h : repairFlag_badIdx q) : ¬ zeroRegion q := by
  unfold repairFlag_badIdx at h; unfold zeroRegion workRegion holeRegion; omega

theorem repairFlag_pi0_good (q : Nat) (h : ¬ repairFlag_badIdx q) : ¬ repairFlag_badIdx (pi0 q) := by
  intro hb
  have fix := pi0_outside (pi0 q) (repairFlag_bad_not_zero _ hb)
  have := pi0.injective fix
  exact h (this ▸ hb)

theorem repairFlag_pi_good (j q : Nat) (hj : j < 170) (h : ¬ repairFlag_badIdx q) : ¬ repairFlag_badIdx (pi j q) := by
  intro hb
  have fix := pi_outside j (pi j q) hj (repairFlag_bad_not_zero _ hb)
  have := (pi j).injective fix
  exact h (this ▸ hb)

theorem repairFlag_allPlaced_good (q : Nat) (h : ¬ repairFlag_badIdx q) : repairFlag_goodW (allPlaced q) :=
  repairFlag_base_good _ (repairFlag_pi0_good q h)

theorem repairFlag_placed_good (j q : Nat) (hj : j < 170) (h : ¬ repairFlag_badIdx q) : repairFlag_goodW (placed j q) :=
  repairFlag_base_good _ (repairFlag_pi_good j q hj h)

theorem repairFlag_shared_not_bad (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : ¬ repairFlag_badIdx q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold repairFlag_badIdx
  omega

theorem repairFlag_packet_not_bad (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : ¬ repairFlag_badIdx q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold repairFlag_badIdx; unfold H at h
  omega

theorem repairFlag_inventory_not_bad (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) : ¬ repairFlag_badIdx q := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact repairFlag_shared_not_bad q h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    unfold repairFlag_badIdx; omega
  · exact repairFlag_packet_not_bad j q hj h

/-! Field side. -/

theorem repairFlag_cell_avoid (divide : Bool) (j i : Nat) (hj : j < 170)
    (hi0 : 3*j ≤ i) (hi : i < 3*j+3) :
    repairFlag_Avoid (renameProgram (placed j) (logicalCell divide i)) := by
  have g : i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have s : 1028+i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    unfold H
    omega
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 (groupInventory j).toFinset
    (by intro q hq; simp only [groupInventory,List.mem_toFinset,List.mem_append];
        exact Or.inl (Or.inl (List.mem_toFinset.mp hq)))
    (by simp [groupInventory]) (by simp [groupInventory,g])
    (by simp [groupInventory,s]) (by simp [groupInventory])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈groupInventory j := by
    cases divide
    · exact List.mem_toFinset.mp (body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw))
    · exact List.mem_toFinset.mp (body.1 (by simpa only [logicalCell,if_true] using hraw))
  exact repairFlag_placed_good j old hj (repairFlag_inventory_not_bad j old hj belongs)

theorem repairFlag_codec_avoid (j : Nat) (hj : j < 170) :
    repairFlag_Avoid (compressedHistoryEncode (placed j) (3*j)) ∧
    repairFlag_Avoid (compressedHistoryDecode (placed j) (3*j)) := by
  constructor
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inl rfl) q hq
    exact repairFlag_placed_good j _ hj (repairFlag_packet_not_bad j _ hj (history_packet j u))
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inr rfl) q hq
    exact repairFlag_placed_good j _ hj (repairFlag_packet_not_bad j _ hj (history_packet j u))

theorem repairFlag_group_avoid (divide : Bool) (j : Nat) (hj : j < 170) : repairFlag_Avoid (mappedGroup divide j) := by
  have codec := repairFlag_codec_avoid j hj
  have a := repairFlag_cell_avoid divide j (3*j) hj (by omega) (by omega)
  have b := repairFlag_cell_avoid divide j (3*j+1) hj (by omega) (by omega)
  have c := repairFlag_cell_avoid divide j (3*j+2) hj (by omega) (by omega)
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,repairFlag_avoid_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem repairFlag_groups_avoid (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    repairFlag_Avoid (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp only [mappedGroups]; exact repairFlag_avoid_nil
  | succ n ih =>
    have current := repairFlag_group_avoid divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,repairFlag_avoid_append]
    · exact ⟨rest,current⟩
    · exact ⟨current,rest⟩

theorem repairFlag_tail_avoid (divide : Bool) (i : Nat) (hi : i=510 ∨ i=511) :
    repairFlag_Avoid (renameProgram allPlaced (logicalCell divide i)) := by
  let W := (CompressedFieldSupport.sharedSites id 2409++[2400,2410,i,1028+i]).toFinset
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 W
    (by intro q hq; simp only [W,List.mem_toFinset,List.mem_append]; exact Or.inl (List.mem_toFinset.mp hq))
    (by simp [W]) (by simp [W]) (by simp [W]) (by simp [W])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈W := by
    cases divide
    · exact body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw)
    · exact body.1 (by simpa only [logicalCell,if_true] using hraw)
  simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,or_assoc] at belongs
  apply repairFlag_allPlaced_good
  rcases belongs with h|rfl|rfl|rfl|rfl
  · exact repairFlag_shared_not_bad old h
  all_goals unfold repairFlag_badIdx; omega

theorem repairFlag_mappedReplay_avoid (divide : Bool) : repairFlag_Avoid (mappedReplay divide) := by
  have groups := repairFlag_groups_avoid divide 0 170 (by omega)
  have a := repairFlag_tail_avoid divide 510 (by omega)
  have b := repairFlag_tail_avoid divide 511 (by omega)
  cases divide <;> simp only [mappedReplay,Bool.false_eq_true,if_false,if_true,repairFlag_avoid_append]
  · exact ⟨⟨b,a⟩,groups⟩
  · exact ⟨⟨groups,a⟩,b⟩

theorem repairFlag_integer_good (q : Nat) (h : q < 1798) (_h' : q ≠ 769) : repairFlag_goodW (base q) := by
  apply repairFlag_base_good; unfold repairFlag_badIdx; omega

theorem repairFlag_tick_layout_avoid (i : Nat) (hi : i < 512) :
    ∀ q ∈ (compactSkywalkTickLayout base i).wires.toFinset, repairFlag_goodW q := by
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
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  by_cases hz : i=0
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; exact repairFlag_integer_good _ (by omega) (by omega)
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; exact repairFlag_integer_good _ (by omega) (by omega)

theorem repairFlag_ticks_avoid (i : Nat) (hi : i < 512) :
    repairFlag_Avoid (compactSkywalkTick base i) ∧ repairFlag_Avoid (compactSkywalkReverseTick base i) :=
  ⟨fun q hq => repairFlag_tick_layout_avoid i hi q (compactSkywalkTick_support base i hi base_pool_nodup hq),
   fun q hq => repairFlag_tick_layout_avoid i hi q (compactSkywalkReverseTick_support base i hi base_pool_nodup hq)⟩

theorem repairFlag_base_codec_avoid (start : Nat) (hs : start+3 ≤ 512) :
    repairFlag_Avoid (compressedHistoryEncode base start) ∧ repairFlag_Avoid (compressedHistoryDecode base start) := by
  have lift (P : Program) (he : P=compressedHistoryEncode base start ∨
      P=compressedHistoryDecode base start) : repairFlag_Avoid P := by
    intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above start hs P he q hq
    have region := compressedHistoryId_region start hs u
    exact repairFlag_integer_good _ (by omega) (by omega)
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem repairFlag_delayed_codec_avoid (i : Nat) (hi : i < 512) :
    repairFlag_Avoid (compressedPackAfter base i) ∧ repairFlag_Avoid (compressedDecodeBefore base i) := by
  cases h : compressedPackDue i
  · simp only [compressedPackAfter,compressedDecodeBefore,h,Bool.false_eq_true,if_false]
    exact ⟨repairFlag_avoid_nil, repairFlag_avoid_nil⟩
  · have due := compressedPackDue_true i h
    have support := repairFlag_base_codec_avoid (i-3) (by omega)
    simpa only [compressedPackAfter,compressedDecodeBefore,h,if_true] using support

theorem repairFlag_integer_avoid (i n : Nat) (h : i+n ≤ 512) :
    repairFlag_Avoid (compressedCompactForward base i n) ∧ repairFlag_Avoid (compressedCompactReverse base i n) := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse]; exact ⟨repairFlag_avoid_nil, repairFlag_avoid_nil⟩
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := repairFlag_ticks_avoid i (by omega)
    have codec := repairFlag_delayed_codec_avoid i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,repairFlag_avoid_append]
    exact ⟨⟨⟨tick.1,codec.1⟩,rest.1⟩,⟨⟨rest.2,codec.2⟩,tick.2⟩⟩

theorem repairFlag_prefixSites_avoid : ∀ q ∈ (NativeFirstDirect.prefixSites base).toFinset, repairFlag_goodW q := by
  intro q hq
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      exact repairFlag_integer_good _ (by omega) (by omega)
    | exact repairFlag_integer_good _ (by omega) (by omega)

theorem repairFlag_clear_avoid : repairFlag_Avoid (skywalkArithmeticClear base) := by
  intro q hq
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact repairFlag_integer_good _ (by omega) (by omega)


theorem repairFlag_target : repairFlag_Avoid centTarget ∧ repairFlag_Avoid canonTarget := by
  have s := BalancedConvert.LaneA.fast_support (balancedSharedTargetConvert base)
  have good : ∀ q∈(balancedSharedTargetConvert base).wires,repairFlag_goodW q := by
    intro q hq
    simp only [balancedSharedTargetConvert,BalancedConvert.Layout.wires,wireBlock,List.mem_append,
      List.mem_cons,List.mem_map,List.mem_range'_1,List.not_mem_nil,or_false,List.cons_append,
      List.nil_append] at hq
    rcases hq with h|h|h|h|h|h
    all_goals first
      | (subst h; apply repairFlag_base_good; unfold repairFlag_badIdx; omega)
      | (obtain ⟨i,hi,rfl⟩ := h; apply repairFlag_base_good; unfold repairFlag_badIdx; omega)
  exact ⟨fun q hq => good q (List.mem_toFinset.mp (s.1 hq)),
    fun q hq => good q (List.mem_toFinset.mp (s.2 hq))⟩

theorem repairFlag_copy : repairFlag_Avoid copyPair256 := by
  intro q hq
  have h := copyRegister_wires_subset none (wireBlock base 2056 256) (wireBlock base 770 256) hq
  simp only [List.mem_toFinset,Option.toList_none,List.nil_append,List.mem_append,wireBlock,
    List.mem_map,List.mem_range'_1] at h
  rcases h with ⟨i,hi,rfl⟩|⟨i,hi,rfl⟩
  all_goals apply repairFlag_base_good; unfold repairFlag_badIdx; omega

theorem repairFlag_replay (divide : Bool) : repairFlag_Avoid (PenultimateMapped.replay divide) :=
  repairFlag_avoid_sub ((PenultimateMapped.replay_support_sub divide).trans
    ((EntryMappedFieldSegmentTrim.terminalReplay_support_sub divide).trans
      (EntryMappedFieldSegmentTrim.replay_support_sub divide))) (repairFlag_mappedReplay_avoid divide)

theorem laneSegment_no_repairFlag (divide : Bool) : repairFlag_Avoid (laneSegment divide) := by
  have t := repairFlag_target
  cases divide <;> simp only [laneSegment,mulSeg,divSeg,Bool.false_eq_true,if_false,if_true,repairFlag_avoid_append]
  · exact ⟨⟨⟨t.1,repairFlag_copy⟩,repairFlag_replay false⟩,t.2⟩
  · exact ⟨t.1,⟨repairFlag_replay true,repairFlag_copy⟩,t.2⟩

theorem laneKernel_no_repairFlag (divide : Bool) : repairFlag_Avoid (laneKernel divide) := by
  have native := NativeFirstDirect.prefix_support base
  have integer := repairFlag_integer_avoid 1 511 (by omega)
  have known := NativeFirstKnown.inverse_support base
  simp only [laneKernel,repairFlag_avoid_append]
  exact ⟨⟨⟨⟨⟨⟨fun q hq => repairFlag_prefixSites_avoid q (native.1 hq),integer.1⟩,
    repairFlag_clear_avoid⟩,laneSegment_no_repairFlag divide⟩,repairFlag_clear_avoid⟩,integer.2⟩,
    fun q hq => repairFlag_prefixSites_avoid q (known hq)⟩

theorem laneKernel_repairFlag_unused (divide : Bool) : base 2411∉wires (laneKernel divide) :=
  fun h => laneKernel_no_repairFlag divide _ h rfl

section Physical
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem arith3_pool1804_unused (multiply : Bool) : L.core.poolWire 1804∉wires (arith3 L multiply) := by
  intro hq
  rw [arith3,renameProgram_support] at hq
  obtain ⟨old,used,e⟩ := Finset.mem_image.mp hq
  have hs := laneKernel_support (!multiply) used
  have slot : base 2411∈slots.toFinset := by
    apply slot_mem <;> simp [live,CompressedAllocation.omitted]
  have image : pointWireFn L (base 2411)=L.core.poolWire 1804 := by
    rw [pointWireFn_base]
    simp [pointIndexWire,pointMeta,skywalkDirectZero]
  have same := pointWireFn_injective_slots L hw hn _ (swap2_slots old hs) _ slot (e.trans image.symm)
  have original : old=base 2411 := by
    rw [←swap2_involutive old,same,swap2_fix _ (by decide) (by decide)]
  exact laneKernel_repairFlag_unused (!multiply) (original ▸ used)

end Physical


section Pool
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

private theorem idle_pool : L.core.poolWire 1804∈L.dialogPool := by
  apply List.mem_of_mem_take (i:=2613)
  rw [pool_block L hw 2613 (le_refl _)]
  exact List.mem_map.mpr ⟨1804,by simp [List.mem_range'_1],rfl⟩

private theorem idle_resident : L.core.poolWire 1804∉CompressedPointSquare.residents L := by
  have dis := (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  exact fun h => List.disjoint_left.mp dis h (idle_pool L hw hn)

private theorem idle_prefix (n : Nat) (h : n≤1804) :
    L.core.poolWire 1804∉L.dialogPool.take n := by
  rw [pool_block L hw n (by omega)]
  intro hq
  obtain ⟨i,hi,e⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have same := pool_inj L hw hn i 1804 (by omega) (by omega) e
  omega

private theorem idle_point : L.core.poolWire 1804∉PointAddLayout.pointWires L.point :=
  fun h => idle_resident L hw hn (by simp [CompressedPointSquare.residents,h])

private theorem idle_control : L.core.poolWire 1804≠L.control :=
  fun h => idle_resident L hw hn (by simp [CompressedPointSquare.residents,h])

private theorem idle_flag (q : Wire) (h : q∈L.inPlaceFlags) : L.core.poolWire 1804≠q :=
  fun e => idle_resident L hw hn (by simp [CompressedPointSquare.residents,e,h])

private theorem idle_generic : L.core.poolWire 1804≠L.core.generic :=
  idle_flag L hw hn _ (by simp [inPlaceFlags])

private theorem const_no_idle (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    L.core.poolWire 1804∉(L.core.generic::(L.recoveryConstant r).wires).toFinset := by
  intro h
  have pool := L.recoveryConstant_pool hw r
  have inpool (q : Wire) (hq : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ hq
  have h' := List.mem_toFinset.mp h
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at h'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at h'
  rcases h' with h | (((h | h) | h) | h | h | h)
  · exact idle_generic L hw hn h
  · exact idle_prefix L hw hn 515 (by omega) (inpool _ (by simp [h]))
  · apply idle_point L hw hn
    rcases hr with rfl|rfl <;> simp [PointAddLayout.pointWires,h]
  all_goals exact idle_prefix L hw hn 515 (by omega) (inpool _ (by simp [h]))

private theorem farith_no_idle (multiply : Bool) :
    L.core.poolWire 1804∉wires (farith L multiply) := by
  have point := idle_point L hw hn
  have fin : L.core.poolWire 1804≠L.point.finite := fun h => point (by simp [PointAddLayout.pointWires,h])
  have x : L.core.poolWire 1804≠x0 L := fun h => point (by
    rw [h]; simp only [PointAddLayout.pointWires,List.mem_cons,List.mem_append]
    exact Or.inl (Or.inr (x0_mem L hw)))
  have pf : L.core.poolWire 1804∉wires (pfix L) := by
    simp [pfix,wires,Instr.wires,fin,x]
  simpa only [farith,wires_append,Finset.mem_union,not_or] using
    And.intro pf (And.intro (arith3_pool1804_unused L hw hn multiply) pf)

private theorem candidate_no_idle : L.core.poolWire 1804∉wires (fastCandidate L) := by
  intro h
  have hs := List.mem_toFinset.mp (fastCandidate_support L hw hn h)
  simp only [List.mem_cons,List.mem_append,or_assoc] at hs
  rcases hs with h|h|h|h
  · exact idle_generic L hw hn h
  · exact idle_point L hw hn (by simp [PointAddLayout.pointWires,h])
  · exact idle_point L hw hn (by simp [PointAddLayout.pointWires,h])
  · exact idle_prefix L hw hn 776 (by omega) h

private theorem square_no_idle : L.core.poolWire 1804∉wires (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  intro h
  rw [fastSquareN,renameProgram_support] at h
  obtain ⟨old,used,e⟩ := Finset.mem_image.mp h
  have fixed : CompressedPointSquare.poolPermutation L.core.poolWire
      (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire 1804)=L.core.poolWire 1804 := by
    apply CompressedPointSquare.outside_fixed
    · rintro ⟨i,lo,hi,eq⟩
      have same := pool_inj L hw hn 1804 i (by omega) (by omega) eq
      omega
    · rintro ⟨i,lo,hi,eq⟩
      have same := pool_inj L hw hn 1804 i (by omega) (by omega) eq
      omega
  have same := (CompressedPointSquare.poolPermutation L.core.poolWire
    (CompressedPointSquare.layout_bounded_injective L hw hn)).injective (e.trans fixed.symm)
  subst same
  exact candidate_no_idle L hw hn used

/-- The entire current generic block avoids the old repair flag. -/
theorem fastGeneric2_no_pool1804 (cx cy : Fp) :
    L.core.poolWire 1804∉wires (fastGeneric2 L cx cy) := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      L.core.poolWire 1804∉wires (fastConstAdd L r k) :=
    fun h => const_no_idle L hw hn r hr ((FastConst.fastAdd_support _ _
      ⟨256,L.recoveryConstant_widths hw r (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩) h)
  have cn : L.core.poolWire 1804∉wires (fastConstNeg L cx) :=
    fun h => const_no_idle L hw hn L.point.x (Or.inl rfl) ((FastConst.fastNeg_support _ _
      ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩) h)
  have cr : L.core.poolWire 1804∉wires (fastConstRefl L (3*cx-1)) :=
    fun h => const_no_idle L hw hn L.point.x (Or.inl rfl) ((FastConst.fastRefl_support _ _
      ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩) h)
  simp only [fastGeneric2,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _,ca _ (Or.inr rfl) _⟩,
    farith_no_idle L hw hn false⟩,square_no_idle L hw hn⟩,cr⟩,
    farith_no_idle L hw hn true⟩,cn⟩,ca _ (Or.inr rfl) _⟩

private theorem idle_tau : tauM L (L.core.poolWire 1804)=L.core.poolWire 1804 := by
  simp [tauM,idle_generic L hw hn,idle_flag L hw hn L.genericSelect (by simp [inPlaceFlags])]

private theorem idle_sig : sigP L (L.core.poolWire 1804)=L.core.poolWire 1804 := by
  have park : L.core.poolWire 1804≠parkWire L := by
    intro e
    have same := pool_inj L hw hn 1804 514 (by omega) (by omega) e
    omega
  simp [sigP,idle_generic L hw hn,park]

private theorem renamed_no_idle (f : Wire → Wire) (hf : Function.Injective f)
    (fix : f (L.core.poolWire 1804)=L.core.poolWire 1804) (P : Program)
    (hp : L.core.poolWire 1804∉wires P) : L.core.poolWire 1804∉wires (renameProgram f P) := by
  rw [renameProgram_support]
  intro h
  obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
  have same := hf (e.trans fix.symm)
  exact hp (same ▸ hq)

private theorem pair_no_idle (t₁ t₂ : Wire) (h1 : t₁∈L.inPlaceFlags) (h2 : t₂∈L.inPlaceFlags)
    (e₁ e₂ : Bool) (C D : Point) : L.core.poolWire 1804∉wires (pairEqual L t₁ t₂ e₁ e₂ C D) := by
  intro hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,pairSrc] at h
  rcases h with h|h|h|h|h|h
  · exact idle_control L hw hn h
  · exact idle_point L hw hn (by simp [PointAddLayout.pointWires,h,yLow_mem L hw])
  · exact idle_flag L hw hn _ h1 h
  · exact idle_flag L hw hn _ h2 h
  · exact idle_point L hw hn (by simp [PointAddLayout.pointWires,h])
  · exact idle_prefix L hw hn 256 (by omega) h

private theorem gated_no_idle (en : Bool) (t : Wire) (ht : t∈L.inPlaceFlags) (P : Point) :
    L.core.poolWire 1804∉wires (gatedShort L en t P) := by
  cases en
  · simp [gatedShort,wires]
  · intro hq
    have h := shortEqual_wires_subset L hw L.control t P (pointCode P)
      (by simpa only [gatedShort,if_true] using hq)
    rw [equalConstant_wires] at h
    have hp := zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp [PointAddLayout.pointWires,L.dialogPool_length hw,
        show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY])
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with h|h|h
    · exact idle_control L hw hn h
    · exact idle_flag L hw hn _ ht h
    · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h|h
      · exact idle_point L hw hn h
      · exact idle_prefix L hw hn 513 (by omega) h

private theorem out_no_idle (C : Point) : L.core.poolWire 1804∉wires (outStage L C) := by
  intro hq
  rcases outStage_wires L hw C _ hq with h|h|h|h|h
  · exact idle_point L hw hn h
  · exact idle_control L hw hn h
  · exact idle_generic L hw hn h
  · have hf : L.core.poolWire 1804∈L.inPlaceFlags := by
      simp only [flagsN,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h|h <;> simp [inPlaceFlags,h]
    exact idle_resident L hw hn (by simp [CompressedPointSquare.residents,hf])
  · exact idle_prefix L hw hn 256 (by omega) h

private theorem genFlag_no_idle : L.core.poolWire 1804∉wires (genFlagN L) := by
  intro hq
  -- Its actual five wires are resident sites.
  simp only [genFlagN,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,or_false] at hq
  apply idle_resident L hw hn
  simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,inPlaceFlags,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem chain_no_idle : L.core.poolWire 1804∉wires (chainErase L.control L.point.finite L.genericSelect) := by
  intro hq
  simp only [chainErase,wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil,or_false] at hq
  apply idle_resident L hw hn
  simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,inPlaceFlags,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  tauto

/-- No wrapper instruction or correction uses the old repair flag. -/
theorem finiteProgramN_no_pool1804 (C : Point) (cy : Fp) (Gen : Program)
    (hGen : L.core.poolWire 1804∉wires Gen) :
    L.core.poolWire 1804∉wires (finiteProgramN L C cy Gen) := by
  have stage : L.core.poolWire 1804∉wires (mergeFlagsN L ++ renameProgram (sigP L) (outTail L C)) := by
    rw [mergeStage_wires L hw hn C,wires_append,Finset.mem_union,not_or]
    exact ⟨genFlag_no_idle L hw hn,renamed_no_idle L hw hn _ (sigP_injective L hw hn)
      (idle_sig L hw hn) _ (out_no_idle L hw hn C)⟩
  simp only [wires_append,Finset.mem_union,not_or] at stage
  simp only [finiteProgramN,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨pair_no_idle L hw hn _ _ (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) _ _ _ _,
    gated_no_idle L hw hn _ _ (by simp [inPlaceFlags]) _⟩,genFlag_no_idle L hw hn⟩,
    renamed_no_idle L hw hn _ (tauM_injective L hn) (idle_tau L hw hn) _ hGen⟩,
    stage.1⟩,stage.2⟩,gated_no_idle L hw hn _ _ (by simp [inPlaceFlags]) _⟩,
    chain_no_idle L hw hn⟩

/-- Remove the proved idle site from the existing certified inventory. -/
def sitesR : Finset Wire := (sitesN L).toFinset.erase (L.core.poolWire 1804)

theorem idle_in_sitesN : L.core.poolWire 1804∈(sitesN L).toFinset := by
  apply List.mem_toFinset.mpr
  apply poolQ_N
  simp only [sharedPoolF,List.mem_append,wireBlock,List.mem_map,List.mem_range'_1]
  exact Or.inr ⟨1804,by omega,rfl⟩

theorem sitesR_card : (sitesR L).card≤1891 := by
  have upper := List.toFinset_card_le (sitesN L)
  rw [sitesN_length L hw] at upper
  have er := Finset.card_erase_of_mem (idle_in_sitesN L hw hn)
  unfold sitesR
  omega

theorem point_R (q : Wire) (hq : q∈PointAddLayout.pointWires L.point) : q∈sitesR L := by
  apply Finset.mem_erase.mpr
  exact ⟨fun e => idle_point L hw hn (e ▸ hq),List.mem_toFinset.mpr (point_N L q hq)⟩

theorem control_R : L.control∈sitesR L := by
  apply Finset.mem_erase.mpr
  exact ⟨(idle_control L hw hn).symm,List.mem_toFinset.mpr (control_N L)⟩

theorem finiteProgramN_supportR (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen⊆(sitesG L).toFinset) (hGen : L.core.poolWire 1804∉wires Gen) :
    wires (finiteProgramN L C cy Gen)⊆sitesR L := by
  intro q hq
  exact Finset.mem_erase.mpr ⟨fun e => finiteProgramN_no_pool1804 L hw hn C cy Gen hGen (e ▸ hq),
    finiteProgramN_support L hw hn C cy Gen hG hq⟩

end Pool
end ECDSAAdd.Entrant
