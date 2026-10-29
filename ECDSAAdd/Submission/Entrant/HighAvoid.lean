import ECDSAAdd.Submission.Entrant.ArithAvoid
import ECDSAAdd.Submission.Entrant.LaneArith

/-! Actual instruction support after the zero high-bit copy is omitted. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed MappedCompressed.LaneA CompressedAllocation Secp256k1
attribute [local irreducible] wires OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
  compressedHistoryEncode compressedHistoryDecode compactSkywalkTick compactSkywalkReverseTick
  NativeFirstDirect.forward NativeFirstKnown.inverse PenultimateMapped.replay laneKernel

def high_badIdx (q : Nat) : Prop := q=2312
def high_goodW (q : Wire) : Prop := q≠base 2312
def high_Avoid (P : Program) : Prop := ∀q∈wires P,high_goodW q

theorem high_avoid_append {P Q : Program} : high_Avoid (P ++ Q) ↔ high_Avoid P ∧ high_Avoid Q := by
  simp only [high_Avoid, wires_append, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · intro h q hq; rcases hq with hq | hq
    · exact h.1 q hq
    · exact h.2 q hq

theorem high_avoid_sub {P Q : Program} (h : wires P ⊆ wires Q) (hq : high_Avoid Q) : high_Avoid P :=
  fun q hp => hq q (h hp)

theorem high_avoid_nil : high_Avoid [] := by intro q hq; simp [wires] at hq

theorem high_base_good (q : Nat) (h : ¬ high_badIdx q) : high_goodW (base q) := by
  show q+16 ≠ 2312+16
  unfold high_badIdx at h; omega

theorem high_bad_not_zero (q : Nat) (h : high_badIdx q) : ¬ zeroRegion q := by
  unfold high_badIdx at h; unfold zeroRegion workRegion holeRegion; omega

theorem high_pi0_good (q : Nat) (h : ¬ high_badIdx q) : ¬ high_badIdx (pi0 q) := by
  intro hb
  have fix := pi0_outside (pi0 q) (high_bad_not_zero _ hb)
  have := pi0.injective fix
  exact h (this ▸ hb)

theorem high_pi_good (j q : Nat) (hj : j < 170) (h : ¬ high_badIdx q) : ¬ high_badIdx (pi j q) := by
  intro hb
  have fix := pi_outside j (pi j q) hj (high_bad_not_zero _ hb)
  have := (pi j).injective fix
  exact h (this ▸ hb)

theorem high_allPlaced_good (q : Nat) (h : ¬ high_badIdx q) : high_goodW (allPlaced q) :=
  high_base_good _ (high_pi0_good q h)

theorem high_placed_good (j q : Nat) (hj : j < 170) (h : ¬ high_badIdx q) : high_goodW (placed j q) :=
  high_base_good _ (high_pi_good j q hj h)

theorem high_shared_not_bad (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : ¬ high_badIdx q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold high_badIdx
  omega

theorem high_packet_not_bad (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : ¬ high_badIdx q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold high_badIdx; unfold H at h
  omega

theorem high_inventory_not_bad (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) : ¬ high_badIdx q := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact high_shared_not_bad q h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    unfold high_badIdx; omega
  · exact high_packet_not_bad j q hj h

/-! Field side. -/

theorem high_cell_avoid (divide : Bool) (j i : Nat) (hj : j < 170)
    (hi0 : 3*j ≤ i) (hi : i < 3*j+3) :
    high_Avoid (renameProgram (placed j) (logicalCell divide i)) := by
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
  exact high_placed_good j old hj (high_inventory_not_bad j old hj belongs)

theorem high_codec_avoid (j : Nat) (hj : j < 170) :
    high_Avoid (compressedHistoryEncode (placed j) (3*j)) ∧
    high_Avoid (compressedHistoryDecode (placed j) (3*j)) := by
  constructor
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inl rfl) q hq
    exact high_placed_good j _ hj (high_packet_not_bad j _ hj (history_packet j u))
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inr rfl) q hq
    exact high_placed_good j _ hj (high_packet_not_bad j _ hj (history_packet j u))

theorem high_group_avoid (divide : Bool) (j : Nat) (hj : j < 170) : high_Avoid (mappedGroup divide j) := by
  have codec := high_codec_avoid j hj
  have a := high_cell_avoid divide j (3*j) hj (by omega) (by omega)
  have b := high_cell_avoid divide j (3*j+1) hj (by omega) (by omega)
  have c := high_cell_avoid divide j (3*j+2) hj (by omega) (by omega)
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,high_avoid_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem high_groups_avoid (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    high_Avoid (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp only [mappedGroups]; exact high_avoid_nil
  | succ n ih =>
    have current := high_group_avoid divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,high_avoid_append]
    · exact ⟨rest,current⟩
    · exact ⟨current,rest⟩

theorem high_tail_avoid (divide : Bool) (i : Nat) (hi : i=510 ∨ i=511) :
    high_Avoid (renameProgram allPlaced (logicalCell divide i)) := by
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
  apply high_allPlaced_good
  rcases belongs with h|rfl|rfl|rfl|rfl
  · exact high_shared_not_bad old h
  all_goals unfold high_badIdx; omega

theorem high_mappedReplay_avoid (divide : Bool) : high_Avoid (mappedReplay divide) := by
  have groups := high_groups_avoid divide 0 170 (by omega)
  have a := high_tail_avoid divide 510 (by omega)
  have b := high_tail_avoid divide 511 (by omega)
  cases divide <;> simp only [mappedReplay,Bool.false_eq_true,if_false,if_true,high_avoid_append]
  · exact ⟨⟨b,a⟩,groups⟩
  · exact ⟨⟨groups,a⟩,b⟩

theorem high_integer_good (q : Nat) (h : q < 1798) (_h' : q ≠ 769) : high_goodW (base q) := by
  apply high_base_good; unfold high_badIdx; omega

theorem high_tick_layout_avoid (i : Nat) (hi : i < 512) :
    ∀ q ∈ (compactSkywalkTickLayout base i).wires.toFinset, high_goodW q := by
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
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; exact high_integer_good _ (by omega) (by omega)
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; exact high_integer_good _ (by omega) (by omega)

theorem high_ticks_avoid (i : Nat) (hi : i < 512) :
    high_Avoid (compactSkywalkTick base i) ∧ high_Avoid (compactSkywalkReverseTick base i) :=
  ⟨fun q hq => high_tick_layout_avoid i hi q (compactSkywalkTick_support base i hi base_pool_nodup hq),
   fun q hq => high_tick_layout_avoid i hi q (compactSkywalkReverseTick_support base i hi base_pool_nodup hq)⟩

theorem high_base_codec_avoid (start : Nat) (hs : start+3 ≤ 512) :
    high_Avoid (compressedHistoryEncode base start) ∧ high_Avoid (compressedHistoryDecode base start) := by
  have lift (P : Program) (he : P=compressedHistoryEncode base start ∨
      P=compressedHistoryDecode base start) : high_Avoid P := by
    intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above start hs P he q hq
    have region := compressedHistoryId_region start hs u
    exact high_integer_good _ (by omega) (by omega)
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem high_delayed_codec_avoid (i : Nat) (hi : i < 512) :
    high_Avoid (compressedPackAfter base i) ∧ high_Avoid (compressedDecodeBefore base i) := by
  cases h : compressedPackDue i
  · simp only [compressedPackAfter,compressedDecodeBefore,h,Bool.false_eq_true,if_false]
    exact ⟨high_avoid_nil, high_avoid_nil⟩
  · have due := compressedPackDue_true i h
    have support := high_base_codec_avoid (i-3) (by omega)
    simpa only [compressedPackAfter,compressedDecodeBefore,h,if_true] using support

theorem high_integer_avoid (i n : Nat) (h : i+n ≤ 512) :
    high_Avoid (compressedCompactForward base i n) ∧ high_Avoid (compressedCompactReverse base i n) := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse]; exact ⟨high_avoid_nil, high_avoid_nil⟩
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := high_ticks_avoid i (by omega)
    have codec := high_delayed_codec_avoid i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,high_avoid_append]
    exact ⟨⟨⟨tick.1,codec.1⟩,rest.1⟩,⟨⟨rest.2,codec.2⟩,tick.2⟩⟩

theorem high_prefixSites_avoid : ∀ q ∈ (NativeFirstDirect.prefixSites base).toFinset, high_goodW q := by
  intro q hq
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      exact high_integer_good _ (by omega) (by omega)
    | exact high_integer_good _ (by omega) (by omega)

theorem high_clear_avoid : high_Avoid (skywalkArithmeticClear base) := by
  intro q hq
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact high_integer_good _ (by omega) (by omega)


theorem high_target : high_Avoid centTarget ∧ high_Avoid canonTarget := by
  have s := BalancedConvert.LaneA.fast_support (balancedSharedTargetConvert base)
  have good : ∀ q∈(balancedSharedTargetConvert base).wires,high_goodW q := by
    intro q hq
    simp only [balancedSharedTargetConvert,BalancedConvert.Layout.wires,wireBlock,List.mem_append,
      List.mem_cons,List.mem_map,List.mem_range'_1,List.not_mem_nil,or_false,List.cons_append,
      List.nil_append] at hq
    rcases hq with h|h|h|h|h|h
    all_goals first
      | (subst h; apply high_base_good; unfold high_badIdx; omega)
      | (obtain ⟨i,hi,rfl⟩ := h; apply high_base_good; unfold high_badIdx; omega)
  exact ⟨fun q hq => good q (List.mem_toFinset.mp (s.1 hq)),
    fun q hq => good q (List.mem_toFinset.mp (s.2 hq))⟩

theorem high_copy : high_Avoid copyPair256 := by
  intro q hq
  have h := copyRegister_wires_subset none (wireBlock base 2056 256) (wireBlock base 770 256) hq
  simp only [List.mem_toFinset,Option.toList_none,List.nil_append,List.mem_append,wireBlock,
    List.mem_map,List.mem_range'_1] at h
  rcases h with ⟨i,hi,rfl⟩|⟨i,hi,rfl⟩
  all_goals apply high_base_good; unfold high_badIdx; omega

theorem high_replay (divide : Bool) : high_Avoid (PenultimateMapped.replay divide) :=
  high_avoid_sub ((PenultimateMapped.replay_support_sub divide).trans
    ((EntryMappedFieldSegmentTrim.terminalReplay_support_sub divide).trans
      (EntryMappedFieldSegmentTrim.replay_support_sub divide))) (high_mappedReplay_avoid divide)

theorem laneSegment_nohigh (divide : Bool) : high_Avoid (laneSegment divide) := by
  have t := high_target
  cases divide <;> simp only [laneSegment,mulSeg,divSeg,Bool.false_eq_true,if_false,if_true,high_avoid_append]
  · exact ⟨⟨⟨t.1,high_copy⟩,high_replay false⟩,t.2⟩
  · exact ⟨t.1,⟨high_replay true,high_copy⟩,t.2⟩

theorem laneKernel_nohigh (divide : Bool) : high_Avoid (laneKernel divide) := by
  have native := NativeFirstDirect.prefix_support base
  have integer := high_integer_avoid 1 511 (by omega)
  have known := NativeFirstKnown.inverse_support base
  simp only [laneKernel,high_avoid_append]
  exact ⟨⟨⟨⟨⟨⟨fun q hq => high_prefixSites_avoid q (native.1 hq),integer.1⟩,
    high_clear_avoid⟩,laneSegment_nohigh divide⟩,high_clear_avoid⟩,integer.2⟩,
    fun q hq => high_prefixSites_avoid q (known hq)⟩

theorem laneControlled_nohigh (divide : Bool) : high_Avoid (laneControlled divide) := by
  intro q hq
  have used := controlRepair_support (laneKernel divide) hq
  rcases Finset.mem_union.mp used with ports|core
  · simp only [Finset.mem_insert,Finset.mem_singleton] at ports
    rcases ports with rfl|rfl|rfl|rfl|rfl
    all_goals (apply high_base_good; unfold high_badIdx; omega)
  · exact laneKernel_nohigh divide q core

theorem laneKernel_high_unused (divide : Bool) : base 2312∉wires (laneKernel divide) :=
  fun h => laneKernel_nohigh divide _ h rfl

end ECDSAAdd.Entrant
