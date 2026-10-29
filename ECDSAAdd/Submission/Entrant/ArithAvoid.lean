import ECDSAAdd.Baselines.SkywalkCertificate

/-! The mapped Skywalk arithmetic never touches the logical labels `2313` or
`2401`–`2408`.

The published support certificate for the arithmetic (`controlled_support`)
places it inside the full 1,899-label inventory.  The arithmetic's actual
gates come from the integer universe (labels below 1,798), from the field
sites (`fieldSite`) and from the history packets, all relocated by the
allocation permutations, which only move labels inside the work/hole region.
None of these is one of the labels above, so their physical images (the
auxiliary carry-in and eight classification/control metadata sites) are not
in the arithmetic's support. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation Secp256k1
attribute [local irreducible] wires OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] dblInPlace halfInPlace copyRegister
attribute [local irreducible] addInPlace subInPlace compareLt
attribute [local irreducible] compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
  NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse

/-- Logical labels avoided by the arithmetic. -/
def badIdx (q : Nat) : Prop := q = 2313 ∨ (2401 ≤ q ∧ q ≤ 2408)

/-- A physical wire that is not the image (under `base`) of a bad label. -/
def goodW (q : Wire) : Prop := ¬ (q = 2313 + 16 ∨ (2401 + 16 ≤ q ∧ q ≤ 2408 + 16))

def Avoid (P : Program) : Prop := ∀ q ∈ wires P, goodW q

theorem avoid_append {P Q : Program} : Avoid (P ++ Q) ↔ Avoid P ∧ Avoid Q := by
  simp only [Avoid, wires_append, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · intro h q hq; rcases hq with hq | hq
    · exact h.1 q hq
    · exact h.2 q hq

theorem avoid_sub {P Q : Program} (h : wires P ⊆ wires Q) (hq : Avoid Q) : Avoid P :=
  fun q hp => hq q (h hp)

theorem avoid_nil : Avoid [] := by intro q hq; simp [wires] at hq

theorem base_good (q : Nat) (h : ¬ badIdx q) : goodW (base q) := by
  show ¬ (q + 16 = 2313 + 16 ∨ (2401 + 16 ≤ q + 16 ∧ q + 16 ≤ 2408 + 16))
  unfold badIdx at h; omega

theorem bad_not_zero (q : Nat) (h : badIdx q) : ¬ zeroRegion q := by
  unfold badIdx at h; unfold zeroRegion workRegion holeRegion; omega

theorem pi0_good (q : Nat) (h : ¬ badIdx q) : ¬ badIdx (pi0 q) := by
  intro hb
  have fix := pi0_outside (pi0 q) (bad_not_zero _ hb)
  have := pi0.injective fix
  exact h (this ▸ hb)

theorem pi_good (j q : Nat) (hj : j < 170) (h : ¬ badIdx q) : ¬ badIdx (pi j q) := by
  intro hb
  have fix := pi_outside j (pi j q) hj (bad_not_zero _ hb)
  have := (pi j).injective fix
  exact h (this ▸ hb)

theorem allPlaced_good (q : Nat) (h : ¬ badIdx q) : goodW (allPlaced q) :=
  base_good _ (pi0_good q h)

theorem placed_good (j q : Nat) (hj : j < 170) (h : ¬ badIdx q) : goodW (placed j q) :=
  base_good _ (pi_good j q hj h)

theorem field_not_bad (q : Nat) (h : fieldSite q) : ¬ badIdx q := by
  unfold fieldSite at h; unfold badIdx; omega

theorem shared_site' (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : fieldSite q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold fieldSite
  omega

theorem packet_not_bad (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : ¬ badIdx q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold badIdx; unfold H at h
  omega

theorem inventory_not_bad (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) : ¬ badIdx q := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact field_not_bad q (shared_site' q h)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    unfold badIdx; omega
  · exact packet_not_bad j q hj h

/-! Field side. -/

theorem cell_avoid (divide : Bool) (j i : Nat) (hj : j < 170)
    (hi0 : 3*j ≤ i) (hi : i < 3*j+3) :
    Avoid (renameProgram (placed j) (logicalCell divide i)) := by
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
  exact placed_good j old hj (inventory_not_bad j old hj belongs)

theorem codec_avoid (j : Nat) (hj : j < 170) :
    Avoid (compressedHistoryEncode (placed j) (3*j)) ∧
    Avoid (compressedHistoryDecode (placed j) (3*j)) := by
  constructor
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inl rfl) q hq
    exact placed_good j _ hj (packet_not_bad j _ hj (history_packet j u))
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inr rfl) q hq
    exact placed_good j _ hj (packet_not_bad j _ hj (history_packet j u))

theorem group_avoid (divide : Bool) (j : Nat) (hj : j < 170) : Avoid (mappedGroup divide j) := by
  have codec := codec_avoid j hj
  have a := cell_avoid divide j (3*j) hj (by omega) (by omega)
  have b := cell_avoid divide j (3*j+1) hj (by omega) (by omega)
  have c := cell_avoid divide j (3*j+2) hj (by omega) (by omega)
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,avoid_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem groups_avoid (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    Avoid (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp only [mappedGroups]; exact avoid_nil
  | succ n ih =>
    have current := group_avoid divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,avoid_append]
    · exact ⟨rest,current⟩
    · exact ⟨current,rest⟩

theorem tail_avoid (divide : Bool) (i : Nat) (hi : i=510 ∨ i=511) :
    Avoid (renameProgram allPlaced (logicalCell divide i)) := by
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
  apply allPlaced_good
  rcases belongs with h|rfl|rfl|rfl|rfl
  · exact field_not_bad old (shared_site' old h)
  all_goals unfold badIdx; omega

theorem mappedReplay_avoid (divide : Bool) : Avoid (mappedReplay divide) := by
  have groups := groups_avoid divide 0 170 (by omega)
  have a := tail_avoid divide 510 (by omega)
  have b := tail_avoid divide 511 (by omega)
  cases divide <;> simp only [mappedReplay,Bool.false_eq_true,if_false,if_true,avoid_append]
  · exact ⟨⟨b,a⟩,groups⟩
  · exact ⟨⟨groups,a⟩,b⟩

theorem convert_site' (target : Bool) (q : Nat)
    (h : q∈(if target then balancedSharedTargetConvert id else balancedSharedSourceConvert id).wires) :
    fieldSite q := by
  cases target <;> simp only [Bool.false_eq_true,if_false,if_true,
    balancedSharedTargetConvert,balancedSharedSourceConvert,BalancedConvert.Layout.wires,
    wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  all_goals dsimp only [id] at h; unfold fieldSite; omega

theorem converters_avoid (canonical : Bool) :
    Avoid (renameProgram allPlaced (converterPair canonical)) := by
  have target := BalancedConvert.support (balancedSharedTargetConvert id)
  have source := BalancedConvert.support (balancedSharedSourceConvert id)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have site : fieldSite old := by
    cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at hraw
    · rcases hraw with h|h
      · exact convert_site' true old (List.mem_toFinset.mp (target.1 h))
      · exact convert_site' false old (List.mem_toFinset.mp (source.1 h))
    · rcases hraw with h|h
      · exact convert_site' true old (List.mem_toFinset.mp (target.2 h))
      · exact convert_site' false old (List.mem_toFinset.mp (source.2 h))
  exact allPlaced_good old (field_not_bad old site)

theorem unary_avoid (divide : Bool) :
    Avoid (renameProgram allPlaced (if divide then dblInPlace (borrowedSkywalkUnary id) p
      else halfInPlace (borrowedSkywalkUnary id) p)) := by
  have u := modUnary_wires (borrowedSkywalkUnary id) 256 p (borrowedSkywalkUnary_widths id) (by omega)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member : old∈((borrowedSkywalkUnary id).z++(borrowedSkywalkUnary id).core.work++
      [(borrowedSkywalkUnary id).flag]).toFinset := by
    cases divide
    · simp only [Bool.false_eq_true,if_false] at hraw
      rw [u.2] at hraw
      exact hraw
    · simp only [if_true] at hraw
      rw [u.1] at hraw
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hraw))
  have site : fieldSite old := by
    change old∈((wireBlock id 2056 256++[id 2312])++
      (wireBlock id 512 257++wireBlock id 1540 256++[id 1797])++[id 769]).toFinset at member
    simp only [List.mem_toFinset,wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false] at member
    dsimp only [id] at member
    simp only [or_assoc] at member
    rcases member with h|rfl|h|h|rfl|rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · norm_num [fieldSite]
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · norm_num [fieldSite]
    · norm_num [fieldSite]
  exact allPlaced_good old (field_not_bad old site)

theorem copy_avoid : Avoid (renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) := by
  have zword : (skywalkSharedField id).z=wireBlock id 2056 257 := skywalkShared_field_z id
  have aword : (skywalkSharedField id).a=wireBlock id 770 257 := rfl
  have cp := copyRegister_wires_subset none (skywalkSharedField id).z (skywalkSharedField id).a
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member := cp hraw
  rw [zword,aword] at member
  have site : fieldSite old := by
    simp only [List.mem_toFinset,Option.toList_none,List.nil_append,wireBlock,List.map_id,
      List.mem_append,List.mem_range'_1] at member
    unfold fieldSite
    omega
  exact allPlaced_good old (field_not_bad old site)

theorem terminalFieldSegment_avoid (divide : Bool) :
    Avoid (EntryMappedFieldSegmentTrim.terminalFieldSegment divide) := by
  have rp : Avoid (EntryMappedFieldSegmentTrim.terminalReplay divide) :=
    avoid_sub ((EntryMappedFieldSegmentTrim.terminalReplay_support_sub divide).trans
      (EntryMappedFieldSegmentTrim.replay_support_sub divide)) (mappedReplay_avoid divide)
  have a := converters_avoid false
  have b := converters_avoid true
  cases divide <;> simp only [EntryMappedFieldSegmentTrim.terminalFieldSegment,Bool.false_eq_true,
    if_false,if_true,avoid_append]
  · exact ⟨⟨⟨⟨copy_avoid,a⟩,rp⟩,b⟩,avoid_nil⟩
  · exact ⟨⟨⟨⟨avoid_nil,a⟩,rp⟩,b⟩,copy_avoid⟩

theorem selectedFieldSegment_avoid (divide : Bool) : Avoid (selectedFieldSegment divide) :=
  avoid_sub (PenultimateMapped.fieldSegment_support_sub divide) (terminalFieldSegment_avoid divide)

/-! Integer side. -/

theorem integer_good (q : Nat) (h : q < 1798) : goodW (base q) := by
  apply base_good; unfold badIdx; omega

theorem tick_layout_avoid (i : Nat) (hi : i < 512) :
    ∀ q ∈ (compactSkywalkTickLayout base i).wires.toFinset, goodW q := by
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
  apply integer_good
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  by_cases hz : i=0
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; omega

theorem ticks_avoid (i : Nat) (hi : i < 512) :
    Avoid (compactSkywalkTick base i) ∧ Avoid (compactSkywalkReverseTick base i) :=
  ⟨fun q hq => tick_layout_avoid i hi q (compactSkywalkTick_support base i hi base_pool_nodup hq),
   fun q hq => tick_layout_avoid i hi q (compactSkywalkReverseTick_support base i hi base_pool_nodup hq)⟩

theorem base_codec_avoid (start : Nat) (hs : start+3 ≤ 512) :
    Avoid (compressedHistoryEncode base start) ∧ Avoid (compressedHistoryDecode base start) := by
  have lift (P : Program) (he : P=compressedHistoryEncode base start ∨
      P=compressedHistoryDecode base start) : Avoid P := by
    intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above start hs P he q hq
    have region := compressedHistoryId_region start hs u
    apply integer_good
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem delayed_codec_avoid (i : Nat) (hi : i < 512) :
    Avoid (compressedPackAfter base i) ∧ Avoid (compressedDecodeBefore base i) := by
  cases h : compressedPackDue i
  · simp only [compressedPackAfter,compressedDecodeBefore,h,Bool.false_eq_true,if_false]
    exact ⟨avoid_nil, avoid_nil⟩
  · have due := compressedPackDue_true i h
    have support := base_codec_avoid (i-3) (by omega)
    simpa only [compressedPackAfter,compressedDecodeBefore,h,if_true] using support

theorem integer_avoid (i n : Nat) (h : i+n ≤ 512) :
    Avoid (compressedCompactForward base i n) ∧ Avoid (compressedCompactReverse base i n) := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse]; exact ⟨avoid_nil, avoid_nil⟩
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := ticks_avoid i (by omega)
    have codec := delayed_codec_avoid i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,avoid_append]
    exact ⟨⟨⟨tick.1,codec.1⟩,rest.1⟩,⟨⟨rest.2,codec.2⟩,tick.2⟩⟩

theorem prefixSites_avoid : ∀ q ∈ (NativeFirstDirect.prefixSites base).toFinset, goodW q := by
  intro q hq
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      exact integer_good _ (by omega)
    | exact integer_good _ (by omega)

theorem clear_avoid : Avoid (skywalkArithmeticClear base) := by
  intro q hq
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact integer_good _ (by omega)

theorem kernel_avoid (divide : Bool) : Avoid (kernel divide) := by
  have native := NativeFirstDirect.prefix_support base
  have integer := integer_avoid 1 511 (by omega)
  have known := NativeFirstKnown.inverse_support base
  simp only [kernel,avoid_append]
  exact ⟨⟨⟨⟨⟨⟨fun q hq => prefixSites_avoid q (native.1 hq),integer.1⟩,clear_avoid⟩,
    selectedFieldSegment_avoid divide⟩,clear_avoid⟩,integer.2⟩,
    fun q hq => prefixSites_avoid q (known hq)⟩

/-! The zero-divisor wrapper never uses its auxiliary carry-in. -/

theorem zeroCompare_avoid (x x' : Wire) (xs : List Wire) (c : Wire) (cs : List Wire) (cin target : Wire)
    (good : ∀ q ∈ x :: x' :: xs ++ c :: cs ++ [target], goodW q) :
    Avoid (ZeroSeededConstantCompare.program (x::x'::xs) (c::cs) cin target) := by
  intro q hq
  simp only [ZeroSeededConstantCompare.program, wires_append, Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · simp [ZeroSeededConstantCompare.prepare, wires, Instr.wires] at h
    rcases h with rfl|rfl <;> exact good _ (by simp)
  · have h' := List.mem_toFinset.mp (compareConstantLt_wires_subset _ _ _ _ _ h)
    apply good
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
    tauto
  · simp [ZeroSeededConstantCompare.release, wires, Instr.wires] at h
    rcases h with rfl|rfl <;> exact good _ (by simp)

theorem controlled_avoid (divide : Bool) : Avoid (controlled divide) := by
  have xs : wireBlock base 770 256 = base 770 :: base 771 :: wireBlock base 772 254 := by
    simp [wireBlock, List.range'_succ]
  have cs : wireBlock base 0 255 = base 0 :: wireBlock base 1 254 := by
    simp [wireBlock, List.range'_succ]
  have good : ∀ q ∈ base 770 :: base 771 :: wireBlock base 772 254 ++ base 0 :: wireBlock base 1 254 ++
      [base 2411], goodW q := by
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, wireBlock, List.mem_map,
      List.mem_range'_1] at hq
    rcases hq with ((rfl|rfl|⟨i,hi,rfl⟩)|(rfl|⟨i,hi,rfl⟩))|rfl
    all_goals apply base_good; unfold badIdx; omega
  have cmp := zeroCompare_avoid _ _ _ _ _ (base 2313) (base 2411) good
  have mask : Avoid (maskedConstant (base 2411) (wireBlock base 770 256) 1) := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ hq)
    rw [xs] at h
    exact good q (by simp only [List.mem_cons, List.mem_append] at h ⊢; tauto)
  simp only [controlled, directZeroControlled, directZeroDivisorEnter, directZeroDivisorLeave,
    avoid_append, xs, cs]
  rw [xs] at mask
  exact ⟨⟨cmp, mask⟩, kernel_avoid divide, mask, cmp⟩

end ECDSAAdd.Entrant
