import ECDSAAdd.Submission.Entrant.FastSquare
import ECDSAAdd.Submission.Entrant.EKFree

/-! Support, frame, resources and validity of `finiteProgramE`.

The program lives in `sitesE`: the point, the control, the five classification
flags still in use, and the certified pool inventory without site 1801. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

def flagsE (L : ControlledPointLayout) : List Wire :=
  [L.infinitySelect, L.doubleSelect, L.genericSelect, L.core.generic, L.core.equalNegY]

def sitesE (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsE L ++ sharedPoolQ L

theorem sitesE_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesE L).length = 1896 := by
  simp [sitesE, flagsE, sharedPoolQ, PointAddLayout.pointWires, wireBlock_length,
    show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]

section Support
attribute [local irreducible] wires shortEqual pairEqual controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

theorem point_E (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesE L := by
  simp [sitesE, hq]

theorem control_E : L.control ∈ sitesE L := by simp [sitesE]

theorem flag_E (t : Wire) (ht : t ∈ flagsE L) : t ∈ sitesE L := by
  simp only [sitesE, List.mem_append]; exact Or.inl (Or.inr ht)

theorem x_E (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesE L :=
  point_E L q (by simp [PointAddLayout.pointWires, hq])
theorem y_E (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesE L :=
  point_E L q (by simp [PointAddLayout.pointWires, hq])
theorem generic_E : L.core.generic ∈ sitesE L := flag_E L _ (by simp [flagsE])

theorem poolQ_E (q : Wire) (hq : q ∈ sharedPoolQ L) : q ∈ sitesE L := by
  simp only [sitesE, List.mem_append]; exact Or.inr hq

theorem sharedPool_Q (q : Wire) (hq : q ∈ CompressedPointSquare.sharedPool L)
    (hne : q ≠ L.core.poolWire 1801) : q ∈ sharedPoolQ L := by
  have h := sitesQ_of_sites L q (List.mem_append_right _ hq) hne
  simp only [sitesQ, List.mem_append] at h
  rcases h with h | h
  · -- the pool part of the original inventory: re-derive membership directly
    simp only [CompressedPointSquare.sharedPool, sharedPoolQ, List.mem_append] at hq ⊢
    rcases hq with (h1 | h1) | h1
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h1))
    · have h' : q ∈ [L.core.poolWire 1800, L.core.poolWire 1801, L.core.poolWire 1802,
          L.core.poolWire 1803, L.core.poolWire 1804] := by
        simpa [wireBlock, List.range'_succ] using h1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with h' | h' | h' | h' | h'
      · exact Or.inl (Or.inr (by simp [h']))
      · exact absurd h' hne
      · exact Or.inr (by simp [wireBlock, List.range'_succ, h'])
      · exact Or.inr (by simp [wireBlock, List.range'_succ, h'])
      · exact Or.inr (by simp [wireBlock, List.range'_succ, h'])
  · exact h

include hw

theorem pool_lowE (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesE L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_E
  simp only [sharedPoolQ, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

include hn

omit hw hn in
theorem E_of_sites (q : Wire) (hq : q ∈ CompressedPointSquare.residents L ++ CompressedPointSquare.sharedPool L)
    (h1 : q ≠ L.core.poolWire 1801) (h2 : q ≠ L.core.equalX) (h3 : q ≠ L.core.double) :
    q ∈ sitesE L := by
  rcases List.mem_append.mp hq with hr | hp
  · simp only [CompressedPointSquare.residents, inPlaceFlags, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (hp | hc) | hf
    · exact point_E L q hp
    · rw [hc]; exact control_E L
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact flag_E L _ (by simp [flagsE])
      · exact flag_E L _ (by simp [flagsE])
      · exact flag_E L _ (by simp [flagsE])
      · exact flag_E L _ (by simp [flagsE])
      · exact absurd rfl h2
      · exact flag_E L _ (by simp [flagsE])
      · exact absurd rfl h3
  · exact poolQ_E L q (sharedPool_Q L q hp h1)

omit hn in
theorem pairE (t₁ t₂ : Wire) (h1 : t₁ ∈ flagsE L) (h2 : t₂ ∈ flagsE L) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (sitesE L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | rfl | rfl | h | h
  · exact control_E L
  · exact y_E L _ hy
  · exact flag_E L _ h1
  · exact flag_E L _ h2
  · exact x_E L _ h
  · exact pool_lowE L hw 256 (by omega) q h

omit hn in
theorem gatedE (en : Bool) (t : Wire) (ht : t ∈ flagsE L) (P : Point) :
    wires (gatedShort L en t P) ⊆ (sitesE L).toFinset := by
  cases en
  · simp [gatedShort, wires]
  · intro q hq
    simp only [gatedShort, if_true] at hq
    have h := shortEqual_wires_subset L hw L.control t P (pointCode P) hq
    rw [equalConstant_wires] at h
    have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp [PointAddLayout.pointWires, L.dialogPool_length hw,
        show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]))
    simp only [List.mem_toFinset, List.mem_cons] at h
    apply List.mem_toFinset.mpr
    rcases h with rfl | rfl | h
    · exact control_E L
    · exact flag_E L _ ht
    · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h' | h'
      · exact point_E L _ h'
      · exact pool_lowE L hw 513 (by omega) _ h'

omit hw hn in
theorem zeroFlagE (t : Wire) (ht : t ∈ flagsE L) :
    wires (zeroFlag L.point.finite L.control t) ⊆ (sitesE L).toFinset := by
  rw [zeroFlag_wires]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl
  · exact point_E L _ (by simp [PointAddLayout.pointWires])
  · exact control_E L
  · exact flag_E L _ ht

omit hw hn in
theorem genericFlagE : wires (pointDialogGenericFlag L) ⊆ (sitesE L).toFinset := by
  intro q hq
  simp [pointDialogGenericFlag, pointInPlaceGenericFlag, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact control_E L
    | exact flag_E L _ (by simp [flagsE])

omit hw hn in
theorem cornersE (C : Point) : wires (pointDialogCorners L C) ⊆ (sitesE L).toFinset := by
  have m (c : Wire) (hc : c ∈ flagsE L) (P : Point) :
      wires (maskedPointConstant c L.point P) ⊆ (sitesE L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedPointConstant_support c L.point P hq)
    apply List.mem_toFinset.mpr
    rcases List.mem_cons.mp h with rfl | h
    · exact flag_E L _ hc
    · exact point_E L _ h
  simp only [pointDialogCorners, pointInPlaceCorners, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨m _ (by simp [flagsE]) _, m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩,
    m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩

omit hn in
theorem finiteProgramEG_support (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (sitesE L).toFinset) :
    wires (finiteProgramEG L C cy Gen) ⊆ (sitesE L).toFinset := by
  have fS : flagsE L = [L.infinitySelect, L.doubleSelect, L.genericSelect, L.core.generic,
    L.core.equalNegY] := rfl
  simp only [finiteProgramEG, wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨zeroFlagE L _ (by simp [fS]), pairE L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _⟩,
    gatedE L hw _ _ (by simp [fS]) _⟩, genericFlagE L⟩, hG⟩, cornersE L _⟩, genericFlagE L⟩,
    pairE L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _⟩, gatedE L hw _ _ (by simp [fS]) _⟩,
    zeroFlagE L _ (by simp [fS])⟩

/-! The Skywalk generic block. -/

theorem arithE (multiply : Bool) :
    wires (pointCompressedArithmetic L multiply) ⊆ (sitesE L).toFinset := by
  intro q hq
  rw [pointCompressedArithmetic, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have hslot := controlled_support (!multiply) used
  have hgood := controlled_avoid (!multiply) old used
  have inv := pointCompressedArithmetic_support L hw multiply
    (by rw [pointCompressedArithmetic, renameProgram_support]; exact Finset.mem_image.mpr ⟨old, used, rfl⟩)
  have mem (i : Nat) (hi : i ∈ indices) : base i ∈ slots.toFinset := by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, hi, rfl⟩)
  have avoid (i : Nat) (hi : i ∈ indices) (hb : pointWireFn L (base i) = pointWireFn L old) : old = base i :=
    (pointWireFn_injective_slots L hw hn old hslot (base i) (mem i hi) hb.symm)
  have hidx (i : Nat) (h1 : 2056 ≤ i ∨ 2400 ≤ i) (h2 : i < 2314 ∨ i < 2412) (h3 : ¬ (515 ≤ i ∧ i < 684))
      (h4 : i < 2314 ∨ 2400 ≤ i) (h5 : i < 1798 ∨ 2056 ≤ i) : i ∈ indices := by
    simp only [indices, List.mem_append, List.mem_range'_1]; omega
  apply List.mem_toFinset.mpr
  apply E_of_sites L _ (List.mem_toFinset.mp inv)
  · intro e
    have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
      simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 2313 (hidx 2313 (by omega) (by omega) (by omega) (by omega) (by omega)) (himg.trans e.symm)
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2406) = L.core.equalX := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.1
    have := avoid 2406 (hidx 2406 (by omega) (by omega) (by omega) (by omega) (by omega)) (himg.trans e.symm)
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2408) = L.core.double := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.2.1
    have := avoid 2408 (hidx 2408 (by omega) (by omega) (by omega) (by omega) (by omega)) (himg.trans e.symm)
    subst this; exact hgood (by simp [base])

theorem squareE : wires (CompressedPointSquare.computableProgram L) ⊆ (sitesE L).toFinset := by
  rw [CompressedPointSquare.computableProgram_eq L hw hn]
  intro q hq
  rw [CompressedPointSquare.program, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have supp := pointMeasuredSquareCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at supp
  apply List.mem_toFinset.mpr
  rcases supp with h | h | h | h
  · rw [h, CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      inPlaceFlags])]
    exact generic_E L
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact y_E L _ h
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact x_E L _ h
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)]
    apply poolQ_E
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have ha := CompressedPointSquare.prefix_allowed i bound
    simp only [sharedPoolQ, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, by omega, rfl⟩))

attribute [local irreducible] fastCandidate in
theorem fastSquareE : wires (fastSquare L) ⊆ (sitesE L).toFinset := by
  rw [fastSquare_eq L hw hn]
  intro q hq
  rw [fastSquareN, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have supp := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at supp
  apply List.mem_toFinset.mpr
  rcases supp with h | h | h | h
  · rw [h, CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      inPlaceFlags])]
    exact generic_E L
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact y_E L _ h
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact x_E L _ h
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)]
    apply poolQ_E
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have ha := CompressedPointSquare.prefix_allowed i bound
    simp only [sharedPoolQ, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, by omega, rfl⟩))

theorem fastSquareNRE : wires (fastSquareNR L) ⊆ (sitesE L).toFinset :=
  (fastSquareNR_wires L).trans (fastSquareE L hw hn)

omit hn in
theorem constAddE (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (k : Fp) :
    wires (pointDialogConstantAdd L r k) ⊆ (sitesE L).toFinset := by
  intro q hq
  have h := List.mem_toFinset.mp (pointRecoveryConstantAdd_support L hw r k hq)
  apply List.mem_toFinset.mpr
  simp only [List.mem_cons, List.mem_append, or_assoc] at h
  rcases h with h | h | h
  · rw [h]; exact generic_E L
  · rcases hr with rfl | rfl
    · exact x_E L _ h
    · exact y_E L _ h
  · exact pool_lowE L hw 515 (by omega) _ h

omit hn in
theorem recoveryE (cx cy : Fp) : wires (pointRecoveryStage L cx cy) ⊆ (sitesE L).toFinset := by
  have neg : wires (pointRecoveryReflection L) ⊆ (sitesE L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (pointRecoveryReflection_support L hw hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_cons, List.mem_append, or_assoc] at h
    rcases h with h | h | h
    · rw [h]; exact generic_E L
    · exact x_E L _ h
    · exact pool_lowE L hw 258 (by omega) _ h
  simp only [pointRecoveryStage, pointDialogConstantAdd, wires_append, Finset.union_subset_iff]
  exact ⟨⟨neg, constAddE L hw _ (Or.inl rfl) _⟩, constAddE L hw _ (Or.inr rfl) _⟩

theorem skywalkGenericE (cx cy : Fp) :
    wires (pointCompressedDialogGeneric L cx cy) ⊆ (sitesE L).toFinset := by
  simp only [pointCompressedDialogGeneric, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨constAddE L hw _ (Or.inl rfl) _, constAddE L hw _ (Or.inr rfl) _⟩,
    arithE L hw hn false⟩, squareE L hw hn⟩, constAddE L hw _ (Or.inl rfl) _⟩,
    arithE L hw hn true⟩, recoveryE L hw cx cy⟩

omit hn in
theorem sharedPool_Q_sub (q : Wire) (hq : q ∈ sharedPoolQ L) : q ∈ L.dialogPool := by
  have big : q ∈ L.dialogPool.take 2613 := by
    rw [pool_block L hw 2613 (le_refl _)]
    simp only [sharedPoolQ, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [wireBlock, List.mem_map, List.mem_range'_1]
    rcases hq with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨1800, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩
  exact List.mem_of_mem_take big

omit hn in
theorem sitesE_used : (sitesE L).toFinset ⊆ L.dialogUsedWires.toFinset := by
  intro q hq
  have h := List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [sitesE, flagsE, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [dialogUsedWires, inPlaceFlags, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · tauto
  · exact Or.inr (sharedPool_Q_sub L hw q h)

end Support

end ECDSAAdd.Entrant
