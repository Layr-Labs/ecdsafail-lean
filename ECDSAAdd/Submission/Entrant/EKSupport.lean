import ECDSAAdd.Submission.Entrant.FastSquare
import ECDSAAdd.Submission.Entrant.FlagG
import ECDSAAdd.Submission.Entrant.Arith2

/-! Support, frame, resources and validity of `finiteProgramE`.

The program lives in `sitesE`: the point, the control, the five classification
flags still in use, and the certified pool inventory without site 1801. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

def flagsE (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.genericSelect, L.core.generic, L.core.equalNegY]

/-- The certified pool inventory without sites 1541 and 1801. -/
def sharedPoolF (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515 ++ wireBlock L.core.poolWire 684 857 ++
    [L.core.poolWire 1800] ++ wireBlock L.core.poolWire 1802 3

def sitesE (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsE L ++ sharedPoolF L

theorem sitesE_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesE L).length = 1894 := by
  simp [sitesE, flagsE, sharedPoolF, PointAddLayout.pointWires, wireBlock_length,
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

theorem poolQ_E (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ sitesE L := by
  simp only [sitesE, List.mem_append]; exact Or.inr hq

theorem sharedPool_F (q : Wire) (hq : q ∈ CompressedPointSquare.sharedPool L)
    (hne : q ≠ L.core.poolWire 1801) (hne' : q ≠ L.core.poolWire 1541) : q ∈ sharedPoolF L := by
  simp only [CompressedPointSquare.sharedPool, sharedPoolF, List.mem_append] at hq ⊢
  rcases hq with (h1 | h1) | h1
  · exact Or.inl (Or.inl (Or.inl h1))
  · simp only [wireBlock, List.mem_map, List.mem_range'_1] at h1 ⊢
    obtain ⟨i, hi, rfl⟩ := h1
    have : i ≠ 1541 := fun e => hne' (by rw [e])
    exact Or.inl (Or.inl (Or.inr ⟨i, by omega, rfl⟩))
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

include hw

theorem pool_lowE (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesE L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_E
  simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

include hn

omit hw hn in
theorem E_of_sites (q : Wire) (hq : q ∈ CompressedPointSquare.residents L ++ CompressedPointSquare.sharedPool L)
    (h1 : q ≠ L.core.poolWire 1801) (h1' : q ≠ L.core.poolWire 1541)
    (h2 : q ≠ L.core.equalX) (h3 : q ≠ L.core.double) (h4 : q ≠ L.infinitySelect) :
    q ∈ sitesE L := by
  rcases List.mem_append.mp hq with hr | hp
  · simp only [CompressedPointSquare.residents, inPlaceFlags, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (hp | hc) | hf
    · exact point_E L q hp
    · rw [hc]; exact control_E L
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h4
      · exact flag_E L _ (by simp [flagsE])
      · exact flag_E L _ (by simp [flagsE])
      · exact flag_E L _ (by simp [flagsE])
      · exact absurd rfl h2
      · exact flag_E L _ (by simp [flagsE])
      · exact absurd rfl h3
  · exact poolQ_E L q (sharedPool_F L q hp h1 h1')

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
theorem genericFlagE : wires (genericFlag2 L) ⊆ (sitesE L).toFinset := by
  intro q hq
  simp [genericFlag2, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [sitesE, flagsE, PointAddLayout.pointWires]

omit hw hn in
theorem cornersE (C : Point) : wires (corners2 L C) ⊆ (sitesE L).toFinset := by
  have m (c : Wire) (hc : c ∈ flagsE L) (P : Point) :
      wires (maskedPointConstant c L.point P) ⊆ (sitesE L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedPointConstant_support c L.point P hq)
    apply List.mem_toFinset.mpr
    rcases List.mem_cons.mp h with rfl | h
    · exact flag_E L _ hc
    · exact point_E L _ h
  simp only [corners2, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨m _ (by simp [flagsE]) _, m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩,
    m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩

omit hw hn in
theorem chainEraseE (t : Wire) (ht : t ∈ flagsE L) :
    wires (chainErase L.control L.point.finite t) ⊆ (sitesE L).toFinset := by
  intro q hq
  have hw' : wires (chainErase L.control L.point.finite t) = {L.control, L.point.finite, t} := by
    ext q
    simp only [chainErase, wires, Instr.wires, correctionWires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  rw [hw'] at hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact List.mem_toFinset.mpr (control_E L)
  · exact List.mem_toFinset.mpr (point_E L L.point.finite (by simp [PointAddLayout.pointWires]))
  · exact List.mem_toFinset.mpr (flag_E L _ ht)

omit hn in
theorem finiteProgramFG_support (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (sitesE L).toFinset) :
    wires (finiteProgramFG L C cy Gen) ⊆ (sitesE L).toFinset := by
  have fS : flagsE L = [L.doubleSelect, L.genericSelect, L.core.generic, L.core.equalNegY] := rfl
  simp only [finiteProgramFG, wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨pairE L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _, gatedE L hw _ _ (by simp [fS]) _⟩,
    genericFlagE L⟩, hG⟩, genericFlagE L⟩, zeroFlagE L _ (by simp [fS])⟩, cornersE L _⟩,
    pairE L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _⟩, gatedE L hw _ _ (by simp [fS]) _⟩,
    chainEraseE L _ (by simp [fS])⟩

/-! The Skywalk generic block. -/

theorem arithE (multiply : Bool) :
    wires (arith2 L multiply) ⊆ (sitesE L).toFinset := by
  intro q hq
  obtain ⟨old, hslot, hgood, rfl⟩ := arith2_wire L multiply q hq
  have hs2 := swap2_slots old hslot
  have inv := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, hs2, rfl⟩)
  have avoid (k : Nat) (hk : base k ∈ slots.toFinset) (hb : pointWireFn L (base k) = pointWireFn L (swap2 old)) :
      old = swap2 (base k) := by
    have := pointWireFn_injective_slots L hw hn _ hs2 (base k) hk hb.symm
    rw [← this, swap2_involutive]
  have mem (k : Nat) (hk : k ∈ indices) : base k ∈ slots.toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hidx (k : Nat) (h : k = 2313 ∨ k = 2406 ∨ k = 2408 ∨ k = 769 ∨ k = 2403) : k ∈ indices := by
    simp only [indices, List.mem_append, List.mem_range'_1]; omega
  apply List.mem_toFinset.mpr
  apply E_of_sites L _ (List.mem_toFinset.mp inv)
  · intro e
    have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
      simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 2313 (mem _ (hidx 2313 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 1797) = L.core.poolWire 1541 := by
      simp only [pointWireFn_base, pointIndexWire, show (1797:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 1797 m1797 (himg.trans e.symm)
    rw [show swap2 (base 1797) = base 769 by simp only [swap2, base]; simp] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2406) = L.core.equalX := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.1
    have := avoid 2406 (mem _ (hidx 2406 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2408) = L.core.double := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.2.1
    have := avoid 2408 (mem _ (hidx 2408 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2403) = L.infinitySelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.1
    have := avoid 2403 (mem _ (hidx 2403 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
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
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
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
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, by omega, rfl⟩))

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

omit hn in
theorem sharedPool_Q_sub (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ L.dialogPool := by
  have big : q ∈ L.dialogPool.take 2613 := by
    rw [pool_block L hw 2613 (le_refl _)]
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1,
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
