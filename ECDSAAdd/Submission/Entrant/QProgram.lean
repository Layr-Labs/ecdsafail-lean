import ECDSAAdd.Submission.Entrant.Program
import ECDSAAdd.Submission.Entrant.QFast

/-! The finite-addend program avoids pool site 1801, so its support lies in
`sitesQ`, the certified inventory without that site. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout
attribute [local irreducible] pointCompressedDialogGeneric fastGeneric shortEqual pairEqual

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hw hn in
theorem flag_resident (t : Wire) (ht : t ∈ L.inPlaceFlags) : t ∈ CompressedPointSquare.residents L := by
  simp [CompressedPointSquare.residents, ht]

omit hw hn in
theorem control_resident : L.control ∈ CompressedPointSquare.residents L := by
  simp [CompressedPointSquare.residents]

omit hw hn in
theorem point_resident (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) :
    q ∈ CompressedPointSquare.residents L := by
  simp [CompressedPointSquare.residents, hq]

theorem p1801_flags (P : Program) (S : List Wire)
    (hS : ∀ q ∈ S, q = L.control ∨ q ∈ L.inPlaceFlags ∨ q ∈ PointAddLayout.pointWires L.point)
    (h : wires P ⊆ S.toFinset) : L.core.poolWire 1801 ∉ wires P := by
  apply p1801_of_subset L hw hn P 0 (by omega)
  intro q hq
  apply List.mem_toFinset.mpr
  apply List.mem_append_left
  rcases hS q (List.mem_toFinset.mp (h hq)) with rfl | h' | h'
  · exact control_resident L
  · exact flag_resident L q h'
  · exact point_resident L q h'

theorem p1801_short (c t : Wire) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
    (C : Point) : L.core.poolWire 1801 ∉ wires (shortEqual L c t C) := by
  apply p1801_of_subset L hw hn _ 513 (by omega)
  intro q hq
  have h := shortEqual_wires_subset L hw c t C (pointCode C) hq
  rw [equalConstant_wires] at h
  have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
    (by simp [PointAddLayout.pointWires, L.dialogPool_length hw,
      show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]))
  simp only [List.mem_toFinset, List.mem_cons] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | h
  · rcases hc with rfl | hc
    · exact List.mem_append_left _ (control_resident L)
    · exact List.mem_append_left _ (flag_resident L _ hc)
  · exact List.mem_append_left _ (flag_resident L _ ht)
  · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h' | h'
    · exact List.mem_append_left _ (point_resident L _ h')
    · exact List.mem_append_right _ h'

theorem p1801_pair (t₁ t₂ : Wire) (h1 : t₁ ∈ L.inPlaceFlags) (h2 : t₂ ∈ L.inPlaceFlags)
    (e₁ e₂ : Bool) (C D : Point) : L.core.poolWire 1801 ∉ wires (pairEqual L t₁ t₂ e₁ e₂ C D) := by
  apply p1801_of_subset L hw hn _ 256 (by omega)
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | rfl | rfl | h | h
  · exact List.mem_append_left _ (control_resident L)
  · exact List.mem_append_left _ (point_resident L _ (by simp [PointAddLayout.pointWires, hy]))
  · exact List.mem_append_left _ (flag_resident L _ h1)
  · exact List.mem_append_left _ (flag_resident L _ h2)
  · exact List.mem_append_left _ (point_resident L _ (by simp [PointAddLayout.pointWires, h]))
  · exact List.mem_append_right _ h

theorem finiteProgram_p1801 (C : Point) (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (finiteProgram L C cx cy) := by
  have e1 : L.core.poolWire 1801 ∉ wires (pointInPlaceDoubleEnable L cy) := by
    apply p1801_flags L hw hn _ [L.control, L.core.double] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simp [inPlaceFlags])))
    by_cases hh : cy≠-cy <;> simp [pointInPlaceDoubleEnable,hh,wires,Instr.wires]
  have e2 : L.core.poolWire 1801 ∉ wires (pointDialogExceptionEnable L C) := by
    apply p1801_flags L hw hn _ [L.control, L.core.equalX] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simp [inPlaceFlags])))
    unfold pointDialogExceptionEnable
    split <;> simp [wires,Instr.wires]
  have z (t : Wire) (ht : t ∈ L.inPlaceFlags) :
      L.core.poolWire 1801 ∉ wires (zeroFlag L.point.finite L.control t) := by
    apply p1801_flags L hw hn _ [L.point.finite, L.control, t] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact Or.inr (Or.inr (by simp [PointAddLayout.pointWires]))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ht))
    rw [zeroFlag_wires]; intro q hq; simpa using hq
  have g : L.core.poolWire 1801 ∉ wires (pointDialogGenericFlag L) := by
    apply p1801_flags L hw hn _ [L.control, L.infinitySelect, L.doubleSelect, L.genericSelect,
      L.core.generic, L.core.equalNegY] (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      all_goals exact Or.inr (Or.inl (by simp [inPlaceFlags])))
    intro q hq
    simp [pointDialogGenericFlag, pointInPlaceGenericFlag, wires, Instr.wires] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have m (c : Wire) (hc : c ∈ L.inPlaceFlags) (P : Point) :
      L.core.poolWire 1801 ∉ wires (maskedPointConstant c L.point P) := by
    apply p1801_flags L hw hn _ (c :: PointAddLayout.pointWires L.point) (by
      intro q hq; simp only [List.mem_cons] at hq
      rcases hq with rfl | h
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr h))
    exact maskedPointConstant_support c L.point P
  have fS : L.inPlaceFlags = [L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.generic,
      L.core.equalX,L.core.equalNegY,L.core.double] := rfl
  have s1 := p1801_pair L hw hn L.doubleSelect L.genericSelect (by simp [fS]) (by simp [fS])
    (decide (cy≠-cy)) true C (-C)
  have s3 := p1801_short L hw hn L.core.equalX L.core.equalNegY (Or.inr (by simp [fS])) (by simp [fS])
    (dialogExceptionPoint C)
  have s4 := p1801_pair L hw hn L.infinitySelect L.core.equalNegY (by simp [fS]) (by simp [fS])
    true (exceptionBit C) C (-C)
  have s5 := p1801_short L hw hn L.core.double L.doubleSelect (Or.inr (by simp [fS])) (by simp [fS]) (C+C)
  have z1 := z L.infinitySelect (by simp [fS])
  have z2 := z L.genericSelect (by simp [fS])
  have m1 := m L.infinitySelect (by simp [fS]) C
  have m2 := m L.doubleSelect (by simp [fS]) C
  have m3 := m L.doubleSelect (by simp [fS]) (C+C)
  have m4 := m L.genericSelect (by simp [fS]) (-C)
  have m5 := m L.core.equalNegY (by simp [fS]) (dialogExceptionPoint C)
  have m6 := m L.core.equalNegY (by simp [fS]) (-C)
  have gen := p1801_fastGeneric L hw hn cx cy
  simp only [finiteProgram, pointDialogCorners, pointInPlaceCorners, wires_append, Finset.mem_union,
    not_or]
  tauto

theorem finiteProgram_supportQ (C : Point) (cx cy : Fp) :
    wires (finiteProgram L C cx cy) ⊆ (sitesQ L).toFinset := by
  intro q hq
  have h1 := List.mem_toFinset.mp (finiteProgram_support L hw hn C cx cy hq)
  have h2 : q ≠ L.core.poolWire 1801 := by
    intro e; subst e; exact finiteProgram_p1801 L hw hn C cx cy hq
  exact List.mem_toFinset.mpr (sitesQ_of_sites L q h1 h2)

end

end ECDSAAdd.Entrant
