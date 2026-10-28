import ECDSAAdd.Arithmetic.ConditionalPointAgreement

namespace ECDSAAdd.Arithmetic.PointInputEncoding
open Secp256k1 ControlledPointLayout FiniteUnitary
noncomputable section
local instance : DecidableEq Point := Classical.decEq _

/-- A mathematical clean-state encoding. The constant-XOR circuit is used only
to define the bit string; it is not appended to the evaluated point-add program. -/
def basis (L : ControlledPointLayout) (b : Bool) (R : Point) : BasisState :=
  writeBit (run (maskedPointConstant L.control L.point R) []
    ⟨false,writeBit (fun _ => false) L.control true⟩).basis L.control b

@[simp] theorem control (L : ControlledPointLayout) (b : Bool) (R : Point) :
    basis L b R L.control = b := by simp [basis, writeBit]

private theorem layout_parts (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    (PointAddLayout.pointWires L.point).Nodup ∧
      L.control ∉ PointAddLayout.pointWires L.point := by
  have h := L.dialogUsed_nodup hn
  have hp := List.nodup_append'.mp h
  refine ⟨?_, ?_⟩
  · exact (List.nodup_append'.mp (List.nodup_append'.mp hp.1).1).1
  · have hc : L.control ∈ L.dialogUsedWires := by simp [dialogUsedWires]
    intro hh
    have counts := List.nodup_iff_count.mp h L.control
    have hm := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires, List.count_append, List.count_cons, beq_self_eq_true,
      if_true, List.count_nil] at counts
    omega

theorem point (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R : Point) : Holds.holds (basis L b R) L.point R := by
  obtain ⟨hp,hc⟩ := layout_parts L hn
  let z : State := ⟨false,writeBit (fun _ => false) L.control true⟩
  have he := maskedPointConstant_correct L.control L.point R hp hc hw.inputX hw.inputY z []
  have hz (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : z.basis q = false := by
    have hqc : q ≠ L.control := fun h => hc (h ▸ hq)
    simp [z, writeBit, hqc]
  have hv : ∀ (r : List Wire), r ⊆ PointAddLayout.pointWires L.point → regValue r z.basis = 0 :=
    fun r hr => (regValue_zero r z.basis).mpr (fun q hq => hz q (hr hq))
  have hx := hv L.point.x (by intro q hq; simp [PointAddLayout.pointWires,hq])
  have hy := hv L.point.y (by intro q hq; simp [PointAddLayout.pointWires,hq])
  have hf := hz L.point.finite (by simp [PointAddLayout.pointWires])
  have hread : ∀ q ∈ PointAddLayout.pointWires L.point,
      basis L b R q = (run (maskedPointConstant L.control L.point R) [] z).basis q := by
    intro q hq
    have hqc : q ≠ L.control := fun h => hc (h ▸ hq)
    simp [basis, writeBit, hqc, z]
  apply (point_holds _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [hread _ (by simp [PointAddLayout.pointWires]),he.finite,hf]
    simp [z,writeBit]
  · rw [regValue_congr _ _ _ (fun q hq => hread q (by simp [PointAddLayout.pointWires,hq])),he.x,hx]
    simp [z,writeBit]
  · rw [regValue_congr _ _ _ (fun q hq => hread q (by simp [PointAddLayout.pointWires,hq])),he.y,hy]
    simp [z,writeBit]

theorem outside (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R : Point) (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) :
    basis L b R q = if q = L.control then b else false := by
  obtain ⟨hp,hc⟩ := layout_parts L hn
  have he := maskedPointConstant_correct L.control L.point R hp hc hw.inputX hw.inputY
    ⟨false,writeBit (fun _ => false) L.control true⟩ []
  by_cases h : q = L.control
  · subst q; simp
  · simp only [basis, writeBit, if_neg h]
    simpa [writeBit,h] using he.outside q hq

private theorem work_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q ∈ L.inPlaceFlags ++ L.dialogPool) :
    q ∉ PointAddLayout.pointWires L.point ∧ q ≠ L.control := by
  have h : ((PointAddLayout.pointWires L.point ++ [L.control]) ++
      (L.inPlaceFlags ++ L.dialogPool)).Nodup := by
    simpa only [dialogUsedWires, List.append_assoc] using L.dialogUsed_nodup hn
  have hd := (List.nodup_append'.mp h).2.2
  have ha : q ∉ PointAddLayout.pointWires L.point ++ [L.control] :=
    fun hh => List.disjoint_left.mp hd hh hq
  simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] using ha

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R : Point) : PointDialogBoundary L R b (fun _ => false) (basis L b R) := by
  refine ⟨point L hw hn b R, control L b R, ?_, ?_⟩
  · intro q hq
    have h := work_away L hn q (List.mem_append_left _ hq)
    simp only [outside L hw hn b R q h.1, if_neg h.2]
  · apply (regValue_zero _ _).mpr
    intro q hq
    have h := work_away L hn q (List.mem_append_right _ hq)
    simp only [outside L hw hn b R q h.1, if_neg h.2]

theorem basis_injective (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    Function.Injective (fun x : Bool × Point => basis L x.1 x.2) := by
  intro x y h
  change basis L x.1 x.2 = basis L y.1 y.2 at h
  have hb : x.1 = y.1 := by simpa only [control] using congrFun h L.control
  have hr : x.2 = y.2 := by
    apply pointCode_injective
    rw [←pointCode_register L.point x.2 (basis L x.1 x.2) hw.inputX (point L hw hn _ _),
      ←pointCode_register L.point y.2 (basis L y.1 y.2) hw.inputX (point L hw hn _ _), h]
  exact Prod.ext hb hr

/-- Only the point and control registers carry input data. All other bits,
including the complete implementation workspace, start at zero. -/
def Bounded (L : ControlledPointLayout) (n : Nat) : Prop :=
  ∀ q ∈ PointAddLayout.pointWires L.point ++ [L.control], q < n

theorem extend_restrict (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {n : Nat} (hb : Bounded L n) (b : Bool) (R : Point) :
    extend (restrict n (basis L b R)) = basis L b R := by
  funext q
  by_cases hq : q < n
  · simp [extend, restrict, hq]
  · have hp : q ∉ PointAddLayout.pointWires L.point :=
      fun h => hq (hb q (List.mem_append_left _ h))
    have hc : q ≠ L.control := by
      intro h
      subst q
      exact hq (hb _ (by simp))
    simp [extend,hq,outside L hw hn b R q hp,hc]

def encoding (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {n : Nat} (hb : Bounded L n) : (Bool × Point) ↪ Bits n where
  toFun x := restrict n (basis L x.1 x.2)
  inj' := by
    intro x y h
    apply basis_injective L hw hn
    have he := congrArg (@extend n) h
    simpa only [extend_restrict L hw hn hb] using he

theorem encoding_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {n : Nat} (hb : Bounded L n) (x : Bool × Point) :
    PointDialogBoundary L x.2 x.1 (fun _ => false) (extend (encoding L hw hn hb x)) := by
  change PointDialogBoundary L x.2 x.1 _ (extend (restrict n (basis L x.1 x.2)))
  rw [extend_restrict L hw hn hb]
  exact boundary L hw hn x.1 x.2

theorem encoding_frame (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {n : Nat} (hb : Bounded L n) (C : Point) (x : Bool × Point)
    (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) :
    extend (encoding L hw hn hb (ConditionalPointDialog.pointAddPerm C x)) q =
      extend (encoding L hw hn hb x) q := by
  change extend (restrict n (basis L x.1 (if x.1 then x.2+C else x.2))) q =
    extend (restrict n (basis L x.1 x.2)) q
  rw [extend_restrict L hw hn hb, extend_restrict L hw hn hb,
    outside L hw hn _ _ q hq, outside L hw hn _ _ q hq]

/-- A finite instance from the proved canonical 513-bit point code, without
assuming the curve point count or a cryptographic group-order theorem. -/
noncomputable def pointFintype : Fintype Point :=
  Fintype.ofInjective (fun R : Point => (⟨pointCode R, pointCode_lt R⟩ : Fin (2^513)))
    (fun _ _ h => pointCode_injective (congrArg Fin.val h))

/-- The encoding and frame obligations of the complete conditional point-add
quantum theorem are now discharged by a concrete clean-state encoding. -/
theorem budget [Fintype (Bool × Point)]
    (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    {n l : Nat} (c : RecordedQuantum.Circuit n 0 l)
    (hc : c.program = ConditionalPointDialog.program backend L C)
    (hb : Bounded L n) (μ : FailureBudget.InputLaw (Bool × Point))
    (bad : Finset (Bool × Point)) (ε : ℝ) (he : 0 ≤ ε) (hlt : ε < 1)
    (hm : μ.mass bad ≤ ε)
    (hsafe : ∀ x, x ∉ bad → ConditionalPointDialog.Safe backend x.1 x.2 C) :
    FailureBudget.QuantumBudget (RecordedQuantum.actual c).toContinuousLinearMap
      (RecordedQuantum.ideal l (FailureBudget.encodedPerm (encoding L hw hn hb)
        (ConditionalPointDialog.pointAddPerm C))).toContinuousLinearMap
      (μ.push (encoding L hw hn hb)) (FailureBudget.encodedBad (encoding L hw hn hb) bad) ε := by
  classical
  exact ConditionalPointDialog.pointAdd_budget backend L hw hn C c hc (encoding L hw hn hb)
    μ bad ε he hlt hm (encoding_boundary L hw hn hb) (encoding_frame L hw hn hb C) hsafe

end
end ECDSAAdd.Arithmetic.PointInputEncoding
