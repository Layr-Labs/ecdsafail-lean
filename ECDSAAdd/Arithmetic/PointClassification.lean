import ECDSAAdd.Arithmetic.PointCandidateSpec

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 点的规范编码；这些函数也可用于任意目标位串的 XOR 规格。 -/
def pointFinite (R : Point) : Bool := (coordinates R).isSome
def pointX (R : Point) : Nat := ((coordinates R).getD (0,0)).1.val
def pointY (R : Point) : Nat := ((coordinates R).getD (0,0)).2.val

def pointGeneric (R : Point) (cx : Fp) : Bool :=
  pointFinite R && !decide (pointX R=cx.val)
def pointDouble (R : Point) (cx cy : Fp) : Bool :=
  pointFinite R && decide (pointX R=cx.val) && !decide (pointY R=(-cy).val)

theorem point_holds (r : PointReg) (R : Point) (s : BasisState) :
    Holds.holds s r R ↔ s r.finite=pointFinite R ∧
      regValue r.x s=pointX R ∧ regValue r.y s=pointY R := by
  cases R <;> rfl

theorem point_coordinates_lt (R : Point) : pointX R<p ∧ pointY R<p := by
  cases R with
  | zero => norm_num [pointX,pointY,coordinates,p]
  | some h => exact ⟨ZMod.val_lt _,ZMod.val_lt _⟩

theorem pointGeneric_domain (R : Point) (cx : Fp) (h : pointGeneric R cx=true) :
    pointFinite R=true ∧ pointX R≠cx.val := by
  simpa [pointGeneric] using h

/-- 四个分支完全覆盖合法点。倍点常量允许为 O，不添加纵坐标非零前提。 -/
theorem point_classification (R : Point) (cx cy : Fp)
    (hc : curve.toAffine.Nonsingular cx cy) :
    let C : Point := .some hc
    let V := candidateResult (pointGeneric R cx) (pointX R) (pointY R) cx.val cy.val
    (pointFinite (R+C),pointX (R+C),pointY (R+C)) =
      if !pointFinite R then (true,cx.val,cy.val)
      else if pointGeneric R cx then (true,V .x,V .y)
      else if pointDouble R cx cy then (pointFinite (C+C),pointX (C+C),pointY (C+C))
      else (false,0,0) := by
  dsimp only
  cases R with
  | zero =>
    change (pointFinite ((0 : Point)+_),pointX ((0 : Point)+_),pointY ((0 : Point)+_))=_
    rw [zero_add]
    rfl
  | @some x y hr =>
    have heq (a b : Fp) : a.val=b.val ↔ a=b := ⟨fun h => ZMod.val_injective p h,congrArg ZMod.val⟩
    by_cases hx : x=cx
    · by_cases hy : y= -cy
      · rw [inverseAdd_correct hr hc hx hy]
        simp [pointFinite,pointX,pointY,coordinates,pointGeneric,pointDouble,hx,hy]
      · have hyy := y_eq_of_x_eq_of_not_inverse hr hc hx hy
        subst x; subst y
        simp [pointFinite,pointX,pointY,coordinates,pointGeneric,pointDouble,heq,hy]
    · have hv := candidateResult_coordinates true x y cx cy
      have hg := pointCandidateValues_generic x y cx cy
      rw [← genericAdd_correct hr hc hx]
      simp only [genericAdd,pointFinite,pointX,pointY,coordinates,Option.isSome_some,
        Option.getD_some,Bool.not_true,Bool.false_eq_true,if_false]
      simp only [pointGeneric,pointDouble,pointFinite,pointX,pointY,coordinates,
        Option.isSome_some,Option.getD_some,heq,hx,decide_false,Bool.not_false,
        Bool.true_and,if_true]
      rw [hv.1,hv.2,hg.1,hg.2]


theorem point_classification_xor (R : Point) (cx cy : Fp)
    (hc : curve.toAffine.Nonsingular cx cy) :
    let C : Point := .some hc
    let G := pointGeneric R cx
    let D := pointDouble R cx cy
    let V := candidateResult G (pointX R) (pointY R) cx.val cy.val
    (G ^^ (D && pointFinite (C+C)) ^^ (!pointFinite R && pointFinite C),
      (if G then V .x else 0) ^^^ (if D then pointX (C+C) else 0) ^^^ (if !pointFinite R then pointX C else 0),
      (if G then V .y else 0) ^^^ (if D then pointY (C+C) else 0) ^^^ (if !pointFinite R then pointY C else 0)) =
    (pointFinite (R+C),pointX (R+C),pointY (R+C)) := by
  dsimp only
  rw [point_classification R cx cy hc]
  cases R with
  | zero => simp [pointGeneric,pointDouble,pointFinite,pointX,pointY,coordinates]
  | @some x y hr =>
    by_cases hx : x.val=cx.val
    · by_cases hy : y.val=(-cy).val <;>
        simp [pointGeneric,pointDouble,pointFinite,pointX,pointY,coordinates,hx,hy]
    · simp [pointGeneric,pointDouble,pointFinite,pointX,pointY,coordinates,hx]

theorem candidateResult_xy_lt (G : Bool) (X Y : Nat) (cx cy : Fp) (hx : X<p) (hy : Y<p) :
    candidateResult G X Y cx.val cy.val .x<p ∧ candidateResult G X Y cx.val cy.val .y<p := by
  have hX : (X : Fp).val=X := by rw [ZMod.val_natCast,Nat.mod_eq_of_lt hx]
  have hY : (Y : Fp).val=Y := by rw [ZMod.val_natCast,Nat.mod_eq_of_lt hy]
  have hh := candidateResult_coordinates G (X : Fp) (Y : Fp) cx cy
  rw [hX,hY] at hh
  rw [hh.1,hh.2]
  exact ⟨ZMod.val_lt _,ZMod.val_lt _⟩

end ECDSAAdd.Arithmetic
