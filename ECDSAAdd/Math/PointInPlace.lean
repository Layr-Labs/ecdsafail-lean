import ECDSAAdd.Math.AffineFormula

namespace ECDSAAdd.Secp256k1

/-- 有限曲线点同横坐标，当且仅当两点相同或互为相反点。 -/
theorem sameX_iff_eq_or_neg {x y cx cy : Fp}
    (hr : curve.toAffine.Nonsingular x y) (hc : curve.toAffine.Nonsingular cx cy) :
    x=cx ↔ (.some hr : Point)=.some hc ∨ (.some hr : Point)=-(.some hc : Point) := by
  constructor
  · intro hx
    by_cases hy : y = -cy
    · right
      rw [WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, by simpa only [negY_eq_neg] using hy⟩
    · left
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, y_eq_of_x_eq_of_not_inverse hr hc hx hy⟩
  · rintro (h | h)
    · exact (WeierstrassCurve.Affine.Point.some.inj h).1
    · rw [WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq] at h
      exact h.1

/-- 普通分支恰好排除 O、C、−C；不要求 C 与 −C 不同。 -/
theorem ordinary_point_iff (R : Point) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    ((coordinates R).isSome=true ∧ ((coordinates R).getD (0,0)).1≠cx) ↔
      R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) := by
  cases R with
  | zero => simp [coordinates, ← WeierstrassCurve.Affine.Point.zero_def]
  | @some x y hr =>
    simp only [coordinates, Option.isSome_some, Option.getD_some, true_and]
    have hh := not_congr (sameX_iff_eq_or_neg hr hc)
    constructor
    · intro hx
      exact ⟨WeierstrassCurve.Affine.Point.some_ne_zero hr, not_or.mp (hh.mp hx)⟩
    · rintro ⟨_, ha, hb⟩
      exact hh.mpr (not_or.mpr ⟨ha,hb⟩)

/-- 构造期纵坐标条件正好识别 C 与 −C 是否不同；退化时禁用倍点标志。 -/
theorem doubling_enabled_iff {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    cy≠-cy ↔ (.some hc : Point)≠-(.some hc : Point) := by
  simp only [ne_eq, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq, negY_eq_neg, true_and]

/-- 输出侧重算输入的三个角落标志；控制为 false 时每个谓词仍为假。 -/
theorem translated_point_flags (R C : Point) (b : Bool) :
    let R' := if b then R+C else R
    ((b=true ∧ R'=C) ↔ (b=true ∧ R=0)) ∧
    ((b=true ∧ C≠-C ∧ R'=C+C) ↔ (b=true ∧ C≠-C ∧ R=C)) ∧
    ((b=true ∧ R'=0) ↔ (b=true ∧ R=-C)) := by
  cases b <;> simp [add_eq_zero_iff_eq_neg]

/-- 12 步原地流程中的三个域等式：清 y、更新 x、重建 y。 -/
theorem generic_inplace_values (x y cx cy : Fp) (hx : x≠cx) :
    let l := genericSlope x y cx cy
    (y-cy)-l*(x-cx)=0 ∧
    (x-cx)-l*l+3*cx=cx-genericX x y cx cy ∧
    l*(cx-genericX x y cx cy)-cy=genericY x y cx cy := by
  dsimp only
  have he : genericSlope x y cx cy * (x-cx) = y-cy := by
    simp only [genericSlope, genericNumerator, genericDenominator]
    field_simp [sub_ne_zero.mpr hx]
  refine ⟨sub_eq_zero.mpr he.symm, ?_, ?_⟩
  · unfold genericX
    ring
  · unfold genericY
    linear_combination -he

/-- 第二个除数为零只会发生在输入 −2C；该结论以普通分支为前提。 -/
theorem second_denominator_zero_iff {x y cx cy : Fp}
    (hr : curve.toAffine.Nonsingular x y) (hc : curve.toAffine.Nonsingular cx cy)
    (hx : x≠cx) :
    cx-genericX x y cx cy=0 ↔ (.some hr : Point)=-((.some hc : Point)+.some hc) := by
  let R : Point := .some hr
  let C : Point := .some hc
  constructor
  · intro hz
    have hs : R+C=C ∨ R+C=-C := by
      rw [← genericAdd_correct hr hc hx]
      exact (sameX_iff_eq_or_neg (generic_nonsingular hr hc hx) hc).mp
        (sub_eq_zero.mp hz).symm
    rcases hs with hs | hs
    · have hR : R=0 := add_right_cancel (hs.trans (zero_add C).symm)
      exact False.elim (WeierstrassCurve.Affine.Point.some_ne_zero hr hR)
    · change R=-(C+C)
      calc
        R = (R+C)-C := by abel
        _ = -C-C := by rw [hs]
        _ = -(C+C) := by abel
  · intro hR
    have hs : R+C=-C := by
      change (.some hr : Point)+(.some hc : Point)=-(.some hc : Point)
      rw [hR]
      abel
    have he := congrArg coordinates ((genericAdd_correct hr hc hx).trans hs)
    simp only [C, genericAdd, WeierstrassCurve.Affine.Point.neg_some, coordinates,
      Option.some.injEq, Prod.mk.injEq] at he
    exact sub_eq_zero.mpr he.1.symm

/-- 例外斜率是编译期常量；O 的坐标按现有编码取零，使定义全域成立。 -/
def exceptionalSlope (C : Point) : Fp :=
  let r := (coordinates (-(C+C))).getD (0,0)
  let c := (coordinates C).getD (0,0)
  genericSlope r.1 r.2 c.1 c.2

/-- 例外分支下该常量就是当前斜率，可由受控常量 XOR 清零。 -/
theorem exceptional_slope_eq {x y cx cy : Fp}
    (hr : curve.toAffine.Nonsingular x y) (hc : curve.toAffine.Nonsingular cx cy)
    (hx : x≠cx) (hz : cx-genericX x y cx cy=0) :
    genericSlope x y cx cy = exceptionalSlope (.some hc) := by
  have he := (second_denominator_zero_iff hr hc hx).mp hz
  unfold exceptionalSlope
  rw [← he]
  rfl

/-- 第二除数非零时，从当前 y 与 x 重算斜率；供减法清理 λ。 -/
theorem slope_from_output (x y cx cy : Fp) (hx : x≠cx)
    (hd : cx-genericX x y cx cy≠0) :
    (genericY x y cx cy+cy) / (cx-genericX x y cx cy) = genericSlope x y cx cy := by
  have he := (generic_inplace_values x y cx cy hx).2.2
  rw [← he]
  field_simp
  ring

end ECDSAAdd.Secp256k1
