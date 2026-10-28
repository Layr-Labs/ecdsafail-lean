import ECDSAAdd.Arithmetic.PointInPlaceGenericPoint

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 三个角落位依次为O、启用的倍点和相反点；完整点编码用于检测。 -/
def inPlaceInfinity (b : Bool) (R : Point) : Bool := b && pointEqual R 0
def inPlaceDouble (b : Bool) (R C : Point) : Bool := b && !pointEqual C (-C) && pointEqual R C
def inPlaceInversePoint (b : Bool) (R C : Point) : Bool := b && pointEqual R (-C)
def inPlaceOrdinary (b : Bool) (R C : Point) : Bool :=
  ((b ^^ inPlaceInfinity b R) ^^ inPlaceDouble b R C) ^^ inPlaceInversePoint b R C

private theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C = decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

/-- XOR分类不重叠；C=-C时禁用倍点，所以也覆盖二阶点。 -/
theorem inPlaceOrdinary_true (b : Bool) (R C : Point) (hc : C≠0) :
    inPlaceOrdinary b R C=true ↔ b=true ∧ R≠0 ∧ R≠C ∧ R≠-C := by
  classical
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  by_cases h0 : R=0
  · subst R
    simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,
      Ne.symm hc,Ne.symm hnc]
  by_cases h1 : R=C
  · subst R
    by_cases h2 : C=-C
    · have he : (C=-C) ↔ True := iff_true_intro h2
      cases b <;> simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,he]
    · cases b <;> simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,h2]
  by_cases h2 : R=-C
  · subst R
    cases b <;> simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hnc,h1]
  cases b <;> simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,h0,h1,h2]

/-- 输出侧检测重建原输入的三个角落位。 -/
theorem inPlaceFlags_output (b : Bool) (R C : Point) :
    let S := if b then R+C else R
    (b && pointEqual S C)=inPlaceInfinity b R ∧
    (b && !pointEqual C (-C) && pointEqual S (C+C))=inPlaceDouble b R C ∧
    (b && pointEqual S 0)=inPlaceInversePoint b R C := by
  classical
  have hh := translated_point_flags R C b
  simp only [inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp]
  apply And.intro
  · apply Bool.eq_iff_iff.mpr
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using hh.1
  constructor
  · apply Bool.eq_iff_iff.mpr
    simpa only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not,← and_assoc] using hh.2.1
  · apply Bool.eq_iff_iff.mpr
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using hh.2.2

/-- 三个角落的XOR写回，对任意零点编码为0的自然数字段成立。 -/
theorem inPlaceCorners_nat (b : Bool) (R C : Point) (hc : C≠0) (f : Point → Nat) (hf : f 0=0) :
    (((f (if inPlaceOrdinary b R C then R+C else R) ^^^
      (if inPlaceInfinity b R then f C else 0)) ^^^
      (if inPlaceDouble b R C then f C else 0)) ^^^
      (if inPlaceDouble b R C then f (C+C) else 0)) ^^^
      (if inPlaceInversePoint b R C then f (-C) else 0) = f (if b then R+C else R) := by
  classical
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,
        Ne.symm hc,Ne.symm hnc,hf]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have hz : C+C=0 := add_eq_zero_iff_eq_neg.mpr h2
        simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,hz,hf,← h2]
      · simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hnc,h1,hf]
    simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,h0,h1,h2]
/-- 三个角落的XOR写回，对任意零点编码为0的布尔字段成立。 -/
theorem inPlaceCorners_bool (b : Bool) (R C : Point) (hc : C≠0) (f : Point → Bool) (hf : f 0=false) :
    ((((f (if inPlaceOrdinary b R C then R+C else R) ^^
      (if inPlaceInfinity b R then f C else false)) ^^
      (if inPlaceDouble b R C then f C else false)) ^^
      (if inPlaceDouble b R C then f (C+C) else false)) ^^
      (if inPlaceInversePoint b R C then f (-C) else false)) = f (if b then R+C else R) := by
  classical
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,
        Ne.symm hc,Ne.symm hnc,hf]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have hz : C+C=0 := add_eq_zero_iff_eq_neg.mpr h2
        simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,hz,hf,← h2]
      · simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,hnc,h1,hf]
    simp [inPlaceOrdinary,inPlaceInfinity,inPlaceDouble,inPlaceInversePoint,equal_simp,h0,h1,h2]

end ECDSAAdd.Arithmetic
