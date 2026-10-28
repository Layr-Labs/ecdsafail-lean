import ECDSAAdd.Math.PointInPlace

namespace ECDSAAdd.Secp256k1

/-- 六阶段流程第二分母为零的唯一额外输入。 -/
def dialogExceptionPoint (C : Point) : Point := -(C+C)

/-- 只启用未被 O、倍点、相反点分支覆盖的新例外。 -/
def dialogExceptionEnabled (C : Point) : Prop :=
  dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C

/-- 禁用重合的经典例外不会遗漏输入；尤其不假定不存在二阶点。 -/
theorem dialog_generic_iff (R C : Point) :
    (R≠0 ∧ (C≠-C → R≠C) ∧ R≠-C ∧ (dialogExceptionEnabled C → R≠dialogExceptionPoint C)) ↔
    (R≠0 ∧ R≠C ∧ R≠-C ∧ R≠dialogExceptionPoint C) := by
  constructor
  · rintro ⟨ho,hd,hi,hh⟩
    have hrc : R≠C := by
      by_cases hc : C=-C
      · exact fun he => hi (he.trans hc)
      · exact hd hc
    refine ⟨ho,hrc,hi,?_⟩
    intro he
    have hen : dialogExceptionEnabled C := by
      unfold dialogExceptionEnabled
      rw [← he]
      exact ⟨ho,hrc,hi⟩
    exact hh hen he
  · rintro ⟨ho,hd,hi,hh⟩
    exact ⟨ho,fun _ => hd,hi,fun _ => hh⟩

/-- 普通路径同时具有两个非零分母，不给点加规格添加新前提。 -/
theorem dialog_denominators_ne_zero {x y cx cy : Fp}
    (hr : curve.toAffine.Nonsingular x y) (hc : curve.toAffine.Nonsingular cx cy)
    (hR : (.some hr : Point)≠(.some hc : Point)) (hI : (.some hr : Point)≠-(.some hc : Point))
    (hH : (.some hr : Point)≠dialogExceptionPoint (.some hc)) :
    x≠cx ∧ cx-genericX x y cx cy≠0 := by
  have hx : x≠cx := by
    intro he
    rcases (sameX_iff_eq_or_neg hr hc).mp he with he|he
    · exact hR he
    · exact hI he
  exact ⟨hx,fun hz => hH ((second_denominator_zero_iff hr hc hx).mp hz)⟩

/-- 新例外的输出恒为 −C。 -/
theorem dialog_exception_add (C : Point) : dialogExceptionPoint C+C=-C := by
  unfold dialogExceptionPoint
  abel

/-- 从输出 −C 重算第四标志，控制为假时也成立。 -/
theorem dialog_translated_exception (R C : Point) (b : Bool) :
    let R' := if b then R+C else R
    (b=true ∧ dialogExceptionEnabled C ∧ R'=-C) ↔
      (b=true ∧ dialogExceptionEnabled C ∧ R=dialogExceptionPoint C) := by
  have he : R+C=-C ↔ R=dialogExceptionPoint C := by
    constructor
    · intro hh
      apply add_right_cancel (b:=C)
      rw [hh,dialog_exception_add]
    · intro hh; rw [hh,dialog_exception_add]
  cases b <;> simp [he]

/-- 四类输入标志两两互斥；倍点类与 H 类均有经典使能条件。 -/
theorem dialog_input_disjoint (R C : Point) (b : Bool) (hC : C≠0) :
    let o := b=true ∧ R=0
    let d := b=true ∧ C≠-C ∧ R=C
    let i := b=true ∧ R=-C
    let h := b=true ∧ dialogExceptionEnabled C ∧ R=dialogExceptionPoint C
    ¬(o∧d) ∧ ¬(o∧i) ∧ ¬(o∧h) ∧ ¬(d∧i) ∧ ¬(d∧h) ∧ ¬(i∧h) := by
  dsimp only
  have hn : -C≠0 := neg_ne_zero.mpr hC
  simp only [dialogExceptionEnabled]
  constructor
  · rintro ⟨⟨_,ho⟩,_,_,hd⟩; exact hC (hd.symm.trans ho)
  constructor
  · rintro ⟨⟨_,ho⟩,_,hi⟩; exact hn (hi.symm.trans ho)
  constructor
  · rintro ⟨⟨_,ho⟩,_,hh,he⟩; exact hh.1 (he.symm.trans ho)
  constructor
  · rintro ⟨⟨_,hd,he⟩,_,hi⟩; exact hd (he.symm.trans hi)
  constructor
  · rintro ⟨⟨_,_,hd⟩,_,hh,he⟩; exact hh.2.1 (he.symm.trans hd)
  · rintro ⟨⟨_,hi⟩,_,hh,he⟩; exact hh.2.2 (he.symm.trans hi)

/-- 输入分支平移到输出分支，四个谓词逐项一致。 -/
theorem dialog_translated_flags (R C : Point) (b : Bool) :
    let R' := if b then R+C else R
    ((b=true ∧ R'=C) ↔ (b=true ∧ R=0)) ∧
    ((b=true ∧ C≠-C ∧ R'=C+C) ↔ (b=true ∧ C≠-C ∧ R=C)) ∧
    ((b=true ∧ R'=0) ↔ (b=true ∧ R=-C)) ∧
    ((b=true ∧ dialogExceptionEnabled C ∧ R'=-C) ↔
      (b=true ∧ dialogExceptionEnabled C ∧ R=dialogExceptionPoint C)) := by
  have ht := translated_point_flags R C b
  exact ⟨ht.1,ht.2.1,ht.2.2,dialog_translated_exception R C b⟩

/-- 输出检测的四类也互斥，无需假设 C≠−C。 -/
theorem dialog_output_disjoint (R C : Point) (b : Bool) (hC : C≠0) :
    let R' := if b then R+C else R
    let o := b=true ∧ R'=C
    let d := b=true ∧ C≠-C ∧ R'=C+C
    let i := b=true ∧ R'=0
    let h := b=true ∧ dialogExceptionEnabled C ∧ R'=-C
    ¬(o∧d) ∧ ¬(o∧i) ∧ ¬(o∧h) ∧ ¬(d∧i) ∧ ¬(d∧h) ∧ ¬(i∧h) := by
  dsimp only
  have ht := dialog_translated_flags R C b
  rw [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
  exact dialog_input_disjoint R C b hC

end ECDSAAdd.Secp256k1
