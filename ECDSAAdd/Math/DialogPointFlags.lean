import ECDSAAdd.Math.DialogPoint

namespace ECDSAAdd.Secp256k1
variable [DecidableEq Point]

def dialogInfinity (b : Bool) (R : Point) : Bool := b && decide (R=0)
def dialogDouble (b : Bool) (R C : Point) : Bool := b && decide (C≠-C) && decide (R=C)
def dialogInversePoint (b : Bool) (R C : Point) : Bool := b && decide (R=-C)
def dialogException (b : Bool) (R C : Point) : Bool :=
  b && decide (dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C) &&
    decide (R=dialogExceptionPoint C)
def dialogOrdinary (b : Bool) (R C : Point) : Bool :=
  b ^^ dialogInfinity b R ^^ dialogDouble b R C ^^ dialogInversePoint b R C ^^ dialogException b R C

@[simp] theorem dialogException_zero (b : Bool) (C : Point) : dialogException b 0 C=false := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.false_eq_true, iff_false, dialogException,Bool.and_eq_true,decide_eq_true_eq]
  rintro ⟨⟨_,he⟩,hr⟩
  exact he.1 hr.symm

@[simp] theorem dialogException_self (b : Bool) (C : Point) : dialogException b C C=false := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.false_eq_true, iff_false, dialogException,Bool.and_eq_true,decide_eq_true_eq]
  rintro ⟨⟨_,he⟩,hr⟩
  exact he.2.1 hr.symm

@[simp] theorem dialogException_neg (b : Bool) (C : Point) : dialogException b (-C) C=false := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.false_eq_true, iff_false, dialogException,Bool.and_eq_true,decide_eq_true_eq]
  rintro ⟨⟨_,he⟩,hr⟩
  exact he.2.2 hr.symm

/-- 四个互斥角落的XOR余位正好选择普通分支。 -/
theorem dialogOrdinary_true (b : Bool) (R C : Point) (hc : C≠0) :
    dialogOrdinary b R C=true ↔
      b=true ∧ R≠0 ∧ R≠C ∧ R≠-C ∧ R≠dialogExceptionPoint C := by
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,
        Ne.symm hc,Ne.symm hnc]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have he : (C=-C) ↔ True := iff_true_intro h2
        simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,he]
      · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hnc,h1]
    by_cases hh : R=dialogExceptionPoint C
    · have hen : dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C := by
        rw [← hh]; exact ⟨h0,h1,h2⟩
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,hh,hen]
    · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,h0,h1,h2,hh]

/-- 输出检测重算四个布尔标志，可对接pointEqual的decide桥。 -/
theorem dialogFlags_output (b : Bool) (R C : Point) :
    let S := if b then R+C else R
    (b && decide (S=C))=dialogInfinity b R ∧
    (b && decide (C≠-C) && decide (S=C+C))=dialogDouble b R C ∧
    (b && decide (S=0))=dialogInversePoint b R C ∧
    (b && decide (dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C) &&
      decide (S=-C))=dialogException b R C := by
  have ht := dialog_translated_flags R C b
  dsimp only
  simp only [dialogInfinity,dialogDouble,dialogInversePoint,dialogException]
  refine ⟨?_,?_,?_,?_⟩ <;> apply Bool.eq_iff_iff.mpr
  · simpa only [Bool.and_eq_true,decide_eq_true_eq] using ht.1
  · simpa only [Bool.and_eq_true,decide_eq_true_eq,← and_assoc] using ht.2.1
  · simpa only [Bool.and_eq_true,decide_eq_true_eq] using ht.2.2.1
  · simpa only [Bool.and_eq_true,decide_eq_true_eq,dialogExceptionEnabled,← and_assoc] using ht.2.2.2


/-- 四类角落的XOR写回，包含H与−C两次常量更新。 -/
theorem dialogCorners_nat (b : Bool) (R C : Point) (hc : C≠0) (f : Point → Nat) (hf : f 0=0) :
    ((((((f (if dialogOrdinary b R C then R+C else R) ^^^
      (if dialogInfinity b R then f C else 0)) ^^^
      (if dialogDouble b R C then f C else 0)) ^^^
      (if dialogDouble b R C then f (C+C) else 0)) ^^^
      (if dialogInversePoint b R C then f (-C) else 0)) ^^^
      (if dialogException b R C then f (dialogExceptionPoint C) else 0)) ^^^
      (if dialogException b R C then f (-C) else 0) ) = f (if b then R+C else R) := by
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,
        Ne.symm hc,Ne.symm hnc,hf]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have hz : C+C=0 := add_eq_zero_iff_eq_neg.mpr h2
        simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,hz,hf,← h2]
      · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hnc,h1,hf]
    by_cases hh : R=dialogExceptionPoint C
    · have hen : dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C := by
        rw [← hh]; exact ⟨h0,h1,h2⟩
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,hh,hen,dialog_exception_add]
    · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,h0,h1,h2,hh]


/-- 四类角落的XOR写回，包含H与−C两次常量更新。 -/
theorem dialogCorners_bool (b : Bool) (R C : Point) (hc : C≠0) (f : Point → Bool) (hf : f 0=false) :
    ((((((f (if dialogOrdinary b R C then R+C else R) ^^
      (if dialogInfinity b R then f C else false)) ^^
      (if dialogDouble b R C then f C else false)) ^^
      (if dialogDouble b R C then f (C+C) else false)) ^^
      (if dialogInversePoint b R C then f (-C) else false)) ^^
      (if dialogException b R C then f (dialogExceptionPoint C) else false)) ^^
      (if dialogException b R C then f (-C) else false) ) = f (if b then R+C else R) := by
  have hnc : -C≠0 := neg_ne_zero.mpr hc
  cases b with
  | false => simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException]
  | true =>
    by_cases h0 : R=0
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,
        Ne.symm hc,Ne.symm hnc,hf]
    by_cases h1 : R=C
    · subst R
      by_cases h2 : C=-C
      · have hz : C+C=0 := add_eq_zero_iff_eq_neg.mpr h2
        simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,hz,hf,← h2]
      · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hc,h2]
    by_cases h2 : R=-C
    · subst R
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,hnc,h1,hf]
    by_cases hh : R=dialogExceptionPoint C
    · have hen : dialogExceptionPoint C≠0 ∧ dialogExceptionPoint C≠C ∧ dialogExceptionPoint C≠-C := by
        rw [← hh]; exact ⟨h0,h1,h2⟩
      simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,hh,hen,dialog_exception_add]
    · simp [dialogOrdinary,dialogInfinity,dialogDouble,dialogInversePoint,dialogException,h0,h1,h2,hh]

end ECDSAAdd.Secp256k1
