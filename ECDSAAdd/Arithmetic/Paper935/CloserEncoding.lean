import ECDSAAdd.Arithmetic.Paper935.WindowBank

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

private theorem signed_split (row : WindowRow) (s : BasisState) :
    row.value s=(regValue row.payload s:Int)-
      (if s row.sign then ((2^row.payload.length:Nat):Int) else 0) := by
  rw [WindowRow.value,WindowRow.wires,signedRegValue_msb,regValue_append]
  cases hs : s row.sign <;>
    simp [regValue,hs,Nat.pow_succ,Nat.cast_add,Nat.cast_mul]
  all_goals ring

theorem closer_row_zero (row : WindowRow) (s : BasisState) (value : row.value s=0) :
    s row.sign=false ∧ ∀ q∈row.payload,s q=false := by
  have sign := signedRegValue_neg_iff row.payload row.sign s
  change row.value s<0 ↔ s row.sign=true at sign
  have hs : s row.sign=false := by
    cases h : s row.sign with
    | false => rfl
    | true => have bad := sign.mpr h; omega
  refine ⟨hs,?_⟩
  have raw := signed_split row s
  rw [value,hs] at raw
  simp only [Bool.false_eq_true,if_false,sub_zero] at raw
  apply (regValue_zero row.payload s).mp
  omega

/-- The physical payload encoding of either sign of a positive magnitude. -/
theorem closer_row_magnitude (row : WindowRow) (s : BasisState) (k : Nat)
    (positive : 0<k) (small : k<2^row.payload.length)
    (magnitude : (row.value s).natAbs=k) :
    regValue row.payload s=if s row.sign then 2^row.payload.length-k else k := by
  have sign := signedRegValue_neg_iff row.payload row.sign s
  change row.value s<0 ↔ s row.sign=true at sign
  have raw := signed_split row s
  have casesValue := Int.natAbs_eq_iff.mp magnitude
  cases hs : s row.sign with
  | false =>
    have nonneg : ¬row.value s<0 := by intro h; have bad := sign.mp h; simp [hs] at bad
    simp only [hs,Bool.false_eq_true,if_false,sub_zero] at raw ⊢
    rcases casesValue with h | h <;> omega
  | true =>
    have negative := sign.mpr hs
    simp only [hs,if_true] at raw ⊢
    rcases casesValue with h | h <;> omega

theorem closer_signs (f gv : WindowRow) (s : BasisState) (p : Nat) (positive : 0<p)
    (value : gv.value s=f.value s*p) : s gv.sign=s f.sign := by
  have fsign := signedRegValue_neg_iff f.payload f.sign s
  have gvsign := signedRegValue_neg_iff gv.payload gv.sign s
  change f.value s<0 ↔ s f.sign=true at fsign
  change gv.value s<0 ↔ s gv.sign=true at gvsign
  apply Bool.eq_iff_iff.mpr
  rw [←fsign,←gvsign,value]
  have hp : (0:Int)<p := by exact_mod_cast positive
  constructor <;> intro h <;> nlinarith

end ECDSAAdd.Arithmetic.Paper935
