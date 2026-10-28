import ECDSAAdd.Arithmetic.SquareReduce

namespace ECDSAAdd.Arithmetic
namespace SquareReduceLayout

theorem value_length (L : SquareReduceLayout) (hw : L.Widths) : L.value.length=256 := by
  simp [value,hw.r]
theorem quotient_length (L : SquareReduceLayout) (hw : L.Widths) : L.quotient.length=33 := by
  simp [quotient,hw.r]
theorem extended_length (L : SquareReduceLayout) (hw : L.Widths) : L.extended.length=257 := by
  simp [extended,L.value_length hw]
theorem value_quotient (L : SquareReduceLayout) : L.value++L.quotient=L.r :=
  List.take_append_drop _ _

theorem first_nodup (L : SquareReduceLayout) (hn : L.wires.Nodup) :
    (L.cin::(L.high++L.r++L.pad++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  simp only [wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem second_nodup (L : SquareReduceLayout) (hn : L.wires.Nodup) :
    (L.cin::(L.quotient++L.extended++L.pad++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  have he := congrArg (List.count w) L.value_quotient
  simp only [List.count_append] at he
  simp only [wires,extended,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem value_read (L : SquareReduceLayout) (hw : L.Widths) (s : BasisState) :
    regValue L.value s=regValue L.r s%SquareReduction.B := by
  rw [←L.value_quotient,regValue_append,L.value_length hw]
  simp only [SquareReduction.B,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by simpa [L.value_length hw] using regValue_lt L.value s)).symm

theorem quotient_read (L : SquareReduceLayout) (hw : L.Widths) (s : BasisState) :
    regValue L.quotient s=regValue L.r s/SquareReduction.B := by
  have he := regValue_append L.value L.quotient s
  rw [L.value_quotient,L.value_length hw] at he
  have hb := regValue_lt L.value s
  rw [L.value_length hw] at hb
  simp only [SquareReduction.B]
  omega

theorem extended_low (L : SquareReduceLayout) (hw : L.Widths) (s : BasisState) :
    regValue L.value s=regValue L.extended s%SquareReduction.B := by
  simpa [extended,L.value_length hw,SquareReduction.B] using regValue_low L.value L.b s

theorem extended_high (L : SquareReduceLayout) (hw : L.Widths) (s : BasisState) :
    (s L.b).toNat=regValue L.extended s/SquareReduction.B := by
  simp only [extended,regValue_append,L.value_length hw,SquareReduction.B]
  rw [Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (by simpa [L.value_length hw] using regValue_lt L.value s)]
  cases hb : s L.b <;> simp [regValue,hb]

end SquareReduceLayout
end ECDSAAdd.Arithmetic
