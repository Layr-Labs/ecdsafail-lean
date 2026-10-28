import ECDSAAdd.Arithmetic.SquareReduceLayout
import ECDSAAdd.Arithmetic.KaratsubaSquareProof

namespace ECDSAAdd.Arithmetic

/-- 第一折叠及其清理。高33位保留为后续折叠的商记录。 -/
theorem squareFirstFold_correct (L : SquareReduceLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState)
    (hz : regValue (L.pad++L.carry) base=0) (hi : base L.cin=false) :
    let U := regValue L.low base+SquareReduction.c*regValue L.high base
    Triple (SquareFrame L.r base 0)
      (copyRegister none L.low L.value ++
        squareFoldAdd L.high L.r L.pad L.carry L.cin squareFoldShifts)
      (SquareFrame L.r base U) ∧
    Triple (SquareFrame L.r base U)
      (squareFoldClear L.high L.r L.pad L.carry L.cin squareFoldShifts ++
        copyRegister none L.low L.value)
      (SquareFrame L.r base 0) := by
  have hr := hw.r
  have hh := hw.high
  have hpad := hw.pad
  have hcarry := hw.carry
  have hlr : (L.low++L.r).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hcopy := karatsuba_copy_low L.low L.r 256 hw.low (by omega) hlr base
  have hlow : regValue L.low base<SquareReduction.B := by
    simpa [hw.low,SquareReduction.B] using regValue_lt L.low base
  have hhigh : regValue L.high base<SquareReduction.B := by
    simpa [hw.high,SquareReduction.B] using regValue_lt L.high base
  have hweight : squareFoldWeight squareFoldShifts=SquareReduction.c := by
    norm_num [squareFoldWeight,squareFoldShifts,SquareReduction.c]
  have hfold := squareFold_correct L.high L.r L.pad L.carry L.cin squareFoldShifts
    (L.first_nodup hn) (by omega)
    (by intro j hj; simp [squareFoldShifts] at hj; omega) (by omega) (by omega)
    base hz hi (regValue L.low base) (by
      rw [hweight,hw.r,Nat.mul_comm (regValue L.high base)]
      exact SquareReduction.first_bound _ _ hlow hhigh)
  simpa only [hweight,Nat.mul_comm (regValue L.high base),SquareReduceLayout.value] using
    And.intro (hcopy.1.seq hfold.1) (hfold.2.seq hcopy.2)

end ECDSAAdd.Arithmetic
