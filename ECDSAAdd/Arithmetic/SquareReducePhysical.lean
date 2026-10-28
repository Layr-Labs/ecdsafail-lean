import ECDSAAdd.Arithmetic.SquareReduce
import ECDSAAdd.Arithmetic.CounterPhysical
import ECDSAAdd.Arithmetic.ControlledUnaryPhysical
import ECDSAAdd.Arithmetic.SquareFoldPhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem squareReductions_physical (L : SquareReduceLayout) (hn : L.wires.Nodup) :
    GatePhysical (squareReduce L) ∧ GatePhysical (squareReduceClear L) := by
  have nd_copy : (L.low++L.value).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have c255 := (List.take_sublist 255 L.carry).count_le w
    have c256 := (List.take_sublist 256 L.carry).count_le w
    have rt := (List.take_sublist 256 L.r).count_le w
    have rd := (List.drop_sublist 256 L.r).count_le w
    have eq := congrArg (List.count w) (List.take_append_drop 256 L.r)
    simp only [List.count_append] at eq
    simp only [SquareReduceLayout.wires,SquareReduceLayout.value,
      
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have nd_high : (L.cin::(L.high++L.r++L.pad++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have c255 := (List.take_sublist 255 L.carry).count_le w
    have c256 := (List.take_sublist 256 L.carry).count_le w
    have rt := (List.take_sublist 256 L.r).count_le w
    have rd := (List.drop_sublist 256 L.r).count_le w
    have eq := congrArg (List.count w) (List.take_append_drop 256 L.r)
    simp only [List.count_append] at eq
    simp only [SquareReduceLayout.wires,
      
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have nd_quot : (L.cin::(L.quotient++L.extended++L.pad++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have c255 := (List.take_sublist 255 L.carry).count_le w
    have c256 := (List.take_sublist 256 L.carry).count_le w
    have rt := (List.take_sublist 256 L.r).count_le w
    have rd := (List.drop_sublist 256 L.r).count_le w
    have eq := congrArg (List.count w) (List.take_append_drop 256 L.r)
    simp only [List.count_append] at eq
    simp only [SquareReduceLayout.wires,SquareReduceLayout.value,
      SquareReduceLayout.quotient,SquareReduceLayout.extended,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have nd_mask : (L.cin::(L.mask++L.value++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have c255 := (List.take_sublist 255 L.carry).count_le w
    have c256 := (List.take_sublist 256 L.carry).count_le w
    have rt := (List.take_sublist 256 L.r).count_le w
    have rd := (List.drop_sublist 256 L.r).count_le w
    have eq := congrArg (List.count w) (List.take_append_drop 256 L.r)
    simp only [List.count_append] at eq
    simp only [SquareReduceLayout.wires,SquareReduceLayout.value,
      
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have nd_cmp : (L.flag::L.cin::(L.value++L.mask++L.carry.take 256)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hn w
    have c255 := (List.take_sublist 255 L.carry).count_le w
    have c256 := (List.take_sublist 256 L.carry).count_le w
    have rt := (List.take_sublist 256 L.r).count_le w
    have rd := (List.drop_sublist 256 L.r).count_le w
    have eq := congrArg (List.count w) (List.take_append_drop 256 L.r)
    simp only [List.count_append] at eq
    simp only [SquareReduceLayout.wires,SquareReduceLayout.value,
      
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bm : L.b ∉ L.mask := by
    intro hm
    have h := List.nodup_iff_count.mp hn L.b
    have hh := List.count_pos_iff.mpr hm
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have fm : L.flag ∉ L.mask := by
    intro hm
    have h := List.nodup_iff_count.mp hn L.flag
    have hh := List.count_pos_iff.mpr hm
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have cp := copyRegister_physical none L.low L.value nd_copy (by simp)
  have hi := squareFolds_physical L.high L.r L.pad L.carry L.cin squareFoldShifts nd_high
  have qt := squareFolds_physical L.quotient L.extended L.pad L.carry L.cin squareFoldShifts nd_quot
  have ba := maskedAddConst_physical L.b L.mask L.value _ L.cin SquareReduction.c nd_mask bm
  have bs := maskedSubConst_physical L.b L.mask L.value _ L.cin SquareReduction.c nd_mask bm
  have fa := maskedAddConst_physical L.flag L.mask L.value _ L.cin SquareReduction.p nd_mask fm
  have fs := maskedSubConst_physical L.flag L.mask L.value _ L.cin SquareReduction.p nd_mask fm
  have cmp := compareLtConst_physical none L.value L.mask _ L.cin L.flag SquareReduction.p nd_cmp (by simp)
  have x : GatePhysical [.X L.flag] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  simp only [squareReduce,squareReduceClear,squareNormalize,squareDenormalize,gatePhysical_append]
  tauto

end ECDSAAdd.Arithmetic
