import ECDSAAdd.Arithmetic.InverseQuotientRecorded
import ECDSAAdd.Arithmetic.MultiplyPorts
import ECDSAAdd.Arithmetic.PointDialogLayout

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

/-- Large reference placement: 1827 product work bits, 257 inverse bits,
257 temporary bits, and one denominator padding bit. -/
def quotientMont (L : ControlledPointLayout) : MontLayout :=
  poolMul L.core.poolWire (wireBlock L.core.poolWire 1827 257) L.point.y
    (wireBlock L.core.poolWire 2084 257)

def quotientDen (L : ControlledPointLayout) : List Wire :=
  L.point.x ++ [L.core.poolWire 2341]

theorem quotient_widths (L : ControlledPointLayout) (hw : L.Widths) :
    L.quotientMont.Widths ∧ L.quotientDen.length = 257 := by
  constructor
  · exact poolMul_widths _ _ _ _ (wireBlock_length _ _ _) hw.inputY (wireBlock_length _ _ _)
  · simp [quotientDen,point,hw.inputX]

theorem quotient_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.core.generic :: L.quotientDen ++ L.quotientMont.wires).Nodup := by
  have hp : wireBlock L.core.poolWire 0 2342 =
      wireBlock L.core.poolWire 0 1827 ++ wireBlock L.core.poolWire 1827 257 ++
      wireBlock L.core.poolWire 2084 257 ++ [L.core.poolWire 2341] := by
    have one : [L.core.poolWire 2341] = wireBlock L.core.poolWire 2341 1 := by
      simp [wireBlock,List.range']
    rw [one,wireBlock_append,wireBlock_append,wireBlock_append]
  have hpref : L.dialogPool.take 2342 = wireBlock L.core.poolWire 0 2342 := by
    rw [L.core.pool_prefix hw 2342 (by omega)]
    simp [dialogPool,List.take_take]
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hle := (List.take_sublist 2342 L.dialogPool).count_le q
  rw [hpref,hp] at hle
  change List.count q (L.core.generic :: L.quotientDen ++
    (L.quotientMont.x ++ L.quotientMont.y ++ L.quotientMont.out ++ L.quotientMont.work)) ≤ 1
  simp only [quotientMont,poolMul_inputs,poolMul_work,quotientDen] at *
  simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.count_append,
    List.count_cons,List.count_nil] at h hle ⊢
  omega

theorem quotient_subset (L : ControlledPointLayout) (hw : L.Widths) :
    L.core.generic :: L.quotientDen ++ L.quotientMont.wires ⊆ L.dialogUsedWires := by
  have pool (i : Nat) (hi : i < 2613) : L.core.poolWire i ∈ L.dialogPool := by
    rw [dialogPool,←L.core.pool_prefix hw 2613 (by omega)]
    exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1]; omega,rfl⟩
  have block (a n : Nat) (h : a+n ≤ 2613) : wireBlock L.core.poolWire a n ⊆ L.dialogPool := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact pool i (by omega)
  intro q hq
  change q ∈ L.core.generic :: L.quotientDen ++
    (L.quotientMont.x ++ L.quotientMont.y ++ L.quotientMont.out ++ L.quotientMont.work) at hq
  simp only [quotientMont,poolMul_inputs,poolMul_work,quotientDen] at hq
  have hi := block 1827 257 (by omega)
  have ht := block 2084 257 (by omega)
  have hz := block 0 1827 (by omega)
  have hp := pool 2341 (by omega)
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq
  simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  have hiq : q ∈ wireBlock L.core.poolWire 1827 257 → q ∈ L.dialogPool := fun h => hi h
  have htq : q ∈ wireBlock L.core.poolWire 2084 257 → q ∈ L.dialogPool := fun h => ht h
  have hzq : q ∈ wireBlock L.core.poolWire 0 1827 → q ∈ L.dialogPool := fun h => hz h
  have hpq : q = L.core.poolWire 2341 → q ∈ L.dialogPool := by intro h; subst q; exact hp
  change ((q = L.core.generic ∨ q ∈ L.point.x ∨ q = L.core.poolWire 2341) ∨
    ((q ∈ wireBlock L.core.poolWire 1827 257 ∨ q ∈ L.point.y) ∨
      q ∈ wireBlock L.core.poolWire 2084 257) ∨ q ∈ wireBlock L.core.poolWire 0 1827) at hq
  tauto

theorem quotient_clean (L : ControlledPointLayout) (hw : L.Widths)
    (bits : Wire → Bool) (hzero : regValue L.dialogPool bits = 0) :
    regValue L.quotientMont.x bits = 0 ∧ regValue L.quotientMont.out bits = 0 ∧
    regValue L.quotientMont.work bits = 0 ∧
    regValue L.quotientDen bits = regValue L.point.x bits := by
  have pool (i : Nat) (hi : i < 2613) : bits (L.core.poolWire i) = false := by
    apply (regValue_zero _ _).mp hzero
    rw [dialogPool,←L.core.pool_prefix hw 2613 (by omega)]
    exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1]; omega,rfl⟩
  have block (a n : Nat) (h : a+n ≤ 2613) : regValue (wireBlock L.core.poolWire a n) bits = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact pool i (by omega)
  refine ⟨block 1827 257 (by omega),block 2084 257 (by omega),?_,?_⟩
  · change regValue (poolMul _ _ _ _).work bits = 0
    rw [poolMul_work]; exact block 0 1827 (by omega)
  · simp [quotientDen,regValue,pool 2341 (by omega)]

end ECDSAAdd.Arithmetic.ControlledPointLayout
