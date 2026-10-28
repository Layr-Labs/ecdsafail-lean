import ECDSAAdd.Arithmetic.CuccaroStreamedSquareControlled
import ECDSAAdd.Arithmetic.ControlledNormalizedResources

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c scratch : Wire)
include hw

theorem controlledSource_counts (src : List Wire) (hs : src.length=256) :
    (toffoliCount (L.controlledAddSource c scratch src)=15857 ∧
      measurementCount (L.controlledAddSource c scratch src)=0) ∧
    (toffoliCount (L.controlledSubSource c scratch src)=17909 ∧
      measurementCount (L.controlledSubSource c scratch src)=0) :=
  controlledNormalizedMod_secp256k1_counts c scratch (L.source src)
    (L.source_widths hw src hs)

theorem controlledCMinusOne_counts (src : List Wire)
    (hs2 : 2≤src.length) (hs : src.length+32≤256) :
    (toffoliCount (L.controlledAddCMinusOne c scratch src)=65480 ∧
      measurementCount (L.controlledAddCMinusOne c scratch src)=0) ∧
    (toffoliCount (L.controlledSubCMinusOne c scratch src)=69584 ∧
      measurementCount (L.controlledSubCMinusOne c scratch src)=0) := by
  have s4 := L.controlledSource_counts hw c scratch _
    (L.shifted_length hw src 4 hs2 (by omega))
  have s6 := L.controlledSource_counts hw c scratch _
    (L.shifted_length hw src 6 hs2 (by omega))
  have s10 := L.controlledSource_counts hw c scratch _
    (L.shifted_length hw src 10 hs2 (by omega))
  have s32 := L.controlledSource_counts hw c scratch _ (L.shifted_length hw src 32 hs2 hs)
  simp [controlledAddCMinusOne,controlledSubCMinusOne,toffoliCount_append,
    measurementCount_append,s4,s6,s10,s32]

theorem controlledRotate128_counts :
    (toffoliCount (L.controlledAddRotate128 c scratch false)=81337 ∧
      measurementCount (L.controlledAddRotate128 c scratch false)=0) ∧
    (toffoliCount (L.controlledSubRotate128 c scratch false)=87493 ∧
      measurementCount (L.controlledSubRotate128 c scratch false)=0) ∧
    (toffoliCount (L.controlledSubRotate128 c scratch true)=105402 ∧
      measurementCount (L.controlledSubRotate128 c scratch true)=0) := by
  have rot := L.controlledSource_counts hw c scratch _ (L.rotated128_view hw).length
  have terms := L.controlledCMinusOne_counts hw c scratch (L.core.product.drop 128)
    (by simp [hw.core.product]) (by simp [hw.core.product])
  have tail := L.controlledSource_counts hw c scratch _
    (L.shifted_length hw (L.core.product.drop 256) 128 (by simp [hw.core.product])
      (by simp [hw.core.product]))
  simp [controlledAddRotate128,controlledSubRotate128,toffoliCount_append,
    measurementCount_append,rot,terms,tail,toffoliCount,measurementCount]

theorem controlledShiftFull_counts (j : Nat) (hj2 : 2≤j) (hj : j≤224) :
    (toffoliCount (L.controlledAddShiftFull c scratch j)=81337 ∧
      measurementCount (L.controlledAddShiftFull c scratch j)=0) ∧
    (toffoliCount (L.controlledSubShiftFull c scratch j)=87493 ∧
      measurementCount (L.controlledSubShiftFull c scratch j)=0) := by
  have rot := L.controlledSource_counts hw c scratch _ (L.rotateFull_view hw j (by omega)).length
  have len : ((L.core.product.take 256).drop (256-j)).length=j := by
    simp [hw.core.product]
    omega
  have terms := L.controlledCMinusOne_counts hw c scratch
    ((L.core.product.take 256).drop (256-j))
    (by rw [len]; exact hj2) (by rw [len]; omega)
  have jnz : j≠0 := by omega
  simp [controlledAddShiftFull,controlledSubShiftFull,jnz,toffoliCount_append,
    measurementCount_append,rot,terms]

theorem controlledTimesC_counts :
    toffoliCount (L.controlledTimesC c scratch)=361725 ∧
    measurementCount (L.controlledTimesC c scratch)=0 := by
  have base := L.controlledSource_counts hw c scratch _ (L.productTake256_view hw).length
  have s4 := L.controlledShiftFull_counts hw c scratch 4 (by omega) (by omega)
  have s6 := L.controlledShiftFull_counts hw c scratch 6 (by omega) (by omega)
  have s10 := L.controlledShiftFull_counts hw c scratch 10 (by omega) (by omega)
  have s32 := L.controlledShiftFull_counts hw c scratch 32 (by omega) (by omega)
  have zeroEq : L.controlledSubShiftFull c scratch 0=
      L.controlledSubSource c scratch (L.core.product.take 256) := rfl
  simp [controlledTimesC,zeroEq,toffoliCount_append,
    measurementCount_append,base,s4,s6,s10,s32]

theorem controlledProgram_counts :
    toffoliCount (L.controlledProgram c scratch)=749338 ∧
      measurementCount (L.controlledProgram c scratch)=0 := by
  have lo := L.core.square128_counts hw.core L.core.low (L.core.low_length hw.core)
  have hi := L.core.square128_counts hw.core L.core.high (L.core.high_length hw.core)
  have sq := L.core.square129_counts hw.core
  have prep := L.core.sum_counts hw.core
  have base := L.controlledSource_counts hw c scratch _ (L.productTake256_view hw).length
  have rot := L.controlledRotate128_counts hw c scratch
  have times := L.controlledTimesC_counts hw c scratch
  simp [controlledProgram,controlledBranchA,controlledBranchB,controlledBranchC,
    toffoliCount_append,measurementCount_append,lo,hi,sq,prep,base,rot,times]

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
