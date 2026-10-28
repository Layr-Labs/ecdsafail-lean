import ECDSAAdd.Arithmetic.MeasuredStreamedSquare

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic

theorem copyNone_free (src dst : List Wire) :
    toffoliCount (copyRegister none src dst)=0 ∧ measurementCount (copyRegister none src dst)=0 := by
  induction src generalizing dst with
  | nil => simp [copyRegister,toffoliCount,measurementCount]
  | cons x xs ih =>
    cases dst with
    | nil => simp [copyRegister,toffoliCount,measurementCount]
    | cons y ys => simp [copyRegister,copyGate,toffoliCount,measurementCount,ih]

namespace CuccaroStreamedSquareWideLayout

theorem measured_bank_widths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.inputBank.length=129 ∧ L.leafCarry.length=257 ∧ L.leafPad.length=1 ∧
    L.foldCarry.length=256 ∧ L.shortCarry.length=255 := by
  simp [inputBank,leafCarry,leafPad,foldCarry,shortCarry,L.foldPad_length hw,hw.core.work]

theorem measuredCore_widths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.measuredCore.Widths 256 :=
  ⟨hw.core.work,hw.core.out,(L.measured_bank_widths hw).2.2.2.1⟩

theorem measured_small_operation_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (toffoliCount L.normalizeSource=511 ∧ measurementCount L.normalizeSource=510) ∧
    (toffoliCount L.restoreSource=511 ∧ measurementCount L.restoreSource=510) ∧
    (toffoliCount L.reflectOutput=255 ∧ measurementCount L.reflectOutput=255) := by
  have banks := L.measured_bank_widths hw
  have cw : L.shortCarry.length+1=L.core.work.length := by rw [banks.2.2.2.2,hw.core.work]
  have co : L.shortCarry.length+1=L.core.out.length := by rw [banks.2.2.2.2,hw.core.out]
  have ge := compareConstantGe_counts L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p cw
  have add := mappedConstAdd_counts (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.c cw
  have sub := mappedConstAdd_counts (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.p cw
  have reflect := mappedConstAdd_counts none L.core.out L.shortCarry L.core.cin SquareReduction.p co
  simp [normalizeSource,restoreSource,reflectOutput,ge.1,ge.2,add.1,add.2,sub.1,sub.2,
    reflect.1,reflect.2,(notRegister_counts L.core.out).1,(notRegister_counts L.core.out).2,
    hw.core.work,hw.core.out]

theorem measuredFold_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (f : MeasuredSquareFold) :
    toffoliCount (L.measuredFold f)=1023+(if f.canonical then 0 else 1022) ∧
    measurementCount (L.measuredFold f)=1023+(if f.canonical then 0 else 1020) := by
  have small := L.measured_small_operation_counts hw
  have copy := copyNone_free f.src (L.foldDestination f)
  have core := L.measuredCore.secp_program_counts (L.measuredCore_widths hw) SquareReduction.c SquareReduction.p
  cases h : f.canonical <;>
    simp [measuredFold,h,copy.1,copy.2,core.1,core.2,small.1.1,small.1.2,small.2.1.1,small.2.1.2]

def measuredFoldsT : Bool → List MeasuredSquareFold → Nat
  | _,[] => 0
  | orientation,f::fs => (if orientation=f.negative then 0 else 255)+
      (1023+(if f.canonical then 0 else 1022))+measuredFoldsT f.negative fs

def measuredFoldsM : Bool → List MeasuredSquareFold → Nat
  | _,[] => 0
  | orientation,f::fs => (if orientation=f.negative then 0 else 255)+
      (1023+(if f.canonical then 0 else 1020))+measuredFoldsM f.negative fs

theorem measuredFolds_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (orientation : Bool) (items : List MeasuredSquareFold) :
    toffoliCount (L.measuredFolds orientation items)=measuredFoldsT orientation items ∧
    measurementCount (L.measuredFolds orientation items)=measuredFoldsM orientation items := by
  induction items generalizing orientation with
  | nil => simp [measuredFolds,measuredFoldsT,measuredFoldsM,toffoliCount,measurementCount]
  | cons f fs ih =>
    have op := L.measuredFold_counts hw f
    have reflect := (L.measured_small_operation_counts hw).2.2
    by_cases same : orientation=f.negative <;>
      simp [measuredFolds,measuredFoldsT,measuredFoldsM,same,op.1,op.2,reflect.1,reflect.2,ih,Nat.add_assoc]

theorem measured_item_prices (L : CuccaroStreamedSquareWideLayout) :
    (measuredFoldsT false L.measuredAItems=7158 ∧ measuredFoldsM false L.measuredAItems=7158) ∧
    (measuredFoldsT false L.measuredBItems=34001 ∧ measuredFoldsM false L.measuredBItems=33993) ∧
    (measuredFoldsT true L.measuredCItems=6648 ∧ measuredFoldsM true L.measuredCItems=6648) := by
  norm_num [measuredAItems,measuredBItems,measuredCItems,nafMinusOneItems,shiftedProductItems,
    measuredFoldsT,measuredFoldsM]

theorem withMeasuredSquare_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (src dst : List Wire) (body : Program)
    (hs : 2≤src.length) (hsmax : src.length≤129) (hd : dst.length=2*src.length) :
    toffoliCount (L.withMeasuredSquare control src dst body)=
      2*(signedSquareRowsCount src.length+dst.length-1)+2*src.length+toffoliCount body ∧
    measurementCount (L.withMeasuredSquare control src dst body)=
      2*(signedSquareRowsCount src.length+dst.length-1)+2*src.length+measurementCount body := by
  have banks := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [banks.1,hsmax]
  have copy := copyRegister_counts (some control) src (L.inputBank.take src.length) inputLen.symm
  have erase := eraseMask_counts control src (L.inputBank.take src.length) inputLen.symm
  have square := mappedSignedSquare_counts (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin
    (by rw [inputLen];exact hs) (by rw [inputLen];exact hd)
    (by rw [banks.2.2.1]) (by rw [banks.2.1,hd];omega)
  simp only [withMeasuredSquare,toffoliCount_append,measurementCount_append,copy.1,copy.2,erase.1,erase.2,
    square.1.1,square.1.2,square.2.1,square.2.2,inputLen,Option.isSome_some,if_true]
  constructor <;> omega

/-- Resource theorem for the complete emitted controlled stage, including
all three producers, fresh-record cleanup, source normalization and frames. -/
theorem measuredProgram_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (L.measuredProgram control)=99902 ∧ measurementCount (L.measuredProgram control)=99382 := by
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := L.withMeasuredSquare_counts hw control L.core.low (L.core.product.take 256)
    (L.measuredFolds false L.measuredAItems) (by omega) (by omega) (by omega)
  have b := L.withMeasuredSquare_counts hw control L.core.high (L.core.product.take 256)
    (L.measuredFolds false L.measuredBItems) (by omega) (by omega) (by omega)
  have c := L.withMeasuredSquare_counts hw control L.core.sum L.core.product
    (L.measuredFolds true L.measuredCItems) (by omega) (by omega) (by rw [hw.core.product,su])
  have fa := L.measuredFolds_counts hw false L.measuredAItems
  have fb := L.measuredFolds_counts hw false L.measuredBItems
  have fc := L.measuredFolds_counts hw true L.measuredCItems
  have prices := L.measured_item_prices
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  rw [prices.2.2.1,prices.2.2.2] at fc
  have reflection := (L.measured_small_operation_counts hw).2.2
  have sum := L.core.sum_counts hw.core
  simp only [measuredProgram,measuredBranchA,measuredBranchB,measuredBranchC,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    reflection.1,reflection.2,sum.1.1,sum.1.2,sum.2.1,sum.2.2,lo,hi,su,p256,hw.core.product]
  norm_num [signedSquareRowsCount]

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
