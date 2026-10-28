import ECDSAAdd.Baselines.SlotSignedSquare

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem cuccaroAdd_gateSlots_le (xs ys : List Wire) (c : Wire) :
    gateSlots (cuccaroAdd xs ys c) ≤ 6*xs.length := by
  induction xs, ys, c using cuccaroAdd.induct with
  | case1 c => simp [cuccaroAdd]
  | case2 a b c => simp [cuccaroAdd, gateSlots_cons, instructionSlots]
  | case3 a a' xs b b' ys c ih =>
    simp only [List.length_cons] at ih
    simp only [cuccaroAdd, gateSlots_append, cuccaroMaj, cuccaroUma, gateSlots_cons,
      gateSlots_nil, instructionSlots, List.length_cons]; omega
  | case4 xs ys c h => simp [cuccaroAdd]

theorem streamedFrames_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    gateSlots L.normalizeSource ≤ 8961 ∧ gateSlots L.restoreSource ≤ 8961 ∧
    gateSlots L.reflectOutput ≤ 4608 := by
  have hc := compareConstant_gateSlots_le L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p
  have hm k := mappedConst_gateSlots_le (some L.core.normFlag) L.core.work L.shortCarry L.core.cin k
  have h1 := hm SquareReduction.c
  have h2 := hm SquareReduction.p
  have h3 := mappedConst_gateSlots_le none L.core.out L.shortCarry L.core.cin SquareReduction.p
  rw [hw.core.work] at hc h1 h2
  rw [hw.core.out] at h3
  simp only [CuccaroStreamedSquareWideLayout.normalizeSource, CuccaroStreamedSquareWideLayout.restoreSource,
    CuccaroStreamedSquareWideLayout.reflectOutput, compareConstantGe, gateSlots_append,
    notRegister_gateSlots, hw.core.out, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem measuredFold_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold) :
    gateSlots (L.measuredFold f) ≤ 36000 := by
  have hf := streamedFrames_gateSlots_le L hw
  have hc := canonicalMod_gateSlots_le L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
  have hd : (L.foldDestination f).length ≤ 256 := by
    simp only [CuccaroStreamedSquareWideLayout.foldDestination, List.length_take, List.length_drop, hw.core.work]; omega
  have hcopy := Nat.min_le_right f.src.length (L.foldDestination f).length
  simp only [CuccaroStreamedSquareWideLayout.measuredFold, gateSlots_append, copyRegister_gateSlots]
  cases f.canonical <;> simp only [Bool.false_eq_true, ↓reduceIte, gateSlots_nil] <;> omega

theorem measuredFolds_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (orientation : Bool) (fs : List MeasuredSquareFold) :
    gateSlots (L.measuredFolds orientation fs) ≤ fs.length*41000 := by
  induction fs generalizing orientation with
  | nil => simp only [CuccaroStreamedSquareWideLayout.measuredFolds, gateSlots_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons f fs ih =>
    have h := measuredFold_gateSlots_le L hw f
    have hr := (streamedFrames_gateSlots_le L hw).2.2
    have ht := ih f.negative
    simp only [CuccaroStreamedSquareWideLayout.measuredFolds, gateSlots_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    by_cases he : orientation = f.negative
    · simp only [he, ↓reduceIte, gateSlots_nil]; omega
    · simp only [he, ↓reduceIte]; omega

theorem withMeasuredSquare_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (src dst : List Wire) (body : Program) (hd : dst.length ≤ 258) :
    gateSlots (L.withMeasuredSquare control src dst body) ≤ 820000 + gateSlots body := by
  have hs := mappedSigned_gateSlots_le (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin
  have hl : (L.inputBank.take src.length).length ≤ 129 := by
    simp only [CuccaroStreamedSquareWideLayout.inputBank, List.length_take, hw.core.work]; omega
  have hcopy := Nat.min_le_right src.length (L.inputBank.take src.length).length
  have hb : (L.inputBank.take src.length).length * (12*((L.inputBank.take src.length).length+1)+6*dst.length) ≤ 400932 := by
    nlinarith
  simp only [CuccaroStreamedSquareWideLayout.withMeasuredSquare, gateSlots_append,
    copyRegister_gateSlots, eraseMask_gateSlots]
  omega

theorem measuredProgram_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : gateSlots (L.measuredProgram control) ≤ 5000000 := by
  have ha := measuredFolds_gateSlots_le L hw false L.measuredAItems
  have hb := measuredFolds_gateSlots_le L hw false L.measuredBItems
  have hc := measuredFolds_gateSlots_le L hw true L.measuredCItems
  have la : L.measuredAItems.length = 6 := by rfl
  have lb : L.measuredBItems.length = 26 := by rfl
  have lc : L.measuredCItems.length = 6 := by rfl
  rw [la] at ha
  rw [lb] at hb
  rw [lc] at hc
  have hd : (L.core.product.take 256).length ≤ 258 := by
    simp only [List.length_take]; omega
  have a := withMeasuredSquare_gateSlots_le L hw control L.core.low _
    (L.measuredFolds false L.measuredAItems) hd
  have b := withMeasuredSquare_gateSlots_le L hw control L.core.high _
    (L.measuredFolds false L.measuredBItems) hd
  have c := withMeasuredSquare_gateSlots_le L hw control L.core.sum L.core.product
    (L.measuredFolds true L.measuredCItems) (by rw [hw.core.product])
  have hp := cuccaroAdd_gateSlots_le (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin
  have hl := L.core.low_length hw.core
  simp only [List.length_append, List.length_cons, List.length_nil, hl] at hp
  change gateSlots L.core.prepareSum ≤ _ at hp
  have hr := (streamedFrames_gateSlots_le L hw).2.2
  simp only [CuccaroStreamedSquareWideLayout.measuredProgram,
    CuccaroStreamedSquareWideLayout.measuredBranchA,
    CuccaroStreamedSquareWideLayout.measuredBranchB,
    CuccaroStreamedSquareWideLayout.measuredBranchC,
    CuccaroStreamedSquareLayout.clearSum, gateSlots_append, reverse_gateSlots]
  omega

end ECDSAAdd.Baselines
