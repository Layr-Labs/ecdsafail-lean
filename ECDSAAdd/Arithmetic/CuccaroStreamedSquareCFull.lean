import ECDSAAdd.Arithmetic.CuccaroStreamedSquareC

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

theorem branchC_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B O : Nat)
    (hA : regValue L.core.low base=A) (hB : regValue L.core.sum base=B)
    (hbound : A+B<2^129) (hprod : regValue L.core.product base=0)
    (hout : regValue L.core.out base=O) (hO : O<SquareReduction.p)
    (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.branchC
      (PairFrame L base 0 (branchCMiddleValue (A+B) O)) := by
  have disPO := L.product_out_disjoint hnd
  have disSP : L.core.sum.Disjoint L.core.product := by
    apply List.disjoint_left.mpr
    intro q hs hp
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hs
    have h2 := List.count_pos_iff.mpr hp
    have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hh2 := (List.drop_sublist 128 L.core.y).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  have disSO : L.core.sum.Disjoint L.core.out := by
    apply List.disjoint_left.mpr
    intro q hs ho
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hs
    have h2 := List.count_pos_iff.mpr ho
    have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hh2 := (List.drop_sublist 128 L.core.y).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  have auxAwaySum (q : Wire)
      (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
      q∉L.core.sum := by
    intro hs
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hs
    have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hh2 := (List.drop_sublist 128 L.core.y).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h h1 h2
    omega
  have prepT := L.prepareSum_frame hw hnd base A B hA hB hbound
    (PairClean.corePad L base hc) hc.cin
  intro s records hs
  have sameBasis : s.basis=base := by
    funext q
    by_cases hp : q∈L.core.product
    · exact (regValue_eq_iff L.core.product _ _).mp
        (hs.product.trans hprod.symm) q hp
    by_cases ho : q∈L.core.out
    · exact (regValue_eq_iff L.core.out _ _).mp (hs.out.trans hout.symm) q ho
    · exact hs.frame q hp ho
  have prepPre : SquareFrame L.core.sum base B s.basis := by
    rw [sameBasis]
    exact ⟨hB,fun _ _ => rfl⟩
  let s1 := run L.core.prepareSum [] s
  have e1 := prepT s [] prepPre
  have prod1 : regValue L.core.product s1.basis=0 := by
    rw [←hprod]
    apply regValue_congr
    intro q hq
    exact e1.2.2 q (fun hs => List.disjoint_left.mp disSP hs hq)
  have out1 : regValue L.core.out s1.basis=O := by
    rw [←hout]
    apply regValue_congr
    intro q hq
    exact e1.2.2 q (fun hs => List.disjoint_left.mp disSO hs hq)
  have clean1 : PairClean L s1.basis := by
    have keep (q : Wire)
        (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
          L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
        s1.basis q=base q :=
      e1.2.2 q (auxAwaySum q hq)
    constructor
    · rw [←hc.pad]
      apply regValue_congr
      intro q hq
      exact keep q (by simp [hq])
    · rw [←hc.work]
      apply regValue_congr
      intro q hq
      exact keep q (by simp [hq])
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have middleT := L.branchC_middle_pair hw hnd s1.basis (A+B) O e1.2.1
    prod1 hO clean1
  have middlePre : PairFrame L s1.basis 0 O s1.basis :=
    ⟨prod1,out1,fun _ _ _ => rfl⟩
  let s2 := run (L.core.square129++L.subRotate128 true++L.core.square129Clear) [] s1
  have e2 := middleT s1 [] middlePre
  let restoreBase : BasisState := fun q => if q∈L.core.out then s2.basis q else s.basis q
  have lowRestore : regValue L.core.low restoreBase=A := by
    rw [←hA]
    apply regValue_congr
    intro q hq
    have away : q∉L.core.out := by
      intro ho
      have h := List.nodup_iff_count.mp hnd q
      have h1 := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
      have h3 := List.count_pos_iff.mpr ho
      simp only [wires,CuccaroStreamedSquareLayout.wires,
        CuccaroStreamedSquareLayout.low,List.count_append,List.count_cons,
        List.count_nil] at h
      omega
    simp [restoreBase,away,sameBasis]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    rw [←hB]
    apply regValue_congr
    intro q hq
    simp [restoreBase,List.disjoint_left.mp disSO hq,sameBasis]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    rw [←PairClean.corePad L base hc]
    apply regValue_congr
    intro q hq
    have away := (L.pairAuxAway hnd q (by simp [foldPad,hq])).2
    simp [restoreBase,away,sameBasis]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway hnd L.core.cin (by simp)).2
    simp [restoreBase,away,sameBasis,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) s2.basis := by
    constructor
    · calc
        regValue L.core.sum s2.basis = regValue L.core.sum s1.basis :=
          regValue_congr _ _ _ (fun q hq => e2.2.frame q
            (List.disjoint_left.mp disSP hq) (List.disjoint_left.mp disSO hq))
        _ = A+B := e1.2.1
    · intro q hq
      simp only [restoreBase]
      by_cases ho : q∈L.core.out
      · simp [ho]
      rw [if_neg ho]
      by_cases hp : q∈L.core.product
      · have z2 := (regValue_zero _ _).mp e2.2.product q hp
        have z0 := (regValue_zero _ _).mp hs.product q hp
        exact z2.trans z0.symm
      · exact (e2.2.frame q hp ho).trans ((e1.2.2 q hq).trans
          (congrFun sameBasis q).symm)
  have clearT := L.clearSum_frame hw hnd restoreBase A B lowRestore sumRestore
    hbound padRestore cinRestore
  let s3 := run L.core.clearSum records s2
  have e3 := clearT s2 records clearPre
  have finalProd : regValue L.core.product s3.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have es := e3.2.2 q (fun hs => List.disjoint_left.mp disSP hs hq)
    have qo : q∉L.core.out := List.disjoint_left.mp disPO hq
    simp only [restoreBase,if_neg qo] at es
    exact es.trans ((regValue_zero _ _).mp hs.product q hq)
  have finalOut : regValue L.core.out s3.basis=branchCMiddleValue (A+B) O := by
    rw [←e2.2.out]
    apply regValue_congr
    intro q hq
    have es := e3.2.2 q (fun hs => List.disjoint_left.mp disSO hs hq)
    simp only [restoreBase,if_pos hq] at es
    exact es
  have prepM := L.core.sum_counts hw.core
  have squareM := L.core.square129_counts hw.core
  have rotM := L.rotate128_counts hw
  have middleM : measurementCount
      (L.core.square129++L.subRotate128 true++L.core.square129Clear)=0 := by
    simp [measurementCount_append,squareM.1.2,squareM.2.2,rotM.2.2.2]
  have exec : run L.branchC records s=s3 := by
    simp [branchC,s1,s2,s3,run_append,prepM.1.2,squareM.1.2,
      squareM.2.2,rotM.2.2.2]
  rw [exec]
  refine ⟨e3.1.trans (e2.1.trans e1.1),finalProd,finalOut,?_⟩
  intro q hp ho
  by_cases hsq : q∈L.core.sum
  · have eqsum := (regValue_eq_iff L.core.sum s3.basis restoreBase).mp
        (e3.2.1.trans sumRestore.symm) q hsq
    simpa [restoreBase,ho,sameBasis] using eqsum
  · have ec := e3.2.2 q hsq
    simp only [restoreBase,if_neg ho] at ec
    exact ec.trans (congrFun sameBasis q)

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
