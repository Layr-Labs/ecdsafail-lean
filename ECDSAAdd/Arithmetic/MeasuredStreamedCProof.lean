import ECDSAAdd.Arithmetic.MeasuredStreamedBranches

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measured_sum_count (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
  have take := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
  have drop := (List.drop_sublist 128 L.core.y).count_le q
  simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at take ⊢
  omega

theorem measured_sum_aux_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.sum := by
  intro bad
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  have bound := L.measured_sum_count q
  simp only [wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_append,List.count_cons,List.count_nil] at h a bound
  omega

theorem measured_sum_disjoint (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    L.core.sum.Disjoint L.core.product ∧ L.core.sum.Disjoint L.core.out := by
  constructor <;> apply List.disjoint_left.mpr <;> intro q hs hq
  all_goals
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hs
    have b := List.count_pos_iff.mpr hq
    have bound := L.measured_sum_count q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h bound
    omega

theorem measuredBranchC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis) :
    (run (L.measuredBranchC control) records s).phase=s.phase ∧
    regValue L.core.out (run (L.measuredBranchC control) records s).basis=
      measuredCMiddleResult ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (L.measuredBranchC control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := L.withMeasuredSquare control L.core.sum L.core.product (L.measuredFolds true L.measuredCItems)
  let u := run L.core.prepareSum [] s
  let v := run middle (records.take (measurementCount middle)) u
  let out := run L.core.clearSum (records.drop (measurementCount middle)) v
  have prep := L.prepareSum_frame hw nd s.basis A B ha hb bound (PairClean.corePad L s.basis hc) hc.cin
    s [] (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have used := L.measuredBranchC_middle_correct hw control hn (A+B) O hO u
    (records.take (measurementCount middle)) prep.2.1 outU productU cleanU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have cleared := L.clearSum_frame hw nd restoreBase A B lowRestore sumRestore bound padRestore cinRestore
    v (records.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      measuredCMiddleResult ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      measuredCMiddleResult ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  have prepM := (L.core.sum_counts hw.core).1.2
  simpa [measuredBranchC,middle,u,v,out,run_append,prepM] using final

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
