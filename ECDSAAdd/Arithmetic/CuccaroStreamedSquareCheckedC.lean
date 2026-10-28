import ECDSAAdd.Arithmetic.CuccaroStreamedSquareOpaque

set_option maxHeartbeats 8000000
set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

/-- Rebase the cross-term branch on the state produced by the two leaf
branches, then transport its frame back to the original stage entry state. -/
theorem checkedBranchC_pair_rebased (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState) (A B O : Nat)
    (hA : regValue L.core.low base=A) (hB : regValue L.core.sum base=B)
    (hbound : A+B<2^129) (hO : O<SquareReduction.p)
    (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedBranchC
      (PairFrame L base 0 (branchCMiddleValue (A+B) O)) := by
  rw [L.checkedBranchC_eq]
  have lowAway (q : Wire) (hq : q∈L.core.low) :
      q∉L.core.product ∧ q∉L.core.out := by
    constructor <;> intro hm
    all_goals
      have h := List.nodup_iff_count.mp hnd q
      have h1 := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
      have h2 := List.count_pos_iff.mpr hm
      simp only [wires,CuccaroStreamedSquareLayout.wires,
        List.count_append,List.count_cons,List.count_nil] at h
      omega
  have sumAway (q : Wire) (hq : q∈L.core.sum) :
      q∉L.core.product ∧ q∉L.core.out := by
    constructor <;> intro hm
    all_goals
      have h := List.nodup_iff_count.mp hnd q
      have h1 := List.count_pos_iff.mpr hq
      have h2 := List.count_pos_iff.mpr hm
      have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
      have hh2 := (List.drop_sublist 128 L.core.y).count_le q
      simp only [wires,CuccaroStreamedSquareLayout.wires,
        CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
        List.count_append,List.count_cons,List.count_nil] at h h1
      omega
  intro s records hs
  have hAs : regValue L.core.low s.basis=A := by
    rw [←hA]
    apply regValue_congr
    intro q hq
    exact hs.frame q (lowAway q hq).1 (lowAway q hq).2
  have hBs : regValue L.core.sum s.basis=B := by
    rw [←hB]
    apply regValue_congr
    intro q hq
    exact hs.frame q (sumAway q hq).1 (sumAway q hq).2
  have cleanS := PairFrame.clean L hnd base 0 O s.basis hs hc
  have ct := L.branchC_pair hw hnd s.basis A B O hAs hBs hbound
    hs.product hs.out hO cleanS
  have preS : PairFrame L s.basis 0 O s.basis :=
    ⟨hs.product,hs.out,fun _ _ _ => rfl⟩
  obtain ⟨phase,out⟩ := ct s records preS
  refine ⟨phase,out.product,out.out,?_⟩
  intro q hp ho
  exact (out.frame q hp ho).trans (hs.frame q hp ho)

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
