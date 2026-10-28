import ECDSAAdd.Arithmetic.InverseCompactSupport

namespace ECDSAAdd.Arithmetic
namespace InverseLoopLayout

def coreWires (L : InverseLoopLayout) : List Wire := L.first.tapeWires L.records++L.extra

theorem core_perm (L : InverseLoopLayout) : (L.restWires++L.phaseWires).Perm L.coreWires := by
  apply List.perm_iff_count.mpr
  intro w
  have hp := L.rest_phase_perm.count_eq w
  simp only [wires,coreWires,List.count_append] at hp ⊢
  omega

theorem phase_subset (L : InverseLoopLayout) : L.phaseWires ⊆ L.coreWires :=
  fun _ h => L.core_perm.mem_iff.mp (List.mem_append_right _ h)

theorem rest_subset (L : InverseLoopLayout) : L.restWires ⊆ L.coreWires :=
  fun _ h => L.core_perm.mem_iff.mp (List.mem_append_left _ h)

/-- 独立求逆仅需要银行前30位；中段乘法的804位另计。 -/
def usedCoreWires (L : InverseLoopLayout) : List Wire := L.first.usedRecordTapeWires L.records++L.arithmetic.wires.take 30

theorem compactCore_sublist (L : InverseLoopLayout) : L.compactCoreWires.Sublist L.coreWires :=
  (L.first.usedRecordTapeWires_sublist L.records).append
    ((List.take_sublist 804 L.arithmetic.wires).trans (List.sublist_append_right _ _))

def usedWires (L : InverseLoopLayout) : List Wire := L.usedCoreWires++L.out

theorem usedCoreWires_sublist (L : InverseLoopLayout) : L.usedCoreWires.Sublist L.coreWires := by
  exact (L.first.usedRecordTapeWires_sublist L.records).append
    ((List.take_sublist 30 L.arithmetic.wires).trans (List.sublist_append_right _ _))

theorem usedWires_sublist (L : InverseLoopLayout) : L.usedWires.Sublist L.wires :=
  L.usedCoreWires_sublist.append_right _

theorem reg_first_used (L : InverseLoopLayout) (f : RoundField) (hf : f≠.out) :
    L.middle.data.reg f ⊆ L.first.usedRecordTapeWires L.records := by
  intro w hw
  have hh : w∈L.middle.usedSharedWires := List.mem_append_left _
    (List.mem_append_right _ (L.middle.data.reg_used_mem f hf hw))
  exact List.mem_append_right _ (L.compact_middle_perm.mem_iff.mp hh)

theorem borrow_used_subset (L : InverseLoopLayout) (hl : L.first.low.length=256) :
    L.compactBorrow.take 1054 ⊆ L.usedCoreWires := by
  rw [L.compactBorrow_prefix hl]
  intro w hw
  rcases List.mem_append.mp hw with hw|hw
  · apply List.mem_append_left
    simp only [List.mem_append] at hw
    rcases hw with ((hw|hw)|hw)|hw
    · exact L.reg_first_used .u (by decide) hw
    · exact L.reg_first_used .v (by decide) hw
    · exact L.reg_first_used .s (by decide) hw
    · exact L.reg_first_used .zero (by decide) (List.mem_of_mem_drop hw)
  · exact List.mem_append_right _ hw

theorem compactScaling_subset (L : InverseLoopLayout) (hl : L.first.low.length=256)
    (hm : L.arithmetic.width=256) : L.compactScaling.wires ⊆ L.usedCoreWires := by
  intro w hw
  simp only [InverseScaleLayout.wires,L.compactScaling_work hm hl,L.compactScaling_live hl,List.mem_append] at hw
  rcases hw with ((hr|hk)|hh)|hb
  · exact List.mem_append_left _ (L.reg_first_used .r (by decide) hr)
  · have hc : w∈L.middle.counter.wires := by
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hk
      exact List.mem_cons_of_mem _ (mem_addWires hb).1
    have hs : w∈L.middle.usedSharedWires := List.mem_append_right _ hc
    exact List.mem_append_left _ (List.mem_append_right _ (L.compact_middle_perm.mem_iff.mp hs))
  · apply List.mem_append_left
    simp only [scaleLive,List.mem_append] at hh
    rcases hh with (hh|hh)|hh
    · exact L.reg_first_used .y (by decide) hh
    · exact L.reg_first_used .zero (by decide) (List.mem_of_mem_take hh)
    · exact L.reg_first_used .carry (by decide) hh
  · exact L.borrow_used_subset hl hb

end InverseLoopLayout

theorem inverseCompute_wires (L : InverseLoopLayout)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hd : 2≤L.first.data.width) (_hwidth : L.first.data.width=L.arithmetic.width+1)
    (_ha : L.a.length=L.arithmetic.width+1) (_ht : L.temp.length=L.arithmetic.width+1)
    (hl : L.first.low.length=256) (hm : L.arithmetic.width=256) (q : Nat) :
    wires (inverseCompute L q)=L.usedCoreWires.toFinset ∧
    wires (inverseUncompute L q)=L.usedCoreWires.toFinset := by
  have hk := oneBitRecordLoop_wires L.first L.records 0 hw hd
  have hne : L.records.isEmpty=false := by
    cases he : L.records with
    | nil => rw [he] at hn; simp at hn
    | cons r rs => rfl
  simp only [hne,Bool.false_eq_true,if_false] at hk
  have hnw := negativeEven_wires L.compactNeg 256 q (L.compactNeg_widths hm hl) (by omega)
  rw [L.compactNeg_core hm hl] at hnw
  have hsw := L.compactScaling_widths (by change (L.middle.data.reg .r).length=257; rw [InverseLoopLayout.middle,loopEnd_data,L.first.data_reg_length,hl]) hm hl hw
  have hsup := L.compactScaling.wires_subset hsw q
  have hcover := L.compactScaling.work_covered hsw q
  rw [L.compactScaling_work hm hl] at hcover
  have first : (L.first.usedRecordTapeWires L.records).toFinset⊆L.usedCoreWires.toFinset := by
    intro w hh; exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hh))
  have bs : (L.compactBorrow.take 1054).toFinset⊆L.usedCoreWires.toFinset := by
    intro w hh; exact List.mem_toFinset.mpr (L.borrow_used_subset hl (List.mem_toFinset.mp hh))
  have take514 : L.compactBorrow.take 514 ⊆ L.compactBorrow.take 1054 :=
    (List.take_sublist_take_left (by omega)).subset
  have neg : wires (negativeEven L.compactNeg q)⊆L.usedCoreWires.toFinset := by
    rw [hnw.1]
    intro w hh
    rcases List.mem_append.mp (List.mem_toFinset.mp hh) with hh|hh
    · exact first (List.mem_toFinset.mpr (L.reg_first_used .r (by decide) hh))
    · exact bs (List.mem_toFinset.mpr (take514 hh))
  have negback : wires (restoreNegativeEven L.compactNeg q)⊆L.usedCoreWires.toFinset := by
    rw [hnw.2,List.toFinset_append]
    apply Finset.union_subset
    · simpa only [hnw.1] using neg
    · intro w hh
      have he : w=L.compactNeg.flag := by simpa using hh
      subst w
      apply bs
      simp only [InverseLoopLayout.compactNeg]
      have hb := L.compactBorrow_length hl hm
      have hi : 1028<(L.compactBorrow.take 1054).length := by simp [hb]
      have he : (L.compactBorrow.take 1054)[1028]=L.compactBorrow.getD 1028 L.first.done := by simp [hb]
      rw [←he]
      exact List.mem_toFinset.mpr (List.getElem_mem hi)
  have sc : L.compactScaling.wires.toFinset⊆L.usedCoreWires.toFinset := by
    intro w hh; exact List.mem_toFinset.mpr (L.compactScaling_subset hl hm (List.mem_toFinset.mp hh))
  have constants : wires (terminalConstants L q)⊆L.usedCoreWires.toFinset := by
    intro w hh
    have hc := List.mem_toFinset.mp ((terminalConstants_resources L q).2.2 hh)
    rcases List.mem_append.mp hc with hc|hc
    · exact first (List.mem_toFinset.mpr (L.reg_first_used .u (by decide) hc))
    · exact first (List.mem_toFinset.mpr (L.reg_first_used .s (by decide) hc))
  have upperF : wires (inverseCompute L q)⊆L.usedCoreWires.toFinset := by
    rw [inverseCompute,wires_append,wires_append,wires_append,hk.1]
    exact Finset.union_subset (Finset.union_subset (Finset.union_subset first constants) neg) (hsup.1.trans sc)
  have upperB : wires (inverseUncompute L q)⊆L.usedCoreWires.toFinset := by
    rw [inverseUncompute,wires_append,wires_append,wires_append,hk.2]
    exact Finset.union_subset (Finset.union_subset (Finset.union_subset (hsup.2.trans sc) negback) constants) first
  have lower (circ : Program) (hfirst : (L.first.usedRecordTapeWires L.records).toFinset⊆wires circ)
      (hfactor : L.compactScaling.factor.toFinset⊆wires circ)
      (hborrow : (L.compactBorrow.take 1054).toFinset⊆wires circ ∪ L.compactScaling.factor.toFinset) :
      L.usedCoreWires.toFinset⊆wires circ := by
    intro w hh
    rcases List.mem_append.mp (List.mem_toFinset.mp hh) with hh|hh
    · exact hfirst (List.mem_toFinset.mpr hh)
    · have hb : w∈(L.compactBorrow.take 1054).toFinset := by
        rw [L.compactBorrow_prefix hl]
        exact List.mem_toFinset.mpr (List.mem_append_right _ hh)
      rcases Finset.mem_union.mp (hborrow hb) with hh|hh
      · exact hh
      · exact hfactor hh
  have factor : L.compactScaling.factor.toFinset⊆wires (negativeEven L.compactNeg q) ∧
      L.compactScaling.factor.toFinset⊆wires (restoreNegativeEven L.compactNeg q) := by
    have ht : L.compactBorrow.take 257 ⊆ L.compactBorrow.take 514 := (List.take_sublist_take_left (by omega)).subset
    constructor <;> intro w hh
    · rw [hnw.1]; exact List.mem_toFinset.mpr (List.mem_append_right _ (ht (List.mem_toFinset.mp hh)))
    · rw [hnw.2]; exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_append_right _ (ht (List.mem_toFinset.mp hh))))
  constructor
  · apply Finset.Subset.antisymm upperF
    apply lower
    · rw [inverseCompute,wires_append,wires_append,wires_append,hk.1]
      exact Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
    · rw [inverseCompute,wires_append,wires_append]
      exact factor.1.trans (Finset.subset_union_right.trans Finset.subset_union_left)
    · exact hcover.1.trans (Finset.union_subset_union (by rw [inverseCompute,wires_append]; exact Finset.subset_union_right) (Finset.Subset.refl _))
  · apply Finset.Subset.antisymm upperB
    apply lower
    · rw [inverseUncompute,wires_append,hk.2]; exact Finset.subset_union_right
    · rw [inverseUncompute,wires_append,wires_append,wires_append]
      exact factor.2.trans (Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left))
    · exact hcover.2.trans (Finset.union_subset_union (by rw [inverseUncompute,wires_append,wires_append,wires_append]; exact Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)) (Finset.Subset.refl _))

theorem inverseLoop_wires (L : InverseLoopLayout)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hd : 2≤L.first.data.width) (hwidth : L.first.data.width=L.arithmetic.width+1)
    (ha : L.a.length=L.arithmetic.width+1)
    (ht : L.temp.length=L.arithmetic.width+1) (ho : L.out.length=L.arithmetic.width+1)
    (hl : L.first.low.length=256) (hm : L.arithmetic.width=256) (q : Nat) :
    wires (inverseLoop L q)=L.usedWires.toFinset := by
  have hc := inverseCompute_wires L hn hw hd hwidth ha ht hl hm q
  have hr : L.middle.r.length=L.out.length := by
    change (L.middle.data.reg .r).length=_
    rw [InverseLoopLayout.middle,loopEnd_data,L.first.data_reg_length,hl,ho,hm]
  have hcopy := copyRegister_wires none L.middle.r L.out hr
  have hne : L.middle.r.isEmpty=false := by
    cases he : L.middle.r with
    | nil => rw [he] at hr; simp [ho] at hr
    | cons a as => rfl
  simp only [hne,Bool.false_eq_true,if_false,Option.toList_none,List.nil_append] at hcopy
  rw [inverseLoop,wires_append,wires_append,hc.1,hc.2,hcopy]
  ext w
  have hmem : w∈L.middle.r → w∈L.usedCoreWires := fun hh =>
    List.mem_append_left _ (L.reg_first_used .r (by decide) hh)
  change _ ↔ w∈(L.usedCoreWires++L.out).toFinset
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_append]
  constructor
  · rintro ((h|h)|h)
    · exact Or.inl h
    · exact h.elim (fun hh => Or.inl (hmem hh)) Or.inr
    · exact Or.inl h
  · rintro (h|h)
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inr h))

end ECDSAAdd.Arithmetic
