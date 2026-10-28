import ECDSAAdd.Arithmetic.Paper935.FoldCompareCell

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The author's compare sweep, controlled keeper toggle, and measured cleanup. -/
def foldCompareBlock (control flag : Wire) : List FoldCell → Option Wire → Program
  | [],cin => cin.toList.map fun d => .CCX control d flag
  | b::rest,cin => foldCompareForward b.literal b.data b.carry cin ++
      foldCompareBlock control flag rest (b.next cin) ++ foldCompareBackward b.literal b.data b.carry cin

private theorem compare_geometry (control flag : Wire) (b : FoldCell) (rest : List FoldCell)
    (cin : Option Wire) (hn : ([control,flag]++cin.toList++(b::rest).flatMap FoldCell.wires).Nodup) :
    ([b.data,b.carry]++cin.toList).Nodup ∧
    ([control,flag]++(b.next cin).toList++rest.flatMap FoldCell.wires).Nodup ∧
    ([control,flag,b.data,b.carry]++cin.toList).Nodup ∧
    List.Disjoint [control,flag,b.data,b.carry] (rest.flatMap FoldCell.wires) := by
  have nextCount (q : Wire) : (b.next cin).toList.count q ≤ cin.toList.count q+[b.carry].count q := by
    cases cin <;> cases hb : b.literal <;> simp [FoldCell.next,hb]
  have localNd : ([control,flag,b.data,b.carry]++cin.toList).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  refine ⟨List.Nodup.of_cons (List.Nodup.of_cons localNd),?_,localNd,?_⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have hnext := nextCount q
    simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h hnext ⊢
    omega
  · apply List.disjoint_left.mpr
    intro q hq hr
    have h := List.nodup_iff_count.mp hn q
    have hc := List.count_pos_iff.mpr hq
    have ht := List.count_pos_iff.mpr hr
    simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h hc
    omega

/-- No phase debt or scratch remains after the actual comparison. -/
theorem foldCompareBlock_run (control flag : Wire) (cells : List FoldCell) (cin : Option Wire)
    (hn : ([control,flag]++cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false) :
    run (foldCompareBlock control flag cells cin) m s=
      ⟨s.phase,writeBit s.basis flag (s.basis flag ^^
        (s.basis control && foldBlockOverflow cells true ((cin.map s.basis).getD false) s.basis))⟩ := by
  induction cells generalizing cin s m with
  | nil =>
    cases cin with
    | none =>
      simp [foldCompareBlock,foldBlockOverflow,run]
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=flag <;> simp [writeBit,Function.update,hq]
    | some d => simp [foldCompareBlock,foldBlockOverflow,run]
  | cons b rest ih =>
    obtain ⟨localNd,tailNd,allNd,apart⟩ := compare_geometry control flag b rest cin hn
    have nd : [control,flag,b.data,b.carry].Nodup := (List.nodup_append.mp allNd).1
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
    obtain ⟨⟨hcf,hcd,hct⟩,⟨hfd,hft⟩,hdt⟩ := nd
    let carry := carryBit (s.basis b.data) b.literal ((cin.map s.basis).getD false)
    let prepared := writeBit s.basis b.carry carry
    let toggle := s.basis flag ^^ (s.basis control && foldBlockOverflow rest true
      (((b.next cin).map prepared).getD false) prepared)
    let after := writeBit prepared flag toggle
    have ctrl : prepared control=s.basis control := by simp [prepared,writeBit,hct]
    have flagSame : prepared flag=s.basis flag := by simp [prepared,writeBit,hft]
    have next : ((b.next cin).map prepared).getD false=carry := by
      cases hi : cin <;> cases hb : b.literal <;>
        simp [FoldCell.next,hb,prepared,writeBit,carry,hi,carryBit]
    have cinAway (q : Wire) (hq : q∈cin.toList) : q≠b.carry ∧ q≠flag := by
      have dis := (List.nodup_append'.mp allNd).2.2
      constructor
      · intro e; subst q
        exact List.disjoint_left.mp dis (show b.carry∈[control,flag,b.data,b.carry] by simp) hq
      · intro e; subst q
        exact List.disjoint_left.mp dis (show flag∈[control,flag,b.data,b.carry] by simp) hq
    have input : (cin.map after).getD false=(cin.map s.basis).getD false := by
      cases hi : cin with
      | none => rfl
      | some q =>
        obtain ⟨ht,hf⟩ := cinAway q (by simp [hi])
        simp [after,prepared,writeBit,ht,hf]
    have dataSame : after b.data=s.basis b.data := by simp [after,prepared,writeBit,Ne.symm hfd,hdt]
    have known : after b.carry=carryBit (after b.data) b.literal ((cin.map after).getD false) := by
      rw [dataSame,input]
      simp [after,prepared,writeBit,Ne.symm hft,carry]
    have nextClean : ∀ c∈rest,prepared c.carry=false := by
      intro c hc
      have mem : c.carry∈rest.flatMap FoldCell.wires := List.mem_flatMap.mpr ⟨c,hc,by simp [FoldCell.wires]⟩
      have ht : c.carry≠b.carry := by
        intro e
        exact List.disjoint_left.mp apart (show b.carry∈[control,flag,b.data,b.carry] by simp) (e ▸ mem)
      simpa [prepared,writeBit,ht] using clean c (by simp [hc])
    have same : foldBlockOverflow rest true carry prepared=foldBlockOverflow rest true carry s.basis := by
      apply foldBlockOverflow_congr
      intro c hc
      have mem : c.data∈rest.flatMap FoldCell.wires := List.mem_flatMap.mpr ⟨c,hc,by simp [FoldCell.wires]⟩
      have ht : c.data≠b.carry := by
        intro e
        exact List.disjoint_left.mp apart (show b.carry∈[control,flag,b.data,b.carry] by simp) (e ▸ mem)
      simp [prepared,writeBit,ht]
    rw [foldCompareBlock,run_append,run_take,run_append,run_take,
      foldCompareForward_run b.literal b.data b.carry cin localNd s m (clean b (by simp)),
      (foldCompareForward_counts b.literal b.data b.carry cin).2,List.drop_zero]
    rw [ih (b.next cin) tailNd ⟨s.phase,prepared⟩ m nextClean]
    simp only [ctrl,flagSame]
    rw [foldCompareBackward_run b.literal b.data b.carry cin localNd ⟨s.phase,after⟩ _ known]
    apply congrArg (State.mk s.phase)
    have toggleEq : toggle=(s.basis flag ^^ (s.basis control &&
        foldBlockOverflow (b::rest) true ((cin.map s.basis).getD false) s.basis)) := by
      simp only [toggle,next,same,foldBlockOverflow,Bool.and_true,carry]
    change writeBit (writeBit prepared flag toggle) b.carry false=_
    rw [toggleEq]
    funext q
    by_cases hf : q=flag <;> by_cases ht : q=b.carry <;>
      simp [prepared,writeBit,Function.update,hf,ht,hft,Ne.symm hft,clean b (by simp)]

theorem foldCompareBlock_counts (control flag : Wire) (cells : List FoldCell) (cin : Option Wire) :
    toffoliCount (foldCompareBlock control flag cells cin)≤cells.length+1 ∧
    measurementCount (foldCompareBlock control flag cells cin)≤cells.length := by
  induction cells generalizing cin with
  | nil => cases cin <;> simp [foldCompareBlock,toffoliCount,measurementCount]
  | cons b rest ih =>
    have h := ih (b.next cin)
    simp only [foldCompareBlock,toffoliCount_append,measurementCount_append,
      (foldCompareForward_counts _ _ _ _).1,(foldCompareForward_counts _ _ _ _).2,
      (foldCompareBackward_counts _ _ _ _).1,(foldCompareBackward_counts _ _ _ _).2,
      List.length_cons]
    split <;> split <;> omega

theorem foldCompareBlock_support (control flag : Wire) (cells : List FoldCell) (cin : Option Wire) :
    wires (foldCompareBlock control flag cells cin) ⊆
      ([control,flag]++cin.toList++cells.flatMap FoldCell.wires).toFinset := by
  induction cells generalizing cin with
  | nil => cases cin <;> simp [foldCompareBlock,wires,Instr.wires,Finset.insert_subset_iff]
  | cons b rest ih =>
    have cell := foldCompare_support b.literal b.data b.carry cin
    rw [wires_append,Finset.union_subset_iff] at cell
    have localSubset : ([b.data,b.carry]++cin.toList).toFinset ⊆
        ([control,flag]++cin.toList++(b::rest).flatMap FoldCell.wires).toFinset := by
      intro q h
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.flatMap_cons,FoldCell.wires,
        List.not_mem_nil,or_false] at h ⊢
      tauto
    have tailSubset : ([control,flag]++(b.next cin).toList++rest.flatMap FoldCell.wires).toFinset ⊆
        ([control,flag]++cin.toList++(b::rest).flatMap FoldCell.wires).toFinset := by
      intro q h
      cases hc : cin <;> cases hb : b.literal <;>
        simp only [FoldCell.next,hc,hb,Bool.false_or,Bool.true_or,Option.isSome_none,Option.isSome_some,
          Bool.false_eq_true,if_false,if_true,Option.toList_none,Option.toList_some,
          List.mem_toFinset,List.mem_append,List.mem_cons,List.flatMap_cons,FoldCell.wires,
          List.not_mem_nil,or_false] at h ⊢ <;> tauto
    rw [foldCompareBlock,wires_append,wires_append,Finset.union_subset_iff,Finset.union_subset_iff]
    exact ⟨⟨Finset.Subset.trans cell.1 localSubset,Finset.Subset.trans (ih (b.next cin)) tailSubset⟩,
      Finset.Subset.trans cell.2 localSubset⟩

theorem foldCompareBlock_physical (control flag : Wire) (cells : List FoldCell) (cin : Option Wire)
    (hn : ([control,flag]++cin.toList++cells.flatMap FoldCell.wires).Nodup) :
    GatePhysical (foldCompareBlock control flag cells cin) := by
  induction cells generalizing cin with
  | nil =>
    cases cin <;> simp_all [foldCompareBlock,GatePhysical,ECDSAAdd.RecordedQuantum.PhysicalInstr,
      ProperGate,List.nodup_cons,ne_comm]
  | cons b rest ih =>
    obtain ⟨localNd,tailNd,_,_⟩ := compare_geometry control flag b rest cin hn
    have cell := foldCompare_physical b.literal b.data b.carry cin localNd
    rw [gatePhysical_append] at cell
    rw [foldCompareBlock,gatePhysical_append,gatePhysical_append]
    exact ⟨⟨cell.1,ih (b.next cin) tailNd⟩,cell.2⟩

end ECDSAAdd.Arithmetic.Paper935
