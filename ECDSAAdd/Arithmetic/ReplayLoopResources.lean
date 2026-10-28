import ECDSAAdd.Arithmetic.ReplayLoopProof

namespace ECDSAAdd.Arithmetic

/-- 活动比较计算/清理各十门，包含在每格账本中。 -/
theorem replayRound_counts (L : ReplayLayout) (n p i : Nat) (rs : List RoundRecord) (r : RoundRecord)
    (hv : L.Valid n rs) (hr : r∈rs) (hn : 0<n) :
    toffoliCount (replayRound L r p i)=13*n+21 ∧
    measurementCount (replayRound L r p i)=8*n+19 ∧
    toffoliCount (replayUnround L r p i)=11*n+19 ∧
    measurementCount (replayUnround L r p i)=6*n+18 := by
  have hc := counterActiveXor_counts L.counter L.active i
  rw [hv.counterWidth] at hc
  have hs := replayCell_counts L.active r.swap r.subtract L.payload n p hv.widths
    (ReplayValues.control_nodup _ _ _ _ (hv.cell L n rs r hr) r.subtract (by simp)) hn
  simp only [replayRound,replayUnround,toffoliCount_append,measurementCount_append,hc.1,hc.2,
    hs.1,hs.2.1,hs.2.2.1,hs.2.2.2]
  omega

theorem replayLoop_counts (L : ReplayLayout) (n p i : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (hn : 0<n) :
    toffoliCount (replayLoop L p i rs)=rs.length*(13*n+21) ∧
    measurementCount (replayLoop L p i rs)=rs.length*(8*n+19) ∧
    toffoliCount (replayUnloop L p i rs)=rs.length*(11*n+19) ∧
    measurementCount (replayUnloop L p i rs)=rs.length*(6*n+18) := by
  induction rs generalizing i with
  | nil => simp [replayLoop,replayUnloop,toffoliCount,measurementCount]
  | cons r rs ih =>
    have hr := replayRound_counts L n p i (r::rs) r hv (by simp) hn
    have ht := ih (i+1) (hv.tail L n r rs)
    simp only [replayLoop,replayUnloop,toffoliCount_append,measurementCount_append,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,List.length_cons]
    refine ⟨?_,?_,?_,?_⟩ <;> ring

/-- 512轮正反回放的实证账本，已包含活动比较。 -/
theorem replay512_counts (L : ReplayLayout) (p : Nat) (rs : List RoundRecord)
    (hv : L.Valid 256 rs) (hl : rs.length=512) :
    toffoliCount (replayLoop L p 0 rs)=1714688 ∧
    measurementCount (replayLoop L p 0 rs)=1058304 ∧
    toffoliCount (replayUnloop L p 0 rs)=1451520 ∧
    measurementCount (replayUnloop L p 0 rs)=795648 := by
  simpa only [hl] using replayLoop_counts L 256 p 0 rs hv (by omega)

private theorem comparison_subset (L : ReplayLayout) (n i : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) : wires (counterActiveXor L.counter L.active i)⊆(L.wires rs).toFinset := by
  rw [counterActiveXor_wires]
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
  rcases hq with rfl|rfl|(hx|hy)|hc
  · simp [ReplayLayout.wires]
  · simp [ReplayLayout.wires,ModInPlaceLayout.wires,hv.cin]
  · simp [ReplayLayout.wires,hx]
  · simp [ReplayLayout.wires,ModInPlaceLayout.wires,hv.constant hy]
  · simp [ReplayLayout.wires,ModInPlaceLayout.wires,hv.carry hc]

/-- 比较临时位全借自格工作区；记录及计数器不会引入隐含银行。 -/
theorem replayLoop_wires_subset (L : ReplayLayout) (n p i : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (hn : 0<n) :
    wires (replayLoop L p i rs)⊆(L.wires rs).toFinset ∧
    wires (replayUnloop L p i rs)⊆(L.wires rs).toFinset := by
  induction rs generalizing i with
  | nil => simp [replayLoop,replayUnloop,wires]
  | cons r rs ih =>
    have ht := ih (i+1) (hv.tail L n r rs)
    have hc := comparison_subset L n i (r::rs) hv
    have hcell := replayCell_wires L.active r.swap r.subtract L.payload n p hv.widths hn
    have hsub : (L.wires rs).toFinset⊆(L.wires (r::rs)).toFinset := by
      intro q hq
      simp only [ReplayLayout.wires,List.flatMap_cons,List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
      tauto
    have hs : wires (replayCell L.active r.swap r.subtract L.payload p)⊆(L.wires (r::rs)).toFinset := by
      rw [hcell.1]
      intro q hq
      simp only [ReplayLayout.wires,List.flatMap_cons,RoundRecord.wires,List.mem_toFinset,
        List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
      tauto
    have hu : wires (replayUncell L.active r.swap r.subtract L.payload p)⊆(L.wires (r::rs)).toFinset := by
      rw [hcell.2]
      intro q hq
      have ha : q∈L.payload.a.take n → q∈L.payload.a := fun h => (List.take_sublist _ _).subset h
      simp only [ReplayLayout.wires,List.flatMap_cons,RoundRecord.wires,List.mem_toFinset,
        ModInPlaceLayout.wires,ModInPlaceLayout.work,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
      clear ht hc hcell hs hv hn
      tauto
    constructor
    · simpa only [replayLoop,replayRound,wires_append] using Finset.union_subset
        (Finset.union_subset (Finset.union_subset hc hs) hc) (ht.1.trans hsub)
    · simpa only [replayUnloop,replayUnround,wires_append] using Finset.union_subset
        (ht.2.trans hsub) (Finset.union_subset (Finset.union_subset hc hu) hc)

private theorem cell_subset_loop (L : ReplayLayout) (p i : Nat) (rs : List RoundRecord)
    (r : RoundRecord) (hr : r∈rs) :
    wires (replayCell L.active r.swap r.subtract L.payload p)⊆wires (replayLoop L p i rs) := by
  induction rs generalizing i with
  | nil => simp at hr
  | cons t ts ih =>
    rcases List.mem_cons.mp hr with he|he
    · subst t
      exact (by
        simp only [replayLoop,replayRound,wires_append]
        exact (Finset.subset_union_right.trans Finset.subset_union_left).trans Finset.subset_union_left)
    · exact (ih (i+1) he).trans (by simp only [replayLoop,wires_append]; exact Finset.subset_union_right)

/-- 非空正回放的支持恰为载荷、共享工作区、记录带、计数器与一个活动位。 -/
theorem replayLoop_wires (L : ReplayLayout) (n p i : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (hn : 0<n) (hne : rs≠[]) :
    wires (replayLoop L p i rs)=(L.wires rs).toFinset := by
  apply Finset.Subset.antisymm (replayLoop_wires_subset L n p i rs hv hn).1
  obtain ⟨r,ts,he⟩ := List.exists_cons_of_ne_nil hne
  subst rs
  have hcell : (L.active::r.swap::r.subtract::L.payload.wires).toFinset⊆wires (replayLoop L p i (r::ts)) := by
    have hh := cell_subset_loop L p i (r::ts) r (by simp)
    rwa [(replayCell_wires L.active r.swap r.subtract L.payload n p hv.widths hn).1] at hh
  have hcmp : wires (counterActiveXor L.counter L.active i)⊆wires (replayLoop L p i (r::ts)) := by
    simp only [replayLoop,replayRound,wires_append]
    exact ((Finset.subset_union_left).trans Finset.subset_union_left).trans Finset.subset_union_left
  intro q hq
  simp only [ReplayLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at hq
  rcases hq with ((hq|hq)|hq)|hq
  · subst q; exact hcell (by simp)
  · apply hcmp; rw [counterActiveXor_wires]; simp [hq]
  · obtain ⟨t,ht,hqt⟩ := List.mem_flatMap.mp hq
    have hh := cell_subset_loop L p i (r::ts) t ht
    rw [(replayCell_wires L.active t.swap t.subtract L.payload n p hv.widths hn).1] at hh
    apply hh
    simpa only [List.mem_toFinset,RoundRecord.wires,List.mem_cons,List.not_mem_nil,or_false] using
      (show q=L.active ∨ q=t.swap ∨ q=t.subtract ∨ q∈L.payload.wires from by
        simp only [RoundRecord.wires,List.mem_cons,List.not_mem_nil,or_false] at hqt
        tauto)
  · exact hcell (by simp [hq])

/-- 固定512轮的实际支持；不是布局分配长度的估算。 -/
theorem replay512_qubits (L : ReplayLayout) (p : Nat) (rs : List RoundRecord)
    (hv : L.Valid 256 rs) (hl : rs.length=512) :
    qubitCount (replayLoop L p 0 rs)=2321 ∧ qubitCount (replayUnloop L p 0 rs)≤2321 := by
  have len : (L.wires rs).length=2321 := by
    have hr : (rs.flatMap RoundRecord.wires).length=2*rs.length := by
      clear hl hv
      induction rs with
      | nil => rfl
      | cons r rs ih => simp only [List.flatMap_cons,List.length_append,RoundRecord.wires,List.length_cons,List.length_nil] at *; omega
    simp only [ReplayLayout.wires,List.length_cons,List.length_append,hr,hl,
      ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,ModAddCoreLayout.z,
      ModAddCoreLayout.work,List.length_nil,AdderLayout.x,List.length_map]
    have hw := hv.widths
    have hk := hv.counterWidth
    simp only [AdderLayout.width] at hk
    rw [hw.core.a,hw.core.low,hw.core.constant,hw.core.carry,hw.mask,hk]
  constructor
  · rw [qubitCount,replayLoop_wires L 256 p 0 rs hv (by omega) (by intro he; simp [he] at hl),
      List.toFinset_card_of_nodup hv.nodup,len]
  · have hc := Finset.card_le_card (replayLoop_wires_subset L 256 p 0 rs hv (by omega)).2
    rwa [List.toFinset_card_of_nodup hv.nodup,len] at hc

end ECDSAAdd.Arithmetic
