import ECDSAAdd.Arithmetic.Divsteps.StepLayout
import ECDSAAdd.Arithmetic.Divsteps.InverseForwardStep

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

private theorem selected_nodup (L : StepLayout) (h : L.Valid) (xs : List Wire)
    (hc : ∀ w, List.count w xs ≤ List.count w L.used) : xs.Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  exact (hc w).trans (List.nodup_iff_count.mp h.unique w)

theorem StepLayout.tags_away (L : StepLayout) (h : L.Valid) :
    List.Disjoint ([L.history.active,L.history.parity,L.history.swap]) (L.f++L.g.wires++L.fv.wires++L.gv++L.gmask++L.gcarry++L.vmask++L.vcarry++L.cz++L.z.wires++L.cc++[L.cin]) := by
  have hn : (([L.history.active,L.history.parity,L.history.swap])++(L.f++L.g.wires++L.fv.wires++L.gv++L.mask++L.carry++L.z.wires++[L.cin])).Nodup := by
    apply selected_nodup L h
    intro w
    simp only [StepLayout.used,StepLayout.data,StepLayout.work,StepLayout.histories,
      StepHistory.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  intro w hx hy
  apply hd (a := w)
  all_goals
    simp only [gmask,gcarry,vmask,vcarry,cz,cc,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hx hy ⊢
    aesop (add safe forward List.mem_of_mem_take)

theorem StepLayout.counter_away (L : StepLayout) (h : L.Valid) :
    List.Disjoint (L.history.active::L.history.swap::(L.cz++L.z.wires++L.cc)) (L.f++L.g.wires++L.fv.wires++L.gv) := by
  have hn : ((L.history.active::L.history.swap::(L.mask++L.z.wires++L.carry))++(L.f++L.g.wires++L.fv.wires++L.gv)).Nodup := by
    apply selected_nodup L h
    intro w
    simp only [StepLayout.used,StepLayout.data,StepLayout.work,StepLayout.histories,
      StepHistory.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  intro w hx hy
  apply hd (a := w)
  all_goals
    simp only [cz,cc,List.mem_append,List.mem_cons] at hx hy ⊢
    aesop (add safe forward List.mem_of_mem_take)

theorem StepLayout.routing_work_away (L : StepLayout) (h : L.Valid) :
    List.Disjoint (L.history.parity::L.cin::L.history.active::(L.gmask++L.gcarry++L.vmask++L.vcarry)) ((L.f++L.fv.wires)++(L.g.wires++L.gv)) := by
  have hn : ((L.history.parity::L.cin::L.history.active::(L.mask++L.carry))++((L.f++L.fv.wires)++(L.g.wires++L.gv))).Nodup := by
    apply selected_nodup L h
    intro w
    simp only [StepLayout.used,StepLayout.data,StepLayout.work,StepLayout.histories,
      StepHistory.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  intro w hx hy
  apply hd (a := w)
  all_goals
    simp only [gmask,gcarry,vmask,vcarry,List.mem_append,List.mem_cons] at hx hy ⊢
    aesop (add safe forward List.mem_of_mem_take)

theorem StepLayout.g_away (L : StepLayout) (h : L.Valid) :
    List.Disjoint (L.g.wires) (L.history.swap::L.history.parity::L.cin::L.history.active::(L.fv.wires++L.vmask++L.gv++L.vcarry)) := by
  have hn : ((L.g.wires)++(L.history.swap::L.history.parity::L.cin::L.history.active::(L.fv.wires++L.mask++L.gv++L.carry))).Nodup := by
    apply selected_nodup L h
    intro w
    simp only [StepLayout.used,StepLayout.data,StepLayout.work,StepLayout.histories,
      StepHistory.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  intro w hx hy
  apply hd (a := w)
  all_goals
    simp only [vmask,vcarry,List.mem_append,List.mem_cons] at hx hy ⊢
    aesop (add safe forward List.mem_of_mem_take)

theorem StepLayout.f_away (L : StepLayout) (h : L.Valid) :
    List.Disjoint (L.f) (L.fv.wires++L.gv) := by
  have hn : ((L.f)++(L.fv.wires++L.gv)).Nodup := by
    apply selected_nodup L h
    intro w
    simp only [StepLayout.used,StepLayout.data,StepLayout.work,StepLayout.histories,
      StepHistory.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  exact hd

theorem StepLayout.fv_gv_away (L : StepLayout) (h : L.Valid) :
    List.Disjoint (L.fv.wires) (L.gv) := by
  have hn : ((L.fv.wires)++(L.gv)).Nodup := by
    apply selected_nodup L h
    intro w
    simp only [StepLayout.used,StepLayout.data,StepLayout.work,StepLayout.histories,
      StepHistory.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  exact hd

theorem StepLayout.active_gv_away (L : StepLayout) (h : L.Valid) :
    List.Disjoint ([L.history.active]) (L.gv) := by
  have hn : (([L.history.active])++(L.gv)).Nodup := by
    apply selected_nodup L h
    intro w
    simp only [StepLayout.used,StepLayout.data,StepLayout.work,StepLayout.histories,
      StepHistory.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  exact hd

/-- Five signed data rows interpreted in the current physical view. -/
def StepLayout.Encodes (L : StepLayout) (st : ZState) (s : BasisState) : Prop :=
  signedRegValue L.f s=st.f ∧ signedRegValue L.g.wires s=st.g ∧
  signedRegValue L.fv.wires s=st.fv ∧ signedRegValue L.gv s=st.gv ∧
  signedRegValue L.z.wires s=st.z

/-- Numeric obligations are explicit, separately from physical allocation. -/
def StepLayout.Fits (L : StepLayout) (st : ZState) : Prop :=
  ∃ pB zB cB : Int, Bounds pB zB cB st ∧ st.f%2=1 ∧
    2*pB<((2^(L.g.middle.length+1):Nat):Int) ∧
    2*cB<((2^(L.gv.length-1):Nat):Int) ∧
    zB+1<((2^(L.z.wires.length-1):Nat):Int)

/-- Ready for one step, including all reserved future controls. -/
def StepLayout.Ready (L : StepLayout) (st : ZState) (s : BasisState) : Prop :=
  L.Encodes st s ∧ L.Clean s ∧ L.Fresh s ∧ L.FutureClean s

/-- Actual constructive inverse using this step's original views and history. -/
def StepLayout.undo (L : StepLayout) : Program :=
  inverseForwardStep L.history.swap L.history.parity L.cin L.history.active
    L.g.low L.g.sign L.fv.low L.fv.sign L.one L.z.sign
    L.f L.g.middle L.gmask L.gcarry L.fv.middle L.vmask L.gv L.vcarry
    L.cz L.z.wires L.cc L.bits

private theorem clean_controls (L : StepLayout) (s : BasisState) (hc : L.Clean s) :
    s L.one=false ∧ s L.cin=false ∧ ∀ b∈L.bits,s b.work=false := by
  refine ⟨hc _ (by simp [StepLayout.work]),hc _ (by simp [StepLayout.work]),?_⟩
  intro b hb
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
  exact hc _ (by
    simp only [StepLayout.work,List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨w,hw,rfl⟩)))

private theorem fresh_controls (L : StepLayout) (s : BasisState) (hf : L.Fresh s) :
    s L.history.swap=false ∧ s L.history.parity=false ∧ s L.history.active=false :=
  ⟨hf _ (by simp [StepHistory.wires]),hf _ (by simp [StepHistory.wires]),
    hf _ (by simp [StepHistory.wires])⟩

theorem StepLayout.next_static (L : StepLayout) :
    L.next.f=L.f ∧ L.next.fv=L.fv ∧ L.next.gv=L.gv ∧ L.next.z=L.z := by
  unfold next nextHistory halfView
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem StepLayout.next_clean (L : StepLayout) (s : BasisState) :
    L.next.Clean s ↔ L.Clean s := by
  have hh := L.halfView_clean s
  unfold next nextHistory
  split <;> exact hh

theorem StepLayout.program_zSlot_controls (L : StepLayout) (h : L.Valid) (st : ZState)
    (hfit : L.Fits st) (s : State) (m : List Bool)
    (he : L.Encodes st s.basis) (hc : L.Clean s.basis) (hf : L.Fresh s.basis) :
    (run L.program m s).phase=s.phase ∧
    L.next.Encodes (zSlot st) (run L.program m s).basis ∧
    L.next.Clean (run L.program m s).basis ∧
    (run L.program m s).basis L.history.active=activeControl st ∧
    (run L.program m s).basis L.history.parity=parityControl st ∧
    (run L.program m s).basis L.history.swap=swapControl st := by
  obtain ⟨pB,zB,cB,hb,ho,hgf,hvf,hzf⟩ := hfit
  obtain ⟨hgm,hvm,hcz,hgk,hvk,hcc⟩ := L.prefix_lengths h
  obtain ⟨gm,vm,cz,gk,vk,cc⟩ := L.clean_prefixes s.basis hc
  obtain ⟨one,cin,work⟩ := clean_controls L s.basis hc
  obtain ⟨q,parity,active⟩ := fresh_controls L s.basis hf
  obtain ⟨phase,f,g,fv,gv,z,frame,ha,hp,hq⟩ := forwardStep_zSlot_controls L.history.swap L.history.parity L.cin L.history.active
    L.g.low L.g.sign L.fv.low L.fv.sign L.one L.z.sign
    L.f L.g.middle L.gmask L.gcarry L.fv.middle L.vmask L.gv L.vcarry
    L.cz L.z.wires L.cc (L.z.low::L.z.middle) L.bits
    (L.activity_nodup h) (L.control_routing_nodup h).1 L.bits_inputs rfl
    (L.tags_away h) (L.arithmetic_nodup h).2.2 hcz hcc (by simp [StepRow.wires]) (L.counter_away h)
    (L.control_routing_nodup h).2.1 h.integers h.coefficients (L.routing_work_away h)
    (L.arithmetic_nodup h).1 (L.arithmetic_nodup h).2.1 (L.control_routing_nodup h).2.2
    (L.fv_gv_away h) (fun hh => L.active_gv_away h (by simp) hh) (L.g_away h) (L.f_away h)
    (h.integers.trans hgm.symm) (by simpa [StepRow.wires] using hgm)
    (by simpa [StepRow.wires] using hgk) (h.coefficients.trans hvm.symm) hvm hvk
    st pB zB cB hb ho hgf hvf hzf
    s m one work q parity active cin he.1 he.2.1 he.2.2.1 he.2.2.2.1
    gm gk cz he.2.2.2.2 cc vm vk
  refine ⟨phase,?_,?_,ha,hp,hq⟩
  · simp only [Encodes,L.next_static.1,L.next_static.2.1,L.next_static.2.2.1,
      L.next_static.2.2.2,L.next_g]
    exact ⟨f,g,fv,gv,z⟩
  · apply (L.next_clean _).mpr
    intro w hw
    have hout : w∉L.history.active::L.history.parity::L.history.swap::L.data := by
      intro hin
      have sep := L.separation h
      simp only [List.mem_cons] at hin
      rcases hin with ha|hp|hq|hd
      · exact List.disjoint_left.mp sep.2.2.2.2.2 hw (by simp [histories,StepHistory.wires,ha])
      · exact List.disjoint_left.mp sep.2.2.2.2.2 hw (by simp [histories,StepHistory.wires,hp])
      · exact List.disjoint_left.mp sep.2.2.2.2.2 hw (by simp [histories,StepHistory.wires,hq])
      · exact List.disjoint_left.mp sep.2.2.2.1 hd hw
    exact (frame w hout).trans (hc w hw)

theorem StepLayout.program_zSlot (L : StepLayout) (h : L.Valid) (st : ZState)
    (hfit : L.Fits st) (s : State) (m : List Bool)
    (he : L.Encodes st s.basis) (hc : L.Clean s.basis) (hf : L.Fresh s.basis) :
    (run L.program m s).phase=s.phase ∧
    L.next.Encodes (zSlot st) (run L.program m s).basis ∧
    L.next.Clean (run L.program m s).basis := by
  obtain ⟨hp,he,hc,_,_,_⟩ := L.program_zSlot_controls h st hfit s m he hc hf
  exact ⟨hp,he,hc⟩

theorem StepLayout.undo_after (L : StepLayout) (h : L.Valid) (st : ZState)
    (hfit : L.Fits st) (s : State) (mf mi : List Bool)
    (he : L.Encodes st s.basis) (hc : L.Clean s.basis) (hf : L.Fresh s.basis) :
    run L.undo mi (run L.program mf s)=s := by
  obtain ⟨pB,zB,cB,hb,ho,hgf,hvf,hzf⟩ := hfit
  obtain ⟨hgm,hvm,hcz,hgk,hvk,hcc⟩ := L.prefix_lengths h
  obtain ⟨gm,vm,cz,gk,vk,cc⟩ := L.clean_prefixes s.basis hc
  obtain ⟨one,cin,work⟩ := clean_controls L s.basis hc
  obtain ⟨q,parity,active⟩ := fresh_controls L s.basis hf
  exact inverseForwardStep_after L.history.swap L.history.parity L.cin L.history.active
    L.g.low L.g.sign L.fv.low L.fv.sign L.one L.z.sign
    L.f L.g.middle L.gmask L.gcarry L.fv.middle L.vmask L.gv L.vcarry
    L.cz L.z.wires L.cc (L.z.low::L.z.middle) L.bits
    (L.activity_nodup h) (L.control_routing_nodup h).1 L.bits_inputs rfl
    (L.tags_away h) (L.arithmetic_nodup h).2.2 hcz hcc (L.counter_away h)
    (L.control_routing_nodup h).2.1 h.integers h.coefficients (L.routing_work_away h)
    (L.arithmetic_nodup h).1 (L.arithmetic_nodup h).2.1 (L.control_routing_nodup h).2.2
    (L.fv_gv_away h) (fun hh => L.active_gv_away h (by simp) hh) (L.g_away h) (L.f_away h)
    (h.integers.trans hgm.symm) (by simpa [StepRow.wires] using hgm)
    (by simpa [StepRow.wires] using hgk) (h.coefficients.trans hvm.symm) hvm hvk
    st pB zB cB hb ho hgf hvf
    s mf mi one work q parity active cin he.1 he.2.1 he.2.2.1 he.2.2.2.1
    gm gk cz he.2.2.2.2 cc vm vk

theorem StepLayout.program_spec (L : StepLayout) (h : L.Valid) (st : ZState)
    (hfit : L.Fits st) (hne : L.future≠[]) :
    Triple (L.Ready st) L.program (L.next.Ready (zSlot st)) := by
  intro s m hs
  obtain ⟨hp,he,hc⟩ := L.program_zSlot h st hfit s m hs.1 hs.2.1 hs.2.2.1
  obtain ⟨hf,hu⟩ := L.next_fresh h s m hs.2.2.2 hne
  exact ⟨hp,he,hc,hf,hu⟩

theorem StepLayout.undo_counts (L : StepLayout) (h : L.Valid) (n v k : Nat)
    (hw : L.Sized n v k) :
    toffoliCount L.undo=5*n+5*v+k-4 ∧
    measurementCount L.undo=4*n+3*v+k-5 := by
  obtain ⟨hgm,hvm,hcz,hgc,hvc,hcc⟩ := L.prefix_lengths h
  have hh := inverseForwardStep_counts L.history.swap L.history.parity L.cin L.history.active
    L.g.low L.g.sign L.fv.low L.fv.sign L.one L.z.sign
    L.f L.g.middle L.gmask L.gcarry L.fv.middle L.vmask L.gv L.vcarry
    L.cz L.z.wires L.cc L.bits (L.control_routing_nodup h).2.1 h.integers h.coefficients
    L.bits_inputs (h.integers.trans hgm.symm) (by simpa [StepRow.wires] using hgm)
    (by simpa [StepRow.wires] using hgc) (h.coefficients.trans hvm.symm) hvm hvc hcz hcc
  have hn : L.g.middle.length+2=n := by simpa [Sized,StepRow.wires] using hw.1
  have hv : L.fv.middle.length+2=v := by
    simpa [StepRow.wires] using h.coefficients.trans hw.2.1
  simpa only [undo,hn,hv,hw.2.2] using hh

theorem StepLayout.undo_current_support (L : StepLayout) (h : L.Valid) :
    wires L.undo⊆(L.data++L.work++L.history.wires).toFinset := by
  obtain ⟨hgm,hvm,hcz,hgc,hvc,hcc⟩ := L.prefix_lengths h
  have hs := inverseForwardStep_wires_subset L.history.swap L.history.parity L.cin L.history.active
    L.g.low L.g.sign L.fv.low L.fv.sign L.one L.z.sign
    L.f L.g.middle L.gmask L.gcarry L.fv.middle L.vmask L.gv L.vcarry
    L.cz L.z.wires L.cc L.bits h.integers h.coefficients
    (h.integers.trans hgm.symm) (by simpa [StepRow.wires] using hgm)
    (by simpa [StepRow.wires] using hgc) (h.coefficients.trans hvm.symm) hvm hvc hcz hcc
  apply hs.trans
  intro w hw
  have hm (k : Nat) : w∈L.mask.take k → w∈L.mask := List.mem_of_mem_take
  have hc (k : Nat) : w∈L.carry.take k → w∈L.carry := List.mem_of_mem_take
  have hb : w∈L.bits.flatMap ZeroBit.wires → w∈L.g.wires ∨ w∈L.g.wires.map L.detect := by
    intro hw
    simp only [bits,List.mem_flatMap,List.mem_map,ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with ⟨b,⟨a,ha,rfl⟩,hh⟩
    rcases hh with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr (List.mem_map.mpr ⟨a,ha,rfl⟩)
  simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append] at hw
  have hg : w∈L.g.wires ↔ w=L.g.low ∨ w∈L.g.middle ∨ w=L.g.sign := by simp [StepRow.wires]
  have hv : w∈L.fv.wires ↔ w=L.fv.low ∨ w∈L.fv.middle ∨ w=L.fv.sign := by simp [StepRow.wires]
  have hz : w∈L.z.wires ↔ w=L.z.low ∨ w∈L.z.middle ∨ w=L.z.sign := by simp [StepRow.wires]
  have hm1 := hm L.g.wires.length
  have hm2 := hm L.gv.length
  have hm3 := hm L.z.wires.length
  have hc1 := hc (L.g.wires.length-1)
  have hc2 := hc (L.gv.length-1)
  have hc3 := hc (L.z.wires.length-1)
  simp only [gmask,vmask,cz,gcarry,vcarry,cc] at hw
  simp only [List.mem_toFinset,data,work,StepHistory.wires,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,hg,hv,hz]
  simp only [hg] at hb
  simp only [hz] at hw
  clear hs h hgm hvm hcz hgc hvc hcc hm hc hg hv hz
  simp only [or_assoc] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals
    first
    | have hh := hb hw
      rcases hh with (hh|hh|hh)|hh <;> simp_all only [or_true,true_or]
    | simp_all only [or_true,true_or]

theorem StepLayout.undo_support (L : StepLayout) (h : L.Valid) :
    wires L.undo⊆L.used.toFinset := by
  apply (L.undo_current_support h).trans
  intro w hw
  simp only [List.mem_toFinset,List.mem_append] at hw
  simp only [List.mem_toFinset,used,histories,List.mem_append]
  tauto

end ECDSAAdd.Arithmetic.Divsteps
