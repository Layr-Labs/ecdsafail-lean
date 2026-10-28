import ECDSAAdd.Arithmetic.FusedSignedHalfPacked
import ECDSAAdd.Arithmetic.RetainedThreshold

/-! Exact retained-carry threshold alternative. The accepted canonical endpoint
remains unchanged; this alternative must pass full composition before use. -/
namespace ECDSAAdd.Arithmetic

/-- Load a selected constant, retain the full addition carry frame, and borrow
its unloaded constant word as the full comparison carry. Both original operands
return before any retained carry is measured. -/
def fusedRetainedThresholdCore (load : Program) (R A C retained : List Wire)
    (cin h : Wire) : Program :=
  load ++ retainedAddStart C A retained cin ++ load ++
    compareLt none R A C cin h ++ load ++ retainedAddFinish C A retained cin ++ load

/-- Includes every full comparison carry and retained carry erasure. -/
theorem fusedRetainedThresholdCore_counts (load : Program) (R A C retained : List Wire)
    (cin h : Wire) (hRA : R.length=A.length) (hCA : C.length=A.length)
    (hc : retained.length+1=A.length) (hl : toffoliCount load=0) (hm : measurementCount load=0) :
    toffoliCount (fusedRetainedThresholdCore load R A C retained cin h)=2*A.length-1 ∧
    measurementCount (fusedRetainedThresholdCore load R A C retained cin h)=2*A.length-1 := by
  have ha := retainedAdd_counts C A retained cin hCA hc
  have hp := compareLt_counts none R A C cin h hRA hCA
  constructor
  · simp only [fusedRetainedThresholdCore,toffoliCount_append,hl,ha.1,ha.2.2.1,hp.1,
      Option.isSome,Bool.false_eq_true,if_false,Nat.add_zero,Nat.zero_add]
    omega
  · simp only [fusedRetainedThresholdCore,measurementCount_append,hm,ha.2.1,ha.2.2.2,hp.2.1,
      Nat.add_zero,Nat.zero_add]
    omega

/-- Actual selected-threshold stream, with old reduction-bit convention unchanged. -/
def fusedRetainedThresholdRecover (b q t d h : Wire) (R A C retained : List Wire)
    (cin : Wire) (K P : Nat) : Program :=
  fusedRetainedThresholdCore (fusedThresholdWordLoad b q t d C K P) R A C retained cin h ++ [.CX b h]

theorem fusedRetainedThresholdRecover_counts (b q t d h : Wire) (R A C retained : List Wire)
    (cin : Wire) (K P : Nat) (hRA : R.length=A.length) (hCA : C.length=A.length)
    (hc : retained.length+1=A.length) :
    toffoliCount (fusedRetainedThresholdRecover b q t d h R A C retained cin K P)=2*A.length-1 ∧
    measurementCount (fusedRetainedThresholdRecover b q t d h R A C retained cin K P)=2*A.length-1 := by
  have hl := fusedThresholdWordLoad_counts b q t d C K P
  have hr := fusedRetainedThresholdCore_counts (fusedThresholdWordLoad b q t d C K P) R A C retained cin h
    hRA hCA hc hl.1 hl.2
  simp only [fusedRetainedThresholdRecover,toffoliCount_append,measurementCount_append,hr.1,hr.2,
    show toffoliCount [.CX b h]=0 by rfl,show measurementCount [.CX b h]=0 by rfl,Nat.add_zero]
  trivial

set_option maxHeartbeats 1000000 in
/-- All-record retained threshold core. The selected constant loader reads only
ctl, which is disjoint from every arithmetic wire and h. C is a genuine zero
comparison carry between unload/reload; finish sees the restored exact image. -/
theorem fusedRetainedThresholdCore_correct (load : Program) (ctl R A C retained : List Wire)
    (cin h : Wire) (F : Nat) (hn : (h::cin::(R++A++C++retained)).Nodup)
    (hctl : ctl.Disjoint (h::cin::(R++A++C++retained)))
    (hRA : R.length=A.length) (hCA : C.length=A.length) (hc : retained.length+1=A.length)
    (hm : measurementCount load=0) (s : State) (record : List Bool)
    (hload : ∀ st : State, ∀ m : List Bool, (∀ w∈ctl,st.basis w=s.basis w) →
      (run load m st).phase=st.phase ∧
      (∀ w,w∉C → (run load m st).basis w=st.basis w) ∧
      regValue C (run load m st).basis=(regValue C st.basis^^^F))
    (hC0 : regValue C s.basis=0) (hk0 : regValue retained s.basis=0) (hi : s.basis cin=false) :
    (run (fusedRetainedThresholdCore load R A C retained cin h) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedRetainedThresholdCore load R A C retained cin h) record s).basis w=s.basis w) ∧
    (run (fusedRetainedThresholdCore load R A C retained cin h) record s).basis h=
      (s.basis h^^decide (regValue R s.basis<(regValue A s.basis+F)%2^A.length)) := by
  have nadd : (cin::(C++A++retained)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h1 := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at h1 ⊢
    omega
  have ncmp : (h::cin::(R++A++C)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h1 := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at h1 ⊢
    omega
  let foot := (cin::(C++A++retained)).toFinset
  have nh (w : Wire) (hw : w∈cin::(C++A++retained)) : w≠h := by
    intro he; subst w
    have h1 := List.nodup_iff_count.mp hn h
    have h2 := List.count_pos_iff.mpr hw
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h1 h2
    omega
  have disCA : C.Disjoint (A++retained) := by
    intro w hwC hwA
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hwC
    have h3 := List.count_pos_iff.mpr hwA
    simp only [List.count_cons,List.count_append] at h1 h3
    omega
  have awayC (w : Wire) (hw : w∈h::cin::(R++A++retained)) : w∉C := by
    intro hh
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hw
    have h3 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append] at h1 h2
    omega
  have awayAR (w : Wire) (hw : w∈h::cin::(R++C)) : w∉A++retained := by
    intro hh
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hw
    have h3 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append] at h1 h2 h3
    omega
  have ctlC (w : Wire) (hw : w∈ctl) : w∉C := by
    intro hh; exact List.disjoint_left.mp hctl hw (by simp [hh])
  have ctlAR (w : Wire) (hw : w∈ctl) : w∉A++retained := by
    intro hh; exact List.disjoint_left.mp hctl hw (by simp only [List.mem_cons,List.mem_append] at hh ⊢; tauto)
  have ctlH (w : Wire) (hw : w∈ctl) : w≠h := by
    intro hh; subst w; exact List.disjoint_left.mp hctl hw (by simp)
  have counts := retainedAdd_counts C A retained cin hCA hc
  obtain ⟨st1,hst1⟩ : ∃ st1 : State,run load record s=st1 := ⟨_,rfl⟩
  have f1 := hload s record (by intros; rfl)
  rw [hst1] at f1
  have ctr1 : ∀w∈ctl,st1.basis w=s.basis w := fun w hw => f1.2.1 w (ctlC w hw)
  have k1 : regValue retained st1.basis=0 := (regValue_congr _ _ _ (fun w hw =>
    f1.2.1 w (awayC w (by simp [hw])))).trans hk0
  have c1 : regValue C st1.basis=F := by simpa only [hC0,Nat.zero_xor] using f1.2.2
  have a1 : regValue A st1.basis=regValue A s.basis := regValue_congr _ _ _ (fun w hw => f1.2.1 w (awayC w (by simp [hw])))
  have i1 : st1.basis cin=false := (f1.2.1 cin (awayC cin (by simp))).trans hi
  obtain ⟨st2,hst2⟩ : ∃ st2 : State,run (retainedAddStart C A retained cin) record st1=st2 := ⟨_,rfl⟩
  have f2 := retainedAddStart_correct C A retained cin nadd hCA hc st1 record ((regValue_zero _ _).mp k1)
  have image2 := retainedAdd_start_image C A retained cin nadd hCA hc st1 record ((regValue_zero _ _).mp k1)
  rw [hst2] at f2 image2
  have ctr2 : ∀w∈ctl,st2.basis w=s.basis w := fun w hw => (f2.2.1 w (ctlAR w hw)).trans (ctr1 w hw)
  have c2 : regValue C st2.basis=F := (regValue_congr _ _ _ (fun w hw =>
    f2.2.1 w (List.disjoint_left.mp disCA hw))).trans c1
  have a2 : regValue A st2.basis=(regValue A s.basis+F)%2^A.length := by
    simpa only [c1,a1,i1,Bool.toNat_false,Nat.add_zero,Nat.add_comm] using f2.2.2
  obtain ⟨st3,hst3⟩ : ∃ st3 : State,run load record st2=st3 := ⟨_,rfl⟩
  have f3 := hload st2 record ctr2
  rw [hst3] at f3
  have ctr3 : ∀w∈ctl,st3.basis w=s.basis w := fun w hw => (f3.2.1 w (ctlC w hw)).trans (ctr2 w hw)
  have c3 : regValue C st3.basis=0 := by simpa only [c2,Nat.xor_self] using f3.2.2
  have a3 : regValue A st3.basis=(regValue A s.basis+F)%2^A.length :=
    (regValue_congr _ _ _ (fun w hw => f3.2.1 w (awayC w (by simp [hw])))).trans a2
  have r3 : regValue R st3.basis=regValue R s.basis := regValue_congr _ _ _ (fun w hw =>
    (f3.2.1 w (awayC w (by simp [hw]))).trans ((f2.2.1 w (awayAR w (by simp [hw]))).trans
      (f1.2.1 w (awayC w (by simp [hw])))))
  have i3 : st3.basis cin=false := (f3.2.1 cin (awayC cin (by simp))).trans
    ((f2.2.1 cin (awayAR cin (by simp))).trans i1)
  obtain ⟨st4,hst4⟩ : ∃ st4 : State,run (compareLt none R A C cin h) record st3=st4 := ⟨_,rfl⟩
  have f4 := compareLt_correct none R A C cin h ncmp (by simp) hRA hCA st3 record i3 ((regValue_zero _ _).mp c3)
  rw [hst4] at f4
  have ctr4 : ∀w∈ctl,st4.basis w=s.basis w := fun w hw => (f4.2.1 w (ctlH w hw)).trans (ctr3 w hw)
  have c4 : regValue C st4.basis=0 := (regValue_congr _ _ _ (fun w hw => f4.2.1 w (nh w (by simp [hw])))).trans c3
  let r6 := record.drop (measurementCount (compareLt none R A C cin h))
  obtain ⟨st5,hst5⟩ : ∃ st5 : State,run load r6 st4=st5 := ⟨_,rfl⟩
  have f5 := hload st4 r6 ctr4
  rw [hst5] at f5
  have c5 : regValue C st5.basis=F := by simpa only [c4,Nat.zero_xor] using f5.2.2
  have same5 : ∀w∈foot,st5.basis w=st2.basis w := by
    intro w hw
    have hm' : w∈cin::(C++A++retained) := List.mem_toFinset.mp hw
    by_cases hwC : w∈C
    · exact (regValue_eq_iff C _ _).mp (c5.trans c2.symm) w hwC
    exact (f5.2.1 w hwC).trans ((f4.2.1 w (nh w hm')).trans (f3.2.1 w hwC))
  have phase5 : st5.phase=st2.phase := f5.1.trans (f4.1.trans f3.1)
  have image5 := retainedAdd_image_congr C A retained cin st1.basis st2 st5 phase5 same5 image2
  obtain ⟨st6,hst6⟩ : ∃ st6 : State,run (retainedAddFinish C A retained cin) r6 st5=st6 := ⟨_,rfl⟩
  have f6 := retainedAdd_finish_image C A retained cin nadd hCA hc st1.basis st5 r6
    ((regValue_zero _ _).mp k1) image5
  rw [hst6] at f6
  have out6 (w : Wire) (hw : w∉foot) : st6.basis w=st5.basis w := by
    rw [←hst6]
    apply run_preserves_outside
    exact fun hh => hw ((retainedAdd_support C A retained cin).2 hh)
  have ctr5 : ∀w∈ctl,st5.basis w=s.basis w := fun w hw => (f5.2.1 w (ctlC w hw)).trans (ctr4 w hw)
  have ctr6 : ∀w∈ctl,st6.basis w=s.basis w := by
    intro w hw
    have hout : w∉foot := by
      intro hh
      exact List.disjoint_left.mp hctl hw (by have hm' := List.mem_toFinset.mp hh; simp only [List.mem_cons,List.mem_append] at hm' ⊢; tauto)
    exact (out6 w hout).trans (ctr5 w hw)
  have c6 : regValue C st6.basis=F := (regValue_congr _ _ _ (fun w hw => f6.2 w (by simp [hw]))).trans c1
  let r7 := record.drop (measurementCount (compareLt none R A C cin h)+measurementCount (retainedAddFinish C A retained cin))
  obtain ⟨st7,hst7⟩ : ∃ st7 : State,run load r7 st6=st7 := ⟨_,rfl⟩
  have f7 := hload st6 r7 ctr6
  rw [hst7] at f7
  have c7 : regValue C st7.basis=0 := by simpa only [c6,Nat.xor_self] using f7.2.2
  have hRun : run (fusedRetainedThresholdCore load R A C retained cin h) record s=st7 := by
    simp only [fusedRetainedThresholdCore,List.append_assoc,run_append,run_take,hm,counts.2.1,List.drop_zero]
    have l1 : run load (record.take 0) s=st1 := by rw [←hm,run_take]; exact hst1
    have l2 : run (retainedAddStart C A retained cin) (record.take 0) st1=st2 := by rw [←counts.2.1,run_take]; exact hst2
    have l3 : run load (record.take 0) st2=st3 := by rw [←hm,run_take]; exact hst3
    rw [l1,l2,l3,hst4]
    have l5 : run load (r6.take 0) st4=st5 := by rw [←hm,run_take]; exact hst5
    rw [l5,hst6,List.drop_drop,hst7]
  rw [hRun]
  refine ⟨f7.1.trans (f6.1.trans (f5.1.trans (f4.1.trans (f3.1.trans (f2.1.trans f1.1))))),?_,?_⟩
  · intro w hwh
    by_cases hwC : w∈C
    · exact (regValue_eq_iff C _ _).mp (c7.trans hC0.symm) w hwC
    rw [f7.2.1 w hwC]
    by_cases hwF : w∈foot
    · exact (f6.2 w hwF).trans (f1.2.1 w hwC)
    have hwAR : w∉A++retained := by intro hh; exact hwF (by simp only [foot,List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢; tauto)
    exact (out6 w hwF).trans ((f5.2.1 w hwC).trans ((f4.2.1 w hwh).trans
      ((f3.2.1 w hwC).trans ((f2.2.1 w hwAR).trans (f1.2.1 w hwC)))))
  · have hcH : h∉C := awayC h (by simp)
    have hF : h∉foot := by
      intro hh
      exact nh h (List.mem_toFinset.mp hh) rfl
    rw [f7.2.1 h hcH,out6 h hF,f5.2.1 h hcH,f4.2.2,r3,a3]
    have hh3 : st3.basis h=s.basis h := (f3.2.1 h hcH).trans
      ((f2.2.1 h (awayAR h (by simp))).trans (f1.2.1 h hcH))
    simp only [hh3,controlValue,Bool.true_and]

/-- The actual selected-constant wrapper has the same old reduction-bit
convention, with no approximation or record dependence. -/
theorem fusedRetainedThresholdRecover_correct (b q t d h : Wire) (R A C retained : List Wire)
    (cin : Wire) (K P : Nat) (hn : ([b,q,t,d,h,cin]++R++A++C++retained).Nodup)
    (hRA : R.length=A.length) (hCA : C.length=A.length) (hc : retained.length+1=A.length)
    (hK : K<2^C.length) (hP : P<2^C.length) (h1 : 1<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (hk0 : regValue retained s.basis=0) (hi : s.basis cin=false) :
    (run (fusedRetainedThresholdRecover b q t d h R A C retained cin K P) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedRetainedThresholdRecover b q t d h R A C retained cin K P) record s).basis w=s.basis w) ∧
    (run (fusedRetainedThresholdRecover b q t d h R A C retained cin K P) record s).basis h=
      ((s.basis h^^decide (regValue R s.basis<
        (regValue A s.basis+fusedThresholdWordValue (s.basis b) (s.basis q) (s.basis t) (s.basis d) K P)%2^A.length))^^s.basis b) := by
  have nload : ([b,q,t,d]++C).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have ncore : (h::cin::(R++A++C++retained)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have nctl : ([b,q,t,d]++(h::cin::(R++A++C++retained))).Nodup := by
    simpa only [List.append_assoc] using hn
  have disctl := (List.nodup_append'.mp nctl).2.2
  let F := fusedThresholdWordValue (s.basis b) (s.basis q) (s.basis t) (s.basis d) K P
  let load := fusedThresholdWordLoad b q t d C K P
  have hload (st : State) (m : List Bool) (hctrl : ∀ w∈[b,q,t,d],st.basis w=s.basis w) :
      (run load m st).phase=st.phase ∧
      (∀ w,w∉C → (run load m st).basis w=st.basis w) ∧
      regValue C (run load m st).basis=(regValue C st.basis^^^F) := by
    have hl := fusedThresholdWordLoad_correct b q t d C K P nload hK hP h1 st m
    refine ⟨hl.1,hl.2.1,?_⟩
    simpa only [hctrl b (by simp),hctrl q (by simp),hctrl t (by simp),hctrl d (by simp)] using hl.2.2
  let core := fusedRetainedThresholdCore load R A C retained cin h
  obtain ⟨st,hst⟩ : ∃ st : State,run core record s=st := ⟨_,rfl⟩
  have hf := fusedRetainedThresholdCore_correct load [b,q,t,d] R A C retained cin h F ncore disctl
    hRA hCA hc (fusedThresholdWordLoad_counts b q t d C K P).2 s record hload hC0 hk0 hi
  rw [hst] at hf
  have bh : b≠h := by
    have hnCount := List.nodup_iff_count.mp hn h
    intro he; subst b
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hnCount
    omega
  rw [fusedRetainedThresholdRecover,run_append,run_take,hst]
  change st.phase=s.phase ∧
    (∀ w,w≠h → (writeBit st.basis h (st.basis h^^st.basis b)) w=s.basis w) ∧
    (writeBit st.basis h (st.basis h^^st.basis b)) h=_
  refine ⟨hf.1,?_,?_⟩
  · intro w hw
    simpa only [writeBit,Function.update_of_ne hw] using hf.2.1 w hw
  · simp only [writeBit,Function.update_self,hf.2.2,hf.2.1 b bh,F]

/-- Exact replacement equality for independent old/new measurement lists.
The spare full comparison carry bit remains untouched by the retained stream. -/
theorem fusedRetainedThresholdRecover_eq_reference (b q t d h : Wire) (R A C retained carry : List Wire)
    (cin : Wire) (K P : Nat) (hn : ([b,q,t,d,h,cin]++R++A++C++carry).Nodup)
    (hsub : retained.Sublist carry) (hRA : R.length=A.length) (hCA : C.length=A.length)
    (hr : retained.length+1=A.length) (hc : carry.length=A.length)
    (hK : K<2^C.length) (hP : P<2^C.length) (h1 : 1<2^C.length)
    (s : State) (oldRecord newRecord : List Bool) (hC0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false) :
    run (fusedRetainedThresholdRecover b q t d h R A C retained cin K P) newRecord s=
      run (fusedThresholdRecover b q t d h R A C retained carry cin K P) oldRecord s := by
  have hnnew : ([b,q,t,d,h,cin]++R++A++C++retained).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hcount := List.nodup_iff_count.mp hn w
    have hsmall := hsub.count_le w
    simp only [List.count_cons,List.count_append,List.count_nil] at hcount ⊢
    omega
  have hknew : regValue retained s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => (regValue_zero _ _).mp hk0 w (hsub.subset hw))
  have hold := fusedThresholdRecover_shared_correct b q t d h R A C retained carry cin K P hn hsub
    hRA hCA hr hc hK hP h1 s oldRecord hC0 hknew hk0 hi
  have hnew := fusedRetainedThresholdRecover_correct b q t d h R A C retained cin K P hnnew
    hRA hCA hr hK hP h1 s newRecord hC0 hknew hi
  apply congrArg₂ State.mk
  · exact hnew.1.trans hold.1.symm
  · funext w
    by_cases hw : w=h
    · subst w; exact hnew.2.2.trans hold.2.2.symm
    · exact (hnew.2.1 w hw).trans (hold.2.1 w hw).symm

/-- Complete paid cleanup after flag transfer into target guards. All word
views here have n bits; the guard flags and constant selectors are outside them. -/
def fusedSignedHalfRetainedBack (b cin q h t d e : Wire) (sourceHalf R A C carry : List Wire) : Program :=
  let ac := carry.take (R.length-1)
  fusedThresholdFlagsSeed b q e t d ++ fusedThresholdPrepare b sourceHalf A ++
    fusedRetainedThresholdRecover b q t d h R A C ac cin (FusedSignedHalf.halfThreshold p) (p+1) ++
    fusedThresholdUnprepare b sourceHalf A ++ fusedThresholdFlagsErase b q e t d ++
    fusedHalfParityClear R C carry cin q


/-- Record-aligned replacement of a whole block. No measurement gate is
reversed: the old block may receive an arbitrary padded record, and the common
suffix receives exactly the new block's remaining independent record list. -/
theorem replace_zero_measurement_prefix (beforeProg oldK newK suffix : Program) (s : State)
    (record : List Bool) (hp : measurementCount beforeProg=0)
    (hk : ∀ oldR newR : List Bool,run newK newR (run beforeProg [] s)=run oldK oldR (run beforeProg [] s)) :
    run (beforeProg++newK++suffix) record s=
      run (beforeProg++oldK++suffix)
        (List.replicate (measurementCount oldK) false ++ record.drop (measurementCount newK)) s := by
  have hprefix (m : List Bool) : run beforeProg m s=run beforeProg [] s := by
    have hh := run_take beforeProg m s
    rw [hp,List.take_zero] at hh
    exact hh.symm
  simp only [List.append_assoc,run_append,run_take,hp,List.drop_zero,hprefix]
  rw [hk (List.replicate (measurementCount oldK) false ++ record.drop (measurementCount newK)) record]
  simp only [List.drop_append,List.length_replicate,List.drop_replicate,Nat.sub_self,List.replicate_zero,List.nil_append,List.drop_zero]

theorem fusedSignedHalfRetainedBack_correct (b cin q h t d e : Wire) (sourceHalf R A C carry : List Wire)
    (X Y : Nat) (hn : ([b,q,h,t,d,e,cin]++sourceHalf++R++A++C++carry).Nodup)
    (hs : sourceHalf.length=R.length) (hA : A.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length) (hw : 3≤R.length)
    (hwidth : p+1<2^R.length) (hX : X<p) (hY : Y<p)
    (s : State) (record : List Bool) (hsV : regValue sourceHalf s.basis=Y/2)
    (heV : s.basis e=FusedSignedHalf.parity (Y:Int))
    (hr : regValue R s.basis=FusedSignedHalf.result p (s.basis b) X Y)
    (ha0 : regValue A s.basis=0) (hc0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (ht0 : s.basis t=false) (hd0 : s.basis d=false)
    (hq : s.basis q=FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (s.basis b) X Y))
    (hh : s.basis h=FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (s.basis b) X Y)) :
    (run (fusedSignedHalfRetainedBack b cin q h t d e sourceHalf R A C carry) record s).phase=s.phase ∧
    (∀ w,w≠q → w≠h → (run (fusedSignedHalfRetainedBack b cin q h t d e sourceHalf R A C carry) record s).basis w=s.basis w) ∧
    (run (fusedSignedHalfRetainedBack b cin q h t d e sourceHalf R A C carry) record s).basis q=false ∧
    (run (fusedSignedHalfRetainedBack b cin q h t d e sourceHalf R A C carry) record s).basis h=false := by
  have bits : [b,q,h,t,d,e,cin].Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hcount := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hcount ⊢
    omega
  have dif := bits
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at dif
  have ns : [b,q,e,t,d].Nodup := by simp; tauto
  have np : (b::(sourceHalf++A)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hcount := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hcount ⊢
    omega
  have nk : ([b,q,t,d,h,cin]++R++A++C++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hcount := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hcount ⊢
    omega
  have safe (w : Wire) (hmem : w∈cin::(C++carry)) : w∉A ∧ w≠t ∧ w≠d := by
    have hcount := List.nodup_iff_count.mp hn w
    have hm' := List.count_pos_iff.mpr hmem
    simp only [List.count_cons,List.count_append,List.count_nil] at hcount hm'
    refine ⟨?_,?_,?_⟩
    · intro ha; have hh' := List.count_pos_iff.mpr ha; omega
    · intro he; subst w
      simp only [beq_self_eq_true,if_true] at hcount hm'
      omega
    · intro he; subst w
      simp only [beq_self_eq_true,if_true] at hcount hm'
      omega
  have atd (w : Wire) (hw' : w∈A) : w≠t ∧ w≠d := by
    constructor
    · intro he; subst w
      have hcount := List.nodup_iff_count.mp hn t
      have hm' := List.count_pos_iff.mpr hw'
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hcount
      omega
    · intro he; subst w
      have hcount := List.nodup_iff_count.mp hn d
      have hm' := List.count_pos_iff.mpr hw'
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hcount
      omega
  let beforeProg := fusedThresholdFlagsSeed b q e t d ++ fusedThresholdPrepare b sourceHalf A
  let suffix := fusedThresholdUnprepare b sourceHalf A ++ fusedThresholdFlagsErase b q e t d ++
    fusedHalfParityClear R C carry cin q
  let ac := carry.take (R.length-1)
  let oldK := fusedThresholdRecover b q t d h R A C ac carry cin (FusedSignedHalf.halfThreshold p) (p+1)
  let newK := fusedRetainedThresholdRecover b q t d h R A C ac cin (FusedSignedHalf.halfThreshold p) (p+1)
  have hsub : ac.Sublist carry := List.take_sublist _ _
  have hac : ac.length+1=A.length := by simp [ac,hk,hA]; omega
  have prepCounts := fusedThresholdPreparation_counts b sourceHalf A (hs.trans hA.symm)
  have flagCounts := fusedThresholdFlags_counts b q e t d
  have hp0 : measurementCount beforeProg=0 := by
    simp only [beforeProg,measurementCount_append,flagCounts.2.1,prepCounts.2.1,Nat.add_zero]
  obtain ⟨st1,hst1⟩ : ∃ st1 : State,run (fusedThresholdFlagsSeed b q e t d) [] s=st1 := ⟨_,rfl⟩
  have f1 := fusedThresholdFlagsSeed_correct b q e t d ns s [] ht0 hd0
  rw [hst1] at f1
  have a1 : regValue A st1.basis=0 := (regValue_congr _ _ _ (fun w hw' =>
    f1.2.1 w (atd w hw').1 (atd w hw').2)).trans ha0
  obtain ⟨st2,hst2⟩ : ∃ st2 : State,run (fusedThresholdPrepare b sourceHalf A) [] st1=st2 := ⟨_,rfl⟩
  have f2 := fusedThresholdPrepare_correct b sourceHalf A np (hs.trans hA.symm) st1 [] a1
  rw [hst2] at f2
  have hpRun : run beforeProg [] s=st2 := by
    dsimp only [beforeProg]
    rw [run_append,run_take]
    simp only [List.drop_nil]
    rw [hst1,hst2]
  have fixed (w : Wire) (hw' : w∈cin::(C++carry)) : st2.basis w=s.basis w :=
    (f2.2.1 w (safe w hw').1).trans (f1.2.1 w (safe w hw').2.1 (safe w hw').2.2)
  have c2 : regValue C st2.basis=0 := (regValue_congr _ _ _ (fun w hw' => fixed w (by simp [hw']))).trans hc0
  have k2 : regValue carry st2.basis=0 := (regValue_congr _ _ _ (fun w hw' => fixed w (by simp [hw']))).trans hk0
  have i2 : st2.basis cin=false := (fixed cin (by simp)).trans hi
  have smallK : FusedSignedHalf.halfThreshold p<2^C.length := by
    rw [hC]
    unfold FusedSignedHalf.halfThreshold
    omega
  have smallP : p+1<2^C.length := by simpa only [hC] using hwidth
  have smallOne : 1<2^C.length := by rw [hC]; omega
  have hkeq (oldR newR : List Bool) : run newK newR (run beforeProg [] s)=run oldK oldR (run beforeProg [] s) := by
    rw [hpRun]
    exact fusedRetainedThresholdRecover_eq_reference b q t d h R A C ac carry cin
      (FusedSignedHalf.halfThreshold p) (p+1) nk hsub hA.symm (hC.trans hA.symm) hac
      (hk.trans hA.symm) smallK smallP smallOne st2 oldR newR c2 k2 i2
  let oldR := List.replicate (measurementCount oldK) false ++ record.drop (measurementCount newK)
  have hruns : run (beforeProg++newK++suffix) record s=run (beforeProg++oldK++suffix) oldR s :=
    replace_zero_measurement_prefix beforeProg oldK newK suffix s record hp0 hkeq
  have eqNew : fusedSignedHalfRetainedBack b cin q h t d e sourceHalf R A C carry=beforeProg++newK++suffix := by
    simp only [fusedSignedHalfRetainedBack,beforeProg,newK,suffix,ac,List.append_assoc]
  have eqOld : fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry=beforeProg++oldK++suffix := by
    simp only [fusedSignedHalfBack,beforeProg,oldK,suffix,ac,List.append_assoc]
  rw [←eqNew,←eqOld] at hruns
  obtain ⟨out,hout⟩ : ∃ out : State,run (fusedSignedHalfBack b cin q h t d e sourceHalf R A C carry) oldR s=out := ⟨_,rfl⟩
  have href := fusedSignedHalfBack_correct b cin q h t d e sourceHalf R A C carry X Y hn hs hA hC hk hw
    hwidth hX hY s oldR hsV heV hr ha0 hc0 hk0 hi ht0 hd0 hq hh
  rw [hout] at href
  rw [hruns,hout]
  exact href

/-- Cleanup costs include the exact old-reduction and normalized-parity comparators. -/
theorem fusedSignedHalfRetainedBack_counts (b cin q h t d e : Wire) (sourceHalf R A C carry : List Wire)
    (hs : sourceHalf.length=R.length) (hA : A.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length) (hw : 3≤R.length) :
    toffoliCount (fusedSignedHalfRetainedBack b cin q h t d e sourceHalf R A C carry)=3*R.length-2 ∧
    measurementCount (fusedSignedHalfRetainedBack b cin q h t d e sourceHalf R A C carry)=3*R.length-2 := by
  let ac := carry.take (R.length-1)
  have hac : ac.length+1=A.length := by simp [ac,hk,hA]; omega
  have hf := fusedThresholdFlags_counts b q e t d
  have hp := fusedThresholdPreparation_counts b sourceHalf A (hs.trans hA.symm)
  have hr := fusedRetainedThresholdRecover_counts b q t d h R A C ac cin (FusedSignedHalf.halfThreshold p) (p+1)
    hA.symm (hC.trans hA.symm) hac
  have hq := fusedHalfParityClear_counts R C carry cin q hC hk
  dsimp only [ac] at hr
  constructor
  · simp only [fusedSignedHalfRetainedBack,toffoliCount_append,hf.1,hf.2.2.1,hp.1,hp.2.2.1,hr.1,hq.1,Nat.add_zero,hA]
    omega
  · simp only [fusedSignedHalfRetainedBack,measurementCount_append,hf.2.1,hf.2.2.2,hp.2.1,hp.2.2.2,hr.2,hq.2,Nat.add_zero,Nat.zero_add,hA]
    omega



namespace FusedHalfPorts

/-- Alternative packed stream; the accepted reference program remains intact. -/
def retainedProgram (L : FusedHalfPorts) : Program :=
  fusedSignedHalfFront L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m L.source L.target L.constant L.carry p ++
    fusedFlagsMove L.a L.h L.qOut L.hOut ++
    fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow L.A L.C
      (L.carry.take L.A.length)

theorem retained_counts (L : FusedHalfPorts) (hw : L.Widths) :
    toffoliCount L.retainedProgram=6*L.A.length+4 ∧
    measurementCount L.retainedProgram=6*L.A.length+5 := by
  have hl := L.widths hw
  have hf := fusedSignedHalfFront_counts L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m
    L.source L.target L.constant L.carry p (hl.1.trans hl.2.1.symm)
    (hl.2.2.1.trans hl.2.1.symm) (hw.carry.trans hl.2.1.symm) (by omega)
  have hm := fusedFlagsMove_counts L.a L.h L.qOut L.hOut
  have hb := fusedSignedHalfRetainedBack_counts L.b L.cin L.qOut L.hOut L.t L.d L.e
    L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)
    (hl.2.2.2.1.trans hl.2.2.2.2.symm) hl.2.2.2.2.symm
    (hw.constant.trans hl.2.2.2.2.symm) (by simp [hw.carry,hl.2.2.2.2])
    (by rw [hl.2.2.2.2]; exact hw.min)
  simp only [retainedProgram,toffoliCount_append,measurementCount_append,hf.1,hf.2,hm.1,hm.2,hb.1,hb.2,
    hl.2.1,hl.2.2.2.2,Nat.add_zero]
  have hn := hw.min
  constructor <;> omega

set_option maxHeartbeats 1000000 in
/-- Complete packed signed-half endpoint. Early flags are borrowed from A;
late flags occupy target and constant guards. Every non-target wire, phase and
complete scratch word restore for every independent measurement record. -/
theorem retained_correct (L : FusedHalfPorts) (hw : L.Widths) (hn : L.wires.Nodup)
    (he : L.early.Sublist L.A) (hwidth : p+1<2^L.A.length)
    (X Y : Nat) (hX : X<p) (hY : Y<p) (s : State) (record : List Bool)
    (hy : regValue L.source s.basis=Y) (hx : regValue L.target s.basis=X)
    (hC0 : regValue L.constant s.basis=0) (hk0 : regValue L.carry s.basis=0)
    (ha0 : regValue L.A s.basis=0) (hi : s.basis L.cin=false) :
    (run L.retainedProgram record s).phase=s.phase ∧
    (∀ w,w∉L.target → (run L.retainedProgram record s).basis w=s.basis w) ∧
    regValue L.target (run L.retainedProgram record s).basis=FusedSignedHalf.result p (s.basis L.b) X Y := by
  have hl := L.widths hw
  have hc (w : Wire) := List.nodup_iff_count.mp hn w
  have earlyA (w : Wire) (hm : w∈L.early) : w∈L.A := he.subset hm
  have aa : L.a∈L.A := earlyA L.a (by simp [early])
  have ah : L.h∈L.A := earlyA L.h (by simp [early])
  have aj : L.j∈L.A := earlyA L.j (by simp [early])
  have al : L.l∈L.A := earlyA L.l (by simp [early])
  have am : L.m∈L.A := earlyA L.m (by simp [early])
  have awayR (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.constant++L.carry++L.A) : w∉L.target := by
    intro hr
    have h1 := hc w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    simp only [wires,List.count_cons,List.count_append,List.count_nil] at h1 h2
    omega
  have awayA (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.target++L.constant++L.carry) : w∉L.A := by
    intro hr
    have h1 := hc w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    simp only [wires,List.count_cons,List.count_append,List.count_nil] at h1 h2
    omega
  have safe (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.constant++L.carry) : w∉L.target ∧ w≠L.a ∧ w≠L.h := by
    refine ⟨awayR w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm ⊢; tauto),?_,?_⟩
    · intro hh; subst w; exact awayA L.a (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm ⊢; tauto) aa
    · intro hh; subst w; exact awayA L.h (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hm ⊢; tauto) ah
  have qr : L.qOut∈L.target := by simp [target]
  have hr : L.hOut∈L.target := by simp [target]
  have nr : L.target.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h1 := hc w
    simp only [wires,List.count_cons,List.count_append] at h1
    omega
  have lowAway (w : Wire) (hm : w∈L.targetLow) : w≠L.qOut ∧ w≠L.hOut := by
    have hd := (List.nodup_append'.mp nr).2.2
    have hnot := List.disjoint_left.mp hd hm
    simpa only [List.mem_cons,List.mem_nil_iff,not_or,not_false_eq_true,and_true] using hnot
  have moveND := L.move_nodup hn he
  have md := moveND
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at md
  have hp : p%2=1 := by norm_num [ECDSAAdd.p]
  have hwR : 0<L.target.length := by omega
  have hfit : 2*p<2^(L.target.length-1) := by
    rw [hl.2.1,show L.A.length+2-1=L.A.length+1 by omega,pow_succ]
    omega
  let front := fusedSignedHalfFront L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m L.source L.target L.constant L.carry p
  obtain ⟨st1,hst1⟩ : ∃ st1 : State, run front record s=st1 := ⟨_,rfl⟩
  have f1 := fusedSignedHalfFront_correct L.b L.cin L.low L.hOut L.a L.h L.j L.l L.m L.source L.target L.constant L.carry
    p X Y (L.front_nodup hn he) (hl.1.trans hl.2.1.symm) (hl.2.2.1.trans hl.2.1.symm)
    (hw.carry.trans hl.2.1.symm)
    (by refine ⟨L.rTail++[L.qOut,L.hOut],?_⟩; rfl)
    (by refine ⟨L.targetLow++[L.qOut],?_⟩; simp [target,List.append_assoc]) hwR hp hX hY hfit s record hy hx hC0 hk0 hi
    ((regValue_zero _ _).mp ha0 L.a aa) ((regValue_zero _ _).mp ha0 L.h ah)
    ((regValue_zero _ _).mp ha0 L.j aj) ((regValue_zero _ _).mp ha0 L.l al) ((regValue_zero _ _).mp ha0 L.m am)
  rw [hst1] at f1
  let Z := FusedSignedHalf.result p (s.basis L.b) X Y
  have hz : Z<2^L.targetLow.length := by
    have h := (FusedSignedHalf.result_spec p X Y (s.basis L.b) hp hX hY).1
    rw [hl.2.2.2.2]
    omega
  have guards := fusedCanonicalGuards L.targetLow L.qOut L.hOut st1.basis Z hz f1.2.2.1
  let r2 := record.drop (measurementCount front)
  obtain ⟨st2,hst2⟩ : ∃ st2 : State, run (fusedFlagsMove L.a L.h L.qOut L.hOut) r2 st1=st2 := ⟨_,rfl⟩
  have f2 := fusedFlagsMove_correct L.a L.h L.qOut L.hOut moveND st1 r2 guards.2.1 guards.2.2
  rw [hst2] at f2
  have lowR (w : Wire) (hm : w∈L.targetLow) : w∈L.target := by simp [target,hm]
  have movedR : regValue L.targetLow st2.basis=Z := (regValue_congr _ _ _ (fun w hm => f2.2.1 w
    (by intro hh; subst w; exact awayR L.a (by simp [aa]) (lowR _ hm))
    (by intro hh; subst w; exact awayR L.h (by simp [ah]) (lowR _ hm)) (lowAway w hm).1 (lowAway w hm).2)).trans guards.1
  have movedA : regValue L.A st2.basis=0 := (regValue_zero _ _).mpr (by
    intro w hm
    by_cases hwa : w=L.a
    · subst w; exact f2.2.2.1
    by_cases hwh : w=L.h
    · subst w; exact f2.2.2.2.1
    have hwq : w≠L.qOut := by intro hh; subst w; exact awayA L.qOut (by simp [qr]) hm
    have hwo : w≠L.hOut := by intro hh; subst w; exact awayA L.hOut (by simp [hr]) hm
    exact (f2.2.1 w hwa hwh hwq hwo).trans ((f1.2.1 w (awayR w (by simp [hm])) hwa hwh).trans
      ((regValue_zero _ _).mp ha0 w hm)))
  have fixed2 (w : Wire) (hm : w∈[L.b,L.cin]++L.source++L.constant++L.carry) : st2.basis w=s.basis w := by
    have hs := safe w hm
    have hwq : w≠L.qOut := by intro hh; subst w; exact hs.1 qr
    have hwo : w≠L.hOut := by intro hh; subst w; exact hs.1 hr
    exact (f2.2.1 w hs.2.1 hs.2.2 hwq hwo).trans (f1.2.1 w hs.1 hs.2.1 hs.2.2)
  have b2 : st2.basis L.b=s.basis L.b := fixed2 L.b (by simp)
  have source2 : regValue L.source st2.basis=Y := (regValue_congr _ _ _ (fun w hm => fixed2 w (by simp [hm]))).trans hy
  have srcSmall : Y<2^(L.e::L.yTail).length := by
    simp only [List.length_cons,hw.source]
    omega
  have half2 := fusedSourceHalfValue L.e L.yTail L.yg0 L.yg1 st2.basis Y srcSmall source2
  have srcGuards := fusedCanonicalGuards (L.e::L.yTail) L.yg0 L.yg1 st2.basis Y srcSmall source2
  have e2 : st2.basis L.e=FusedSignedHalf.parity (Y:Int) := by
    have hb := fusedWordLowBit L.e L.yTail st2.basis
    rw [srcGuards.1] at hb
    rw [hb]
    apply decide_eq_decide.mpr
    change Y%2=1 ↔ (Y:Int)%2=1
    omega
  have cc2 : regValue L.C st2.basis=0 := (regValue_zero _ _).mpr (by
    intro w hm
    have hmem : w∈L.constant := by simp [constant,hm]
    exact (fixed2 w (by simp [hmem])).trans ((regValue_zero _ _).mp hC0 w hmem))
  have k2 : regValue (L.carry.take L.A.length) st2.basis=0 := (regValue_zero _ _).mpr (by
    intro w hm
    have hmem := List.mem_of_mem_take hm
    exact (fixed2 w (by simp [hmem])).trans ((regValue_zero _ _).mp hk0 w hmem))
  have i2 : st2.basis L.cin=false := (fixed2 L.cin (by simp)).trans hi
  have t2 : st2.basis L.t=false := (fixed2 L.t (by simp [constant])).trans
    ((regValue_zero _ _).mp hC0 L.t (by simp [constant]))
  have d2 : st2.basis L.d=false := (fixed2 L.d (by simp [constant])).trans
    ((regValue_zero _ _).mp hC0 L.d (by simp [constant]))
  have q2 : st2.basis L.qOut=FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum (st2.basis L.b) X Y) := by
    rw [f2.2.2.2.2.1,f1.2.2.2.1,f1.2.2.2.2,b2]
    rfl
  have h2 : st2.basis L.hOut=FusedSignedHalf.reduction p (FusedSignedHalf.signedSum (st2.basis L.b) X Y) := by
    rw [f2.2.2.2.2.2,f1.2.2.2.2,b2]
  let back := fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow L.A L.C
    (L.carry.take L.A.length)
  obtain ⟨st3,hst3⟩ : ∃ st3 : State, run back r2 st2=st3 := ⟨_,rfl⟩
  have f3 := fusedSignedHalfRetainedBack_correct L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow L.A L.C
    (L.carry.take L.A.length) X Y (L.back_nodup hn) (hl.2.2.2.1.trans hl.2.2.2.2.symm)
    hl.2.2.2.2.symm (hw.constant.trans hl.2.2.2.2.symm)
    (by simp [hw.carry,hl.2.2.2.2]) (by rw [hl.2.2.2.2]; exact hw.min) (by simpa only [hl.2.2.2.2] using hwidth)
    hX hY st2 r2 half2 e2 (by simpa only [b2] using movedR) movedA cc2 k2 i2 t2 d2 q2 h2
  rw [hst3] at f3
  have target3 : regValue L.target st3.basis=Z := by
    have low3 : regValue L.targetLow st3.basis=Z := (regValue_congr _ _ _ (fun w hm =>
      f3.2.1 w (lowAway w hm).1 (lowAway w hm).2)).trans movedR
    rw [target,regValue_append]
    change regValue L.targetLow st3.basis+2^L.targetLow.length*
      ((if st3.basis L.qOut then 1 else 0)+2*(if st3.basis L.hOut then 1 else 0))=Z
    rw [f3.2.2.1,f3.2.2.2]
    simpa only [Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] using low3
  have hRun : run L.retainedProgram record s=st3 := by
    rw [retainedProgram,List.append_assoc,run_append,run_take,hst1,run_append,run_take]
    simp only [(fusedFlagsMove_counts L.a L.h L.qOut L.hOut).2,List.drop_zero]
    rw [hst2,hst3]
  rw [hRun]
  refine ⟨f3.1.trans (f2.1.trans f1.1),?_,target3⟩
  intro w hwR
  have hwq : w≠L.qOut := by intro hh; subst w; exact hwR qr
  have hwo : w≠L.hOut := by intro hh; subst w; exact hwR hr
  rw [f3.2.1 w hwq hwo]
  by_cases hmA : w∈L.A
  · exact ((regValue_zero _ _).mp movedA w hmA).trans (((regValue_zero _ _).mp ha0 w hmA).symm)
  have hwa : w≠L.a := by intro hh; subst w; exact hmA aa
  have hwh : w≠L.h := by intro hh; subst w; exact hmA ah
  exact (f2.2.1 w hwa hwh hwq hwo).trans (f1.2.1 w hwR hwa hwh)

end FusedHalfPorts

end ECDSAAdd.Arithmetic
