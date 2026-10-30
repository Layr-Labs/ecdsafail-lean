import ECDSAAdd.Submission.Entrant.FrontierEntryReplay
import ECDSAAdd.Submission.Entrant.FrontierEntryKernelProgram
import ECDSAAdd.Submission.Entrant.FrontierEntryKernelResources

/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntryKernel
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS OneFlagSW.endPacketS

theorem replay_records_drop (m : List Bool) :
    (FrontierEntry.oldRecords m).drop (measurementCount (OneFlagSW.replayS true))=
      m.drop (measurementCount FrontierEntry.replay) := by
  let a:=measurementCount (OneFlagSW.firstPacketS true)
  let b:=measurementCount FrontierEntry.firstPacket
  let c:=measurementCount (OneFlagSW.groupsS true 1 101)+measurementCount (OneFlagSW.endPacketS true)
  have old : measurementCount (OneFlagSW.replayS true)=a+c := by
    simp only [OneFlagSW.replayS,(renameProgram_counts (OB5.sig 511) (OneFlagSW.logicalReplayS true)).2,OneFlagSW.logicalReplayS,if_true,
      measurementCount_append,a,c,Nat.add_assoc]
  have fresh : measurementCount FrontierEntry.replay=b+c := by
    simp only [FrontierEntry.replay,(renameProgram_counts (OB5.sig 511) FrontierEntry.logicalReplay).2,FrontierEntry.logicalReplay,
      measurementCount_append,b,c,Nat.add_assoc]
  have nil : (List.replicate a false).drop (a+c)=[] :=
    List.drop_eq_nil_iff.mpr (by simp only [List.length_replicate];omega)
  rw [old,fresh,FrontierEntry.oldRecords,List.drop_append,List.length_replicate,nil]
  simp only [Nat.add_sub_cancel_left,List.nil_append,List.drop_drop]

/-- The initial code is read from the actual trace, not from arbitrary legal tape bits. -/
private theorem first_nonzero_of_trace (origin : BasisState) (x : Nat) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    origin (base 0)=true ∨ origin (base 1028)=true := by
  have read : (skywalkTapeControls origin (skywalkSharedTape base)).getD 0 (false,false)=
      (origin (base 0),origin (base 1028)) := by
    simp [skywalkTapeControls,skywalkSharedTape]
  have head : (origin (base 0),origin (base 1028))=
      SkywalkTrace.code (SkywalkRails.encode false false (x:Int) (p:Int)) := by
    rw [←read,trace]
    rfl
  have nz:=FirstNonzero.initial_code_nonzero x p (by norm_num [p]) (by norm_num [p]) hx
  have equal:=congrArg (fun pair:Bool×Bool=>pair.1 || pair.2) head
  have on:(origin (base 0) || origin (base 1028))=true := equal.trans nz
  exact Bool.or_eq_true.mp on

private theorem field_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (first : FrontierEntry.FirstTrit origin) (Z : Fp) (s : State) (m : List Bool)
    (input : FieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    run field5S m s=run OneFlagEntryRaw.field5S (FrontierEntry.oldRecords m) s := by
  have eq:=FrontierEntry.replay_compare origin ctx hb first Z s m input
  simp only [field5S,OneFlagEntryRaw.field5S,run_append,run_take]
  rw [eq,replay_records_drop]

private theorem hosted_compare (P Q : Program) (s : State) (m n : List Bool)
    (pf : base 511∉wires P) (qf : base 511∉wires Q)
    (sg : s.basis (base 2409)=false) (hg : s.basis (base 511)=true)
    (se : s.basis (base 2410)=false) (he : s.basis (base 1542)=false)
    (eq : run P m s=run Q n s) :
    run ([.X (base 511)]++(renameProgram HostOB5.hostSwap P++[.X (base 511)])) m s=
      run ([.X (base 511)]++(renameProgram HostOB5.hostSwap Q++[.X (base 511)])) n s := by
  let X:Program := [.X (base 511)]
  let u:=run X [] s
  have dis (R : Program) (hr : base 511∉wires R) : Disjoint (wires X) (wires R) := by
    apply Finset.disjoint_left.mpr
    intro q hq used
    have e:q=base 511 := by simpa only [X,wires,Instr.wires,Finset.union_empty,Finset.mem_singleton] using hq
    exact hr (e ▸ used)
  have cp:=run_disjoint_commute X P (dis P pf) [] m s
  have cq:=run_disjoint_commute X Q (dis Q qf) [] n s
  have equal : run P m u=run Q n u := cp.symm.trans ((congrArg (run X []) eq).trans cq)
  have pull : pullState HostOB5.hostSwap u=u := by
    apply HostOB5.host_pull
    · simp [u,X,run,writeBit,Function.update,base,sg,hg]
    · simp [u,X,run,writeBit,Function.update,base,se,he]
  have rp:=ECDSAAdd.run_rename HostOB5.hostSwap HostOB5.hostSwap_injective P m u
  have rq:=ECDSAAdd.run_rename HostOB5.hostSwap HostOB5.hostSwap_injective Q n u
  rw [pull] at rp rq
  have ren : run (renameProgram HostOB5.hostSwap P) m u=run (renameProgram HostOB5.hostSwap Q) n u := by
    have e:=congrArg (pullState HostOB5.hostSwap) (rp.trans (equal.trans rq.symm))
    simpa only [pullState,HostOB5.hostSwap_invol] using e
  have records (r : List Bool) (t : State) : run X r t=run X [] t := rfl
  have zero : measurementCount X=0 := rfl
  simpa only [run_append,zero,List.take_zero,List.drop_zero,run_take,records] using
    congrArg (run X []) ren

/-- Exact field equality at the actual fused prefix boundary. -/
theorem field_state_compare
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) (v1 v2 v3 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run stackForwardT m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3) :
    run hostField5S m4 v3=run OneFlagEntryRaw.hostField5S (FrontierEntry.oldRecords m4) v3 ∧
      v3.basis (base 2400)=true := by
  let a1:=run (NativeFirstDirect.forward base) m1 s
  let a2:=run stackForwardT m2 a1
  let a3:=run (skywalkArithmeticClear base) m3 a2
  have paired:=EntryFuse.pool_three (NativeFirstDirect.forward base) stackForwardT
    (skywalkArithmeticClear base) EntryFuse.first_pool5 EntryFuse.forward_pool5 EntryFuse.clear_pool5
    s t m1 m2 m3 phase.symm (fun q hq=>(same q hq).symm) v1 v2 v3 h1 h2 h3
  change a3.phase=v3.phase ∧ (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
    (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q) at paired
  have target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2) :=
    (regValue_congr _ _ _ paired.2.2).trans value
  have first:=NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  change CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 a1.basis at first
  let t2:=run (compactForward5 base 1 511) m2 a1
  let t3:=run (skywalkArithmeticClear base) m3 t2
  obtain ⟨hp0,hpo,hpp,cop⟩:=OB5.prime_facts x hx0 hx
  have pool:=skywalkShared_integer_nodup base hn
  have firstW:=(W.compactSkywalkStage_one base _ a1.basis).mpr first
  have gap : p+2^32≤2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 a1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp gap hx cop a1 m2 m2 first
  have e2 : a2=pullState (OB5.sig 511) t2 := by
    change run stackForwardT m2 a1=_
    rw [stackForwardT_run hn hlo x hx0 hx a1 m2 firstW]
    have fwd:=StackOB5.forward_run x hx0 hx a1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,encEq,entry⟩:=Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin a1 t2 t3 rfl rfl rfl first
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg:origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs:origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have enabled:origin.basis (base 2400)=true := (facts.controls _ (by simp)).trans hb
  have canonical : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have logicalSame : ∀q,q∉wireBlock base 2056 256 →
      (pullState (OB5.sig 511) v3).basis q=(pullState (OB5.sig 511) a3).basis q := by
    intro q hq
    exact (paired.2.1 _ (EntryFuse.sig_num_away q hq)).symm
  have logicalValue : regValue (wireBlock base 2056 256) (pullState (OB5.sig 511) v3).basis=centerWord (Y/2) := by
    apply (regValue_congr _ _ _ ?_).trans target
    intro q hq
    change v3.basis (OB5.sig 511 q)=v3.basis q
    rw [EntryFuse.sig_num_fix q hq]
  have frame : FieldFrameOB5.EncodedFieldFrame origin.basis (Y/2) 0 v3 :=
    EntryFuse.encoded_retarget5 hn origin.basis facts.targetHigh facts.sourceHigh Y
      (pullState (OB5.sig 511) a3) (pullState (OB5.sig 511) v3) paired.1.symm logicalSame logicalValue canonical
  let ctx : OneFlagReplay.Context origin.basis :=
    ⟨hn,ho,hp,hf,hg,hs,facts.env,legal,facts.targetHigh⟩
  have firstTrit : FrontierEntry.FirstTrit origin.basis :=
    ⟨FrontierEntry.firstLegal_of_context origin.basis ctx,
      first_nonzero_of_trace origin.basis x hx facts.trace⟩
  have unhosted:=field_compare origin.basis ctx enabled firstTrit (Y/2) v3 m4 frame
  have selectors:=EntryFuse.encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero Y a3 canonical
  have hosts:=EntryFuse.encoded_host_bits5 x hx0 hx origin t3 a3 facts.trace encEq e3
  have outside (i : Nat) (hi : i<2056 ∨ 2312≤i) : base i∉wireBlock base 2056 256 :=
    OwnPlusHost.not_block i 2056 256 (by omega)
  have keep (i : Nat) (hi : i<2056 ∨ 2312≤i) : v3.basis (base i)=a3.basis (base i) :=
    (paired.2.1 _ (outside i hi)).symm
  have oldFree : base 511∉wires OneFlagEntryRaw.field5S := fun used=>
    OneFlagEntryRaw.field_free.1 (OneFlagEntryRaw.selField5.sub.wires_sub used)
  have compared:=hosted_compare field5S OneFlagEntryRaw.field5S v3 m4 (FrontierEntry.oldRecords m4)
    field5S_hosts_free.1 oldFree ((keep 2409 (by omega)).trans selectors.1)
    ((keep 511 (by omega)).trans hosts.1) ((keep 2410 (by omega)).trans selectors.2)
    ((keep 1542 (by omega)).trans hosts.2) unhosted
  have on:=FrontierEntry.encoded_enable origin.basis ctx enabled (Y/2) 0 (pullState (OB5.sig 511) v3) frame
  have sigb : OB5.sig 511 (base 2400)=base 2400 := by decide
  refine ⟨?_,?_⟩
  · simpa only [hostField5S,OneFlagEntryRaw.hostField5S] using compared
  · simpa only [pullState,sigb] using on

private theorem enabled_kernel_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase) (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s
      (run (Q5FusionPhase.kernel hostField5S) m t) := by
  let P : State→State→Prop := fun initial out=>initial.phase=s.phase →
    (∀q,q∉wireBlock base 2056 256 → initial.basis q=s.basis q) →
    regValue (wireBlock base 2056 256) initial.basis=centerWord (Y/2) →
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s out
  have all:=skywalkRunSeven (NativeFirstDirect.forward base) stackForwardT (skywalkArithmeticClear base)
    hostField5S (skywalkArithmeticClear base) stackReverseT (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 ph sm val
      have pair:=field_state_compare hn hlo ho hf x Y hx0 hx s initial m1 m2 m3 m4 hin hg0 hs0
        ph sm val hb v1 v2 v3 h1 h2 h3
      have selected:=(OneFlagEntryRaw.selHostField5.eq (FrontierEntry.oldRecords m4) v3 pair.2).1
      have old4 : run OneFlagEntryRaw.hostField5 (FrontierEntry.oldRecords m4) v3=v4 := by
        have e:=pair.1.symm.trans h4
        rw [selected] at e
        simpa only [OneFlagEntryRaw.hostField5,OneFlagEntryRaw.field5] using e
      exact OneFlagEntryRaw.kernel5_states hn hlo ho hf x Y hx0 hx s initial m1 m2 m3
        (FrontierEntry.oldRecords m4) m5 m6 m7 hin hg0 hs0 ph sm val
        v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 old4 h5 h6 h7) t m
  simpa only [Q5FusionPhase.kernel,firstPhase,lastPhase,List.append_assoc] using all phase same value

private theorem enabled_base_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase) (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run baseKernel m t) := by
  have old:=enabled_kernel_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value hb
  have eq:=Q5FusionPhase.state_eq_of_contract hn x Y hx0 hx s t m hostField5S true
    hin same hostField5S_1026_free old
  rw [baseKernel,eq]
  exact old

/-- Full fused-numerator contract, including the inactive control basis states. -/
theorem base_kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out:=run baseKernel m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let a := EntryFuse.forceControl5 s
  let b := EntryFuse.forceControl5 t
  have shared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have divAway : base 2400∉wireBlock base 770 256 := fun h =>
    shared (arith_block_subset_shared base 770 256 (by omega) h)
  have numAway : base 2400∉wireBlock base 2056 256 := fun h =>
    shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input : SkywalkArithmeticInput base x Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=x
      apply (regValue_congr _ _ _ ?_).trans hin.1
      intro q hq
      exact EntryFuse.forceControl5_keep s q (fun e => divAway (e ▸ hq))
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      apply (regValue_congr _ _ _ ?_).trans hin.2.1
      intro q hq
      exact EntryFuse.forceControl5_keep s q (fun e => numAway (e ▸ hq))
    · intro q hq hdx hdy
      rw [EntryFuse.forceControl5_keep s q (fun e => shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have hg : a.basis (base 2409)=false :=
    (EntryFuse.forceControl5_keep s _ (by simp [base])).trans hg0
  have hs : a.basis (base 2410)=false :=
    (EntryFuse.forceControl5_keep s _ (by simp [base])).trans hs0
  have ab : a.basis (base 2400)=true := EntryFuse.forceControl5_true s
  have phases : b.phase=a.phase := phase
  have paired (q : Wire) (hq : q∉wireBlock base 2056 256) : b.basis q=a.basis q := by
    by_cases e : q=base 2400
    · subst q; rw [EntryFuse.forceControl5_true,EntryFuse.forceControl5_true]
    · rw [EntryFuse.forceControl5_keep t q e,EntryFuse.forceControl5_keep s q e]
      exact same q hq
  have half : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    exact EntryFuse.forceControl5_keep t q (fun e => numAway (e ▸ hq))
  have strong:=enabled_base_correct hn hlo ho hf x Y hx0 hx a b m input hg hs phases paired half ab
  unfold DirectSkywalkArithmeticStrong at strong
  rw [ab] at strong
  simp only [directSkywalkResult,if_true] at strong
  have agree:=pool_run_agrees baseKernel (wires baseKernel) (Finset.Subset.refl _) m t b rfl
    (fun q hq=>(EntryFuse.forceControl5_keep t q (fun e=>baseKernel_control_free (e ▸ hq))).symm)
  have sameRun (q : Wire) (hq : q≠base 2400) :
      (run baseKernel m t).basis q=(run baseKernel m b).basis q := by
    by_cases used:q∈wires baseKernel
    · exact agree.2 q used
    · rw [run_preserves_outside _ m t q used,run_preserves_outside _ m b q used]
      exact (EntryFuse.forceControl5_keep t q hq).symm
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans strong.2.1
    intro q hq
    exact sameRun q (fun e=>numAway (e ▸ hq))
  · intro q hq
    by_cases e:q=base 2400
    · subst q
      exact (run_preserves_outside _ m t _ baseKernel_control_free).trans (same _ numAway)
    · exact (sameRun q e).trans ((strong.2.2 q hq).trans (EntryFuse.forceControl5_keep s q e))

end ECDSAAdd.Entrant.FrontierEntryKernel
