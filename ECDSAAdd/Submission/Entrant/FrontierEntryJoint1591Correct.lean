import ECDSAAdd.Submission.Entrant.FrontierEntryJoint1591Frames
import ECDSAAdd.Submission.Entrant.FrontierEntryJoint1591Support
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Kernel

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntryJoint1591
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical DirectSkywalk
open FrontierEntry1591Field (controls work host numerator field_canonical_outside
  controls_away_numerator field_special_at controls_away_control canonical_numerator_value)
attribute [local irreducible] run wires

theorem entry_run_eq (s : State) (m : List Bool)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis))
    (workIn : s.basis work=false) (workOut : (run entryHosted m s).basis work=false)
    (payload : ∀q∈controls,(run entryHosted m s).basis q=s.basis q) :
    run entry m s=run entryHosted m s :=
  ParityField1591.run_eq controls work host entryHosted s m (by decide)
    FrontierEntry1591Field.host_not_controls entryHosted_avoids_host parity workIn workOut payload

theorem entry_core_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (enabled : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin Z 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run entry m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin (2*(Z/(x:Fp))) 0 (run entry m s) := by
  have result := entryField_frame origin ctx ha x hx0 hx trace enabled Z s m input
  have outside := field_canonical_outside origin ctx ha Z _ s _ input result.2 result.1
  have g0 : s.basis (base 2409)=false := by
    have bit := field_special_at origin Z 0 s 2409 (by simp) input
    have fix : OB5.sig 511 (base 2409)=base 2409 := by decide +kernel
    exact (fix ▸ bit).trans ctx.hg0
  have s0 : s.basis (base 2410)=false := by
    have bit := field_special_at origin Z 0 s 2410 (by simp) input
    have fix : OB5.sig 511 (base 2410)=base 2410 := by decide +kernel
    exact (fix ▸ bit).trans ctx.hs0
  have gOff : base 2409∉numerator := OwnPlusHost.not_block 2409 2056 256 (by omega)
  have sOff : base 2410∉numerator := OwnPlusHost.not_block 2410 2056 256 (by omega)
  have hostedEq : run entryHosted m s=run entryField m s :=
    HostOB5.hosted_run entryField s m entryField_hosts_free.1 entryField_hosts_free.2
      g0 in511 s0 in1542 ((outside _ gOff).trans g0) ((outside _ sOff).trans s0)
  have allEq := entry_run_eq s m parity workIn
    (by rw [hostedEq];exact (outside work (OwnPlusHost.not_block 1797 2056 256 (by omega))).trans workIn)
    (by intro q hq;rw [hostedEq];exact outside q (controls_away_numerator q hq))
  rw [allEq,hostedEq]
  exact result

private theorem double_half_div (Y W : Fp) : 2*(Y/2/W)=Y/W := by
  have two : (2:Fp)≠0 := by decide
  rw [div_div,mul_comm (2:Fp) W,←div_div,mul_div_cancel₀ _ two]

private theorem restore_origin (origin : BasisState) :
    writeBit (writeBit origin (base 2400) true) (base 2400) (origin (base 2400))=origin := by
  funext q
  by_cases eq : q=base 2400
  · subst q;simp only [writeBit,Function.update_self]
  · simp only [writeBit,Function.update_of_ne eq]

private theorem canonical_unforce (P : Program) (off : base 2400∉wires P)
    (origin : BasisState) (s forced : State) (m : List Bool)
    (forceEq : forced=⟨s.phase,writeBit s.basis (base 2400) true⟩)
    (B : Fp) (control : s.basis (base 2400)=origin (base 2400))
    (result : (run P m forced).phase=forced.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame (writeBit origin (base 2400) true) B 0 (run P m forced)) :
    (run P m s).phase=s.phase ∧ NewFieldFrameOB5.EncodedCanonicalFrame origin B 0 (run P m s) := by
  subst forced
  have back := FrontierEntry1591.canonical_control_set (writeBit origin (base 2400) true) B 0
    (run P m ⟨s.phase,writeBit s.basis (base 2400) true⟩) (origin (base 2400)) result.2
  have undo := FrontierEntry1591.run_control_unset P off s m true
  refine ⟨(congrArg State.phase undo).trans result.1,?_⟩
  rw [undo]
  simpa only [restore_origin,control] using back

theorem entry_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run entry m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin (Y/(x:Fp)) 0 (run entry m s) := by
  let origin' := writeBit origin (base 2400) true
  let forced : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩
  have ctx' := FrontierEntry1591.context_control_set origin ctx true
  have ha' := FrontierEntry1591.source_zero_control_set origin true ha
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)) := by
    rw [FrontierEntry1591.trace_control_set]
    exact trace
  have input' := FrontierEntry1591.frame_control_set origin (Y/2) 0 s true input
  have parity' := FrontierEntry1591.parity_host_control_set controls host (by decide)
    controls_away_control s true parity
  have result := entry_core_frame origin' ctx' ha' x hx0 hx trace'
    (by simp only [origin',writeBit,Function.update_self]) (Y/2) forced m input'
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 511≠base 2400 from by decide)] using in511)
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 1542≠base 2400 from by decide)] using in1542)
    (by simpa only [forced,writeBit,Function.update_of_ne (show work≠base 2400 from by decide)] using workIn)
    parity'
  rw [double_half_div] at result
  have control : s.basis (base 2400)=origin (base 2400) := by
    have bit := field_special_at origin (Y/2) 0 s 2400 (by simp) input
    rwa [OneFlagSW.selSig_2400] at bit
  exact canonical_unforce entry entry_control_free origin s forced m rfl (Y/(x:Fp)) control result

theorem entry_result (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (virtual actual : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 virtual)
    (phase : actual.phase=virtual.phase)
    (same : ∀q,q∉numerator → actual.basis q=virtual.basis q)
    (half : regValue numerator actual.basis=centerWord (Y/2))
    (in511 : actual.basis (base 511)=true) (in1542 : actual.basis (base 1542)=false)
    (workIn : actual.basis work=false)
    (parity : actual.basis host=TraceParity5.parity (controls.map actual.basis)) :
    (run entry m actual).phase=actual.phase ∧
      regValue numerator (run entry m actual).basis=(Y/(x:Fp)).val ∧
      ∀q,q∉numerator → (run entry m actual).basis q=actual.basis q := by
  have fieldInput := FrontierEntry1591EntryFrame.canonical_to_field ctx.hn origin ctx.parity ctx.env.2.2
    Y virtual actual phase same half input
  have result := entry_frame origin ctx ha x hx0 hx trace Y actual m fieldInput in511 in1542 workIn parity
  exact ⟨result.1,canonical_numerator_value origin ctx _ _ result.2,
    field_canonical_outside origin ctx ha _ _ actual _ fieldInput result.2 result.1⟩


section Kernel
open FrontierEntry1591Callers FrontierEntry1591Kernel
attribute [local irreducible] firstPhase lastPhase rawEntryKernel entryKernel
  NewStackOB5.stackForwardT FrontierEntry1591Native.forward

private theorem trace_last (x : Nat) (hx0 : 0<x) (hx : x<p) (origin : BasisState)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    origin (base 511)=true := by
  have tr : (skywalkTapeControls origin (skywalkSharedTape base)).getD 511 (false,false)=
      (true,false) := by
    rw [trace]
    exact SkywalkTrace.trace512_last x hx0 hx _
  have e : (skywalkTapeControls origin (skywalkSharedTape base)).getD 511 (false,false)=
      (origin (base 511),origin (base (1028+511))) := by
    simp [skywalkTapeControls,skywalkSharedTape]
  rw [e] at tr
  exact (Prod.mk.inj tr).1

private theorem prepared511 (origin : BasisState) (Y : Fp) (s : State)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s)
    (last : origin (base 511)=true) : s.basis (base 511)=true := by
  have bit := FrontierEntry1591Field.canonical_special_at origin Y 0 s 511 (by simp) input
  have fix : OB5.sig 511 (base 511)=base 511 := by decide +kernel
  exact (fix ▸ bit).trans last

private theorem context (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (s origin : State) (facts : PreparationFacts x Y s origin)
    (legal : History5.RawLegal base 102 origin.basis)
    (hg : s.basis (base 2409)=false) (hs : s.basis (base 2410)=false) :
    FrontierReplay1591.Context origin.basis := by
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  exact ⟨hn,ho,hp,hf,(facts.controls _ (by simp)).trans hg,
    (facts.controls _ (by simp)).trans hs,facts.env,legal,facts.targetHigh⟩


private theorem field_numerator_inputs (virtual actual : State) (value : Nat)
    (same : ∀q,q∉wireBlock base 2056 256 → actual.basis q=virtual.basis q)
    (half : regValue (wireBlock base 2056 256) actual.basis=value) :
    (∀q,q∉FrontierEntry1591Field.numerator → actual.basis q=virtual.basis q) ∧
      regValue FrontierEntry1591Field.numerator actual.basis=value := by
  exact ⟨same,half⟩

private theorem field_work_inputs (actual : State)
    (work : actual.basis (base 1797)=false)
    (parity : actual.basis (base 1543)=TraceParity5.parity (payloadControls.map actual.basis)) :
    actual.basis FrontierEntry1591Field.work=false ∧
      actual.basis FrontierEntry1591Field.host=
        TraceParity5.parity (FrontierEntry1591Field.controls.map actual.basis) := by
  exact ⟨work,parity⟩

private theorem field_output_result (before after : State) (value : Nat)
    (result : after.phase=before.phase ∧
      regValue FrontierEntry1591Field.numerator after.basis=value ∧
      ∀q,q∉FrontierEntry1591Field.numerator → after.basis q=before.basis q) :
    after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q := by
  exact result

theorem entry_boundary (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (mp mf : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg : s.basis (base 2409)=false) (hs : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (half : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let before := run firstPhase mp t
    let after := run entry mf before
    after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=(Y/(x:Fp)).val ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q := by
  let mn := mp.take (measurementCount (FrontierEntry1591Native.forward base))
  let rest := mp.drop (measurementCount (FrontierEntry1591Native.forward base))
  let mi := rest.take (measurementCount NewStackOB5.stackForwardT)
  let mc := rest.drop (measurementCount NewStackOB5.stackForwardT)
  let a1 := run (FrontierEntry1591Native.forward base) mn t
  let a2 := run NewStackOB5.stackForwardT mi a1
  let a3 := run (skywalkArithmeticClear base) mc a2
  have paired := EntryFuse.pool_three (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT
    (skywalkArithmeticClear base) (FrontierEntry1591Native.native_pool base base_pool_nodup).1
    forward_pool EntryFuse.clear_pool5 s t mn mi mc phase.symm (fun q hq => (same q hq).symm)
    a1 a2 a3 rfl rfl rfl
  have paired' : (run firstPhase mp s).phase=(run firstPhase mp t).phase ∧
      (∀q,q∉wireBlock base 2056 256 → (run firstPhase mp s).basis q=(run firstPhase mp t).basis q) ∧
      (∀q,q∈wireBlock base 2056 256 → (run firstPhase mp t).basis q=t.basis q) := by
    simpa only [firstPhase,run_append] using paired
  obtain ⟨origin,facts,legal,frame⟩ := first_prepared hn hlo ho x Y hx0 hx s mp input
  have ctx := context hn ho hf x Y s origin facts legal hg hs
  have actualInput := paired_input x Y.val s t input same
  have bits := first_clean hn x _ hx0 hx t mp actualInput
  have high : (run firstPhase mp t).basis (base 1542)=false :=
    bits _ (by simp [FrontierEntry1591Native.workSites])
  have code : (run firstPhase mp t).basis (base 511)=true :=
    (paired'.2.1 _ (OwnPlusHost.not_block 511 2056 256 (by omega))).symm.trans
      (prepared511 origin.basis Y _ frame (trace_last x hx0 hx origin.basis facts.trace))
  have target : regValue (wireBlock base 2056 256) (run firstPhase mp t).basis=centerWord (Y/2) :=
    (regValue_congr _ _ _ paired'.2.2).trans half
  have parity := first_parity hn hlo x _ hx0 hx t mp actualInput
  have numeratorInputs := field_numerator_inputs (run firstPhase mp s) (run firstPhase mp t)
    (centerWord (Y/2)) (fun q hq => (paired'.2.1 q hq).symm) target
  have workInputs := field_work_inputs (run firstPhase mp t)
    (first_work_zero hn x _ t mp actualInput) parity
  exact field_output_result (run firstPhase mp t)
    (run entry mf (run firstPhase mp t)) (Y/(x:Fp)).val
    (entry_result origin.basis ctx facts.sourceZero x hx0 hx facts.trace Y
      (run firstPhase mp s) (run firstPhase mp t) mf frame paired'.1.symm
      numeratorInputs.1 numeratorInputs.2 code high workInputs.1 workInputs.2)


theorem raw_entry_correct : EntryCorrect rawEntryKernel := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actualInput := paired_input x Y.val s t input same
  have result := raw_result entry hn hlo x _ hx0 hx t m
    (Y/(x:Fp)).val actualInput
    (fun mp mf => entry_boundary hn hlo ho hf x Y hx0 hx s t mp mf input hg hs phase same half)
  simpa only [rawEntryKernel,skywalkArithmeticResult,if_true] using
    And.intro (result.1.trans phase) (And.intro result.2.1
      (fun q hq => (result.2.2 q hq).trans (same q hq)))


private theorem away_work_host (q : Wire) (hq : q∈FrontierEntry1591Native.workSites∪
    FrontierEntry1591Native.hostSites) : q∉wireBlock base 2056 256 := by
  simp only [FrontierEntry1591Native.workSites,FrontierEntry1591Native.hostSites,
    Finset.mem_union,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with (rfl|rfl|rfl)|(rfl|rfl|rfl) <;>
    exact OwnPlusHost.not_block _ 2056 256 (by omega)

private theorem field_work_free (F : Program)
    (free : ∀i∈logicalOmissions,base i∉wires F) :
    ∀q∈FrontierEntry1591Native.workSites,q∉wires F := by
  intro q hq
  simp only [FrontierEntry1591Native.workSites,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl <;> exact free _ (by simp [logicalOmissions])

private theorem hosted_alias_run_eq (First F Last Raw Hosted : Program)
    (rawShape : Raw=FrontierEntry1591Native.kernel First F Last)
    (hostedShape : Hosted=FrontierEntry1591Native.relocated First F Last)
    (s : State) (m : List Bool)
    (input : ∀q∈FrontierEntry1591Native.workSites∪FrontierEntry1591Native.hostSites,s.basis q=false)
    (first_free : ∀q∈FrontierEntry1591Native.hostSites,q∉wires First)
    (first_clean : ∀mi,∀q∈FrontierEntry1591Native.workSites,(run First mi s).basis q=false)
    (field_free : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (last_free : ∀q∈FrontierEntry1591Native.hostSites,q∉wires Last)
    (output : ∀q∈FrontierEntry1591Native.workSites∪FrontierEntry1591Native.hostSites,
      (run Raw m s).basis q=false) :
    run Hosted m s=run Raw m s := by
  have eq := FrontierEntry1591Native.hosted_kernel_run_eq First F Last s m input first_free
    (first_clean (m.take (measurementCount First))) field_free last_free
    (by simpa only [rawShape] using output)
  simpa only [hostedShape,rawShape] using eq

private theorem state_predicate_transport (P : State → Prop) (a b : State)
    (eq : a=b) (result : P b) : P a := by
  cases eq
  exact result

theorem entry_correct : EntryCorrect entryKernel := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have result := raw_entry_correct hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actualInput := paired_input x Y.val s t input same
  have output : ∀q∈FrontierEntry1591Native.workSites∪FrontierEntry1591Native.hostSites,
      (run rawEntryKernel m t).basis q=false := by
    intro q hq
    exact (result.2.2 q (away_work_host q hq)).trans
      (FrontierEntry1591Native.caller_clean_sites x Y.val s input q hq)
  have eq := hosted_alias_run_eq firstPhase entry lastPhase rawEntryKernel entryKernel
    (by unfold rawEntryKernel;rfl) (by unfold entryKernel;rfl)
    t m (FrontierEntry1591Native.caller_clean_sites_paired x Y.val s t input same)
    first_host_free (fun mi => first_clean hn x _ hx0 hx t mi actualInput)
    (field_work_free _ entry_free) last_host_free output
  exact state_predicate_transport
    (fun out => out.phase=s.phase ∧
      regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q)
    (run entryKernel m t) (run rawEntryKernel m t) eq result



end Kernel
end ECDSAAdd.Entrant.FrontierEntryJoint1591
