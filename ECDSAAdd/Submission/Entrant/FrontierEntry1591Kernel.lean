import ECDSAAdd.Submission.Entrant.FrontierEntry1591Phases
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Preparation
import ECDSAAdd.Submission.Entrant.FrontierEntry1591FieldCorrect
import ECDSAAdd.Submission.Entrant.FrontierEntry1591KernelResources

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
  FrontierEntry1591Callers
attribute [local irreducible] run wires firstPhase lastPhase rawEntry rawExit entryKernel exitKernel
  NewStackOB5.stackForwardT FrontierEntry1591Native.forward

theorem first_prepared (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis) :
    ∃origin : State,PreparationFacts x Y s origin ∧ History5.RawLegal base 102 origin.basis ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 (run firstPhase m s) := by
  let mn := m.take (measurementCount (FrontierEntry1591Native.forward base))
  let rest := m.drop (measurementCount (FrontierEntry1591Native.forward base))
  have prep := preparation_placed hn hlo ho x Y hx0 hx s mn
    (rest.take (measurementCount NewStackOB5.stackForwardT))
    (rest.drop (measurementCount NewStackOB5.stackForwardT)) input
  simpa only [firstPhase,run_append] using prep

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

private theorem pool_composed (N F C First : Program)
    (shape : First=N++(F++C))
    (hN : wires N⊆(skywalkPoolWires base).toFinset)
    (hF : wires F⊆(skywalkPoolWires base).toFinset)
    (hC : wires C⊆(skywalkPoolWires base).toFinset)
    (s t : State) (m : List Bool) (phase : s.phase=t.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → s.basis q=t.basis q) :
    (run First m s).phase=(run First m t).phase ∧
      (∀q,q∉wireBlock base 2056 256 → (run First m s).basis q=(run First m t).basis q) ∧
      (∀q,q∈wireBlock base 2056 256 → (run First m t).basis q=t.basis q) := by
  let mn := m.take (measurementCount N)
  let rest := m.drop (measurementCount N)
  let mi := rest.take (measurementCount F)
  let mc := rest.drop (measurementCount F)
  let a1 := run N mn t
  let a2 := run F mi a1
  let a3 := run C mc a2
  have paired := EntryFuse.pool_three N F C hN hF hC s t mn mi mc phase same
    a1 a2 a3 rfl rfl rfl
  simpa only [shape,run_append] using paired

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
    let after := run FrontierEntry1591Field.entry mf before
    after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=(Y/(x:Fp)).val ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q := by
  have paired' : (run firstPhase mp s).phase=(run firstPhase mp t).phase ∧
      (∀q,q∉wireBlock base 2056 256 → (run firstPhase mp s).basis q=(run firstPhase mp t).basis q) ∧
      (∀q,q∈wireBlock base 2056 256 → (run firstPhase mp t).basis q=t.basis q) :=
    pool_composed (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT
      (skywalkArithmeticClear base) firstPhase (by unfold firstPhase;rfl)
      (FrontierEntry1591Native.native_pool base base_pool_nodup).1
      forward_pool EntryFuse.clear_pool5 s t mp phase.symm (fun q hq => (same q hq).symm)
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
    (run FrontierEntry1591Field.entry mf (run firstPhase mp t)) (Y/(x:Fp)).val
    (FrontierEntry1591Field.entry_result origin.basis ctx facts.sourceZero x hx0 hx facts.trace Y
      (run firstPhase mp s) (run firstPhase mp t) mf frame paired'.1.symm
      numeratorInputs.1 numeratorInputs.2 code high workInputs.1 workInputs.2)

theorem exit_boundary (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (mp mf : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg : s.basis (base 2409)=false) (hs : s.basis (base 2410)=false) :
    let before := run firstPhase mp s
    let after := run FrontierEntry1591Field.exit mf before
    after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=centerWord (Y*(x:Fp)/2) ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q := by
  obtain ⟨origin,facts,legal,frame⟩ := first_prepared hn hlo ho x Y hx0 hx s mp input
  have ctx := context hn ho hf x Y s origin facts legal hg hs
  have bits := first_clean hn x Y.val hx0 hx s mp input
  have workInputs := field_work_inputs (run firstPhase mp s)
    (first_work_zero hn x Y.val s mp input) (first_parity hn hlo x Y.val hx0 hx s mp input)
  exact field_output_result (run firstPhase mp s)
    (run FrontierEntry1591Field.exit mf (run firstPhase mp s)) (centerWord (Y*(x:Fp)/2))
    (FrontierEntry1591Field.exit_result origin.basis ctx facts.sourceZero x hx0 hx facts.trace Y
      (run firstPhase mp s) mf frame
      (prepared511 origin.basis Y _ frame (trace_last x hx0 hx origin.basis facts.trace))
      (bits _ (by simp [FrontierEntry1591Native.workSites])) workInputs.1 workInputs.2)

theorem raw_entry_correct : EntryCorrect rawEntry := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actualInput := paired_input x Y.val s t input same
  have result := raw_result FrontierEntry1591Field.entry hn hlo x _ hx0 hx t m
    (Y/(x:Fp)).val actualInput
    (fun mp mf => entry_boundary hn hlo ho hf x Y hx0 hx s t mp mf input hg hs phase same half)
  simpa only [rawEntry,skywalkArithmeticResult,if_true] using
    And.intro (result.1.trans phase) (And.intro result.2.1
      (fun q hq => (result.2.2 q hq).trans (same q hq)))

theorem raw_exit_correct : ExitCorrect rawExit := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have result := raw_result FrontierEntry1591Field.exit hn hlo x Y.val hx0 hx s m
    (centerWord (Y*(x:Fp)/2)) input
    (fun mp mf => exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  simpa only [rawExit,skywalkArithmeticNumerator] using result

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
      (run rawEntry m t).basis q=false := by
    intro q hq
    exact (result.2.2 q (away_work_host q hq)).trans
      (FrontierEntry1591Native.caller_clean_sites x Y.val s input q hq)
  have eq := hosted_alias_run_eq firstPhase FrontierEntry1591Field.entry lastPhase rawEntry entryKernel
    (by unfold rawEntry;rfl) (by unfold entryKernel;rfl) t m (FrontierEntry1591Native.caller_clean_sites_paired x Y.val s t input same)
    first_host_free (fun mi => first_clean hn x _ hx0 hx t mi actualInput)
    (field_work_free _ FrontierEntry1591Field.entry_free) last_host_free output
  exact state_predicate_transport
    (fun out => out.phase=s.phase ∧
      regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q)
    (run entryKernel m t) (run rawEntry m t) eq result

theorem exit_correct : ExitCorrect exitKernel := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have result := raw_exit_correct hn hlo ho hf x Y hx0 hx s m input hg hs
  have output : ∀q∈FrontierEntry1591Native.workSites∪FrontierEntry1591Native.hostSites,
      (run rawExit m s).basis q=false := by
    intro q hq
    exact (result.2.2 q (away_work_host q hq)).trans
      (FrontierEntry1591Native.caller_clean_sites x Y.val s input q hq)
  have eq := hosted_alias_run_eq firstPhase FrontierEntry1591Field.exit lastPhase rawExit exitKernel
    (by unfold rawExit;rfl) (by unfold exitKernel;rfl) s m (FrontierEntry1591Native.caller_clean_sites x Y.val s input)
    first_host_free (fun mi => first_clean hn x Y.val hx0 hx s mi input)
    (field_work_free _ FrontierEntry1591Field.exit_free) last_host_free output
  exact state_predicate_transport
    (fun out => out.phase=s.phase ∧
      regValue (skywalkArithmeticNumerator base) out.basis=centerWord (Y*(x:Fp)/2) ∧
      ∀q,q∉skywalkArithmeticNumerator base → out.basis q=s.basis q)
    (run exitKernel m s) (run rawExit m s) eq result

end ECDSAAdd.Entrant.FrontierEntry1591Kernel
