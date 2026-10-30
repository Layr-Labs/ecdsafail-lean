import ECDSAAdd.Submission.Entrant.OneFlag
import ECDSAAdd.Submission.Entrant.ParityReplay
set_option Elab.async false
set_option linter.unusedTactic false


-- Public component FrontierEntry1591FieldFrames.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591Field
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires

def entryPlain : Program :=
  FrontierReplay1591.replay true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)

def exitPlain : Program :=
  OwnQ5Endpoint.centerT ++ (HalfFieldOB5.copyN ++ FrontierReplay1591.replay false)

theorem entry_sel : SW.Sel (base 2400) 1020 entryField entryPlain := by
  have tail : base 2400∉wires (HalfFieldOB5.copyN++OwnQ5Endpoint.canonT) := by
    intro used
    apply OneFlagEntryRaw.selField5.away
    change base 2400∈wires (OneFlagSW.replayS true++(HalfFieldOB5.copyN++OwnQ5Endpoint.canonT))
    rw [wires_append]
    exact Finset.mem_union_right _ used
  exact ((FrontierSW1591.selReplay_sel true).append (SW.Sel.refl _ _ tail)).cast
    (by omega) rfl rfl

theorem exit_sel : SW.Sel (base 2400) 1020 exitField exitPlain := by
  have leftPart : base 2400∉wires (OwnQ5Endpoint.centerT++HalfFieldOB5.copyN) := by
    intro used
    apply OneFlagExitRaw.selField.away
    change base 2400∈wires (OwnQ5Endpoint.centerT++(HalfFieldOB5.copyN++OneFlagSW.replayS false))
    simp only [wires_append] at used ⊢
    rcases Finset.mem_union.mp used with h|h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
  have h := (SW.Sel.refl _ _ leftPart).append (FrontierSW1591.selReplay_sel false)
  simpa only [entryField,exitField,exitPlain,List.append_assoc,Nat.zero_add] using h

theorem entryPlain_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (A : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin A 0 s) :
    (run entryPlain m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin
        (2*(if origin (base 2400) then A/(x:Fp) else A)) 0 (run entryPlain m s) := by
  let Z := if origin (base 2400) then A/(x:Fp) else A
  have result := run_three_states (FrontierReplay1591.replay true) HalfFieldOB5.copyN OwnQ5Endpoint.canonT
    (fun a d => NewFieldFrameOB5.EncodedFieldFrame origin A 0 a →
      d.phase=a.phase ∧ NewFieldFrameOB5.EncodedCanonicalFrame origin (2*Z) 0 d) (by
      intro a b c d m1 m2 m3 h1 h2 h3 hin
      have first := FrontierReplay1591.forward_frame origin ctx x hx0 hx trace A a m1 hin
      rw [h1] at first
      have middle := NewHalfFieldOB5.copy_clear ctx.hn origin Z b m2 first.2
      rw [h2] at middle
      have last := NewOwnQ5Endpoint.canon_frame ctx.hn (ctx.hp _ (by simp)) origin
        ctx.env ctx.legal ctx.parity ha Z c m3 middle.2
      change (run OwnQ5Endpoint.canonT m3 c).phase=c.phase ∧
        NewFieldFrameOB5.EncodedCanonicalFrame origin (2*Z) 0 (run OwnQ5Endpoint.canonT m3 c) at last
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m
  exact result input

theorem exitPlain_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    (run exitPlain m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin
        (if origin (base 2400) then Y/2*(x:Fp) else Y/2) 0 (run exitPlain m s) := by
  let Z := if origin (base 2400) then Y/2*(x:Fp) else Y/2
  have result := run_three_states OwnQ5Endpoint.centerT HalfFieldOB5.copyN (FrontierReplay1591.replay false)
    (fun a d => NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 a →
      d.phase=a.phase ∧ NewFieldFrameOB5.EncodedFieldFrame origin Z 0 d) (by
      intro a b c d m1 m2 m3 h1 h2 h3 hin
      have first := NewOwnQ5Endpoint.center_frame ctx.hn (ctx.hp _ (by simp)) origin
        ctx.env ctx.legal ctx.parity ha Y a m1 hin
      change (run OwnQ5Endpoint.centerT m1 a).phase=a.phase ∧
        NewFieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 (run OwnQ5Endpoint.centerT m1 a) at first
      rw [h1] at first
      have middle := NewHalfFieldOB5.copy_fill ctx.hn origin (Y/2) b m2 first.2
      rw [h2] at middle
      have last := FrontierReplay1591.inverse_frame origin ctx x hx0 hx trace (Y/2) c m3 middle.2
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m
  exact result input

theorem entryField_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (A : Fp) (s : State) (m : List Bool)
    (sel : s.basis (base 2400)=true)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin A 0 s) :
    (run entryField m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin
        (2*(if origin (base 2400) then A/(x:Fp) else A)) 0 (run entryField m s) := by
  rw [(entry_sel.eq m s sel).1]
  exact entryPlain_frame origin ctx ha x hx0 hx trace A s m input

theorem exitField_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (sel : s.basis (base 2400)=true)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    (run exitField m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin
        (if origin (base 2400) then Y/2*(x:Fp) else Y/2) 0 (run exitField m s) := by
  rw [(exit_sel.eq m s sel).1]
  exact exitPlain_frame origin ctx ha x hx0 hx trace Y s m input

abbrev numerator : List Wire := wireBlock base 2056 256
abbrev source : List Wire := (balancedSharedPorts base (base 2409)).y

theorem numerator_encoder_away (q : Wire) (hq : q∈numerator) :
    q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have hist := NewHistory5.allEncode_history_support base 102 (by decide) used
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [List.mem_toFinset,List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at hist
  rcases hist with ⟨j,hj,eq⟩|⟨j,hj,eq⟩
  all_goals have same := base_injective eq; omega

theorem source_subset_a : source⊆(skywalkSharedField base).a := by
  intro q hq
  rw [source,balancedSharedPorts_y] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  change base i∈wireBlock base 770 257
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1];omega,rfl⟩

theorem raw_pair_outside (origin current : BasisState) (A : Nat)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (frame : PairFrame numerator source origin A 0 current) :
    ∀q,q∉numerator → current q=origin q := by
  intro q hq
  by_cases inSource : q∈source
  · exact ((regValue_zero source current).mp frame.2.1 q inSource).trans
      ((regValue_zero _ origin).mp ha q (source_subset_a inSource)).symm
  · exact frame.2.2 q hq inSource

theorem canonical_raw_pair (origin current : BasisState) (X : Fp)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (frame : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val (0:Fp).val current) : PairFrame numerator source origin X.val 0 current := by
  have splitZ : (skywalkSharedField base).z=numerator++[base 2312] := by
    rw [skywalkShared_field_z]
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using
      (wireBlock_append base 2056 256 1).symm
  have splitA : (skywalkSharedField base).a=source++[base 1026] := by
    rw [source,balancedSharedPorts_y]
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using
      (wireBlock_append base 770 256 1).symm
  have bound : X.val<2^numerator.length := by
    rw [wireBlock_length]
    letI : NeZero p := ⟨p_prime.ne_zero⟩
    exact (ZMod.val_lt X).trans (by norm_num [p])
  rw [splitZ,splitA,ZMod.val_zero] at frame
  exact balancedPair_narrow numerator source (base 2312) (base 1026) origin current X.val 0
    bound (by rw [source,balancedSharedPorts_y,wireBlock_length];norm_num) frame hr hy

theorem encoded_pair_outside (origin : BasisState) (ha : regValue (skywalkSharedField base).a origin=0)
    (A B : Nat) (a b s t : State)
    (pa : PairFrame numerator source origin A 0 a.basis)
    (pb : PairFrame numerator source origin B 0 b.basis)
    (phase : a.phase=b.phase)
    (ea : s=run (NewHistory5.allEncode base 102) [] a)
    (eb : t=run (NewHistory5.allEncode base 102) [] b) :
    ∀q,q∉numerator → t.basis q=s.basis q := by
  have rawEq (q : Wire) (hq : q∉numerator) : b.basis q=a.basis q :=
    (raw_pair_outside origin b.basis B ha pb q hq).trans
      (raw_pair_outside origin a.basis A ha pa q hq).symm
  have same := run_measured_locality (NewHistory5.allEncode base 102)
    (wires (NewHistory5.allEncode base 102)) (fun _ h => h) b a [] phase.symm (by
      intro q hq
      exact rawEq q (fun mem => numerator_encoder_away q mem hq))
  intro q hq
  rw [ea,eb]
  by_cases used : q∈wires (NewHistory5.allEncode base 102)
  · exact same.2 q used
  · rw [run_preserves_outside _ [] b q used,run_preserves_outside _ [] a q used]
    exact rawEq q hq

theorem sig_numerator (q : Wire) (hq : q∈numerator) : OB5.sig 511 q=q := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [OB5.sig_base 511 i (by decide),if_neg (by omega)]

theorem sig_outside_numerator (q : Wire) (hq : q∉numerator) : OB5.sig 511 q∉numerator := by
  intro mem
  have fix := sig_numerator (OB5.sig 511 q) mem
  have invol := OB5.sig_invol 511 (by decide) q
  have eq : OB5.sig 511 q=q := fix.symm.trans invol
  exact hq (eq ▸ mem)

theorem field_canonical_outside (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0) (A B : Fp) (s t : State)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin A 0 s)
    (output : NewFieldFrameOB5.EncodedCanonicalFrame origin B 0 t) (phase : t.phase=s.phase) :
    ∀q,q∉numerator → t.basis q=s.basis q := by
  obtain ⟨a,ap,af,ae⟩ := input
  obtain ⟨b,bp,bf,be⟩ := output
  rw [NewHalfField5.centerWord_zero] at af
  have bf' := canonical_raw_pair origin b.basis B ctx.parity ctx.env.2.2 bf
  have same := encoded_pair_outside origin ha _ _ a b
    (pullState (OB5.sig 511) s) (pullState (OB5.sig 511) t) af bf'
    (ap.trans (phase.symm.trans bp.symm)) ae be
  intro q hq
  simpa only [pullState,OB5.sig_invol 511 (by decide)] using
    same (OB5.sig 511 q) (sig_outside_numerator q hq)

theorem canonical_field_outside (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0) (A B : Fp) (s t : State)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin A 0 s)
    (output : NewFieldFrameOB5.EncodedFieldFrame origin B 0 t) (phase : t.phase=s.phase) :
    ∀q,q∉numerator → t.basis q=s.basis q := by
  obtain ⟨a,ap,af,ae⟩ := input
  obtain ⟨b,bp,bf,be⟩ := output
  rw [NewHalfField5.centerWord_zero] at bf
  have af' := canonical_raw_pair origin a.basis A ctx.parity ctx.env.2.2 af
  have same := encoded_pair_outside origin ha _ _ a b
    (pullState (OB5.sig 511) s) (pullState (OB5.sig 511) t) af' bf
    (ap.trans (phase.symm.trans bp.symm)) ae be
  intro q hq
  simpa only [pullState,OB5.sig_invol 511 (by decide)] using
    same (OB5.sig 511 q) (sig_outside_numerator q hq)

theorem encoder_special_away (q : Nat) (hq : q∈[511,1539,1797,2409,2410,2400]) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  rw [NewHistory5.allEncode_support_eq] at used
  obtain ⟨j,hj,mem⟩ := History5.allEncode_member base 102 (base q) used
  obtain ⟨r,eq⟩ := History5.history_gate_mem base (5*j) _ (Or.inl rfl) (base q) mem
  have index := base_injective eq
  have port := r.isLt
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  unfold History5.historyMap History5.historyId at index
  split_ifs at index <;> omega

theorem field_special_at (origin : BasisState) (X Y : Fp) (s : State)
    (q : Nat) (hq : q∈[511,1539,1797,2409,2410,2400])
    (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (OB5.sig 511 (base q))=origin (base q) := by
  obtain ⟨raw,_,frame,encoded⟩ := input
  have rawEq : raw.basis (base q)=origin (base q) := by
    apply frame.2.2
    · rw [balancedSharedPorts_r]
      exact OwnPlusHost.not_block q 2056 256 (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq;omega)
    · rw [balancedSharedPorts_y]
      exact OwnPlusHost.not_block q 770 256 (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq;omega)
  change (pullState (OB5.sig 511) s).basis (base q)=_
  rw [encoded]
  exact (run_preserves_outside _ [] raw _ (encoder_special_away q hq)).trans rawEq

theorem canonical_special_at (origin : BasisState) (X Y : Fp) (s : State)
    (q : Nat) (hq : q∈[511,1539,1797,2409,2410,2400])
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X Y s) :
    s.basis (OB5.sig 511 (base q))=origin (base q) := by
  obtain ⟨raw,_,frame,encoded⟩ := input
  have rawEq : raw.basis (base q)=origin (base q) := by
    apply frame.2.2
    · rw [skywalkShared_field_z]
      exact OwnPlusHost.not_block q 2056 257 (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq;omega)
    · exact OwnPlusHost.not_block q 770 257 (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq;omega)
  change (pullState (OB5.sig 511) s).basis (base q)=_
  rw [encoded]
  exact (run_preserves_outside _ [] raw _ (encoder_special_away q hq)).trans rawEq

theorem controls_away_numerator (q : Wire) (hq : q∈controls) : q∉numerator := by
  obtain ⟨i,hi,eq⟩ := controls_member q hq
  rw [←eq]
  apply sig_outside_numerator
  rw [(payload_index_bound i hi).1]
  have bound := (payload_index_bound i hi).2
  exact OwnPlusHost.not_block _ 2056 256 (by omega)

theorem controls_away_control : base 2400∉controls := by
  intro used
  obtain ⟨i,hi,eq⟩ := controls_member (base 2400) used
  have same := OB5.sig_injective 511 (by decide) (eq.trans OneFlagSW.selSig_2400.symm)
  rw [(payload_index_bound i hi).1] at same
  have index := base_injective same
  have bound := (payload_index_bound i hi).2
  omega

theorem entryField_support_eq : wires entryField=wires OneFlagEntryRaw.field5S := by
  simp only [entryField,OneFlagEntryRaw.field5S,wires_append,FrontierSW1591.support_eq]

theorem exitField_support_eq : wires exitField=wires OneFlagExitRaw.fieldMulS := by
  simp only [exitField,OneFlagExitRaw.fieldMulS,wires_append,FrontierSW1591.support_eq]

theorem entryField_host_free : base 511∉wires entryField ∧ base 1542∉wires entryField := by
  rw [entryField_support_eq]
  exact ⟨fun h => OneFlagEntryRaw.field_free.1 (OneFlagEntryRaw.selField5.sub.wires_sub h),
    fun h => OneFlagEntryRaw.field_free.2 (OneFlagEntryRaw.selField5.sub.wires_sub h)⟩

theorem exitField_host_free : base 511∉wires exitField ∧ base 1542∉wires exitField := by
  rw [exitField_support_eq]
  exact ⟨fun h => OB5Support.seg_host_free.1
      (OneFlagExitGeometry.field_support (OneFlagExitRaw.selField.sub.wires_sub h)),
    fun h => OB5Support.seg_host_free.2
      (OneFlagExitGeometry.field_support (OneFlagExitRaw.selField.sub.wires_sub h))⟩

theorem field_numerator_value (origin : BasisState) (A B : Fp) (s : State)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin A B s) :
    regValue numerator s.basis=centerWord A := by
  obtain ⟨raw,_,frame,encoded⟩ := input
  apply Eq.trans (regValue_congr _ _ _ ?_) frame.1
  intro q hq
  have fixed := sig_numerator q hq
  have same : (pullState (OB5.sig 511) s).basis q=raw.basis q := by
    rw [encoded]
    exact run_preserves_outside _ [] raw q (numerator_encoder_away q hq)
  simpa only [pullState,fixed] using same

theorem canonical_numerator_value (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (A : Fp) (s : State) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin A 0 s) :
    regValue numerator s.basis=A.val := by
  obtain ⟨raw,_,frame,encoded⟩ := input
  have pair := canonical_raw_pair origin raw.basis A ctx.parity ctx.env.2.2 frame
  apply Eq.trans (regValue_congr _ _ _ ?_) pair.1
  intro q hq
  have fixed := sig_numerator q hq
  have same : (pullState (OB5.sig 511) s).basis q=raw.basis q := by
    rw [encoded]
    exact run_preserves_outside _ [] raw q (numerator_encoder_away q hq)
  simpa only [pullState,fixed] using same

theorem hosted_control_away (P : Program) (hp : base 2400∉wires P) :
    base 2400∉wires (hosted P) := by
  have body := OneFlagReplay.rename_free HostOB5.hostSwap HostOB5.hostSwap_injective
    (base 2400) (base 2400) OneFlagSW.selHost_fix P hp
  simpa only [hosted,wires_append,Finset.mem_union,not_or] using
    ⟨OneFlagSW.selX511_away,body,OneFlagSW.selX511_away⟩

theorem parity_control_away (P : Program) (hp : base 2400∉wires P) :
    base 2400∉wires (ParityField1591.program controls work host P) := by
  have setup : base 2400∉wires (ParityHost5.setup controls host) := by
    intro used
    have mem := ParityHost5.setup_support controls host used
    rcases Finset.mem_insert.mp mem with eq|mem
    · exact (show base 2400≠host from by decide) eq
    · exact controls_away_control (List.mem_toFinset.mp mem)
  have body := OneFlagReplay.rename_free (Equiv.swap work host) (Equiv.swap work host).injective
    (base 2400) (base 2400) (by decide +kernel) P hp
  simpa only [ParityField1591.program,ParityHostTransport5.program,wires_append,
    Finset.mem_union,not_or] using ⟨⟨setup,body⟩,setup⟩

theorem entry_control_away : base 2400∉wires entry :=
  parity_control_away entryHosted (hosted_control_away entryField entry_sel.away)

theorem exit_control_away : base 2400∉wires exit :=
  parity_control_away exitHosted (hosted_control_away exitField exit_sel.away)

theorem entry_core_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (A : Fp) (s : State) (m : List Bool)
    (sel : s.basis (base 2400)=true)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin A 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run entry m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin
        (2*(if origin (base 2400) then A/(x:Fp) else A)) 0 (run entry m s) := by
  have result := entryField_frame origin ctx ha x hx0 hx trace A s m sel input
  have outside := field_canonical_outside origin ctx ha A _ s _ input result.2 result.1
  have g0 : s.basis (base 2409)=false := by
    have bit := field_special_at origin A 0 s 2409 (by simp) input
    have fix : OB5.sig 511 (base 2409)=base 2409 := by decide +kernel
    exact (fix ▸ bit).trans ctx.hg0
  have s0 : s.basis (base 2410)=false := by
    have bit := field_special_at origin A 0 s 2410 (by simp) input
    have fix : OB5.sig 511 (base 2410)=base 2410 := by decide +kernel
    exact (fix ▸ bit).trans ctx.hs0
  have gOff : base 2409∉numerator := OwnPlusHost.not_block 2409 2056 256 (by omega)
  have sOff : base 2410∉numerator := OwnPlusHost.not_block 2410 2056 256 (by omega)
  have hostedEq : run entryHosted m s=run entryField m s :=
    HostOB5.hosted_run entryField s m entryField_host_free.1 entryField_host_free.2
      g0 in511 s0 in1542 ((outside _ gOff).trans g0) ((outside _ sOff).trans s0)
  have allEq := entry_run_eq s m parity workIn
    (by rw [hostedEq];exact (outside work (OwnPlusHost.not_block 1797 2056 256 (by omega))).trans workIn)
    (by intro q hq;rw [hostedEq];exact outside q (controls_away_numerator q hq))
  rw [allEq,hostedEq]
  exact result

theorem exit_core_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (sel : s.basis (base 2400)=true)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run exit m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin
        (if origin (base 2400) then Y/2*(x:Fp) else Y/2) 0 (run exit m s) := by
  have result := exitField_frame origin ctx ha x hx0 hx trace Y s m sel input
  have outside := canonical_field_outside origin ctx ha Y _ s _ input result.2 result.1
  have g0 : s.basis (base 2409)=false := by
    have bit := canonical_special_at origin Y 0 s 2409 (by simp) input
    have fix : OB5.sig 511 (base 2409)=base 2409 := by decide +kernel
    exact (fix ▸ bit).trans ctx.hg0
  have s0 : s.basis (base 2410)=false := by
    have bit := canonical_special_at origin Y 0 s 2410 (by simp) input
    have fix : OB5.sig 511 (base 2410)=base 2410 := by decide +kernel
    exact (fix ▸ bit).trans ctx.hs0
  have gOff : base 2409∉numerator := OwnPlusHost.not_block 2409 2056 256 (by omega)
  have sOff : base 2410∉numerator := OwnPlusHost.not_block 2410 2056 256 (by omega)
  have hostedEq : run exitHosted m s=run exitField m s :=
    HostOB5.hosted_run exitField s m exitField_host_free.1 exitField_host_free.2
      g0 in511 s0 in1542 ((outside _ gOff).trans g0) ((outside _ sOff).trans s0)
  have allEq := exit_run_eq s m parity workIn
    (by rw [hostedEq];exact (outside work (OwnPlusHost.not_block 1797 2056 256 (by omega))).trans workIn)
    (by intro q hq;rw [hostedEq];exact outside q (controls_away_numerator q hq))
  rw [allEq,hostedEq]
  exact result

end ECDSAAdd.Entrant.FrontierEntry1591Field

end

-- Public component FrontierEntry1591EntryFrame.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591EntryFrame
open Arithmetic Secp256k1 MappedCompressed CompressedAllocation CompressedFieldSupport BalancedField
  NewHistory5 EntryFuse
attribute [local irreducible] run wires NewHistory5.allEncode

theorem encoded_retarget (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s t : State) (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (input : NewHistory5.EncodedCanonicalFrame5 origin Y 0 s) :
    NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Y/2) 0 t := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let R := (balancedSharedPorts base (base 2409)).r
  let W := (balancedSharedPorts base (base 2409)).y
  have rEq : R=wireBlock base 2056 256 := balancedSharedPorts_r base (base 2409)
  have wEq : W=wireBlock base 770 256 := balancedSharedPorts_y base (base 2409)
  have split : (skywalkSharedField base).z=R++[base 2312] ∧
      (skywalkSharedField base).a=W++[base 1026] := by
    rw [skywalkShared_field_z,rEq,wEq]
    constructor
    · have h := wireBlock_append base 2056 256 1
      simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using h.symm
    · have h := wireBlock_append base 770 256 1
      simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using h.symm
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  rw [split.1,split.2,ZMod.val_zero] at rawFrame
  have yBound : Y.val<2^256 := (ZMod.val_lt Y).trans (by norm_num [p])
  have narrow := balancedPair_narrow R W (base 2312) (base 1026) origin raw.basis Y.val 0
    (by rw [rEq,wireBlock_length]; exact yBound) (by rw [wEq,wireBlock_length]; norm_num)
    rawFrame hr hy
  have dis : R.Disjoint W :=
    (List.nodup_append'.mp (balancedSharedLayout_pairND base (base 2409) hn)).2.2
  let raw' : State := ⟨t.phase,fun q => if q∈R then t.basis q else raw.basis q⟩
  have keeps (q : Wire) (hq : q∉R) : raw'.basis q=raw.basis q := by simp [raw',hq]
  have target : regValue R raw'.basis=centerWord (Y/2) := by
    have h : regValue R raw'.basis=regValue R t.basis := by
      apply regValue_congr
      intro q hq
      simp [raw',hq]
    rw [h,rEq]
    exact value
  have pf : PairFrame R W origin (centerWord (Y/2)) (centerWord 0) raw'.basis := by
    rw [NewHalfField5.centerWord_zero]
    exact PairFrame.update_temp R W origin raw.basis raw'.basis Y.val 0 _ dis narrow keeps target
  have rawPhase' : raw'.phase=raw.phase := by
    change t.phase=raw.phase
    exact phase.trans rawPhase.symm
  have support := NewHalfField5.encoder_pool_support
  have away (q : Wire) (hq : q∈wires (NewHistory5.allEncode base 102)) : q∉R := by
    rw [rEq]
    exact pool_away q (List.mem_toFinset.mp (support hq))
  have reads : ∀q∈wires (NewHistory5.allEncode base 102),raw'.basis q=raw.basis q := by
    intro q hq
    exact keeps q (away q hq)
  have inc := run_local_increment (NewHistory5.allEncode base 102) raw' raw [] reads
  have eqphase : (run (NewHistory5.allEncode base 102) [] raw').phase =
      (run (NewHistory5.allEncode base 102) [] raw).phase := by
    rw [rawPhase'] at inc
    cases raw.phase <;> simpa using inc.1
  have encoded' : t=run (NewHistory5.allEncode base 102) [] raw' := by
    apply State.extensionality
    · rw [eqphase,←encoded]
      exact phase
    · funext q
      by_cases hq : q∈R
      · have unused : q∉wires (NewHistory5.allEncode base 102) := fun h => away q h hq
        rw [run_preserves_outside _ [] raw' q unused]
        simp [raw',hq]
      · have eq : (run (NewHistory5.allEncode base 102) [] raw').basis q=
            (run (NewHistory5.allEncode base 102) [] raw).basis q := by
          by_cases used : q∈wires (NewHistory5.allEncode base 102)
          · exact inc.2 q used
          · rw [run_preserves_outside _ [] raw' q used,run_preserves_outside _ [] raw q used]
            exact keeps q hq
        rw [eq,←encoded]
        apply same q
        simpa only [rEq] using hq
  exact ⟨raw',rfl,pf,encoded'⟩


theorem canonical_to_field (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s t : State) (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    NewFieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 t := by
  apply encoded_retarget hn origin hr hy Y (pullState (OB5.sig 511) s)
    (pullState (OB5.sig 511) t) phase
  · intro q hq
    exact same _ (EntryFuse.sig_num_away q hq)
  · apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    change t.basis (OB5.sig 511 q)=t.basis q
    rw [EntryFuse.sig_num_fix q hq]
  · exact input

end ECDSAAdd.Entrant.FrontierEntry1591EntryFrame

end

-- Public component FrontierEntry1591FieldCorrect.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591Field
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires

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

private theorem field_unforce (P : Program) (off : base 2400∉wires P)
    (origin : BasisState) (s forced : State) (m : List Bool)
    (forceEq : forced=⟨s.phase,writeBit s.basis (base 2400) true⟩)
    (B : Fp) (control : s.basis (base 2400)=origin (base 2400))
    (result : (run P m forced).phase=forced.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame (writeBit origin (base 2400) true) B 0 (run P m forced)) :
    (run P m s).phase=s.phase ∧ NewFieldFrameOB5.EncodedFieldFrame origin B 0 (run P m s) := by
  subst forced
  have back := FrontierEntry1591.frame_control_set (writeBit origin (base 2400) true) B 0
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
  have result := entry_core_frame origin' ctx' ha' x hx0 hx trace' (Y/2) forced m
    (by simp only [forced,writeBit,Function.update_self]) input'
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 511≠base 2400 from by decide)] using in511)
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 1542≠base 2400 from by decide)] using in1542)
    (by simpa only [forced,writeBit,Function.update_of_ne (show work≠base 2400 from by decide)] using workIn)
    parity'
  have value : 2*(if origin' (base 2400) then Y/2/(x:Fp) else Y/2)=Y/(x:Fp) := by
    simp only [origin',writeBit,Function.update_self,if_true]
    exact double_half_div Y (x:Fp)
  rw [value] at result
  have control : s.basis (base 2400)=origin (base 2400) := by
    have bit := field_special_at origin (Y/2) 0 s 2400 (by simp) input
    rwa [OneFlagSW.selSig_2400] at bit
  exact canonical_unforce entry entry_control_away origin s forced m rfl (Y/(x:Fp)) control result

theorem exit_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run exit m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin (Y*(x:Fp)/2) 0 (run exit m s) := by
  let origin' := writeBit origin (base 2400) true
  let forced : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩
  have ctx' := FrontierEntry1591.context_control_set origin ctx true
  have ha' := FrontierEntry1591.source_zero_control_set origin true ha
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)) := by
    rw [FrontierEntry1591.trace_control_set]
    exact trace
  have input' := FrontierEntry1591.canonical_control_set origin Y 0 s true input
  have parity' := FrontierEntry1591.parity_host_control_set controls host (by decide)
    controls_away_control s true parity
  have result := exit_core_frame origin' ctx' ha' x hx0 hx trace' Y forced m
    (by simp only [forced,writeBit,Function.update_self]) input'
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 511≠base 2400 from by decide)] using in511)
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 1542≠base 2400 from by decide)] using in1542)
    (by simpa only [forced,writeBit,Function.update_of_ne (show work≠base 2400 from by decide)] using workIn)
    parity'
  have value : (if origin' (base 2400) then Y/2*(x:Fp) else Y/2)=Y*(x:Fp)/2 := by
    simp only [origin',writeBit,Function.update_self,if_true,div_eq_mul_inv]
    ring
  rw [value] at result
  have control : s.basis (base 2400)=origin (base 2400) := by
    have bit := canonical_special_at origin Y 0 s 2400 (by simp) input
    rwa [OneFlagSW.selSig_2400] at bit
  exact field_unforce exit exit_control_away origin s forced m rfl (Y*(x:Fp)/2) control result

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

theorem exit_result (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run exit m s).phase=s.phase ∧
      regValue numerator (run exit m s).basis=centerWord (Y*(x:Fp)/2) ∧
      ∀q,q∉numerator → (run exit m s).basis q=s.basis q := by
  have result := exit_frame origin ctx ha x hx0 hx trace Y s m input in511 in1542 workIn parity
  exact ⟨result.1,field_numerator_value origin _ _ _ result.2,
    canonical_field_outside origin ctx ha _ _ s _ input result.2 result.1⟩

end ECDSAAdd.Entrant.FrontierEntry1591Field

end

-- Public component FrontierEntry1591KernelProgram.lean
section
namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk

def rawEntry : Program :=
  FrontierEntry1591Native.kernel firstPhase FrontierEntry1591Field.entry lastPhase

def rawExit : Program :=
  FrontierEntry1591Native.kernel firstPhase FrontierEntry1591Field.exit lastPhase

def entryKernel : Program :=
  FrontierEntry1591Native.relocated firstPhase FrontierEntry1591Field.entry lastPhase

def exitKernel : Program :=
  FrontierEntry1591Native.relocated firstPhase FrontierEntry1591Field.exit lastPhase

end ECDSAAdd.Entrant.FrontierEntry1591Kernel

end

-- Public component FrontierEntry1591FieldCounts.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.FrontierEntry1591Field
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  entryHosted exitHosted

theorem entry_counts : toffoliCount entry=toffoliCount entryHosted ∧
    measurementCount entry=measurementCount entryHosted ∧
    Challenge.gateSlots entry=Challenge.gateSlots entryHosted+1632 := by
  have result := ParityField1591.counts controls work host entryHosted
  have size : 2*controls.length=1632 := by rw [controls_length]
  exact ⟨result.1,result.2.1,result.2.2.trans
    (congrArg (fun n => Challenge.gateSlots entryHosted+n) size)⟩

theorem exit_counts : toffoliCount exit=toffoliCount exitHosted ∧
    measurementCount exit=measurementCount exitHosted ∧
    Challenge.gateSlots exit=Challenge.gateSlots exitHosted+1632 := by
  have result := ParityField1591.counts controls work host exitHosted
  have size : 2*controls.length=1632 := by rw [controls_length]
  exact ⟨result.1,result.2.1,result.2.2.trans
    (congrArg (fun n => Challenge.gateSlots exitHosted+n) size)⟩

end ECDSAAdd.Entrant.FrontierEntry1591Field

end

-- Public component ParityHistoryResources.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewHistory5
open Arithmetic Challenge Baselines

theorem decode_metrics (w : Nat → Wire) (start : Nat) :
    toffoliCount (decode w start)=toffoliCount (History5.decode w start) ∧
    measurementCount (decode w start)=measurementCount (History5.decode w start) ∧
    gateSlots (decode w start)=gateSlots (History5.decode w start)+2 := by
  have n := decode_counts w start
  have o := History5.decode_counts w start
  refine ⟨by omega,by omega,?_⟩
  change gateSlots (ParityCodec5New.decodeAt (History5.historyMap w start))=
    gateSlots (MeasuredCodec5.decodeAt (History5.historyMap w start))+2
  rw [(ParityCodec5New.slotsAt _).2,(MeasuredCodec5.slotsAt _).2]

theorem decodeBefore_metrics (w : Nat → Wire) (i : Nat) :
    toffoliCount (decodeBefore w i)=toffoliCount (History5.decodeBefore w i) ∧
    measurementCount (decodeBefore w i)=measurementCount (History5.decodeBefore w i) ∧
    gateSlots (decodeBefore w i)=gateSlots (History5.decodeBefore w i)+
      2*(if History5.packDue i then 1 else 0) := by
  change toffoliCount (if History5.packDue i then decode w (i-5) else [])=
      toffoliCount (if History5.packDue i then History5.decode w (i-5) else []) ∧
    measurementCount (if History5.packDue i then decode w (i-5) else [])=
      measurementCount (if History5.packDue i then History5.decode w (i-5) else []) ∧
    gateSlots (if History5.packDue i then decode w (i-5) else [])=
      gateSlots (if History5.packDue i then History5.decode w (i-5) else [])+
        2*(if History5.packDue i then 1 else 0)
  cases due : History5.packDue i
  · simp only [due,Bool.false_eq_true,if_false,mul_zero,add_zero]
    exact ⟨trivial,trivial,trivial⟩
  · simpa only [due,if_true,mul_one] using
      decode_metrics w (i-5)

end ECDSAAdd.Entrant.NewHistory5

namespace ECDSAAdd.Entrant.ParityCodec5New
open Arithmetic Challenge Baselines

theorem first_decode_metrics (f : Fin 10 → Wire) :
    toffoliCount (decodeAtFirst f)=toffoliCount (FirstNonzeroCodec.decodeAtFirst f) ∧
    measurementCount (decodeAtFirst f)=measurementCount (FirstNonzeroCodec.decodeAtFirst f) ∧
    gateSlots (decodeAtFirst f)=gateSlots (FirstNonzeroCodec.decodeAtFirst f)+2 := by
  have n := first_countsAt f
  have o := FirstNonzeroCodec.counts
  have ns := first_slotsAt f
  have os := FirstNonzeroCodec.restricted_slots
  simp only [FirstNonzeroCodec.decodeAtFirst,renameProgram_counts,rename_gateSlots]
  exact ⟨n.2.1.trans o.2.1.symm,n.2.2.2.trans o.2.2.2.symm,by omega⟩

end ECDSAAdd.Entrant.ParityCodec5New

end

-- Public component FrontierEntry1591Callers.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.FrontierEntry1591Callers
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
  ControlledPointLayout CompressedPointDialog EntryFuse EntryFuseFinite
attribute [local irreducible] run wires

def EntryCorrect (K : Program) : Prop := ∀ (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)),
    let out := run K m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q

def ExitCorrect (K : Program) : Prop := ∀
    (hn : (skywalkSharedWires base).Nodup) (hlo : HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false),
    let out := run K m s
    out.phase=s.phase ∧ regValue (skywalkArithmeticNumerator base) out.basis=centerWord (Y*(x:Fp)/2) ∧
      ∀q,q∉skywalkArithmeticNumerator base → out.basis q=s.basis q

private theorem mapped_reg (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- A renamed replay receives the same pool as a canonical virtual state,
while its actual numerator has already been half-centered. -/
theorem entryTransfer (K : Program) (correct : EntryCorrect K) (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires K⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f K) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits (q : Wire) (hq : q∈domain) : b.basis q=t.basis (f q) := by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [mapped_reg f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [mapped_reg f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside (q : Wire) (hq : q∈domain) (haway : q∉wireBlock base 2056 256) : f q∉L.point.y := by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩ := List.mem_map.mp bad
    have eq : q=r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q := by
    intro q hq
    by_cases used : q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    rw [mapped_reg f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective K sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (mapped_reg f _ (run K m b).basis
      (run (renameProgram f K) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain K sites m t q image).trans (same q hq)


section Entry
variable (K : Program) (kernelSupport : wires K⊆OB5Support.logicalSites) (correct : EntryCorrect K)

def entry (K : Program) (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) K

include kernelSupport in
theorem entry_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (entry K L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ kernelSupport

private theorem entry_divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem entry_numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem entry_control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

include kernelSupport correct in
theorem entry_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (entry K L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact entryTransfer K correct L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    entry_divisor_sitesS entry_numerator_sitesS entry_control_siteS (kernelSupport.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] entry arithS

include kernelSupport correct in
theorem entry_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    run (entry K L) m t=run (arithS L false) [] s := by
  have newer := entry_correct K kernelSupport correct L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (entry K L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm


def division (K : Program) (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ entry K L

section EntryStep
attribute [local irreducible] fusedY fastConstAdd

include kernelSupport correct in
theorem division_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (division K L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin) := by
  intro s m v
  let Z : Fp := Y+(if G then k else 0)
  let n := measurementCount (fusedY L k)
  let a := run (fusedY L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase : a.phase=c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis=centerWord (Z/2) := by
    simpa only [v.generic,Z] using fused.2.1
  have hp : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := entry_eq K kernelSupport correct L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (division K L k) m s=run (arithS L false) [] c := by
    simp only [division,run_append]
    change run (entry K L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep
end Entry

section Exit
variable (K : Program) (kernelSupport : wires K⊆OB5Support.logicalSites) (correct : ExitCorrect K)

def exit (K : Program) (L : ControlledPointLayout) : Program:=renameProgram (wireFn2 L) K
include kernelSupport correct in
theorem exit_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (hX : X < p) (hX0 : 0 < X) (hY : Y < p)
    (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (exit K L) m s).phase=s.phase ∧
    regValue L.point.y (run (exit K L) m s).basis=
      centerWord (((Y:Fp)*(X:Fp))/2) ∧
    ∀q,q∉L.point.y → (run (exit K L) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,
    selectorG,selectorS,zeroFlag⟩
  have dx : (wireBlock base 770 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have dy : (wireBlock base 2056 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have result := OwnExitFuseQ5.wordTransfer L (wireFn2 L) OB5Support.logicalSites
    (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
      (ArithmeticOB5.logical_sub_old hb) eq)
    divisorMap numeratorMap
    (fun q hq used hx hy => sharedWork q hq (ArithmeticOB5.logical_sub_old used) hx hy)
    selectorG selectorS dx dy X (Y:Fp) (centerWord (((Y:Fp)*(X:Fp))/2))
    s m hx (hy.trans yValue.symm) hc
    K kernelSupport
    (fun t records input hg hs => correct
      config.1 above config.2.1 config.2.2 X (Y:Fp) hX0 hX t records input hg hs)
  simpa only [exit] using result

end Exit

end ECDSAAdd.Entrant.FrontierEntry1591Callers

end

-- Public component ParityPointResources.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Q1591Resources
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FiniteHostStack FiniteHostFusion
  FiniteHostFive GenericQ5Geometry ExitFusionResearch
attribute [local irreducible] wires run toffoliCount measurementCount fastConstAdd fastConstNeg

def genericOmissions : List Nat := [1800,766,765,767,770,1285,1286,769]

theorem qubits_ten (P : Program)
    (sub : ioWires ∪ wires P ⊆ (WrapperOB5.sites layout).toFinset)
    (free : ∀ k ∈ ([1400,1800,766,765,767,1540,770,1285,1286] : List Nat),
      layout.core.poolWire k ∉ wires P)
    (extra : layout.core.poolWire 769 ∉ wires P) : qubits P ≤ 1591 := by
  let q := layout.core.poolWire 769
  let witness : Program := [.X q] ++ P
  have qm : q ∈ (WrapperOB5.sites layout).toFinset := by
    apply List.mem_toFinset.mpr
    simp only [q,WrapperOB5.sites,List.mem_append,List.mem_singleton,
      wireBlock,List.mem_map,List.mem_range'_1]
    exact Or.inl (Or.inl (Or.inr ⟨769,by omega,rfl⟩))
  have ww : wires witness = insert q (wires P) := by
    unfold witness
    rw [wires_append]
    simp only [wires,Instr.wires,Finset.union_empty,Finset.singleton_union]
  have ws : ioWires ∪ wires witness ⊆ (WrapperOB5.sites layout).toFinset := by
    rw [ww]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact sub (Finset.mem_union.mpr (Or.inl hx))
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact qm
      · exact sub (Finset.mem_union.mpr (Or.inr hx))
  have wf : ∀ k ∈ ([1400,1800,766,765,767,1540,770,1285,1286] : List Nat),
      layout.core.poolWire k ∉ wires witness := by
    intro k hk
    rw [ww]
    intro h
    rcases Finset.mem_insert.mp h with he | hp
    · have kb : k < 2613 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        omega
      have kn : k ≠ 769 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        omega
      exact kn (pool_inj layout layout_widths layout_nodup k 769 kb (by omega) he)
    · exact free k hk hp
  have bound := Q7Inventory.qubits_nine witness ws
    (fun k hk => wf k (List.mem_append_left [1286] hk)) (wf 1286 (by simp))
  have fresh : q ∉ ioWires ∪ wires P := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact FiniteHostStack.io_avoids_pool 769 (by omega) h
    · exact extra h
  have sets : ioWires ∪ wires witness = insert q (ioWires ∪ wires P) := by
    rw [ww,Finset.union_insert]
  change (ioWires ∪ wires witness).card ≤ 1592 at bound
  rw [sets,Finset.card_insert_of_notMem fresh] at bound
  change (ioWires ∪ wires P).card ≤ 1591
  omega

theorem edges_wrapG_qubits (G : Program)
    (hG : wires G ⊆ (OB5Support.sites layout).toFinset)
    (hFree : ∀ k ∈ genericOmissions,layout.core.poolWire k ∉ wires G)
    (C : Point) (cy : Fp) :
    qubits (Edges.wrapper layout C cy (wrapG layout G)) ≤ 1591 := by
  have supported := Edges.wrapper_support layout layout_widths layout_nodup C cy _
    (wrapG_sites layout layout_widths layout_nodup G hG)
  have sub := Finset.union_subset FiniteHostStack.io_support_original supported
  have edge (k : Nat) (hk : 515≤k ∧ k<2613)
      (old : layout.core.poolWire k ∉ wires (WrapperOB5.program layout C cy (wrapG layout G))) :
      layout.core.poolWire k ∉ wires (Edges.wrapper layout C cy (wrapG layout G)) := by
    intro h
    rcases Finset.mem_union.mp (Edges.wrapper_wires layout C cy _ h) with h | h
    · exact old h
    · exact Edges.small_away layout layout_widths layout_nodup k hk
        (Edges.extra_small layout layout_widths layout_nodup C h)
  have omitted (k : Nat) (hk : k ∈ genericOmissions) :
      layout.core.poolWire k ∉ wires (Edges.wrapper layout C cy (wrapG layout G)) := by
    have bounds : 515≤k ∧ k<2613 ∧ k≠684 ∧ k≠717 ∧ k≠1400 ∧ k≠1540 := by
      simp only [genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
      omega
    apply edge k ⟨bounds.1,bounds.2.1⟩
    exact finWrapper_avoid layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩
      bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.2 _
      (wrapG_avoid_of_generic layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩
        bounds.2.2.2.2.1 G (hFree k hk)) C cy
  apply qubits_ten _ sub
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply edge 1400 (by omega)
      exact finWrapper_avoid layout layout_widths layout_nodup 1400 (by omega)
        (by omega) (by omega) (by omega) (wrapG layout G)
        (spare_not_wrapG layout layout_widths layout_nodup G hG) C cy
    · exact omitted 1800 (by simp [genericOmissions])
    · exact omitted 766 (by simp [genericOmissions])
    · exact omitted 765 (by simp [genericOmissions])
    · exact omitted 767 (by simp [genericOmissions])
    · apply edge 1540 (by omega)
      exact finWrapper_avoid1540 layout layout_widths layout_nodup _ (wrapG_noDouble G hG) C cy
    · exact omitted 770 (by simp [genericOmissions])
    · exact omitted 1285 (by simp [genericOmissions])
    · exact omitted 1286 (by simp [genericOmissions])
  · exact omitted 769 (by simp [genericOmissions])

theorem generic_counts_eq (L : ControlledPointLayout) (D : Fp → Program) (S P : Program)
    (dc : ∀ k,toffoliCount (D k)=toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF L k) ∧
      measurementCount (D k)=measurementCount (OwnOneFlagEntryQ7.fusedDivisionF L k))
    (sc : toffoliCount S=toffoliCount (OwnDiagAll12PlacedQ7.program L) ∧
      measurementCount S=measurementCount (OwnDiagAll12PlacedQ7.program L))
    (pc : toffoliCount P=toffoliCount (OwnOneFlagExitQ7.arithExit L) ∧
      measurementCount P=measurementCount (OwnOneFlagExitQ7.arithExit L)) (cx cy : Fp) :
    toffoliCount (All12Generic.generic L D S P cx cy OwnDiagAll12Square.sqOff)=toffoliCount (OwnOneFlagActual.generic L cx cy) ∧
    measurementCount (All12Generic.generic L D S P cx cy OwnDiagAll12Square.sqOff)=measurementCount (OwnOneFlagActual.generic L cx cy) := by
  have d := dc (-cy)
  simp only [OwnOneFlagActual.generic,OneFlagProducer.generic,All12Generic.generic,
    toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem gen_counts_eq (L : ControlledPointLayout) (D : Fp → Program) (S P : Program)
    (dc : ∀ k,toffoliCount (D k)=toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF L k) ∧
      measurementCount (D k)=measurementCount (OwnOneFlagEntryQ7.fusedDivisionF L k))
    (sc : toffoliCount S=toffoliCount (OwnDiagAll12PlacedQ7.program L) ∧
      measurementCount S=measurementCount (OwnDiagAll12PlacedQ7.program L))
    (pc : toffoliCount P=toffoliCount (OwnOneFlagExitQ7.arithExit L) ∧
      measurementCount P=measurementCount (OwnOneFlagExitQ7.arithExit L)) (cx cy : Fp) :
    toffoliCount (All12Generic.gen L D S P cx cy OwnDiagAll12Square.sqOff)=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
    measurementCount (All12Generic.gen L D S P cx cy OwnDiagAll12Square.sqOff)=measurementCount (OwnOneFlagActual.gen L cx cy) := by
  have h := generic_counts_eq L D S P dc sc pc cx cy
  simp only [OwnOneFlagActual.generic,OneFlagProducer.generic] at h
  simp only [OwnOneFlagActual.gen,OneFlagProducer.gen,All12Generic.gen,All12Generic.mid,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (S P : Program)
    (ds : ∀ k,wires (D k) ⊆ (OB5Support.sites L).toFinset)
    (ss : wires S ⊆ (OB5Support.sites L).toFinset)
    (ps : wires P ⊆ (OB5Support.sites L).toFinset) (cx cy : Fp) :
    wires (All12Generic.gen L D S P cx cy OwnDiagAll12Square.sqOff) ⊆ (OB5Support.genericSites L).toFinset := by
  rw [All12Generic.gen_shape (ko := OwnDiagAll12Square.sqOff)]
  exact wrapG_sites L hw hn _ (All12Generic.generic_sites L hw D S P ds ss ps cx cy OwnDiagAll12Square.sqOff)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (S P : Program)
    (dp : ∀ k,GatePhysical (D k)) (sp : GatePhysical S) (pp : GatePhysical P) (cx cy : Fp) :
    GatePhysical (All12Generic.gen L D S P cx cy OwnDiagAll12Square.sqOff) :=
  All12Generic.gen_physical L hw hn D S P dp sp pp cx cy OwnDiagAll12Square.sqOff

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (S P : Program)
    (df : ∀ c k,k ∈ genericOmissions → L.core.poolWire k ∉ wires (D c))
    (sf : ∀ k,k ∈ genericOmissions → L.core.poolWire k ∉ wires S)
    (pf : ∀ k,k ∈ genericOmissions → L.core.poolWire k ∉ wires P)
    (k : Nat) (hk : k ∈ genericOmissions) (cx cy : Fp) :
    L.core.poolWire k ∉ wires (All12Generic.generic L D S P cx cy OwnDiagAll12Square.sqOff) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  exact All12Generic.generic_free L hw hn D S P k bounds
    (fun c => df c k hk) (sf k hk) (pf k hk) cx cy OwnDiagAll12Square.sqOff

theorem gen_qubits (D : Fp → Program) (S P : Program)
    (ds : ∀ k,wires (D k) ⊆ (OB5Support.sites layout).toFinset)
    (ss : wires S ⊆ (OB5Support.sites layout).toFinset)
    (ps : wires P ⊆ (OB5Support.sites layout).toFinset)
    (df : ∀ c k,k ∈ genericOmissions → layout.core.poolWire k ∉ wires (D c))
    (sf : ∀ k,k ∈ genericOmissions → layout.core.poolWire k ∉ wires S)
    (pf : ∀ k,k ∈ genericOmissions → layout.core.poolWire k ∉ wires P)
    (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (All12Generic.gen layout D S P cx cy OwnDiagAll12Square.sqOff)) ≤ 1591 := by
  rw [All12Generic.gen_shape (ko := OwnDiagAll12Square.sqOff)]
  exact edges_wrapG_qubits _
    (All12Generic.generic_sites layout layout_widths D S P ds ss ps cx cy OwnDiagAll12Square.sqOff)
    (fun k hk => generic_free layout layout_widths layout_nodup D S P df sf pf k hk cx cy) C cy

theorem gen_slots (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp → Program) (S P : Program)
    (ds : ∀ k,gateSlots (D k) ≤ 20527454)
    (ss : gateSlots S ≤ 8000000) (ps : gateSlots P ≤ 20502454) (cx cy : Fp) :
    gateSlots (All12Generic.gen L D S P cx cy OwnDiagAll12Square.sqOff) ≤ 49204896 := by
  have add (k : Fp) : gateSlots (fastConstAdd L L.point.x k) ≤ 15368 := by
    simpa only [fastConstAdd] using FastConst.fastAdd_gateSlots_le
      (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have neg : gateSlots (fastConstNeg L cx) ≤ 17928 := by
    simpa only [fastConstNeg] using FastConst.fastNeg_gateSlots_le
      (g:=L.core.generic) 256 p cx.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a := add (-cx)
  have b := add (3*cx-(OwnDiagAll12Square.sqOff : Nat))
  have d := ds (-cy)
  have e := exitY_slots L hw cy
  have z := zrep_gateSlots_le L hw
  have c := clrF_gateSlots_le L hw
  simp only [All12Generic.gen,All12Generic.mid,All12Generic.generic,gateSlots_append,rename_gateSlots]
  omega

theorem gen_slots_eq (L : ControlledPointLayout) (D : Fp → Program) (S P : Program)
    (ds : ∀ k,gateSlots (D k)=gateSlots (OwnOneFlagEntryQ7.fusedDivisionF L k)+2448)
    (ss : gateSlots S=gateSlots (OwnDiagAll12PlacedQ7.program L))
    (ps : gateSlots P=gateSlots (OwnOneFlagExitQ7.arithExit L)+2448) (cx cy : Fp) :
    gateSlots (All12Generic.gen L D S P cx cy OwnDiagAll12Square.sqOff)=
      gateSlots (OwnOneFlagActual.gen L cx cy)+4896 := by
  have d := ds (-cy)
  simp only [OwnOneFlagActual.gen,OneFlagProducer.gen,All12Generic.gen,
    All12Generic.mid,All12Generic.generic,gateSlots_append,rename_gateSlots]
  omega

theorem wrapper_slots (L : ControlledPointLayout) (hw : L.Widths)
    (G : Program) (gs : gateSlots G ≤ 49204896) (C : Point) (cy : Fp) :
    gateSlots (Edges.wrapper L C cy G) ≤ 50004900 := by
  have h := Edges.wrapper_slots L hw C cy G
  omega

end ECDSAAdd.Entrant.Q1591Resources

end

-- Public component FrontierEntry1591CallerResources.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Callers
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount

def logicalOmissions : List Nat := [2312,766,765,767,1026,1541,1542,1797]

theorem placed_physical (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kp : GatePhysical K) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (renameProgram (wireFn2 L) K) := by
  apply gatePhysical_rename_support (wireFn2 L) K
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (ks ha))
      b (ArithmeticOB5.logical_sub_old (ks hb)) eq
  · exact kp

theorem division_support (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (division K L k)⊆(OB5Support.sites L).toFinset := by
  simp only [division,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    entry_support K ks L hw⟩

theorem exit_support (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (L : ControlledPointLayout) (hw : L.Widths) :
    wires (exit K L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ ks

theorem division_physical (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kp : GatePhysical K) (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (division K L k) := by
  simp only [division,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,placed_physical K ks kp L hw hn⟩

theorem division_counts_eq (K : Program)
    (kc : toffoliCount K=toffoliCount OwnOneFlagEntryQ7.kernel5S ∧
      measurementCount K=measurementCount OwnOneFlagEntryQ7.kernel5S)
    (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (division K L k)=toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF L k) ∧
      measurementCount (division K L k)=measurementCount (OwnOneFlagEntryQ7.fusedDivisionF L k) := by
  simp only [division,entry,OwnOneFlagEntryQ7.fusedDivisionF,OwnOneFlagEntryQ7.arithEntryS,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  exact ⟨congrArg _ kc.1,congrArg _ kc.2⟩

theorem exit_counts_eq (K : Program)
    (kc : toffoliCount K=toffoliCount OwnOneFlagExitQ7.kernelS ∧
      measurementCount K=measurementCount OwnOneFlagExitQ7.kernelS)
    (L : ControlledPointLayout) :
    toffoliCount (exit K L)=toffoliCount (OwnOneFlagExitQ7.arithExit L) ∧
      measurementCount (exit K L)=measurementCount (OwnOneFlagExitQ7.arithExit L) := by
  simpa only [exit,OwnOneFlagExitQ7.arithExit,renameProgram_counts] using kc

theorem exit_slots (K : Program) (ks : gateSlots K≤20502454) (L : ControlledPointLayout) :
    gateSlots (exit K L)≤20502454 := by
  simpa only [exit,rename_gateSlots] using ks

theorem division_slots (K : Program) (ks : gateSlots K≤20502454)
    (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    gateSlots (division K L k)≤20527454 := by
  have y:=entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
  simp only [division,entry,EntryFuse.fusedY,gateSlots_append,rename_gateSlots]
  omega

private theorem logical_site (i : Nat) (hi : i∈logicalOmissions) :
    base i∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  simp only [logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem placed_free (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (i k : Nat)
    (hi : base i∈OB5Support.logicalSites) (hm : wireFn2 L (base i)=L.core.poolWire k)
    (free : base i∉wires K) : L.core.poolWire k∉wires (renameProgram (wireFn2 L) K) := by
  rw [renameProgram_support]
  intro h
  obtain ⟨old,used,eq⟩ := Finset.mem_image.mp h
  have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
  have back := (placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (ks used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
  exact free (back ▸ used)

theorem placed_omissions (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kf : ∀i∈logicalOmissions,base i∉wires K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈Q1591Resources.genericOmissions) :
    L.core.poolWire k∉wires (renameProgram (wireFn2 L) K) := by
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact placed_free K ks L hw hn 2312 1800 (logical_site 2312 (by simp [logicalOmissions]))
      rfl (kf 2312 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 766 766 (logical_site 766 (by simp [logicalOmissions]))
      rfl (kf 766 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 765 765 (logical_site 765 (by simp [logicalOmissions]))
      rfl (kf 765 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 767 767 (logical_site 767 (by simp [logicalOmissions]))
      rfl (kf 767 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 1026 770 (logical_site 1026 (by simp [logicalOmissions]))
      rfl (kf 1026 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 1541 1285 (logical_site 1541 (by simp [logicalOmissions]))
      rfl (kf 1541 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 1542 1286 (logical_site 1542 (by simp [logicalOmissions]))
      rfl (kf 1542 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 1797 769 (logical_site 1797 (by simp [logicalOmissions]))
      rfl (kf 1797 (by simp [logicalOmissions]))

theorem division_free (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kf : ∀i∈logicalOmissions,base i∉wires K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Fp) (k : Nat) (hk : k∈Q1591Resources.genericOmissions) :
    L.core.poolWire k∉wires (division K L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  have old := ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [division,entry,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),placed_omissions K ks kf L hw hn k hk⟩

end ECDSAAdd.Entrant.FrontierEntry1591Callers

end

-- Public component FrontierEntry1591FieldResources.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierSW1591
open Arithmetic MappedCompressed Challenge Baselines
attribute [local irreducible] wires toffoliCount measurementCount gateSlots

private theorem encode_metrics (start : Nat) :
    toffoliCount (NewHistory5.encode base start)=toffoliCount (History5.encode base start) ∧
    measurementCount (NewHistory5.encode base start)=measurementCount (History5.encode base start) ∧
    gateSlots (NewHistory5.encode base start)=gateSlots (History5.encode base start)+2 := by
  have n:=NewHistory5.encode_counts base start
  have o:=History5.encode_counts base start
  refine ⟨by omega,by omega,?_⟩
  simp only [NewHistory5.encode,History5.encode,ParityCodec5New.slotsAt,MeasuredCodec5.slotsAt]

theorem packet_metrics (divide : Bool) (j : Nat) :
    toffoliCount (packetS divide j)=toffoliCount (OneFlagSW.packetS divide j) ∧
    measurementCount (packetS divide j)=measurementCount (OneFlagSW.packetS divide j) ∧
    gateSlots (packetS divide j)=gateSlots (OneFlagSW.packetS divide j)+4 := by
  have e:=encode_metrics (5*j)
  have d:=NewHistory5.decode_metrics base (5*j)
  have raw : rawReplayS divide (Replay5.letters j)=OneFlagSW.rawReplayS divide (Replay5.letters j) := rfl
  simp only [packetS,OneFlagSW.packetS,renameProgram_counts,rename_gateSlots,
    basePacketS,OneFlagSW.basePacketS,toffoliCount_append,measurementCount_append,
    gateSlots_append,raw]
  exact ⟨by omega,by omega,by omega⟩

theorem first_metrics (divide : Bool) :
    toffoliCount (firstPacketS divide)=toffoliCount (OneFlagSW.firstPacketS divide) ∧
    measurementCount (firstPacketS divide)=measurementCount (OneFlagSW.firstPacketS divide) ∧
    gateSlots (firstPacketS divide)=gateSlots (OneFlagSW.firstPacketS divide)+4 := by
  have e:=encode_metrics 0
  have d:=NewHistory5.decode_metrics base 0
  have raw : firstBodyS divide=OneFlagSW.firstBodyS divide := rfl
  simp only [firstPacketS,OneFlagSW.firstPacketS,renameProgram_counts,rename_gateSlots,
    baseFirstPacketS,OneFlagSW.baseFirstPacketS,toffoliCount_append,measurementCount_append,
    gateSlots_append,raw]
  exact ⟨by omega,by omega,by omega⟩

theorem groups_metrics (divide : Bool) (j n : Nat) :
    toffoliCount (groupsS divide j n)=toffoliCount (OneFlagSW.groupsS divide j n) ∧
    measurementCount (groupsS divide j n)=measurementCount (OneFlagSW.groupsS divide j n) ∧
    gateSlots (groupsS divide j n)=gateSlots (OneFlagSW.groupsS divide j n)+4*n := by
  induction n generalizing j with
  | zero => simp [groupsS,OneFlagSW.groupsS,PacketSequence.program,toffoliCount,measurementCount,gateSlots]
  | succ n ih =>
    have head:=packet_metrics divide j
    have rest:=ih (j+1)
    cases divide <;> simp only [groupsS,OneFlagSW.groupsS,PacketSequence.program,
      Bool.false_eq_true,if_false,if_true,toffoliCount_append,measurementCount_append,gateSlots_append]
    all_goals
      change _=_ ∧ _=_ ∧ _=_ at rest
      simp only [groupsS,OneFlagSW.groupsS] at rest
      exact ⟨by omega,by omega,by omega⟩

theorem replay_metrics (divide : Bool) :
    toffoliCount (replayS divide)=toffoliCount (OneFlagSW.replayS divide) ∧
    measurementCount (replayS divide)=measurementCount (OneFlagSW.replayS divide) ∧
    gateSlots (replayS divide)=gateSlots (OneFlagSW.replayS divide)+408 := by
  have mid:=groups_metrics divide 1 101
  have first:=first_metrics divide
  have last : endPacketS divide=OneFlagSW.endPacketS divide := rfl
  cases divide <;> simp only [replayS,OneFlagSW.replayS,renameProgram_counts,rename_gateSlots,
    logicalReplayS,OneFlagSW.logicalReplayS,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,gateSlots_append,last] <;>
    exact ⟨by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.FrontierSW1591

namespace ECDSAAdd.Entrant.FrontierReplay1591
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] wires

private theorem codec_physical (start : Nat) (hs : start+5≤512) :
    GatePhysical (NewHistory5.encode base start) ∧ GatePhysical (NewHistory5.decode base start) :=
  ParityCodec5New.physicalAt _ (History5.historyMap_injective base base_pool_nodup start hs)

theorem packet_physical (divide : Bool) (j : Nat) (hj : j<102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (Replay5.letters j)) :
    GatePhysical (packet divide j) := by
  have codec:=codec_physical (5*j) (by omega)
  have raw : GatePhysical (body divide j) := OneFlagReplay.raw_physical divide _ hn ho hf
  exact gatePhysical_rename _ (shifted (Placement5.pi j)).injective _
    ((gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨codec.2,raw⟩,codec.1⟩)

theorem groups_physical (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : ∀k,k<102 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (Replay5.letters k)) :
    GatePhysical (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,GatePhysical]
  | succ n ih =>
    have head:=packet_physical divide j (by omega) hn ho (hf j (by omega))
    have rest:=ih (j+1) (by omega)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,
      if_false,if_true,gatePhysical_append]
    · exact ⟨rest,head⟩
    · exact ⟨head,rest⟩

theorem first_physical (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (firstPacket divide) := by
  have swap : GatePhysical firstSwap := by
    unfold firstSwap OneFlagCell.selectSwap
    apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    exact swapRegisters_physical _ _ _ OneFlagReplay.base_sign_nd
  have swapM : GatePhysical firstSwapM := by
    unfold firstSwapM OneFlagCell.selectMSwap
    apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    exact UncompSwap.mswap_physical _ _ _ OneFlagReplay.base_sign_nd
  have layout : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      Replay5.restLetters := by
    intro l hl
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hl
    have bound:=List.mem_range'_1.mp hk
    simpa only [Replay5.restLetters,tapeLetter] using mixedTape_getD_layout base _ _ _ hf k (by omega)
  have rest : GatePhysical (rawReplay divide Replay5.restLetters) :=
    OneFlagReplay.raw_physical divide _ hn ho layout
  have codec:=codec_physical 0 (by omega)
  have body : GatePhysical (baseFirstPacket divide) := by
    cases divide <;> simp only [baseFirstPacket,firstBody,Bool.false_eq_true,
      if_false,if_true,gatePhysical_append]
    · exact ⟨⟨codec.2,rest,swapM⟩,codec.1⟩
    · exact ⟨⟨codec.2,swap,rest⟩,codec.1⟩
  exact gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ body

theorem physical (divide : Bool) : GatePhysical (replay divide) := by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have first:=first_physical divide cfg.1 cfg.2.1 cfg.2.2
  have mid:=groups_physical divide 1 101 (by omega) cfg.1 cfg.2.1 (Replay5.letters_layouts cfg.2.2)
  have last : GatePhysical (endPacket divide) := OneFlagReplay.endPacket_physical divide
  apply gatePhysical_rename _ (OB5.sig_injective 511 (by omega))
  cases divide <;> simp only [logicalReplay,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨last,mid⟩,first⟩
  · exact ⟨⟨first,mid⟩,last⟩

end ECDSAAdd.Entrant.FrontierReplay1591

namespace ECDSAAdd.Entrant.FrontierEntry1591Field
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport Challenge Baselines
attribute [local irreducible] wires toffoliCount measurementCount gateSlots

private theorem hosted_metrics (P Q : Program)
    (h : toffoliCount P=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
      gateSlots P=gateSlots Q+408) :
    toffoliCount (hosted P)=toffoliCount (hosted Q) ∧
    measurementCount (hosted P)=measurementCount (hosted Q) ∧
    gateSlots (hosted P)=gateSlots (hosted Q)+408 := by
  simp only [hosted,toffoliCount_append,measurementCount_append,gateSlots_append,
    renameProgram_counts,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem entryHosted_metrics :
    toffoliCount entryHosted=toffoliCount OneFlagEntryRaw.hostField5S ∧
    measurementCount entryHosted=measurementCount OneFlagEntryRaw.hostField5S ∧
    gateSlots entryHosted=gateSlots OneFlagEntryRaw.hostField5S+408 := by
  apply hosted_metrics entryField OneFlagEntryRaw.field5S
  have h:=FrontierSW1591.replay_metrics true
  simp only [entryField,OneFlagEntryRaw.field5S,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem exitHosted_metrics :
    toffoliCount exitHosted=toffoliCount OneFlagExitRaw.hostMulS ∧
    measurementCount exitHosted=measurementCount OneFlagExitRaw.hostMulS ∧
    gateSlots exitHosted=gateSlots OneFlagExitRaw.hostMulS+408 := by
  apply hosted_metrics exitField OneFlagExitRaw.fieldMulS
  have h:=FrontierSW1591.replay_metrics false
  simp only [exitField,OneFlagExitRaw.fieldMulS,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem entry_counts_eq : toffoliCount entry=toffoliCount OneFlagEntryRaw.hostField5S ∧
    measurementCount entry=measurementCount OneFlagEntryRaw.hostField5S :=
  ⟨entry_counts.1.trans entryHosted_metrics.1,
    entry_counts.2.1.trans entryHosted_metrics.2.1⟩

theorem exit_counts_eq : toffoliCount exit=toffoliCount OneFlagExitRaw.hostMulS ∧
    measurementCount exit=measurementCount OneFlagExitRaw.hostMulS :=
  ⟨exit_counts.1.trans exitHosted_metrics.1,
    exit_counts.2.1.trans exitHosted_metrics.2.1⟩

private theorem slot_sum (n : Nat) : (n+408)+1632=n+2040 := by omega

theorem entry_slots : gateSlots entry=gateSlots OneFlagEntryRaw.hostField5S+2040 :=
  entry_counts.2.2.trans ((congrArg (fun n=>n+1632) entryHosted_metrics.2.2).trans (slot_sum _))

theorem exit_slots : gateSlots exit=gateSlots OneFlagExitRaw.hostMulS+2040 :=
  exit_counts.2.2.trans ((congrArg (fun n=>n+1632) exitHosted_metrics.2.2).trans (slot_sum _))

theorem entry_physical : GatePhysical entry := by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have ends:=OwnQ5Endpoint.endpoint_physical cfg.1
  have replay:=(FrontierSW1591.selReplay_sel true).sub.physical (FrontierReplay1591.physical true)
  apply ParityField1591.physical controls work host entryHosted host_not_controls
  apply Q5FusionFields.host_physical
  exact (gatePhysical_append _ _).mpr ⟨replay,(gatePhysical_append _ _).mpr ⟨ends.2.2,ends.2.1⟩⟩

theorem exit_physical : GatePhysical exit := by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have ends:=OwnQ5Endpoint.endpoint_physical cfg.1
  have replay:=(FrontierSW1591.selReplay_sel false).sub.physical (FrontierReplay1591.physical false)
  apply ParityField1591.physical controls work host exitHosted host_not_controls
  apply Q5FusionFields.host_physical
  exact (gatePhysical_append _ _).mpr ⟨ends.1,(gatePhysical_append _ _).mpr ⟨ends.2.2,replay⟩⟩

theorem entryHosted_support_eq : wires entryHosted=wires OneFlagEntryRaw.hostField5S := by
  simp only [entryHosted,hosted,entryField,OneFlagEntryRaw.hostField5S,OneFlagEntryRaw.field5S,
    wires_append,renameProgram_support,FrontierSW1591.support_eq]

theorem exitHosted_support_eq : wires exitHosted=wires OneFlagExitRaw.hostMulS := by
  simp only [exitHosted,hosted,exitField,OneFlagExitRaw.hostMulS,OneFlagExitRaw.fieldMulS,
    wires_append,renameProgram_support,FrontierSW1591.support_eq]

theorem entryHosted_support : wires entryHosted⊆OB5Support.logicalSites := by
  rw [entryHosted_support_eq]
  exact OneFlagEntryRaw.selHostField5.sub.wires_sub.trans
    (OneFlagEntryGeometry.host_support _ OneFlagEntryRaw.field_support)

theorem exitHosted_support : wires exitHosted⊆OB5Support.logicalSites := by
  rw [exitHosted_support_eq]
  exact OneFlagExitRaw.selHost.sub.wires_sub.trans
    (OneFlagEntryGeometry.host_support _ OneFlagExitGeometry.field_support)

theorem controls_index (q : Wire) (hq : q∈controls) :
    ∃j,q=base j ∧ (j<510 ∨ (1028≤j ∧ j<1285) ∨ (1544≤j ∧ j<1797)) := by
  obtain ⟨i,hi,eq⟩:=controls_member q hq
  have bound:=(payload_index_bound i hi).2
  rw [←eq,(payload_index_bound i hi).1,OB5.sig_base 511 _ (by omega)]
  refine ⟨_,rfl,?_⟩
  split_ifs <;> omega

theorem controls_support : controls.toFinset⊆OB5Support.logicalSites := by
  intro q hq
  obtain ⟨i,rfl,hi⟩:=controls_index q (List.mem_toFinset.mp hq)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  omega

theorem controls_free (i : Nat) (hi : i∈FrontierEntry1591Callers.logicalOmissions) :
    base i∉controls := by
  intro used
  obtain ⟨j,eq,hj⟩:=controls_index _ used
  have same:=base_injective eq
  simp only [FrontierEntry1591Callers.logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem work_support : work∈OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨1797,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  omega

private theorem host_support : host∈OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨1543,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  omega

private theorem program_support (P : Program) (hp : wires P⊆OB5Support.logicalSites) :
    wires (ParityField1591.program controls work host P)⊆OB5Support.logicalSites := by
  have mid:=OwnDiagAll12Placed.swap_support P work host OB5Support.logicalSites hp
    work_support host_support
  rw [renameProgram_support] at mid
  intro q hq
  rcases Finset.mem_union.mp (ParityField1591.support controls work host P hq) with h|h
  · rcases Finset.mem_insert.mp h with rfl|h
    · exact host_support
    · exact controls_support h
  · exact mid h

theorem entry_support : wires entry⊆OB5Support.logicalSites :=
  program_support _ entryHosted_support

theorem exit_support : wires exit⊆OB5Support.logicalSites :=
  program_support _ exitHosted_support

private theorem entryHosted_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
    base i∉wires entryHosted := by
  rw [entryHosted_support_eq]
  by_cases last:i=1542
  · subst i;exact OneFlagEntrySupport.hostS1542_free
  have allowed : i∈[1541,1026,2312,766,765,767] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  have old:=Q6EndpointOmissions.host_free _ i allowed (Q6EndpointOmissions.field_free i allowed)
  exact fun used=>old (OneFlagEntrySupport.hostS_subset used)

private theorem exitHosted_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
    base i∉wires exitHosted := by
  rw [exitHosted_support_eq]
  by_cases last:i=1542
  · subst i;exact OneFlagExitSupport.hostS1542_free
  have allowed : i∈[1541,1026,2312,766,765,767] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  have field : base i∉wires OneFlagExitRaw.fieldMul := by
    simp only [OneFlagExitRaw.fieldMul,wires_append,Finset.mem_union,not_or]
    exact ⟨(Q6EndpointOmissions.converter_free i allowed).1,
      Q6EndpointOmissions.copy_free i allowed,
      fun used=>Q6EndpointOmissions.replay_free false i allowed
        (OneFlagReplay.replay_subset_old false used)⟩
  have old:=Q6EndpointOmissions.host_free _ i allowed field
  exact fun used=>old (OneFlagExitRaw.selHost.sub.wires_sub used)

private theorem program_free (P : Program) (i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542]) (free : base i∉wires P) :
    base i∉wires (ParityField1591.program controls work host P) := by
  have bounds : i≠1797 ∧ i≠1543 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  have aw : base i≠work := fun eq=>bounds.1 (base_injective eq)
  have ah : base i≠host := fun eq=>bounds.2 (base_injective eq)
  have fix : Equiv.swap work host (base i)=base i := Equiv.swap_apply_of_ne_of_ne aw ah
  have noControls : base i∉controls := controls_free i (by
    simp only [FrontierEntry1591Callers.logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega)
  intro used
  rcases Finset.mem_union.mp (ParityField1591.support controls work host P used) with h|h
  · rcases Finset.mem_insert.mp h with h|h
    · exact ah h
    · exact noControls (List.mem_toFinset.mp h)
  · obtain ⟨old,mem,eq⟩:=Finset.mem_image.mp h
    have same:=(Equiv.swap work host).injective (eq.trans fix.symm)
    exact free (same ▸ mem)

theorem entry_free (i : Nat) (hi : i∈FrontierEntry1591Callers.logicalOmissions) :
    base i∉wires entry := by
  by_cases last:i=1797
  · subst i
    exact ParityField1591.avoids_work controls work host entryHosted (by decide)
      work_not_controls entryHosted_avoids_host
  have allowed : i∈[2312,766,765,767,1026,1541,1542] := by
    simp only [FrontierEntry1591Callers.logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  exact program_free _ i allowed (entryHosted_free i allowed)

theorem exit_free (i : Nat) (hi : i∈FrontierEntry1591Callers.logicalOmissions) :
    base i∉wires exit := by
  by_cases last:i=1797
  · subst i
    exact ParityField1591.avoids_work controls work host exitHosted (by decide)
      work_not_controls exitHosted_avoids_host
  have allowed : i∈[2312,766,765,767,1026,1541,1542] := by
    simp only [FrontierEntry1591Callers.logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  exact program_free _ i allowed (exitHosted_free i allowed)

end ECDSAAdd.Entrant.FrontierEntry1591Field

end

-- Public component ParityInverseResources.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewStackOB5
open Arithmetic Challenge Baselines MappedCompressed Secp256k1 OB5
attribute [local irreducible] reverse regularReverse StackOB5.reverse Stack5.reverse5

theorem unpackFirst_metrics (w : Nat → Wire) (i : Nat) :
    toffoliCount (unpackFirst w i)=toffoliCount (FirstNonzeroCodec.unpack9first w i) ∧
    measurementCount (unpackFirst w i)=measurementCount (FirstNonzeroCodec.unpack9first w i) ∧
    gateSlots (unpackFirst w i)=gateSlots (FirstNonzeroCodec.unpack9first w i)+
      2*(if History5.packDue i then 1 else 0) := by
  by_cases hi : i=5
  · subst i
    simpa only [unpackFirst,FirstNonzeroCodec.unpack9first,if_pos rfl,
      show History5.packDue 5=true from rfl,if_true,mul_one] using
      ParityCodec5New.first_decode_metrics (History5.historyMap w 0)
  · simpa only [unpackFirst,FirstNonzeroCodec.unpack9first,if_neg hi,
      FirstNonzeroCodec.unpack11] using NewHistory5.decodeBefore_metrics w i

theorem regularReverse_metrics (w : Nat → Wire) (i n : Nat) :
    toffoliCount (regularReverse w i n)=toffoliCount (Stack5.reverse5 w i n) ∧
    measurementCount (regularReverse w i n)=measurementCount (Stack5.reverse5 w i n) ∧
    gateSlots (regularReverse w i n)=gateSlots (Stack5.reverse5 w i n)+2*History5.packCount i n := by
  induction n generalizing i with
  | zero => simp [regularReverse,Stack5.reverse5,History5.packCount]
  | succ n ih =>
    have tail := ih (i+1)
    have step := NewHistory5.decodeBefore_metrics w i
    simp only [regularReverse,Stack5.reverse5,History5.packCount,toffoliCount_append,
      measurementCount_append,gateSlots_append]
    constructor
    · omega
    · constructor <;> omega

theorem reverse_metrics (i n : Nat) :
    toffoliCount (reverse i n)=toffoliCount (StackOB5.reverse i n) ∧
    measurementCount (reverse i n)=measurementCount (StackOB5.reverse i n) ∧
    gateSlots (reverse i n)=gateSlots (StackOB5.reverse i n)+2*History5.packCount i n := by
  induction n generalizing i with
  | zero => simp [reverse,StackOB5.reverse,History5.packCount]
  | succ n ih =>
    have tail := ih (i+1)
    have step := unpackFirst_metrics base i
    simp only [reverse,StackOB5.reverse,History5.packCount,toffoliCount_append,
      measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots]
    constructor
    · omega
    · constructor <;> omega

theorem stackReverse510_metrics_eq :
    toffoliCount stackReverse510=toffoliCount ECDSAAdd.Entrant.stackReverse510 ∧
    measurementCount stackReverse510=measurementCount ECDSAAdd.Entrant.stackReverse510 ∧
    gateSlots stackReverse510=gateSlots ECDSAAdd.Entrant.stackReverse510+204 := by
  have tail := reverse_metrics 1 509
  have step := NewHistory5.decodeBefore_metrics base 510
  have packets : History5.packCount 1 509=101 := by decide
  have due : History5.packDue 510=true := by decide
  rw [packets] at tail
  simp [due] at step
  simp only [stackReverse510,ECDSAAdd.Entrant.stackReverse510,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots]
  constructor
  · omega
  · constructor <;> omega

theorem stackReverseT_counts :
    toffoliCount stackReverseT=toffoliCount ECDSAAdd.Entrant.stackReverseT ∧
    measurementCount stackReverseT=measurementCount ECDSAAdd.Entrant.stackReverseT := by
  have h := stackReverse510_metrics_eq
  simp only [stackReverseT,ECDSAAdd.Entrant.stackReverseT,toffoliCount_append,
    measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem stackReverseT_slots :
    gateSlots stackReverseT=gateSlots ECDSAAdd.Entrant.stackReverseT+204 := by
  have h := stackReverse510_metrics_eq
  simp only [stackReverseT,ECDSAAdd.Entrant.stackReverseT,gateSlots_append]
  omega

end ECDSAAdd.Entrant.NewStackOB5

end

-- Public component FrontierEntry1591KernelResources.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic Secp256k1 Challenge Baselines MappedCompressed DirectSkywalk
open FrontierEntry1591Callers
attribute [local irreducible] wires run toffoliCount measurementCount gateSlots

theorem first_metrics :
    toffoliCount firstPhase=toffoliCount Q5Global718.firstPhase ∧
    measurementCount firstPhase=measurementCount Q5Global718.firstPhase ∧
    gateSlots firstPhase=gateSlots Q5Global718.firstPhase+204 := by
  have n := FrontierEntry1591Native.counts base
  have o := NativeFirstDirect.forward_counts base
  have s := FrontierEntry1591Native.slots base
  have f := NewStackOB5.stackForwardT_counts
  simp only [firstPhase,Q5Global718.firstPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem last_metrics :
    toffoliCount lastPhase=toffoliCount Q5Global718.lastPhase ∧
    measurementCount lastPhase=measurementCount Q5Global718.lastPhase ∧
    gateSlots lastPhase=gateSlots Q5Global718.lastPhase+204 := by
  have n := FrontierEntry1591Native.counts base
  have o := NativeFirstKnown.inverse_counts base
  have s := FrontierEntry1591Native.slots base
  have r := NewStackOB5.stackReverseT_counts
  have rs := NewStackOB5.stackReverseT_slots
  simp only [lastPhase,Q5Global718.lastPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem relocated_counts_eq (F Old : Program)
    (fc : toffoliCount F=toffoliCount Old ∧ measurementCount F=measurementCount Old) :
    toffoliCount (FrontierEntry1591Native.relocated firstPhase F lastPhase)=
      toffoliCount (Q7FusionPhase.relocated Old) ∧
    measurementCount (FrontierEntry1591Native.relocated firstPhase F lastPhase)=
      measurementCount (Q7FusionPhase.relocated Old) := by
  have a := FrontierEntry1591Native.relocated_counts firstPhase F lastPhase
  have b := OneFlagEntryResources.outer_counts Old
  have f := first_metrics
  have r := last_metrics
  simp only [FrontierEntry1591Native.kernel,Q5FusionPhase.kernel,
    toffoliCount_append,measurementCount_append] at a b
  exact ⟨by omega,by omega⟩

private theorem relocated_slots_eq (F Old : Program)
    (fs : gateSlots F=gateSlots Old+2040) :
    gateSlots (FrontierEntry1591Native.relocated firstPhase F lastPhase)=
      gateSlots (Q7FusionPhase.relocated Old)+2448 := by
  have a := FrontierEntry1591Native.relocated_slots firstPhase F lastPhase
  have b := OneFlagEntryResources.outer_slots Old
  have f := first_metrics
  have r := last_metrics
  simp only [FrontierEntry1591Native.kernel,Q5FusionPhase.kernel,gateSlots_append] at a b
  omega

theorem entry_counts_eq :
    toffoliCount entryKernel=toffoliCount OwnOneFlagEntryQ7.kernel5S ∧
    measurementCount entryKernel=measurementCount OwnOneFlagEntryQ7.kernel5S :=
  relocated_counts_eq FrontierEntry1591Field.entry OneFlagEntryRaw.hostField5S
    FrontierEntry1591Field.entry_counts_eq

theorem exit_counts_eq :
    toffoliCount exitKernel=toffoliCount OwnOneFlagExitQ7.kernelS ∧
    measurementCount exitKernel=measurementCount OwnOneFlagExitQ7.kernelS :=
  relocated_counts_eq FrontierEntry1591Field.exit OneFlagExitRaw.hostMulS
    FrontierEntry1591Field.exit_counts_eq

theorem entry_slots_eq :
    gateSlots entryKernel=gateSlots OwnOneFlagEntryQ7.kernel5S+2448 := by
  have shape : entryKernel=FrontierEntry1591Native.relocated firstPhase
      FrontierEntry1591Field.entry lastPhase := rfl
  have old : Q7FusionPhase.relocated OneFlagEntryRaw.hostField5S=OwnOneFlagEntryQ7.kernel5S := rfl
  exact (congrArg gateSlots shape).trans
    ((relocated_slots_eq FrontierEntry1591Field.entry OneFlagEntryRaw.hostField5S
      FrontierEntry1591Field.entry_slots).trans (congrArg (fun P : Program => gateSlots P+2448) old))

theorem exit_slots_eq :
    gateSlots exitKernel=gateSlots OwnOneFlagExitQ7.kernelS+2448 := by
  have shape : exitKernel=FrontierEntry1591Native.relocated firstPhase
      FrontierEntry1591Field.exit lastPhase := rfl
  have old : Q7FusionPhase.relocated OneFlagExitRaw.hostMulS=OwnOneFlagExitQ7.kernelS := rfl
  exact (congrArg gateSlots shape).trans
    ((relocated_slots_eq FrontierEntry1591Field.exit OneFlagExitRaw.hostMulS
      FrontierEntry1591Field.exit_slots).trans (congrArg (fun P : Program => gateSlots P+2448) old))

theorem entry_slots : gateSlots entryKernel≤20502454 := by
  have h := entry_slots_eq
  have old := OwnOneFlagEntryQ7.kernel5S_slots_le
  omega

theorem exit_slots : gateSlots exitKernel≤20502454 := by
  have h := exit_slots_eq
  have old := OwnOneFlagExitQ7.kernelS_slots_le
  omega

theorem first_support : wires firstPhase⊆OB5Support.logicalSites := by
  have n := FrontierEntry1591Native.native_support_logical.1
  have f := NewStackOB5.stackForwardT_subset.trans
    (StackOB5.forward_support.trans OB5Support.integer_sub_logical)
  have c := OB5Support.clear_support_logical
  simpa only [firstPhase,wires_append,Finset.union_subset_iff] using ⟨n,f,c⟩

theorem last_support : wires lastPhase⊆OB5Support.logicalSites := by
  have n := FrontierEntry1591Native.native_support_logical.2
  have r := NewStackOB5.stackReverseT_subset.trans
    (StackOB5.reverse_support.trans OB5Support.integer_sub_logical)
  have c := OB5Support.clear_support_logical
  simpa only [lastPhase,wires_append,Finset.union_subset_iff] using ⟨c,r,n⟩

theorem entry_support : wires entryKernel⊆OB5Support.logicalSites := by
  have f := FrontierEntry1591Native.hosted_support_logical _ first_support
  have r := FrontierEntry1591Native.hosted_support_logical _ last_support
  simpa only [entryKernel,FrontierEntry1591Native.relocated,wires_append,
    Finset.union_subset_iff] using ⟨f,FrontierEntry1591Field.entry_support,r⟩

theorem exit_support : wires exitKernel⊆OB5Support.logicalSites := by
  have f := FrontierEntry1591Native.hosted_support_logical _ first_support
  have r := FrontierEntry1591Native.hosted_support_logical _ last_support
  simpa only [exitKernel,FrontierEntry1591Native.relocated,wires_append,
    Finset.union_subset_iff] using ⟨f,FrontierEntry1591Field.exit_support,r⟩

theorem first_physical : GatePhysical firstPhase := by
  simpa only [firstPhase,gatePhysical_append] using
    And.intro (FrontierEntry1591Native.physical base base_pool_nodup).1
      (And.intro NewStackOB5.stackForwardT_physical mappedClear_physical)

theorem last_physical : GatePhysical lastPhase := by
  simpa only [lastPhase,gatePhysical_append] using
    And.intro mappedClear_physical
      (And.intro NewStackOB5.stackReverseT_physical
        (FrontierEntry1591Native.physical base base_pool_nodup).2)

theorem entry_physical : GatePhysical entryKernel := by
  apply FrontierEntry1591Native.relocated_physical firstPhase FrontierEntry1591Field.entry lastPhase
  simpa only [FrontierEntry1591Native.kernel,gatePhysical_append] using
    And.intro first_physical (And.intro FrontierEntry1591Field.entry_physical last_physical)

theorem exit_physical : GatePhysical exitKernel := by
  apply FrontierEntry1591Native.relocated_physical firstPhase FrontierEntry1591Field.exit lastPhase
  simpa only [FrontierEntry1591Native.kernel,gatePhysical_append] using
    And.intro first_physical (And.intro FrontierEntry1591Field.exit_physical last_physical)

private def phaseOmissions : List Nat := [2312,766,765,767,718,719,720,1797]

private theorem native_sites_free (i : Nat) (hi : i∈phaseOmissions) :
    base i∉FrontierEntry1591Native.sites base := by
  intro h
  simp only [phaseOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  simp only [FrontierEntry1591Native.sites,Finset.mem_erase,Finset.mem_insert,
    List.mem_toFinset,NativeFirstDirect.prefixSites,List.mem_append,wireBlock,
    List.mem_map,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false,
    base_injective.eq_iff] at h
  simp only [exists_eq_right] at h
  have ne : i≠1797 := fun e => h.1 (congrArg base e)
  omega

private theorem integer_sites_free (i : Nat) (hi : i∈phaseOmissions) :
    base i∉OB5.integerSites := by
  intro h
  obtain ⟨j,e,hj⟩ := (OB5.integerSites_mem _).mp h
  have eq := base_injective e
  simp only [phaseOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem clear_free (i : Nat) (hi : i∈phaseOmissions) :
    base i∉wires (skywalkArithmeticClear base) := by
  simp only [phaseOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]

private theorem first_free (i : Nat) (hi : i∈phaseOmissions) : base i∉wires firstPhase := by
  have n := fun h => native_sites_free i hi ((FrontierEntry1591Native.support base base_pool_nodup).1 h)
  have f := fun h => integer_sites_free i hi
    (StackOB5.forward_support (NewStackOB5.stackForwardT_subset h))
  simpa only [firstPhase,wires_append,Finset.mem_union,not_or] using ⟨n,f,clear_free i hi⟩

private theorem last_free (i : Nat) (hi : i∈phaseOmissions) : base i∉wires lastPhase := by
  have n := fun h => native_sites_free i hi ((FrontierEntry1591Native.support base base_pool_nodup).2 h)
  have r := fun h => integer_sites_free i hi
    (StackOB5.reverse_support (NewStackOB5.stackReverseT_subset h))
  simpa only [lastPhase,wires_append,Finset.mem_union,not_or] using ⟨clear_free i hi,r,n⟩

theorem first_host_free (q : Wire) (hq : q∈FrontierEntry1591Native.hostSites) :
    q∉wires firstPhase := by
  simp only [FrontierEntry1591Native.hostSites,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact first_free 718 (by simp [phaseOmissions])
  · exact first_free 719 (by simp [phaseOmissions])
  · exact first_free 720 (by simp [phaseOmissions])

theorem last_host_free (q : Wire) (hq : q∈FrontierEntry1591Native.hostSites) :
    q∉wires lastPhase := by
  simp only [FrontierEntry1591Native.hostSites,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact last_free 718 (by simp [phaseOmissions])
  · exact last_free 719 (by simp [phaseOmissions])
  · exact last_free 720 (by simp [phaseOmissions])

private theorem hosted_free (P : Program) (free : ∀i∈phaseOmissions,base i∉wires P)
    (i : Nat) (hi : i∈logicalOmissions) :
    base i∉wires (FrontierEntry1591Native.hosted P) := by
  have lift (j : Nat) (hj : j∈phaseOmissions)
      (mapped : FrontierEntry1591Native.acceptedSwap (base j)=base i) :
      base i∉wires (FrontierEntry1591Native.hosted P) := by
    intro h
    rw [FrontierEntry1591Native.hosted_support] at h
    obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
    exact free j hj ((FrontierEntry1591Native.acceptedSwap.injective (e.trans mapped.symm)) ▸ hq)
  simp only [logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lift 2312 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 766 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 765 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 767 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 718 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 719 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 720 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 1797 (by simp [phaseOmissions]) (by decide +kernel)

theorem entry_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires entryKernel := by
  simpa only [entryKernel,FrontierEntry1591Native.relocated,wires_append,
    Finset.mem_union,not_or] using
    And.intro (hosted_free firstPhase first_free i hi)
      (And.intro (FrontierEntry1591Field.entry_free i hi) (hosted_free lastPhase last_free i hi))

theorem exit_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires exitKernel := by
  simpa only [exitKernel,FrontierEntry1591Native.relocated,wires_append,
    Finset.mem_union,not_or] using
    And.intro (hosted_free firstPhase first_free i hi)
      (And.intro (FrontierEntry1591Field.exit_free i hi) (hosted_free lastPhase last_free i hi))

end ECDSAAdd.Entrant.FrontierEntry1591Kernel

end

-- Public component FrontierEntry1591Kernel.lean
section
attribute [local irreducible] ECDSAAdd.Entrant.FrontierEntry1591Field.entry ECDSAAdd.Entrant.FrontierEntry1591Field.exit ECDSAAdd.regValue ECDSAAdd.Arithmetic.wireBlock
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
  FrontierEntry1591Callers
attribute [local irreducible] run wires firstPhase lastPhase rawEntry rawExit entryKernel exitKernel
  NewStackOB5.stackForwardT FrontierEntry1591Native.forward

private theorem compose_recordsPrepared (N F C First : Program)
    (shape : First=N++(F++C)) (s : State) (m : List Bool) (P : State → Prop)
    (step : ∀mn mf mc,P (run C mc (run F mf (run N mn s)))) :
    P (run First m s) := by
  rw [shape,run_append,run_append]
  exact step _ _ _
theorem first_prepared (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis) :
    ∃origin : State,PreparationFacts x Y s origin ∧ History5.RawLegal base 102 origin.basis ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 (run firstPhase m s) := by
  refine compose_recordsPrepared (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT
    (skywalkArithmeticClear base) firstPhase (by unfold firstPhase;rfl) s m
    (fun out => ∃origin : State,PreparationFacts x Y s origin ∧ History5.RawLegal base 102 origin.basis ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 out) ?_
  intro mn mf mc
  exact preparation_placed hn hlo ho x Y hx0 hx s mn mf mc input


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

private theorem close_boundary (F : Program) (m : List Bool) (st : State) (value : Nat)
    (h : (run F m st).phase=st.phase ∧
      regValue FrontierEntry1591Field.numerator (run F m st).basis=value ∧
      ∀q,q∉FrontierEntry1591Field.numerator → (run F m st).basis q=st.basis q) :
    let before := st
    let after := run F m before
    after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q := by
  simpa only [FrontierEntry1591Field.numerator] using h

private theorem entry_boundary_result (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (virtual actual : State) (m : List Bool)
    (frame : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 virtual)
    (phase : actual.phase=virtual.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → actual.basis q=virtual.basis q)
    (half : regValue (wireBlock base 2056 256) actual.basis=centerWord (Y/2))
    (code : actual.basis (base 511)=true) (high : actual.basis (base 1542)=false)
    (work : actual.basis (base 1797)=false)
    (parity : actual.basis (base 1543)=TraceParity5.parity (payloadControls.map actual.basis)) :
    let before := actual
    let after := run FrontierEntry1591Field.entry m before
    after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=(Y/(x:Fp)).val ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q := by
  have sameTyped : ∀q,q∉FrontierEntry1591Field.numerator → actual.basis q=virtual.basis q := by
    simpa only [FrontierEntry1591Field.numerator] using same
  have targetTyped : regValue FrontierEntry1591Field.numerator actual.basis=centerWord (Y/2) := by
    simpa only [FrontierEntry1591Field.numerator] using half
  have workTyped : actual.basis FrontierEntry1591Field.work=false := by
    simpa only [FrontierEntry1591Field.work] using work
  have parityTyped : actual.basis FrontierEntry1591Field.host=
      TraceParity5.parity (FrontierEntry1591Field.controls.map actual.basis) := by
    simpa only [FrontierEntry1591Field.host,FrontierEntry1591Field.controls,payloadControls] using parity
  exact close_boundary FrontierEntry1591Field.entry m actual (Y/(x:Fp)).val
    (FrontierEntry1591Field.entry_result origin ctx ha x hx0 hx trace Y virtual actual m frame phase
      sameTyped targetTyped code high workTyped parityTyped)

theorem entry_boundary (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (mp mf : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg : s.basis (base 2409)=false) (hs : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (half : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let before : State := run firstPhase mp t
    let after : State := run FrontierEntry1591Field.entry mf before
    after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=(Y/(x:Fp)).val ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q := by
  have paired := EntryFuse.pool_transport firstPhase first_pool s t mp phase.symm
    (fun q hq => (same q hq).symm)
  have paired' : (run firstPhase mp s).phase=(run firstPhase mp t).phase ∧
      (∀q,q∉wireBlock base 2056 256 → (run firstPhase mp s).basis q=(run firstPhase mp t).basis q) ∧
      (∀q,q∈wireBlock base 2056 256 → (run firstPhase mp t).basis q=t.basis q) :=
    ⟨paired.1,paired.2.1,fun q hq => (paired.2.2 q hq).2⟩
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
  exact entry_boundary_result origin.basis ctx facts.sourceZero x hx0 hx facts.trace Y
    (run firstPhase mp s) (run firstPhase mp t) mf frame paired'.1.symm
    (fun q hq => (paired'.2.1 q hq).symm) target code high
    (first_work_zero hn x _ t mp actualInput) parity

private theorem exit_boundary_result (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (actual : State) (m : List Bool)
    (frame : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 actual)
    (code : actual.basis (base 511)=true) (high : actual.basis (base 1542)=false)
    (work : actual.basis (base 1797)=false)
    (parity : actual.basis (base 1543)=TraceParity5.parity (payloadControls.map actual.basis)) :
    let before := actual
    let after := run FrontierEntry1591Field.exit m before
    after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=centerWord (Y*(x:Fp)/2) ∧
      ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q := by
  have workTyped : actual.basis FrontierEntry1591Field.work=false := by
    simpa only [FrontierEntry1591Field.work] using work
  have parityTyped : actual.basis FrontierEntry1591Field.host=
      TraceParity5.parity (FrontierEntry1591Field.controls.map actual.basis) := by
    simpa only [FrontierEntry1591Field.host,FrontierEntry1591Field.controls,payloadControls] using parity
  exact close_boundary FrontierEntry1591Field.exit m actual (centerWord (Y*(x:Fp)/2))
    (FrontierEntry1591Field.exit_result origin ctx ha x hx0 hx trace Y actual m frame code high
      workTyped parityTyped)

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
  exact exit_boundary_result origin.basis ctx facts.sourceZero x hx0 hx facts.trace Y
    (run firstPhase mp s) mf frame
    (prepared511 origin.basis Y _ frame (trace_last x hx0 hx origin.basis facts.trace))
    (bits _ (by simp [FrontierEntry1591Native.workSites]))
    (first_work_zero hn x Y.val s mp input) (first_parity hn hlo x Y.val hx0 hx s mp input)

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

private theorem result_congr (P Q : Program) (m : List Bool) (initial reference : State)
    (r : List Wire) (value : Nat) (eq : run P m initial=run Q m initial)
    (h : let out := run Q m initial
      out.phase=reference.phase ∧ regValue r out.basis=value ∧
        ∀q,q∉r → out.basis q=reference.basis q) :
    let out := run P m initial
    out.phase=reference.phase ∧ regValue r out.basis=value ∧
      ∀q,q∉r → out.basis q=reference.basis q := by
  simpa only [eq] using h

private theorem hosted_result (First F Last : Program) (initial reference : State) (m : List Bool)
    (r : List Wire) (value : Nat)
    (input : ∀q∈FrontierEntry1591Native.workSites∪FrontierEntry1591Native.hostSites,initial.basis q=false)
    (firstFree : ∀q∈FrontierEntry1591Native.hostSites,q∉wires First)
    (firstClean : ∀q∈FrontierEntry1591Native.workSites,
      (run First (m.take (measurementCount First)) initial).basis q=false)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (lastFree : ∀q∈FrontierEntry1591Native.hostSites,q∉wires Last)
    (away : ∀q,q∈FrontierEntry1591Native.workSites∪FrontierEntry1591Native.hostSites → q∉r)
    (referenceClean : ∀q∈FrontierEntry1591Native.workSites∪FrontierEntry1591Native.hostSites,reference.basis q=false)
    (result : let out := run (FrontierEntry1591Native.kernel First F Last) m initial
      out.phase=reference.phase ∧ regValue r out.basis=value ∧ ∀q,q∉r → out.basis q=reference.basis q) :
    let out := run (FrontierEntry1591Native.relocated First F Last) m initial
    out.phase=reference.phase ∧ regValue r out.basis=value ∧ ∀q,q∉r → out.basis q=reference.basis q := by
  have output : ∀q∈FrontierEntry1591Native.workSites∪FrontierEntry1591Native.hostSites,
      (run (FrontierEntry1591Native.kernel First F Last) m initial).basis q=false := by
    intro q hq
    exact (result.2.2 q (away q hq)).trans (referenceClean q hq)
  have eq := FrontierEntry1591Native.hosted_kernel_run_eq First F Last initial m input firstFree
    firstClean fieldFree lastFree output
  exact result_congr _ _ m initial reference r value eq result

theorem entry_correct : EntryCorrect entryKernel := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  unfold entryKernel
  have actualInput := paired_input x Y.val s t input same
  exact hosted_result firstPhase FrontierEntry1591Field.entry lastPhase t s m
    (wireBlock base 2056 256) (skywalkArithmeticResult true x Y).val
    (FrontierEntry1591Native.caller_clean_sites_paired x Y.val s t input same)
    first_host_free (first_clean hn x _ hx0 hx t _ actualInput)
    (field_work_free _ FrontierEntry1591Field.entry_free) last_host_free away_work_host
    (FrontierEntry1591Native.caller_clean_sites x Y.val s input)
    (by simpa only [rawEntry] using
      (raw_entry_correct hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half))

theorem exit_correct : ExitCorrect exitKernel := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  unfold exitKernel
  exact hosted_result firstPhase FrontierEntry1591Field.exit lastPhase s s m
    (skywalkArithmeticNumerator base) (centerWord (Y*(x:Fp)/2))
    (FrontierEntry1591Native.caller_clean_sites x Y.val s input)
    first_host_free (first_clean hn x Y.val hx0 hx s _ input)
    (field_work_free _ FrontierEntry1591Field.exit_free) last_host_free away_work_host
    (FrontierEntry1591Native.caller_clean_sites x Y.val s input)
    (by simpa only [rawExit] using
      (raw_exit_correct hn hlo ho hf x Y hx0 hx s m input hg hs))

end ECDSAAdd.Entrant.FrontierEntry1591Kernel

end

-- Public component PrefixFrontierSquare1591.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace ECDSAAdd.Entrant.PrefixFrontierSquare1591
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

private theorem resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial_spare_free (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    L.core.poolWire 1539∉wires (OwnDiagAll12Placed.initial L) := by
  rw [OwnDiagAll12Placed.initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnDiagAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=resident_away L hn L.core.generic
      (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · have away:=resident_away L hn old
      (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · have away:=resident_away L hn old
      (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1539
      (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1539
      (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem pool_swap_fix (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (a b n : Nat)
    (ha : a<2613) (hb : b<2613) (hnn : n<2613) (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b))
      (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1539∉wires (OwnDiagAll12PlacedQ7.program L) := by
  have p0:=initial_spare_free L hw hn
  have p1 : L.core.poolWire 1539∉wires (OwnDiagAll12Placed.plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 766 1530 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1539∉wires (OwnDiagAll12Placed.guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 765 1531 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1539∉wires (OwnDiagAll12Placed.minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 767 1532 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1539∉wires (OwnDiagAll12Placed.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 770 1536 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  have p5 : L.core.poolWire 1539∉wires (OwnDiagAll12PlacedQ6.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 1285 1537 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p4
  exact OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 1286 1538 1539
    (by omega) (by omega) (by omega) (by omega) (by omega)) p5

def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)

def program (L : ControlledPointLayout) : Program :=
  renameProgram (swap L) (OwnDiagAll12PlacedQ7.program L)
attribute [local irreducible] program

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 769
  · subst q
    simpa only [swap,Equiv.swap_apply_left] using
      Square5Placement.pool_member L hw 1539 (by omega)
  · by_cases b:q=L.core.poolWire 1539
    · subst q
      simpa only [swap,Equiv.swap_apply_right] using
        Square5Placement.pool_member L hw 769 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 769:=fun e=>
    hq (e.symm ▸ Square5Placement.pool_member L hw 769 (by omega))
  have b:q≠L.core.poolWire 1539:=fun e=>
    hq (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b

theorem run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (hin : regValue L.dialogPool s.basis=0)
    (hout : regValue L.dialogPool (run P m s).basis=0) :
    run (renameProgram (swap L) P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L (swap L) (pool L hw) (outside L hw)
    P s m hin hout

theorem program_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Fp) (G : Bool) (origin : BasisState)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (OwnDiagAll12PlacedQ7.program L) m s := by
  have old:=OwnDiagAll12PlacedQ7.correct L hw hn X Y G origin s m v
  unfold program
  exact run_eq L hw _ s m v.clean old.2.clean

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    OwnDiagAll12Placed.SquareCorrect L (program L) := by
  unfold program
  exact OwnDiagAll12Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (OwnDiagAll12PlacedQ7.correct L hw hn)

theorem counts (L : ControlledPointLayout) :
    toffoliCount (program L)=toffoliCount (OwnDiagAll12PlacedQ7.program L) ∧
    measurementCount (program L)=measurementCount (OwnDiagAll12PlacedQ7.program L) := by
  unfold program
  exact renameProgram_counts (swap L) _

theorem slots_eq (L : ControlledPointLayout) :
    Challenge.gateSlots (program L)=
      Challenge.gateSlots (OwnDiagAll12PlacedQ7.program L) := by
  unfold program
  exact Baselines.rename_gateSlots _ _

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 :=
  (slots_eq L).le.trans (OwnDiagAll12PlacedQ7.slots L hw)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  unfold program
  exact gatePhysical_rename (swap L) (swap L).injective _
    (OwnDiagAll12PlacedQ7.physical L hw hn)

theorem support_eq (L : ControlledPointLayout) :
    wires (program L)=(wires (OwnDiagAll12PlacedQ7.program L)).image (swap L) := by
  unfold program
  exact renameProgram_support _ _

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset := by
  unfold program swap
  exact OwnDiagAll12Placed.swap_support _ _ _ _ (OwnDiagAll12PlacedQ7.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 769
      (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1539
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 769∉wires (program L) := by
  unfold program swap
  exact OwnDiagAll12Placed.swap_target_free _ _ _ (spare_free L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769]) :
    L.core.poolWire k∉wires (program L) := by
  by_cases h:k=769
  · subst k;exact retired_free L hw hn
  have hkold : k∈[1800,766,765,767,770,1285,1286] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    omega
  have f : swap L (L.core.poolWire k)=L.core.poolWire k :=
    pool_swap_fix L hw hn 769 1539 k (by omega) (by omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega) h
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega)
  unfold program
  exact OwnPlusHost.rename_avoid _ _ _ f (OwnDiagAll12PlacedQ7.square_free L hw hn k hkold)

end ECDSAAdd.Entrant.PrefixFrontierSquare1591

end

-- Public component FrontierEntry1591Point.lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Point
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Callers
attribute [local irreducible] wires run toffoliCount measurementCount

def gen (K E : Program) (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.gen L (division K L) (PrefixFrontierSquare1591.program L) (exit E L) cx cy OwnDiagAll12Square.sqOff

theorem square_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (PrefixFrontierSquare1591.program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (OwnDiagAll12Square.sqOff:Nat) else 0)) Y G origin) := by
  have h := PrefixFrontierSquare1591.correct L hw hn X Y G origin
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h

theorem ok (K E : Program) (ks : wires K⊆OB5Support.logicalSites)
    (es : wires E⊆OB5Support.logicalSites) (kc : EntryCorrect K) (ec : ExitCorrect E)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen K E L cx cy) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  exact All12Generic.genFFused_ok L hw hn _ _ _ (exit_correct E es ec L hw hn)
    (division_step K ks kc L hw hn config.1 above config.2.1 config.2.2)
    (square_step L hw hn) hc

theorem sites (K E : Program) (ks : wires K⊆OB5Support.logicalSites)
    (es : wires E⊆OB5Support.logicalSites) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (gen K E L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  Q1591Resources.gen_sites L hw hn _ _ _ (division_support K ks L hw)
    (PrefixFrontierSquare1591.support L hw hn) (exit_support E es L hw) cx cy

theorem physical (K E : Program) (ks : wires K⊆OB5Support.logicalSites)
    (es : wires E⊆OB5Support.logicalSites) (kp : GatePhysical K) (ep : GatePhysical E)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (gen K E L cx cy) :=
  Q1591Resources.gen_physical L hw hn _ _ _ (division_physical K ks kp L hw hn)
    (PrefixFrontierSquare1591.physical L hw hn) (placed_physical E es ep L hw hn) cx cy

theorem counts_eq (K E : Program)
    (kc : toffoliCount K=toffoliCount OwnOneFlagEntryQ7.kernel5S ∧
      measurementCount K=measurementCount OwnOneFlagEntryQ7.kernel5S)
    (ec : toffoliCount E=toffoliCount OwnOneFlagExitQ7.kernelS ∧
      measurementCount E=measurementCount OwnOneFlagExitQ7.kernelS)
    (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen K E L cx cy)=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
      measurementCount (gen K E L cx cy)=measurementCount (OwnOneFlagActual.gen L cx cy) :=
  Q1591Resources.gen_counts_eq L _ _ _ (division_counts_eq K kc L)
    (PrefixFrontierSquare1591.counts L) (exit_counts_eq E ec L) cx cy

theorem slots (K E : Program) (ks : gateSlots K≤20502454) (es : gateSlots E≤20502454)
    (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (gen K E L cx cy)≤49204896 :=
  Q1591Resources.gen_slots L hw _ _ _ (division_slots K ks L hw)
    (PrefixFrontierSquare1591.slots L hw) (exit_slots E es L) cx cy

theorem qubits (K E : Program) (ks : wires K⊆OB5Support.logicalSites)
    (es : wires E⊆OB5Support.logicalSites)
    (kf : ∀i∈logicalOmissions,base i∉wires K)
    (ef : ∀i∈logicalOmissions,base i∉wires E) (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen K E layout cx cy))≤1591 :=
  Q1591Resources.gen_qubits _ _ _ (division_support K ks layout layout_widths)
    (PrefixFrontierSquare1591.support layout layout_widths layout_nodup)
    (exit_support E es layout layout_widths)
    (division_free K ks kf layout layout_widths layout_nodup)
    (PrefixFrontierSquare1591.square_free layout layout_widths layout_nodup)
    (placed_omissions E es ef layout layout_widths layout_nodup) C cx cy

end ECDSAAdd.Entrant.FrontierEntry1591Point

end

-- Public component FrontierEntry1591Actual.lean
section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Entrant.OwnParity1591Actual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Kernel

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  FrontierEntry1591Point.gen entryKernel exitKernel L cx cy

theorem sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  FrontierEntry1591Point.sites entryKernel exitKernel entry_support exit_support L hw hn cx cy

theorem ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) :=
  FrontierEntry1591Point.ok entryKernel exitKernel entry_support exit_support
    entry_correct exit_correct L hw hn hc

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (gen L cx cy) :=
  FrontierEntry1591Point.physical entryKernel exitKernel entry_support exit_support
    entry_physical exit_physical L hw hn cx cy

theorem counts_eq (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen L cx cy)=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
      measurementCount (gen L cx cy)=measurementCount (OwnOneFlagActual.gen L cx cy) :=
  FrontierEntry1591Point.counts_eq entryKernel exitKernel entry_counts_eq exit_counts_eq L cx cy

theorem slots (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (gen L cx cy)≤49204896 :=
  FrontierEntry1591Point.slots entryKernel exitKernel entry_slots exit_slots L hw cx cy

theorem qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1591 :=
  FrontierEntry1591Point.qubits entryKernel exitKernel entry_support exit_support
    entry_free exit_free C cx cy

end ECDSAAdd.Entrant.OwnParity1591Actual

end
