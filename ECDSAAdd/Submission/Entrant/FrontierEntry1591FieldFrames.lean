import ECDSAAdd.Submission.Entrant.FrontierEntry1591Field
import ECDSAAdd.Submission.Entrant.FrontierEntry1591FieldControl

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
