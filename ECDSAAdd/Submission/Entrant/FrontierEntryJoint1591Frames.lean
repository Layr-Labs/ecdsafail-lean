import ECDSAAdd.Submission.Entrant.FrontierEntryJoint1591Program
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstPacket
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstSupport
import ECDSAAdd.Submission.Entrant.FrontierEntry1591FieldFrames

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntryJoint1591
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires

theorem firstTrit_of_trace (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (x : Nat) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    FrontierEntry.FirstTrit origin := by
  let oldCtx : OneFlagReplay.Context origin :=
    ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,ctx.hg0,ctx.hs0,ctx.env,ctx.legal,ctx.parity⟩
  refine ⟨FrontierEntry.firstLegal_of_context origin oldCtx,?_⟩
  have read : (skywalkTapeControls origin (skywalkSharedTape base)).getD 0 (false,false)=
      (origin (base 0),origin (base 1028)) := by
    simp [skywalkTapeControls,skywalkSharedTape]
  have head : (origin (base 0),origin (base 1028))=
      SkywalkTrace.code (SkywalkRails.encode false false (x:Int) (p:Int)) := by
    rw [←read,trace]
    rfl
  have nonzero := FirstNonzero.initial_code_nonzero x p (by norm_num [p]) (by norm_num [p]) hx
  have equal := congrArg (fun pair : Bool×Bool => pair.1 || pair.2) head
  simpa only [Bool.or_eq_true] using equal.trans nonzero

theorem firstBody_read_support : wires FrontierEntry.firstBody⊆
    NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} := by
  rw [NewHistory5.groupReadSites_eq]
  exact FrontierEntry.firstBody_read_support

theorem firstPacket_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (x : Nat) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (enabled : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    (run firstPacket m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin
        (Replay5.firstPayload true origin (Z,0)).1 (Replay5.firstPayload true origin (Z,0)).2
        (run firstPacket m s) := by
  let oldCtx : OneFlagReplay.Context origin :=
    ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,ctx.hg0,ctx.hs0,ctx.env,ctx.legal,ctx.parity⟩
  have body : Triple
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
        origin (centerWord Z) (centerWord (0:Fp))) FrontierEntry.firstBody
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
        origin (centerWord (Replay5.firstPayload true origin (Z,0)).1)
        (centerWord (Replay5.firstPayload true origin (Z,0)).2)) := by
    simpa only [FrontierEntry.ports_r,FrontierEntry.ports_y,HalfField.centerWord_zero] using
      FrontierEntry.firstBody_frame origin oldCtx enabled (firstTrit_of_trace origin ctx x hx trace) Z
  have fresh := NewFieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp 0 (by decide) origin Z 0 _ _ _ firstBody_read_support body s m input ctx.legal
  have placed := Replay5.placed_eq (Placement5.pi 0) baseFirstPacket
    (fun q hq => Placement5.pi_outside 0 q (by decide) hq) s m
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp))
      origin ctx.env ctx.legal Z 0 s input)
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp))
      origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run firstPacket m s=run baseFirstPacket m s := placed
  rw [same]
  exact fresh

theorem logical_control (origin : BasisState) (X Y : Fp) (s : State)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    s.basis (base 2400)=origin (base 2400) := by
  obtain ⟨raw,_,frame,encoded⟩ := input
  have rawControl : raw.basis (base 2400)=origin (base 2400) := by
    apply frame.2.2
    · rw [balancedSharedPorts_r]
      exact OwnPlusHost.not_block 2400 2056 256 (by omega)
    · rw [balancedSharedPorts_y]
      exact OwnPlusHost.not_block 2400 770 256 (by omega)
  rw [encoded]
  exact (run_preserves_outside _ [] raw _
    (FrontierEntry1591Field.encoder_special_away 2400 (by simp))).trans rawControl

theorem groups_frame (j n : Nat) (bound : j+n≤102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (FrontierSW1591.groupsS true j n) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin
        (Replay5.groupsPayload true origin j n (X,Y)).1
        (Replay5.groupsPayload true origin j n (X,Y)).2
        (run (FrontierSW1591.groupsS true j n) m s) := by
  have same := ((FrontierSW1591.selGroups_sel true j n bound).eq m s
    ((logical_control origin X Y s input).trans enabled)).1
  rw [same]
  exact FrontierReplay1591.groups_frame true j n bound origin ctx X Y s m input

theorem endPacket_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp)
    (hend : (Replay5.endPayload true origin (X,Y)).1=Y) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (FrontierSW1591.endPacketS true) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin
        (Replay5.endPayload true origin (X,Y)).1 (Replay5.endPayload true origin (X,Y)).2
        (run (FrontierSW1591.endPacketS true) m s) := by
  have same := ((FrontierSW1591.selEnd_sel true).eq m s
    ((logical_control origin X Y s input).trans enabled)).1
  rw [same]
  exact FrontierReplay1591.endPacket_frame true origin ctx X Y (fun _ => hend) s m input

attribute [local irreducible] Replay5.groupsPayload Replay5.firstPayload Replay5.endPayload
  mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

theorem logical_forward_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (enabled : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    (run logicalReplay m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Z/(x:Fp)) (Z/(x:Fp))
        (run logicalReplay m s) := by
  have result := run_three_states firstPacket (FrontierSW1591.groupsS true 1 101)
    (FrontierSW1591.endPacketS true)
    (fun a d => NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z 0 a →
      d.phase=a.phase ∧ NewHistory5.EncodedFieldFrame5 base (base 2409) origin
        (Z/(x:Fp)) (Z/(x:Fp)) d) (by
      intro a b c d m1 m2 m3 h1 h2 h3 hin
      have first := firstPacket_frame origin ctx x hx trace enabled Z a m1 hin
      rw [h1] at first
      have middle := groups_frame 1 101 (by decide) origin ctx enabled _ _ b m2 first.2
      rw [h2] at middle
      have fp := Replay5.forward_payload origin x Z hx0 hx trace
      have last := endPacket_frame origin ctx enabled _ _ (by
        rw [Prod.mk.eta,fp]
        exact (congrArg Prod.snd fp).symm.trans (by simp only [Replay5.endPayload])) c m3 middle.2
      rw [h3] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.forward_payload origin x Z hx0 hx trace,
        enabled,if_true] using last.2) s m
  simpa only [logicalReplay,List.append_assoc] using result input

theorem forward_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (enabled : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    (run replay m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin (Z/(x:Fp)) (Z/(x:Fp)) (run replay m s) :=
  NewFieldFrameOB5.placed_step logicalReplay origin Z 0 _ _
    (logical_forward_frame origin ctx x hx0 hx trace enabled Z) s m input

theorem entryField_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (enabled : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    (run entryField m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin (2*(Z/(x:Fp))) 0 (run entryField m s) := by
  have result := run_three_states replay HalfFieldOB5.copyN OwnQ5Endpoint.canonT
    (fun a d => NewFieldFrameOB5.EncodedFieldFrame origin Z 0 a →
      d.phase=a.phase ∧ NewFieldFrameOB5.EncodedCanonicalFrame origin (2*(Z/(x:Fp))) 0 d) (by
      intro a b c d m1 m2 m3 h1 h2 h3 hin
      have first := forward_frame origin ctx x hx0 hx trace enabled Z a m1 hin
      rw [h1] at first
      have middle := NewHalfFieldOB5.copy_clear ctx.hn origin (Z/(x:Fp)) b m2 first.2
      rw [h2] at middle
      have last := NewOwnQ5Endpoint.canon_frame ctx.hn (ctx.hp _ (by simp)) origin
        ctx.env ctx.legal ctx.parity ha (Z/(x:Fp)) c m3 middle.2
      change (run OwnQ5Endpoint.canonT m3 c).phase=c.phase ∧
        NewFieldFrameOB5.EncodedCanonicalFrame origin (2*(Z/(x:Fp))) 0
          (run OwnQ5Endpoint.canonT m3 c) at last
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m
  exact result input

end ECDSAAdd.Entrant.FrontierEntryJoint1591
