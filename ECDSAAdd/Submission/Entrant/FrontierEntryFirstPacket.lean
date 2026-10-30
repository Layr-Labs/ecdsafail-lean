import ECDSAAdd.Submission.Entrant.FrontierEntryJointFrame
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstProgram
import ECDSAAdd.Submission.Entrant.FrontierEntry1593Support

/-! The source-zero entry frame, followed by the unchanged first-packet tail. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed CompressedFieldSupport Secp256k1
attribute [local irreducible] run mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

private theorem work_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r ∧ q∉L.y := by
  have nd := BalancedCircuit.allND L hn
  have h := List.nodup_iff_count.mp nd q
  have w := List.count_pos_iff.mpr hq
  constructor <;> intro hd <;> have d := List.count_pos_iff.mpr hd
  all_goals
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h w
    omega

private theorem joint_pair (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (hj : J∉L.r ∧ J∉L.y) (hg : G∉L.r ∧ G∉L.y)
    (origin : BasisState) (hc : ∀q∈BalancedCircuit.work L,origin q=false)
    (hs : origin L.sign=false) (Z : Fp) :
    Triple (PairFrame L.r L.y origin (centerWord Z) 0) (joint L J G)
      (PairFrame L.r L.y origin
        (encodeWord 256 (halfResult (signedY (origin J && !origin G) (centerFp Z))))
        (encodeWord 256 (if origin J then centerFp Z else 0))) := by
  intro s m h
  have sign_away : L.sign∉L.r ∧ L.sign∉L.y := by
    have f := BalancedCircuit.flagAway L hn L.sign (by simp)
    exact ⟨fun a=>f (by simp only [List.mem_append];tauto),
      fun a=>f (by simp only [List.mem_append];tauto)⟩
  have clean : ∀q∈BalancedCircuit.work L,s.basis q=false := by
    intro q hq
    have away := work_away L hn q hq
    exact (h.2.2 q away.1 away.2).trans (hc q hq)
  have out := joint_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m h.1 h.2.1 clean
    ((h.2.2 _ sign_away.1 sign_away.2).trans hs)
    (h.2.2 _ hj.1 hj.2) (h.2.2 _ hg.1 hg.2)
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩

private theorem unary_half (b : Bool) (Z : Fp) :
    halfResult (signedY b (centerFp Z))=centerFp ((if b then -Z else Z)/2) := by
  have h:=signedY_bounds b (centerFp Z) (centerFp_bounds Z)
  have q0 : 0≤BalancedField.q := (BalancedField.constants).1.le
  have bounds : -(2*BalancedField.q)≤signedY b (centerFp Z) ∧
      signedY b (centerFp Z)≤2*BalancedField.q := by
    unfold Centered at h
    omega
  have hh:=halfResult_center _ bounds
  cases b <;> simpa only [signedY,Bool.false_eq_true,if_false,if_true,Int.cast_neg,centerFp_cast] using hh

private theorem source_word (b : Bool) (Z : Fp) :
    encodeWord 256 (if b then centerFp Z else 0)=centerWord (if b then Z else 0) := by
  cases b
  · simp only [Bool.false_eq_true,if_false,HalfField.centerWord_zero]
    rfl
  · rfl

private theorem enable_frame {k : Nat} {P Q : Program} (h : SW.Sel (base 2400) k P Q)
    (origin : BasisState) (hb : origin (base 2400)=true)
    (away : base 2400∉ports.r ∧ base 2400∉ports.y) (I J X Y : Nat)
    (hq : Triple (PairFrame ports.r ports.y origin I J) Q (PairFrame ports.r ports.y origin X Y)) :
    Triple (PairFrame ports.r ports.y origin I J) P (PairFrame ports.r ports.y origin X Y) := by
  intro s m hs
  rw [(h.eq m s ((hs.2.2 _ away.1 away.2).trans hb)).1]
  exact hq s m hs

private theorem letters_layout (origin : BasisState) (ctx : OneBankReplay5.Context origin)
    (ls : List MixedTranscriptLetter)
    (hl : ∀l∈ls,∃i,i<510 ∧ l=tapeLetter i) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls := by
  intro l h
  obtain ⟨i,hi,rfl⟩:=hl l h
  simpa only [tapeLetter] using mixedTape_getD_layout base _ _ _ ctx.hf i (by omega)

private theorem first_payload_split (origin : BasisState) (hb : origin (base 2400)=true) (Z : Fp) :
    Replay5.firstPayload true origin (Z,0)=
      directionalPayload false (mixedTranscriptControls origin (base 2400) remainingLetters)
        (skywalkPayloadCell (origin (base 1)) (origin (base 1029))
          (if origin (base 1028) then (0,Z) else (Z,0))) := by
  have rest : Replay5.restLetters=tapeLetter 1::remainingLetters := rfl
  simp only [Replay5.firstPayload,if_true,rest,mixedTranscriptControls,List.map_cons,
    directionalPayload,Bool.false_eq_true,if_false,skywalkPayloadReplay]
  simp only [tapeLetter,mixedTape_base_getD 1 (by decide),mixedTranscriptBit,hb,if_true]

/-- Joint initial copy/half, then the unchanged S1 swap and cells2..4. -/
theorem firstBody_frame (origin : BasisState) (ctx : OneBankReplay5.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) :
    Triple (PairFrame ports.r ports.y origin (centerWord Z) 0) firstBody
      (PairFrame ports.r ports.y origin
        (centerWord (Replay5.firstPayload true origin (Z,0)).1)
        (centerWord (Replay5.firstPayload true origin (Z,0)).2)) := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 1 (by decide)) ctx.ho
  rw [mixedTape_base_getD 1 (by decide)] at layout
  have newLayout := OneBankCell5.ports_transcript base (base 2400) (base 1) (base 1029)
    (base 2409) (base 2410) ctx.hn layout (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have hn := newLayout.kernel
  have hw := newLayout.widths
  have hJ : base 1028∉ports.wires := by decide
  have hG : base 1∉ports.wires := by decide
  have outside (q : Wire) (hq : q∉ports.wires) : q∉ports.r ∧ q∉ports.y := by
    constructor <;> intro h <;> apply hq
    · exact EntryRetained5.data_member ports q (by simp [h])
    · exact EntryRetained5.data_member ports q (by simp [h])
  have away : base 2400∉ports.r ∧ base 2400∉ports.y := newLayout.outside _ (by simp)
  have clean := OneBankCell5.clean_of_env_work base (base 2409) origin ctx.env ctx.parity
  have hjoint := joint_pair ports hw hn _ _ hJ hG (by decide) (outside _ hJ) (outside _ hG)
    origin clean ctx.hg0 Z
  let J:=origin (base 1028)
  let G:=origin (base 1)
  let S:=origin (base 1029)
  let A:Fp := (if J && !G then -Z else Z)/2
  let B:Fp := if J then Z else 0
  have jfOld : Triple (PairFrame ports.r ports.y origin (centerWord Z) 0)
      (joint ports (base 1028) (base 1)) (PairFrame ports.r ports.y origin (centerWord A) (centerWord B)) := by
    rw [unary_half,source_word] at hjoint
    exact hjoint
  have jf : Triple (PairFrame ports.r ports.y origin (centerWord Z) 0) joint1593
      (PairFrame ports.r ports.y origin (centerWord A) (centerWord B)) := by
    intro state records input
    rw [joint1593_eq origin ctx Z state records input]
    exact jfOld state records input
  have swap := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 1) (base 1029)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 1 (false,false)).2
    layout origin ctx.hs0 A B
  have sel := ((SW.Sel.refl (base 2400) SW.swapBody SW.selSwap_away).window (base 1029) (base 2410)
    (mixedTranscriptUnitTrace.getD 1 (false,false)).2 (by decide))
  have sf := enable_frame sel origin hb away (centerWord A) (centerWord B)
    (centerWord (if S then B else A)) (centerWord (if S then A else B)) (by
      simpa only [EntryFieldSeedCancellation.selectedSwap,mixedTranscriptBit,hb,if_true,S] using swap)
  have lsf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) remainingLetters :=
    letters_layout origin ctx _ (by
      intro l hl
      obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hl
      exact ⟨i,by have := List.mem_range'_1.mp hi;omega,rfl⟩)
  have rf := OneBankReplay5.raw_frame true remainingLetters lsf origin ctx (if S then B else A) (if S then A else B)
  have rs := SW.selRaw_sel true remainingLetters (by
    intro l hl
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hl
    exact SW.selLetter_nodup i (by have := List.mem_range'_1.mp hi;omega))
  have tail := enable_frame rs origin hb away _ _ _ _ rf
  have all := (jf.seq sf).seq tail
  have cell : (if S then B else A,if S then A else B)=
      skywalkPayloadCell G S (if J then (0,Z) else (Z,0)) := by
    cases eJ:J <;> cases eG:G <;> cases eS:S <;>
      simp [A,B,skywalkPayloadCell,eJ,eG,eS]
  rw [first_payload_split origin hb Z]
  simpa only [firstBody,List.append_assoc,cell,J,G,S] using all

/-- Codec records, entry records and tail records remain independent. -/
theorem firstPacket_frame (origin : BasisState) (ctx : OneBankReplay5.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (support : wires firstBody⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312})
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    (run firstPacket m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin
        (Replay5.firstPayload true origin (Z,0)).1 (Replay5.firstPayload true origin (Z,0)).2
        (run firstPacket m s) := by
  have body : Triple
      (PairFrame ports.r ports.y origin (centerWord Z) (centerWord (0:Fp))) firstBody
      (PairFrame ports.r ports.y origin
        (centerWord (Replay5.firstPayload true origin (Z,0)).1)
        (centerWord (Replay5.firstPayload true origin (Z,0)).2)) := by
    simpa only [HalfField.centerWord_zero] using firstBody_frame origin ctx hb Z
  have fresh := FieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp 0 (by decide) origin Z 0 _ _ _ support body s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi 0) baseFirstPacket
    (fun q hq=>Placement5.pi_outside 0 q (by decide) hq) s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal Z 0 s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run firstPacket m s=run baseFirstPacket m s := eq
  rw [same]
  exact fresh

end ECDSAAdd.Entrant.FrontierEntry
