import ECDSAAdd.Submission.Entrant.FrontierEntryJointFrame
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstProgram
import ECDSAAdd.Submission.Entrant.FrontierEntry1592Support

/-! The source-zero entry frame, followed by the unchanged first-packet tail. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed CompressedFieldSupport Secp256k1
attribute [local irreducible] run mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

/-- Exact caller facts for the first raw G/S pair. -/
def FirstTrit (origin : BasisState) : Prop :=
  (origin (base 0)).toNat+2*(origin (base 1028)).toNat<3 ∧
    (origin (base 0)=true ∨ origin (base 1028)=true)

theorem firstLegal_of_context (origin : BasisState) (ctx : OneFlagReplay.Context origin) :
    (origin (base 0)).toNat+2*(origin (base 1028)).toNat<3 :=
  (ctx.legal 0 (by decide)) 0 (by decide)

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

private theorem letters_layout (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (ls : List MixedTranscriptLetter)
    (hl : ∀l∈ls,∃i,i<510 ∧ l=tapeLetter i) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls := by
  intro l h
  obtain ⟨i,hi,rfl⟩:=hl l h
  simpa only [tapeLetter] using mixedTape_getD_layout base _ _ _ ctx.hf i (by omega)

private theorem rest_split : Replay5.restLetters=tapeLetter 1::remainingLetters := by
  have range : List.range' 1 4=1::List.range' 2 3 := rfl
  have mapped:=congrArg (fun ns:List Nat=>ns.map tapeLetter) range
  simpa only [Replay5.restLetters,remainingLetters,List.map_cons] using mapped

private theorem letter_sources (i : Nat) (hi : i<512) :
    (tapeLetter i).1=(base i,base (1028+i)) :=
  congrArg Prod.fst (mixedTape_base_getD i hi)

private theorem prefix_append_eq (P Q R : Program) (s : State) (m : List Bool)
    (equal : ∀a b,run P a s=run Q b s) :
    run (P++R) m s=run (Q++R)
      (List.replicate (measurementCount Q) false++m.drop (measurementCount P)) s := by
  let n:=measurementCount Q
  have take : (List.replicate n false++m.drop (measurementCount P)).take n=List.replicate n false := by
    rw [List.take_append_of_le_length (by simpa only [List.length_replicate] using Nat.le_refl n)]
    simpa only [List.length_replicate] using List.take_length (l:=List.replicate n false)
  have drop : (List.replicate n false++m.drop (measurementCount P)).drop n=m.drop (measurementCount P) := by
    simp [List.drop_append,List.length_replicate]
  rw [run_append,run_append,take,drop,equal]

private theorem raw_cons (l : MixedTranscriptLetter) (ls : List MixedTranscriptLetter) :
    OneFlagSW.rawReplayS true (l::ls)=OneFlagSW.cellS true l.1.1 l.1.2++OneFlagSW.rawReplayS true ls := rfl

private theorem raw_rest_split : OneFlagSW.rawReplayS true Replay5.restLetters=
    OneFlagSW.cellS true (base 1) (base 1029)++OneFlagSW.rawReplayS true remainingLetters := by
  have eq:=congrArg (OneFlagSW.rawReplayS true) rest_split
  have head:=raw_cons (tapeLetter 1) remainingLetters
  have g:=congrArg Prod.fst (letter_sources 1 (by decide))
  have sw:=congrArg Prod.snd (letter_sources 1 (by decide))
  rw [g,sw] at head
  exact eq.trans head

/-- Joint initial copy/half, then the unchanged S1 swap and cells2..4. -/
theorem firstBody_frame (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (first : FirstTrit origin) (Z : Fp) :
    Triple (PairFrame ports.r ports.y origin (centerWord Z) 0) firstBody
      (PairFrame ports.r ports.y origin
        (centerWord (Replay5.firstPayload true origin (Z,0)).1)
        (centerWord (Replay5.firstPayload true origin (Z,0)).2)) := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 1 (by decide)) ctx.ho
  rw [mixedTape_base_getD 1 (by decide)] at layout
  have newLayout := Q6EndpointCell.ports_transcript base (base 2400) (base 1) (base 1029)
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
  have clean := Q6EndpointCell.clean_of_env_work base (base 2409) origin ctx.env ctx.parity
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
  have jf : Triple (PairFrame ports.r ports.y origin (centerWord Z) 0) joint1592
      (PairFrame ports.r ports.y origin (centerWord A) (centerWord B)) :=
    joint1592_frame origin ctx.env (centerWord Z) 0 (centerWord A) (centerWord B)
      first.1 first.2 jfOld
  have q6Layout:=Q6EndpointCell.ports_transcript base (base 2400) (base 1) (base 1029)
    (base 2409) (base 2410) ctx.hn layout (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have swap := OneFlagCell.selectSwap_frame base (base 2400) (base 1029) (base 2409)
    (mixedTranscriptUnitTrace.getD 1 (false,false)).2 OneFlagReplay.base_sign_nd (by decide)
    (q6Layout.outside _ (by simp)) (q6Layout.outside _ (by simp))
    (q6Layout.outside _ (by simp [Q6EndpointCell.ports_sign])) origin ctx.hg0 A B
  have sel := ((SW.Sel.refl (base 2400) OneFlagSW.swapBody OneFlagSW.selSwap_away).window
    (base 1029) (base 2409) (mixedTranscriptUnitTrace.getD 1 (false,false)).2 (by decide))
  have sf := enable_frame sel origin hb away (centerWord A) (centerWord B)
    (centerWord (if S then B else A)) (centerWord (if S then A else B)) (by
      simpa only [OneFlagCell.selectSwap,OneFlagSW.swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,
        mixedTranscriptBit,hb,if_true,S] using swap)
  let C:=skywalkPayloadCell G S (if J then (0,Z) else (Z,0))
  have cell : (if S then B else A,if S then A else B)=C := by
    cases eJ:J <;> cases eG:G <;> cases eS:S <;>
      simp [C,A,B,skywalkPayloadCell,eJ,eG,eS]
  have newPrefix : Triple (PairFrame ports.r ports.y origin (centerWord Z) 0)
      (joint1592++SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)
      (PairFrame ports.r ports.y origin (centerWord C.1) (centerWord C.2)) := by
    have cx : (if S then B else A)=C.1 := congrArg Prod.fst cell
    have cy : (if S then A else B)=C.2 := congrArg Prod.snd cell
    simpa only [cx,cy] using jf.seq sf
  let D:Fp:=if J then 0 else Z
  let E:Fp:=if J then Z else 0
  have pair0 : (D,E)=(if J then (0,Z) else (Z,0)) := by cases eJ:J <;> simp [D,E,eJ]
  have layout0:=balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  rw [mixedTape_base_getD 0 (by decide)] at layout0
  have q6Layout0:=Q6EndpointCell.ports_transcript base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) ctx.hn layout0 (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have swap0:=OneFlagCell.selectSwap_frame base (base 2400) (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 OneFlagReplay.base_sign_nd (by decide)
    (q6Layout0.outside _ (by simp)) (q6Layout0.outside _ (by simp))
    (q6Layout0.outside _ (by simp [Q6EndpointCell.ports_sign])) origin ctx.hg0 Z 0
  have oldSwap : Triple (PairFrame ports.r ports.y origin (centerWord Z) 0) OneFlagSW.firstSwapS
      (PairFrame ports.r ports.y origin (centerWord D) (centerWord E)) :=
    enable_frame OneFlagSW.selFirstSwap_sel origin hb away _ _ _ _ (by
      simpa only [OneFlagReplay.firstSwap,OneFlagCell.selectSwap,mixedTranscriptBit,hb,if_true,
        HalfField.centerWord_zero,J,D,E] using swap0)
  have oldCell:=OneFlagCell.cell_frame_legacy true base (base 2400) (base 1) (base 1029)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 1 (false,false)).1
    (mixedTranscriptUnitTrace.getD 1 (false,false)).2 q6Layout origin ctx.hg0
    (Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity) D E
  have oldSelected:=OneFlagSW.selCell_sel true (base 1) (base 1029)
    (mixedTranscriptUnitTrace.getD 1 (false,false)).1 (mixedTranscriptUnitTrace.getD 1 (false,false)).2
    (by decide) (by decide)
  have oldHalf : Triple (PairFrame ports.r ports.y origin (centerWord D) (centerWord E))
      (OneFlagSW.cellS true (base 1) (base 1029))
      (PairFrame ports.r ports.y origin (centerWord C.1) (centerWord C.2)) :=
    enable_frame oldSelected origin hb away _ _ _ _ (by
      simpa only [Q6EndpointCell.payload,if_true,mixedTranscriptBit,hb,pair0,C,G,S] using oldCell)
  have oldPrefix:=oldSwap.seq oldHalf
  have selected:=(OneFlagSW.selFirstSwap_sel.append (OneFlagSW.selRaw_sel true Replay5.restLetters OneFlagSW.selRest_nodup))
  have accepted:=OneFlagReplay.firstBody_frame true origin ctx Z 0 (by simp)
  have full : Triple (PairFrame ports.r ports.y origin (centerWord Z) 0)
      (OneFlagSW.firstSwapS++OneFlagSW.rawReplayS true Replay5.restLetters)
      (PairFrame ports.r ports.y origin
        (centerWord (Replay5.firstPayload true origin (Z,0)).1)
        (centerWord (Replay5.firstPayload true origin (Z,0)).2)) :=
    enable_frame selected origin hb away _ _ _ _ (by
      simpa only [OneFlagReplay.firstBody,if_true,HalfField.centerWord_zero] using accepted)
  intro state records input
  have eq:=prefix_append_eq
    (joint1592++SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)
    (OneFlagSW.firstSwapS++OneFlagSW.cellS true (base 1) (base 1029))
    (OneFlagSW.rawReplayS true remainingLetters) state records (by
      intro a b
      exact PairFrame.program_eq _ _ origin _ _ _ _ _ _ newPrefix oldPrefix state a b input)
  have shape : firstBody=(joint1592++SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)++
      OneFlagSW.rawReplayS true remainingLetters := by simp only [firstBody,List.append_assoc]
  have oldShape : OneFlagSW.firstSwapS++OneFlagSW.rawReplayS true Replay5.restLetters=
      (OneFlagSW.firstSwapS++OneFlagSW.cellS true (base 1) (base 1029))++OneFlagSW.rawReplayS true remainingLetters := by
    rw [raw_rest_split,List.append_assoc]
  rw [shape,eq]
  rw [oldShape] at full
  exact full state _ input


/-- Codec records, entry records and tail records remain independent. -/
theorem firstPacket_frame (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (first : FirstTrit origin) (Z : Fp) (s : State) (m : List Bool)
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
    simpa only [HalfField.centerWord_zero] using firstBody_frame origin ctx hb first Z
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
