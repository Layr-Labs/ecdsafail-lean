import ECDSAAdd.Submission.Entrant.FrontierEntryReplayProgram
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstPacket
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstSupport

/-! The new first packet with the old, unchanged forward replay suffix. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport
attribute [local irreducible] run measurementCount OneFlagSW.groupsS OneFlagSW.endPacketS

theorem oldRecords_take (m : List Bool) :
    (oldRecords m).take (measurementCount (OneFlagSW.firstPacketS true))=
      List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false := by
  rw [oldRecords,List.take_append_of_le_length (by
    simpa only [List.length_replicate] using
      (Nat.le_refl (measurementCount (OneFlagSW.firstPacketS true))))]
  simpa only [List.length_replicate] using
    List.take_length (l:=List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false)

theorem oldRecords_drop (m : List Bool) :
    (oldRecords m).drop (measurementCount (OneFlagSW.firstPacketS true))=
      m.drop (measurementCount firstPacket) := by
  have nil : (List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false).drop
      (measurementCount (OneFlagSW.firstPacketS true))=[] := by
    simpa only [List.length_replicate] using
      List.drop_length (l:=List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false)
  rw [oldRecords,List.drop_append,List.length_replicate,nil,Nat.sub_self,List.drop_zero,List.nil_append]

private theorem encoded_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : History5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (ht : History5.EncodedFieldFrame5 base (base 2409) origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩:=hs
  obtain ⟨b,hb,fb,eb⟩:=ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

theorem encoded_enable (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (X Y : Fp) (s : State)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    s.basis (base 2400)=true := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  have away := layout.outside (base 2400) (by simp)
  obtain ⟨raw,_,frame,encoded⟩:=input
  have unused : base 2400∉wires (History5.allEncode base 102) := by
    intro used
    have pool : base 2400∈skywalkPoolWires base :=
      List.mem_toFinset.mp (HalfField5.encoder_pool_support used)
    exact ctx.hp (base 2400) (by simp) pool
  rw [encoded,run_preserves_outside _ [] raw _ unused]
  exact (frame.2.2 _ away.1 away.2).trans hb

/-- Both packet record tapes are arbitrary and independent. -/
theorem firstPacket_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (first : FirstTrit origin) (Z : Fp) (s : State) (mNew mOld : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    run firstPacket mNew s=run (OneFlagSW.firstPacketS true) mOld s := by
  have fresh := firstPacket_frame origin ctx hb first Z s mNew firstBody_read_support input
  have old := OneFlagReplay.firstPacket_frame true origin ctx Z 0 s mOld input (by simp)
  have eq := (OneFlagSW.selFirstPacket_sel true).eq mOld s (encoded_enable origin ctx hb Z 0 s input)
  rw [←eq.1] at old
  exact encoded_unique origin _ _ _ _ fresh.2 old.2 (fresh.1.trans old.1.symm)

/-- Only the old first-packet tape is padded. The groups and end packet are unchanged. -/
theorem logical_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (first : FirstTrit origin) (Z : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    run logicalReplay m s=run (OneFlagSW.logicalReplayS true) (oldRecords m) s := by
  have first := firstPacket_compare origin ctx hb first Z s (m.take (measurementCount firstPacket))
    (List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false) input
  have freshShape : logicalReplay=firstPacket++(OneFlagSW.groupsS true 1 101++OneFlagSW.endPacketS true) := by
    simp only [logicalReplay,List.append_assoc]
  have oldShape : OneFlagSW.logicalReplayS true=OneFlagSW.firstPacketS true++(OneFlagSW.groupsS true 1 101++OneFlagSW.endPacketS true) := by
    simp only [OneFlagSW.logicalReplayS,if_true,List.append_assoc]
  rw [freshShape,oldShape]
  simp only [run_append,oldRecords_take,oldRecords_drop]
  rw [first]

/-- The same record builder works after the final sig511 field placement. -/
theorem replay_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (first : FirstTrit origin) (Z : Fp) (s : State) (m : List Bool)
    (input : FieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    run replay m s=run (OneFlagSW.replayS true) (oldRecords m) s := by
  have localEq := logical_compare origin ctx hb first Z (pullState (OB5.sig 511) s) m input
  have fresh := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide)) logicalReplay m s
  have old := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (OneFlagSW.logicalReplayS true) (oldRecords m) s
  have eq := congrArg (pullState (OB5.sig 511)) (fresh.trans (localEq.trans old.symm))
  simpa only [OB5.pull_invol 511 (by decide),replay,OneFlagSW.replayS] using eq

end ECDSAAdd.Entrant.FrontierEntry
