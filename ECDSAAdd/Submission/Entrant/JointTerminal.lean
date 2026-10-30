import ECDSAAdd.Submission.Entrant.JointEntry
import ECDSAAdd.Submission.Entrant.TerminalGraph

section
-- Verified combined component CombinedReplay

/-! The new first packet with the old, unchanged forward replay suffix. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalQ7
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport
attribute [local irreducible] wires History5.allEncode run measurementCount OneFlagSW.groupsS TerminalGraphSW.endPacketS

abbrev firstPacket := JointEntryQ7.firstPacket

def logicalReplay : Program :=
  firstPacket ++ TerminalGraphSW.groupsS true 1 101 ++ TerminalGraphSW.endPacketS true

def replay : Program := renameProgram (OB5.sig 511) logicalReplay

/-- The old packet uses its own record tape; the unchanged suffix keeps the new tape. -/
def oldRecords (m : List Bool) : List Bool :=
  List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false ++
    m.drop (measurementCount firstPacket)

theorem oldRecords_take (m : List Bool) :
    (oldRecords m).take (measurementCount (TerminalGraphSW.firstPacketS true))=
      List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false := by
  rw [oldRecords,List.take_append_of_le_length (by
    simpa only [List.length_replicate] using
      (Nat.le_refl (measurementCount (TerminalGraphSW.firstPacketS true))))]
  simpa only [List.length_replicate] using
    List.take_length (l:=List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false)

theorem oldRecords_drop (m : List Bool) :
    (oldRecords m).drop (measurementCount (TerminalGraphSW.firstPacketS true))=
      m.drop (measurementCount firstPacket) := by
  have nil : (List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false).drop
      (measurementCount (TerminalGraphSW.firstPacketS true))=[] := by
    simpa only [List.length_replicate] using
      List.drop_length (l:=List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false)
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
    have support : wires (History5.allEncode base 102)⊆(skywalkPoolWires base).toFinset := HalfField5.encoder_pool_support
    have pool : base 2400∈skywalkPoolWires base := List.mem_toFinset.mp (support used)
    exact ctx.hp (base 2400) (by simp) pool
  rw [encoded,run_preserves_outside _ [] raw _ unused]
  exact (frame.2.2 _ away.1 away.2).trans hb

/-- Both packet record tapes are arbitrary and independent. -/
theorem firstPacket_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (mNew mOld : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    run firstPacket mNew s=run (TerminalGraphSW.firstPacketS true) mOld s := by
  have fresh := JointEntryQ7.firstPacket_frame origin ctx hb Z s mNew input
  have old := OneFlagReplay.firstPacket_frame true origin ctx Z 0 s mOld input (by simp)
  have eq := (OneFlagSW.selFirstPacket_sel true).eq mOld s (encoded_enable origin ctx hb Z 0 s input)
  rw [←eq.1] at old
  exact encoded_unique origin _ _ _ _ fresh.2 old.2 (fresh.1.trans old.1.symm)

/-- Only the old first-packet tape is padded. The groups and end packet are unchanged. -/
theorem logical_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    run logicalReplay m s=run (TerminalGraphSW.logicalReplayS true) (oldRecords m) s := by
  have first := firstPacket_compare origin ctx hb Z s (m.take (measurementCount firstPacket))
    (List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false) input
  have freshShape : logicalReplay=firstPacket++(TerminalGraphSW.groupsS true 1 101++TerminalGraphSW.endPacketS true) := by
    simp only [logicalReplay,List.append_assoc]
  have oldShape : TerminalGraphSW.logicalReplayS true=TerminalGraphSW.firstPacketS true++(TerminalGraphSW.groupsS true 1 101++TerminalGraphSW.endPacketS true) := by
    simp only [TerminalGraphSW.logicalReplayS,if_true,List.append_assoc]
  rw [freshShape,oldShape]
  simp only [run_append,oldRecords_take,oldRecords_drop]
  rw [first]

/-- The same record builder works after the final sig511 field placement. -/
theorem replay_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : FieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    run replay m s=run (TerminalGraphSW.replayS true) (oldRecords m) s := by
  have localEq := logical_compare origin ctx hb Z (pullState (OB5.sig 511) s) m input
  have fresh := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide)) logicalReplay m s
  have old := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (TerminalGraphSW.logicalReplayS true) (oldRecords m) s
  have eq := congrArg (pullState (OB5.sig 511)) (fresh.trans (localEq.trans old.symm))
  simpa only [OB5.pull_invol 511 (by decide),replay,TerminalGraphSW.replayS] using eq

end ECDSAAdd.Entrant.JointTerminalQ7

end

section
-- Verified combined component CombinedKernelProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
def field5S : Program := JointTerminalQ7.replay ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5S : Program := [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5S ++ [.X (base 511)])
def rawKernel : Program := Q5FusionPhase.kernel hostField5S
def baseKernel : Program := Q5FusionPhase.relocated hostField5S
def kernel6S : Program := Q6FusionPhase.relocated hostField5S
def kernel5S : Program := Q7FusionPhase.relocated hostField5S
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedRecordCounts
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket



theorem old_replay_count_shape :
 measurementCount (TerminalGraphSW.replayS true)=measurementCount (OneFlagSW.firstPacketS true)+
   (measurementCount (OneFlagSW.groupsS true 1 101)+measurementCount (TerminalGraphSW.endPacketS true)) := by
 unfold TerminalGraphSW.replayS
 rw [(renameProgram_counts (OB5.sig 511) (TerminalGraphSW.logicalReplayS true)).2]
 simp only [TerminalGraphSW.logicalReplayS,TerminalGraphSW.firstPacketS,TerminalGraphSW.groupsS,if_true,measurementCount_append,Nat.add_assoc]



theorem new_replay_count_shape :
 measurementCount JointTerminalQ7.replay=measurementCount JointEntryQ7.firstPacket+
   (measurementCount (OneFlagSW.groupsS true 1 101)+measurementCount (TerminalGraphSW.endPacketS true)) := by
 unfold JointTerminalQ7.replay
 rw [(renameProgram_counts (OB5.sig 511) JointTerminalQ7.logicalReplay).2]
 simp only [JointTerminalQ7.logicalReplay,JointTerminalQ7.firstPacket,TerminalGraphSW.groupsS,measurementCount_append,Nat.add_assoc]



private theorem drop_pad (a b c : Nat) (m : List Bool) :
 (List.replicate a false ++m.drop b).drop (a+c)=m.drop (b+c) := by
 have nil : (List.replicate a false).drop (a+c)=[] :=
  List.drop_eq_nil_iff.mpr (by simp only [List.length_replicate];omega)
 rw [List.drop_append,List.length_replicate,nil]
 simp only [Nat.add_sub_cancel_left,List.nil_append,List.drop_drop]

theorem replay_records_drop (m : List Bool) :
    (JointTerminalQ7.oldRecords m).drop (measurementCount (TerminalGraphSW.replayS true))=
      m.drop (measurementCount JointTerminalQ7.replay) := by
 conv_lhs => rw [old_replay_count_shape]
 conv_rhs => rw [new_replay_count_shape]
 simpa only [JointTerminalQ7.oldRecords,JointTerminalQ7.firstPacket,TerminalGraphSW.firstPacketS] using
  drop_pad (measurementCount (OneFlagSW.firstPacketS true)) (measurementCount JointEntryQ7.firstPacket)
   (measurementCount (OneFlagSW.groupsS true 1 101)+measurementCount (TerminalGraphSW.endPacketS true)) m

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedFieldTransferPrefix
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

theorem field_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : FieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    run field5S m s=run TerminalGraphEntryRaw.field5S (JointTerminalQ7.oldRecords m) s := by
  have eq:=JointTerminalQ7.replay_compare origin ctx hb Z s m input
  simp only [field5S,TerminalGraphEntryRaw.field5S,run_append,run_take]
  rw [eq,replay_records_drop]

theorem hosted_compare (P Q : Program) (s : State) (m n : List Bool)
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
    · simp [u,X,run,writeBit,Function.update,base]
      change s.basis (base 2409)=!s.basis (base 511)
      rw [sg,hg];rfl
    · simp [u,X,run,writeBit,Function.update,base]
      change s.basis (base 2410)=s.basis (base 1542)
      rw [se,he]
  have rp:=ECDSAAdd.run_rename HostOB5.hostSwap HostOB5.hostSwap_injective P m u
  have rq:=ECDSAAdd.run_rename HostOB5.hostSwap HostOB5.hostSwap_injective Q n u
  rw [pull] at rp rq
  have ren : run (renameProgram HostOB5.hostSwap P) m u=run (renameProgram HostOB5.hostSwap Q) n u := by
    have e:=congrArg (pullState HostOB5.hostSwap) (rp.trans (equal.trans rq.symm))
    simpa only [pullState,HostOB5.hostSwap_invol] using e
  have records (r : List Bool) (t : State) : run X r t=run X [] t := by simp only[X,run]
  simpa only [X,u,run_append,measurementCount,List.take_zero,List.drop_zero,run_take,run] using
    congrArg (run X []) ren

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedFieldReady
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires field5S hostField5S TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S
 TerminalGraphEntryRaw.field5

theorem field_from_ready
 (hostFree : base 511∉wires field5S) (origin : BasisState) (ctx : OneFlagReplay.Context origin)
 (enabled : origin (base 2400)=true) (Z : Fp) (a3 v3 : State) (m : List Bool)
 (frame : FieldFrameOB5.EncodedFieldFrame origin Z 0 v3)
 (paired : ∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q)
 (selectors : a3.basis (base 2409)=false ∧ a3.basis (base 2410)=false)
 (hosts : a3.basis (base 511)=true ∧ a3.basis (base 1542)=false) :
 run hostField5S m v3=run TerminalGraphEntryRaw.hostField5S (JointTerminalQ7.oldRecords m) v3 ∧
 v3.basis (base 2400)=true := by
 have unhosted : run field5S m v3=run TerminalGraphEntryRaw.field5S (JointTerminalQ7.oldRecords m) v3 :=
  field_compare origin ctx enabled Z v3 m frame
 have outside (i : Nat) (hi : i<2056 ∨ 2312 ≤ i) : base i∉wireBlock base 2056 256 :=
  OwnPlusHost.not_block i 2056 256 (by omega)
 have keep (i : Nat) (hi : i<2056 ∨ 2312 ≤ i) : v3.basis (base i)=a3.basis (base i) :=
  (paired _ (outside i hi)).symm
 have oldSubset : wires TerminalGraphEntryRaw.field5S⊆wires TerminalGraphEntryRaw.field5 :=
  TerminalGraphEntryRaw.selField5.sub.wires_sub
 have oldAway : base 511∉wires TerminalGraphEntryRaw.field5 := TerminalGraphEntryRaw.field_free.1
 have oldFree : base 511∉wires TerminalGraphEntryRaw.field5S := fun used=>oldAway (oldSubset used)
 have compared:=hosted_compare field5S TerminalGraphEntryRaw.field5S v3 m (JointTerminalQ7.oldRecords m)
  hostFree oldFree ((keep 2409 (by omega)).trans selectors.1)
  ((keep 511 (by omega)).trans hosts.1) ((keep 2410 (by omega)).trans selectors.2)
  ((keep 1542 (by omega)).trans hosts.2) unhosted
 have on:=JointTerminalQ7.encoded_enable origin ctx enabled Z 0 (pullState (OB5.sig 511) v3) frame
 have sigb : OB5.sig 511 (base 2400)=base 2400 := by decide
 refine ⟨?_,?_⟩
 · simpa only [hostField5S,TerminalGraphEntryRaw.hostField5S] using compared
 · simpa only [pullState,sigb] using on
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedFieldFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires field5S hostField5S TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S

theorem field_from_facts (hostFree : base 511∉wires field5S)
 (hn : (skywalkSharedWires base).Nodup)
 (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
 (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
 (x : Nat) (Y : Fp) (s origin a3 v3 : State) (m : List Bool)
 (facts : PreparationFacts x Y s origin) (legal : History5.RawLegal base 102 origin.basis)
 (canonical : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3)
 (hosts : a3.basis (base 511)=true ∧ a3.basis (base 1542)=false)
 (phase : a3.phase=v3.phase)
 (same : ∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q)
 (target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2))
 (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
 (hb : s.basis (base 2400)=true) :
 run hostField5S m v3=run TerminalGraphEntryRaw.hostField5S (JointTerminalQ7.oldRecords m) v3 ∧
 v3.basis (base 2400)=true := by
 have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
  intro q hq bad
  exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
 have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
 have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
 have enabled : origin.basis (base 2400)=true := (facts.controls _ (by simp)).trans hb
 have frame:=JointEntryPrepared.retarget hn origin.basis facts.targetHigh facts.sourceHigh Y a3 v3 phase same target canonical
 let ctx : OneFlagReplay.Context origin.basis := ⟨hn,ho,hp,hf,hg,hs,facts.env,legal,facts.targetHigh⟩
 have selectors:=EntryFuse.encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero Y a3 canonical
 exact field_from_ready hostFree origin.basis ctx enabled (Y/2) a3 v3 m frame same selectors hosts
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedStateCompare
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free

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
    run hostField5S m4 v3=run TerminalGraphEntryRaw.hostField5S (JointTerminalQ7.oldRecords m4) v3 ∧
      v3.basis (base 2400)=true := by
  generalize ha1 : run (NativeFirstDirect.forward base) m1 s = a1
  generalize ha2 : run stackForwardT m2 a1 = a2
  generalize ha3 : run (skywalkArithmeticClear base) m3 a2 = a3
  have paired:=JointEntryPrepared.paired_prefix s t a1 a2 a3 v1 v2 v3 m1 m2 m3
    phase same ha1 ha2 ha3 h1 h2 h3
  have target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2) :=
    (regValue_congr _ _ _ paired.2.2).trans value
  obtain ⟨origin,facts,legal,canonical,hosts⟩:=JointEntryPrepared.canonical_prefix hn hlo ho
    x Y hx0 hx s m1 m2 m3 hin a1 a2 a3 ha1 ha2 ha3
  exact field_from_facts field5S_hosts_free.1 hn ho hf x Y s origin a3 v3 m4 facts legal canonical hosts
    paired.1 paired.2.1 target hg0 hs0 hb

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedEnabledKernel
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free

theorem enabled_kernel_correct
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
      have pair:=field_state_compare field5S_hosts_free hn hlo ho hf x Y hx0 hx s initial m1 m2 m3 m4 hin hg0 hs0
        ph sm val hb v1 v2 v3 h1 h2 h3
      have selected:=(TerminalGraphEntryRaw.selHostField5.eq (JointTerminalQ7.oldRecords m4) v3 pair.2).1
      have old4 : run TerminalGraphEntryRaw.hostField5 (JointTerminalQ7.oldRecords m4) v3=v4 := by
        have e:=pair.1.symm.trans h4
        rw [selected] at e
        simpa only [TerminalGraphEntryRaw.hostField5,TerminalGraphEntryRaw.field5,EntryFuse.hostField5,EntryFuse.field5] using e
      exact TerminalGraphEntryRaw.kernel5_states hn hlo ho hf x Y hx0 hx s initial m1 m2 m3
        (JointTerminalQ7.oldRecords m4) m5 m6 m7 hin hg0 hs0 ph sm val
        v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 old4 h5 h6 h7) t m
  simpa only [Q5FusionPhase.kernel,firstPhase,lastPhase,List.append_assoc] using all phase same value

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedEnabledBase
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free hostField5S_1026_free

theorem enabled_base_correct
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
  have old:=enabled_kernel_correct field5S_hosts_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value hb
  have eq:=Q5FusionPhase.state_eq_of_contract hn x Y hx0 hx s t m hostField5S true
    hin same hostField5S_1026_free old
  rw [baseKernel,eq]
  exact old


end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedBaseCorrect
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free hostField5S_1026_free baseKernel_control_free

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
  have strong:=enabled_base_correct field5S_hosts_free hostField5S_1026_free hn hlo ho hf x Y hx0 hx a b m input hg hs phases paired half ab
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

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelCorrect
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
variable (hostField5S_1541_free : base 1541∉wires hostField5S)
variable (hostField5S_1542_free : base 1542∉wires hostField5S)
attribute [local irreducible] run wires kernel5S kernel6S baseKernel hostField5S

/- Relocate the integer phases only after the field stage has restored both loan sites. -/
include field5S_hosts_free hostField5S_1026_free baseKernel_control_free hostField5S_1541_free
theorem kernel6S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel6S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=base_kernel5S_correct field5S_hosts_free hostField5S_1026_free baseKernel_control_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have shape : Q6FusionPhase.kernel hostField5S=baseKernel :=
    by simpa only [baseKernel] using Q6FusionGeometry.old_shape hostField5S
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [shape] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S hin same
    hostField5S_1541_free frame
  simpa only [kernel6S,eq,shape] using old

/- Relocate the integer phases only after the field stage has restored both loan sites. -/
include hostField5S_1542_free
theorem kernel5S_correct_of_static
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=kernel6S_correct field5S_hosts_free hostField5S_1026_free baseKernel_control_free hostField5S_1541_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have shape : Q7FusionPhase.kernel hostField5S=kernel6S :=
    by simpa only [kernel6S] using Q7FusionPhase.old_shape hostField5S
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q7FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [shape] using old.2.2
  have eq:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S hin same
    hostField5S_1542_free frame
  simpa only [kernel5S,eq,shape] using old

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelSupport
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed BalancedField History5 JointEntryQ7
attribute [local irreducible] wires JointEntryQ7.joint JointEntryQ7.firstBody JointEntryQ7.firstPacket JointTerminalQ7.logicalReplay JointTerminalQ7.replay OneFlagSW.swapBody OneFlagSW.rawReplayS OneFlagSW.firstBodyS TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S field5S hostField5S

private theorem cell_half_sub :
 wires (Q6EndpointCell.half true base (base 2409))⊆wires (OneFlagSW.cellS true (base 1) (base 1029)) := by
 intro q h
 simp only [OneFlagSW.cellS,if_true,SW.selW,wires_append,Finset.mem_union]
 tauto

private theorem oldBody_shape :
 OneFlagSW.firstBodyS true=OneFlagSW.firstSwapS++
 (OneFlagSW.cellS true (base 1) (base 1029)++OneFlagSW.rawReplayS true remainingLetters) := by
 have rest : Replay5.restLetters=tapeLetter 1::remainingLetters:=rfl
 simp only [OneFlagSW.firstBodyS,if_true,rest]
 rw [OneFlagSW.rawReplayS]
 rfl

private theorem half_body_sub : wires (Q6EndpointCell.half true base (base 2409))⊆wires (OneFlagSW.firstBodyS true) := by
 intro q h
 have hc:=cell_half_sub h
 rw [oldBody_shape,wires_append,wires_append]
 exact Finset.mem_union_right _ (Finset.mem_union_left _ hc)

private theorem extra_codec : {base 1028,base 1,base 0}⊆wires (History5.decode base 0) := by decide +kernel

private theorem union_into_packet (D B E : Program) (C F : Finset Wire)
 (hc : C⊆wires B) (hf : F⊆wires D) : C∪F⊆wires (D++B++E) := by
 rw [wires_append,wires_append]
 exact Finset.union_subset (hc.trans ((Finset.subset_union_right).trans Finset.subset_union_left))
   (hf.trans (Finset.subset_union_left.trans Finset.subset_union_left))

private theorem joint_base_sub : wires (joint (base 1028) (base 1))⊆wires (OneFlagSW.baseFirstPacketS true) := by
 have sub : wires (joint (base 1028) (base 1))⊆
   JointEntryKernelFootprint.coreSites (Q6EndpointCell.ports base (base 2409))∪{base 1028,base 1,base 0} := by
   simpa only [JointEntryKernelFootprint.sites_split] using joint_support (base 1028) (base 1) (by decide +kernel)
 have target := union_into_packet (History5.decode base 0) (OneFlagSW.firstBodyS true) (History5.encode base 0)
   _ _ (JointEntryKernelFootprint.actual_core_subset_half.trans half_body_sub) extra_codec
 exact sub.trans target

private theorem tail_body_sub :
 wires (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody++OneFlagSW.rawReplayS true remainingLetters)⊆
 wires (OneFlagSW.firstBodyS true) := by
 have cell : wires (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)⊆wires (OneFlagSW.cellS true (base 1) (base 1029)) := by
   simp only [OneFlagSW.cellS,if_true,wires_append]
   exact Finset.subset_union_right
 intro q used
 rw [oldBody_shape]
 simp only [wires_append,Finset.mem_union] at used ⊢
 rcases used with h|h
 · exact Or.inr (Or.inl (cell h))
 · exact Or.inr (Or.inr h)

private theorem first_base_sub : wires baseFirstPacket⊆wires (OneFlagSW.baseFirstPacketS true) := by
 intro q used
 simp only [baseFirstPacket,wires_append,Finset.mem_union] at used
 rcases used with (hd|hb)|he
 · simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
 · simp only [firstBody,wires_append,Finset.mem_union] at hb
   rcases hb with (hj|hs)|hr
   · exact joint_base_sub hj
   · have htail:=tail_body_sub (by rw [wires_append]; exact Finset.mem_union_left _ hs)
     simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
   · have htail:=tail_body_sub (by rw [wires_append]; exact Finset.mem_union_right _ hr)
     simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
 · simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto

private theorem first_sub : wires firstPacket⊆wires (TerminalGraphSW.firstPacketS true) := by
 simpa only [firstPacket,TerminalGraphSW.firstPacketS,OneFlagSW.firstPacketS,renameProgram_support] using Finset.image_subset_image first_base_sub

private theorem replay_sub : wires JointTerminalQ7.replay⊆wires (TerminalGraphSW.replayS true) := by
 have log : wires JointTerminalQ7.logicalReplay⊆wires (TerminalGraphSW.logicalReplayS true) := by
   intro q used
   simp only [JointTerminalQ7.logicalReplay,TerminalGraphSW.logicalReplayS,if_true,wires_append,Finset.mem_union] at used ⊢
   rcases used with (h|h)|h
   · exact Or.inl (Or.inl (first_sub h))
   · exact Or.inl (Or.inr h)
   · exact Or.inr h
 simpa only [JointTerminalQ7.replay,TerminalGraphSW.replayS,renameProgram_support] using Finset.image_subset_image log

theorem field_subset_old : wires field5S⊆wires TerminalGraphEntryRaw.field5S := by
 simp only [field5S,TerminalGraphEntryRaw.field5S,wires_append]
 exact Finset.union_subset_union replay_sub (Finset.Subset.refl _)

theorem hosted_subset_old : wires hostField5S⊆wires TerminalGraphEntryRaw.hostField5S := by
 have ren:=Finset.image_subset_image (f:=HostOB5.hostSwap) field_subset_old
 simp only [hostField5S,TerminalGraphEntryRaw.hostField5S,wires_append,renameProgram_support]
 exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union ren (Finset.Subset.refl _))

theorem field5S_support : wires field5S⊆OB5Support.segSites :=
 field_subset_old.trans (TerminalGraphEntryRaw.selField5.sub.wires_sub.trans TerminalGraphEntryRaw.field_support)

theorem field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S := by
 have off : base 511∉OB5Support.segSites ∧ base 1542∉OB5Support.segSites := OB5Support.seg_host_free
 exact ⟨fun h=>off.1 (field5S_support h),fun h=>off.2 (field5S_support h)⟩

theorem field5S_control_free : base 2400∉wires field5S := fun h=>TerminalGraphEntryRaw.selField5.away (field_subset_old h)
theorem hostField5S_1026_free : base 1026∉wires hostField5S :=fun h=>TerminalGraphEntryQ5.hostField5S_free (hosted_subset_old h)
theorem hostField5S_1541_free : base 1541∉wires hostField5S :=fun h=>TerminalGraphEntryQ6.hostField5S_free1541 (hosted_subset_old h)
theorem hostField5S_1542_free : base 1542∉wires hostField5S :=fun h=>OwnTerminalGraphEntryQ7.hostField5S_free1542 (hosted_subset_old h)

theorem hostField5S_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) : base i∉wires hostField5S := by
 intro used
 apply TerminalGraphEntryOmissions.kernel_free7 i hi
 have sub : wires TerminalGraphEntryRaw.hostField5S⊆wires OwnTerminalGraphEntryQ7.kernel5S := by
   intro q hq
   simp only [OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated,wires_append,Finset.mem_union]
   exact Or.inr (Or.inl hq)
 exact sub (hosted_subset_old used)
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelGeometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic MappedCompressed Q5Global718
attribute [local irreducible] wires run
 TerminalGraphEntryRaw.kernel5 TerminalGraphEntryRaw.kernel5S TerminalGraphEntryRaw.hostField5S
 hostField5S baseKernel rawKernel kernel6S kernel5S

theorem hostField5S_control_free : base 2400∉wires hostField5S :=
 fun used=>TerminalGraphEntryRaw.selHostField5.away (hosted_subset_old used)

theorem baseKernel_control_free : base 2400∉wires baseKernel := by
 have f:=OwnQ5SW.renamed_first_away
 have l:=OwnQ5SW.renamed_last_away
 simpa only [baseKernel,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or] using
  And.intro f (And.intro hostField5S_control_free l)

private theorem replace_middle (a b p q : Program) (h : wires p⊆wires q) :
 wires (a++(p++b))⊆wires (a++(q++b)) := by
 simp only [wires_append]
 exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))

theorem kernel_subset_old : wires kernel5S⊆wires OwnTerminalGraphEntryQ7.kernel5S := by
 simpa only [kernel5S,OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated] using
  replace_middle (renameProgram Q7IntegerHost.swap Q7FusionPhase.q6First)
   (renameProgram Q7IntegerHost.swap Q7FusionPhase.q6Last) hostField5S TerminalGraphEntryRaw.hostField5S hosted_subset_old

theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites :=
 kernel_subset_old.trans OwnTerminalGraphEntryQ7.kernel5S_support

theorem kernel5S_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∉wires kernel5S := fun used=>TerminalGraphEntryOmissions.kernel_free7 i hi (kernel_subset_old used)
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelClosed
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
 exact kernel5S_correct_of_static field5S_hosts_free hostField5S_1026_free baseKernel_control_free
  hostField5S_1541_free hostField5S_1542_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelCosts
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5 Challenge Baselines
attribute [local irreducible] wires toffoliCount measurementCount gateSlots
 Q7FusionPhase.q6First Q7FusionPhase.q6Last
 TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S
 JointEntryQ7.firstPacket OneFlagSW.firstPacketS OneFlagSW.groupsS TerminalGraphSW.endPacketS

theorem kernel5S_counts_diff :
    toffoliCount kernel5S + 504 = toffoliCount OwnTerminalGraphEntryQ7.kernel5S ∧
    measurementCount kernel5S + 510 = measurementCount OwnTerminalGraphEntryQ7.kernel5S := by
  have first := JointEntryQ7.firstPacket_counts_diff
  simp only [kernel5S,OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated,
    hostField5S,field5S,JointTerminalQ7.replay,JointTerminalQ7.logicalReplay,
    TerminalGraphEntryRaw.hostField5S,TerminalGraphEntryRaw.field5S,TerminalGraphSW.replayS,TerminalGraphSW.logicalReplayS,
    if_true,JointTerminalQ7.firstPacket,TerminalGraphSW.firstPacketS,TerminalGraphSW.groupsS,toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega

theorem kernel5S_slots_le : gateSlots kernel5S ≤ gateSlots OwnTerminalGraphEntryQ7.kernel5S+9000 := by
  have first := JointEntryQ7.firstPacket_slots_le
  simp only [kernel5S,OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated,
    hostField5S,field5S,JointTerminalQ7.replay,JointTerminalQ7.logicalReplay,
    TerminalGraphEntryRaw.hostField5S,TerminalGraphEntryRaw.field5S,TerminalGraphSW.replayS,TerminalGraphSW.logicalReplayS,
    if_true,JointTerminalQ7.firstPacket,TerminalGraphSW.firstPacketS,TerminalGraphSW.groupsS,gateSlots_append,rename_gateSlots]
  omega

theorem replay_physical : GatePhysical JointTerminalQ7.replay := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have oldGroups := OneFlagReplay.groups_physical true 1 101 (by decide)
    cfg.1 cfg.2.1 (Replay5.letters_layouts cfg.2.2)
  have groups := (OneFlagSW.selGroups_sel true 1 101 (by decide)).sub.physical oldGroups
  have last := (TerminalGraphSW.selEnd_sel TerminalGraphSupport.half_subset true).sub.physical (TerminalGraphReplay.endPacket_physical true)
  have logical : GatePhysical JointTerminalQ7.logicalReplay := by
    simpa only [JointTerminalQ7.logicalReplay,gatePhysical_append] using
      And.intro (And.intro JointEntryQ7.firstPacket_physical groups) last
  exact gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _ logical

theorem field5S_physical : GatePhysical field5S := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have old := (TerminalGraphEntryRaw.selField5.sub.physical
    (TerminalGraphEntryResources.field_sub.physical (TerminalGraphSegment.physical true cfg.1 cfg.2.1 cfg.2.2)))
  simp only [TerminalGraphEntryRaw.field5S,gatePhysical_append] at old
  simpa only [field5S,gatePhysical_append] using And.intro replay_physical old.2

theorem hostField5S_physical : GatePhysical hostField5S := by
  simpa only [hostField5S] using Q5FusionFields.host_physical field5S field5S_physical

theorem kernel5S_physical : GatePhysical kernel5S := by
  have old := OwnTerminalGraphEntryQ7.kernel5S_physical
  simp only [OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated,gatePhysical_append] at old
  simpa only [kernel5S,Q7FusionPhase.relocated,gatePhysical_append] using
    And.intro old.1 (And.intro hostField5S_physical old.2.2)
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedDivision

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointTerminalDivisionQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires

private theorem mapped_regS (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

theorem kernelTransferS (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires JointTerminalKernelQ7.kernel5S⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f JointTerminalKernelQ7.kernel5S) m t
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
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
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
    rw [mapped_regS f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := JointTerminalKernelQ7.kernel5S_correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective JointTerminalKernelQ7.kernel5S sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (mapped_regS f _ (run JointTerminalKernelQ7.kernel5S m b).basis
      (run (renameProgram f JointTerminalKernelQ7.kernel5S) m t).basis
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
    · exact (run_rename_pool_outside f domain JointTerminalKernelQ7.kernel5S sites m t q image).trans (same q hq)



open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots
def arithEntryS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) JointTerminalKernelQ7.kernel5S

theorem arithEntryS_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithEntryS L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ JointTerminalKernelQ7.kernel5S_support

theorem arithEntryS_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (arithEntryS L) := by
  apply gatePhysical_rename_support (wireFn2 L) JointTerminalKernelQ7.kernel5S
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (JointTerminalKernelQ7.kernel5S_support ha)) b
      (ArithmeticOB5.logical_sub_old (JointTerminalKernelQ7.kernel5S_support hb)) eq
  · exact JointTerminalKernelQ7.kernel5S_physical

private theorem divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem arithEntryS_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
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
    let out := run (arithEntryS L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact kernelTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    divisor_sitesS numerator_sitesS control_siteS (JointTerminalKernelQ7.kernel5S_support.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] arithEntryS arithS

theorem arithEntryS_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
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
    run (arithEntryS L) m t=run (arithS L false) [] s := by
  have newer := arithEntryS_correct L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (arithEntryS L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm


open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
open Challenge Baselines
def fusedDivisionF (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ arithEntryS L

section EntryStep
attribute [local irreducible] fusedY fastConstAdd

theorem fusedDivisionF_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedDivisionF L k)
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
  have equal := arithEntryS_eq L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (fusedDivisionF L k) m s=run (arithS L false) [] c := by
    simp only [fusedDivisionF,run_append]
    change run (arithEntryS L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep

theorem fusedDivisionF_support (L : ControlledPointLayout) (hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    wires (fusedDivisionF L k)⊆(OB5Support.sites L).toFinset := by
  simp only [fusedDivisionF,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    arithEntryS_support L hw⟩

theorem fusedDivisionF_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (fusedDivisionF L k) := by
  simp only [fusedDivisionF,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,arithEntryS_physical L hw hn⟩

theorem fusedDivisionF_counts_diff (L : ControlledPointLayout) (_hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    toffoliCount (fusedDivisionF L k)+504=toffoliCount (OwnTerminalGraphEntryQ7.fusedDivisionF L k) ∧
      measurementCount (fusedDivisionF L k)+510=measurementCount (OwnTerminalGraphEntryQ7.fusedDivisionF L k) := by
  have c:=JointTerminalKernelQ7.kernel5S_counts_diff
  have a:=renameProgram_counts (wireFn2 L) JointTerminalKernelQ7.kernel5S
  have b:=renameProgram_counts (wireFn2 L) OwnTerminalGraphEntryQ7.kernel5S
  simp only [fusedDivisionF,OwnTerminalGraphEntryQ7.fusedDivisionF,arithEntryS,OwnTerminalGraphEntryQ7.arithEntryS,
    toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  constructor <;> omega

theorem fusedDivisionF_slots_le (L : ControlledPointLayout) (_hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    gateSlots (fusedDivisionF L k)≤gateSlots (OwnTerminalGraphEntryQ7.fusedDivisionF L k)+9000 := by
  simp only [fusedDivisionF,OwnTerminalGraphEntryQ7.fusedDivisionF,arithEntryS,OwnTerminalGraphEntryQ7.arithEntryS,
    gateSlots_append,rename_gateSlots]
  have h:=JointTerminalKernelQ7.kernel5S_slots_le
  omega

private theorem placed_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i k : Nat) (hi : base i∈OB5Support.logicalSites)
    (hm : wireFn2 L (base i)=L.core.poolWire k)
    (free : base i∉wires JointTerminalKernelQ7.kernel5S) :
    L.core.poolWire k∉wires (arithEntryS L) := by
  rw [arithEntryS,renameProgram_support]
  intro h
  obtain ⟨old,used,eq⟩:=Finset.mem_image.mp h
  have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (JointTerminalKernelQ7.kernel5S_support used)) (base i)
    (ArithmeticOB5.logical_sub_old hi) mapped
  exact free (back ▸ used)

private theorem logical_mem (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
    base i∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem arithEntryS_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286]) :
    L.core.poolWire k∉wires (arithEntryS L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact placed_free L hw hn 2312 1800 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 766 766 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 765 765 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 767 767 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 1026 770 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 1541 1285 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 1542 1286 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))

theorem fusedDivisionF_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat)
    (hk : k∈[1800,766,765,767,770,1285,1286]) (c : Fp) :
    L.core.poolWire k∉wires (fusedDivisionF L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have old:=ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [fusedDivisionF,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),arithEntryS_free L hw hn k hk⟩

end ECDSAAdd.Entrant.JointTerminalDivisionQ7

end

section
-- Verified combined component CombinedActual
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount gateSlots
 fastConstAdd fastConstNeg fastConstRefl

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
 All12Generic.generic L (JointTerminalDivisionQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L)
  (OwnOneFlagExitQ7.arithExit L) cx cy
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
 All12Generic.gen L (JointTerminalDivisionQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L)
  (OwnOneFlagExitQ7.arithExit L) cx cy

theorem generic_counts_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 toffoliCount (generic L cx cy)+504=toffoliCount (OwnTerminalGraphActual.generic L cx cy) ∧
 measurementCount (generic L cx cy)+510=measurementCount (OwnTerminalGraphActual.generic L cx cy) := by
 have d:=JointTerminalDivisionQ7.fusedDivisionF_counts_diff L hw hn (-cy)
 simp only [generic,OwnTerminalGraphActual.generic,TerminalGraphProducer.generic,All12Generic.generic,
  toffoliCount_append,measurementCount_append]
 constructor <;> omega

theorem gen_counts_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 toffoliCount (gen L cx cy)+504=toffoliCount (OwnTerminalGraphActual.gen L cx cy) ∧
 measurementCount (gen L cx cy)+510=measurementCount (OwnTerminalGraphActual.gen L cx cy) := by
 have d:=generic_counts_diff L hw hn cx cy
 simp only [generic,OwnTerminalGraphActual.generic,TerminalGraphProducer.generic] at d
 simp only [gen,OwnTerminalGraphActual.gen,TerminalGraphProducer.gen,All12Generic.gen,All12Generic.mid,
  toffoliCount_append,measurementCount_append,renameProgram_counts]
 constructor <;> omega

theorem generic_sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
 All12Generic.generic_sites L hw _ _ _ (JointTerminalDivisionQ7.fusedDivisionF_support L hw hn)
  (OwnDiagAll12PlacedQ7.support L hw hn) (OwnTerminalGraphActual.exit_support L hw) cx cy

theorem sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
 rw [gen,All12Generic.gen_shape]
 exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)

theorem physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 GatePhysical (gen L cx cy) :=
 All12Generic.gen_physical L hw hn _ _ _ (JointTerminalDivisionQ7.fusedDivisionF_physical L hw hn)
  (OwnDiagAll12PlacedQ7.physical L hw hn) (OwnOneFlagExitQ7.arithExit_physical L hw hn) cx cy

theorem gen_slots_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 gateSlots (gen L cx cy)≤gateSlots (OwnTerminalGraphActual.gen L cx cy)+9000 := by
 have d:=JointTerminalDivisionQ7.fusedDivisionF_slots_le L hw hn (-cy)
 simp only [gen,OwnTerminalGraphActual.gen,TerminalGraphProducer.gen,All12Generic.gen,All12Generic.mid,
  All12Generic.generic,gateSlots_append,rename_gateSlots]
 omega

theorem slots (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 gateSlots (gen L cx cy)≤49233000 := by
 have h:=gen_slots_diff L hw hn cx cy
 have old:=OwnTerminalGraphActual.slots L hw cx cy
 omega

theorem generic_free (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (k:Nat) (hk:k∈[1800,766,765,767,770,1285,1286]) (cx cy:Fp) :
 L.core.poolWire k∉wires (generic L cx cy) := by
 have bounds : 515≤k ∧ k<2613 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
 exact All12Generic.generic_free L hw hn _ _ _ k bounds
  (JointTerminalDivisionQ7.fusedDivisionF_free L hw hn k hk)
  (OwnDiagAll12PlacedQ7.square_free L hw hn k hk)
  (OneFlagExitOmissions.exit_avoids L hw hn k hk) cx cy

theorem ok (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (logicalND : (skywalkSharedWires base).Nodup) (hlo:History5.HistoryAbove base)
 (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
 (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
 {cx cy:Fp} (hc:curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) :=
 All12Generic.genFFused_ok L hw hn _ _ _ (OwnOneFlagExitQ7.arithExit_correct L hw hn)
  (JointTerminalDivisionQ7.fusedDivisionF_step L hw hn logicalND hlo logicalAway logicalReplay)
  (TerminalGraphProducer.square_step L hw hn) hc

theorem qubits (C:Point) (cx cy:Fp) : qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1592 := by
 rw [gen,All12Generic.gen_shape]
 apply GenericQ7Geometry.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy)
 · intro k hk
   exact generic_free layout layout_widths layout_nodup k (List.mem_append_left [1285,1286] hk) cx cy
 · exact generic_free layout layout_widths layout_nodup 1285 (by simp) cx cy
 · exact generic_free layout layout_widths layout_nodup 1286 (by simp) cx cy
end ECDSAAdd.Entrant.JointTerminalActual

end
