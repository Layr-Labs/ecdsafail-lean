import ECDSAAdd.Submission.Entrant.FrontierEntryJoint1591Support
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstCosts
import ECDSAAdd.Submission.Entrant.FrontierEntry1591KernelResources

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntryJoint1591
open Arithmetic Secp256k1 BalancedField MappedCompressed DirectSkywalk Challenge Baselines
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

private theorem tc_rename (f : Wire → Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem mc_rename (f : Wire → Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem firstPacket_codec_metrics :
    toffoliCount firstPacket=toffoliCount FrontierEntry.firstPacket ∧
    measurementCount firstPacket=measurementCount FrontierEntry.firstPacket ∧
    gateSlots firstPacket=gateSlots FrontierEntry.firstPacket+4 := by
  have ne:=NewHistory5.encode_counts base 0
  have nd:=NewHistory5.decode_counts base 0
  have oe:=History5.encode_counts base 0
  have od:=History5.decode_counts base 0
  have es : gateSlots (NewHistory5.encode base 0)=gateSlots (History5.encode base 0)+2 := by
    simp only [NewHistory5.encode,History5.encode,ParityCodec5New.slotsAt,MeasuredCodec5.slotsAt]
  have ds:=NewHistory5.decode_metrics base 0
  simp only [firstPacket,FrontierEntry.firstPacket,baseFirstPacket,FrontierEntry.baseFirstPacket,
    tc_rename,mc_rename,rename_gateSlots,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem firstPacket_counts_diff :
    toffoliCount firstPacket+505=toffoliCount (FrontierSW1591.firstPacketS true) ∧
    measurementCount firstPacket+509=measurementCount (FrontierSW1591.firstPacketS true) := by
  have fresh:=firstPacket_codec_metrics
  have old:=FrontierSW1591.first_metrics true
  have diff:=FrontierEntry.firstPacket_counts_diff
  exact ⟨by omega,by omega⟩

theorem firstPacket_counts : toffoliCount firstPacket=4875 ∧ measurementCount firstPacket=3590 :=
  ⟨firstPacket_codec_metrics.1.trans FrontierEntry.firstPacket_counts.1,
    firstPacket_codec_metrics.2.1.trans FrontierEntry.firstPacket_counts.2⟩

theorem firstPacket_slots_le : gateSlots firstPacket≤gateSlots (FrontierSW1591.firstPacketS true) := by
  have fresh:=firstPacket_codec_metrics.2.2
  have old:=(FrontierSW1591.first_metrics true).2.2
  have diff:=FrontierEntry.firstPacket_slots_le
  omega

theorem replay_counts_diff :
    toffoliCount replay+505=toffoliCount (FrontierSW1591.replayS true) ∧
    measurementCount replay+509=measurementCount (FrontierSW1591.replayS true) := by
  have first:=firstPacket_counts_diff
  simp only [replay,FrontierSW1591.replayS,logicalReplay,FrontierSW1591.logicalReplayS,
    if_true,tc_rename,mc_rename,toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem replay_slots_le : gateSlots replay≤gateSlots (FrontierSW1591.replayS true) := by
  have first:=firstPacket_slots_le
  simp only [replay,FrontierSW1591.replayS,logicalReplay,FrontierSW1591.logicalReplayS,
    if_true,rename_gateSlots,gateSlots_append]
  omega

theorem entryHosted_counts_diff :
    toffoliCount entryHosted+505=toffoliCount FrontierEntry1591Field.entryHosted ∧
    measurementCount entryHosted+509=measurementCount FrontierEntry1591Field.entryHosted := by
  have diff:=replay_counts_diff
  simp only [entryHosted,FrontierEntry1591Field.entryHosted,FrontierEntry1591Field.hosted,
    entryField,FrontierEntry1591Field.entryField,tc_rename,mc_rename,
    toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem entryHosted_slots_le : gateSlots entryHosted≤gateSlots FrontierEntry1591Field.entryHosted := by
  have diff:=replay_slots_le
  simp only [entryHosted,FrontierEntry1591Field.entryHosted,FrontierEntry1591Field.hosted,
    entryField,FrontierEntry1591Field.entryField,rename_gateSlots,gateSlots_append]
  omega

-- Keep circuit costs abstract in the parity-window proof.
private theorem parity_counts_diff (controls : List Wire) (work host : Wire) (P Q : Program)
    (diff : toffoliCount P+505=toffoliCount Q ∧ measurementCount P+509=measurementCount Q) :
    toffoliCount (ParityField1591.program controls work host P)+505=
      toffoliCount (ParityField1591.program controls work host Q) ∧
    measurementCount (ParityField1591.program controls work host P)+509=
      measurementCount (ParityField1591.program controls work host Q) := by
  have fresh:=ParityField1591.counts controls work host P
  have old:=ParityField1591.counts controls work host Q
  exact ⟨(congrArg (fun n : Nat=>n+505) fresh.1).trans (diff.1.trans old.1.symm),
    (congrArg (fun n : Nat=>n+509) fresh.2.1).trans (diff.2.trans old.2.1.symm)⟩

private theorem parity_slots_le (controls : List Wire) (work host : Wire) (P Q : Program)
    (diff : gateSlots P≤gateSlots Q) :
    gateSlots (ParityField1591.program controls work host P)≤
      gateSlots (ParityField1591.program controls work host Q) := by
  have fresh:=ParityField1591.counts controls work host P
  have old:=ParityField1591.counts controls work host Q
  exact fresh.2.2.le.trans ((Nat.add_le_add_right diff _).trans old.2.2.symm.le)

private theorem entry_program : entry=ParityField1591.program FrontierEntry1591Field.controls
    FrontierEntry1591Field.work FrontierEntry1591Field.host entryHosted := rfl

private theorem old_entry_program : FrontierEntry1591Field.entry=
    ParityField1591.program FrontierEntry1591Field.controls FrontierEntry1591Field.work
      FrontierEntry1591Field.host FrontierEntry1591Field.entryHosted := rfl

theorem entry_counts_diff :
    toffoliCount entry+505=toffoliCount FrontierEntry1591Field.entry ∧
    measurementCount entry+509=measurementCount FrontierEntry1591Field.entry := by
  have diff:=parity_counts_diff FrontierEntry1591Field.controls FrontierEntry1591Field.work
    FrontierEntry1591Field.host entryHosted FrontierEntry1591Field.entryHosted entryHosted_counts_diff
  exact ⟨(congrArg (fun P : Program=>toffoliCount P+505) entry_program).trans
      (diff.1.trans (congrArg toffoliCount old_entry_program).symm),
    (congrArg (fun P : Program=>measurementCount P+509) entry_program).trans
      (diff.2.trans (congrArg measurementCount old_entry_program).symm)⟩

theorem entry_slots_le : gateSlots entry≤gateSlots FrontierEntry1591Field.entry := by
  have diff:=parity_slots_le FrontierEntry1591Field.controls FrontierEntry1591Field.work
    FrontierEntry1591Field.host entryHosted FrontierEntry1591Field.entryHosted entryHosted_slots_le
  exact (congrArg gateSlots entry_program).le.trans
    (diff.trans (congrArg gateSlots old_entry_program).symm.le)

theorem entryKernel_counts_diff :
    toffoliCount entryKernel+505=toffoliCount FrontierEntry1591Kernel.entryKernel ∧
    measurementCount entryKernel+509=measurementCount FrontierEntry1591Kernel.entryKernel := by
  have diff:=entry_counts_diff
  simp only [entryKernel,FrontierEntry1591Kernel.entryKernel,FrontierEntry1591Native.relocated,
    toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem entryKernel_slots_le : gateSlots entryKernel≤gateSlots FrontierEntry1591Kernel.entryKernel := by
  have diff:=entry_slots_le
  simp only [entryKernel,FrontierEntry1591Kernel.entryKernel,FrontierEntry1591Native.relocated,
    gateSlots_append]
  omega

theorem entryKernel_slots : gateSlots entryKernel≤20502454 :=
  entryKernel_slots_le.trans FrontierEntry1591Kernel.entry_slots

private theorem unrename_physical (f : Wire → Wire) (P : Program)
    (hp : GatePhysical (renameProgram f P)) : GatePhysical P := by
  intro i hi
  have h:=hp (renameInstr f i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
  cases i with
  | X _ => trivial
  | CX _ _ => exact fun eq=>h (congrArg f eq)
  | CCX _ _ _ => exact ⟨fun eq=>h.1 (congrArg f eq),fun eq=>h.2 (congrArg f eq)⟩
  | measureX _ _ _ => trivial

theorem firstPacket_physical : GatePhysical firstPacket := by
  have old:=unrename_physical (shifted (Placement5.pi 0))
    FrontierEntry.baseFirstPacket FrontierEntry.firstPacket_physical
  have body : GatePhysical FrontierEntry.firstBody := by
    simp only [FrontierEntry.baseFirstPacket,gatePhysical_append] at old
    exact old.1.2
  have codec:=ParityCodec5New.physicalAt (History5.historyMap base 0)
    (History5.historyMap_injective base base_pool_nodup 0 (by omega))
  exact gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _
    ((gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨codec.2,body⟩,codec.1⟩)

theorem replay_physical : GatePhysical replay := by
  have groups:=(FrontierSW1591.selGroups_sel true 1 101 (by omega)).sub.physical
    (FrontierReplay1591.groups_physical true 1 101 (by omega)
      MappedCompressed.LaneA.laneLogical_config.1 MappedCompressed.LaneA.laneLogical_config.2.1
      (Replay5.letters_layouts MappedCompressed.LaneA.laneLogical_config.2.2))
  have last:=(FrontierSW1591.selEnd_sel true).sub.physical (OneFlagReplay.endPacket_physical true)
  apply gatePhysical_rename _ (OB5.sig_injective 511 (by omega))
  simpa only [logicalReplay,gatePhysical_append] using ⟨⟨firstPacket_physical,groups⟩,last⟩

theorem entryHosted_physical : GatePhysical entryHosted := by
  have ends:=OwnQ5Endpoint.endpoint_physical MappedCompressed.LaneA.laneLogical_config.1
  apply Q5FusionFields.host_physical
  exact (gatePhysical_append _ _).mpr
    ⟨replay_physical,(gatePhysical_append _ _).mpr ⟨ends.2.2,ends.2.1⟩⟩

theorem entry_physical : GatePhysical entry :=
  ParityField1591.physical _ _ _ _ FrontierEntry1591Field.host_not_controls entryHosted_physical

theorem entryKernel_physical : GatePhysical entryKernel := by
  have old:=FrontierEntry1591Kernel.entry_physical
  simp only [FrontierEntry1591Kernel.entryKernel,FrontierEntry1591Native.relocated,
    gatePhysical_append] at old
  simpa only [entryKernel,FrontierEntry1591Native.relocated,gatePhysical_append] using
    ⟨old.1,entry_physical,old.2.2⟩


end ECDSAAdd.Entrant.FrontierEntryJoint1591
