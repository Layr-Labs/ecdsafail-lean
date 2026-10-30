import ECDSAAdd.Submission.Entrant.FrontierEntry1591FieldCounts
import ECDSAAdd.Submission.Entrant.ParityHistoryResources
import ECDSAAdd.Submission.Entrant.FrontierEntry1591CallerResources

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
