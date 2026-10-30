import ECDSAAdd.Submission.Entrant.FrontierEntryKernelProgram
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstCosts

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntryKernel
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5 Challenge Baselines

private theorem tc_rename (f : Wire → Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem mc_rename (f : Wire → Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem kernel5S_counts_diff :
    toffoliCount kernel5S + 505 = toffoliCount OwnOneFlagEntryQ7.kernel5S ∧
    measurementCount kernel5S + 509 = measurementCount OwnOneFlagEntryQ7.kernel5S := by
  have first := FrontierEntry.firstPacket_counts_diff
  simp only [kernel5S,OwnOneFlagEntryQ7.kernel5S,Q7FusionPhase.relocated,
    hostField5S,field5S,FrontierEntry.replay,FrontierEntry.logicalReplay,
    OneFlagEntryRaw.hostField5S,OneFlagEntryRaw.field5S,OneFlagSW.replayS,OneFlagSW.logicalReplayS,
    if_true,toffoliCount_append,measurementCount_append,tc_rename,mc_rename]
  constructor <;> omega

theorem kernel5S_slots_le : gateSlots kernel5S ≤ gateSlots OwnOneFlagEntryQ7.kernel5S := by
  have first := FrontierEntry.firstPacket_slots_le
  simp only [kernel5S,OwnOneFlagEntryQ7.kernel5S,Q7FusionPhase.relocated,
    hostField5S,field5S,FrontierEntry.replay,FrontierEntry.logicalReplay,
    OneFlagEntryRaw.hostField5S,OneFlagEntryRaw.field5S,OneFlagSW.replayS,OneFlagSW.logicalReplayS,
    if_true,gateSlots_append,rename_gateSlots]
  omega

theorem replay_physical : GatePhysical FrontierEntry.replay := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have oldGroups := OneFlagReplay.groups_physical true 1 101 (by decide)
    cfg.1 cfg.2.1 (Replay5.letters_layouts cfg.2.2)
  have groups := (OneFlagSW.selGroups_sel true 1 101 (by decide)).sub.physical oldGroups
  have last := (OneFlagSW.selEnd_sel true).sub.physical (OneFlagReplay.endPacket_physical true)
  have logical : GatePhysical FrontierEntry.logicalReplay := by
    simpa only [FrontierEntry.logicalReplay,gatePhysical_append] using
      And.intro (And.intro FrontierEntry.firstPacket_physical groups) last
  exact gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _ logical

theorem field5S_physical : GatePhysical field5S := by
  have old := OneFlagEntryRaw.selField5.sub.physical
    (OneFlagEntryResources.field_sub.physical (OneFlagSegment.program_physical true
      MappedCompressed.LaneA.laneLogical_config.1 MappedCompressed.LaneA.laneLogical_config.2.1
      MappedCompressed.LaneA.laneLogical_config.2.2))
  simp only [OneFlagEntryRaw.field5S,gatePhysical_append] at old
  simpa only [field5S,gatePhysical_append] using And.intro replay_physical old.2

theorem hostField5S_physical : GatePhysical hostField5S := by
  simpa only [hostField5S] using Q5FusionFields.host_physical field5S field5S_physical

theorem kernel5S_physical : GatePhysical kernel5S := by
  have old := OwnOneFlagEntryQ7.kernel5S_physical
  simp only [OwnOneFlagEntryQ7.kernel5S,Q7FusionPhase.relocated,gatePhysical_append] at old
  simpa only [kernel5S,Q7FusionPhase.relocated,gatePhysical_append] using
    And.intro old.1 (And.intro hostField5S_physical old.2.2)
end ECDSAAdd.Entrant.FrontierEntryKernel
