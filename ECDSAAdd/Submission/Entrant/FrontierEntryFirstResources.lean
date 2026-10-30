import ECDSAAdd.Submission.Entrant.FrontierEntryFirstSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed
attribute [local irreducible] wires toffoliCount measurementCount

private theorem rest_nodup (l : MixedTranscriptLetter) (hl : l∈remainingLetters) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup := by
  apply OneFlagSW.selRest_nodup
  change l∈tapeLetter 1::remainingLetters
  exact List.mem_cons_of_mem _ hl

private theorem swap_nd : (base 2409::(ports.r++ports.y)).Nodup := by
  have hn := MappedCompressed.LaneA.laneLogical_config.1
  have ho : base 2409∉skywalkSharedWires base :=
    MappedCompressed.LaneA.laneLogical_config.2.1 _ (by simp)
  have own : base 2409∉balancedSharedIds.map base := fun h =>
    ho (balancedSharedLayout_mapSubset base balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup base (base 2409) hn own
  have aw := BalancedCircuit.flagAway (balancedSharedPorts base (base 2409)) nd (base 2409)
    (by simp [balancedSharedPorts])
  apply List.nodup_cons.mpr
  refine ⟨?_,balancedSharedLayout_pairND base (base 2409) hn⟩
  intro h
  rcases List.mem_append.mp h with h|h
  · have hr : base 2409∈(balancedSharedPorts base (base 2409)).r := by
      simpa only [ports_r,balancedSharedPorts_r] using h
    exact aw (List.mem_append_left _ (List.mem_append_left _ hr))
  · have hy : base 2409∈(balancedSharedPorts base (base 2409)).y := by
      simpa only [ports_y,balancedSharedPorts_y] using h
    exact aw (List.mem_append_left _ (List.mem_append_right _ hy))

private theorem selSwap_counts :
    toffoliCount (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)=256 ∧
      measurementCount (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)=1 := by
  have width:=BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))
  have nd : (base 2409::((balancedSharedPorts base (base 2409)).r++
      (balancedSharedPorts base (base 2409)).y)).Nodup := by
    simpa only [ports_r,ports_y] using swap_nd
  have c:=swapRegisters_resources (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y (width.2.1.trans width.2.2.1.symm) nd
  simp only [SW.selW,OneFlagSW.swapBody,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,c.1,c.2.1,width.2.1]
  norm_num

private theorem raw_counts_nd :
    (base 2410::((Q6EndpointCell.ports base (base 2409)).r++
      (Q6EndpointCell.ports base (base 2409)).y)).Nodup := by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have layout:=balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ cfg.2.2 0 (by decide)) cfg.2.1
  simpa only [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y] using layout.swapND

theorem firstPacket_counts : toffoliCount firstPacket=4875 ∧ measurementCount firstPacket=3590 := by
  have old:=OneFlagReplay.raw_counts true remainingLetters raw_counts_nd
  have len : remainingLetters.length=3 := by simp [remainingLetters]
  rw [len] at old
  have selected:=OneFlagSW.selRaw_sel true remainingLetters rest_nodup
  have selectedT:=selected.tc
  have selectedM:=selected.mc
  have jointC:=joint1592_counts
  have sw:=selSwap_counts
  have ec:=History5.encode_counts base 0
  have dc:=History5.decode_counts base 0
  have placed:=renameProgram_counts (shifted (Placement5.pi 0)) baseFirstPacket
  change toffoliCount (renameProgram (shifted (Placement5.pi 0)) baseFirstPacket)=4875 ∧
    measurementCount (renameProgram (shifted (Placement5.pi 0)) baseFirstPacket)=3590
  rw [placed.1,placed.2]
  simp only [baseFirstPacket,firstBody,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem firstPacket_counts_diff :
    toffoliCount firstPacket+505=toffoliCount (OneFlagSW.firstPacketS true) ∧
      measurementCount firstPacket+509=measurementCount (OneFlagSW.firstPacketS true) := by
  have old:=OneFlagReplay.firstPacket_counts true MappedCompressed.LaneA.laneLogical_config.1
    (MappedCompressed.LaneA.laneLogical_config.2.1 _ (by simp))
  have selected:=OneFlagSW.selFirstPacket_sel true
  have selectedT:=selected.tc
  have selectedM:=selected.mc
  have fresh:=firstPacket_counts
  simp only [if_true] at old
  constructor <;> omega

end ECDSAAdd.Entrant.FrontierEntry
