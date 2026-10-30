import ECDSAAdd.Submission.Entrant.FrontierEntryFirstResources

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed Challenge Baselines

private theorem remaining_mem (l : MixedTranscriptLetter) (hl : l ∈ remainingLetters) :
    l ∈ Replay5.restLetters := by
  change l ∈ tapeLetter 1 :: remainingLetters
  exact List.mem_cons_of_mem _ hl

private theorem cost_swap_nd : (base 2409::(ports.r++ports.y)).Nodup := by
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


private theorem remaining_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) remainingLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range'_1.mp hk
  simpa only [remainingLetters,tapeLetter] using
    mixedTape_getD_layout base _ _ _ hf k (by omega)

private theorem selected_physical (source flag : Wire) (P : Program)
    (away : source ≠ flag) (physical : GatePhysical P) :
    GatePhysical (SW.selW source flag P) := by
  have head : GatePhysical [Instr.CX source flag] := by
    simpa [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate] using away
  have tail : GatePhysical [Instr.measureX flag [] [Correction.Z source]] := by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  simpa only [SW.selW,gatePhysical_append] using And.intro (And.intro head physical) tail

theorem firstPacket_physical : GatePhysical firstPacket := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have pair := cost_swap_nd
  have swap : GatePhysical OneFlagSW.swapBody := by
    simpa only [OneFlagSW.swapBody] using swapRegisters_physical _ _ _ pair
  have selected := OneFlagSW.selRaw_sel true remainingLetters
    (fun l hl => OneFlagSW.selRest_nodup l (remaining_mem l hl))
  have rest := OneFlagReplay.raw_physical true remainingLetters cfg.1 cfg.2.1
    (remaining_layout cfg.2.2)
  have body : GatePhysical firstBody := by
    simpa only [firstBody,gatePhysical_append] using
      And.intro (And.intro (joint1592_physical (by
          simpa only [loanPorts1592,Q6EndpointCell.ports,OneBankCell5.ports] using
            (Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective (by decide +kernel))))
        (selected_physical (base 1029) (base 2409) OneFlagSW.swapBody (by decide +kernel) swap))
        (selected.sub.physical rest)
  have e := History5.encode_physical base (skywalkShared_integer_nodup base cfg.1) 0 (by decide)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base cfg.1) 0 (by decide)
  have packet : GatePhysical baseFirstPacket := by
    simpa only [baseFirstPacket,gatePhysical_append] using And.intro (And.intro d body) e
  exact gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ packet

private theorem first_body_slots :
    gateSlots joint1592 + gateSlots (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody) ≤
      gateSlots OneFlagSW.firstSwapS +
        gateSlots (OneFlagSW.cellS true (tapeLetter 1).1.1 (tapeLetter 1).1.2) := by
  decide +kernel

theorem firstPacket_slots_le : gateSlots firstPacket ≤ gateSlots (OneFlagSW.firstPacketS true) := by
  have core := first_body_slots
  have letters : Replay5.restLetters = tapeLetter 1 :: remainingLetters := rfl
  simp only [firstPacket,rename_gateSlots,baseFirstPacket,firstBody,
    OneFlagSW.firstPacketS,OneFlagSW.baseFirstPacketS,OneFlagSW.firstBodyS,if_true,letters,
    OneFlagSW.rawReplayS,gateSlots_append]
  omega
end ECDSAAdd.Entrant.FrontierEntry
