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
  have pair := OneBankReplay5.swap_nodup cfg.1 (cfg.2.1 _ (by simp))
  have swap : GatePhysical SW.swapBody := by
    simpa only [SW.swapBody] using swapRegisters_physical _ _ _ pair
  have selected := SW.selRaw_sel true remainingLetters
    (fun l hl => SW.selRest_nodup l (remaining_mem l hl))
  have rest := OneBankReplay5.raw_physical true remainingLetters cfg.1 cfg.2.1
    (fun l hl => OneBankReplay5.rest_layout cfg.2.2 l (remaining_mem l hl))
  have body : GatePhysical firstBody := by
    simpa only [firstBody,gatePhysical_append] using
      And.intro (And.intro joint1593_physical
        (selected_physical (base 1029) (base 2410) SW.swapBody (by decide +kernel) swap))
        (selected.sub.physical rest)
  have e := History5.encode_physical base (skywalkShared_integer_nodup base cfg.1) 0 (by decide)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base cfg.1) 0 (by decide)
  have packet : GatePhysical baseFirstPacket := by
    simpa only [baseFirstPacket,gatePhysical_append] using And.intro (And.intro d body) e
  exact gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ packet

private theorem first_body_slots :
    gateSlots joint1593 + gateSlots (SW.selW (base 1029) (base 2410) SW.swapBody) ≤
      gateSlots SW.firstSwapS +
        gateSlots (SW.cellS true (tapeLetter 1).1.1 (tapeLetter 1).1.2) := by
  decide +kernel

theorem firstPacket_slots_le : gateSlots firstPacket ≤ gateSlots (SW.firstPacketS true) := by
  have core := first_body_slots
  have letters : Replay5.restLetters = tapeLetter 1 :: remainingLetters := rfl
  simp only [firstPacket,rename_gateSlots,baseFirstPacket,firstBody,
    SW.firstPacketS,SW.baseFirstPacketS,SW.firstBodyS,if_true,letters,
    SW.rawReplayS,gateSlots_append]
  omega
end ECDSAAdd.Entrant.FrontierEntry
