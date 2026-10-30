import ECDSAAdd.Submission.Entrant.FrontierEntryFirstSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed
attribute [local irreducible] wires toffoliCount measurementCount

private theorem rest_nodup (l : MixedTranscriptLetter) (hl : l∈remainingLetters) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2410].Nodup := by
  apply SW.selRest_nodup
  change l∈tapeLetter 1::remainingLetters
  exact List.mem_cons_of_mem _ hl

theorem firstBody_control_free : base 2400∉wires firstBody := by
  have raw : base 2400∉wires (joint ports (base 1028) (base 1)) := by
    have off : base 2400∉EntryRetained5.retSites ports (base 1028) (base 1) := by decide +kernel
    have core := EntryRetained5.program_support ports (OneBankCell5.ports_widths _ _) (base 1028) (base 1)
    have unused : base 2400∉wires (EntryRetained5.program ports (base 1028) (base 1)) := fun h=>off (core h)
    have x : base 2400∉wires [Instr.X (base 1)] := by simp [wires,Instr.wires,base]
    simpa only [joint,wires_append,Finset.mem_union,not_or] using And.intro (And.intro x unused) x
  have borrowed : base 2400∉wires joint1593 :=
    OwnPlusHost.rename_avoid entryLoan _ _ (by decide +kernel) raw
  have sw := (((SW.Sel.refl (base 2400) SW.swapBody SW.selSwap_away).window
    (base 1029) (base 2410) false (by decide +kernel))).away
  have tail := (SW.selRaw_sel true remainingLetters rest_nodup).away
  simpa only [firstBody,wires_append,Finset.mem_union,not_or] using And.intro (And.intro borrowed sw) tail

theorem firstPacket_control_free : base 2400∉wires firstPacket := by
  have codec := SW.selHist_away 0 (by omega)
  have raw : base 2400∉wires baseFirstPacket := by
    simpa only [baseFirstPacket,wires_append,Finset.mem_union,not_or] using
      And.intro (And.intro codec.2 firstBody_control_free) codec.1
  exact OwnPlusHost.rename_avoid (shifted (Placement5.pi 0)) _ _ (SW.selShift_fix 0 (by omega)) raw

private theorem swap_nd : (base 2410::(ports.r++ports.y)).Nodup := by
  have hn := MappedCompressed.LaneA.laneLogical_config.1
  have ho : base 2410∉skywalkSharedWires base :=
    MappedCompressed.LaneA.laneLogical_config.2.1 _ (by simp)
  have own : base 2410∉balancedSharedIds.map base := fun h =>
    ho (balancedSharedLayout_mapSubset base balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup base (base 2410) hn own
  have aw := BalancedCircuit.flagAway (balancedSharedPorts base (base 2410)) nd (base 2410)
    (by simp [balancedSharedPorts])
  apply List.nodup_cons.mpr
  refine ⟨?_,balancedSharedLayout_pairND base (base 2410) hn⟩
  intro h
  rcases List.mem_append.mp h with h|h
  · have hr : base 2410∈(balancedSharedPorts base (base 2410)).r := by
      simpa only [ports,OneBankCell5.ports_r,balancedSharedPorts_r] using h
    exact aw (List.mem_append_left _ (List.mem_append_left _ hr))
  · have hy : base 2410∈(balancedSharedPorts base (base 2410)).y := by
      simpa only [ports,OneBankCell5.ports_y,balancedSharedPorts_y] using h
    exact aw (List.mem_append_left _ (List.mem_append_right _ hy))

private theorem selSwap_counts :
    toffoliCount (SW.selW (base 1029) (base 2410) SW.swapBody)=256 ∧
      measurementCount (SW.selW (base 1029) (base 2410) SW.swapBody)=1 := by
  have hw:=OneBankCell5.ports_widths base (base 2409)
  have width:=BalancedCleanup.widths ports.toLayout hw
  have c:=swapRegisters_resources (base 2410) ports.r ports.y
    (width.2.1.trans width.2.2.1.symm) swap_nd
  simp only [SW.selW,SW.swapBody,OneBankCell5.ports_r,OneBankCell5.ports_y,
    toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    c.1,c.2.1,width.2.1]
  norm_num

theorem firstPacket_counts : toffoliCount firstPacket=4875 ∧ measurementCount firstPacket=3590 := by
  have old:=OneBankReplay5.raw_counts true remainingLetters
    swap_nd
  have len : remainingLetters.length=3 := by simp [remainingLetters]
  rw [len] at old
  have selected:=SW.selRaw_sel true remainingLetters rest_nodup
  have selectedT:=selected.tc
  have selectedM:=selected.mc
  have jointC:=joint1593_counts
  have sw:=selSwap_counts
  have ec:=History5.encode_counts base 0
  have dc:=History5.decode_counts base 0
  have placed:=renameProgram_counts (shifted (Placement5.pi 0)) baseFirstPacket
  simp only [firstPacket,placed.1,placed.2,baseFirstPacket,firstBody,
    toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem firstPacket_counts_diff :
    toffoliCount firstPacket+505=toffoliCount (SW.firstPacketS true) ∧
      measurementCount firstPacket+509=measurementCount (SW.firstPacketS true) := by
  have old:=OneBankReplay5.firstPacket_counts true MappedCompressed.LaneA.laneLogical_config.1
    (MappedCompressed.LaneA.laneLogical_config.2.1 _ (by simp))
  have selected:=SW.selFirstPacket_sel true
  have selectedT:=selected.tc
  have selectedM:=selected.mc
  have fresh:=firstPacket_counts
  simp only [if_true] at old
  constructor <;> omega

end ECDSAAdd.Entrant.FrontierEntry
