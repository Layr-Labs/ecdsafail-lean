import ECDSAAdd.Submission.Entrant.FrontierEntryFirstProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed

private theorem ports_field_sites :
    (ports.r++ports.y++ports.carry++[ports.parity,ports.lower,ports.one,ports.sign]).toFinset ⊆
      OneFlagReplay.fieldSites := by
  intro q hq
  simp only [ports,loanPorts1592,Q6EndpointCell.ids,OneFlagReplay.fieldSites,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    wireBlock,List.map_append,List.map_cons,List.map_nil,List.mem_toFinset,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  tauto

private theorem sel_support (source flag : Wire) (P : Program) (W : Finset Wire)
    (hs : source∈W) (hf : flag∈W) (hp : wires P⊆W) :
    wires (SW.selW source flag P)⊆W := by
  have head : wires [Instr.CX source flag]⊆W := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    rcases hq with rfl|rfl <;> assumption
  have tail : wires [Instr.measureX flag [] [Correction.Z source]]⊆W := by
    intro q hq
    simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,List.toFinset_cons,List.toFinset_nil,
      List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,Finset.union_empty,
      Finset.empty_union,or_false] at hq
    rcases hq with rfl|rfl <;> assumption
  simpa only [SW.selW,wires_append,Finset.union_subset_iff] using ⟨⟨head,hp⟩,tail⟩

theorem firstBody_support : wires firstBody⊆OneFlagReplay.readSites 0 := by
  let W := OneFlagReplay.readSites 0
  have hi : OneFlagReplay.fieldSites⊆W := fun _ h =>
    Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hb : base 2400∈W := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  have he : base 2410∈W := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  have js : base 1028∈W := Finset.mem_union_right _ (by
    simpa using (Replay5.history_controls 0 0 (by decide)).2)
  have gg : base 1∈W := Finset.mem_union_right _ (by
    simpa using (Replay5.history_controls 0 1 (by decide)).1)
  have ss : base 1029∈W := Finset.mem_union_right _ (by
    simpa using (Replay5.history_controls 0 1 (by decide)).2)
  have data (q : Wire)
      (hq : q∈ports.r++ports.y++ports.carry++[ports.parity,ports.lower,ports.one,ports.sign]) : q∈W :=
    hi (ports_field_sites (List.mem_toFinset.mpr hq))
  have retained : EntryRetained5.retSites ports (base 1028) (base 1)⊆W := by
    intro q hq
    simp only [EntryRetained5.retSites,List.mem_toFinset,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with hr|hy|hc|rfl|rfl|rfl|rfl|rfl|rfl
    · exact data q (by simp [hr])
    · exact data q (by simp [hy])
    · exact data q (by simp [List.mem_of_mem_take hc])
    · exact data _ (by simp)
    · exact data _ (by simp)
    · exact data _ (by simp)
    · exact data _ (by simp)
    · exact js
    · exact gg
  have primitive := (EntryRetained5.program_support ports ports_widths _ _).trans retained
  have xg : wires [Instr.X (base 1)]⊆W := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simpa only [hq] using gg
  have jointW : wires (joint ports (base 1028) (base 1))⊆W := by
    simpa only [joint,wires_append,Finset.union_subset_iff] using ⟨⟨xg,primitive⟩,xg⟩
  have hsign : base 2409∈W := hi (by simp [OneFlagReplay.fieldSites])
  have rawSwap : wires OneFlagSW.swapBody⊆W := by
    have sub : wires OneFlagSW.swapBody⊆wires (Q6EndpointCell.body true base (base 2409) (base 2409)) := by
      simp only [OneFlagSW.swapBody,Q6EndpointCell.body,if_true,wires_append,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y]
      exact Finset.subset_union_right
    exact sub.trans (Q6EndpointCell.body_support true base (base 2409) (base 2409) W hi hsign)
  have swapW := sel_support (base 1029) (base 2409) OneFlagSW.swapBody W ss hsign rawSwap
  have gzero : base 0∈W := Finset.mem_union_right _ (by
    simpa using (Replay5.history_controls 0 0 (by decide)).1)
  have borrowed : wires joint1592⊆W :=
    (joint1592_support W jointW js gzero).trans (Finset.erase_subset _ _)
  have restMem : ∀l∈remainingLetters,l∈Replay5.restLetters := by
    intro l hl
    change l∈tapeLetter 1::remainingLetters
    exact List.mem_cons_of_mem _ hl
  have selected := OneFlagSW.selRaw_sel true remainingLetters (fun l hl=>OneFlagSW.selRest_nodup l (restMem l hl))
  have oldRest : wires (OneFlagReplay.rawReplay true remainingLetters)⊆W := by
    apply OneFlagReplay.raw_support true remainingLetters W hi hb he
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    have bound := List.mem_range'_1.mp hk
    have tape := mixedTape_base_getD k (by omega)
    have controls := Replay5.history_controls 0 k (by omega)
    simp only [Nat.zero_add] at controls
    simpa only [tapeLetter,tape] using
      (show base k∈W ∧ base (1028+k)∈W from
        ⟨Finset.mem_union_right _ controls.1,Finset.mem_union_right _ controls.2⟩)
  have restW := selected.sub.wires_sub.trans oldRest
  simpa only [firstBody,wires_append,Finset.union_subset_iff] using ⟨⟨borrowed,swapW⟩,restW⟩

theorem firstBody_read_support : wires firstBody⊆
    History5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
  firstBody_support.trans (OneFlagReplay.readSites_sub 0)

end ECDSAAdd.Entrant.FrontierEntry
