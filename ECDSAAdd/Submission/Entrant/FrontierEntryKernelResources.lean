import ECDSAAdd.Submission.Entrant.FrontierEntryKernelProgram
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstResources

/-! Only the new entry's finite site image extends the old support proof. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntryKernel
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5 FrontierEntry
attribute [local irreducible] wires

private theorem same_sub (P : Program) (E : Finset Wire) : wires P⊆wires P∪E :=
  Finset.subset_union_left

private theorem append_sub (P P' Q Q' : Program) (E : Finset Wire)
    (hp : wires P⊆wires P'∪E) (hq : wires Q⊆wires Q'∪E) :
    wires (P++Q)⊆wires (P'++Q')∪E := by
  intro q used
  simp only [wires_append,Finset.mem_union] at used ⊢
  rcases used with h|h
  · have x:=hp h
    simp only [Finset.mem_union] at x
    tauto
  · have x:=hq h
    simp only [Finset.mem_union] at x
    tauto

private theorem rename_sub (f : Wire → Wire) (P P' : Program) (E : Finset Wire)
    (hp : wires P⊆wires P'∪E) :
    wires (renameProgram f P)⊆wires (renameProgram f P')∪E.image f := by
  simpa only [renameProgram_support,Finset.image_union] using Finset.image_subset_image hp

private def rawExtra : Finset Wire :=
  (EntryRetained5.retSites loanPorts1592 (base 1028) (base 1)∪{base 0}).erase (base 1541)
private def packetExtra : Finset Wire := rawExtra.image (shifted (Placement5.pi 0))
private def fieldExtra : Finset Wire := packetExtra.image (OB5.sig 511)
private def hostExtra : Finset Wire := fieldExtra.image HostOB5.hostSwap

private theorem joint_extra : wires joint1592⊆rawExtra := by
  let S:=EntryRetained5.retSites loanPorts1592 (base 1028) (base 1)∪{base 0}
  have core : wires (EntryRetained5.program loanPorts1592 (base 1028) (base 1))⊆S :=
    (EntryRetained5.program_support loanPorts1592 loanPorts1592_widths (base 1028) (base 1)).trans Finset.subset_union_left
  have x : wires [Instr.X (base 1)]⊆S := by
    intro q used
    have eq : q=base 1 := by simpa [wires,Instr.wires] using used
    subst q
    apply Finset.mem_union_left
    simp [EntryRetained5.retSites]
  have old : wires (joint loanPorts1592 (base 1028) (base 1))⊆S := by
    rw [joint,wires_append,wires_append]
    exact Finset.union_subset (Finset.union_subset x core) x
  exact joint1592_support S old (by simp [S,EntryRetained5.retSites]) (by simp [S])

private theorem tail_sub :
    wires (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody ++ OneFlagSW.rawReplayS true remainingLetters)⊆
      wires (OneFlagSW.firstBodyS true) := by
  have rest : Replay5.restLetters=tapeLetter 1::remainingLetters := rfl
  have cell : wires (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)⊆
      wires (OneFlagSW.cellS true (base 1) (base 1029)) := by
    intro q used
    simp only [OneFlagSW.cellS,if_true,wires_append,Finset.mem_union]
    exact Or.inr used
  intro q used
  have shape : OneFlagSW.firstBodyS true=OneFlagSW.firstSwapS++
      (OneFlagSW.cellS true (base 1) (base 1029)++OneFlagSW.rawReplayS true remainingLetters) := by
    simp only [OneFlagSW.firstBodyS,if_true,rest,OneFlagSW.rawReplayS,tapeLetter,
      mixedTape_base_getD 1 (by omega),List.append_assoc]
  rw [shape]
  simp only [wires_append,Finset.mem_union] at used ⊢
  rcases used with h|h
  · exact Or.inr (Or.inl (cell h))
  · exact Or.inr (Or.inr h)

private theorem body_sub : wires firstBody⊆wires (OneFlagSW.firstBodyS true)∪rawExtra := by
  intro q used
  have shape : firstBody=joint1592++
      (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody++OneFlagSW.rawReplayS true remainingLetters) := by
    simp only [firstBody,List.append_assoc]
  rw [shape,wires_append] at used
  rcases Finset.mem_union.mp used with h|h
  · exact Finset.mem_union_right _ (joint_extra h)
  · exact Finset.mem_union_left _ (tail_sub h)

private theorem outer_sub (A B P Q : Program) (E : Finset Wire)
    (h : wires P⊆wires Q∪E) : wires (A++(P++B))⊆wires (A++(Q++B))∪E :=
  append_sub A A (P++B) (Q++B) E (same_sub A E)
    (append_sub P Q B B E h (same_sub B E))

private theorem first_sub : wires firstPacket⊆wires (OneFlagSW.firstPacketS true)∪packetExtra := by
  have head : wires (History5.decode base 0++firstBody)⊆
      wires (History5.decode base 0++OneFlagSW.firstBodyS true)∪rawExtra :=
    append_sub (History5.decode base 0) (History5.decode base 0) firstBody
      (OneFlagSW.firstBodyS true) rawExtra (same_sub _ _) body_sub
  have raw : wires baseFirstPacket⊆wires (OneFlagSW.baseFirstPacketS true)∪rawExtra :=
    append_sub (History5.decode base 0++firstBody) (History5.decode base 0++OneFlagSW.firstBodyS true)
      (History5.encode base 0) (History5.encode base 0) rawExtra head (same_sub _ _)
  exact rename_sub (shifted (Placement5.pi 0)) baseFirstPacket (OneFlagSW.baseFirstPacketS true) rawExtra raw

private theorem logical_sub : wires logicalReplay⊆wires (OneFlagSW.logicalReplayS true)∪packetExtra := by
  have head : wires (firstPacket++OneFlagSW.groupsS true 1 101)⊆
      wires (OneFlagSW.firstPacketS true++OneFlagSW.groupsS true 1 101)∪packetExtra :=
    append_sub firstPacket (OneFlagSW.firstPacketS true) (OneFlagSW.groupsS true 1 101)
      (OneFlagSW.groupsS true 1 101) packetExtra first_sub (same_sub _ _)
  exact append_sub _ _ (OneFlagSW.endPacketS true) (OneFlagSW.endPacketS true)
    packetExtra head (same_sub _ _)

private theorem replay_sub : wires replay⊆wires (OneFlagSW.replayS true)∪fieldExtra :=
  rename_sub (OB5.sig 511) logicalReplay (OneFlagSW.logicalReplayS true) packetExtra logical_sub

private theorem field_sub : wires field5S⊆wires OneFlagEntryRaw.field5S∪fieldExtra :=
  append_sub replay (OneFlagSW.replayS true) (HalfFieldOB5.copyN++OwnQ5Endpoint.canonT)
    (HalfFieldOB5.copyN++OwnQ5Endpoint.canonT) fieldExtra replay_sub (same_sub _ _)

private theorem hosted_sub : wires hostField5S⊆wires OneFlagEntryRaw.hostField5S∪hostExtra := by
  apply outer_sub
  exact rename_sub HostOB5.hostSwap field5S OneFlagEntryRaw.field5S fieldExtra field_sub

private theorem base_sub : wires baseKernel⊆wires OneFlagEntryQ5.kernel5S∪hostExtra := by
  unfold baseKernel OneFlagEntryQ5.kernel5S Q5FusionPhase.relocated
  exact outer_sub _ _ _ _ hostExtra hosted_sub

private theorem kernel_sub : wires kernel5S⊆wires OwnOneFlagEntryQ7.kernel5S∪hostExtra := by
  unfold kernel5S OwnOneFlagEntryQ7.kernel5S Q7FusionPhase.relocated
  exact outer_sub _ _ _ _ hostExtra hosted_sub

private theorem extra_logical : hostExtra⊆OB5Support.logicalSites := by decide +kernel
private theorem extra_segment : fieldExtra⊆OB5Support.segSites := by decide +kernel
private theorem extra_control : base 2400∉fieldExtra ∧ base 2400∉hostExtra := by decide +kernel
private theorem extra_free : ∀ i∈[2312,766,765,767,1026,1541,1542],base i∉hostExtra := by
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem baseKernel_control_free : base 2400∉wires baseKernel := by
  intro used
  rcases Finset.mem_union.mp (base_sub used) with h|h
  · have old : base 2400∉wires OneFlagEntryQ5.kernel5S := by
      simp only [OneFlagEntryQ5.kernel5S,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or]
      exact ⟨OwnQ5SW.renamed_first_away,OneFlagEntryRaw.selHostField5.away,OwnQ5SW.renamed_last_away⟩
    exact old h
  · exact extra_control.2 h

theorem field5S_control_free : base 2400∉wires field5S := by
  intro used
  rcases Finset.mem_union.mp (field_sub used) with h|h
  · exact OneFlagEntryRaw.selField5.away h
  · exact extra_control.1 h

theorem field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S := by
  have support : wires field5S⊆OB5Support.segSites := by
    intro q used
    rcases Finset.mem_union.mp (field_sub used) with h|h
    · exact Q6EndpointEntryRaw.field_support
        (OneFlagEntrySupport.field_subset (OneFlagEntryRaw.selField5.sub.wires_sub h))
    · exact extra_segment h
  have off : base 511∉OB5Support.segSites ∧ base 1542∉OB5Support.segSites := by decide +kernel
  exact ⟨fun h=>off.1 (support h),fun h=>off.2 (support h)⟩

theorem hostField5S_1541_free : base 1541∉wires hostField5S := by
  intro used
  rcases Finset.mem_union.mp (hosted_sub used) with h|h
  · exact OneFlagEntryQ6.hostField5S_free1541 h
  · exact extra_free 1541 (by simp) h

theorem hostField5S_1026_free : base 1026∉wires hostField5S := by
  intro used
  rcases Finset.mem_union.mp (hosted_sub used) with h|h
  · exact OneFlagEntryQ5.hostField5S_free h
  · exact extra_free 1026 (by simp) h

theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites := by
  intro q used
  rcases Finset.mem_union.mp (kernel_sub used) with h|h
  · exact OwnOneFlagEntryQ7.kernel5S_support h
  · exact extra_logical h

theorem hostField5S_1542_free : base 1542∉wires hostField5S := by
  intro used
  rcases Finset.mem_union.mp (hosted_sub used) with h|h
  · exact OwnOneFlagEntryQ7.hostField5S_free1542 h
  · exact extra_free 1542 (by simp) h

theorem kernel5S_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
    base i∉wires kernel5S := by
  intro used
  rcases Finset.mem_union.mp (kernel_sub used) with h|h
  · exact OneFlagEntryOmissions.kernel_free7 i hi h
  · exact extra_free i hi h

end ECDSAAdd.Entrant.FrontierEntryKernel
