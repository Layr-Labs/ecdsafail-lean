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
  (EntryRetained5.retSites loanPorts (base 1028) (base 1)).image entryLoan
private def packetExtra : Finset Wire := rawExtra.image (shifted (Placement5.pi 0))
private def fieldExtra : Finset Wire := packetExtra.image (OB5.sig 511)
private def hostExtra : Finset Wire := fieldExtra.image HostOB5.hostSwap

private theorem joint_extra : wires joint1593⊆rawExtra := by
  have old : wires (joint loanPorts (base 1028) (base 1))⊆
      EntryRetained5.retSites loanPorts (base 1028) (base 1) := by
    have core:=EntryRetained5.program_support loanPorts (OneBankCell5.ports_widths _ _) _ _
    have x : wires [Instr.X (base 1)]⊆EntryRetained5.retSites loanPorts (base 1028) (base 1) := by
      intro q used
      have eq : q=base 1 := by simpa only [wires,Instr.wires,Finset.union_empty,Finset.mem_singleton] using used
      subst q
      simp [EntryRetained5.retSites]
    simpa only [joint,wires_append,Finset.union_subset_iff] using And.intro (And.intro x core) x
  simpa only [joint1593,renameProgram_support,rawExtra] using Finset.image_subset_image old

private theorem tail_sub :
    wires (SW.selW (base 1029) (base 2410) SW.swapBody ++ SW.rawReplayS true remainingLetters)⊆
      wires (SW.firstBodyS true) := by
  have rest : Replay5.restLetters=tapeLetter 1::remainingLetters := rfl
  have cell : wires (SW.selW (base 1029) (base 2410) SW.swapBody)⊆
      wires (SW.cellS true (base 1) (base 1029)) := by
    intro q used
    simp only [SW.cellS,SW.selW,OneBankCell5.body,if_true,SW.swapBody,
      OneBankCell5.ports_r,OneBankCell5.ports_y,wires_append,Finset.mem_union] at used ⊢
    tauto
  intro q used
  have shape : SW.firstBodyS true=SW.firstSwapS++
      (SW.cellS true (base 1) (base 1029)++SW.rawReplayS true remainingLetters) := by
    simp only [SW.firstBodyS,if_true,rest,SW.rawReplayS,tapeLetter,
      mixedTape_base_getD 1 (by omega),List.append_assoc]
  rw [shape]
  simp only [wires_append,Finset.mem_union] at used ⊢
  rcases used with h|h
  · exact Or.inr (Or.inl (cell h))
  · exact Or.inr (Or.inr h)

private theorem body_sub : wires firstBody⊆wires (SW.firstBodyS true)∪rawExtra := by
  intro q used
  have shape : firstBody=joint1593++
      (SW.selW (base 1029) (base 2410) SW.swapBody++SW.rawReplayS true remainingLetters) := by
    simp only [firstBody,List.append_assoc]
  rw [shape,wires_append] at used
  rcases Finset.mem_union.mp used with h|h
  · exact Finset.mem_union_right _ (joint_extra h)
  · exact Finset.mem_union_left _ (tail_sub h)

private theorem first_sub : wires firstPacket⊆wires (SW.firstPacketS true)∪packetExtra := by
  have baseSub := append_sub _ _ _ _ rawExtra
    (append_sub _ _ _ _ rawExtra (same_sub _ _) body_sub) (same_sub _ _)
  have raw : wires baseFirstPacket⊆wires (SW.baseFirstPacketS true)∪rawExtra := baseSub
  exact rename_sub _ _ _ _ raw

private theorem logical_sub : wires logicalReplay⊆wires (SW.logicalReplayS true)∪packetExtra := by
  have a:=append_sub _ _ _ _ packetExtra first_sub (same_sub (SW.groupsS true 1 101) _)
  simpa only [logicalReplay,SW.logicalReplayS,if_true] using
    append_sub _ _ _ _ packetExtra a (same_sub (SW.endPacketS true) _)

private theorem replay_sub : wires replay⊆wires (SW.replayS true)∪fieldExtra :=
  rename_sub _ _ _ _ logical_sub

private theorem field_sub : wires field5S⊆wires Q5FusionFields.field5S∪fieldExtra :=
  append_sub _ _ _ _ fieldExtra replay_sub (same_sub _ _)

private theorem hosted_sub : wires hostField5S⊆wires Q5FusionFields.hostField5S∪hostExtra :=
  append_sub _ _ _ _ hostExtra (same_sub _ _)
    (append_sub _ _ _ _ hostExtra (rename_sub _ _ _ _ field_sub) (same_sub _ _))

private theorem base_sub : wires baseKernel⊆wires OwnEntryFuseQ5.kernel5S∪hostExtra := by
  simpa only [baseKernel,OwnEntryFuseQ5.kernel5S,Q5FusionPhase.relocated,List.append_assoc] using
    append_sub _ _ _ _ hostExtra (same_sub _ _)
      (append_sub _ _ _ _ hostExtra hosted_sub (same_sub _ _))

private theorem kernel_sub : wires kernel5S⊆wires OwnEntryFuseQ6.kernel5S∪hostExtra := by
  simpa only [kernel5S,OwnEntryFuseQ6.kernel5S,Q6FusionPhase.relocated,List.append_assoc] using
    append_sub _ _ _ _ hostExtra (same_sub _ _)
      (append_sub _ _ _ _ hostExtra hosted_sub (same_sub _ _))

private theorem extra_logical : hostExtra⊆OB5Support.logicalSites := by decide +kernel
private theorem extra_segment : fieldExtra⊆OB5Support.segSites := by decide +kernel
private theorem extra_control : base 2400∉fieldExtra ∧ base 2400∉hostExtra := by decide +kernel
private theorem extra_free : ∀ i∈[2312,766,765,767,1026,1541],base i∉hostExtra := by
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem baseKernel_control_free : base 2400∉wires baseKernel := by
  intro used
  rcases Finset.mem_union.mp (base_sub used) with h|h
  · exact OwnEntryFuseQ5.selKernel5.away h
  · exact extra_control.2 h

theorem field5S_control_free : base 2400∉wires field5S := by
  intro used
  rcases Finset.mem_union.mp (field_sub used) with h|h
  · exact Q5FusionFields.selField5.away h
  · exact extra_control.1 h

theorem field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S := by
  have support : wires field5S⊆OB5Support.segSites := by
    intro q used
    rcases Finset.mem_union.mp (field_sub used) with h|h
    · exact Q5FusionFields.field5S_support h
    · exact extra_segment h
  have off : base 511∉OB5Support.segSites ∧ base 1542∉OB5Support.segSites := by decide +kernel
  exact ⟨fun h=>off.1 (support h),fun h=>off.2 (support h)⟩

theorem hostField5S_1541_free : base 1541∉wires hostField5S := by
  intro used
  rcases Finset.mem_union.mp (hosted_sub used) with h|h
  · exact OwnQ6Actual.entry_selected_free h
  · exact extra_free 1541 (by simp) h

theorem hostField5S_1026_free : base 1026∉wires hostField5S := by
  intro used
  rcases Finset.mem_union.mp (hosted_sub used) with h|h
  · exact Q5FusionFields.hostField5S_free h
  · exact extra_free 1026 (by simp) h

theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites := by
  intro q used
  rcases Finset.mem_union.mp (kernel_sub used) with h|h
  · exact OwnEntryFuseQ6.kernel5S_support h
  · exact extra_logical h

private theorem old_five_free (i : Nat) (hi : i∈[2312,766,765,767,1026]) :
    base i∉wires OwnEntryFuseQ5.kernel5S := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl
  · exact fun h=>OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
      (OwnParityHost.kernel_parity_free true)
      (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub h))
  · exact fun h=>OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
      (OwnPlusFinal.kernel_free true)
      (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub h))
  · exact fun h=>OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
      (OwnGuardFinal.kernel_free true)
      (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub h))
  · exact fun h=>OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
      (OwnMinusFinal.kernel_free true)
      (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub h))
  · exact OwnEntryFuseQ5.kernel5S_1026_free

theorem kernel5S_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
    base i∉wires kernel5S := by
  have old : base i∉wires OwnEntryFuseQ6.kernel5S := by
    by_cases last : i=1541
    · subst i
      exact OwnEntryFuseQ6.kernel5S_1541_free OwnQ6Actual.entry_selected_free
    have five : i∈[2312,766,765,767,1026] := by simpa [last] using hi
    have a : base i≠base 1541 := fun h=>last (base_injective h)
    have b : base i≠base 719 := by
      intro h
      have eq:=base_injective h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at five
      omega
    simpa only [OwnEntryFuseQ6.kernel5S,OwnEntryFuseQ5.kernel5S] using
      Q6FusionGeometry.avoids Q5FusionFields.hostField5S (base i) a b
        (by simpa only [OwnEntryFuseQ5.kernel5S] using old_five_free i five)
  intro used
  rcases Finset.mem_union.mp (kernel_sub used) with h|h
  · exact old h
  · exact extra_free i hi h

end ECDSAAdd.Entrant.FrontierEntryKernel
