import ECDSAAdd.Submission.Entrant.FrontierEntryJoint1591Program
import ECDSAAdd.Submission.Entrant.FrontierEntry1591KernelResources

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntryJoint1591
open Arithmetic Secp256k1 BalancedField MappedCompressed DirectSkywalk Challenge Baselines
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

open FrontierEntry (joint1592 loanPorts1592 loanPorts1592_widths remainingLetters joint joint1592_support)

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

private theorem body_sub : wires FrontierEntry.firstBody⊆wires (OneFlagSW.firstBodyS true)∪rawExtra := by
  intro q used
  have shape : FrontierEntry.firstBody=joint1592++
      (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody++OneFlagSW.rawReplayS true remainingLetters) := by
    simp only [FrontierEntry.firstBody,List.append_assoc]
  rw [shape,wires_append] at used
  rcases Finset.mem_union.mp used with h|h
  · exact Finset.mem_union_right _ (joint_extra h)
  · exact Finset.mem_union_left _ (tail_sub h)

private theorem outer_sub (A B P Q : Program) (E : Finset Wire)
    (h : wires P⊆wires Q∪E) : wires (A++(P++B))⊆wires (A++(Q++B))∪E :=
  append_sub A A (P++B) (Q++B) E (same_sub A E)
    (append_sub P Q B B E h (same_sub B E))

private theorem first_sub :
    wires firstPacket⊆wires (FrontierSW1591.firstPacketS true)∪packetExtra := by
  have body : wires FrontierEntry.firstBody⊆wires (FrontierSW1591.firstBodyS true)∪rawExtra := body_sub
  have head:=append_sub (NewHistory5.decode base 0) (NewHistory5.decode base 0)
    FrontierEntry.firstBody (FrontierSW1591.firstBodyS true) rawExtra (same_sub _ _) body
  have raw : wires baseFirstPacket⊆wires (FrontierSW1591.baseFirstPacketS true)∪rawExtra :=
    append_sub _ _ (NewHistory5.encode base 0) (NewHistory5.encode base 0) rawExtra head (same_sub _ _)
  exact rename_sub (shifted (Placement5.pi 0)) _ _ rawExtra raw

private theorem logical_sub :
    wires logicalReplay⊆wires (FrontierSW1591.logicalReplayS true)∪packetExtra := by
  have head:=append_sub firstPacket (FrontierSW1591.firstPacketS true)
    (FrontierSW1591.groupsS true 1 101) (FrontierSW1591.groupsS true 1 101)
    packetExtra first_sub (same_sub _ _)
  exact append_sub _ _ (FrontierSW1591.endPacketS true) (FrontierSW1591.endPacketS true)
    packetExtra head (same_sub _ _)

private theorem replay_sub : wires replay⊆wires (FrontierSW1591.replayS true)∪fieldExtra :=
  rename_sub (OB5.sig 511) _ _ packetExtra logical_sub

private theorem field_sub : wires entryField⊆wires FrontierEntry1591Field.entryField∪fieldExtra :=
  append_sub replay (FrontierSW1591.replayS true) (HalfFieldOB5.copyN++OwnQ5Endpoint.canonT)
    (HalfFieldOB5.copyN++OwnQ5Endpoint.canonT) fieldExtra replay_sub (same_sub _ _)

private theorem hosted_sub : wires entryHosted⊆wires FrontierEntry1591Field.entryHosted∪hostExtra := by
  apply outer_sub
  exact rename_sub HostOB5.hostSwap _ _ fieldExtra field_sub

private def paritySwap : Equiv.Perm Wire :=
  Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host

private def entryExtra : Finset Wire := hostExtra.image paritySwap

private theorem entry_sub : wires entry⊆wires FrontierEntry1591Field.entry∪entryExtra := by
  have h:=rename_sub paritySwap entryHosted FrontierEntry1591Field.entryHosted hostExtra hosted_sub
  have out:=outer_sub (ParityHost5.setup FrontierEntry1591Field.controls FrontierEntry1591Field.host)
    (ParityHost5.setup FrontierEntry1591Field.controls FrontierEntry1591Field.host) _ _ entryExtra h
  simpa only [entry,FrontierEntry1591Field.entry,ParityField1591.program,
    ParityHostTransport5.program,paritySwap,List.append_assoc] using out

private theorem kernel_sub : wires entryKernel⊆wires FrontierEntry1591Kernel.entryKernel∪entryExtra := by
  unfold entryKernel FrontierEntry1591Kernel.entryKernel FrontierEntry1591Native.relocated
  exact outer_sub _ _ _ _ entryExtra entry_sub

private theorem raw_index (q : Wire) (hq : q∈rawExtra) :
    ∃ i, q = base i ∧ (i<2 ∨ (512 ≤ i ∧ i<765) ∨ i=768 ∨ (770 ≤ i ∧ i<1026) ∨
      i=1027 ∨ i=1028 ∨ i=1540 ∨ i=1797 ∨ (2056 ≤ i ∧ i<2312) ∨ i=2409) := by
  have len : (wireBlock base 512 253).length=253 := by simp [wireBlock]
  have take : (wireBlock base 512 253).take 255=wireBlock base 512 253 :=
    List.take_of_length_le (by rw [len]; omega)
  have carry : loanPorts1592.carry.take 255=wireBlock base 512 253++[base 1540,base 1541] := by
    change (wireBlock base 512 253++[base 1540,base 1541,base 1026]).take 255=_
    rw [List.take_append,take,len]
    rfl
  obtain ⟨off,used⟩ := Finset.mem_erase.mp hq
  simp only [Finset.mem_union,Finset.mem_singleton] at used
  rcases used with used|rfl
  · simp only [EntryRetained5.retSites,List.mem_toFinset] at used
    rw [carry] at used
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
      loanPorts1592,wireBlock,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      List.mem_map,List.mem_range'_1] at used
    simp only [or_assoc] at used
    rcases used with rfl|h|rfl|h|rfl|h|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact False.elim (off rfl)
      | exact ⟨_,rfl,by simp only [base] at off; omega⟩
      | obtain ⟨i,hi,eq⟩ := h
        exact ⟨i,eq.symm,by omega⟩
  · exact ⟨0,rfl,by omega⟩

private theorem extra_segment : fieldExtra⊆OB5Support.segSites := by
  intro q used
  obtain ⟨middle,hm,rfl⟩ := Finset.mem_image.mp used
  obtain ⟨old,ho,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨i,rfl,hi⟩ := raw_index old ho
  have avoid (c : Nat) (hc : ¬Placement5.zeroRegion c) (off : i≠c) : Placement5.pi 0 i≠c := by
    intro eq
    exact off ((Placement5.pi 0).injective
      (eq.trans (Placement5.pi_outside 0 c (by decide) hc).symm))
  have frame : (Placement5.pi 0 i<1542 ∧ Placement5.pi 0 i≠511 ∧
      Placement5.pi 0 i≠769 ∧ Placement5.pi 0 i≠1539) ∨ Placement5.pi 0 i=1797 ∨
      (2056≤Placement5.pi 0 i ∧ Placement5.pi 0 i<2312) ∨ Placement5.pi 0 i=2409 := by
    by_cases low : i<1542
    · left
      have bound : Placement5.pi 0 i<1542 := by
        by_contra bad
        have outside : ¬Placement5.zeroRegion (Placement5.pi 0 i) := by
          unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
          omega
        have same := (Placement5.pi 0).injective
          (Placement5.pi_outside 0 (Placement5.pi 0 i) (by decide) outside)
        omega
      refine ⟨bound,avoid 511 ?_ (by omega),avoid 769 ?_ (by omega),avoid 1539 ?_ (by omega)⟩
      all_goals unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega
    · have outside : ¬Placement5.zeroRegion i := by
        unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
        omega
      rw [Placement5.pi_outside 0 i (by decide) outside]
      omega
  have safe := Placement5.nonhole_pi_safe 0 i (by decide) (by
    unfold Placement5.holeRegion
    omega)
  rw [shifted_base,OB5.sig_base 511 _ (by decide)]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨_,?_,rfl⟩
  simp only [OB5Support.segIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  unfold Placement5.omitted at safe
  split_ifs <;> omega

private theorem extra_logical : hostExtra⊆OB5Support.logicalSites := by
  intro q used
  obtain ⟨old,ho,rfl⟩ := Finset.mem_image.mp used
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (extra_segment ho))
  have moved : HostOB5.hostSwap (base i)=base
      (if i=2409 then 511 else if i=511 then 2409 else
        if i=2410 then 1542 else if i=1542 then 2410 else i) := by
    simp only [HostOB5.hostSwap,base,Nat.add_right_cancel_iff]
    split_ifs <;> rfl
  rw [moved]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨_,?_,rfl⟩
  simp only [OB5Support.segIndices,OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  split_ifs <;> omega

private theorem image_off (f : Wire → Wire) (hf : Function.Injective f)
    (S : Finset Wire) (a b : Wire) (off : a∉S) (eq : f a=b) : b∉S.image f := by
  intro used
  obtain ⟨old,ho,he⟩ := Finset.mem_image.mp used
  exact off (hf (he.trans eq.symm) ▸ ho)

private theorem raw_off (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,2410,2400,1538]) :
    base i∉rawExtra := by
  intro used
  obtain ⟨j,eq,hj⟩ := raw_index (base i) used
  have same := base_injective eq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem field_off (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,2410,2400]) :
    base i∉fieldExtra := by
  have pfix : shifted (Placement5.pi 0) (base i)=base i := by
    rw [shifted_base,Placement5.pi_outside 0 i (by decide) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega)]
  have sfix : OB5.sig 511 (base i)=base i := by
    rw [OB5.sig_base 511 i (by decide)]
    congr 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    split_ifs <;> first | rfl | omega
  have packet : base i∉packetExtra :=
    image_off _ (shifted (Placement5.pi 0)).injective rawExtra _ _ (raw_off i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;omega)) pfix
  exact image_off _ (OB5.sig_injective 511 (by decide)) packetExtra _ _ packet sfix

private theorem extra_control : base 2400∉fieldExtra ∧ base 2400∉hostExtra := by
  have off := field_off 2400 (by simp)
  exact ⟨off,image_off _ HostOB5.hostSwap_injective fieldExtra _ _ off OneFlagSW.selHost_fix⟩

private theorem extra_free : ∀ i∈[2312,766,765,767,1026,1541,1542],base i∉hostExtra := by
  intro i hi
  by_cases special : i=1542
  · subst i
    exact image_off _ HostOB5.hostSwap_injective fieldExtra (base 2410) _
      (field_off 2410 (by simp)) (by decide +kernel)
  · have off : base i∉fieldExtra := field_off i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega)
    apply image_off _ HostOB5.hostSwap_injective fieldExtra _ _ off
    simp only [HostOB5.hostSwap,base,Nat.add_right_cancel_iff]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    split_ifs <;> first | rfl | omega


private theorem extra_host_free : FrontierEntry1591Field.host∉hostExtra := by
  have pfix : shifted (Placement5.pi 0) (base 1538)=base 1538 := by
    rw [shifted_base,Placement5.pi_outside 0 1538 (by omega)]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  have packet : base 1538∉packetExtra :=
    image_off _ (shifted (Placement5.pi 0)).injective rawExtra _ _
      (raw_off 1538 (by simp)) pfix
  have field : base 1543∉fieldExtra :=
    image_off _ (OB5.sig_injective 511 (by omega)) packetExtra _ _ packet (by decide +kernel)
  exact image_off _ HostOB5.hostSwap_injective fieldExtra _ _ field (by decide +kernel)

private theorem logical_member (i : Nat) (hi : i∈[1797,1543]) :
    base i∈OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem entryExtra_logical : entryExtra⊆OB5Support.logicalSites := by
  intro q used
  obtain ⟨old,ho,rfl⟩:=Finset.mem_image.mp used
  by_cases work:old=FrontierEntry1591Field.work
  · subst old
    simpa only [paritySwap,Equiv.swap_apply_left] using logical_member 1543 (by simp)
  · by_cases host:old=FrontierEntry1591Field.host
    · exact False.elim (extra_host_free (host ▸ ho))
    · simpa only [paritySwap,Equiv.swap_apply_of_ne_of_ne work host] using extra_logical ho

private theorem entryExtra_free (i : Nat) (hi : i∈FrontierEntry1591Callers.logicalOmissions) :
    base i∉entryExtra := by
  by_cases work:i=1797
  · subst i
    exact image_off paritySwap paritySwap.injective hostExtra _ _ extra_host_free
      (Equiv.swap_apply_right _ _)
  have old : i∈[2312,766,765,767,1026,1541,1542] := by
    simp only [FrontierEntry1591Callers.logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  have host:i≠1543 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at old;omega
  have fix : paritySwap (base i)=base i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact fun eq=>work (base_injective eq)
    · exact fun eq=>host (base_injective eq)
  exact image_off paritySwap paritySwap.injective hostExtra _ _ (extra_free i old) fix

private theorem oldField_support_eq :
    wires FrontierEntry1591Field.entryField=wires OneFlagEntryRaw.field5S := by
  simp only [FrontierEntry1591Field.entryField,OneFlagEntryRaw.field5S,
    wires_append,FrontierSW1591.support_eq]

theorem entryField_support : wires entryField⊆OB5Support.segSites := by
  have old : wires FrontierEntry1591Field.entryField⊆OB5Support.segSites := by
    rw [oldField_support_eq]
    exact OneFlagEntryRaw.selField5.sub.wires_sub.trans OneFlagEntryRaw.field_support
  exact field_sub.trans (Finset.union_subset old extra_segment)

theorem entryField_hosts_free : base 511∉wires entryField ∧ base 1542∉wires entryField :=
  ⟨fun used=>OB5Support.seg_host_free.1 (entryField_support used),
    fun used=>OB5Support.seg_host_free.2 (entryField_support used)⟩

theorem entryField_control_free : base 2400∉wires entryField := by
  intro used
  rcases Finset.mem_union.mp (field_sub used) with h|h
  · rw [oldField_support_eq] at h
    exact OneFlagEntryRaw.selField5.away h
  · exact extra_control.1 h

theorem entryHosted_control_free : base 2400∉wires entryHosted := by
  intro used
  rcases Finset.mem_union.mp (hosted_sub used) with h|h
  · rw [FrontierEntry1591Field.entryHosted_support_eq] at h
    exact OneFlagEntryRaw.selHostField5.away h
  · exact extra_control.2 h

theorem entryHosted_avoids_host : FrontierEntry1591Field.host∉wires entryHosted := by
  intro used
  rcases Finset.mem_union.mp (hosted_sub used) with h|h
  · exact FrontierEntry1591Field.entryHosted_avoids_host h
  · exact extra_host_free h

theorem entry_control_free : base 2400∉wires entry := by
  have noControls : base 2400∉FrontierEntry1591Field.controls := by
    intro used
    obtain ⟨i,eq,bound⟩:=FrontierEntry1591Field.controls_index _ used
    have same:=base_injective eq
    omega
  have fix : paritySwap (base 2400)=base 2400 := by
    apply Equiv.swap_apply_of_ne_of_ne <;> decide +kernel
  have middle : base 2400∉(wires entryHosted).image paritySwap := by
    rw [←renameProgram_support]
    exact OwnPlusHost.rename_avoid paritySwap _ _ fix entryHosted_control_free
  intro used
  rcases Finset.mem_union.mp (ParityField1591.support _ _ _ _ used) with h|h
  · rcases Finset.mem_insert.mp h with h|h
    · exact (show base 2400≠FrontierEntry1591Field.host by decide +kernel) h
    · exact noControls (List.mem_toFinset.mp h)
  · exact middle h

theorem entry_support : wires entry⊆OB5Support.logicalSites :=
  entry_sub.trans (Finset.union_subset FrontierEntry1591Field.entry_support entryExtra_logical)

theorem entry_free (i : Nat) (hi : i∈FrontierEntry1591Callers.logicalOmissions) :
    base i∉wires entry := by
  intro used
  exact (Finset.mem_union.mp (entry_sub used)).elim
    (FrontierEntry1591Field.entry_free i hi) (entryExtra_free i hi)

theorem entryKernel_support : wires entryKernel⊆OB5Support.logicalSites :=
  kernel_sub.trans (Finset.union_subset FrontierEntry1591Kernel.entry_support entryExtra_logical)

theorem entryKernel_free (i : Nat) (hi : i∈FrontierEntry1591Callers.logicalOmissions) :
    base i∉wires entryKernel := by
  intro used
  exact (Finset.mem_union.mp (kernel_sub used)).elim
    (FrontierEntry1591Kernel.entry_free i hi) (entryExtra_free i hi)

end ECDSAAdd.Entrant.FrontierEntryJoint1591
