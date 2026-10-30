import ECDSAAdd.Submission.Entrant.FrontierEntry1591KernelProgram
import ECDSAAdd.Submission.Entrant.FrontierEntry1591FieldResources
import ECDSAAdd.Submission.Entrant.ParityInverseResources
import ECDSAAdd.Submission.Entrant.FrontierEntry1591CallerResources

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic Secp256k1 Challenge Baselines MappedCompressed DirectSkywalk
open FrontierEntry1591Callers
attribute [local irreducible] wires run toffoliCount measurementCount gateSlots

theorem first_metrics :
    toffoliCount firstPhase=toffoliCount Q5Global718.firstPhase ∧
    measurementCount firstPhase=measurementCount Q5Global718.firstPhase ∧
    gateSlots firstPhase=gateSlots Q5Global718.firstPhase+204 := by
  have n := FrontierEntry1591Native.counts base
  have o := NativeFirstDirect.forward_counts base
  have s := FrontierEntry1591Native.slots base
  have f := NewStackOB5.stackForwardT_counts
  simp only [firstPhase,Q5Global718.firstPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem last_metrics :
    toffoliCount lastPhase=toffoliCount Q5Global718.lastPhase ∧
    measurementCount lastPhase=measurementCount Q5Global718.lastPhase ∧
    gateSlots lastPhase=gateSlots Q5Global718.lastPhase+204 := by
  have n := FrontierEntry1591Native.counts base
  have o := NativeFirstKnown.inverse_counts base
  have s := FrontierEntry1591Native.slots base
  have r := NewStackOB5.stackReverseT_counts
  have rs := NewStackOB5.stackReverseT_slots
  simp only [lastPhase,Q5Global718.lastPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem relocated_counts_eq (F Old : Program)
    (fc : toffoliCount F=toffoliCount Old ∧ measurementCount F=measurementCount Old) :
    toffoliCount (FrontierEntry1591Native.relocated firstPhase F lastPhase)=
      toffoliCount (Q7FusionPhase.relocated Old) ∧
    measurementCount (FrontierEntry1591Native.relocated firstPhase F lastPhase)=
      measurementCount (Q7FusionPhase.relocated Old) := by
  have a := FrontierEntry1591Native.relocated_counts firstPhase F lastPhase
  have b := OneFlagEntryResources.outer_counts Old
  have f := first_metrics
  have r := last_metrics
  simp only [FrontierEntry1591Native.kernel,Q5FusionPhase.kernel,
    toffoliCount_append,measurementCount_append] at a b
  exact ⟨by omega,by omega⟩

private theorem relocated_slots_eq (F Old : Program)
    (fs : gateSlots F=gateSlots Old+2040) :
    gateSlots (FrontierEntry1591Native.relocated firstPhase F lastPhase)=
      gateSlots (Q7FusionPhase.relocated Old)+2448 := by
  have a := FrontierEntry1591Native.relocated_slots firstPhase F lastPhase
  have b := OneFlagEntryResources.outer_slots Old
  have f := first_metrics
  have r := last_metrics
  simp only [FrontierEntry1591Native.kernel,Q5FusionPhase.kernel,gateSlots_append] at a b
  omega

theorem entry_counts_eq :
    toffoliCount entryKernel=toffoliCount OwnOneFlagEntryQ7.kernel5S ∧
    measurementCount entryKernel=measurementCount OwnOneFlagEntryQ7.kernel5S :=
  relocated_counts_eq FrontierEntry1591Field.entry OneFlagEntryRaw.hostField5S
    FrontierEntry1591Field.entry_counts_eq

theorem exit_counts_eq :
    toffoliCount exitKernel=toffoliCount OwnOneFlagExitQ7.kernelS ∧
    measurementCount exitKernel=measurementCount OwnOneFlagExitQ7.kernelS :=
  relocated_counts_eq FrontierEntry1591Field.exit OneFlagExitRaw.hostMulS
    FrontierEntry1591Field.exit_counts_eq

theorem entry_slots_eq :
    gateSlots entryKernel=gateSlots OwnOneFlagEntryQ7.kernel5S+2448 := by
  have shape : entryKernel=FrontierEntry1591Native.relocated firstPhase
      FrontierEntry1591Field.entry lastPhase := rfl
  have old : Q7FusionPhase.relocated OneFlagEntryRaw.hostField5S=OwnOneFlagEntryQ7.kernel5S := rfl
  exact (congrArg gateSlots shape).trans
    ((relocated_slots_eq FrontierEntry1591Field.entry OneFlagEntryRaw.hostField5S
      FrontierEntry1591Field.entry_slots).trans (congrArg (fun P : Program => gateSlots P+2448) old))

theorem exit_slots_eq :
    gateSlots exitKernel=gateSlots OwnOneFlagExitQ7.kernelS+2448 := by
  have shape : exitKernel=FrontierEntry1591Native.relocated firstPhase
      FrontierEntry1591Field.exit lastPhase := rfl
  have old : Q7FusionPhase.relocated OneFlagExitRaw.hostMulS=OwnOneFlagExitQ7.kernelS := rfl
  exact (congrArg gateSlots shape).trans
    ((relocated_slots_eq FrontierEntry1591Field.exit OneFlagExitRaw.hostMulS
      FrontierEntry1591Field.exit_slots).trans (congrArg (fun P : Program => gateSlots P+2448) old))

theorem entry_slots : gateSlots entryKernel≤20502454 := by
  have h := entry_slots_eq
  have old := OwnOneFlagEntryQ7.kernel5S_slots_le
  omega

theorem exit_slots : gateSlots exitKernel≤20502454 := by
  have h := exit_slots_eq
  have old := OwnOneFlagExitQ7.kernelS_slots_le
  omega

theorem first_support : wires firstPhase⊆OB5Support.logicalSites := by
  have n := FrontierEntry1591Native.native_support_logical.1
  have f := NewStackOB5.stackForwardT_subset.trans
    (StackOB5.forward_support.trans OB5Support.integer_sub_logical)
  have c := OB5Support.clear_support_logical
  simpa only [firstPhase,wires_append,Finset.union_subset_iff] using ⟨n,f,c⟩

theorem last_support : wires lastPhase⊆OB5Support.logicalSites := by
  have n := FrontierEntry1591Native.native_support_logical.2
  have r := NewStackOB5.stackReverseT_subset.trans
    (StackOB5.reverse_support.trans OB5Support.integer_sub_logical)
  have c := OB5Support.clear_support_logical
  simpa only [lastPhase,wires_append,Finset.union_subset_iff] using ⟨c,r,n⟩

theorem entry_support : wires entryKernel⊆OB5Support.logicalSites := by
  have f := FrontierEntry1591Native.hosted_support_logical _ first_support
  have r := FrontierEntry1591Native.hosted_support_logical _ last_support
  simpa only [entryKernel,FrontierEntry1591Native.relocated,wires_append,
    Finset.union_subset_iff] using ⟨f,FrontierEntry1591Field.entry_support,r⟩

theorem exit_support : wires exitKernel⊆OB5Support.logicalSites := by
  have f := FrontierEntry1591Native.hosted_support_logical _ first_support
  have r := FrontierEntry1591Native.hosted_support_logical _ last_support
  simpa only [exitKernel,FrontierEntry1591Native.relocated,wires_append,
    Finset.union_subset_iff] using ⟨f,FrontierEntry1591Field.exit_support,r⟩

theorem first_physical : GatePhysical firstPhase := by
  simpa only [firstPhase,gatePhysical_append] using
    And.intro (FrontierEntry1591Native.physical base base_pool_nodup).1
      (And.intro NewStackOB5.stackForwardT_physical mappedClear_physical)

theorem last_physical : GatePhysical lastPhase := by
  simpa only [lastPhase,gatePhysical_append] using
    And.intro mappedClear_physical
      (And.intro NewStackOB5.stackReverseT_physical
        (FrontierEntry1591Native.physical base base_pool_nodup).2)

theorem entry_physical : GatePhysical entryKernel := by
  apply FrontierEntry1591Native.relocated_physical firstPhase FrontierEntry1591Field.entry lastPhase
  simpa only [FrontierEntry1591Native.kernel,gatePhysical_append] using
    And.intro first_physical (And.intro FrontierEntry1591Field.entry_physical last_physical)

theorem exit_physical : GatePhysical exitKernel := by
  apply FrontierEntry1591Native.relocated_physical firstPhase FrontierEntry1591Field.exit lastPhase
  simpa only [FrontierEntry1591Native.kernel,gatePhysical_append] using
    And.intro first_physical (And.intro FrontierEntry1591Field.exit_physical last_physical)

private def phaseOmissions : List Nat := [2312,766,765,767,718,719,720,1797]

private theorem native_sites_free (i : Nat) (hi : i∈phaseOmissions) :
    base i∉FrontierEntry1591Native.sites base := by
  intro h
  simp only [phaseOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  simp only [FrontierEntry1591Native.sites,Finset.mem_erase,Finset.mem_insert,
    List.mem_toFinset,NativeFirstDirect.prefixSites,List.mem_append,wireBlock,
    List.mem_map,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false,
    base_injective.eq_iff] at h
  simp only [exists_eq_right] at h
  have ne : i≠1797 := fun e => h.1 (congrArg base e)
  omega

private theorem integer_sites_free (i : Nat) (hi : i∈phaseOmissions) :
    base i∉OB5.integerSites := by
  intro h
  obtain ⟨j,e,hj⟩ := (OB5.integerSites_mem _).mp h
  have eq := base_injective e
  simp only [phaseOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem clear_free (i : Nat) (hi : i∈phaseOmissions) :
    base i∉wires (skywalkArithmeticClear base) := by
  simp only [phaseOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]

private theorem first_free (i : Nat) (hi : i∈phaseOmissions) : base i∉wires firstPhase := by
  have n := fun h => native_sites_free i hi ((FrontierEntry1591Native.support base base_pool_nodup).1 h)
  have f := fun h => integer_sites_free i hi
    (StackOB5.forward_support (NewStackOB5.stackForwardT_subset h))
  simpa only [firstPhase,wires_append,Finset.mem_union,not_or] using ⟨n,f,clear_free i hi⟩

private theorem last_free (i : Nat) (hi : i∈phaseOmissions) : base i∉wires lastPhase := by
  have n := fun h => native_sites_free i hi ((FrontierEntry1591Native.support base base_pool_nodup).2 h)
  have r := fun h => integer_sites_free i hi
    (StackOB5.reverse_support (NewStackOB5.stackReverseT_subset h))
  simpa only [lastPhase,wires_append,Finset.mem_union,not_or] using ⟨clear_free i hi,r,n⟩

theorem first_host_free (q : Wire) (hq : q∈FrontierEntry1591Native.hostSites) :
    q∉wires firstPhase := by
  simp only [FrontierEntry1591Native.hostSites,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact first_free 718 (by simp [phaseOmissions])
  · exact first_free 719 (by simp [phaseOmissions])
  · exact first_free 720 (by simp [phaseOmissions])

theorem last_host_free (q : Wire) (hq : q∈FrontierEntry1591Native.hostSites) :
    q∉wires lastPhase := by
  simp only [FrontierEntry1591Native.hostSites,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact last_free 718 (by simp [phaseOmissions])
  · exact last_free 719 (by simp [phaseOmissions])
  · exact last_free 720 (by simp [phaseOmissions])

private theorem hosted_free (P : Program) (free : ∀i∈phaseOmissions,base i∉wires P)
    (i : Nat) (hi : i∈logicalOmissions) :
    base i∉wires (FrontierEntry1591Native.hosted P) := by
  have lift (j : Nat) (hj : j∈phaseOmissions)
      (mapped : FrontierEntry1591Native.acceptedSwap (base j)=base i) :
      base i∉wires (FrontierEntry1591Native.hosted P) := by
    intro h
    rw [FrontierEntry1591Native.hosted_support] at h
    obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
    exact free j hj ((FrontierEntry1591Native.acceptedSwap.injective (e.trans mapped.symm)) ▸ hq)
  simp only [logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lift 2312 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 766 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 765 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 767 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 718 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 719 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 720 (by simp [phaseOmissions]) (by decide +kernel)
  · exact lift 1797 (by simp [phaseOmissions]) (by decide +kernel)

theorem entry_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires entryKernel := by
  simpa only [entryKernel,FrontierEntry1591Native.relocated,wires_append,
    Finset.mem_union,not_or] using
    And.intro (hosted_free firstPhase first_free i hi)
      (And.intro (FrontierEntry1591Field.entry_free i hi) (hosted_free lastPhase last_free i hi))

theorem exit_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires exitKernel := by
  simpa only [exitKernel,FrontierEntry1591Native.relocated,wires_append,
    Finset.mem_union,not_or] using
    And.intro (hosted_free firstPhase first_free i hi)
      (And.intro (FrontierEntry1591Field.exit_free i hi) (hosted_free lastPhase last_free i hi))

end ECDSAAdd.Entrant.FrontierEntry1591Kernel
