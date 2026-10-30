import ECDSAAdd.Submission.Entrant.FrontierEntry1591Callers
import ECDSAAdd.Submission.Entrant.ParityPointResources

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Callers
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount

def logicalOmissions : List Nat := [2312,766,765,767,1026,1541,1542,1797]

theorem placed_physical (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kp : GatePhysical K) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (renameProgram (wireFn2 L) K) := by
  apply gatePhysical_rename_support (wireFn2 L) K
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (ks ha))
      b (ArithmeticOB5.logical_sub_old (ks hb)) eq
  · exact kp

theorem division_support (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (division K L k)⊆(OB5Support.sites L).toFinset := by
  simp only [division,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    entry_support K ks L hw⟩

theorem exit_support (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (L : ControlledPointLayout) (hw : L.Widths) :
    wires (exit K L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ ks

theorem division_physical (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kp : GatePhysical K) (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (division K L k) := by
  simp only [division,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,placed_physical K ks kp L hw hn⟩

theorem division_counts_eq (K : Program)
    (kc : toffoliCount K=toffoliCount OwnOneFlagEntryQ7.kernel5S ∧
      measurementCount K=measurementCount OwnOneFlagEntryQ7.kernel5S)
    (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (division K L k)=toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF L k) ∧
      measurementCount (division K L k)=measurementCount (OwnOneFlagEntryQ7.fusedDivisionF L k) := by
  simp only [division,entry,OwnOneFlagEntryQ7.fusedDivisionF,OwnOneFlagEntryQ7.arithEntryS,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  exact ⟨congrArg _ kc.1,congrArg _ kc.2⟩

theorem exit_counts_eq (K : Program)
    (kc : toffoliCount K=toffoliCount OwnOneFlagExitQ7.kernelS ∧
      measurementCount K=measurementCount OwnOneFlagExitQ7.kernelS)
    (L : ControlledPointLayout) :
    toffoliCount (exit K L)=toffoliCount (OwnOneFlagExitQ7.arithExit L) ∧
      measurementCount (exit K L)=measurementCount (OwnOneFlagExitQ7.arithExit L) := by
  simpa only [exit,OwnOneFlagExitQ7.arithExit,renameProgram_counts] using kc

theorem exit_slots (K : Program) (ks : gateSlots K≤20502454) (L : ControlledPointLayout) :
    gateSlots (exit K L)≤20502454 := by
  simpa only [exit,rename_gateSlots] using ks

theorem division_slots (K : Program) (ks : gateSlots K≤20502454)
    (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    gateSlots (division K L k)≤20527454 := by
  have y:=entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
  simp only [division,entry,EntryFuse.fusedY,gateSlots_append,rename_gateSlots]
  omega

private theorem logical_site (i : Nat) (hi : i∈logicalOmissions) :
    base i∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  simp only [logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem placed_free (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (i k : Nat)
    (hi : base i∈OB5Support.logicalSites) (hm : wireFn2 L (base i)=L.core.poolWire k)
    (free : base i∉wires K) : L.core.poolWire k∉wires (renameProgram (wireFn2 L) K) := by
  rw [renameProgram_support]
  intro h
  obtain ⟨old,used,eq⟩ := Finset.mem_image.mp h
  have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
  have back := (placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (ks used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
  exact free (back ▸ used)

theorem placed_omissions (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kf : ∀i∈logicalOmissions,base i∉wires K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈Q1591Resources.genericOmissions) :
    L.core.poolWire k∉wires (renameProgram (wireFn2 L) K) := by
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact placed_free K ks L hw hn 2312 1800 (logical_site 2312 (by simp [logicalOmissions]))
      rfl (kf 2312 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 766 766 (logical_site 766 (by simp [logicalOmissions]))
      rfl (kf 766 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 765 765 (logical_site 765 (by simp [logicalOmissions]))
      rfl (kf 765 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 767 767 (logical_site 767 (by simp [logicalOmissions]))
      rfl (kf 767 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 1026 770 (logical_site 1026 (by simp [logicalOmissions]))
      rfl (kf 1026 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 1541 1285 (logical_site 1541 (by simp [logicalOmissions]))
      rfl (kf 1541 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 1542 1286 (logical_site 1542 (by simp [logicalOmissions]))
      rfl (kf 1542 (by simp [logicalOmissions]))
  · exact placed_free K ks L hw hn 1797 769 (logical_site 1797 (by simp [logicalOmissions]))
      rfl (kf 1797 (by simp [logicalOmissions]))

theorem division_free (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kf : ∀i∈logicalOmissions,base i∉wires K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Fp) (k : Nat) (hk : k∈Q1591Resources.genericOmissions) :
    L.core.poolWire k∉wires (division K L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  have old := ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [division,entry,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),placed_omissions K ks kf L hw hn k hk⟩

end ECDSAAdd.Entrant.FrontierEntry1591Callers
