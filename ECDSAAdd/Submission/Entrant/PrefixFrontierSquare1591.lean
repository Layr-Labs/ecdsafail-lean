import ECDSAAdd.Submission.Entrant.OneFlag

set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace ECDSAAdd.Entrant.PrefixFrontierSquare1591
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

private theorem resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial_spare_free (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    L.core.poolWire 1539∉wires (OwnDiagAll12Placed.initial L) := by
  rw [OwnDiagAll12Placed.initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnDiagAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=resident_away L hn L.core.generic
      (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · have away:=resident_away L hn old
      (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · have away:=resident_away L hn old
      (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1539
      (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1539
      (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem pool_swap_fix (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (a b n : Nat)
    (ha : a<2613) (hb : b<2613) (hnn : n<2613) (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b))
      (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1539∉wires (OwnDiagAll12PlacedQ7.program L) := by
  have p0:=initial_spare_free L hw hn
  have p1 : L.core.poolWire 1539∉wires (OwnDiagAll12Placed.plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 766 1530 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1539∉wires (OwnDiagAll12Placed.guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 765 1531 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1539∉wires (OwnDiagAll12Placed.minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 767 1532 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1539∉wires (OwnDiagAll12Placed.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 770 1536 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  have p5 : L.core.poolWire 1539∉wires (OwnDiagAll12PlacedQ6.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 1285 1537 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p4
  exact OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 1286 1538 1539
    (by omega) (by omega) (by omega) (by omega) (by omega)) p5

def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)

def program (L : ControlledPointLayout) : Program :=
  renameProgram (swap L) (OwnDiagAll12PlacedQ7.program L)
attribute [local irreducible] program

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 769
  · subst q
    simpa only [swap,Equiv.swap_apply_left] using
      Square5Placement.pool_member L hw 1539 (by omega)
  · by_cases b:q=L.core.poolWire 1539
    · subst q
      simpa only [swap,Equiv.swap_apply_right] using
        Square5Placement.pool_member L hw 769 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 769:=fun e=>
    hq (e.symm ▸ Square5Placement.pool_member L hw 769 (by omega))
  have b:q≠L.core.poolWire 1539:=fun e=>
    hq (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b

theorem run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (hin : regValue L.dialogPool s.basis=0)
    (hout : regValue L.dialogPool (run P m s).basis=0) :
    run (renameProgram (swap L) P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L (swap L) (pool L hw) (outside L hw)
    P s m hin hout

theorem program_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Fp) (G : Bool) (origin : BasisState)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (OwnDiagAll12PlacedQ7.program L) m s := by
  have old:=OwnDiagAll12PlacedQ7.correct L hw hn X Y G origin s m v
  unfold program
  exact run_eq L hw _ s m v.clean old.2.clean

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    OwnDiagAll12Placed.SquareCorrect L (program L) := by
  unfold program
  exact OwnDiagAll12Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (OwnDiagAll12PlacedQ7.correct L hw hn)

theorem counts (L : ControlledPointLayout) :
    toffoliCount (program L)=toffoliCount (OwnDiagAll12PlacedQ7.program L) ∧
    measurementCount (program L)=measurementCount (OwnDiagAll12PlacedQ7.program L) := by
  unfold program
  exact renameProgram_counts (swap L) _

theorem slots_eq (L : ControlledPointLayout) :
    Challenge.gateSlots (program L)=
      Challenge.gateSlots (OwnDiagAll12PlacedQ7.program L) := by
  unfold program
  exact Baselines.rename_gateSlots _ _

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 :=
  (slots_eq L).le.trans (OwnDiagAll12PlacedQ7.slots L hw)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  unfold program
  exact gatePhysical_rename (swap L) (swap L).injective _
    (OwnDiagAll12PlacedQ7.physical L hw hn)

theorem support_eq (L : ControlledPointLayout) :
    wires (program L)=(wires (OwnDiagAll12PlacedQ7.program L)).image (swap L) := by
  unfold program
  exact renameProgram_support _ _

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset := by
  unfold program swap
  exact OwnDiagAll12Placed.swap_support _ _ _ _ (OwnDiagAll12PlacedQ7.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 769
      (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1539
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 769∉wires (program L) := by
  unfold program swap
  exact OwnDiagAll12Placed.swap_target_free _ _ _ (spare_free L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769]) :
    L.core.poolWire k∉wires (program L) := by
  by_cases h:k=769
  · subst k;exact retired_free L hw hn
  have hkold : k∈[1800,766,765,767,770,1285,1286] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    omega
  have f : swap L (L.core.poolWire k)=L.core.poolWire k :=
    pool_swap_fix L hw hn 769 1539 k (by omega) (by omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega) h
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega)
  unfold program
  exact OwnPlusHost.rename_avoid _ _ _ f (OwnDiagAll12PlacedQ7.square_free L hw hn k hkold)

end ECDSAAdd.Entrant.PrefixFrontierSquare1591
