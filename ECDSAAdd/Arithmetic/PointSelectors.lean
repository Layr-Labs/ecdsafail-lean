import ECDSAAdd.Arithmetic.ControlledPointLayout

namespace ECDSAAdd.Arithmetic

def selectorState (L : ControlledPointLayout) (s : BasisState) (G D O : Bool) : BasisState :=
  writeBit (writeBit (writeBit s L.genericSelect G) L.doubleSelect D) L.infinitySelect O

theorem ControlledPointLayout.selector_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    [L.control,L.core.generic,L.core.double,L.core.input.finite,
      L.genericSelect,L.doubleSelect,L.infinitySelect].Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  simp only [ControlledPointLayout.wires,ControlledPointLayout.extras,ControlledPointLayout.selectors,
    PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.flags,
    List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

theorem pointSelectors_correct (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) :
    run (pointSelectors L) m s=⟨s.phase,selectorState L s.basis
      (s.basis L.genericSelect ^^ (s.basis L.control && s.basis L.core.generic))
      (s.basis L.doubleSelect ^^ (s.basis L.control && s.basis L.core.double))
      (s.basis L.infinitySelect ^^ (s.basis L.control && !s.basis L.core.input.finite))⟩ := by
  have hh := L.selector_nodup hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,not_false_eq_true,and_true] at hh
  rcases hh with ⟨⟨hbg,hbd,hbf,hbG,hbD,hbO⟩,⟨hgd,hgf,hgG,hgD,hgO⟩,
    ⟨hdf,hdG,hdD,hdO⟩,⟨hfG,hfD,hfO⟩,⟨hGD,hGO⟩,hDO⟩
  simp only [pointSelectors,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hG : w=L.genericSelect
  · subst w; simp [selectorState,writeBit, *, Ne.symm]
  · by_cases hD : w=L.doubleSelect
    · subst w; simp [selectorState,writeBit, *, Ne.symm]
    · by_cases hO : w=L.infinitySelect
      · subst w; simp [selectorState,writeBit, *, Ne.symm]
      · by_cases hf : w=L.core.input.finite
        · subst w; simp [selectorState,writeBit, *, Ne.symm]
        · simp [selectorState,writeBit, *, Ne.symm]

theorem selectorState_outside (L : ControlledPointLayout) (s : BasisState) (G D O : Bool)
    (w : Wire) (hw : w∉L.selectors) : selectorState L s G D O w=s w := by
  simp only [ControlledPointLayout.selectors,List.mem_cons,List.not_mem_nil,or_false,not_or] at hw
  simp [selectorState,writeBit,hw.1,hw.2.1,hw.2.2]

theorem selectorState_values (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (s : BasisState) (G D O : Bool) :
    selectorState L s G D O L.genericSelect=G ∧ selectorState L s G D O L.doubleSelect=D ∧
      selectorState L s G D O L.infinitySelect=O := by
  have hh := (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).2
  change [L.genericSelect,L.doubleSelect,L.infinitySelect].Nodup at hh
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,not_false_eq_true,and_true] at hh
  rcases hh with ⟨⟨hGD,hGO⟩,hDO⟩
  simp [selectorState,writeBit, *]

theorem pointSelectors_counts (L : ControlledPointLayout) :
    toffoliCount (pointSelectors L)=3 ∧ measurementCount (pointSelectors L)=0 := by
  simp [pointSelectors,toffoliCount,measurementCount]

theorem pointSelectors_wires (L : ControlledPointLayout) :
    wires (pointSelectors L)=[L.control,L.core.generic,L.core.double,L.core.input.finite,
      L.genericSelect,L.doubleSelect,L.infinitySelect].toFinset := by
  ext w; simp [pointSelectors,wires,Instr.wires]; tauto

end ECDSAAdd.Arithmetic
