import ECDSAAdd.Arithmetic.Paper935.HornerCarryErase

namespace ECDSAAdd.Arithmetic.Paper935

/-- Static wire constraints for the quantum carry sweeps at luo_core.py:882–910.
Later carry scratch must be outside the three wires written by this cell. -/
def HornerCarryGeometry (ctrl : Wire) : List HornerCarryCell → Option Wire → Prop
  | [], _ => True
  | b::bs, cin => ([ctrl,b.target,b.addend,b.carry]++cin.toList).Nodup ∧
      (∀d∈bs,d.carry≠b.target ∧ d.carry≠b.addend ∧ d.carry≠b.carry) ∧
      HornerCarryGeometry ctrl bs (some b.carry)

/-- All three physical ports of each cell, in low-to-high cell order. -/
def hornerCarryPorts (bs : List HornerCarryCell) : List Wire :=
  bs.flatMap fun b => [b.target,b.addend,b.carry]

/-- A single globally distinct layout establishes the static geometry. -/
theorem hornerCarryGeometry_of_nodup (ctrl : Wire) (bs : List HornerCarryCell)
    (cin : Option Wire) (distinct : (ctrl::(cin.toList++hornerCarryPorts bs)).Nodup) :
    HornerCarryGeometry ctrl bs cin := by
  induction bs generalizing cin with
  | nil => trivial
  | cons b bs ih =>
    have nd : (ctrl::(cin.toList++([b.target,b.addend,b.carry]++hornerCarryPorts bs))).Nodup := distinct
    have allAway := (List.nodup_cons.mp nd).1
    have body := (List.nodup_append.mp (List.nodup_cons.mp nd).2).2.1
    have initialND : (ctrl::(cin.toList++[b.target,b.addend,b.carry])).Nodup :=
      (List.nodup_append.mp (by simpa only [List.cons_append,List.append_assoc] using nd)).1
    have head : ([ctrl,b.target,b.addend,b.carry]++cin.toList).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change ctrl∉([b.target,b.addend,b.carry]++cin.toList)
        simpa only [List.mem_append,or_comm] using (List.nodup_cons.mp initialND).1
      · exact List.nodup_append_comm.mp (List.nodup_cons.mp initialND).2
    refine ⟨head,?_,ih (some b.carry) ?_⟩
    · intro d hd
      have mem : d.carry∈hornerCarryPorts bs := List.mem_flatMap.mpr ⟨d,hd,by simp⟩
      have apart := (List.nodup_append.mp body).2.2
      exact ⟨Ne.symm (apart _ (by simp) _ mem),Ne.symm (apart _ (by simp) _ mem),
        Ne.symm (apart _ (by simp) _ mem)⟩
    · apply List.nodup_cons.mpr
      constructor
      · intro h
        apply allAway
        apply List.mem_append_right
        change ctrl∈b.carry::hornerCarryPorts bs at h
        simp only [List.mem_cons] at h
        rcases h with h|h
        · simp [h]
        · exact List.mem_append_right _ h
      · exact (List.nodup_cons.mp (List.nodup_cons.mp body).2).2

theorem hornerCarryAdvance_frame (b : HornerCarryCell) (cin : Option Wire) (s : BasisState)
    (q : Wire) (ha : q≠b.target) (he : q≠b.addend) (ht : q≠b.carry) :
    b.advance cin s q=s q := by
  simp [HornerCarryCell.advance,writeBit,ha,he,ht]

/-- All readiness obligations follow from static geometry and zero scratch
at entry; callers need not assume anything about intermediate execution. -/
theorem hornerCarryEraseReady_of_geometry (ctrl : Wire) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : BasisState) (geometry : HornerCarryGeometry ctrl bs cin)
    (clean : ∀b∈bs,s b.carry=false) : HornerCarryEraseReady ctrl bs cin s := by
  induction bs generalizing cin s with
  | nil => trivial
  | cons b bs ih =>
    refine ⟨geometry.1,clean b (by simp),ih _ _ geometry.2.2 ?_⟩
    intro d hd
    have away := geometry.2.1 d hd
    rw [hornerCarryAdvance_frame b cin s d.carry away.1 away.2.1 away.2.2]
    exact clean d (List.mem_cons_of_mem b hd)

theorem hornerCarrySweep_erase_of_geometry (ctrl : Wire) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : State) (m n : List Bool)
    (geometry : HornerCarryGeometry ctrl bs cin) (clean : ∀b∈bs,s.basis b.carry=false) :
    run (hornerCarryUnsweep ctrl false false bs cin) n (run (hornerCarrySweep bs cin) m s)=s :=
  hornerCarrySweep_erase ctrl bs cin s m n (hornerCarryEraseReady_of_geometry ctrl bs cin s.basis geometry clean)

end ECDSAAdd.Arithmetic.Paper935
