import ECDSAAdd.Arithmetic.Paper935.HornerCarryFinishFrame

namespace ECDSAAdd.Arithmetic.Paper935

theorem hornerCarryAdvance_block_frame (bs : List HornerCarryCell) (cin : Option Wire)
    (s : BasisState) (q : Wire) (away : q∉hornerCarryPorts bs) :
    hornerCarryAdvance bs cin s q=s q := by
  induction bs generalizing cin s with
  | nil => rfl
  | cons b bs ih =>
    have h : q≠b.target ∧ q≠b.addend ∧ q≠b.carry ∧ q∉hornerCarryPorts bs := by
      simpa [hornerCarryPorts,List.mem_flatMap] using away
    rw [hornerCarryAdvance,ih _ _ h.2.2.2]
    exact hornerCarryAdvance_frame b cin s q h.1 h.2.1 h.2.2.1

/-- Global distinctness ensures that writing higher sums cannot spoil a
lower cell's dressed inputs or carry relation. Thus backward readiness is
proved for both flags, rather than assumed about intermediate execution. -/
theorem hornerCarryFinishReady_of_advance (ctrl : Wire) (sums keep : Bool)
    (bs : List HornerCarryCell) (cin : Option Wire) (s : BasisState)
    (distinct : (ctrl::(cin.toList++hornerCarryPorts bs)).Nodup) :
    HornerCarryFinishReady ctrl sums keep bs cin (hornerCarryAdvance bs cin s) := by
  induction bs generalizing cin s with
  | nil => trivial
  | cons b bs ih =>
    have nd : (ctrl::(cin.toList++([b.target,b.addend,b.carry]++hornerCarryPorts bs))).Nodup := distinct
    have body := (List.nodup_append.mp (List.nodup_cons.mp nd).2).2.1
    have next : (ctrl::((some b.carry).toList++hornerCarryPorts bs)).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · intro h
        apply (List.nodup_cons.mp nd).1
        apply List.mem_append_right
        change ctrl∈b.carry::hornerCarryPorts bs at h
        rcases List.mem_cons.mp h with h|h
        · simp [h]
        · exact List.mem_append_right _ h
      · exact (List.nodup_cons.mp (List.nodup_cons.mp body).2).2
    let t := b.advance cin s
    let a := hornerCarryAdvance bs (some b.carry) t
    let u := hornerCarryFinishSweep ctrl sums keep bs (some b.carry) a
    have splitND : ((ctrl::(cin.toList++[b.target,b.addend,b.carry]))++hornerCarryPorts bs).Nodup := by
      simpa only [List.cons_append,List.append_assoc] using nd
    have unchanged (q : Wire) (hq : q∈ctrl::(cin.toList++[b.target,b.addend,b.carry])) : u q=t q := by
      have away : q∉hornerCarryPorts bs := fun h => (List.nodup_append.mp splitND).2.2 q hq q h rfl
      exact (hornerCarryFinishSweep_frame ctrl sums keep bs (some b.carry) a q away).trans
        (hornerCarryAdvance_block_frame bs (some b.carry) t q away)
    have cinEq : (cin.map u).getD false=(cin.map t).getD false := by
      cases cin with
      | none => rfl
      | some d => exact unchanged d (by simp)
    have geometry := hornerCarryGeometry_of_nodup ctrl (b::bs) cin distinct
    refine ⟨ih _ t next,geometry.1,?_⟩
    change u b.carry=carryBit (u b.target ^^ (cin.map u).getD false)
      (u b.addend ^^ (cin.map u).getD false) ((cin.map u).getD false)
    rw [unchanged b.carry (by simp),unchanged b.target (by simp),unchanged b.addend (by simp),cinEq]
    exact hornerCarryAdvance_valid b cin s (List.nodup_cons.mp geometry.1).2

/-- Exact full-state block result with controlled sums and optional highest
carry retention. Only static distinctness and initially zero carries are
assumed; all intermediate carry relations are derived. -/
theorem hornerCarryBlock_run (ctrl : Wire) (sums keep : Bool)
    (bs : List HornerCarryCell) (cin : Option Wire) (s : State) (m n : List Bool)
    (distinct : (ctrl::(cin.toList++hornerCarryPorts bs)).Nodup)
    (clean : ∀b∈bs,s.basis b.carry=false) :
    run (hornerCarryUnsweep ctrl sums keep bs cin) n (run (hornerCarrySweep bs cin) m s)=
      ⟨s.phase,hornerCarryFinishSweep ctrl sums keep bs cin (hornerCarryAdvance bs cin s.basis)⟩ := by
  have geometry := hornerCarryGeometry_of_nodup ctrl bs cin distinct
  have ready := hornerCarryEraseReady_of_geometry ctrl bs cin s.basis geometry clean
  rw [hornerCarrySweep_run bs cin s m (hornerCarryEraseReady_forward ctrl bs cin s.basis ready)]
  exact hornerCarryUnsweep_run ctrl sums keep bs cin _ n
    (hornerCarryFinishReady_of_advance ctrl sums keep bs cin s.basis distinct)

end ECDSAAdd.Arithmetic.Paper935
