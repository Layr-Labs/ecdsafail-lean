import ECDSAAdd.Arithmetic.Paper935.HornerCarryForward

namespace ECDSAAdd.Arithmetic.Paper935

/-- Clean carries and cell geometry along the pure forward recurrence.
The explicit external control is reserved even in release-only mode. -/
def HornerCarryEraseReady (ctrl : Wire) : List HornerCarryCell → Option Wire → BasisState → Prop
  | [], _, _ => True
  | b::bs, cin, s => ([ctrl,b.target,b.addend,b.carry]++cin.toList).Nodup ∧
      s b.carry=false ∧ HornerCarryEraseReady ctrl bs (some b.carry) (b.advance cin s)

theorem hornerCarryEraseReady_forward (ctrl : Wire) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : BasisState) (ready : HornerCarryEraseReady ctrl bs cin s) :
    HornerCarrySweepReady bs cin s := by
  induction bs generalizing cin s with
  | nil => trivial
  | cons b bs ih =>
    exact ⟨(List.nodup_cons.mp ready.1).2,ready.2.1,ih _ _ ready.2.2⟩

/-- The release-only descending sweep from luo_core.py:897–910 restores
the original complete state. No reverse list of measured gates is used. -/
theorem hornerCarryUnsweep_erase (ctrl : Wire) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : State) (m : List Bool)
    (ready : HornerCarryEraseReady ctrl bs cin s.basis) :
    run (hornerCarryUnsweep ctrl false false bs cin) m
      ⟨s.phase,hornerCarryAdvance bs cin s.basis⟩=s := by
  induction bs generalizing cin s m with
  | nil => cases s; rfl
  | cons b bs ih =>
    obtain ⟨distinct,zero,rest⟩ := ready
    have cell := hornerCarryCell_run ctrl b.target b.addend b.carry cin false false distinct s
      (m.drop (measurementCount (hornerCarryUnsweep ctrl false false bs (some b.carry)))) zero
    have first := hornerCarryForward_run b.target b.addend b.carry cin
      (List.nodup_cons.mp distinct).2 s
      (m.drop (measurementCount (hornerCarryUnsweep ctrl false false bs (some b.carry)))) zero
    have count : measurementCount (hornerCarryForward b.target b.addend b.carry cin)=0 := by
      cases cin <;> rfl
    rw [run_append,run_take,count,List.drop_zero,first] at cell
    have unchanged :
        (⟨s.phase,writeBit (writeBit s.basis b.carry false) b.target (s.basis b.target)⟩ : State)=s := by
      rw [←zero]
      simp only [writeBit,Function.update_eq_self]
    simp only [Bool.false_and,Bool.false_eq_true,if_false] at cell
    rw [unchanged] at cell
    simp only [hornerCarryUnsweep,hornerCarryAdvance]
    rw [run_append,run_take]
    have tail := ih (some b.carry) ⟨s.phase,b.advance cin s.basis⟩ m rest
    rw [tail]
    exact cell

theorem hornerCarrySweep_erase (ctrl : Wire) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : State) (m n : List Bool)
    (ready : HornerCarryEraseReady ctrl bs cin s.basis) :
    run (hornerCarryUnsweep ctrl false false bs cin) n (run (hornerCarrySweep bs cin) m s)=s := by
  rw [hornerCarrySweep_run bs cin s m (hornerCarryEraseReady_forward ctrl bs cin s.basis ready)]
  exact hornerCarryUnsweep_erase ctrl bs cin s n ready

end ECDSAAdd.Arithmetic.Paper935
