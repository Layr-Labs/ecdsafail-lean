import ECDSAAdd.Arithmetic.Paper935.HornerCarryBlock

namespace ECDSAAdd.Arithmetic.Paper935

/-- Pure carry/dressing update of luo_core.py:882–894. It does not invoke
an interpreter and is also defined on dirty scratch inputs. -/
def HornerCarryCell.advance (b : HornerCarryCell) (cin : Option Wire) (s : BasisState) : BasisState :=
  writeBit (writeBit (writeBit s b.carry
    (carryBit (s b.target) (s b.addend) ((cin.map s).getD false))) b.target
    (s b.target ^^ (cin.map s).getD false)) b.addend
    (s b.addend ^^ (cin.map s).getD false)

def hornerCarryAdvance : List HornerCarryCell → Option Wire → BasisState → BasisState
  | [], _, s => s
  | b::bs, cin, s => hornerCarryAdvance bs (some b.carry) (b.advance cin s)

/-- Per-cell prerequisites are expressed on the pure carry recurrence,
not on values extracted from the circuit execution. -/
def HornerCarrySweepReady : List HornerCarryCell → Option Wire → BasisState → Prop
  | [], _, _ => True
  | b::bs, cin, s => ([b.target,b.addend,b.carry]++cin.toList).Nodup ∧
      s b.carry=false ∧ HornerCarrySweepReady bs (some b.carry) (b.advance cin s)

/-- The complete actual forward sweep follows the pure carry recurrence
and leaves the phase unchanged for every measurement tape. -/
theorem hornerCarrySweep_run (bs : List HornerCarryCell) (cin : Option Wire)
    (s : State) (m : List Bool) (ready : HornerCarrySweepReady bs cin s.basis) :
    run (hornerCarrySweep bs cin) m s=⟨s.phase,hornerCarryAdvance bs cin s.basis⟩ := by
  induction bs generalizing cin s m with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨distinct,zero,rest⟩ := ready
    have first := hornerCarryForward_run b.target b.addend b.carry cin distinct s m zero
    have count : measurementCount (hornerCarryForward b.target b.addend b.carry cin)=0 := by
      cases cin <;> rfl
    rw [hornerCarrySweep,run_append,run_take,count,List.drop_zero,first]
    exact ih (some b.carry) ⟨s.phase,b.advance cin s.basis⟩ m rest

end ECDSAAdd.Arithmetic.Paper935
