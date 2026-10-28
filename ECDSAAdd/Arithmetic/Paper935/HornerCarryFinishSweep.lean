import ECDSAAdd.Arithmetic.Paper935.HornerCarryBackward
import ECDSAAdd.Arithmetic.Paper935.HornerCarryBlock

namespace ECDSAAdd.Arithmetic.Paper935

/-- Pure descending recurrence of luo_core.py:897–910, including
controlled sum writes and the retained highest carry. -/
def hornerCarryFinishSweep (ctrl : Wire) (sums keep : Bool) :
    List HornerCarryCell → Option Wire → BasisState → BasisState
  | [], _, s => s
  | b::bs, cin, s => hornerCarryFinish ctrl b.target b.addend b.carry cin sums
      (keep && bs.isEmpty) (hornerCarryFinishSweep ctrl sums keep bs (some b.carry) s)

/-- The required carry relation is on the pure descending recurrence;
it is not an assumption about the result of running a circuit. -/
def HornerCarryFinishReady (ctrl : Wire) (sums keep : Bool) :
    List HornerCarryCell → Option Wire → BasisState → Prop
  | [], _, _ => True
  | b::bs, cin, s =>
      let u := hornerCarryFinishSweep ctrl sums keep bs (some b.carry) s
      HornerCarryFinishReady ctrl sums keep bs (some b.carry) s ∧
      ([ctrl,b.target,b.addend,b.carry]++cin.toList).Nodup ∧
      u b.carry=carryBit (u b.target ^^ (cin.map u).getD false)
        (u b.addend ^^ (cin.map u).getD false) ((cin.map u).getD false)

/-- Exact whole-state backward semantics for both sum and keep flags. -/
theorem hornerCarryUnsweep_run (ctrl : Wire) (sums keep : Bool)
    (bs : List HornerCarryCell) (cin : Option Wire) (s : State) (m : List Bool)
    (ready : HornerCarryFinishReady ctrl sums keep bs cin s.basis) :
    run (hornerCarryUnsweep ctrl sums keep bs cin) m s=
      ⟨s.phase,hornerCarryFinishSweep ctrl sums keep bs cin s.basis⟩ := by
  induction bs generalizing cin s m with
  | nil => rfl
  | cons b bs ih =>
    rw [hornerCarryUnsweep,run_append,run_take,ih _ s m ready.1]
    exact hornerCarryBackward_run ctrl b.target b.addend b.carry cin sums (keep && bs.isEmpty)
      ready.2.1 _ _ ready.2.2

end ECDSAAdd.Arithmetic.Paper935
