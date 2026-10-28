import ECDSAAdd.Arithmetic.Paper935.HornerCarryBlock
import ECDSAAdd.Arithmetic.RippleAdder

namespace ECDSAAdd.Arithmetic.Paper935

private theorem word_cons (q : Wire) (r : List Wire) (s : BasisState) :
    regValue (q::r) s=(s q).toNat+2*regValue r s := by
  cases h : s q <;> simp [regValue,h]

/-- Mathematical low word of the quantum/quantum carry recurrence from
luo_core.py:882–910, read from original operand bits. -/
def hornerWordSum : List HornerCarryCell → Bool → BasisState → Nat
  | [], _, _ => 0
  | b::bs, cin, s => (sumBit (s b.target) (s b.addend) cin).toNat +
      2*hornerWordSum bs (carryBit (s b.target) (s b.addend) cin) s

/-- Mathematical final carry of that same recurrence. -/
def hornerWordCarry : List HornerCarryCell → Bool → BasisState → Bool
  | [], cin, _ => cin
  | b::bs, cin, s => hornerWordCarry bs (carryBit (s b.target) (s b.addend) cin) s

/-- The low-word recurrence is addition modulo its actual bit width. -/
theorem hornerWordSum_value (bs : List HornerCarryCell) (cin : Bool) (s : BasisState) :
    hornerWordSum bs cin s=
      (regValue (bs.map HornerCarryCell.target) s + regValue (bs.map HornerCarryCell.addend) s + cin.toNat)%2^bs.length := by
  induction bs generalizing cin with
  | nil => simp [hornerWordSum,regValue,Nat.mod_one]
  | cons b bs ih =>
    rw [hornerWordSum,ih]
    simpa only [List.map_cons,List.length_cons,word_cons] using sum_value_step (s b.target) (s b.addend) cin
      (regValue (bs.map HornerCarryCell.target) s) (regValue (bs.map HornerCarryCell.addend) s) bs.length

/-- Low word plus the retained high carry is the full integer sum, so
retaining a carry has its ordinary arithmetic meaning. -/
theorem hornerWordSum_carry (bs : List HornerCarryCell) (cin : Bool) (s : BasisState) :
    hornerWordSum bs cin s + 2^bs.length*(hornerWordCarry bs cin s).toNat=
      regValue (bs.map HornerCarryCell.target) s + regValue (bs.map HornerCarryCell.addend) s + cin.toNat := by
  induction bs generalizing cin with
  | nil => simp [hornerWordSum,hornerWordCarry,regValue]
  | cons b bs ih =>
    have lower := ih (carryBit (s b.target) (s b.addend) cin)
    have bit := fullAdder_bit_value (s b.target) (s b.addend) cin
    simp only [hornerWordSum,hornerWordCarry,List.length_cons,List.map_cons,word_cons,Nat.pow_succ]
    change (sumBit (s b.target) (s b.addend) cin).toNat +
      2*hornerWordSum bs (carryBit (s b.target) (s b.addend) cin) s +
      (2^bs.length*2)*(hornerWordCarry bs (carryBit (s b.target) (s b.addend) cin) s).toNat =
      (s b.target).toNat + 2*regValue (bs.map HornerCarryCell.target) s +
      ((s b.addend).toNat + 2*regValue (bs.map HornerCarryCell.addend) s) + cin.toNat
    nlinarith [lower,bit]

end ECDSAAdd.Arithmetic.Paper935
