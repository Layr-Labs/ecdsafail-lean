import ECDSAAdd.Arithmetic.InPlaceAdder

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.KnownOutputCarry

/-- An immutable complete sum makes its incoming carry an affine read. -/
theorem incoming_from_sum (a b c : Bool) :
    a ^^ b ^^ sumBit a b c = c := by
  cases a <;> cases b <;> cases c <;> decide

/-- The outgoing carry expressed in the completed sum, with unchanged source. -/
def postCarry (a s c : Bool) : Bool :=
  (((a ^^ c) ^^ (a && s)) ^^ (a && c)) ^^ (s && c)

theorem completed_sum_carry (a b c : Bool) :
    carryBit a b c = postCarry a (sumBit a b c) c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Fresh measurement; its five quadratic terms read the completed sum. -/
def erasePost (a s c out : Wire) : Program :=
  [.measureX out [] [.Z a,.Z c,.CZ a s,.CZ a c,.CZ s c]]

theorem erasePost_counts (a s c out : Wire) :
    toffoliCount (erasePost a s c out)=0 ∧
    measurementCount (erasePost a s c out)=1 := by
  simp [erasePost,toffoliCount,measurementCount]

/-- Full-state equality for every record and incoming phase. This is a leaf
contract, not a complete known-output adder or caller equivalence. -/
theorem erasePost_correct (a y c out : Wire) (s : State) (m : List Bool)
    (ha : a≠out) (hy : y≠out) (hc : c≠out)
    (hk : s.basis out=postCarry (s.basis a) (s.basis y) (s.basis c)) :
    run (erasePost a y c out) m s=
      ⟨s.phase,writeBit s.basis out false⟩ := by
  cases hA : s.basis a <;> cases hY : s.basis y <;>
    cases hC : s.basis c <;> cases hM : m.head?.getD false <;>
    simp [erasePost,run,measureAndCorrect,correct,writeBit,ha,hy,hc,
      hk,postCarry,hA,hY,hC,hM]

end ECDSAAdd.Arithmetic.KnownOutputCarry

#print axioms ECDSAAdd.Arithmetic.KnownOutputCarry.incoming_from_sum
#print axioms ECDSAAdd.Arithmetic.KnownOutputCarry.completed_sum_carry
#print axioms ECDSAAdd.Arithmetic.KnownOutputCarry.erasePost_counts
#print axioms ECDSAAdd.Arithmetic.KnownOutputCarry.erasePost_correct
