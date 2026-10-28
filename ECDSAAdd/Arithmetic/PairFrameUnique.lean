import ECDSAAdd.Arithmetic.ConditionalXor
import ECDSAAdd.Framework.WireRename

set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic

/-- Equal exact register words determine every bit occurring in the register.
No disjointness or clean-work hypothesis is needed for this finite fact. -/
theorem regValue_equal_bits (r : List Wire) (s t : BasisState)
    (h : regValue r s=regValue r t) : ∀q∈r,s q=t q := by
  induction r with
  | nil => simp
  | cons a as ih =>
    change (if s a then 1 else 0)+2*regValue as s=
      (if t a then 1 else 0)+2*regValue as t at h
    have head : s a=t a := by
      cases hs : s a <;> cases ht : t a <;>
        simp only [hs,ht,Bool.false_eq_true,if_true,if_false] at h ⊢ <;> omega
    have tail : regValue as s=regValue as t := by
      rw [head] at h
      omega
    intro q hq
    rcases List.mem_cons.mp hq with eq|member
    · simpa only [eq] using head
    · exact ih tail q member

/-- The complete two-register frame has a unique output basis state. -/
theorem PairFrame.unique (r y : List Wire) (base : BasisState) (X Y : Nat)
    (s t : BasisState) (hs : PairFrame r y base X Y s)
    (ht : PairFrame r y base X Y t) : s=t := by
  funext q
  by_cases hr : q∈r
  · exact regValue_equal_bits r s t (hs.1.trans ht.1.symm) q hr
  · by_cases hy : q∈y
    · exact regValue_equal_bits y s t (hs.2.1.trans ht.2.1.symm) q hy
    · exact (hs.2.2 q hr hy).trans (ht.2.2 q hr hy).symm

/-- Independent record streams can be compared through complete frames, rather
than expanding either instruction list. Both programs must prove phase repair. -/
theorem PairFrame.program_eq (r y : List Wire) (base : BasisState) (I J X Y : Nat)
    (p q : Program)
    (hp : Triple (PairFrame r y base I J) p (PairFrame r y base X Y))
    (hq : Triple (PairFrame r y base I J) q (PairFrame r y base X Y))
    (s : State) (mp mq : List Bool) (h : PairFrame r y base I J s.basis) :
    run p mp s=run q mq s := by
  have a := hp s mp h
  have b := hq s mq h
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · exact PairFrame.unique r y base X Y _ _ a.2 b.2

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.regValue_equal_bits
#print axioms ECDSAAdd.Arithmetic.PairFrame.unique
#print axioms ECDSAAdd.Arithmetic.PairFrame.program_eq
