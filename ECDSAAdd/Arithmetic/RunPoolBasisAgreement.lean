import ECDSAAdd.Arithmetic.DisjointPrograms
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run wires

/-- Basis locality on a certified pool is independent of incoming phase.
Every correction operand is included in the actual program support. -/
theorem run_pool_basis_agreement (p : Program) (W : Finset Wire)
    (support : wires p⊆W) (s t : State) (m : List Bool)
    (bits : ∀q∈W,s.basis q=t.basis q) :
    ∀q∈W,(run p m s).basis q=(run p m t).basis q := by
  have read : ∀q∈wires p,s.basis q=t.basis q := fun q hq => bits q (support hq)
  have increment := run_local_increment p s t m read
  intro q hq
  by_cases used : q∈wires p
  · exact increment.2 q used
  · exact (run_preserves_outside p m s q used).trans
      ((bits q hq).trans (run_preserves_outside p m t q used).symm)
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.run_pool_basis_agreement
