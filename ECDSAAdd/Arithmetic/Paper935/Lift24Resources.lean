import ECDSAAdd.Arithmetic.Paper935.Lift24Inverse

namespace ECDSAAdd.Arithmetic.Paper935

/-- Counts of the actual three-block plus/minus-one routine, including
reverse-order measurement-based keeper erasure. -/
theorem lift24Program_counts (subtract : Bool) :
    toffoliCount (lift24Program subtract)=95 ∧
    measurementCount (lift24Program subtract)=92 := by
  cases subtract <;> decide +kernel

/-- The stated 83-address support includes one control, 58 window data bits,
and a 24-wire pool. Other payload bits belong to the outer lift operation. -/
theorem lift24Program_frame (subtract : Bool) (s : State) (m : List Bool)
    (q : Wire) (outside : 83≤q) :
    (run (lift24Program subtract) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro mem
  have := lift24Program_support subtract mem
  simp only [Finset.mem_range] at this
  dsimp only [Wire] at *
  omega

end ECDSAAdd.Arithmetic.Paper935
