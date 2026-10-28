import ECDSAAdd.Arithmetic.CompressedAllocationBoundary

namespace ECDSAAdd.Arithmetic.CompressedAllocation

private theorem inverse_outside (e : Equiv.Perm Nat)
    (fix : ∀ q, ¬zeroRegion q → e q=q) (q : Nat) (hq : ¬zeroRegion q) :
    e.symm q=q := by
  calc
    e.symm q = e.symm (e q) := by rw [fix q hq]
    _ = q := e.symm_apply_apply q

/-- Switch two public placements only at a proved-zero allocation boundary.
The logical State, including phase and every live coordinate, is identical.
No swap instruction or measurement is inserted into the actual circuit. -/
theorem switch_zero_placements (old next : Equiv.Perm Nat) (actual logical : State)
    (oldFix : ∀ q, ¬zeroRegion q → old q=q)
    (nextFix : ∀ q, ¬zeroRegion q → next q=q)
    (hmap : pullState old actual=logical)
    (hz : ∀ q, zeroRegion q → logical.basis q=false) :
    pullState next actual=logical := by
  have original : pullState old.symm logical=actual := by
    rw [←hmap]
    apply State.extensionality
    · rfl
    · funext q
      simp only [pullState,old.apply_symm_apply]
  let delta := next.trans old.symm
  have fix : ∀ q, ¬zeroRegion q → delta q=q := by
    intro q hq
    change old.symm (next q)=q
    rw [nextFix q hq,inverse_outside old oldFix q hq]
  have same := pull_zero_permutation delta logical fix hz
  rw [←original]
  change pullState delta logical=logical
  exact same

/-- The next renamed block executes the same logical instructions and every
measurement correction under its new injective placement. -/
theorem run_switch_zero_placements (old next : Equiv.Perm Nat)
    (actual logical : State) (program : Program) (m : List Bool)
    (oldFix : ∀ q, ¬zeroRegion q → old q=q)
    (nextFix : ∀ q, ¬zeroRegion q → next q=q)
    (hmap : pullState old actual=logical)
    (hz : ∀ q, zeroRegion q → logical.basis q=false) :
    pullState next (run (renameProgram next program) m actual)=run program m logical := by
  rw [run_rename next next.injective,
    switch_zero_placements old next actual logical oldFix nextFix hmap hz]

theorem run_switch_packet_placements (a j : Nat) (ha : a < 170) (hj : j < 170)
    (actual logical : State) (program : Program) (m : List Bool)
    (hmap : pullState (pi a) actual=logical)
    (hz : ∀ q, zeroRegion q → logical.basis q=false) :
    pullState (pi j) (run (renameProgram (pi j) program) m actual)=run program m logical :=
  run_switch_zero_placements (pi a) (pi j) actual logical program m
    (fun q hq => pi_outside a q ha hq) (fun q hq => pi_outside j q hj hq) hmap hz

end ECDSAAdd.Arithmetic.CompressedAllocation
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.switch_zero_placements
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.run_switch_zero_placements
#print axioms ECDSAAdd.Arithmetic.CompressedAllocation.run_switch_packet_placements
