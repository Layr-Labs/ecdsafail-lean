import ECDSAAdd.Arithmetic.NativeFirstDirectInverseWrapper
import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
import ECDSAAdd.Arithmetic.CompressedCompactRestore

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run forward inverse

/-- Field outsiders may differ. The new inverse restores the full original
integer pool, including phase, and preserves every changed field outsider. -/
theorem inverse_restore_after_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (initial field : State) (mF mI : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x initial.basis)
    (hphase : field.phase=(run (forward w) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires w,field.basis q=(run (forward w) mF initial).basis q) :
    (run (inverse w) mI field).phase=initial.phase ∧
    (∀q∈skywalkPoolWires w,(run (inverse w) mI field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w → (run (inverse w) mI field).basis q=field.basis q) := by
  have support : wires (inverse w) ⊆ (skywalkPoolWires w).toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (prefix_pool_subset w (List.mem_toFinset.mp ((prefix_support w).2 hq)))
  have restored := inverse_forward_ready w hn x initial mF mI hin
  have agrees := pool_run_agrees (inverse w) (skywalkPoolWires w).toFinset support mI
    field (run (forward w) mF initial) hphase
    (fun q hq => hpool q (List.mem_toFinset.mp hq))
  rw [restored] at agrees
  refine ⟨agrees.1,?_,?_⟩
  · intro q hq
    exact agrees.2 q (List.mem_toFinset.mpr hq)
  · intro q hq
    exact run_preserves_outside (inverse w) mI field q
      (fun h => hq (List.mem_toFinset.mp (support h)))

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.inverse_restore_after_outside
