import ECDSAAdd.Arithmetic.MappedCompressedPacketTransport
import ECDSAAdd.Arithmetic.CompressedFieldEncodedZeros

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run

private theorem inverse_zero (e : Equiv.Perm Nat)
    (fix : ∀q,¬zeroRegion q → e q=q) (q : Nat) (hq : zeroRegion q) :
    zeroRegion (e q) := by
  by_contra bad
  have eq := e.injective (fix (e q) bad)
  exact bad (eq.symm ▸ hq)

theorem shifted_zero_boundary (e : Equiv.Perm Nat)
    (fix : ∀q,¬zeroRegion q → e q=q) (s : State)
    (hz : ∀q,zeroRegion q → s.basis (base q)=false) :
    pullState (shifted e) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (shifted e q)=s.basis q
    by_cases small : q < 16
    · change s.basis (shiftedFn e q)=s.basis q
      simp only [shiftedFn,if_pos small]
    · have eq : q=base (q-16) := by
        change q=(q-16)+16
        exact (Nat.sub_add_cancel (Nat.le_of_not_gt small)).symm
      rw [eq,shifted_base]
      by_cases clean : zeroRegion (q-16)
      · exact (hz _ (inverse_zero e fix _ clean)).trans (hz _ clean).symm
      · rw [fix _ clean]

theorem pullState_perm_injective (e : Equiv.Perm Nat) : Function.Injective (pullState e) := by
  intro s t h
  apply State.extensionality
  · have ph := congrArg (fun x : State => x.phase) h
    exact ph
  · funext q
    have bit := congrArg (fun x : State => x.basis (e.symm q)) h
    simpa only [pullState,e.apply_symm_apply] using bit

/-- A packet whose reference input and output have clean allocation roles
executes identically as a complete State, not only on the retained payload. -/
theorem mappedGroup_state_eq (divide : Bool) (j : Nat) (hj : j < 170)
    (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀q,zeroRegion q → (run (baseGroup divide j) m s).basis (base q)=false) :
    run (mappedGroup divide j) m s=run (baseGroup divide j) m s := by
  have fix := fun q hq => pi_outside j q hj hq
  have input := shifted_zero_boundary (pi j) fix s hin
  have output := shifted_zero_boundary (pi j) fix (run (baseGroup divide j) m s) hout
  apply pullState_perm_injective (shifted (pi j))
  rw [mappedGroup_run divide j hj,input,output]

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.shifted_zero_boundary
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedGroup_state_eq
