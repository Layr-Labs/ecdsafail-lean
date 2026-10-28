import ECDSAAdd.Arithmetic.BlockedZero
import ECDSAAdd.Framework.FailureBudget

namespace ECDSAAdd.Arithmetic.Paper935
open FailureBudget

/-- The independently specified controlled zero-test state, including all
unchanged wires and the original phase. -/
def blockedZeroIdeal (c target : Wire) (bs : List BlockedZero.Block) (s : State) : State :=
  ⟨s.phase,writeBit s.basis target
    (s.basis target ^^ (s.basis c && decide (regValue (BlockedZero.inputs bs) s.basis=0)))⟩

/-- A failure means some phase/tape violates the exact zero-test action.
This is an event on original input labels, not a fictitious law on tapes. -/
noncomputable def blockedZeroFailure {X : Type*} [Fintype X]
    (c target : Wire) (bs : List BlockedZero.Block) (input : X → BasisState) : Finset X := by
  classical
  exact traceEvent input (fun s => ∃ phase tape,
    run (BlockedZero.program c target bs) tape ⟨phase,s⟩ ≠
      blockedZeroIdeal c target bs ⟨phase,s⟩)

theorem blockedZeroFailure_empty {X : Type*} [Fintype X]
    (c target : Wire) (bs : List BlockedZero.Block) (input : X → BasisState)
    (hv : BlockedZero.Valid c target bs) (hc : ∀ x,BlockedZero.clean bs (input x)) :
    blockedZeroFailure c target bs input=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨phase,tape,h⟩ := (mem_traceEvent _ _ x).mp hx
  apply h
  simpa only [blockedZeroIdeal,BlockedZero.test_eq_zero] using
    BlockedZero.run_eq c target bs hv ⟨phase,input x⟩ tape (hc x)

/-- Measurement-based zero detection contributes exactly zero exceptional mass
for any input law once layout validity and clean scratch are established. -/
theorem blockedZeroFailure_mass_zero {X : Type*} [Fintype X]
    (μ : InputLaw X) (c target : Wire) (bs : List BlockedZero.Block) (input : X → BasisState)
    (hv : BlockedZero.Valid c target bs) (hc : ∀ x,BlockedZero.clean bs (input x)) :
    μ.mass (blockedZeroFailure c target bs input)=0 := by
  rw [blockedZeroFailure_empty c target bs input hv hc,μ.mass_empty]

/-- If clean scratch is only known off an existing bad set, the zero test adds
no new exceptional input. This avoids assuming earlier failing lanes are clean. -/
theorem blockedZeroFailure_subset {X : Type*} [Fintype X] [DecidableEq X]
    (c target : Wire) (bs : List BlockedZero.Block) (input : X → BasisState)
    (bad : Finset X) (hv : BlockedZero.Valid c target bs)
    (hc : ∀ x,x∉bad → BlockedZero.clean bs (input x)) :
    blockedZeroFailure c target bs input⊆bad := by
  classical
  intro x hx
  by_contra hbad
  obtain ⟨phase,tape,h⟩ := (mem_traceEvent _ _ x).mp hx
  apply h
  simpa only [blockedZeroIdeal,BlockedZero.test_eq_zero] using
    BlockedZero.run_eq c target bs hv ⟨phase,input x⟩ tape (hc x hbad)

theorem blockedZeroFailure_union_mass {X : Type*} [Fintype X] [DecidableEq X]
    (μ : InputLaw X) (c target : Wire) (bs : List BlockedZero.Block) (input : X → BasisState)
    (bad : Finset X) (hv : BlockedZero.Valid c target bs)
    (hc : ∀ x,x∉bad → BlockedZero.clean bs (input x)) :
    μ.mass (bad∪blockedZeroFailure c target bs input)=μ.mass bad := by
  rw [Finset.union_eq_left.mpr (blockedZeroFailure_subset c target bs input bad hv hc)]

end ECDSAAdd.Arithmetic.Paper935
