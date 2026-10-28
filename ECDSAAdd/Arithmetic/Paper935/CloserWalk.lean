import ECDSAAdd.Arithmetic.Paper935.CloserEndpoint
import ECDSAAdd.Arithmetic.Paper935.CloserCapacity

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- Actual successful forward execution followed by the physical closer may
release exactly the three cleared payloads, leaving the 620-wire arena Ready. -/
theorem seededAuthorWalk_closer_release {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m n : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) :
    let before := runWithTape (seededAuthorWalkProgram p slots) m ordinal s
    let bank := walkExitBank walkSeedBank slots
    let out := run (closerProgram bank p) n before
    (walkExitArena walkSeedArena slots).release (closerPayloads bank).toFinset out.basis=
      some (authorClosedArena slots) ∧
    (authorClosedArena slots).Ready out.basis ∧ (authorClosedArena slots).live.card=620 ∧
    out.phase=before.phase := by
  have endpoint := seededAuthorWalk_closer_endpoint input p hp x odd coprime good slots compiled s m ordinal ready encoding
  have executed := seededAuthorWalk_run input p hp x odd good slots compiled s m ordinal ready encoding
  have widths := compileAuthorWalk_exit_widths slots compiled
  have positive : 0<p := by
    by_contra bad
    have zero : p=0 := by omega
    simp [zero] at odd
  have fw : 1<2^(walkExitBank walkSeedBank slots).f.payload.length := by rw [widths.1]; decide
  have pw : p<2^(walkExitBank walkSeedBank slots).gv.payload.length := by
    rw [widths.2.2.2]
    exact lt_trans hp (Nat.pow_lt_pow_right (by decide) (by decide))
  have released := closerProgram_release (walkExitBank walkSeedBank slots) p
    (walkExitArena walkSeedArena slots) (compileAuthorWalk_exit_owned slots compiled) fw positive pw
    (runWithTape (seededAuthorWalkProgram p slots) m ordinal s) n executed.2.1
    endpoint.1 endpoint.2.1 endpoint.2.2
  have clear := closerProgram_clear (walkExitBank walkSeedBank slots) p
    (compileAuthorWalk_exit_owned slots compiled).1 fw positive pw
    (runWithTape (seededAuthorWalkProgram p slots) m ordinal s) n endpoint.1 endpoint.2.1 endpoint.2.2
  exact ⟨released.1,released.2,compileAuthorWalk_closed_card slots compiled,clear.1⟩

end ECDSAAdd.Arithmetic.Paper935
