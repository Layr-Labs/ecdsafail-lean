import ECDSAAdd.Arithmetic.Paper935.AuthorWalkEndpoint
import ECDSAAdd.Arithmetic.Paper935.ScalingNoBorrow

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- Canonical mathematical scaled inverse, before the 498-call seam.
This definition does not assert that a physical normalization program exists. -/
def scaledInverseSeed (p : Nat) (d : Int) : Nat :=
  let rows := (pinWalk 498 p d 533).rows
  ((rows.f : ZMod p)*(rows.fv : ZMod p)).val

/-- Candidate seed for a fused quotient, separate from the closed-inverse
adapters currently implemented in InverseQuotientRecorded/InverseProductRecorded. -/
def scaledQuotientSeed (p : Nat) (d a : Int) : Nat :=
  let rows := (pinWalk 498 p d 533).rows
  ((a : ZMod p)*(rows.f : ZMod p)*(rows.fv : ZMod p)).val

/-- Mathematical observation of two signed physical row registers. It is not
an allocated output register or an executed normalization circuit. -/
def endpointSeedRead (p : Nat) (bank : WindowBank) (s : BasisState) : Nat :=
  ((bank.f.value s : ZMod p)*(bank.fv.value s : ZMod p)).val

/-- Bind the canonical endpoint observation to its original-label model using
actual walk execution, without assuming a seed-value equality. -/
theorem seededAuthorWalk_seed_read {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) :
    endpointSeedRead p (walkExitBank walkSeedBank slots)
      (runWithTape (seededAuthorWalkProgram p slots) m ordinal s).basis = scaledInverseSeed p (input x) := by
  have h := seededAuthorWalk_run input p hp x odd good slots compiled s m ordinal ready encoding
  unfold endpointSeedRead scaledInverseSeed
  rw [h.2.2.1.1,h.2.2.1.2.2.1]

/-- The already proved physical endpoint congruence also holds for the
canonical mathematical seed. This is not yet a physical seed-register binding. -/
theorem seededAuthorWalk_seed_relation {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) :
    (scaledInverseSeed p (input x) : ZMod p)*(input x : ZMod p)=
      (2 : ZMod p)^(498+(pinWalk 498 p (input x) 533).offset) := by
  letI : NeZero p := ⟨by intro zero; simp [zero] at odd⟩
  have h := seededAuthorWalk_scaled_inverse input p hp x odd coprime good slots compiled s m ordinal ready encoding
  have run := seededAuthorWalk_run input p hp x odd good slots compiled s m ordinal ready encoding
  have eq := (ZMod.intCast_eq_intCast_iff _ _ p).2 h.2.2.2
  rw [run.2.2.1.1,run.2.2.1.2.2.1,run.1.offset] at eq
  simpa only [scaledInverseSeed,ZMod.natCast_zmod_val,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using eq

end ECDSAAdd.Arithmetic.Paper935
