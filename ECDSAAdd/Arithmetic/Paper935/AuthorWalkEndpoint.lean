import ECDSAAdd.Arithmetic.Paper935.SeededAuthorWalkRun
import ECDSAAdd.Arithmetic.Paper935.PinStoppingTime

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- Read the scaled inverse directly from the actual final bank. The exponent
is the stored stopping offset plus 498, not the fixed schedule length 533. -/
theorem seededAuthorWalk_scaled_inverse {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) :
    let out := runWithTape (seededAuthorWalkProgram p slots) m ordinal s
    let bank := walkExitBank walkSeedBank slots
    out.basis walkRegisters.frozen=true ∧ bank.g.value out.basis=0 ∧
    (bank.f.value out.basis).natAbs=1 ∧
    bank.f.value out.basis * bank.fv.value out.basis * input x ≡
      2^(498+regValue walkRegisters.offset out.basis) [ZMOD (p : Int)] := by
  have run := seededAuthorWalk_run input p hp x odd good slots compiled s m ordinal ready encoding
  obtain ⟨_,_,noEarly,deadline,_,_⟩ :=
    trajectory_good input p 498 7 533 7 authorHistoryCapacityAt authorWindows x good
  obtain ⟨t,_,offset,first,zero,rows⟩ := pinWalk_stopping_time 498 (by omega) p (input x) noEarly 533 deadline
  have ep := endpoint_zWalk odd coprime t zero
  have inverse := inverse_zWalk odd coprime t first zero
  dsimp only
  have encoded := run.2.2.1
  rw [rows] at encoded
  refine ⟨run.1.frozen.trans deadline,encoded.2.1.trans zero,?_,?_⟩
  · rw [encoded.1]; exact ep.1
  · rw [encoded.1,encoded.2.2.1,run.1.offset,←offset]
    exact inverse

end ECDSAAdd.Arithmetic.Paper935
