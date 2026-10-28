import ECDSAAdd.Arithmetic.Paper935.AuthorWalkEndpoint

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- The endpoint facts needed by the author's reversible closer, read from
its actual compiled bank. In particular gv=f*p follows from the determinant
invariant, not a new endpoint assumption. -/
theorem seededAuthorWalk_closer_endpoint {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) :
    let out := runWithTape (seededAuthorWalkProgram p slots) m ordinal s
    let bank := walkExitBank walkSeedBank slots
    bank.g.value out.basis=0 ∧ (bank.f.value out.basis).natAbs=1 ∧
      bank.gv.value out.basis=bank.f.value out.basis*p := by
  have executed := seededAuthorWalk_run input p hp x odd good slots compiled s m ordinal ready encoding
  obtain ⟨_,_,noEarly,deadline,_,_⟩ :=
    trajectory_good input p 498 7 533 7 authorHistoryCapacityAt authorWindows x good
  obtain ⟨t,_,_,_,zero,rows⟩ := pinWalk_stopping_time 498 (by omega) p (input x) noEarly 533 deadline
  have endpoint := endpoint_zWalk odd coprime t zero
  dsimp only
  have encoded := executed.2.2.1
  rw [rows] at encoded
  exact ⟨encoded.2.1.trans zero,encoded.1 ▸ endpoint.1,by rw [encoded.2.2.2,encoded.1]; exact endpoint.2⟩

end ECDSAAdd.Arithmetic.Paper935
