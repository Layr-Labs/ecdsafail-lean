import ECDSAAdd.Arithmetic.Paper935.PublicSlotLocality

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Freezing preserves the mathematical divstep invariant. -/
theorem pinStep_inv (tmin index : Nat) (p : Int) (old : PinState)
    (inv : Inv p old.rows) (odd : p%2=1) : Inv p (pinStep tmin index old).rows := by
  rw [pinStep_rows]
  split
  · exact inv
  · exact inv.zStep odd

theorem pinWalk_inv (tmin : Nat) (p x : Int) (odd : p%2=1) (t : Nat) :
    Inv p (pinWalk tmin p x t).rows := by
  induction t with
  | zero => exact inv_zSeed odd
  | succ t ih => exact pinStep_inv tmin t p _ ih odd

/-- Only a genuine zero test can freeze the integer control model. -/
theorem pinStep_frozen_zero (tmin index : Nat) (old : PinState)
    (oldZero : old.frozen=true → old.rows.g=0) :
    (pinStep tmin index old).frozen=true → (pinStep tmin index old).rows.g=0 := by
  unfold pinStep
  split
  · exact oldZero
  · dsimp only
    split
    next h => exact fun _ => h.2
    next h => simp

theorem pinWalk_frozen_zero (tmin : Nat) (p x : Int) (t : Nat) :
    (pinWalk tmin p x t).frozen=true → (pinWalk tmin p x t).rows.g=0 := by
  induction t with
  | zero => simp [pinWalk]
  | succ t ih => exact pinStep_frozen_zero tmin t _ ih

/-- Both offset premises of the actual post-stage follow from its mathematical
record invariant, independently of numerical trajectory success. -/
theorem pinWalk_offset_inputs (tmin : Nat) (p x : Int) (t : Nat) :
    (tmin≤t → (pinWalk tmin p x t).offset<t+1-tmin) ∧
    ((pinWalk tmin p x t).frozen=false → (pinWalk tmin p x t).offset=0) := by
  have record := pinWalk_record tmin p x t
  constructor
  · intro ht
    have h := record.2
    omega
  · intro hf
    have hn : ¬0<(pinWalk tmin p x t).offset := fun h => by
      have he := record.1.mpr h
      rw [hf] at he
      contradiction
    omega

end ECDSAAdd.Arithmetic.Paper935
