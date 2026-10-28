import ECDSAAdd.Math.FusedSignedHalf

namespace ECDSAAdd.FusedSignedHalf
open Secp256k1

/-- Canonical mathematical inverse. This is a specification for the independent
emitted inverse endpoint, not a gate implementation or resource claim. -/
def inverseValue (b : Bool) (R Y : Nat) : Nat :=
  (2*(R : Fp)-(if b then -(Y : Fp) else (Y : Fp))).val

theorem inverseValue_bound (b : Bool) (R Y : Nat) :
    inverseValue b R Y<ECDSAAdd.p := by
  letI : NeZero ECDSAAdd.p := ⟨p_prime.ne_zero⟩
  exact ZMod.val_lt _

theorem inverseValue_field (b : Bool) (R Y : Nat) :
    (inverseValue b R Y : Fp)=2*(R : Fp)-(if b then -(Y : Fp) else (Y : Fp)) := by
  letI : NeZero ECDSAAdd.p := ⟨p_prime.ne_zero⟩
  simp only [inverseValue,ZMod.natCast_zmod_val]

private theorem inverse_two_nonzero : (2 : Fp)≠0 := by decide

/-- Every canonical output has an exact canonical preimage, including zero,
ties and modulus boundaries. This removes any sampled-input premise from the
future inverse gate proof. -/
theorem result_inverseValue (b : Bool) (R Y : Nat)
    (hR : R<ECDSAAdd.p) (hY : Y<ECDSAAdd.p) :
    result ECDSAAdd.p b (inverseValue b R Y) Y=R := by
  letI : NeZero ECDSAAdd.p := ⟨p_prime.ne_zero⟩
  have hid := field_identity (inverseValue b R Y) Y b
    (inverseValue_bound b R Y) hY
  rw [inverseValue_field] at hid
  have hfield : (result ECDSAAdd.p b (inverseValue b R Y) Y : Fp)=(R : Fp) := by
    rw [hid]
    apply (div_eq_iff inverse_two_nonzero).mpr
    ring
  have hv := congrArg (fun z : Fp => z.val) hfield
  dsimp only at hv
  rw [ZMod.val_natCast_of_lt (result_spec ECDSAAdd.p (inverseValue b R Y) Y b
    (by norm_num [ECDSAAdd.p]) (inverseValue_bound b R Y) hY).1,
    ZMod.val_natCast_of_lt hR] at hv
  exact hv

/-- The inverse specification also recovers the original canonical input. -/
theorem inverseValue_result (b : Bool) (X Y : Nat)
    (hX : X<ECDSAAdd.p) (hY : Y<ECDSAAdd.p) :
    inverseValue b (result ECDSAAdd.p b X Y) Y=X := by
  letI : NeZero ECDSAAdd.p := ⟨p_prime.ne_zero⟩
  have hid := field_identity X Y b hX hY
  have hfield : (inverseValue b (result ECDSAAdd.p b X Y) Y : Fp)=(X : Fp) := by
    rw [inverseValue_field,hid]
    rw [mul_comm (2 : Fp),div_mul_cancel₀ _ inverse_two_nonzero]
    ring
  have hv := congrArg (fun z : Fp => z.val) hfield
  dsimp only at hv
  rw [ZMod.val_natCast_of_lt (inverseValue_bound b _ Y),
    ZMod.val_natCast_of_lt hX] at hv
  exact hv

end ECDSAAdd.FusedSignedHalf
