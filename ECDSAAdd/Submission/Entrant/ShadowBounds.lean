import ECDSAAdd.Submission.Entrant.ShadowGates
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open SkywalkNat

/-- The far branch alone needs the smaller word to fit the narrowed cutoff. -/
def SmallIfFar (b k : Nat) (z : SkywalkNat.State) : Prop :=
  Shadow.far b k z → min z.u z.v < 2^b

/-- At the end of a block the smaller true word fits the entry cutoff in both branches. -/
def EndSmall (b : Nat) (z : SkywalkNat.State) : Prop :=
  min (step^[15] z).u (step^[15] z).v < 2^b

namespace Envelope

theorem exponent_bound (t : Nat) (h : t ≤ 390) : 512 - t ≤ sbP t + sbP t + 14 := by
  unfold sbP
  omega

theorem small_of_far (b : Nat) (z : SkywalkNat.State)
    (prod : z.u*z.v < 16384 * (2^b * 2^b))
    (far : Shadow.far b 15 z) : min z.u z.v < 2^b := by
  have positive : 0 < Shadow.limb b 15 := by unfold Shadow.limb; positivity
  have hf := (Nat.le_div_iff_mul_le positive).mp far
  have he : Shadow.limb b 15 = 65536*2^b := by
    unfold Shadow.limb
    rw [show b+15+1 = 16+b by omega, pow_add]
    rfl
  rw [he] at hf
  by_contra! large
  have hu := le_trans large (min_le_left z.u z.v)
  have hv := le_trans large (min_le_right z.u z.v)
  have hlarge : 16384*2^b ≤ z.u ∨ 16384*2^b ≤ z.v := by omega
  rcases hlarge with h | h
  · have q := Nat.mul_le_mul h hv
    have e : 16384*2^b*2^b = 16384*(2^b*2^b) := Nat.mul_assoc _ _ _
    omega
  · have q := Nat.mul_le_mul hu h
    have e : 2^b*(16384*2^b) = 16384*(2^b*2^b) := by ring
    omega

theorem endpoint_small (b : Nat) (z : SkywalkNat.State)
    (prod : z.u*z.v < 16384 * (2^b * 2^b)) :
    let e := step^[15] z
    min e.u e.v < 2^b := by
  dsimp only
  have contracted := iter_product_bound 15 z
  change 32768 * ((step^[15] z).u * (step^[15] z).v) ≤ z.u*z.v at contracted
  by_contra! large
  have hu := le_trans large (min_le_left _ _)
  have hv := le_trans large (min_le_right _ _)
  have both := Nat.mul_le_mul hu hv
  omega

theorem inputs_through (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 512) :
    let b := sbP t
    let z := step^[t] (init x p)
    SmallIfFar b 15 z ∧ EndSmall b z := by
  let z := step^[t] (init x p)
  have strict : x*p < 2^512 := by
    rw [show (512:Nat)=256+256 by decide, pow_add]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hx.le) (Nat.mul_lt_mul_of_pos_left hp (by positivity))
  have h := iter_product_bound t (init x p)
  change 2^t*(z.u*z.v) ≤ x*p at h
  have stepBound : z.u*z.v < 2^(512-t) := by
    have e : (2:Nat)^512 = 2^t*2^(512-t) := by rw [← pow_add]; congr 1; omega
    rw [e] at strict
    exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h strict)
  have envelope : 512 - t ≤ sbP t + sbP t + 14 := by unfold sbP; omega
  have power := Nat.pow_le_pow_right (by decide : 0 < 2) envelope
  have e : 2^(sbP t + sbP t + 14) = 16384*(2^(sbP t)*2^(sbP t)) := by
    rw [pow_add, pow_add, Nat.mul_comm]
    rfl
  have prod := lt_of_lt_of_le stepBound (power.trans_eq e)
  exact ⟨small_of_far _ _ prod, endpoint_small _ _ prod⟩

theorem inputs (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 390) :
    let b := sbP t
    let z := step^[t] (init x p)
    SmallIfFar b 15 z ∧ EndSmall b z :=
  inputs_through x p t hx hp (by omega)

/-- The hand-off uses the next cutoff only when the next state is far. -/
theorem nextFarSmall (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 390) :
    SmallIfFar (sbP (t+15)) 15 (step^[15] (step^[t] (init x p))) := by
  rw [← Function.iterate_add_apply, Nat.add_comm 15 t]
  exact (inputs_through x p (t+15) hx hp (by omega)).1

end Envelope
end ECDSAAdd.Entrant.StairPacket.Shadow7
