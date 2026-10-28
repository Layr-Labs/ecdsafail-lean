import ECDSAAdd.Math.Divsteps.Invariant
import ECDSAAdd.Math.Divsteps.Recovery

namespace ECDSAAdd.Divsteps

/-- Once a walk is frozen, later scheduled slots preserve the entire state. -/
theorem zWalk_frozen (p x : Int) (t : Nat) (h : (zWalk p x t).g = 0) (u : Nat) :
    zWalk p x (t + u) = zWalk p x t := by
  induction u with
  | zero => simp
  | succ u ih => rw [Nat.add_succ, zWalk_succ, ih, if_pos h]

/-- A fixed-slot endpoint is scaled by the number of active steps, which
can be smaller than the slot count. This distinction is essential for early
termination; using `2^N` with frozen coefficient registers would be wrong. -/
theorem bounded_inverse (p x : Int) (hp : p % 2 = 1) (hcop : Int.gcd p x = 1)
    (N : Nat) (hend : (zWalk p x N).g = 0) :
    ∃ t ≤ N, (∀ u < t, (zWalk p x u).g ≠ 0) ∧
      (zWalk p x N).f * (zWalk p x N).fv * x ≡ 2^t [ZMOD p] := by
  have hex : ∃ t, (zWalk p x t).g = 0 := ⟨N, hend⟩
  let t := Nat.find hex
  have ht : (zWalk p x t).g = 0 := Nat.find_spec hex
  have hle : t ≤ N := Nat.find_min' hex hend
  have hactive : ∀ u < t, (zWalk p x u).g ≠ 0 := fun u hu => Nat.find_min hex hu
  have hsame : zWalk p x N = zWalk p x t := by
    simpa only [Nat.add_sub_of_le hle] using zWalk_frozen p x t ht (N - t)
  refine ⟨t, hle, hactive, ?_⟩
  rw [hsame]
  exact inverse_zWalk hp hcop t hactive ht

/-- Generic connection from a checked hull certificate to the frozen walk.
The certificate remains an explicit hypothesis until a concrete instance
has been proved with the permitted axioms. -/
theorem zWalk_of_certificate (N : Nat) (M p x : Int)
    (hp : p % 2 = 1) (hpM : p ≤ M) (hx0 : 0 ≤ x) (hxp : x ≤ p)
    (hcert : certEmpty M N = true) : (zWalk p x N).g = 0 := by
  rw [(zWalk_hdRun p x N).2.1]
  exact g_reaches_zero N M p x hp hpM hx0 hxp hcert

set_option maxRecDepth 10000 in
/-- A small closed certificate exercises the actual checker with kernel
reduction. It is deliberately not a secp256k1 termination claim. -/
theorem small_certificate : certEmpty 2 3 = true := by decide +kernel

end ECDSAAdd.Divsteps
