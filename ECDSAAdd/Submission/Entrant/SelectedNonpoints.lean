import ECDSAAdd.Submission.Entrant.NonpointSelection

namespace ECDSAAdd.Entrant.SelectedNonpoints
open Secp256k1 PointCardinalityBridge

structure Pair (offset : Nat) where
  S : Nat
  N : Nat
  positiveS : 0 < S
  boundedS : S < p
  nonpointS : ¬ HasX (S : Fp)
  positiveN : 0 < N
  boundedN : N < p
  nonpointN : ¬ HasX (N : Fp)
  relation : S = offset ^^^ N

theorem pair_nonempty (offset : Nat) (h : offset < 2 ^ 256) : Nonempty (Pair offset) := by
  obtain ⟨S, N, hs0, hsp, hsbad, hn0, hnp, hnbad, eq⟩ :=
    NonpointSelection.exists_pair offset h
  exact ⟨⟨S, N, hs0, hsp, hsbad, hn0, hnp, hnbad, eq⟩⟩

noncomputable def selected (offset : Nat) (h : offset < 2 ^ 256) : Pair offset :=
  Classical.choice (pair_nonempty offset h)

theorem fourth_eq {offset : Nat} (v : Pair offset) : offset ^^^ v.S = v.N := by
  rw [v.relation, Nat.xor_xor_cancel_left]

theorem distinct {offset : Nat} (v : Pair offset) (ho : offset ≠ 0) : v.S ≠ v.N := by
  intro eq
  have cancel := congrArg (fun x => x ^^^ v.N) v.relation
  change v.S ^^^ v.N = (offset ^^^ v.N) ^^^ v.N at cancel
  rw [eq, Nat.xor_self, Nat.xor_xor_cancel_right] at cancel
  exact ho cancel.symm

theorem S_ne_finite {offset : Nat} (v : Pair offset) {x y : Fp}
    (hc : curve.toAffine.Nonsingular x y) : x.val ≠ v.S := by
  intro eq
  apply v.nonpointS
  have hx : (v.S : Fp) = x := by rw [← eq]; exact ZMod.natCast_zmod_val x
  exact ⟨y, by rw [hx]; exact hc⟩

theorem N_ne_finite {offset : Nat} (v : Pair offset) {x y : Fp}
    (hc : curve.toAffine.Nonsingular x y) : x.val ≠ v.N := by
  intro eq
  apply v.nonpointN
  have hx : (v.N : Fp) = x := by rw [← eq]; exact ZMod.natCast_zmod_val x
  exact ⟨y, by rw [hx]; exact hc⟩

end ECDSAAdd.Entrant.SelectedNonpoints
