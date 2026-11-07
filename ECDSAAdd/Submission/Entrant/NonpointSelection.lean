import ECDSAAdd.Submission.Entrant.PointCardinalityBridge
import ECDSAAdd.Submission.Entrant.SiblingGeneratorOrder
import ECDSAAdd.Submission.Entrant.NonpointXorPair
import Mathlib.SetTheory.Cardinal.Finite

namespace ECDSAAdd.Entrant.NonpointSelection

open Secp256k1 PointCardinalityBridge

theorem exists_pair (offset : Nat) (hoffset : offset < 2 ^ 256) :
    ∃ S N : Nat, 0 < S ∧ S < p ∧ ¬ HasX (S : Fp) ∧
      0 < N ∧ N < p ∧ ¬ HasX (N : Fp) ∧ S = offset ^^^ N := by
  classical
  have hpoints : Nat.card Point = order :=
    point_natCard_eq_order_of_generator_order SiblingOrder.generator_order
  let badSet : Set Fp := {x | ¬ HasX x}
  let badFp : Finset Fp := (Set.toFinite badSet).toFinset
  have hbadCard : badFp.card = p - (order - 1) / 2 := by
    change (Set.toFinite badSet).toFinset.card = _
    rw [← Nat.card_eq_card_finite_toFinset (Set.toFinite badSet)]
    exact nonpoint_natCard_of_point_card hpoints
  have hval : Function.Injective (fun x : Fp => x.val) := by
    intro x y h
    change x.val = y.val at h
    calc
      x = (x.val : Fp) := (ZMod.natCast_zmod_val x).symm
      _ = (y.val : Fp) := by rw [h]
      _ = y := ZMod.natCast_zmod_val y
  let bad : Finset Nat := (badFp.erase 0).image (fun x : Fp => x.val)
  have hcard : bad.card = (badFp.erase 0).card :=
    Finset.card_image_of_injective _ hval
  have herase : badFp.card ≤ (badFp.erase 0).card + 1 := by
    by_cases hzero : (0 : Fp) ∈ badFp
    · have h := Finset.card_erase_add_one hzero
      omega
    · simp only [Finset.erase_eq_of_notMem hzero]
      omega
  have hlarge : 2 ^ 256 < 2 * bad.card := by
    have hmargin : 2 ^ 256 + 2 < 2 * badFp.card := by
      rw [hbadCard]
      norm_num [p, order]
    omega
  have hspec (x : Nat) (hx : x ∈ bad) : 0 < x ∧ x < p ∧ ¬ HasX (x : Fp) := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hyzero, hybad⟩ := Finset.mem_erase.mp hy
    have hpositive : 0 < y.val := by
      by_contra h
      have hz : y.val = 0 := by omega
      apply hyzero
      have hcast := congrArg (fun z : Nat => (z : Fp)) hz
      simpa only [ZMod.natCast_zmod_val, Nat.cast_zero] using hcast
    have hnot : ¬ HasX y := by
      simpa only [badFp, Set.Finite.mem_toFinset, badSet, Set.mem_setOf_eq] using hybad
    exact ⟨hpositive, ZMod.val_lt y, by simpa only [ZMod.natCast_zmod_val] using hnot⟩
  have hbounded : ∀ x ∈ bad, x < 2 ^ 256 := by
    intro x hx
    exact lt_trans (hspec x hx).2.1 (by norm_num [p])
  obtain ⟨N, hN, hS⟩ := NonpointXorPair.exists_pair 256 offset bad hoffset hbounded hlarge
  obtain ⟨hn0, hnp, hnBad⟩ := hspec N hN
  obtain ⟨hs0, hsp, hsBad⟩ := hspec (N ^^^ offset) hS
  exact ⟨N ^^^ offset, N, hs0, hsp, hsBad, hn0, hnp, hnBad, Nat.xor_comm N offset⟩

end ECDSAAdd.Entrant.NonpointSelection
