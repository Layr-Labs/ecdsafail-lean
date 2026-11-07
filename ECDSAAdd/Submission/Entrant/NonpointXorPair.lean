import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Lean.Elab.Tactic.Omega

namespace ECDSAAdd.Entrant.NonpointXorPair

/-- A subset larger than half a binary word space meets each XOR translate. -/
theorem exists_pair (width offset : Nat) (bad : Finset Nat)
    (hoffset : offset < 2 ^ width)
    (hbounded : ∀ x ∈ bad, x < 2 ^ width)
    (hlarge : 2 ^ width < 2 * bad.card) :
    ∃ x ∈ bad, x ^^^ offset ∈ bad := by
  classical
  have hinjective : Function.Injective (fun x : Nat => x ^^^ offset) := by
    intro x y h
    have h' := congrArg (fun z : Nat => z ^^^ offset) h
    simpa only [Nat.xor_xor_cancel_right] using h'
  have hcard : (bad.image (fun x => x ^^^ offset)).card = bad.card :=
    Finset.card_image_of_injective bad hinjective
  by_contra hnone
  have hdisjoint : Disjoint bad (bad.image (fun x => x ^^^ offset)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hi
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hi
    exact hnone ⟨y, hy, he.symm ▸ hx⟩
  have hsubset : bad ∪ bad.image (fun x => x ^^^ offset) ⊆ Finset.range (2 ^ width) := by
    intro x hx
    apply Finset.mem_range.mpr
    rcases Finset.mem_union.mp hx with hb | hi
    · exact hbounded x hb
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
      exact Nat.xor_lt_two_pow (hbounded y hy) hoffset
  have hupper := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisjoint, hcard, Finset.card_range] at hupper
  omega

end ECDSAAdd.Entrant.NonpointXorPair
