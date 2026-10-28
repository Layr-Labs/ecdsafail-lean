import ECDSAAdd.Arithmetic.BalancedFoldMath

set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic.BalancedFold
open BalancedField BalancedCircuit

/-- Repeated virtual source positions touch only the two immutable selectors. -/
theorem foldBits_sources (L : BalancedCircuit.Layout) (w : Wire)
    (hw : w∈mappedWires (foldBits L)) : w=L.plus ∨ w=L.minus := by
  obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp hw
  rw [foldBits] at hb
  rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨i,hi,he⟩ := List.mem_map.mp hb
    subst b
    cases ht : sparseF.testBit (i+1)
    · right; simpa [ht] using hm
    · left; simpa [ht] using hm
  · have he : b={wire:=none,flip:=false} := by simpa using hb
    subst b
    simp at hm

theorem toggle_top_value (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T=
      if originalParity T then
        if encodeWord 257 T/modulusWord=0 then
          encodeWord 257 T+modulusWord else encodeWord 257 T-modulusWord
      else encodeWord 257 T := by
  rw [raw_sign T ht]
  cases ha : originalParity T <;> cases hs : decide (T<0) <;>
    simp [toggledWord,ha,hs]

private theorem generic_toggle_bound (M U r : Nat) (a s : Bool)
    (hr : r<M) (hd : r+M*s.toNat=U) :
    (if a then if s then U-M else U+M else U)<2*M := by
  cases a <;> cases s <;> simp at hd ⊢ <;> omega

theorem toggledWord_bound (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T<2^257 := by
  have hd := Nat.mod_add_div (encodeWord 257 T) modulusWord
  rw [raw_sign T ht] at hd
  have hr := Nat.mod_lt (encodeWord 257 T) (show 0<modulusWord by norm_num [modulusWord])
  have h := generic_toggle_bound modulusWord (encodeWord 257 T)
    (encodeWord 257 T%modulusWord) (originalParity T) (decide (T<0)) hr hd
  have hm : 2*modulusWord=(2^257 : Nat) := by decide
  simpa only [toggledWord,hm] using h

/-- CX of the parity into the original low bit clears that bit exactly. -/
theorem parity_clear_value (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T-(originalParity T).toNat=2*(toggledWord T/2) := by
  have h := cleared_low_word T ht
  omega

private theorem generic_half_bound (U M : Nat) (h : U<2*M) : U/2<M := by omega

theorem prepared_upper_bound (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T/2<modulusWord := by
  have h := toggledWord_bound T ht
  have hm : 2*modulusWord=(2^257 : Nat) := by decide
  rw [←hm] at h
  exact generic_half_bound _ _ h

end ECDSAAdd.Arithmetic.BalancedFold

#print axioms ECDSAAdd.Arithmetic.BalancedFold.foldBits_sources
#print axioms ECDSAAdd.Arithmetic.BalancedFold.toggle_top_value
#print axioms ECDSAAdd.Arithmetic.BalancedFold.toggledWord_bound
#print axioms ECDSAAdd.Arithmetic.BalancedFold.parity_clear_value
#print axioms ECDSAAdd.Arithmetic.BalancedFold.prepared_upper_bound
