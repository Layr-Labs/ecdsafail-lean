import ECDSAAdd.Arithmetic.Paper935.DecoderWindow

namespace ECDSAAdd.Arithmetic.Paper935

private theorem split_prefix (xs : List Wire) (n : Nat) (h : n<xs.length) :
    ∃ front tail, xs=front++tail ∧ front.length=n ∧ tail≠[] := by
  refine ⟨xs.take n,xs.drop n,(List.take_append_drop n xs).symm,?_,?_⟩
  · simp [List.length_take,Nat.min_eq_left (by omega : n≤xs.length)]
  · intro he
    have hl : (xs.drop n).length=xs.length-n := List.length_drop
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega

/-- The physical f row supplies the two low selector wires, four lookup
inputs and a nonempty signed tail once six payload wires exist. -/
theorem WindowRow.f_decoder_view (r : WindowRow) (h : 6≤r.payload.length) :
    ∃ flow address data tail, r.wires=flow::address::(data++tail) ∧
      data.length=4 ∧ tail≠[] := by
  have hl : 7≤r.wires.length := by simp only [WindowRow.wires,List.length_append,List.length_singleton]; omega
  generalize r.wires=xs at *
  cases xs with
  | nil => simp at hl
  | cons flow xs =>
    cases xs with
    | nil => simp at hl
    | cons address rest =>
      have hr : 4<rest.length := by simp only [List.length_cons] at hl; omega
      obtain ⟨data,tail,he,hd,ht⟩ := split_prefix rest 4 hr
      exact ⟨flow,address,data,tail,by rw [he],hd,ht⟩

/-- Two views of the same physical coefficient row: the divisibility
predicate's low prefix and the quotient lookup's shifted five-bit word.
Both tails retain at least the sign wire. -/
theorem WindowRow.fv_decoder_views (r : WindowRow) (depth : Nat)
    (h : depth+6≤r.payload.length) :
    (∃ low bits tail, r.wires=low::(bits++tail) ∧ bits.length=depth ∧ tail≠[]) ∧
    (∃ slice low bits tail, r.wires=slice++low::(bits++tail) ∧
      slice.length=depth ∧ bits.length=5 ∧ tail≠[]) := by
  have hl : depth+7≤r.wires.length := by simp only [WindowRow.wires,List.length_append,List.length_singleton]; omega
  constructor
  · generalize r.wires=xs at *
    cases xs with
    | nil => simp at hl
    | cons low rest =>
      have hr : depth<rest.length := by simp only [List.length_cons] at hl; omega
      obtain ⟨bits,tail,he,hb,ht⟩ := split_prefix rest depth hr
      exact ⟨low,bits,tail,by rw [he],hb,ht⟩
  · obtain ⟨slice,rest,he,hs,ht⟩ := split_prefix r.wires depth (by omega)
    cases rest with
    | nil => exact (ht rfl).elim
    | cons low rest =>
      have hr : 5<rest.length := by
        rw [he,List.length_append,List.length_cons,hs] at hl
        omega
      obtain ⟨bits,tail,hrest,hb,htail⟩ := split_prefix rest 5 hr
      exact ⟨slice,low,bits,tail,by rw [he,hrest],hs,hb,htail⟩

end ECDSAAdd.Arithmetic.Paper935
