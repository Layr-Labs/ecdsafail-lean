import ECDSAAdd.Framework.Semantics
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd

def parityAt (basis : BasisState) : List Wire → Bool
  | [] => false
  | w :: ws => basis w ^^ parityAt basis ws

theorem correctZs (ws : List Wire) (s : State) :
    correct (ws.map Correction.Z) s = ⟨s.phase ^^ parityAt s.basis ws, s.basis⟩ := by
  induction ws generalizing s with
  | nil => simp [correct, parityAt]
  | cons w ws ih =>
    simp only [List.map_cons, correct, ih, parityAt]
    congr 1
    exact Bool.xor_assoc _ _ _

theorem parityAt_update (basis : BasisState) (t : Wire) (ws : List Wire)
    (h : ∀ w ∈ ws, w ≠ t) : parityAt (writeBit basis t false) ws = parityAt basis ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [parityAt]
    rw [show writeBit basis t false w = basis w by simpa [writeBit] using (Function.update_of_ne (h w (by simp)) false basis)]
    rw [ih (fun w hw => h w (by simp [hw]))]

theorem eraseLinear (ws : List Wire) (t : Wire) (s : State) (m : List Bool)
    (h : ∀ w ∈ ws, w ≠ t) (hv : s.basis t = parityAt s.basis ws) :
    run [.measureX t [] (ws.map Correction.Z)] m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  cases hm : m.headD false
  · simp only [run, measureAndCorrect, hm, Bool.false_eq_true, if_false, correct, Bool.false_and, Bool.xor_false]
  · simp only [run, measureAndCorrect, hm, if_true, Bool.true_and, correctZs]
    rw [parityAt_update _ _ _ h, hv]
    simp
theorem eraseTwoProductsLinear (a b c d t : Wire) (ws : List Wire)
    (ha : a ≠ t) (hb : b ≠ t) (hc : c ≠ t) (hd : d ≠ t)
    (h : ∀ w ∈ ws, w ≠ t) (s : State) (m : List Bool)
    (hv : s.basis t = ((s.basis a && s.basis b) ^^ (s.basis c && s.basis d) ^^ parityAt s.basis ws)) :
    run [.measureX t [] ([.CZ a b, .CZ c d] ++ ws.map Correction.Z)] m s =
      ⟨s.phase, writeBit s.basis t false⟩ := by
  cases hm : m.headD false
  · simp only [run, measureAndCorrect, hm, Bool.false_eq_true, if_false, correct, Bool.false_and, Bool.xor_false]
  · simp only [run, measureAndCorrect, hm, if_true, Bool.true_and, List.cons_append, correct,
      writeBit, Function.update_of_ne ha, Function.update_of_ne hb, Function.update_of_ne hc,
      Function.update_of_ne hd, correctZs]
    simp only [List.nil_append, correctZs]
    have hp := parityAt_update s.basis t ws h
    simp only [writeBit] at hp
    rw [hp, hv]
    cases s.phase <;> cases s.basis a <;> cases s.basis b <;> cases s.basis c <;> cases s.basis d <;> cases parityAt s.basis ws <;> simp_all

theorem eraseOneProductLinear (a b t : Wire) (ws : List Wire)
    (ha : a ≠ t) (hb : b ≠ t) (h : ∀ w ∈ ws, w ≠ t) (s : State) (m : List Bool)
    (hv : s.basis t = ((s.basis a && s.basis b) ^^ parityAt s.basis ws)) :
    run [.measureX t [] ([.CZ a b] ++ ws.map Correction.Z)] m s =
      ⟨s.phase, writeBit s.basis t false⟩ := by
  cases hm : m.headD false
  · simp only [run, measureAndCorrect, hm, Bool.false_eq_true, if_false, correct, Bool.false_and, Bool.xor_false]
  · simp only [run, measureAndCorrect, hm, if_true, Bool.true_and, List.cons_append, correct,
      writeBit, Function.update_of_ne ha, Function.update_of_ne hb]
    simp only [List.nil_append, correctZs]
    have hp := parityAt_update s.basis t ws h
    simp only [writeBit] at hp
    rw [hp, hv]
    cases s.phase <;> cases s.basis a <;> cases s.basis b <;> cases parityAt s.basis ws <;> simp_all

def compareCorrections (bit : Bool) (x v e : Wire) (ws : List Wire) : List Correction :=
  (if bit then [.CZ x v] else [.CZ x v, .CZ e x, .Z v]) ++ ws.map Correction.Z

theorem eraseCompareAccumulator (bit : Bool) (x v e t : Wire) (ws : List Wire)
    (hx : x ≠ t) (hv : v ≠ t) (he : e ≠ t) (h : ∀ w ∈ ws, w ≠ t)
    (s : State) (m : List Bool)
    (ht : s.basis t = (((s.basis x == bit) && s.basis v) ^^ parityAt s.basis ws ^^
      (s.basis e && (s.basis x && !bit)))) :
    run [.measureX t [] (compareCorrections bit x v e ws)] m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  cases bit
  · have hws : ∀ w ∈ v::ws, w ≠ t := by simpa using And.intro hv h
    have ht' : s.basis t = ((s.basis x && s.basis v) ^^ (s.basis e && s.basis x) ^^ parityAt s.basis (v::ws)) := by
      simp only [parityAt]
      rw [ht]
      cases s.basis x <;> cases s.basis v <;> cases s.basis e <;> cases parityAt s.basis ws <;> simp_all
    simpa [compareCorrections] using eraseTwoProductsLinear x v e x t (v::ws) hx hv he hx hws s m ht'
  · have ht' : s.basis t = ((s.basis x && s.basis v) ^^ parityAt s.basis ws) := by
      rw [ht]
      cases s.basis x <;> cases s.basis v <;> cases s.basis e <;> cases parityAt s.basis ws <;> simp_all
    simpa [compareCorrections] using eraseOneProductLinear x v t ws hx hv h s m ht'

end ECDSAAdd
