import ECDSAAdd.Framework.Hoare

namespace ECDSAAdd

private theorem write_agree (S : Finset Wire) (s t : BasisState) (q : Wire) (v : Bool)
    (h : ∀ w∈S,s w=t w) : ∀ w∈S,writeBit s q v w=writeBit t q v w := by
  intro w hw
  by_cases he : w=q <;> simp [writeBit,Function.update,he,h w hw]

/-- Immediate Z/CZ corrections depend only on their declared support. -/
theorem correct_phase_locality (cs : List Correction) (S : Finset Wire)
    (hc : correctionWires cs⊆S) (s t : State) (hp : s.phase=t.phase)
    (hb : ∀ w∈S,s.basis w=t.basis w) : (correct cs s).phase=(correct cs t).phase := by
  induction cs generalizing s t with
  | nil => exact hp
  | cons c cs ih =>
    cases c with
    | Z q =>
      have hq := hb q (hc (by simp [correctionWires]))
      apply ih (fun w hw => hc (by simp [correctionWires,hw]))
        ⟨s.phase ^^ s.basis q,s.basis⟩ ⟨t.phase ^^ t.basis q,t.basis⟩
      · simp [hp,hq]
      · exact hb
    | CZ a b =>
      have ha := hb a (hc (by simp [correctionWires]))
      have hb' := hb b (hc (by simp [correctionWires]))
      apply ih (fun w hw => hc (by simp [correctionWires,hw]))
        ⟨s.phase ^^ (s.basis a && s.basis b),s.basis⟩
        ⟨t.phase ^^ (t.basis a && t.basis b),t.basis⟩
      · simp [hp,ha,hb']
      · exact hb

/-- Measured programs with the same tape depend only on their full declared
support, including all immediate phase-correction inputs. Agreement on a
larger support is preserved; basis bits outside it may differ arbitrarily. -/
theorem run_measured_locality (p : Program) (S : Finset Wire) (hw : wires p⊆S)
    (s t : State) (m : List Bool) (hp : s.phase=t.phase)
    (hb : ∀ w∈S,s.basis w=t.basis w) :
    (run p m s).phase=(run p m t).phase ∧
    ∀ w∈S,(run p m s).basis w=(run p m t).basis w := by
  induction p generalizing s t m with
  | nil => exact ⟨hp,hb⟩
  | cons i p ih =>
    have hi : i.wires⊆S := fun w hw' => hw (Finset.mem_union_left _ hw')
    have ht : wires p⊆S := fun w hw' => hw (Finset.mem_union_right _ hw')
    cases i with
    | X q =>
      have hq := hb q (hi (by simp [Instr.wires]))
      simp only [run]
      refine ih ht _ _ m hp ?_
      simpa only [hq] using write_agree S s.basis t.basis q (!t.basis q) hb
    | CX c q =>
      have hc := hb c (hi (by simp [Instr.wires]))
      have hq := hb q (hi (by simp [Instr.wires]))
      simp only [run]
      refine ih ht _ _ m hp ?_
      simpa only [hq,hc] using write_agree S s.basis t.basis q (t.basis q ^^ t.basis c) hb
    | CCX a b q =>
      have ha := hb a (hi (by simp [Instr.wires]))
      have hb' := hb b (hi (by simp [Instr.wires]))
      have hq := hb q (hi (by simp [Instr.wires]))
      simp only [run]
      refine ih ht _ _ m hp ?_
      simpa only [hq,ha,hb'] using write_agree S s.basis t.basis q
        (t.basis q ^^ (t.basis a && t.basis b)) hb
    | measureX q c0 c1 =>
      have hq := hb q (hi (by simp [Instr.wires]))
      have hc : correctionWires (if m.headD false then c1 else c0)⊆S := by
        intro w hw'
        apply hi
        split at hw' <;> simp [Instr.wires,hw']
      apply ih ht _ _ m.tail
      · apply correct_phase_locality _ S hc
        · simp [hp,hq]
        · exact write_agree S s.basis t.basis q false hb
      · simpa only [measureAndCorrect,correct_basis] using write_agree S s.basis t.basis q false hb

end ECDSAAdd
