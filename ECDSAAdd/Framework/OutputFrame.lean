import ECDSAAdd.Framework.RecordedSemantics

namespace ECDSAAdd

/-- Replace only the declared output bits, retaining the phase. -/
def withOutput (O : Finset Wire) (v : BasisState) (s : State) : State :=
  ⟨s.phase,fun q => if q∈O then v q else s.basis q⟩

private theorem write_output (O : Finset Wire) (v b : BasisState) (t : Wire) (x : Bool)
    (ht : t∉O) :
    writeBit (fun q => if q∈O then v q else b q) t x =
      fun q => if q∈O then v q else writeBit b t x q := by
  funext q
  by_cases h : q=t
  · subst q; simp [writeBit,ht]
  · simp [writeBit,h]

private theorem correct_output (cs : List Correction) (O : Finset Wire)
    (v : BasisState) (s : State) (h : Disjoint O (correctionWires cs)) :
    correct cs (withOutput O v s)=withOutput O v (correct cs s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z t =>
      have ht : t∉O := fun hm => Finset.disjoint_left.mp h hm (by simp [correctionWires])
      have hc : Disjoint O (correctionWires cs) := h.mono_right (by intro q hq; simp [correctionWires,hq])
      simpa [correct,withOutput,ht] using ih ⟨s.phase ^^ s.basis t,s.basis⟩ hc
    | CZ a b =>
      have ha : a∉O := fun hm => Finset.disjoint_left.mp h hm (by simp [correctionWires])
      have hb : b∉O := fun hm => Finset.disjoint_left.mp h hm (by simp [correctionWires])
      have hc : Disjoint O (correctionWires cs) := h.mono_right (by intro q hq; simp [correctionWires,hq])
      simpa [correct,withOutput,ha,hb] using ih ⟨s.phase ^^ (s.basis a && s.basis b),s.basis⟩ hc

private theorem one_output (i : Instr) (O : Finset Wire) (v : BasisState)
    (s : State) (m : List Bool) (h : Disjoint O i.wires) :
    run [i] m (withOutput O v s)=withOutput O v (run [i] m s) := by
  have outside : ∀ q∈i.wires,q∉O := fun q hq ho => Finset.disjoint_left.mp h ho hq
  cases i with
  | X t =>
    have ht := outside t (by simp [Instr.wires])
    simp [run,withOutput,ht,write_output O v s.basis t _ ht]
  | CX c t =>
    have hc := outside c (by simp [Instr.wires])
    have ht := outside t (by simp [Instr.wires])
    simp [run,withOutput,hc,ht,write_output O v s.basis t _ ht]
  | CCX a b t =>
    have ha := outside a (by simp [Instr.wires])
    have hb := outside b (by simp [Instr.wires])
    have ht := outside t (by simp [Instr.wires])
    simp [run,withOutput,ha,hb,ht,write_output O v s.basis t _ ht]
  | measureX t c₀ c₁ =>
    have ht := outside t (by simp [Instr.wires])
    have hc : Disjoint O (correctionWires (if m.headD false then c₁ else c₀)) := by
      apply h.mono_right
      split <;> intro q hq <;> simp_all [Instr.wires]
    simp only [run,measureAndCorrect]
    have eqs : (⟨(withOutput O v s).phase ^^ (m.headD false && (withOutput O v s).basis t),
        writeBit (withOutput O v s).basis t false⟩ : State) =
        withOutput O v ⟨s.phase ^^ (m.headD false && s.basis t),writeBit s.basis t false⟩ := by
      simp [withOutput,ht,write_output O v s.basis t false ht]
    rw [eqs,correct_output _ O v _ hc]

/-- A syntactically disjoint output survives every gate, measurement and saved
record correction, without changing the computation or its phase. -/
theorem runWithTape_withOutput (p : RecordedProgram) (O : Finset Wire)
    (v : BasisState) (s : State) (m : List Bool) (k : Nat)
    (h : Disjoint O (recordedWires p)) :
    runWithTape p m k (withOutput O v s)=withOutput O v (runWithTape p m k s) := by
  induction p generalizing k s with
  | nil => rfl
  | cons i p ih =>
    have hi := h.mono_right (Finset.subset_union_left : i.quantumWires⊆i.quantumWires∪recordedWires p)
    have hp := h.mono_right (Finset.subset_union_right : recordedWires p⊆i.quantumWires∪recordedWires p)
    cases i with
    | gate i => rw [runWithTape,one_output i O v s (m.drop k) hi,ih _ _ hp]; rfl
    | phaseFromRecord j cs =>
      simp only [runWithTape]
      split
      · rw [correct_output cs O v s hi,ih _ _ hp]
      · exact ih s k hp

end ECDSAAdd
