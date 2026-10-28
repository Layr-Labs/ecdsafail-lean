import ECDSAAdd.Framework.WireRename

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd

private theorem pool_write_rename (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀a∈S,∀b∈S,f a=f b → a=b) (a : Wire) (ha : a∈S)
    (logical physical : BasisState) (v : Bool)
    (hb : ∀q∈S,logical q=physical (f q)) :
    ∀q∈S,writeBit logical a v q=writeBit physical (f a) v (f q) := by
  intro q hq
  by_cases same : q=a
  · subst q
    simp [writeBit]
  · have different : f q≠f a := fun eq => same (hf q hq a ha eq)
    simp [writeBit,Function.update,same,different,hb q hq]

private theorem pool_correct_rename (f : Wire → Wire) (S : Finset Wire)
    (cs : List Correction) (hc : correctionWires cs⊆S) (t s : State)
    (hp : t.phase=s.phase) (hb : ∀q∈S,t.basis q=s.basis (f q)) :
    (correct cs t).phase=(correct (cs.map (renameCorrection f)) s).phase ∧
    ∀q∈S,(correct cs t).basis q=(correct (cs.map (renameCorrection f)) s).basis (f q) := by
  induction cs generalizing t s with
  | nil => exact ⟨hp,hb⟩
  | cons c cs ih =>
    have tail : correctionWires cs⊆S := by
      intro q hq
      apply hc
      cases c <;> exact Finset.mem_union_right _ hq
    cases c with
    | Z a =>
      simp only [List.map_cons,renameCorrection,correct]
      apply ih tail
      · simp only [hp,hb a (hc (by simp [correctionWires]))]
      · exact hb
    | CZ a b =>
      simp only [List.map_cons,renameCorrection,correct]
      apply ih tail
      · simp only [hp,hb a (hc (by simp [correctionWires])),
          hb b (hc (by simp [correctionWires]))]
      · exact hb

private theorem pool_run_rename (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀a∈S,∀b∈S,f a=f b → a=b) (p : Program) (hw : wires p⊆S)
    (m : List Bool) (t s : State) (hp : t.phase=s.phase)
    (hb : ∀q∈S,t.basis q=s.basis (f q)) :
    (run p m t).phase=(run (renameProgram f p) m s).phase ∧
    ∀q∈S,(run p m t).basis q=(run (renameProgram f p) m s).basis (f q) := by
  induction p generalizing m t s with
  | nil => exact ⟨hp,hb⟩
  | cons i p ih =>
    have tail : wires p⊆S := fun q hq => hw (Finset.mem_union_right _ hq)
    have head : i.wires⊆S := fun q hq => hw (Finset.mem_union_left _ hq)
    cases i with
    | X a =>
      have ha : a∈S := head (by simp [Instr.wires])
      simp only [renameProgram,List.map_cons,renameInstr,run]
      apply ih tail
      · exact hp
      · rw [hb a ha]
        exact pool_write_rename f S hf a ha t.basis s.basis _ hb
    | CX a q =>
      have ha : a∈S := head (by simp [Instr.wires])
      have hq : q∈S := head (by simp [Instr.wires])
      simp only [renameProgram,List.map_cons,renameInstr,run]
      apply ih tail
      · exact hp
      · rw [hb q hq,hb a ha]
        exact pool_write_rename f S hf q hq t.basis s.basis _ hb
    | CCX a b q =>
      have ha : a∈S := head (by simp [Instr.wires])
      have hb0 : b∈S := head (by simp [Instr.wires])
      have hq : q∈S := head (by simp [Instr.wires])
      simp only [renameProgram,List.map_cons,renameInstr,run]
      apply ih tail
      · exact hp
      · rw [hb q hq,hb a ha,hb b hb0]
        exact pool_write_rename f S hf q hq t.basis s.basis _ hb
    | measureX q c0 c1 =>
      have hq : q∈S := head (by simp [Instr.wires])
      have corrections : correctionWires (if m.headD false then c1 else c0)⊆S := by
        cases outcome : m.headD false <;> simp only [outcome,Bool.false_eq_true,if_false,if_true]
        · intro a ha
          exact head (Finset.mem_union_left _ (Finset.mem_union_right _ ha))
        · intro a ha
          exact head (Finset.mem_union_right _ ha)
      have selected : (if m.headD false then c1 else c0).map (renameCorrection f)=
          (if m.headD false then c1.map (renameCorrection f) else c0.map (renameCorrection f)) := by
        cases m.headD false <;> rfl
      have updated := pool_correct_rename f S (if m.headD false then c1 else c0) corrections
        ⟨t.phase ^^ (m.headD false && t.basis q),writeBit t.basis q false⟩
        ⟨s.phase ^^ (m.headD false && s.basis (f q)),writeBit s.basis (f q) false⟩
        (by simp only [hp,hb q hq])
        (pool_write_rename f S hf q hq t.basis s.basis false hb)
      have measured :
          (measureAndCorrect q c0 c1 (m.headD false) t).phase=
            (measureAndCorrect (f q) (c0.map (renameCorrection f))
              (c1.map (renameCorrection f)) (m.headD false) s).phase ∧
          ∀a∈S,(measureAndCorrect q c0 c1 (m.headD false) t).basis a=
            (measureAndCorrect (f q) (c0.map (renameCorrection f))
              (c1.map (renameCorrection f)) (m.headD false) s).basis (f a) := by
        simpa only [measureAndCorrect,selected] using updated
      simp only [renameProgram,List.map_cons,renameInstr,run]
      exact ih tail m.tail _ _ measured.1 measured.2

/-- Finite-support semantic relabeling. Only wires inside S must be
injectively placed and related to the logical input. Both correction lists
are covered by actual instruction support; measurement records are arbitrary. -/
theorem run_rename_pool (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀a∈S,∀b∈S,f a=f b → a=b) (p : Program) (hw : wires p⊆S)
    (m : List Bool) (t s : State) (hp : t.phase=s.phase)
    (hb : ∀q∈S,t.basis q=s.basis (f q)) :
    (run (renameProgram f p) m s).phase=(run p m t).phase ∧
    ∀q∈S,(run (renameProgram f p) m s).basis (f q)=(run p m t).basis q := by
  have equality := pool_run_rename f S hf p hw m t s hp hb
  exact ⟨equality.1.symm,fun q hq => (equality.2 q hq).symm⟩

/-- Physical outsiders restore without any relation to logical ghost wires
outside S. This conclusion does not require injectivity. -/
theorem run_rename_pool_outside (f : Wire → Wire) (S : Finset Wire)
    (p : Program) (hw : wires p⊆S) (m : List Bool) (s : State)
    (q : Wire) (hq : q∉S.image f) :
    (run (renameProgram f p) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,equal⟩ := Finset.mem_image.mp h
  exact hq (Finset.mem_image.mpr ⟨a,hw ha,equal⟩)

end ECDSAAdd
#print axioms ECDSAAdd.run_rename_pool
#print axioms ECDSAAdd.run_rename_pool_outside
