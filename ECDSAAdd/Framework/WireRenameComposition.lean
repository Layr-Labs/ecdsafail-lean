import ECDSAAdd.Framework.WireRename

namespace ECDSAAdd

theorem renameCorrection_comp (f g : Wire → Wire) (c : Correction) :
    renameCorrection f (renameCorrection g c)=renameCorrection (f ∘ g) c := by
  cases c <;> rfl

theorem renameInstr_comp (f g : Wire → Wire) (i : Instr) :
    renameInstr f (renameInstr g i)=renameInstr (f ∘ g) i := by
  cases i <;> simp [renameInstr,List.map_map,Function.comp_def,renameCorrection_comp]

theorem renameProgram_comp (f g : Wire → Wire) (p : Program) :
    renameProgram f (renameProgram g p)=renameProgram (f ∘ g) p := by
  simp only [renameProgram,List.map_map]
  apply List.map_congr_left
  intro i _
  exact renameInstr_comp f g i

theorem renameCorrections_congr (f g : Wire → Wire) (cs : List Correction)
    (h : ∀ q∈correctionWires cs, f q=g q) :
    cs.map (renameCorrection f)=cs.map (renameCorrection g) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z q =>
      have qeq := h q (by simp [correctionWires])
      have tail := ih (fun q hq => h q (Finset.mem_union_right _ hq))
      simp only [List.map_cons,renameCorrection,qeq,tail]
    | CZ a b =>
      have ae := h a (by simp [correctionWires])
      have be := h b (by simp [correctionWires])
      have tail := ih (fun q hq => h q (Finset.mem_union_right _ hq))
      simp only [List.map_cons,renameCorrection,ae,be,tail]

theorem renameInstr_congr (f g : Wire → Wire) (i : Instr)
    (h : ∀ q∈i.wires, f q=g q) : renameInstr f i=renameInstr g i := by
  cases i with
  | X q => simp only [renameInstr,h q (by simp [Instr.wires])]
  | CX a q => simp only [renameInstr,h a (by simp [Instr.wires]),h q (by simp [Instr.wires])]
  | CCX a b q =>
    simp only [renameInstr,h a (by simp [Instr.wires]),h b (by simp [Instr.wires]),
      h q (by simp [Instr.wires])]
  | measureX q c0 c1 =>
    have qeq := h q (by simp [Instr.wires])
    have e0 := renameCorrections_congr f g c0
      (fun q hq => h q (Finset.mem_union_left _ (Finset.mem_union_right _ hq)))
    have e1 := renameCorrections_congr f g c1
      (fun q hq => h q (Finset.mem_union_right _ hq))
    simp only [renameInstr,qeq,e0,e1]

/-- Equality of placements on actual gate and correction support suffices;
unaccessed descriptor names never affect the emitted program. -/
theorem renameProgram_congr_support (f g : Wire → Wire) (p : Program)
    (h : ∀ q∈wires p, f q=g q) : renameProgram f p=renameProgram g p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    have head := renameInstr_congr f g i (fun q hq => h q (Finset.mem_union_left _ hq))
    have tail := ih (fun q hq => h q (Finset.mem_union_right _ hq))
    change renameInstr f i :: renameProgram f p = renameInstr g i :: renameProgram g p
    rw [head,tail]

end ECDSAAdd
#print axioms ECDSAAdd.renameProgram_comp
#print axioms ECDSAAdd.renameProgram_congr_support
