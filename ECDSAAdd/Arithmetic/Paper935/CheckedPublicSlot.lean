import ECDSAAdd.Arithmetic.Paper935.SlotFrontChecks

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.RecordedQuantum

def PublicSlot.PostChecks (P : PublicSlot) (F : SlotRegisters) : Prop :=
  match P.post with
  | some post => post.ports.toFinset⊆arenaWires
  | none => F.frozen≠F.active ∧ F.work1≠F.active ∧
      [F.frozen,F.work1,F.active].toFinset⊆arenaWires

instance (P : PublicSlot) (F : SlotRegisters) : Decidable (P.PostChecks F) := by
  unfold PublicSlot.PostChecks
  cases P.post <;> infer_instance

def compileCheckedPublicSlot (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) : Option PublicSlot := do
  let P ← compilePublicSlot A b addWidth exitWidth F armed probeWidth offset
  if P.front.PhysicalChecks F ∧ P.PostChecks F then some P else none

theorem compileCheckedPublicSlot_contract (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) (P : PublicSlot)
    (h : compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset=some P) :
    compilePublicSlot A b addWidth exitWidth F armed probeWidth offset=some P ∧
    P.front.PhysicalChecks F ∧ P.PostChecks F := by
  unfold compileCheckedPublicSlot at h
  obtain ⟨Q,hq,h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next valid => cases h; exact ⟨hq,valid⟩
  next invalid => simp at h

theorem compilePublicSlot_post_valid (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) (P : PublicSlot)
    (h : compilePublicSlot A b addWidth exitWidth F armed probeWidth offset=some P)
    (post : WindowPostLayout) (hp : P.post=some post) : post.Valid := by
  cases armed with
  | false =>
    have hn := (compilePublicSlot_unarmed A b addWidth exitWidth F probeWidth offset P h).1
    rw [hn] at hp
    contradiction
  | true =>
    obtain ⟨Q,hq,hc⟩ := compilePublicSlot_armed A b addWidth exitWidth F probeWidth offset P h
    have eq : Q=post := Option.some.inj (hq.symm.trans hp)
    subst Q
    have pair := compileBorrowedPost_contract P.front.exitArena P.postArena true F.one F.work0 F.frozen F.work1 F.active
      P.front.exitBank.g.wires F.offset P.postWork probeWidth offset post hc
    exact (compilePost_contract true F.one F.work0 F.frozen F.work1 F.active
      P.front.exitBank.g.wires F.offset P.postWork probeWidth offset post pair.2).1

/-- Actual emitted programs in both directions satisfy ordinary-gate
legality and use only physical arena addresses, for any input state. -/
theorem compileCheckedPublicSlot_resources (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) (P : PublicSlot)
    (h : compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset=some P) :
    (GatePhysical (P.program F) ∧ GatePhysical (P.inverse F)) ∧
    (wires (P.program F)⊆arenaWires ∧ wires (P.inverse F)⊆arenaWires) := by
  have hc := compileCheckedPublicSlot_contract A b addWidth exitWidth F armed probeWidth offset P h
  have front := compileSlotFront_contract A b addWidth exitWidth F P.front
    (compilePublicSlot_front A b addWidth exitWidth F armed probeWidth offset P hc.1)
  have frontPhys := front.physical P.front A b addWidth exitWidth F hc.2.1
  have frontSupport := front.support P.front A b addWidth exitWidth F hc.2.1
  have postPhys : GatePhysical (P.postProgram F) ∧ GatePhysical (P.postInverse F) := by
    cases hp : P.post with
    | none =>
      have checks := hc.2.2
      simp only [PublicSlot.PostChecks,hp] at checks
      have proper := (unarmedPost_resources F checks.1 checks.2.1).1
      simp only [PublicSlot.postProgram,PublicSlot.postInverse,hp]
      exact ⟨(physical_embed _).mp (physical_of_proper _ proper),
        (physical_embed _).mp (physical_of_proper _ (properProgram_reverse _ proper))⟩
    | some post =>
      have valid := compilePublicSlot_post_valid A b addWidth exitWidth F armed probeWidth offset P hc.1 post hp
      simpa only [PublicSlot.postProgram,PublicSlot.postInverse,hp] using post.physical valid
  have postSupport : wires (P.postProgram F)⊆arenaWires ∧ wires (P.postInverse F)⊆arenaWires := by
    cases hp : P.post with
    | none =>
      have checks := hc.2.2
      simp only [PublicSlot.PostChecks,hp] at checks
      have support := (unarmedPost_resources F checks.1 checks.2.1).2.2.trans checks.2.2
      simpa only [PublicSlot.postProgram,PublicSlot.postInverse,hp,wires_reverse] using And.intro support support
    | some post =>
      have checks := hc.2.2
      simp only [PublicSlot.PostChecks,hp] at checks
      simpa only [PublicSlot.postProgram,PublicSlot.postInverse,hp] using
        And.intro (post.support.1.trans checks) (post.support.2.trans checks)
  simp only [PublicSlot.program,PublicSlot.inverse,gatePhysical_append,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨frontPhys.1,postPhys.1⟩,⟨postPhys.2,frontPhys.2⟩⟩,
    ⟨⟨frontSupport.1,postSupport.1⟩,⟨postSupport.2,frontSupport.2⟩⟩⟩

theorem compileCheckedPublicSlot_qubits (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) (P : PublicSlot)
    (h : compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset=some P) :
    qubitCount (P.program F)≤935 ∧ qubitCount (P.inverse F)≤935 := by
  have support := (compileCheckedPublicSlot_resources A b addWidth exitWidth F armed probeWidth offset P h).2
  exact ⟨arena_program_qubits _ support.1,arena_program_qubits _ support.2⟩

end ECDSAAdd.Arithmetic.Paper935
