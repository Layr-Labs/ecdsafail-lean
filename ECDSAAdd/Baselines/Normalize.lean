import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Framework.RecordedQuantum

namespace ECDSAAdd.Baselines
open Challenge

/-- Remove repeated controls without changing signed-basis execution. -/
def normalizeCorrection : Correction → Correction
  | .Z t => .Z t
  | .CZ a b => if a = b then .Z a else .CZ a b

def normalizeInstr : Instr → Instr
  | .CCX a b t => if a = b then .CX a t else .CCX a b t
  | .measureX t c₀ c₁ => .measureX t (c₀.map normalizeCorrection) (c₁.map normalizeCorrection)
  | i => i

def normalizeProgram (p : Program) : Program := p.map normalizeInstr

theorem normalizeCorrection_valid (c : Correction) :
    correctionValid (normalizeCorrection c) := by
  cases c with
  | Z t => trivial
  | CZ a b => by_cases h : a = b <;> simp [normalizeCorrection, h, correctionValid]

theorem normalizeInstr_valid (i : Instr)
    (h : RecordedQuantum.PhysicalInstr (.gate i)) :
    instructionValid (normalizeInstr i) := by
  cases i with
  | X t => trivial
  | CX c t => exact h
  | CCX a b t =>
    change a ≠ t ∧ b ≠ t at h
    by_cases hab : a = b
    · simpa [normalizeInstr, hab, instructionValid] using h.1
    · simpa [normalizeInstr, hab, instructionValid] using And.intro hab h
  | measureX t c₀ c₁ =>
    simp only [normalizeInstr, instructionValid, List.mem_map]
    constructor <;> intro c hc <;> obtain ⟨d, hd, rfl⟩ := hc
    all_goals exact normalizeCorrection_valid d

theorem normalize_correct (cs : List Correction) (s : State) :
    correct (cs.map normalizeCorrection) s = correct cs s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z t => simpa only [List.map_cons, normalizeCorrection, correct] using ih _
    | CZ a b =>
      by_cases hab : a = b
      · subst b
        simpa [normalizeCorrection, correct] using ih ⟨s.phase ^^ s.basis a, s.basis⟩
      · simpa [normalizeCorrection, hab, correct] using ih ⟨s.phase ^^ (s.basis a && s.basis b), s.basis⟩

theorem normalize_run (p : Program) (m : List Bool) (s : State) :
    run (normalizeProgram p) m s = run p m s := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t => simpa only [normalizeProgram, List.map_cons, normalizeInstr, run] using ih m _
    | CX c t => simpa only [normalizeProgram, List.map_cons, normalizeInstr, run] using ih m _
    | CCX a b t =>
      by_cases hab : a = b
      · subst b
        simpa [normalizeProgram, normalizeInstr, run] using
          ih m ⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis a)⟩
      · simpa [normalizeProgram, normalizeInstr, hab, run] using
          ih m ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩
    | measureX t c₀ c₁ =>
      simp only [normalizeProgram, List.map_cons, normalizeInstr, run]
      change run (normalizeProgram p) m.tail _ = _
      rw [ih]
      congr 1
      simp only [measureAndCorrect]
      split <;> exact normalize_correct _ _

theorem normalize_slots (p : Program) : gateSlots (normalizeProgram p) = gateSlots p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | CCX a b t =>
      by_cases hab : a = b <;>
        simp_all [normalizeProgram, normalizeInstr, gateSlots, instructionSlots]
    | X t => simpa [normalizeProgram, normalizeInstr, gateSlots, instructionSlots] using ih
    | CX c t => simpa [normalizeProgram, normalizeInstr, gateSlots, instructionSlots] using ih
    | measureX t c₀ c₁ => simpa [normalizeProgram, normalizeInstr, gateSlots, instructionSlots] using ih

theorem normalize_measurements (p : Program) :
    measurementCount (normalizeProgram p) = measurementCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp_all [normalizeProgram, normalizeInstr, measurementCount]
    split <;> simp_all [measurementCount]

/-- Number of Toffoli slots removed by normalization. -/
def repeatedControls : Program → Nat
  | [] => 0
  | .CCX a b _ :: p => (if a = b then 1 else 0) + repeatedControls p
  | _ :: p => repeatedControls p

theorem normalize_toffoli_exact (p : Program) :
    toffoliCount (normalizeProgram p) + repeatedControls p = toffoliCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | CCX a b t =>
      by_cases h : a = b <;>
        simp only [normalizeProgram, List.map_cons, normalizeInstr, h, ↓reduceIte,
          toffoliCount, repeatedControls] at ih ⊢ <;> omega
    | X t => simpa [normalizeProgram, normalizeInstr, toffoliCount, repeatedControls] using ih
    | CX a t => simpa [normalizeProgram, normalizeInstr, toffoliCount, repeatedControls] using ih
    | measureX t cs ds => simpa [normalizeProgram, normalizeInstr, toffoliCount, repeatedControls] using ih

theorem normalize_toffoli (p : Program) :
    toffoliCount (normalizeProgram p) ≤ toffoliCount p := by
  induction p with
  | nil => exact Nat.le_refl _
  | cons i p ih =>
    cases i <;> simp_all [normalizeProgram, normalizeInstr, toffoliCount]
    split <;> simp_all [toffoliCount]
    exact Nat.le_trans ih (Nat.le_add_left _ _)

theorem normalize_correctionWires (cs : List Correction) :
    correctionWires (cs.map normalizeCorrection) = correctionWires cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z t => simp [normalizeCorrection, correctionWires, ih]
    | CZ a b => by_cases hab : a = b <;> simp [normalizeCorrection, hab, correctionWires, ih]

theorem normalize_wires (p : Program) : wires (normalizeProgram p) = wires p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | CCX a b t => by_cases hab : a = b <;> simp_all [normalizeProgram, normalizeInstr, wires, Instr.wires]
    | measureX t c₀ c₁ =>
      simp only [normalizeProgram, List.map_cons, normalizeInstr, wires, Instr.wires,
        normalize_correctionWires]
      exact congrArg (_ ∪ ·) ih
    | X t => simpa only [normalizeProgram, List.map_cons, normalizeInstr, wires] using congrArg (_ ∪ ·) ih
    | CX c t => simpa only [normalizeProgram, List.map_cons, normalizeInstr, wires] using congrArg (_ ∪ ·) ih

theorem normalize_physical (p : Program)
    (h : ∀ i ∈ p, RecordedQuantum.PhysicalInstr (.gate i)) :
    ∀ i ∈ normalizeProgram p, instructionValid i := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact normalizeInstr_valid j (h j hj)

theorem normalize_qubits (p : Program) : qubits (normalizeProgram p) = qubits p := by
  simp only [qubits, normalize_wires]

theorem normalize_triple (p : Program) (P Q : BasisState → Prop) :
    Triple P (normalizeProgram p) Q ↔ Triple P p Q := by
  simp only [Triple, normalize_run]

end ECDSAAdd.Baselines
