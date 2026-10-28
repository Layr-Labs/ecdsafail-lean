import ECDSAAdd.Framework.RecordedQuantum
import ECDSAAdd.Framework.RecordedHoare

namespace ECDSAAdd.RecordedQuantum

/-- Local physical validity: every ordinary target differs from its controls.
Measurements and saved-record phase instructions are admitted. -/
def PhysicalProgram (p : RecordedProgram) : Prop := ∀ i ∈ p, PhysicalInstr i

theorem physical_append (p q : RecordedProgram) :
    PhysicalProgram (p++q) ↔ PhysicalProgram p ∧ PhysicalProgram q := by
  simp only [PhysicalProgram,List.mem_append,or_imp,forall_and]

theorem physical_relocate (offset : Nat) (p : RecordedProgram) :
    PhysicalProgram (relocateRecords offset p) ↔ PhysicalProgram p := by
  simp only [PhysicalProgram,relocateRecords,List.mem_map]
  constructor
  · intro h i hi
    have hh := h (relocateRecord offset i) ⟨i,hi,rfl⟩
    cases i <;> exact hh
  · intro h i hi
    obtain ⟨j,hj,rfl⟩ := hi
    have hh := h j hj
    cases j <;> exact hh

theorem physical_then (p q : RecordedProgram) :
    PhysicalProgram (recordedThen p q) ↔ PhysicalProgram p ∧ PhysicalProgram q := by
  rw [recordedThen,physical_append,physical_relocate]

theorem physical_embed (p : Program) :
    PhysicalProgram (embedRecorded p) ↔ ∀ i ∈ p, PhysicalInstr (.gate i) := by
  simp [PhysicalProgram,embedRecorded]

theorem physical_of_proper (p : Program) (hp : ProperProgram p) :
    PhysicalProgram (embedRecorded p) := by
  rw [physical_embed]
  intro i hi
  have h := hp i hi
  cases i <;> simp_all [PhysicalInstr,ProperGate]

end ECDSAAdd.RecordedQuantum
