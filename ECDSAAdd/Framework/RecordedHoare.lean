import ECDSAAdd.Framework.RecordedRelocation
import ECDSAAdd.Framework.Hoare

namespace ECDSAAdd

/-- A closed recorded segment owns its measurement references. Correctness
quantifies over arbitrary incoming phase and arbitrary finite tapes. -/
def RecordedTriple (P : BasisState → Prop) (c : RecordedProgram)
    (Q : BasisState → Prop) : Prop :=
  ∀ (s : State) (m : List Bool), P s.basis →
    (runWithTape c m 0 s).phase=s.phase ∧ Q (runWithTape c m 0 s).basis

theorem Triple.recorded {P Q : BasisState → Prop} {c : Program}
    (h : Triple P c Q) : RecordedTriple P (embedRecorded c) Q := by
  intro s m hs
  simpa only [runWithTape_embedRecorded,List.drop_zero] using h s m hs

theorem RecordedTriple.seq {P Q R : BasisState → Prop} {c d : RecordedProgram}
    (hc : RecordedTriple P c Q) (hd : RecordedTriple Q d R) :
    RecordedTriple P (recordedThen c d) R := by
  intro s m hs
  rw [recordedThen_run]
  obtain ⟨hp,hq⟩ := hc s m hs
  obtain ⟨hp',hr⟩ := hd _ (m.drop (recordedMeasurementCount c)) hq
  exact ⟨hp'.trans hp,hr⟩

/-- Relocating a closed segment preserves its Hoare contract at any cursor.
The caller keeps the full tape, including any earlier measurement outcomes. -/
theorem RecordedTriple.at_cursor {P Q : BasisState → Prop} {c : RecordedProgram}
    (h : RecordedTriple P c Q) (offset : Nat) (s : State) (m : List Bool)
    (hs : P s.basis) :
    (runWithTape (relocateRecords offset c) m offset s).phase=s.phase ∧
    Q (runWithTape (relocateRecords offset c) m offset s).basis := by
  have he := runWithTape_relocate c offset 0 m s
  simp only [Nat.add_zero] at he
  rw [he]
  exact h s (m.drop offset) hs

theorem recordedThen_counts (c d : RecordedProgram) :
    recordedToffoliCount (recordedThen c d)=recordedToffoliCount c+recordedToffoliCount d ∧
    recordedMeasurementCount (recordedThen c d)=recordedMeasurementCount c+recordedMeasurementCount d := by
  simp only [recordedThen,recordedToffoliCount_append,recordedMeasurementCount_append,
    (relocateRecords_counts _ _).1,(relocateRecords_counts _ _).2,and_self]

theorem recordedThen_wires (c d : RecordedProgram) :
    recordedWires (recordedThen c d)=recordedWires c ∪ recordedWires d := by
  simp only [recordedThen,recordedWires_append,relocateRecords_wires]

theorem relocateRecords_embed (offset : Nat) (p : Program) :
    relocateRecords offset (embedRecorded p)=embedRecorded p := by
  induction p with
  | nil => rfl
  | cons i p ih => simpa only [embedRecorded,List.map_cons,relocateRecords,
      relocateRecord] using congrArg (List.cons (RecordedInstr.gate i)) ih

theorem recordedThen_embed (p q : Program) :
    recordedThen (embedRecorded p) (embedRecorded q)=embedRecorded (p++q) := by
  rw [recordedThen,relocateRecords_embed]
  exact List.map_append.symm

end ECDSAAdd
