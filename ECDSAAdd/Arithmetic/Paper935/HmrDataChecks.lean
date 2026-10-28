import ECDSAAdd.Framework.RecordedPermutation
namespace ECDSAAdd.Arithmetic.Paper935

/-- Check only the small wire set of each instruction, never build the union. -/
def hmrCheckWires (f : Wire → Bool) (P : RecordedProgram) : Bool :=
  P.all (fun i => decide (∀ q ∈ i.quantumWires, f q = true))

theorem hmrCheckWires_sound (f : Wire → Bool) (P : RecordedProgram)
    (h : hmrCheckWires f P = true) : ∀q∈recordedWires P, f q = true := by
  induction P with
  | nil => simp [recordedWires]
  | cons i P ih =>
    simp only [hmrCheckWires, List.all_cons, Bool.and_eq_true] at h
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (of_decide_eq_true h.1) q hq
    · exact ih h.2 q hq

def hmrCheckRecords : Nat → RecordedProgram → Bool
  | _, [] => true
  | k, .gate i :: P => hmrCheckRecords (k + measurementCount [i]) P
  | k, .phaseFromRecord j _ :: P => decide (j < k) && hmrCheckRecords k P

theorem hmrCheckRecords_sound (P : RecordedProgram) (k : Nat)
    (h : hmrCheckRecords k P = true) : RecordedWellFormedAt k P := by
  induction P generalizing k with
  | nil => trivial
  | cons i P ih =>
    cases i with
    | gate i => exact ih _ h
    | phaseFromRecord j cs =>
      simp only [hmrCheckRecords, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, ih _ h.2⟩

def hmrGatesOnly (P : RecordedProgram) : Bool :=
  P.all (fun | .gate _ => true | .phaseFromRecord _ _ => false)

theorem hmrGatesOnly_wellFormed (P : RecordedProgram) (h : hmrGatesOnly P = true)
    (cursor : Nat) : RecordedWellFormedAt cursor P := by
  induction P generalizing cursor with
  | nil => trivial
  | cons i P ih =>
    cases i with
    | gate i => exact ih (by simpa [hmrGatesOnly] using h) _
    | phaseFromRecord j cs => simp [hmrGatesOnly] at h

@[simp] theorem hmrGatesOnly_rename (w : Wire → Wire) (P : RecordedProgram) :
    hmrGatesOnly (renameRecordedProgram w P) = hmrGatesOnly P := by
  induction P with
  | nil => rfl
  | cons i P ih => cases i <;> simp_all [hmrGatesOnly,renameRecordedProgram,renameRecordedInstr]

@[simp] theorem hmrGatesOnly_relocate (b : Nat) (P : RecordedProgram) :
    hmrGatesOnly (relocateRecords b P) = hmrGatesOnly P := by
  induction P with
  | nil => rfl
  | cons i P ih => cases i <;> simp_all [hmrGatesOnly,relocateRecords,relocateRecord]

end ECDSAAdd.Arithmetic.Paper935
