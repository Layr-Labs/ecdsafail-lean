import ECDSAAdd.Arithmetic.RecordedRailRippleProgram

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple
open RecordedRailCarry

/-- Actual terminal gate order gives complete State equality; no separate
carry is allocated, and both source bits plus incoming carry are restored. -/
theorem terminal_state_some (a0 a1 b0 b1 p : Wire)
    (nd : [a0,a1,b0,b1,p].Nodup) (s : State) (m : List Bool) :
    run (terminalStep a0 a1 b0 b1 (some p)) m s=
      ⟨s.phase,writeBit (writeBit s.basis b0 ((s.basis b0 ^^ s.basis a0) ^^ s.basis p))
        b1 ((s.basis b1 ^^ s.basis a1) ^^ carryValue a0 b0 (some p) s.basis)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨h01,h0b,h0B,h0p⟩,⟨h1b,h1B,h1p⟩,⟨hbB,hbp⟩,hBp⟩ := nd
  have h10 := Ne.symm h01
  have hb0 := Ne.symm h0b
  have hB0 := Ne.symm h0B
  have hp0 := Ne.symm h0p
  have hb1 := Ne.symm h1b
  have hB1 := Ne.symm h1B
  have hp1 := Ne.symm h1p
  have hBb := Ne.symm hbB
  have hpb := Ne.symm hbp
  have hpB := Ne.symm hBp
  simp only [terminalStep,run]
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq0 : q=b0 <;> by_cases hq1 : q=b1 <;> by_cases hqa : q=a0 <;>
      cases hA0 : s.basis a0 <;> cases hA1 : s.basis a1 <;>
      cases hB0 : s.basis b0 <;> cases hB1 : s.basis b1 <;> cases hP : s.basis p <;>
      simp_all [carryValue,writeBit,Function.update]

theorem terminal_state_none (a0 a1 b0 b1 : Wire)
    (nd : [a0,a1,b0,b1].Nodup) (s : State) (m : List Bool) :
    run (terminalStep a0 a1 b0 b1 none) m s=
      ⟨s.phase,writeBit (writeBit s.basis b0 (s.basis b0 ^^ s.basis a0))
        b1 ((s.basis b1 ^^ s.basis a1) ^^ carryValue a0 b0 none s.basis)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨h01,h0b,h0B⟩,⟨h1b,h1B⟩,hbB⟩ := nd
  have h10 := Ne.symm h01
  have hb0 := Ne.symm h0b
  have hB0 := Ne.symm h0B
  have hb1 := Ne.symm h1b
  have hB1 := Ne.symm h1B
  have hBb := Ne.symm hbB
  simp only [terminalStep,run]
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq0 : q=b0 <;> by_cases hq1 : q=b1 <;>
      cases hA0 : s.basis a0 <;> cases hA1 : s.basis a1 <;>
      cases hB0 : s.basis b0 <;> cases hB1 : s.basis b1 <;>
      simp_all [carryValue,writeBit,Function.update]

/-- Numeric boundary of the recursive unsigned contract: the terminal really
computes modulo four, for arbitrary quantum basis inputs and phase. -/
theorem terminal_value_some (a0 a1 b0 b1 p : Wire)
    (nd : [a0,a1,b0,b1,p].Nodup) (s : State) (m : List Bool) (cursor : Nat) :
    regValue [b0,b1] (runWithTape (embedRecorded (terminalStep a0 a1 b0 b1 (some p))) m cursor s).basis=
      (regValue [a0,a1] s.basis+regValue [b0,b1] s.basis+(s.basis p).toNat)%4 := by
  rw [runWithTape_embedRecorded,terminal_state_some a0 a1 b0 b1 p nd]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨h01,h0b,h0B,h0p⟩,⟨h1b,h1B,h1p⟩,⟨hbB,hbp⟩,hBp⟩ := nd
  have h10 := Ne.symm h01
  have hb0 := Ne.symm h0b
  have hB0 := Ne.symm h0B
  have hp0 := Ne.symm h0p
  have hb1 := Ne.symm h1b
  have hB1 := Ne.symm h1B
  have hp1 := Ne.symm h1p
  have hBb := Ne.symm hbB
  have hpb := Ne.symm hbp
  have hpB := Ne.symm hBp
  cases hA0 : s.basis a0 <;> cases hA1 : s.basis a1 <;>
    cases hB0 : s.basis b0 <;> cases hB1 : s.basis b1 <;> cases hP : s.basis p <;>
    simp_all [regValue,carryValue,writeBit,Function.update]

theorem terminal_value_none (a0 a1 b0 b1 : Wire)
    (nd : [a0,a1,b0,b1].Nodup) (s : State) (m : List Bool) (cursor : Nat) :
    regValue [b0,b1] (runWithTape (embedRecorded (terminalStep a0 a1 b0 b1 none)) m cursor s).basis=
      (regValue [a0,a1] s.basis+regValue [b0,b1] s.basis)%4 := by
  rw [runWithTape_embedRecorded,terminal_state_none a0 a1 b0 b1 nd]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨h01,h0b,h0B⟩,⟨h1b,h1B⟩,hbB⟩ := nd
  have h10 := Ne.symm h01
  have hb0 := Ne.symm h0b
  have hB0 := Ne.symm h0B
  have hb1 := Ne.symm h1b
  have hB1 := Ne.symm h1B
  have hBb := Ne.symm hbB
  cases hA0 : s.basis a0 <;> cases hA1 : s.basis a1 <;>
    cases hB0 : s.basis b0 <;> cases hB1 : s.basis b1 <;>
    simp_all [regValue,carryValue,writeBit,Function.update]

theorem terminal_outside_some (a0 a1 b0 b1 p : Wire)
    (nd : [a0,a1,b0,b1,p].Nodup) (s : State) (m : List Bool) (cursor : Nat)
    (q : Wire) (hq0 : q ≠ b0) (hq1 : q ≠ b1) :
    (runWithTape (embedRecorded (terminalStep a0 a1 b0 b1 (some p))) m cursor s).basis q=s.basis q := by
  rw [runWithTape_embedRecorded,terminal_state_some a0 a1 b0 b1 p nd]
  simp [writeBit,Function.update_of_ne,hq0,hq1]

theorem terminal_phase (a0 a1 b0 b1 : Wire) (prev : Option Wire)
    (s : State) (m : List Bool) (cursor : Nat) :
    (runWithTape (embedRecorded (terminalStep a0 a1 b0 b1 prev)) m cursor s).phase=s.phase := by
  rw [runWithTape_embedRecorded]
  cases prev <;> rfl

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.terminal_state_some
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.terminal_value_some
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.terminal_value_none
