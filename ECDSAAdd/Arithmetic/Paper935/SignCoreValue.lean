import ECDSAAdd.Arithmetic.Paper935.SignCoreProgram
import ECDSAAdd.Arithmetic.Paper935.FusedEndpointModel

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] sign24Program signWindow signComplement

private theorem window_pull_value (s : State) :
    regValue sign24Word (pullState signWindowMap s).basis=regValue sign24Word s.basis := by
  apply regValue_congr
  intro q hq
  have bound : q<59 := by
    simp only [sign24Word,List.mem_range'] at hq
    dsimp only [Wire] at *
    omega
  simp [pullState,signWindowMap,bound]

theorem signWindow_contract (subtract : Bool) (s : State) (m : List Bool)
    (ready : SignReady s.basis) :
    let out := run (signWindow subtract) m s
    regValue sign24Word out.basis=
      (regValue sign24Word s.basis+(if s.basis 0 then sign24Literal subtract else 0))%2^58 ∧
    SignReady out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  have clean : Sign24Ready 0 (pullState signWindowMap s).basis := by
    intro i hi _
    simpa [pullState,signWindowMap,show ¬59+i<59 by omega,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using ready i hi
  have h := sign24Program_contract subtract (pullState signWindowMap s) m clean
  have execution := run_rename signWindowMap signWindowMap_injective (sign24Program subtract) m s
  rw [←signWindow] at execution
  dsimp only at h
  rw [←execution,window_pull_value,window_pull_value] at h
  refine ⟨h.1,?_,h.2.2.1,h.2.2.2⟩
  intro i hi
  dsimp only [Wire] at i hi
  have pool := h.2.1 i hi (Nat.zero_le _)
  simpa [pullState,signWindowMap,show ¬59+i<59 by omega,Nat.add_assoc,
    Nat.add_comm,Nat.add_left_comm] using pool

theorem signWindow_high_frame (subtract : Bool) (s : State) (m : List Bool)
    (q : Wire) (lo : 59≤q) (hi : q<257) :
    (run (signWindow subtract) m s).basis q=s.basis q := by
  apply run_preserves_outside
  rw [signWindow,renameProgram_support]
  intro mem
  obtain ⟨j,_,eq⟩ := Finset.mem_image.mp mem
  dsimp [signWindowMap] at eq
  dsimp only [Wire] at *
  split_ifs at eq <;> omega


/-- Scratch, control, and phase are restored by either orientation. No
arithmetic success assumption is needed for these structural conclusions. -/
theorem signCore_cleanup (inverse : Bool) (s : State) (m : List Bool)
    (ready : SignReady s.basis) :
    let out := run (signCore inverse) m s
    SignReady out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  have fan (t : State) (tape : List Bool) := signComplement_correct 0 signPayload
    (by unfold signPayload; exact List.nodup_range') (by simp [signPayload]) t tape
  cases inverse with
  | false =>
    let t := run (signComplement 0 signPayload) m s
    have clean : SignReady t.basis := by
      intro i hi
      rw [(fan s m).2.1 (257+i) (by simp [signPayload])]
      exact ready i hi
    have h := signWindow_contract true t m clean
    simp only [signCore,Bool.false_eq_true,if_false,run_append,run_take]
    simp only [(signComplement_counts 0 signPayload).2,List.drop_zero]
    exact ⟨h.2.1,h.2.2.1.trans ((fan s m).2.1 0 (by simp [signPayload])),
      h.2.2.2.trans (fan s m).1⟩
  | true =>
    let t := run (signWindow false) m s
    let tape := m.drop (measurementCount (signWindow false))
    have h := signWindow_contract false s m ready
    have clean : SignReady (run (signComplement 0 signPayload) tape t).basis := by
      intro i hi
      rw [(fan t tape).2.1 (257+i) (by simp [signPayload])]
      exact h.2.1 i hi
    simp only [signCore,if_true,run_append,run_take]
    exact ⟨clean,((fan t tape).2.1 0 (by simp [signPayload])).trans h.2.2.1,
      (fan t tape).1.trans h.2.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
