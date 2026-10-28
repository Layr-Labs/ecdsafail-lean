import ECDSAAdd.Arithmetic.RecordedRailRippleProofFrame

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple

/-- The one-bit top instruction preserves arbitrary spectators and phase. -/
theorem one_frame (a b : Wire) (prev : Option Wire)
    (nd : (prev.toList++[a,b]).Nodup) (bits : BasisState) (phase : Bool)
    (m : List Bool) (cursor : Nat) :
    let out := runWithTape (ripple [a] [b] prev [] []) m cursor ⟨phase,bits⟩
    out.phase=phase ∧
    regValue [b] out.basis=(regValue [a] bits+regValue [b] bits+
      (incomingValue prev bits).toNat)%2^([b] : List Wire).length ∧
    (∀q,q∉([b] : List Wire) → out.basis q=bits q) := by
  cases prev with
  | none =>
    simp only [Option.toList_none,List.nil_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_true] at nd
    have hab : a≠b := by simpa using nd
    dsimp
    rw [ripple,runWithTape_embedRecorded]
    refine ⟨rfl,?_,?_⟩
    · cases ha : bits a <;> cases hb : bits b <;>
        simp_all [topStep,run,regValue,incomingValue,writeBit,Function.update]
    · intro q hq
      simp only [List.mem_singleton] at hq
      simp [topStep,run,writeBit,hq]
  | some p =>
    simp only [Option.toList_some,List.singleton_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
    obtain ⟨⟨hpa,hpb⟩,hab⟩ := nd
    dsimp
    rw [ripple,runWithTape_embedRecorded]
    refine ⟨rfl,?_,?_⟩
    · cases ha : bits a <;> cases hb : bits b <;> cases hp : bits p <;>
        simp_all [topStep,run,regValue,incomingValue,writeBit,Function.update]
    · intro q hq
      simp only [List.mem_singleton] at hq
      simp [topStep,run,writeBit,hq]

/-- Two-bit terminal frame, including the complete unsigned value. -/
theorem two_frame (a0 a1 b0 b1 : Wire) (prev : Option Wire)
    (nd : (prev.toList++[a0,a1,b0,b1]).Nodup) (bits : BasisState) (phase : Bool)
    (m : List Bool) (cursor : Nat) :
    let out := runWithTape (ripple [a0,a1] [b0,b1] prev [] []) m cursor ⟨phase,bits⟩
    out.phase=phase ∧
    regValue [b0,b1] out.basis=(regValue [a0,a1] bits+regValue [b0,b1] bits+
      (incomingValue prev bits).toNat)%2^([b0,b1] : List Wire).length ∧
    (∀q,q∉([b0,b1] : List Wire) → out.basis q=bits q) := by
  dsimp
  rw [ripple]
  refine ⟨terminal_phase _ _ _ _ _ _ _ _,?_,?_⟩
  · cases prev with
    | none =>
      simpa [incomingValue] using terminal_value_none a0 a1 b0 b1 nd ⟨phase,bits⟩ m cursor
    | some p =>
      have hn : [a0,a1,b0,b1,p].Nodup := by
        simpa [List.nodup_cons,List.mem_cons,not_or,and_assoc,and_left_comm,and_comm,
          ne_comm] using nd
      simpa [incomingValue] using terminal_value_some a0 a1 b0 b1 p hn ⟨phase,bits⟩ m cursor
  · intro q hq
    have hq0 : q≠b0 := by simpa using fun h => hq (by simp [h])
    have hq1 : q≠b1 := by simpa using fun h => hq (by simp [h])
    cases prev with
    | none =>
      rw [runWithTape_embedRecorded,terminal_state_none a0 a1 b0 b1 nd]
      simp [writeBit,hq0,hq1]
    | some p =>
      have hn : [a0,a1,b0,b1,p].Nodup := by
        simpa [List.nodup_cons,List.mem_cons,not_or,and_assoc,and_left_comm,and_comm,
          ne_comm] using nd
      exact terminal_outside_some a0 a1 b0 b1 p hn ⟨phase,bits⟩ m cursor q hq0 hq1

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.one_frame
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.two_frame
