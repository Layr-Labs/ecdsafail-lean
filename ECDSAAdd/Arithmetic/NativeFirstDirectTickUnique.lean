import ECDSAAdd.Arithmetic.CompactSkywalkTickOutputSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect

/-- Signed interpretation is injective on physical words of a fixed width. -/
theorem signed_word_unique (r : List Wire) (a b : BasisState)
    (h : signedRegValue r a=signedRegValue r b) :
    ∀q∈r,a q=b q := by
  have ha := regValue_lt r a
  have hb := regValue_lt r b
  have hm := congrArg (fun v : Int => v%((2^r.length : Nat) : Int)) h
  unfold signedRegValue at hm
  dsimp only at hm
  rw [signedDecode_emod,signedDecode_emod,←Int.natCast_emod,←Int.natCast_emod,
    Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hm
  have hv : regValue r a=regValue r b := by exact_mod_cast hm
  exact (regValue_eq_iff r a b).mp hv

/-- Complete state uniqueness at an unshrunk integer tick boundary. Every
carry, retained transcript flag, and spectator participates in the frame. -/
theorem native_output_state_unique (L : SkywalkIntegerLayout) (s t : State)
    (phase : s.phase=t.phase)
    (half : signedRegValue L.half s.basis=signedRegValue L.half t.basis)
    (target : signedRegValue L.b s.basis=signedRegValue L.b t.basis)
    (orientation : s.basis L.a0=t.basis L.a0)
    (history : s.basis L.history=t.basis L.history)
    (previous : s.basis L.previous=t.basis L.previous)
    (carry : regValue L.carry s.basis=regValue L.carry t.basis)
    (outside : ∀q,q∉L.wires → s.basis q=t.basis q) : s=t := by
  apply congrArg₂ State.mk phase
  have hh := signed_word_unique L.half s.basis t.basis half
  have hb := signed_word_unique L.b s.basis t.basis target
  have hc := (regValue_eq_iff L.carry s.basis t.basis).mp carry
  funext q
  by_cases hq : q∈L.wires
  · simp only [SkywalkIntegerLayout.wires,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|((hq|hq)|hq)
    · exact previous
    · exact history
    · exact hh L.ext (by simp [SkywalkIntegerLayout.half])
    · exact orientation
    · exact hb L.b0 (by simp [SkywalkIntegerLayout.b])
    · exact hh q (by simp [SkywalkIntegerLayout.half,hq])
    · exact hb q (by simp [SkywalkIntegerLayout.b,hq])
    · exact hc q hq
  · exact outside q hq

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.signed_word_unique
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.native_output_state_unique
