import ECDSAAdd.Arithmetic.Paper935.DecoderViews
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Framework.FiniteUnitary

namespace ECDSAAdd.Arithmetic.Paper935

private theorem state_eq {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
  cases s; cases t; simp_all

private theorem run_write_outside (p : Program) (port : Wire) (hp : port∉wires p)
    (s : State) (m : List Bool) (value : Bool) :
    run p m ⟨s.phase,writeBit s.basis port value⟩=
      ⟨(run p m s).phase,writeBit (run p m s).basis port value⟩ := by
  have h := run_measured_locality p (wires p) (Finset.Subset.refl _)
    ⟨s.phase,writeBit s.basis port value⟩ s m rfl (by
      intro q hq
      change writeBit s.basis port value q=s.basis q
      exact Function.update_of_ne (show q≠port from fun he => hp (he ▸ hq)) _ _)
  apply state_eq
  · exact h.1
  · funext q
    by_cases hq : q∈wires p
    · change _ = writeBit (run p m s).basis port value q
      rw [show writeBit (run p m s).basis port value q=(run p m s).basis q from Function.update_of_ne (show q≠port from fun he => hp (he ▸ hq)) _ _]
      exact h.2 q hq
    · rw [run_preserves_outside p m _ q hq]
      change writeBit s.basis port value q=writeBit (run p m s).basis port value q
      by_cases he : q=port
      · subst q; simp [writeBit]
      · simp only [writeBit,Function.update_of_ne he,run_preserves_outside p m s q hq]

/-- Undo temporary decoder sign-extension after branch recovery. The
recovered output and corrected phase survive; every padding wire is restored
exactly. The reversed stream is proper, not a reversal of measured gates. -/
theorem decoder_unpad (p : Program) (proper : ProperProgram p)
    (port : Wire) (away : port∉wires p) (s : State) (m n : List Bool)
    (phase value : Bool) :
    run p.reverse n ⟨phase,writeBit (run p m s).basis port value⟩=
      ⟨phase,writeBit s.basis port value⟩ := by
  have hp := properProgram_reverse p proper
  have ha : port∉wires p.reverse := by simpa only [wires_reverse] using away
  rw [run_write_outside p.reverse port ha ⟨phase,(run p m s).basis⟩ n value]
  have round := run_reverse_proper p proper s m n
  have hb := FiniteUnitary.run_basis_phase p.reverse hp (run p m s).basis phase
    (run p m s).phase n
  have hc := FiniteUnitary.run_basis_phase p.reverse hp (run p m s).basis
    (run p m s).phase (run p m s).phase n
  have basis : (run p.reverse n ⟨phase,(run p m s).basis⟩).basis=s.basis := by
    calc
      _ = (run p.reverse n (run p m s)).basis := hb.trans hc.symm
      _ = s.basis := congrArg State.basis round
  rw [FiniteUnitary.run_phase p.reverse hp,basis]

end ECDSAAdd.Arithmetic.Paper935
