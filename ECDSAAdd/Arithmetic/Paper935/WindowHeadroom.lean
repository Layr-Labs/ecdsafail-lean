import ECDSAAdd.Arithmetic.Paper935.WindowSchedule

namespace ECDSAAdd.Arithmetic.Paper935

theorem PayloadFits.double {w : Nat} {x : Int} (h : PayloadFits w x) :
    PayloadFits (w+1) (2*x) := by simpa [two_mul] using h.add h

/-- Dropping the low bit cannot escape a window with an even lower endpoint. -/
theorem PayloadFits.twice_half {w : Nat} {x : Int} (h : PayloadFits (w+1) x) :
    PayloadFits (w+1) (2*(x/2)) := by
  simp only [PayloadFits,Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at *
  omega

/-- The paired public headroom suffices for all arithmetic intermediates;
no additional probabilistic overflow event is introduced by the add stage. -/
theorem RowWindow.addPad_step_fits (w : RowWindow) (s : ECDSAAdd.Divsteps.ZState)
    (h : w.Fits s) :
    PayloadFits w.addPad.g (2*(ECDSAAdd.Divsteps.zStep s).g) ∧
    PayloadFits w.addPad.gv (ECDSAAdd.Divsteps.zStep s).gv ∧
    PayloadFits w.addPad.fv (ECDSAAdd.Divsteps.zStep s).fv := by
  have hp := h.mono w.pairPad_covers
  have fg : PayloadFits (max w.f w.g) s.f := hp.1
  have gg : PayloadFits (max w.f w.g) s.g := hp.2.1
  have fv : PayloadFits (max w.fv w.gv) s.fv := hp.2.2.1
  have gv : PayloadFits (max w.fv w.gv) s.gv := hp.2.2.2
  by_cases swap : 0≤s.z ∧ s.g%2=1
  · rw [ECDSAAdd.Divsteps.zStep_swap swap]
    exact ⟨(gg.sub fg).twice_half,gv.sub fv,gv.double⟩
  · rw [ECDSAAdd.Divsteps.zStep_nonswap swap]
    have parity : s.g%2=0 ∨ s.g%2=1 := by omega
    rcases parity with hg | hg
    · simp only [hg,zero_mul,add_zero]
      exact ⟨(gg.mono (by omega)).twice_half,gv.mono (by dsimp [RowWindow.addPad]; omega),fv.double⟩
    · simp only [hg,one_mul]
      exact ⟨(gg.add fg).twice_half,gv.add fv,fv.double⟩

end ECDSAAdd.Arithmetic.Paper935
