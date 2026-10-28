import ECDSAAdd.Arithmetic.Paper935.FireCleanup
import ECDSAAdd.Arithmetic.Paper935.ZeroLatch

namespace ECDSAAdd.Arithmetic.Paper935

/-- The positive predicate uses the signed high bit and an exact zz witness. -/
def positiveFlag (sign zz target : Wire) : Program :=
  [.X sign,.X zz,.CCX sign zz target,.X zz,.X sign]

def erasePositiveFlag (sign zz target : Wire) : Program :=
  [.X sign,.X zz] ++ eraseAnd sign zz target ++ [.X zz,.X sign]

theorem positiveFlag_run (sign zz target : Wire) (hsz : sign≠zz)
    (hst : sign≠target) (hzt : zz≠target) (s : State) (m : List Bool) :
    run (positiveFlag sign zz target) m s=
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ (!s.basis sign && !s.basis zz))⟩ := by
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hws : w=sign <;> by_cases hwz : w=zz <;> by_cases hwt : w=target <;>
    simp_all [writeBit,Function.update_apply,Ne.symm hsz]

theorem erasePositiveFlag_run (sign zz target : Wire) (hsz : sign≠zz)
    (hst : sign≠target) (hzt : zz≠target) (s : State) (m : List Bool)
    (h : s.basis target=(!s.basis sign && !s.basis zz)) :
    run (erasePositiveFlag sign zz target) m s=⟨s.phase,writeBit s.basis target false⟩ := by
  let v : State := ⟨s.phase,writeBit (writeBit s.basis sign (!s.basis sign)) zz (!s.basis zz)⟩
  have he : v.basis target=(v.basis sign && v.basis zz) := by
    simpa [v,writeBit,hsz,Ne.symm hst,Ne.symm hzt] using h
  rw [erasePositiveFlag,run_append,run_take,run_append,run_take]
  have hv : run [.X sign,.X zz] m s=v := by simp [v,run,writeBit,Ne.symm hsz]
  simp only [measurementCount,List.drop_zero]
  rw [hv,eraseAnd_run sign zz target hst hzt v m he]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hws : w=sign <;> by_cases hwz : w=zz <;> by_cases hwt : w=target <;>
    simp_all [v,run,writeBit,Function.update_apply]

/-- The zz witness and signed high bit decide strictly positive integers,
including zz and the full negative half of the two's-complement range. -/
theorem positiveFlag_value (lo : List Wire) (sign zz : Wire) (s : BasisState)
    (hz : s zz=decide (regValue (lo++[sign]) s=0)) :
    (!s sign && !s zz)=decide (0<signedRegValue (lo++[sign]) s) := by
  have hn := signedRegValue_neg_iff lo sign s
  have he := signedRegValue_zero_iff (lo++[sign]) s
  rw [hz]
  cases hs : s sign <;> by_cases hzero : regValue (lo++[sign]) s=0 <;>
    simp [hs,hzero] at hn he ⊢ <;> omega

theorem positiveFlag_counts (sign zz target : Wire) :
    toffoliCount (positiveFlag sign zz target)=1 ∧
    measurementCount (positiveFlag sign zz target)=0 ∧
    toffoliCount (erasePositiveFlag sign zz target)=0 ∧
    measurementCount (erasePositiveFlag sign zz target)=1 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem positivePredicate_value (lo : List Wire) (sign : Wire) (s : BasisState) :
    (!s sign && !decide (regValue (lo++[sign]) s=0))=
      decide (0<signedRegValue (lo++[sign]) s) := by
  have hn := signedRegValue_neg_iff lo sign s
  have he := signedRegValue_zero_iff (lo++[sign]) s
  cases hs : s sign <;> by_cases hz : regValue (lo++[sign]) s=0 <;>
    simp [hs,hz] at hn he ⊢ <;> omega

theorem positiveFlag_support (sign zz target : Wire) :
    wires (positiveFlag sign zz target)={sign,zz,target} ∧
    wires (erasePositiveFlag sign zz target)={sign,zz,target} := by
  constructor <;> ext w <;>
    simp [positiveFlag,erasePositiveFlag,eraseAnd,wires,Instr.wires,correctionWires] <;> tauto

end ECDSAAdd.Arithmetic.Paper935
