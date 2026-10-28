import ECDSAAdd.Arithmetic.Paper935.HornerCarryCell

namespace ECDSAAdd.Arithmetic.Paper935

/-- One stratum of engine.py HmrWalk._jflags: split a live pre into
its set-bit anchor and its remaining zero-bit pre, using two CX gates. -/
def hmrFlagCell (pre bit anchor rest : Wire) : Program :=
  [.CCX pre bit anchor,.CX pre rest,.CX anchor rest]

def hmrFlagRelease (pre bit anchor rest : Wire) : Program :=
  [.CX anchor rest,.CX pre rest,.measureX anchor [] [.CZ pre bit]]

theorem hmrFlagCell_run (pre bit anchor rest : Wire)
    (distinct : [pre,bit,anchor,rest].Nodup) (s : State) (m : List Bool)
    (ha : s.basis anchor=false) (hr : s.basis rest=false) :
    run (hmrFlagCell pre bit anchor rest) m s=
      ⟨s.phase,writeBit (writeBit s.basis anchor (s.basis pre && s.basis bit)) rest
        (s.basis pre && !s.basis bit)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hpb,hpa,hpr⟩,⟨hba,hbr⟩,har⟩ := distinct
  have hap := Ne.symm hpa
  have hab := Ne.symm hba
  have hrp := Ne.symm hpr
  have hrb := Ne.symm hbr
  have hra := Ne.symm har
  cases hp : s.basis pre <;> cases hb : s.basis bit <;>
    simp_all [hmrFlagCell,run,writeBit,Function.update]

theorem hmrFlagCell_release (pre bit anchor rest : Wire)
    (distinct : [pre,bit,anchor,rest].Nodup) (s : State) (m : List Bool)
    (ha : s.basis anchor=false) (hr : s.basis rest=false) :
    run (hmrFlagCell pre bit anchor rest ++ hmrFlagRelease pre bit anchor rest) m s=s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨hpb,hpa,hpr⟩,⟨hba,hbr⟩,har⟩ := distinct
  have hap := Ne.symm hpa
  have hab := Ne.symm hba
  have hrp := Ne.symm hpr
  have hrb := Ne.symm hbr
  have hra := Ne.symm har
  cases hp : s.basis pre <;> cases hb : s.basis bit <;> cases hm : m.head?.getD false <;>
    simp_all [hmrFlagCell,hmrFlagRelease,run,measureAndCorrect,correct,writeBit,Function.update]

  all_goals
    have hx (v : Bool) : Function.update (Function.update (Function.update s.basis anchor v) rest false) anchor false = s.basis := by
      funext q
      by_cases hqa : q=anchor <;> by_cases hqr : q=rest <;> simp_all [Function.update]
    rw [hx]



end ECDSAAdd.Arithmetic.Paper935
