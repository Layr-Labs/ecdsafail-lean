import ECDSAAdd.Framework.WireRename

namespace ECDSAAdd.Arithmetic

/-- Store B AND (source XOR constant). The source returns before the body. -/
def transcriptSelectCompute (b source flag : Wire) (constant : Bool) : Program :=
  (if constant then [.X source] else []) ++ [.CCX b source flag] ++
    (if constant then [.X source] else [])

/-- During the body the flag is the selected actual/constant transcript bit. -/
def transcriptSelectExpose (flag : Wire) (constant : Bool) : Program :=
  if constant then [.X flag] else []

def transcriptSelectErase (b source flag : Wire) (constant : Bool) : Program :=
  [.measureX flag [] (if constant then [.Z b,.CZ b source] else [.CZ b source])]

theorem transcriptSelect_value (b actual constant : Bool) :
    (constant ^^ (b && (actual ^^ constant)))=(if b then actual else constant) := by
  cases b <;> cases actual <;> cases constant <;> rfl

private theorem select_distinct (b source flag : Wire) (hn : [b,source,flag].Nodup) :
    b≠source ∧ b≠flag ∧ source≠flag := by
  simpa [List.nodup_cons,List.mem_cons,and_assoc] using hn

theorem transcriptSelectCompute_correct (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool) :
    run (transcriptSelectCompute b source flag constant) m s=
      ⟨s.phase,writeBit s.basis flag
        (s.basis flag ^^ (s.basis b && (s.basis source ^^ constant)))⟩ := by
  have h := select_distinct b source flag hn
  cases constant <;> simp only [transcriptSelectCompute,Bool.false_eq_true,if_false,if_true,
    List.nil_append,List.cons_append,List.append_nil,run]
  all_goals apply State.extensionality
  all_goals try rfl
  all_goals
    funext q
    by_cases hq : q=source
    · subst q
      cases hb : s.basis b <;> cases hs : s.basis source <;> cases hf : s.basis flag <;>
        simp_all [writeBit,Function.update]
    · by_cases hqf : q=flag
      · subst q
        cases hb : s.basis b <;> cases hs : s.basis source <;> cases hf : s.basis flag <;>
          simp_all [writeBit,Function.update]
      · simp_all [writeBit,Function.update]

/-- Measured cleanup is exact for both outcomes, including complemented
source selection. No global-phase shortcut or approximate predictor is used. -/
theorem transcriptSelectErase_correct (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool)
    (hv : s.basis flag=(s.basis b && (s.basis source ^^ constant))) :
    run (transcriptSelectErase b source flag constant) m s=
      ⟨s.phase,writeBit s.basis flag false⟩ := by
  have h := select_distinct b source flag hn
  cases constant <;> cases hm : m.headD false <;>
    cases hb : s.basis b <;> cases hs : s.basis source <;>
    simp_all [transcriptSelectErase,run,measureAndCorrect,correct,writeBit,Function.update]

theorem transcriptSelect_counts (b source flag : Wire) (constant : Bool) :
    toffoliCount (transcriptSelectCompute b source flag constant)=1 ∧
    measurementCount (transcriptSelectCompute b source flag constant)=0 ∧
    toffoliCount (transcriptSelectExpose flag constant)=0 ∧
    measurementCount (transcriptSelectExpose flag constant)=0 ∧
    toffoliCount (transcriptSelectErase b source flag constant)=0 ∧
    measurementCount (transcriptSelectErase b source flag constant)=1 := by
  cases constant <;> simp [transcriptSelectCompute,transcriptSelectExpose,transcriptSelectErase,
    toffoliCount,measurementCount]

/-- The second exposure restores the stored product before measurement.
Keeping this inside the emitted window prevents a complemented-control
cleanup from introducing an outcome-dependent global phase. -/
def transcriptSelectWindow (b source flag : Wire) (constant : Bool) (body : Program) : Program :=
  transcriptSelectCompute b source flag constant ++ transcriptSelectExpose flag constant ++
    body ++ transcriptSelectExpose flag constant ++ transcriptSelectErase b source flag constant

/-- Safe cleanup after a body that preserves the effective flag and its
enable/source inputs. The semantic premise is the selected control value. -/
theorem transcriptSelect_finish_correct (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool)
    (hv : s.basis flag=(if s.basis b then s.basis source else constant)) :
    run (transcriptSelectExpose flag constant ++ transcriptSelectErase b source flag constant) m s=
      ⟨s.phase,writeBit s.basis flag false⟩ := by
  have h := select_distinct b source flag hn
  cases constant <;> cases hm : m.headD false <;>
    cases hb : s.basis b <;> cases hs : s.basis source <;>
    simp_all [transcriptSelectExpose,transcriptSelectErase,run,measureAndCorrect,
      correct,writeBit,Function.update]

theorem transcriptSelectWindow_counts (b source flag : Wire) (constant : Bool) (body : Program) :
    toffoliCount (transcriptSelectWindow b source flag constant body)=toffoliCount body+1 ∧
    measurementCount (transcriptSelectWindow b source flag constant body)=measurementCount body+1 := by
  have hc := transcriptSelect_counts b source flag constant
  simp only [transcriptSelectWindow,toffoliCount_append,measurementCount_append,
    hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2]
  constructor <;> omega

end ECDSAAdd.Arithmetic
