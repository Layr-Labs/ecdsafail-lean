import ECDSAAdd.Framework.Cost

namespace ECDSAAdd

/-- Relabel every gate and every measurement correction together. -/
def renameCorrection (f : Wire → Wire) : Correction → Correction
  | .Z q => .Z (f q)
  | .CZ a b => .CZ (f a) (f b)

def renameInstr (f : Wire → Wire) : Instr → Instr
  | .X q => .X (f q)
  | .CX a q => .CX (f a) (f q)
  | .CCX a b q => .CCX (f a) (f b) (f q)
  | .measureX q c0 c1 =>
      .measureX (f q) (c0.map (renameCorrection f)) (c1.map (renameCorrection f))

def renameProgram (f : Wire → Wire) (p : Program) : Program := p.map (renameInstr f)

def pullState (f : Wire → Wire) (s : State) : State :=
  ⟨s.phase,fun q => s.basis (f q)⟩

theorem State.extensionality (s t : State) (hp : s.phase=t.phase)
    (hb : s.basis=t.basis) : s=t := by
  cases s
  cases t
  simp_all

theorem pullState_write (f : Wire → Wire) (hf : Function.Injective f)
    (ph : Bool) (bits : BasisState) (q : Wire) (v : Bool) :
    pullState f ⟨ph,writeBit bits (f q) v⟩ =
      ⟨ph,writeBit (fun j => bits (f j)) q v⟩ := by
  unfold pullState
  congr 1
  funext j
  simp [writeBit,Function.update,hf.eq_iff]

theorem pullState_correct (f : Wire → Wire) (cs : List Correction) (s : State) :
    pullState f (correct (cs.map (renameCorrection f)) s) =
      correct cs (pullState f s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp only [List.map_cons,renameCorrection,correct] <;>
      rw [ih] <;> rfl

theorem pullState_measure (f : Wire → Wire) (hf : Function.Injective f)
    (q : Wire) (c0 c1 : List Correction) (m : Bool) (s : State) :
    pullState f (measureAndCorrect (f q)
      (c0.map (renameCorrection f)) (c1.map (renameCorrection f)) m s) =
      measureAndCorrect q c0 c1 m (pullState f s) := by
  cases m <;> simp only [measureAndCorrect,Bool.false_eq_true,if_false,if_true]
  all_goals
    rw [pullState_correct,pullState_write f hf]
    rfl

/-- Renaming preserves basis behavior and phase on all measurement records.
The injectivity premise forbids aliasing distinct circuit wires. -/
theorem run_rename (f : Wire → Wire) (hf : Function.Injective f)
    (p : Program) (m : List Bool) (s : State) :
    pullState f (run (renameProgram f p) m s) = run p m (pullState f s) := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [renameProgram,List.map_cons,renameInstr,run]
    all_goals change pullState f (run (renameProgram f p) _ _) = _
    all_goals rw [ih]
    all_goals first
      | rw [pullState_write f hf]; rfl
      | rw [pullState_measure f hf]

theorem renameProgram_counts (f : Wire → Wire) (p : Program) :
    toffoliCount (renameProgram f p) = toffoliCount p ∧
      measurementCount (renameProgram f p) = measurementCount p := by
  induction p with
  | nil => exact ⟨rfl,rfl⟩
  | cons i p ih =>
    simp only [renameProgram] at ih
    cases i <;> simp [renameProgram,renameInstr,toffoliCount,measurementCount,ih]

theorem renameCorrection_support (f : Wire → Wire) (cs : List Correction) :
    correctionWires (cs.map (renameCorrection f)) = (correctionWires cs).image f := by
  induction cs with
  | nil => simp [correctionWires]
  | cons c cs ih =>
    cases c <;> simp [renameCorrection,correctionWires,ih]

theorem renameInstr_support (f : Wire → Wire) (i : Instr) :
    (renameInstr f i).wires=i.wires.image f := by
  cases i <;> simp [renameInstr,Instr.wires,renameCorrection_support,Finset.image_union]

theorem renameProgram_support (f : Wire → Wire) (p : Program) :
    wires (renameProgram f p)=(wires p).image f := by
  induction p with
  | nil => simp [renameProgram,wires]
  | cons i p ih =>
    simp only [renameProgram] at ih
    simp [renameProgram,wires,renameInstr_support,ih,Finset.image_union]

end ECDSAAdd
