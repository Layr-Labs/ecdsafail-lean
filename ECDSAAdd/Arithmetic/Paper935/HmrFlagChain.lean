import ECDSAAdd.Arithmetic.Paper935.HmrFlagCell

namespace ECDSAAdd.Arithmetic.Paper935

structure HmrFlagStage where
  pre : Wire
  bit : Wire
  anchor : Wire
  rest : Wire

def HmrFlagStage.advance (b : HmrFlagStage) (s : BasisState) : BasisState :=
  writeBit (writeBit s b.anchor (s b.pre && s b.bit)) b.rest (s b.pre && !s b.bit)

def hmrFlagSweep : List HmrFlagStage → Program
  | [] => []
  | b::bs => hmrFlagCell b.pre b.bit b.anchor b.rest ++ hmrFlagSweep bs

def hmrFlagUnsweep : List HmrFlagStage → Program
  | [] => []
  | b::bs => hmrFlagUnsweep bs ++ hmrFlagRelease b.pre b.bit b.anchor b.rest

def hmrFlagAdvance : List HmrFlagStage → BasisState → BasisState
  | [],s => s
  | b::bs,s => hmrFlagAdvance bs (b.advance s)

def HmrFlagReady : List HmrFlagStage → BasisState → Prop
  | [],_ => True
  | b::bs,s => [b.pre,b.bit,b.anchor,b.rest].Nodup ∧
      s b.anchor=false ∧ s b.rest=false ∧ HmrFlagReady bs (b.advance s)

theorem hmrFlagSweep_measurementCount (bs : List HmrFlagStage) :
    measurementCount (hmrFlagSweep bs)=0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [hmrFlagSweep,hmrFlagCell,measurementCount,ih]

theorem hmrFlagSweep_run (bs : List HmrFlagStage) (s : State) (m : List Bool)
    (ready : HmrFlagReady bs s.basis) :
    run (hmrFlagSweep bs) m s=⟨s.phase,hmrFlagAdvance bs s.basis⟩ := by
  induction bs generalizing s m with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨distinct,ha,hr,rest⟩ := ready
    have cell := hmrFlagCell_run b.pre b.bit b.anchor b.rest distinct s m ha hr
    have count : measurementCount (hmrFlagCell b.pre b.bit b.anchor b.rest)=0 := rfl
    rw [hmrFlagSweep,run_append,run_take,count,List.drop_zero,cell]
    exact ih ⟨s.phase,b.advance s.basis⟩ m rest

theorem hmrFlagUnsweep_run (bs : List HmrFlagStage) (s : State) (m : List Bool)
    (ready : HmrFlagReady bs s.basis) :
    run (hmrFlagUnsweep bs) m ⟨s.phase,hmrFlagAdvance bs s.basis⟩=s := by
  induction bs generalizing s m with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨distinct,ha,hr,rest⟩ := ready
    rw [hmrFlagUnsweep,run_append,run_take]
    change run (hmrFlagRelease b.pre b.bit b.anchor b.rest)
      (m.drop (measurementCount (hmrFlagUnsweep bs)))
      (run (hmrFlagUnsweep bs) m ⟨s.phase,hmrFlagAdvance bs (b.advance s.basis)⟩)=s
    rw [ih ⟨s.phase,b.advance s.basis⟩ m rest]
    let tape := m.drop (measurementCount (hmrFlagUnsweep bs))
    have h := hmrFlagCell_release b.pre b.bit b.anchor b.rest distinct s tape ha hr
    have count : measurementCount (hmrFlagCell b.pre b.bit b.anchor b.rest)=0 := rfl
    rw [run_append,run_take,count,List.drop_zero,
      hmrFlagCell_run b.pre b.bit b.anchor b.rest distinct s tape ha hr] at h
    exact h

theorem hmrFlagSweep_release (bs : List HmrFlagStage) (s : State) (m : List Bool)
    (ready : HmrFlagReady bs s.basis) :
    run (hmrFlagSweep bs ++ hmrFlagUnsweep bs) m s=s := by
  rw [run_append,run_take,hmrFlagSweep_measurementCount,List.drop_zero,
    hmrFlagSweep_run bs s m ready]
  exact hmrFlagUnsweep_run bs s m ready


end ECDSAAdd.Arithmetic.Paper935
