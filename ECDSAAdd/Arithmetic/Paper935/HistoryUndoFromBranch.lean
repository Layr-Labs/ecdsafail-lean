import ECDSAAdd.Arithmetic.Paper935.WalkRecovery

namespace ECDSAAdd.Arithmetic.Paper935

structure HistoryLayout.CleanInput (H : HistoryLayout) (s : BasisState) : Prop where
  one : s H.one=true
  zz : s H.zz=false
  pos : s H.pos=false
  output : s H.output=false
  counterWork : ∀ b∈H.zb,s b.work=false
  coefficientWork : ∀ b∈H.frozen::H.positive::H.low,s b.work=false

/-- The only decoder contract needed locally is its actual branch value.
The original recorded outcome then cancels the measurement phase before pop. -/
theorem historyUndoAt_of_branch_run (H : HistoryLayout) (valid : H.Valid)
    (s : State) (clean : H.CleanInput s.basis)
    (fit : H.selected s.basis=true → 2*regValue H.record s.basis+(s.basis H.port).toNat<2^H.record.length)
    (decoder : Program) (m : List Bool) (ordinal cursor : Nat)
    (decoded : let u := runWithTape H.program m ordinal s
      run decoder (m.drop cursor) u=
        ⟨u.phase,writeBit u.basis H.port (!H.selected s.basis && s.basis H.port)⟩) :
    HistoryUndoAt H decoder m ordinal cursor s := by
  obtain ⟨hz,hf,hsg,hp,hfr,hl,hw,hpush,hout,hstable⟩ := valid
  let segment := storePush H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record
  let t := run segment (m.drop ordinal) s
  let u := runWithTape H.program m ordinal s
  have hs := storePush_spec H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record
    hz hf hsg hp hfr hl hw s (m.drop ordinal) clean.one clean.zz clean.pos clean.counterWork clean.coefficientWork
    hpush clean.output hout hstable fit
  have hu := storePushForget_run H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record
    hz hf hsg hp hfr hl hw s m clean.one clean.zz clean.pos clean.counterWork clean.coefficientWork
    hpush clean.output hout hstable fit ordinal
  have phase : u.phase=(s.phase ^^ (m.getD (ordinal+measurementCount segment) false &&
      (!H.selected s.basis && s.basis H.port))) := congrArg State.phase hu
  have restore := ECDSAAdd.Arithmetic.Divsteps.recoverBranch_cancel decoder H.port
    (ordinal+measurementCount segment) m cursor u (!H.selected s.basis && s.basis H.port) s.phase phase decoded
  have htport : t.basis H.port=(!H.selected s.basis && s.basis H.port) := by
    have h := hs.2.2.1
    change t.basis H.port=(if H.selected s.basis then false else s.basis H.port) at h
    cases hsel : H.selected s.basis <;> simpa only [hsel,ite_true,Bool.false_eq_true,ite_false,
      Bool.not_true,Bool.not_false,Bool.false_and,Bool.true_and] using h
  have recovered : runWithTape (ECDSAAdd.Arithmetic.Divsteps.recoverBranch decoder H.port
      (ordinal+measurementCount segment)) m cursor u=t := by
    rw [restore]
    have hp' : s.phase=t.phase := hs.1.symm
    have hb' : writeBit u.basis H.port (!H.selected s.basis && s.basis H.port)=t.basis := by
      rw [show u= _ from hu]
      change writeBit (writeBit t.basis H.port false) H.port (!H.selected s.basis && s.basis H.port)=t.basis
      rw [←htport]
      simp [writeBit]
    cases h : t
    simp only [h] at hp' hb'
    simp only [hp',hb']
  change runWithTape (_ ++ _) m cursor u=s
  rw [runWithTape_append,recovered,runWithTape_embedRecorded]
  exact storeHistory_roundtrip H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record
    hz hf hsg hp hfr hl hw s (m.drop ordinal) clean.one clean.zz clean.pos clean.counterWork clean.coefficientWork
    hpush clean.output hout hstable fit _

end ECDSAAdd.Arithmetic.Paper935
