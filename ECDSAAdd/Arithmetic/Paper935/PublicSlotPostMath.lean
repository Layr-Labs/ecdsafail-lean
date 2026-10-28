import ECDSAAdd.Arithmetic.Paper935.UnarmedPostMath
import ECDSAAdd.Arithmetic.Paper935.SlotOutputValues

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileCheckedPublicSlot_post_math (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth tmin index : Nat) (P : PublicSlot)
    (h : compileCheckedPublicSlot A b addWidth exitWidth F (decide (tmin≤ index)) probeWidth (index+1-tmin)=some P)
    (old : PinState) (s : State) (m : List Bool) (ready : P.front.exitArena.Ready s.basis)
    (rows : P.front.exitBank.Encodes s.basis (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows))
    (mid : F.MidValues s.basis old) (oldOffset : tmin≤ index → old.offset< index+1-tmin)
    (activeOffset : old.frozen=false → old.offset=0)
    (owned : (F.active::F.frozen::F.offset).toFinset⊆P.front.exitArena.live)
    (rowApart : ∀ q∈P.front.exitBank.rows.flatMap WindowRow.wires,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset)
    (metaApart : ∀ q∈[F.one,F.swap,F.parity]++F.counter,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset)
    (workApart : F.work0≠F.active ∧ F.work1≠F.active) (offsetApart : F.active∉F.offset) :
    let t := run (P.postProgram F) m s
    t.phase=s.phase ∧ P.front.exitArena.Ready t.basis ∧
    P.front.exitBank.Encodes t.basis (pinStep tmin index old).rows ∧
    F.OutputValues t.basis old (pinStep tmin index old) := by
  have hc := compileCheckedPublicSlot_contract A b addWidth exitWidth F _ probeWidth (index+1-tmin) P h
  have activity : s.basis F.active= !s.basis F.frozen := by rw [mid.active,mid.frozen]
  cases ha : decide (tmin≤ index) with
  | false =>
    have compile := hc.1
    rw [ha] at compile
    have post := (compilePublicSlot_unarmed A b addWidth exitWidth F probeWidth (index+1-tmin) P compile).1
    have checks := hc.2.2
    simp only [PublicSlot.PostChecks,post] at checks
    have before : index<tmin := Nat.lt_of_not_ge (of_decide_eq_false ha)
    have rowAway : F.active∉P.front.exitBank.rows.flatMap WindowRow.wires := by
      intro hh; exact (rowApart _ hh).1 rfl
    have result := unarmedPost_pinStep P.front.exitArena F P.front.exitBank tmin index before old s m
      ready checks.1 checks.2.1 activity mid.work1 mid.frozen mid.offset activeOffset rows rowAway offsetApart
    rcases result with ⟨phase,clean,enc,flag,record,active,frame⟩
    dsimp only
    simp only [PublicSlot.postProgram,post]
    refine ⟨phase,clean,enc,?_⟩
    exact F.output_from_post s.basis _ old tmin index mid flag record active
      ((frame _ workApart.1).trans mid.work0) ((frame _ workApart.2).trans mid.work1)
      (fun q hq _ _ => frame q hq) metaApart
  | true =>
    have compile := hc.1
    rw [ha] at compile
    obtain ⟨post,hpost,hcompile⟩ := compilePublicSlot_armed A b addWidth exitWidth F probeWidth (index+1-tmin) P compile
    have result := compileBorrowedPost_pinStep P.front.exitArena P.postArena F P.front.exitBank
      P.postWork probeWidth tmin index post (by simpa only [ha] using hcompile) old s m ready
      mid.one mid.work0 mid.work1 activity mid.frozen mid.offset oldOffset activeOffset rows owned rowApart
    rcases result with ⟨phase,clean,enc,flag,record,active,w0,w1,_,frame⟩
    dsimp only
    simp only [PublicSlot.postProgram,hpost]
    exact ⟨phase,clean,enc,F.output_from_post s.basis _ old tmin index mid flag record active w0 w1 frame metaApart⟩

end ECDSAAdd.Arithmetic.Paper935
