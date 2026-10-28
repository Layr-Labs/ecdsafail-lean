import ECDSAAdd.Arithmetic.Paper935.CompiledPostMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- Before freeze detection begins, the emitted three-gate post-stage
preserves the mathematical rows/offset and clears activity with no work pool. -/
theorem unarmedPost_pinStep (A : Arena) (F : SlotRegisters) (b : WindowBank)
    (tmin index : Nat) (before : index<tmin) (old : PinState) (s : State) (m : List Bool)
    (ready : A.Ready s.basis) (hf : F.frozen≠F.active) (hw : F.work1≠F.active)
    (activity : s.basis F.active= !s.basis F.frozen) (fire : s.basis F.work1=false)
    (hfrozen : s.basis F.frozen=old.frozen) (hoffset : regValue F.offset s.basis=old.offset)
    (activeOffset : old.frozen=false → old.offset=0)
    (rows : b.Encodes s.basis (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows))
    (rowAway : F.active∉b.rows.flatMap WindowRow.wires) (offsetAway : F.active∉F.offset) :
    let t := run (retireActivity F.frozen F.work1 F.active) m s
    t.phase=s.phase ∧ A.Ready t.basis ∧ b.Encodes t.basis (pinStep tmin index old).rows ∧
    t.basis F.frozen=(pinStep tmin index old).frozen ∧
    regValue F.offset t.basis=(pinStep tmin index old).offset ∧ t.basis F.active=false ∧
    (∀ q,q≠F.active → t.basis q=s.basis q) := by
  have run_eq := retireActivity_run F.frozen F.work1 F.active hf hw s m (by simpa [fire] using activity)
  have frame (q : Wire) (hq : q≠F.active) : (writeBit s.basis F.active false) q=s.basis q :=
    Function.update_of_ne hq _ _
  have pin := pinStep_flag_record tmin index old activeOffset
  simp only [show ¬tmin≤ index from Nat.not_le_of_gt before,decide_false,Bool.false_and,
    Bool.or_false,Bool.false_eq_true,ite_false,Nat.xor_zero] at pin
  dsimp only
  rw [run_eq]
  refine ⟨rfl,?_,?_,?_,?_,?_,frame⟩
  · intro q hq hn
    by_cases he : q=F.active
    · subst q; exact Function.update_self _ _ _
    · exact (frame q he).trans (ready q hq hn)
  · rw [pinStep_rows]
    apply b.encodes_congr s.basis _ _ rows
    intro q hq
    exact frame q (fun he => rowAway (he ▸ hq))
  · exact (frame F.frozen hf).trans (hfrozen.trans pin.1.symm)
  · rw [regValue_congr F.offset _ s.basis (fun q hq => frame q (fun he => offsetAway (he ▸ hq))),hoffset]
    exact pin.2.symm
  · exact Function.update_self _ _ _

end ECDSAAdd.Arithmetic.Paper935
