import ECDSAAdd.Arithmetic.Paper935.CheckedPublicSlot
import ECDSAAdd.Arithmetic.Paper935.WindowSlotMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- The compiled armed post-stage implements the mathematical freeze flag
and offset transition on actual row values. All workspace is allocator-derived. -/
theorem compileBorrowedPost_pinStep (A D : Arena) (F : SlotRegisters) (b : WindowBank)
    (work : List Wire) (width tmin index : Nat) (P : WindowPostLayout)
    (h : compileBorrowedPost A (decide (tmin≤ index)) F.one F.work0 F.frozen F.work1 F.active
      b.g.wires F.offset width (index+1-tmin)=some (D,work,P))
    (old : PinState) (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (hone : s.basis F.one=true) (hzf : s.basis F.work0=false) (hfire : s.basis F.work1=false)
    (activity : s.basis F.active= !s.basis F.frozen)
    (hfrozen : s.basis F.frozen=old.frozen) (hoffset : regValue F.offset s.basis=old.offset)
    (oldOffset : tmin≤ index → old.offset< index+1-tmin)
    (activeOffset : old.frozen=false → old.offset=0)
    (rows : b.Encodes s.basis (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows))
    (owned : (F.active::F.frozen::F.offset).toFinset⊆A.live)
    (separate : ∀ q∈b.rows.flatMap WindowRow.wires,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset) :
    let t := run P.program m s
    t.phase=s.phase ∧ A.Ready t.basis ∧ b.Encodes t.basis (pinStep tmin index old).rows ∧
    t.basis F.frozen=(pinStep tmin index old).frozen ∧
    regValue F.offset t.basis=(pinStep tmin index old).offset ∧
    t.basis F.active=false ∧ t.basis F.work0=false ∧ t.basis F.work1=false ∧
    D.release work.toFinset t.basis=some A ∧
    (∀ q,q≠F.active → q≠F.frozen → q∉F.offset → t.basis q=s.basis q) := by
  have pair := compileBorrowedPost_contract A D _ F.one F.work0 F.frozen F.work1 F.active
    b.g.wires F.offset work width (index+1-tmin) P h
  have hc := compilePost_contract _ F.one F.work0 F.frozen F.work1 F.active
    b.g.wires F.offset work width (index+1-tmin) P pair.2
  have ids := compilePost_identity _ F.one F.work0 F.frozen F.work1 F.active
    b.g.wires F.offset work width (index+1-tmin) P pair.2
  have limit : decide (tmin≤ index)=true → regValue F.offset s.basis< index+1-tmin := by
    intro hi
    rw [hoffset]
    exact oldOffset (of_decide_eq_true hi)
  have zero : s.basis F.frozen=false → regValue F.offset s.basis=0 := by
    rw [hfrozen,hoffset]
    exact activeOffset
  have r := compileBorrowedPost_ready A D _ F.one F.work0 F.frozen F.work1 F.active
    b.g.wires F.offset work width (index+1-tmin) P h s.basis ready hone hzf hfire activity limit zero
  have post := P.run_spec hc.1 s m r
  have release := compileBorrowedPost_release A D _ F.one F.work0 F.frozen F.work1 F.active
    b.g.wires F.offset work width (index+1-tmin) P h owned s m ready hone hzf hfire activity limit zero
  have enc := b.encodes_congr s.basis (run P.program m s).basis _ rows (by
    intro q hq
    obtain ⟨ha,hf,hr⟩ := separate q hq
    apply post.2.2.2.2.2.2 q
    · rw [ids.2.2.2.2.2.1]; exact ha
    · rw [ids.2.2.2.1]; exact hf
    · rw [hc.2.2.1]; exact hr)
  have zeroeq : decide (regValue (BlockedZero.inputs P.blocks) s.basis=0)=
      decide ((if old.frozen then old.rows.g else (ECDSAAdd.Divsteps.zStep old.rows).g)=0) := by
    simp only [hc.2.1,←signedRegValue_zero_iff]
    have gvalue := rows.2.1
    cases hf : old.frozen <;> simpa [WindowRow.value,hf] using congrArg (fun x : Int => decide (x=0)) gvalue
  have pin := pinStep_flag_record tmin index old activeOffset
  dsimp only
  refine ⟨post.1,release.2,?_,?_,?_,?_,?_,?_,release.1,?_⟩
  · rw [pinStep_rows]; exact enc
  · rw [←ids.2.2.2.1,post.2.2.2.2.1,ids.2.2.2.1,hfrozen,zeroeq,ids.1]
    exact pin.1.symm
  · rw [←hc.2.2.1,post.2.2.2.2.2.1,hc.2.2.1,hoffset,ids.2.2.2.1,hfrozen,zeroeq,ids.1,ids.2.2.2.2.2.2]
    exact pin.2.symm
  · rw [←ids.2.2.2.2.2.1]; exact post.2.1
  · rw [←ids.2.2.1]; exact post.2.2.1
  · rw [←ids.2.2.2.2.1]; exact post.2.2.2.1

  · intro q ha hf hr
    apply post.2.2.2.2.2.2 q
    · rw [ids.2.2.2.2.2.1]; exact ha
    · rw [ids.2.2.2.1]; exact hf
    · rw [hc.2.2.1]; exact hr

end ECDSAAdd.Arithmetic.Paper935
