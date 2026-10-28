import ECDSAAdd.Arithmetic.Paper935.PublicSlotPostMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- Complete emitted public slot: actual padding, arithmetic, resizing,
counter update, and the selected post-stage implement one pinStep. The
retained parity bit is explicit; history transport is a subsequent stage. -/
theorem compileCheckedPublicSlot_run (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth tmin index : Nat) (P : PublicSlot)
    (h : compileCheckedPublicSlot A b addWidth exitWidth F (decide (tmin≤ index)) probeWidth (index+1-tmin)=some P)
    (checks : P.front.MathChecks F exitWidth)
    (old : PinState) (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis old.rows) (prefit : addWidth.Fits old.rows)
    (values : F.Values s.basis old) (owned : F.wires.toFinset⊆A.live)
    (away : List.Disjoint F.wires (b.rows.flatMap WindowRow.wires))
    (p : Int) (inv : ECDSAAdd.Divsteps.Inv p old.rows) (odd : p%2=1) (fodd : old.rows.f%2=1)
    (frozenZero : old.frozen=true → old.rows.g=0)
    (gfit : old.frozen=false → PayloadFits (P.front.layout.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep old.rows).g))
    (gvfit : old.frozen=false → PayloadFits (P.front.layout.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep old.rows).gv)
    (fvfit : old.frozen=false → PayloadFits (P.front.layout.vmid.length+1) (ECDSAAdd.Divsteps.zStep old.rows).fv)
    (exitfit : exitWidth.Fits (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows))
    (zfit : PayloadFits (F.counter.length-1) (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows).z)
    (oldOffset : tmin≤ index → old.offset< index+1-tmin) (activeOffset : old.frozen=false → old.offset=0)
    (postOwned : (F.active::F.frozen::F.offset).toFinset⊆P.front.exitArena.live)
    (postRows : ∀ q∈P.front.exitBank.rows.flatMap WindowRow.wires,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset)
    (postMeta : ∀ q∈[F.one,F.swap,F.parity]++F.counter,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset)
    (offsetApart : F.active∉F.offset) :
    let t := run (P.program F) m s
    t.phase=s.phase ∧ P.front.exitArena.Ready t.basis ∧
    P.front.exitBank.Encodes t.basis (pinStep tmin index old).rows ∧
    F.OutputValues t.basis old (pinStep tmin index old) := by
  have hc := compileCheckedPublicSlot_contract A b addWidth exitWidth F _ probeWidth (index+1-tmin) P h
  have compiled := compileSlotFront_contract A b addWidth exitWidth F P.front
    (compilePublicSlot_front A b addWidth exitWidth F _ probeWidth (index+1-tmin) P hc.1)
  have front := compiled.run_math P.front A b addWidth exitWidth F hc.2.1 checks old s m ready rows prefit
    values owned away p inv odd fodd frozenZero gfit gvfit fvfit exitfit zfit
  have ids := compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.front.addBank P.front.layout compiled.routed
  have workApart : F.work0≠F.active ∧ F.work1≠F.active := by
    have a := checks.persistent F.work0 (by simp)
    have b := checks.persistent F.work1 (by simp)
    rw [←ids.2.2.2.2.2.2]
    exact ⟨a.2.2.2.1,b.2.2.2.1⟩
  have post := compileCheckedPublicSlot_post_math A b addWidth exitWidth F probeWidth tmin index P h
    old (run (P.front.program F) m s) (m.drop (measurementCount (P.front.program F)))
    front.2.1 front.2.2.1 front.2.2.2 oldOffset activeOffset postOwned postRows postMeta workApart offsetApart
  dsimp only
  rw [PublicSlot.program,run_append,run_take]
  exact ⟨post.1.trans front.1,post.2⟩

end ECDSAAdd.Arithmetic.Paper935
