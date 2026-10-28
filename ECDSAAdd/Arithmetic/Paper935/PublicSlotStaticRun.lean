import ECDSAAdd.Arithmetic.Paper935.SlotIntermediateBounds

namespace ECDSAAdd.Arithmetic.Paper935

/-- The actual public slot implements pinStep with all intermediate-width and
address premises discharged by static geometry. Only mathematical input/state
conditions and the actual exit/counter fit events remain explicit. -/
theorem compileCheckedPublicSlot_static_run (A : Arena) (b : WindowBank) (exitWidth : RowWindow)
    (F : SlotRegisters) (record : List Wire) (probeWidth tmin index : Nat) (P : PublicSlot)
    (compiled : compileCheckedPublicSlot A b (bankWidths b).addPad exitWidth F (decide (tmin≤ index))
      probeWidth (index+1-tmin)=some P)
    (checks : P.StaticMathChecks F)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (old : PinState) (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis old.rows) (fit : (bankWidths b).Fits old.rows)
    (values : F.Values s.basis old)
    (p : Int) (inv : ECDSAAdd.Divsteps.Inv p old.rows) (odd : p%2=1) (fodd : old.rows.f%2=1)
    (frozenZero : old.frozen=true → old.rows.g=0)
    (exitfit : exitWidth.Fits (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows))
    (zfit : PayloadFits (F.counter.length-1) (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows).z)
    (oldOffset : tmin≤ index → old.offset< index+1-tmin) (activeOffset : old.frozen=false → old.offset=0) :
    let t := run (P.program F) m s
    t.phase=s.phase ∧ P.front.exitArena.Ready t.basis ∧
    P.front.exitBank.Encodes t.basis (pinStep tmin index old).rows ∧
    F.OutputValues t.basis old (pinStep tmin index old) := by
  have publicCompiled := (compileCheckedPublicSlot_contract _ _ _ _ _ _ _ _ _ compiled).1
  have frontCompiled := compilePublicSlot_front _ _ _ _ _ _ _ _ _ publicCompiled
  have front := compileSlotFront_contract A b (bankWidths b).addPad exitWidth F P.front frontCompiled
  have intermediate := front.intermediates_fit P.front A b (bankWidths b) exitWidth F old.rows fit
  have widths := compileBankResize_widths P.front.addArena P.front.exitArena P.front.layout.after
    P.front.exitBank exitWidth P.front.resizing front.resizing
  have wc : bankWidths P.front.exitBank=exitWidth := by
    cases exitWidth
    simp only [WindowBank.Widths] at widths
    simp only [bankWidths,widths.1,widths.2.1,widths.2.2.1,widths.2.2.2]
  have metaOwned : F.wires.toFinset⊆A.live := by
    intro q hq
    apply owned
    simp only [List.mem_toFinset,List.mem_append] at hq ⊢
    exact Or.inl (Or.inl hq)
  have apart : List.Disjoint F.wires (b.rows.flatMap WindowRow.wires) := by
    have h := (List.nodup_append'.mp distinct).2.2
    exact List.disjoint_left.mpr (fun q hq hr => List.disjoint_left.mp h (List.mem_append_left _ hq) hr)
  exact compileCheckedPublicSlot_run A b (bankWidths b).addPad exitWidth F probeWidth tmin index P compiled
    (by simpa only [wc] using checks.front) old s m ready rows intermediate.1 values metaOwned apart
    p inv odd fodd frozenZero (fun _ => intermediate.2.1) (fun _ => intermediate.2.2.1)
    (fun _ => intermediate.2.2.2) exitfit zfit oldOffset activeOffset
    checks.postOwned checks.postRows checks.postMeta checks.offsetApart

end ECDSAAdd.Arithmetic.Paper935
