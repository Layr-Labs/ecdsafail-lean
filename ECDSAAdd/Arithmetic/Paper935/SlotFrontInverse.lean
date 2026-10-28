import ECDSAAdd.Arithmetic.Paper935.SlotFrontMath

namespace ECDSAAdd.Arithmetic.Paper935

theorem SlotFront.Compiled.roundtrip (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (compiled : P.Compiled A b addWidth exitWidth F)
    (physical : P.PhysicalChecks F) (checks : P.MathChecks F exitWidth)
    (old : PinState) (s : State) (m n : List Bool) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis old.rows) (prefit : addWidth.Fits old.rows)
    (values : F.Values s.basis old) (owned : F.wires.toFinset⊆A.live)
    (away : List.Disjoint F.wires (b.rows.flatMap WindowRow.wires))
    (p : Int) (inv : ECDSAAdd.Divsteps.Inv p old.rows) (odd : p%2=1) (fodd : old.rows.f%2=1)
    (frozenZero : old.frozen=true → old.rows.g=0)
    (gfit : old.frozen=false → PayloadFits (P.layout.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep old.rows).g))
    (gvfit : old.frozen=false → PayloadFits (P.layout.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep old.rows).gv)
    (fvfit : old.frozen=false → PayloadFits (P.layout.vmid.length+1) (ECDSAAdd.Divsteps.zStep old.rows).fv)
    (exitfit : exitWidth.Fits (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows))
    : run (P.inverse F) n (run (P.program F) m s)=s := by
  let v := run P.padding m s
  let ms := m.drop (measurementCount P.padding)
  have padding := compiled.padding_state P A b addWidth exitWidth F old s m ready rows prefit values owned away
  rcases padding with ⟨vready,vrows,vvalues,vowned,vmeta⟩
  have layouts := compiled.layouts P A b addWidth exitWidth F physical.1
  obtain ⟨valid,view,qeq,beq,ueq,keq,aeq⟩ :=
    compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.addBank P.layout compiled.routed
  have ownCounter : (P.layout.active::P.layout.q::F.counter).toFinset⊆P.addArena.live := by
    rw [aeq,qeq]
    intro q hq
    apply vmeta
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl|rfl|hq
    · simp [SlotRegisters.wires]
    · simp [SlotRegisters.wires]
    · simp [SlotRegisters.wires,hq]
  have ownParity : P.layout.parity∈P.addArena.live := by
    rw [beq]
    exact vmeta (by simp [SlotRegisters.wires])
  have body := P.layout.retiredWindow_roundtrip valid P.exitBank exitWidth P.addArena P.exitArena P.counterArena
    P.resizing layouts.2.2.2.1 F.counter P.zero P.carry physical.2.1 layouts.2.2.2.2.1 layouts.2.2.2.2.2.1
    vowned.2 ownCounter checks.beforeApart checks.afterApart checks.exitApart layouts.2.2.2.2.2.2
    F.frozen (F.counter.getLastD 0) F.counter.dropLast checks.counterView checks.tags ownParity checks.preparation
    physical.2.2.2.2.1 checks.coefficientWidth p old.rows inv odd old.frozen fodd v ms n
    vvalues.frozen vvalues.counter (by rw [ueq]; exact vvalues.work0) (by rw [keq]; exact vvalues.work1)
    (by rw [aeq]; exact vvalues.active) (by rw [qeq]; exact vvalues.swap) (by rw [beq]; exact vvalues.parity)
    vrows frozenZero gfit gvfit fvfit vready exitfit
  rw [SlotFront.program,run_append,run_take,SlotFront.inverse,run_append,run_take,body]
  exact b.resize_roundtrip P.addBank addWidth A P.addArena P.padding layouts.1 s m _

end ECDSAAdd.Arithmetic.Paper935
