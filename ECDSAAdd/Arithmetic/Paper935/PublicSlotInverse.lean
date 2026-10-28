import ECDSAAdd.Arithmetic.Paper935.PublicSlotPostInverse
import ECDSAAdd.Arithmetic.Paper935.SlotFrontInverse

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileCheckedPublicSlot_roundtrip (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth tmin index : Nat) (P : PublicSlot)
    (h : compileCheckedPublicSlot A b addWidth exitWidth F (decide (tmin≤ index)) probeWidth (index+1-tmin)=some P)
    (checks : P.front.MathChecks F exitWidth)
    (old : PinState) (s : State) (m n : List Bool) (ready : A.Ready s.basis)
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
    : run (P.inverse F) n (run (P.program F) m s)=s := by
  have hc := compileCheckedPublicSlot_contract A b addWidth exitWidth F _ probeWidth (index+1-tmin) P h
  have compiled := compileSlotFront_contract A b addWidth exitWidth F P.front
    (compilePublicSlot_front A b addWidth exitWidth F _ probeWidth (index+1-tmin) P hc.1)
  have front := compiled.run_math P.front A b addWidth exitWidth F hc.2.1 checks old s m ready rows prefit
    values owned away p inv odd fodd frozenZero gfit gvfit fvfit exitfit zfit
  have postInverse := compileCheckedPublicSlot_post_roundtrip A b addWidth exitWidth F probeWidth tmin index P h
    old (run (P.front.program F) m s) (m.drop (measurementCount (P.front.program F))) n
    front.2.1 front.2.2.2 oldOffset activeOffset
  rw [PublicSlot.program,run_append,run_take,PublicSlot.inverse,run_append,run_take,postInverse]
  exact compiled.roundtrip P.front A b addWidth exitWidth F hc.2.1 checks old s m _ ready rows prefit
    values owned away p inv odd fodd frozenZero gfit gvfit fvfit exitfit

end ECDSAAdd.Arithmetic.Paper935
