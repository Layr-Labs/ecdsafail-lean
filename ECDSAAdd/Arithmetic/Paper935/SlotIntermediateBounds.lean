import ECDSAAdd.Arithmetic.Paper935.AuthorWalkMathGeometry
import ECDSAAdd.Arithmetic.Paper935.WindowHeadroom

namespace ECDSAAdd.Arithmetic.Paper935

/-- The actual padded routed layout has enough headroom for every arithmetic
intermediate whenever the incoming mathematical rows fit their public bank. -/
theorem SlotFront.Compiled.intermediates_fit (P : SlotFront) (A : Arena) (b : WindowBank)
    (before exitWidth : RowWindow) (F : SlotRegisters)
    (compiled : P.Compiled A b before.addPad exitWidth F)
    (old : ECDSAAdd.Divsteps.ZState) (fit : before.Fits old) :
    before.addPad.Fits old ∧
    PayloadFits (P.layout.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep old).g) ∧
    PayloadFits (P.layout.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep old).gv ∧
    PayloadFits (P.layout.vmid.length+1) (ECDSAAdd.Divsteps.zStep old).fv := by
  have widths := compileBankResize_widths A P.addArena b P.addBank before.addPad P.padding compiled.padding
  have route := compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.addBank P.layout compiled.routed
  have layoutWidths : P.layout.before.Widths before.addPad := by rw [route.2.1]; exact widths
  have intermediate := before.addPad_step_fits old fit
  have g : P.layout.gmid.length+1=before.addPad.g := by
    simpa only [WindowBank.Widths,RoutedBankLayout.before,List.length_cons,Nat.add_comm] using layoutWidths.2.1
  have gv : P.layout.gv.wires.length-1=before.addPad.gv := by
    simpa only [RoutedBankLayout.before,WindowRow.wires,List.length_append,List.length_singleton,Nat.add_sub_cancel] using layoutWidths.2.2.2
  have fv : P.layout.vmid.length+1=before.addPad.fv := by
    simpa only [RoutedBankLayout.before,List.length_cons,Nat.add_comm] using layoutWidths.2.2.1
  refine ⟨(fit.mono before.pairPad_covers).mono before.addPad_covers,?_,?_,?_⟩
  · simpa only [g] using intermediate.1
  · simpa only [gv] using intermediate.2.1
  · simpa only [fv] using intermediate.2.2

end ECDSAAdd.Arithmetic.Paper935
