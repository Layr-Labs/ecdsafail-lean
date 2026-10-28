import ECDSAAdd.Arithmetic.Paper935.BankCompiler
import ECDSAAdd.Arithmetic.Paper935.RoutedCompilerTotal
import ECDSAAdd.Arithmetic.Paper935.WindowSlotPhysical

namespace ECDSAAdd.Arithmetic.Paper935

/-- Seven persistent control sites; work0/work1 are reused by arithmetic
and freeze post-processing. Counter and offset lists include all their bits. -/
structure SlotRegisters where
  one : Wire
  frozen : Wire
  parity : Wire
  active : Wire
  swap : Wire
  work0 : Wire
  work1 : Wire
  counter : List Wire
  offset : List Wire

def SlotRegisters.wires (F : SlotRegisters) : List Wire :=
  [F.one,F.frozen,F.parity,F.active,F.swap,F.work0,F.work1]++F.counter++F.offset

structure SlotFront where
  addArena : Arena
  addBank : WindowBank
  padding : Program
  layout : RoutedBankLayout
  exitArena : Arena
  exitBank : WindowBank
  resizing : Program
  counterArena : Arena
  zero : List Wire
  carry : List Wire

/-- Allocate the public addition window, route the actual rows, shrink to
the exit window, then borrow counter scratch from the newly freed space. -/
def compileSlotFront (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) : Option SlotFront := do
  let (B,padded,padding) ← compileBankResize A b addWidth
  let L ← compileRoutedBank F.swap F.parity F.work0 F.work1 F.active padded
  let (C,out,resizing) ← compileBankResize B L.after exitWidth
  let (D,zero,carry) ← planCounterScratch C F.counter.length
  pure ⟨B,padded,padding,L,C,out,resizing,D,zero,carry⟩

structure SlotFront.Compiled (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) : Prop where
  padding : compileBankResize A b addWidth=some (P.addArena,P.addBank,P.padding)
  routed : compileRoutedBank F.swap F.parity F.work0 F.work1 F.active P.addBank=some P.layout
  resizing : compileBankResize P.addArena P.layout.after exitWidth=some (P.exitArena,P.exitBank,P.resizing)
  counter : planCounterScratch P.exitArena F.counter.length=some (P.counterArena,P.zero,P.carry)

theorem compileSlotFront_contract (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (P : SlotFront) (h : compileSlotFront A b addWidth exitWidth F=some P) :
    P.Compiled A b addWidth exitWidth F := by
  unfold compileSlotFront at h
  obtain ⟨⟨B,padded,padding⟩,hpad,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨L,hl,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨C,out,resizing⟩,hresize,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨D,zero,carry⟩,hcounter,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨hpad,hl,hresize,hcounter⟩

/-- All public row plans and exact counter lengths now come from compilation. -/
theorem SlotFront.Compiled.layouts (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (h : P.Compiled A b addWidth exitWidth F)
    (hz : 1≤F.counter.length) :
    b.Planned P.addBank addWidth A P.addArena P.padding ∧ P.layout.Valid ∧
    P.layout.before=P.addBank ∧
    P.layout.after.Planned P.exitBank exitWidth P.addArena P.exitArena P.resizing ∧
    P.zero.length=F.counter.length ∧ P.carry.length+1=F.counter.length ∧
    P.exitArena.reserve (P.zero++P.carry).toFinset=some P.counterArena := by
  have routed := compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.addBank P.layout h.routed
  have counter := planCounterScratch_contract P.exitArena P.counterArena F.counter.length P.zero P.carry hz h.counter
  exact ⟨compileBankResize_contract A P.addArena b P.addBank addWidth P.padding h.padding,
    routed.1,routed.2.1,
    compileBankResize_contract P.addArena P.exitArena P.layout.after P.exitBank exitWidth P.resizing h.resizing,
    counter.1,counter.2.1,counter.2.2.2⟩

def SlotFront.program (P : SlotFront) (F : SlotRegisters) : Program :=
  P.padding++P.layout.retiredWindow P.exitBank F.frozen (F.counter.getLastD 0)
    P.resizing P.zero F.counter P.carry

def SlotFront.inverse (P : SlotFront) (F : SlotRegisters) : Program :=
  P.layout.retiredWindowInverse P.exitBank F.frozen (F.counter.getLastD 0)
    P.resizing P.zero F.counter P.carry++P.padding.reverse

end ECDSAAdd.Arithmetic.Paper935
