import ECDSAAdd.Arithmetic.Paper935.BorrowGeometry
import ECDSAAdd.Arithmetic.Paper935.AuthorWalkCompiler
import ECDSAAdd.Arithmetic.Paper935.BorrowedDepthsRun
import ECDSAAdd.Arithmetic.Paper935.PaddedBranch
import ECDSAAdd.Arithmetic.Paper935.DecoderBankReady

namespace ECDSAAdd.Arithmetic.Paper935

/-- One shared borrowed pool is used for the offset comparison and then for
all five depth stages. The three retained control registers are restored by
`cleanBranchProgram`; they are not counted as newly allocated scratch. -/
structure SlotDecoder where
  paddedArena : Arena
  bank : WindowBank
  padding : Program
  borrowedArena : Arena
  work : List Wire
  layouts : List DepthLayout

/-- Compile against this slot's own post-arithmetic bank and grown history
arena. Later slots must already have been undone before this decoder runs. -/
def compileSlotDecoder (F : SlotRegisters) (Q : HistoricalSlot) : Option SlotDecoder := do
  let b := Q.slot.front.exitBank
  let (C,out,padding) ← compileBankResize Q.historyArena b b.decoderWidth
  let (D,work,layouts) ← compileBorrowedDepths C F.one F.frozen Q.history.port
    F.counter out.f.wires out.fv.wires
  pure ⟨C,out,padding,D,work,layouts⟩

/-- Before checking is enabled the stored offset is zero, so comparison with
one is harmless. Once checking starts this is precisely the stored step offset. -/
def decoderOffset (index : Nat) : Nat := max 1 (index+1-498)

def SlotDecoder.program (D : SlotDecoder) (F : SlotRegisters) (Q : HistoricalSlot)
    (p : Int) (index : Nat) : Program :=
  paddedCleanBranch D.padding D.layouts p F.frozen F.work0 F.work1
    (D.bank.fv.wires.getD 1 0) F.swap Q.history.port
    (List.zipWith ZeroBit.mk F.offset D.work) (decoderOffset index)

/-- The empty fallback only totalizes the syntax interface; realization and
correctness theorems must supply successful compilation. -/
def actualHistoryDecoder (F : SlotRegisters) (p : Int) (index : Nat)
    (Q : HistoricalSlot) : Program :=
  match compileSlotDecoder F Q with
  | none => []
  | some D => D.program F Q p index

theorem compileSlotDecoder_contract (F : SlotRegisters) (Q : HistoricalSlot)
    (D : SlotDecoder) (h : compileSlotDecoder F Q=some D) :
    compileBankResize Q.historyArena Q.slot.front.exitBank Q.slot.front.exitBank.decoderWidth=
      some (D.paddedArena,D.bank,D.padding) ∧
    compileBorrowedDepths D.paddedArena F.one F.frozen Q.history.port F.counter
      D.bank.f.wires D.bank.fv.wires=some (D.borrowedArena,D.work,D.layouts) := by
  unfold compileSlotDecoder at h
  obtain ⟨⟨C,b,p⟩,hp,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨A,w,ls⟩,hw,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨hp,hw⟩

theorem actualHistoryDecoder_of_compiled (F : SlotRegisters) (Q : HistoricalSlot)
    (D : SlotDecoder) (h : compileSlotDecoder F Q=some D) (p : Int) (index : Nat) :
    actualHistoryDecoder F p index Q=D.program F Q p index := by
  simp only [actualHistoryDecoder,h]

theorem compileSlotDecoder_pool (F : SlotRegisters) (Q : HistoricalSlot)
    (D : SlotDecoder) (h : compileSlotDecoder F Q=some D) :
    D.work.length=11 ∧ D.borrowedArena.live.card=D.paddedArena.live.card+11 ∧
    D.layouts.map (fun L => L.low.length)=[2,3,4,5,6] := by
  have hc := (compileSlotDecoder_contract F Q D h).2
  have pair := compileBorrowedDepths_contract D.paddedArena D.borrowedArena F.one F.frozen
    Q.history.port F.counter D.bank.f.wires D.bank.fv.wires D.work D.layouts hc
  exact ⟨(D.paddedArena.borrowMany_contract _ _ _ pair.1).1,
    (D.paddedArena.borrowMany_live _ _ _ pair.1).2,
    (compileDepthList_contract F.one F.frozen Q.history.port F.counter D.bank.f.wires
      D.bank.fv.wires D.work _ D.layouts pair.2).1⟩

end ECDSAAdd.Arithmetic.Paper935
