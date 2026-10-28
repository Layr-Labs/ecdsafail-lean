import ECDSAAdd.Arithmetic.Paper935.CheckedPublicSlot
import ECDSAAdd.Arithmetic.Paper935.WindowSlotMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- Classical input meaning of the actual persistent metadata addresses. -/
structure SlotRegisters.Values (F : SlotRegisters) (s : BasisState) (old : PinState) : Prop where
  one : s F.one=true
  frozen : s F.frozen=old.frozen
  parity : s F.parity=false
  active : s F.active=false
  swap : s F.swap=false
  work0 : s F.work0=false
  work1 : s F.work1=false
  counter : signedRegValue F.counter s=old.rows.z
  offset : regValue F.offset s=old.offset

theorem SlotRegisters.Values.frame (F : SlotRegisters) (s t : BasisState) (old : PinState)
    (h : F.Values s old) (keep : ∀ q∈F.wires,t q=s q) : F.Values t old := by
  constructor
  · rw [keep F.one (by simp [SlotRegisters.wires])]; exact h.one
  · rw [keep F.frozen (by simp [SlotRegisters.wires])]; exact h.frozen
  · rw [keep F.parity (by simp [SlotRegisters.wires])]; exact h.parity
  · rw [keep F.active (by simp [SlotRegisters.wires])]; exact h.active
  · rw [keep F.swap (by simp [SlotRegisters.wires])]; exact h.swap
  · rw [keep F.work0 (by simp [SlotRegisters.wires])]; exact h.work0
  · rw [keep F.work1 (by simp [SlotRegisters.wires])]; exact h.work1
  · unfold signedRegValue
    rw [regValue_congr F.counter t s (by intro q hq; exact keep q (by simp [SlotRegisters.wires,hq]))]
    exact h.counter
  · rw [regValue_congr F.offset t s (by intro q hq; exact keep q (by simp [SlotRegisters.wires,hq]))]
    exact h.offset

/-- Actual sign-padding preserves every persistent metadata value and
supplies owned encoded rows to the routed stage. -/
theorem SlotFront.Compiled.padding_state (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (h : P.Compiled A b addWidth exitWidth F)
    (old : PinState) (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis old.rows) (fit : addWidth.Fits old.rows)
    (values : F.Values s.basis old) (owned : F.wires.toFinset⊆A.live)
    (away : List.Disjoint F.wires (b.rows.flatMap WindowRow.wires)) :
    let t := run P.padding m s
    P.addArena.Ready t.basis ∧ P.layout.before.Encodes t.basis old.rows ∧ F.Values t.basis old ∧
    rowsOwned P.addArena P.layout.before.rows ∧ F.wires.toFinset⊆P.addArena.live := by
  have plan := compileBankResize_contract A P.addArena b P.addBank addWidth P.padding h.padding
  have resized := b.resize_correct P.addBank addWidth A P.addArena P.padding plan s m old.rows ready rows fit
  have layout := compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.addBank P.layout h.routed
  have keep (q : Wire) (hq : q∈F.wires) := resized.2.2.2.2 q
    (owned (List.mem_toFinset.mpr hq)) (List.disjoint_left.mp away hq)
  dsimp only
  rw [layout.2.1]
  exact ⟨resized.2.1,resized.2.2.1,values.frame F s.basis _ old (fun q hq => (keep q hq).2),
    resized.1,fun q hq => (keep q (List.mem_toFinset.mp hq)).1⟩

end ECDSAAdd.Arithmetic.Paper935
