import ECDSAAdd.Arithmetic.FixedFieldPhysical
import ECDSAAdd.Arithmetic.TranscriptSelectFlag
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem transcriptWindow_physical (b source flag : Wire) (constant : Bool) (body : Program)
    (hb : b≠flag) (hs : source≠flag) (hp : GatePhysical body) :
    GatePhysical (transcriptSelectWindow b source flag constant body) := by
  have comp : GatePhysical (transcriptSelectCompute b source flag constant) := by
    cases constant <;> simp [transcriptSelectCompute,GatePhysical,PhysicalInstr,ProperGate,hb,hs]
  have expose : GatePhysical (transcriptSelectExpose flag constant) := by
    cases constant <;> simp [transcriptSelectExpose,GatePhysical,PhysicalInstr,ProperGate]
  have erase : GatePhysical (transcriptSelectErase b source flag constant) := by
    cases constant <;> simp [transcriptSelectErase,GatePhysical,PhysicalInstr]
  simp only [transcriptSelectWindow,gatePhysical_append]
  exact ⟨⟨⟨⟨comp,expose⟩,hp⟩,expose⟩,erase⟩

theorem fixedFieldSwap_physical : GatePhysical
    (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y) := by
  apply physicalGateCheck_correct
  decide +kernel

theorem fixedFieldBodies_physical :
    GatePhysical (OffsetBorrowedCanonical.body id 2409 2410) ∧
    GatePhysical (OffsetBorrowedInverseCanonical.body id 2409 2410) := by
  have x : GatePhysical [.X 2409] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  simp only [OffsetBorrowedCanonical.body,OffsetBorrowedInverseCanonical.body,
    OffsetBorrowedInverseCanonical.double,gatePhysical_append]
  exact ⟨⟨⟨⟨x,fixedForwardField_physical⟩,x⟩,fixedFieldSwap_physical⟩,
    ⟨fixedFieldSwap_physical,⟨⟨x,fixedInverseField_physical⟩,x⟩⟩⟩

theorem fixedSelectedCells_physical (i : Nat) (hi : i<512) (ig is : Bool) :
    GatePhysical (OffsetBorrowedCanonical.cell id 2400 i (1028+i) 2409 2410 ig is) ∧
    GatePhysical (OffsetBorrowedInverseCanonical.cell id 2400 i (1028+i) 2409 2410 ig is) := by
  have outerB : (2400 : Wire) ≠ 2409 := by decide
  have outerS : (i : Wire) ≠ 2409 := by omega
  have innerB : (2400 : Wire) ≠ 2410 := by decide
  have innerS : (1028+i : Wire) ≠ 2410 := by
    exact Nat.ne_of_lt ((Nat.add_lt_add_left hi 1028).trans (by decide))
  exact ⟨transcriptWindow_physical _ _ _ _ _ outerB outerS
    (transcriptWindow_physical _ _ _ _ _ innerB innerS fixedFieldBodies_physical.1),
    transcriptWindow_physical _ _ _ _ _ outerB outerS
    (transcriptWindow_physical _ _ _ _ _ innerB innerS fixedFieldBodies_physical.2)⟩
end ECDSAAdd.Arithmetic
