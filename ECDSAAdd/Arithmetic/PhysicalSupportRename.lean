import ECDSAAdd.Arithmetic.PointSquarePhysical
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem gatePhysical_rename_support (f : Wire → Wire) (p : Program)
    (hf : ∀ a∈wires p,∀ b∈wires p,f a=f b → a=b) (hp : GatePhysical p) :
    GatePhysical (renameProgram f p) := by
  induction p with
  | nil => simp [renameProgram,GatePhysical]
  | cons i p ih =>
    have first : PhysicalInstr (.gate i) := hp i (by simp)
    have sub : ∀ a∈i.wires,∀ b∈i.wires,f a=f b → a=b := by
      intro a ha b hb eq
      exact hf a (Finset.mem_union_left _ ha) b (Finset.mem_union_left _ hb) eq
    have head : GatePhysical (renameProgram f [i]) := by
      cases i with
      | X t => simp [renameProgram,renameInstr,GatePhysical,PhysicalInstr,ProperGate]
      | measureX t a b => simp [renameProgram,renameInstr,GatePhysical,PhysicalInstr]
      | CX c t =>
        have ne : f c≠f t := fun eq => first (sub c (by simp [Instr.wires]) t (by simp [Instr.wires]) eq)
        simpa [renameProgram,renameInstr,GatePhysical,PhysicalInstr,ProperGate] using ne
      | CCX a b t =>
        have na : f a≠f t := fun eq => first.1 (sub a (by simp [Instr.wires]) t (by simp [Instr.wires]) eq)
        have nb : f b≠f t := fun eq => first.2 (sub b (by simp [Instr.wires]) t (by simp [Instr.wires]) eq)
        simpa [renameProgram,renameInstr,GatePhysical,PhysicalInstr,ProperGate] using And.intro na nb
    have tail := ih (fun a ha b hb eq => hf a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb) eq)
      (fun j hj => hp j (by simp [hj]))
    change GatePhysical (renameProgram f [i] ++ renameProgram f p)
    exact (gatePhysical_append _ _).mpr ⟨head,tail⟩
end ECDSAAdd.Arithmetic
