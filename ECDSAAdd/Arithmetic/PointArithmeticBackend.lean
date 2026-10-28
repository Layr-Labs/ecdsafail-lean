import ECDSAAdd.Arithmetic.MappedCompressedPointArithmetic

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- A replacement for the point dialogue's two in-place arithmetic calls.
`false` divides and `true` multiplies. Nonzero input is required only on
an enabled call; the disabled case includes zero. All record streams and
incoming phases are covered. The declared pool is clean at both boundaries.
This interface is for `Program`; a `RecordedProgram` needs its own bridge. -/
structure PointArithmeticBackend where
  program : ControlledPointLayout → Bool → Program
  correct : ∀ (L : ControlledPointLayout), L.Widths → L.wires.Nodup →
    ∀ (multiply : Bool) (X Y : Nat) (B : Bool), X<p → (B=true → X≠0) → Y<p →
    ∀ (s : State) (m : List Bool), s.basis L.core.generic=B →
    regValue L.point.x s.basis=X → regValue L.point.y s.basis=Y →
    regValue L.dialogPool s.basis=0 →
    (run (program L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (program L multiply) m s).basis=
      (if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y) ∧
    ∀ q,q∉L.point.y → (run (program L multiply) m s).basis q=s.basis q
  support : ∀ (L : ControlledPointLayout), L.Widths → L.wires.Nodup →
    ∀ multiply, wires (program L multiply) ⊆ L.dialogUsedWires.toFinset

namespace PointArithmeticBackend

theorem shared_subset (L : ControlledPointLayout) (hw : L.Widths) :
    CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L ⊆ L.dialogUsedWires := by
  intro q hq
  rcases List.mem_append.mp hq with res|pool
  · exact List.mem_append_left _ res
  · have mem : q∈L.dialogPool := by
      simp only [CompressedPointSquare.sharedPool,List.mem_append] at pool
      rcases pool with (pool|pool)|pool
      all_goals
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp pool
        simp only [List.mem_range'_1] at hi
        change L.core.poolWire i∈L.core.pool.take 2613
        rw [←L.core.pool_prefix hw 2613 (by omega)]
        exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1];omega,rfl⟩
    exact List.mem_append_right _ mem

/-- The existing exact Skywalk is a concrete witness for the interface. -/
def skywalk : PointArithmeticBackend where
  program := MappedCompressed.pointCompressedArithmetic
  correct := MappedCompressed.pointCompressedArithmetic_correct
  support L hw _ multiply := by
    apply (MappedCompressed.pointCompressedArithmetic_support L hw multiply).trans
    intro q hq
    exact List.mem_toFinset.mpr (shared_subset L hw (List.mem_toFinset.mp hq))

end PointArithmeticBackend
end ECDSAAdd.Arithmetic
