import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.MeasuredStreamedPhysical
import ECDSAAdd.Arithmetic.CompressedPointSquarePool
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem gatePhysical_rename (f : Wire → Wire) (hf : Function.Injective f)
    (p : Program) (hp : GatePhysical p) : GatePhysical (renameProgram f p) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have h := hp j hj
  cases j <;> simp_all [renameInstr,PhysicalInstr,ProperGate, hf.eq_iff]

theorem pointMeasuredSquareCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (pointMeasuredSquareCandidate L) := by
  apply L.dialogStreamedSquareWide.measuredProgram_physical (L.dialogStreamedSquareWide_widths hw)
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢; omega

theorem CompressedPointSquare.computableProgram_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (computableProgram L) := by
  rw [computableProgram_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact pointMeasuredSquareCandidate_physical L hw hn

end ECDSAAdd.Arithmetic
