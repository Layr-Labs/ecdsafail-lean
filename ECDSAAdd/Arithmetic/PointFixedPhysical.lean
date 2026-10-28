import ECDSAAdd.Arithmetic.PointFixedPrimitivesPhysical
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Arithmetic.ConditionalPointDialogSpec
import ECDSAAdd.Arithmetic.PointDialogFlagSteps
namespace ECDSAAdd.Arithmetic
open RecordedQuantum Secp256k1 ControlledPointLayout

theorem pointDialogConstantAdd_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    GatePhysical (pointDialogConstantAdd L r k) :=
  compactRecoveryConstant_physical _ _ _ _ _ (L.recoveryConstant_nodup hw hn r hr)

theorem pointRecoveryStage_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) : GatePhysical (pointRecoveryStage L cx cy) := by
  simp only [pointRecoveryStage,gatePhysical_append]
  exact ⟨⟨CompactRecoveryNegateLayout.reflection_physical _ _ _ (L.recoveryNegate_nodup hw hn),
    pointDialogConstantAdd_physical L hw hn _ (Or.inl rfl) _⟩,
    pointDialogConstantAdd_physical L hw hn _ (Or.inr rfl) _⟩

theorem dialogEqual_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags)
    (hct : c≠t) (k : Nat) : GatePhysical (equalConstant c t L.dialogPointZero k) := by
  apply equalConstant_physical
  have h := L.dialogPointZero_nodup hn c t hct hc ht
  have len : (PointAddLayout.pointWires L.point).length = (L.dialogPool.take 513).length := by
    have hx : L.point.x.length = 256 := hw.inputX
    have hy : L.point.y.length = 256 := hw.inputY
    simp [PointAddLayout.pointWires,hx,hy,L.dialogPool_length hw]
  exact ((zeroPorts_perm _ _ len).cons t |>.cons c).nodup_iff.mpr h

theorem pointDialogFlags_physical (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (cy : Fp) (C : Point) :
    GatePhysical (pointInPlaceDoubleEnable L cy) ∧
    GatePhysical (pointDialogExceptionEnable L C) ∧
    GatePhysical (pointDialogGenericFlag L) := by
  have h := dialogFlag_separation (L:=L) hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at h
  constructor
  · unfold pointInPlaceDoubleEnable
    split <;> simp_all [GatePhysical,PhysicalInstr,ProperGate]
  constructor
  · unfold pointDialogExceptionEnable
    split <;> simp_all [GatePhysical,PhysicalInstr,ProperGate]
  · simp_all [pointDialogGenericFlag,pointInPlaceGenericFlag,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

theorem pointDialogCorners_physical (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (C : Point) : GatePhysical (pointDialogCorners L C) := by
  have away (c : Wire) (hc : c ∈ L.inPlaceFlags) : c ∉ PointAddLayout.pointWires L.point := by
    intro hm
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) c
    have hf := List.count_pos_iff.mpr hc
    have hp := List.count_pos_iff.mpr hm
    simp only [dialogUsedWires,List.count_append,List.count_cons] at h
    omega
  have all (c : Wire) (hc : c ∈ L.inPlaceFlags) (D : Point) : GatePhysical (maskedPointConstant c L.point D) :=
    maskedPointConstant_physical c L.point D (away c hc)
  simp only [pointDialogCorners,pointInPlaceCorners,gatePhysical_append]
  repeat constructor
  all_goals apply all _ (by simp [inPlaceFlags])

end ECDSAAdd.Arithmetic
