import ECDSAAdd.Arithmetic.ValueWalkPointResources

namespace ECDSAAdd.Submissions.ValueWalk
open Arithmetic Secp256k1

/-- PR #80：固定512轮、已证位宽收窄的完整受控原地点加。 -/
def program (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      valueWalkPointDialogFinite L C cx cy

/-- 有限经典加数的静态成本；gate 指 Toffoli，线路数为精确支持基数。 -/
def gateCount : Nat := 6286806
def measurementCount : Nat := 3779274
def qubitCount : Nat := 3134

/-- 所有合法输入点、控制位和测量记录；相位恢复，全部工作位清零。 -/
theorem correctness (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) :
    {{ L.control=b,L.point=R,L.work=0 }} program L C
    {{ L.control=b,L.point=(if b then R+C else R),L.work=0 }} := by
  cases C with
  | zero =>
    intro s m hs
    change s.phase=s.phase ∧ _
    refine ⟨rfl,?_⟩
    change ((Holds.holds s.basis L.control b ∧ Holds.holds s.basis L.point (if b then R+0 else R)) ∧ _)
    simpa only [add_zero,ite_self] using hs
  | some hp => exact valueWalkPointDialogFinite_full_spec L hw hn R hp b

theorem gate_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.toffoliCount (program L (.some hc))=gateCount :=
  (valueWalkPointDialogFinite_counts L hw hn (.some hc) cx cy).1

theorem measurement_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.measurementCount (program L (.some hc))=measurementCount :=
  (valueWalkPointDialogFinite_counts L hw hn (.some hc) cx cy).2

theorem qubit_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.qubitCount (program L (.some hc))=qubitCount :=
  valueWalkPointDialogFinite_qubits L hw hn (.some hc) cx cy

/-- 无穷远常量在构造期发出空程序。 -/
theorem zero_resources (L : ControlledPointLayout) :
    ECDSAAdd.toffoliCount (program L 0)=0 ∧
    ECDSAAdd.measurementCount (program L 0)=0 ∧
    ECDSAAdd.qubitCount (program L 0)=0 := by
  simp [program,ECDSAAdd.toffoliCount,ECDSAAdd.measurementCount,ECDSAAdd.qubitCount,wires]

end ECDSAAdd.Submissions.ValueWalk
