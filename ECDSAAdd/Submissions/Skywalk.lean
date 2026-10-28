import ECDSAAdd.Arithmetic.ControlledPointAddSpec
import ECDSAAdd.Arithmetic.ControlledPointResources

namespace ECDSAAdd.Submissions.Skywalk
open Arithmetic Secp256k1

/-- PR #81：压缩 Skywalk 完整受控原地点加，与现有公开入口相同。 -/
def program (L : ControlledPointLayout) (C : Point) : Program := controlledPointAdd L C

/-- 有限经典加数的静态 Toffoli 与测量指令计数。 -/
def gateCount : Nat := 2217386
def measurementCount : Nat := 1557928
/-- 真实支持集基数的已证上界；不声称等于该值或为峰值存活线路数。 -/
def qubitBound : Nat := 1899

/-- 所有合法输入点、控制位和测量记录；相位恢复，全部工作位清零。 -/
theorem correctness (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) :
    {{ L.control=b,L.point=R,L.work=0 }} program L C
    {{ L.control=b,L.point=(if b then R+C else R),L.work=0 }} :=
  controlledPointAdd_spec L hw hn b R C

theorem gate_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.toffoliCount (program L (.some hc))=gateCount :=
  (controlledPointAdd_finite_resources L hw hn cx cy hc).1

theorem measurement_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.measurementCount (program L (.some hc))=measurementCount :=
  (controlledPointAdd_finite_resources L hw hn cx cy hc).2.1

theorem qubit_count (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    ECDSAAdd.qubitCount (program L (.some hc))≤qubitBound :=
  (controlledPointAdd_finite_resources L hw hn cx cy hc).2.2

/-- 无穷远常量在构造期发出空程序。 -/
theorem zero_resources (L : ControlledPointLayout) :
    ECDSAAdd.toffoliCount (program L 0)=0 ∧
    ECDSAAdd.measurementCount (program L 0)=0 ∧
    ECDSAAdd.qubitCount (program L 0)=0 :=
  controlledPointAdd_zero_resources L

end ECDSAAdd.Submissions.Skywalk
