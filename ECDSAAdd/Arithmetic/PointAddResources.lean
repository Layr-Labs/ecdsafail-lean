import ECDSAAdd.Arithmetic.PointAddSupport
import ECDSAAdd.Arithmetic.PointCandidateResources

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 有限常量的同程序精确资源，包含计算、输出、全部清理及测量修正支持。 -/
theorem pointAddOut_finite_resources (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (pointAddOut L (.some hc))=9295106 ∧
    measurementCount (pointAddOut L (.some hc))=6126846 ∧
    qubitCount (pointAddOut L (.some hc))=6727 := by
  have cc := pointCandidate_counts L h hn cx cy
  have cf := pointFlags_counts L h cx cy
  have co := pointOutput_counts L h (.some hc)
  refine ⟨?_,?_,?_⟩
  · simp only [pointAddOut,toffoliCount_append,cc.1.1,cc.2.1,cf.1.1,cf.2.1,co.1]
  · simp only [pointAddOut,measurementCount_append,cc.1.2,cc.2.2,cf.1.2,cf.2.2,co.2]
  · rw [qubitCount,pointAddOut_support L h cx cy hc,List.toFinset_card_of_nodup (L.usedWires_nodup h hn),L.usedWires_length h]

/-- 无穷远常量在构造期选择 513 个 CX，仅触及两个点寄存器。 -/
theorem pointAddOut_zero_resources (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (pointAddOut L 0)=0 ∧ measurementCount (pointAddOut L 0)=0 ∧
    qubitCount (pointAddOut L 0)=1026 := by
  have hh := pointCopy_counts L.input L.output (h.inputX.trans h.outputX.symm) (h.inputY.trans h.outputY.symm)
  refine ⟨hh.1,hh.2,?_⟩
  change (wires (pointCopy L.input L.output)).card=1026
  rw [pointCopy_support _ _ h.inputX h.inputY h.outputX h.outputY,
    List.toFinset_card_of_nodup (List.nodup_append'.mp hn).1]
  simp [PointAddLayout.pointWires,h.inputX,h.inputY,h.outputX,h.outputY]

end ECDSAAdd.Arithmetic
