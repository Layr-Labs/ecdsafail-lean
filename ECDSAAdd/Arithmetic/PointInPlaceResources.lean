import ECDSAAdd.Arithmetic.PointInPlaceIntegration

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem ControlledPointLayout.inPlaceUsedWires_nodup (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : L.inPlaceUsedWires.Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have hh := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
  have hi := L.inPlaceOuterCore_sublist.count_le q
  simp only [inPlaceUsedWires,List.count_append] at hh hi ⊢
  omega

/-- 3939来自同一门列的支持等式，未重排原9817位分配。 -/
theorem pointInPlaceFinite_qubits (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : qubitCount (pointInPlaceFinite L C cx cy)=3939 := by
  let D := L.inPlaceDivide L.core.generic L.point.x L.point.y
  have hd := L.inPlaceDivide_widths hw L.core.generic _ _ hw.inputX hw.inputY
  have nd := L.inPlaceDivide_nodup hw hn L.core.generic (by simp [inPlaceFlags])
  have hq := (divide_qubits D hd nd).1
  rw [qubitCount,(divide_wires D hd).1,List.toFinset_card_of_nodup (D.usedWires_nodup nd)] at hq
  change (L.core.generic::L.point.x++L.point.y++L.inPlaceSlope++L.inPlaceInverse.compactCoreWires).length=3931 at hq
  simp only [List.length_append,List.length_cons,show L.point.x.length=256 from hw.inputX,
    show L.point.y.length=256 from hw.inputY,L.inPlaceSlope_length hw] at hq
  rw [qubitCount,pointInPlaceFinite_wires L hw hn,List.toFinset_card_of_nodup (L.inPlaceUsedWires_nodup hw hn)]
  simp only [inPlaceUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.length_append,List.length_cons,List.length_nil,
    show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY,L.inPlaceSlope_length hw,
    inPlaceOuterCoreWires]
  omega

end ECDSAAdd.Arithmetic
