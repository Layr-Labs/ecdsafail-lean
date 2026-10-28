import ECDSAAdd.Arithmetic.SquareSubPool
import ECDSAAdd.Arithmetic.PointInPlaceLayoutProof

namespace ECDSAAdd.Arithmetic
namespace ControlledPointLayout

/-- 平方专用视图复用 P 的前2217位，不分配新的量子线。 -/
def inPlaceKaratsuba (L : ControlledPointLayout) : SquareSubLayout :=
  SquareSubLayout.fromPool (L.inPlaceSlope.take 256) L.point.x L.inPlaceBorrow

theorem inPlaceKaratsuba_widths (L : ControlledPointLayout) (hw : L.Widths) :
    L.inPlaceKaratsuba.Widths :=
  SquareSubLayout.fromPool_widths _ _ _ (by simp [L.inPlaceSlope_length hw]) hw.inputX
    (by rw [L.inPlaceBorrow_length hw]; omega)

theorem inPlaceKaratsuba_work (L : ControlledPointLayout) (hw : L.Widths) :
    L.inPlaceKaratsuba.work=L.inPlaceBorrow.take 2217 :=
  SquareSubLayout.fromPool_work _ _ _ (by rw [L.inPlaceBorrow_length hw]; omega)

theorem inPlaceKaratsuba_work_subset (L : ControlledPointLayout) (hw : L.Widths) :
    L.inPlaceKaratsuba.work⊆L.inPlaceBorrow := by
  rw [L.inPlaceKaratsuba_work hw]
  exact List.take_subset _ _

theorem inPlaceKaratsuba_x (L : ControlledPointLayout) (hw : L.Widths) :
    L.inPlaceKaratsuba.x=L.inPlaceSlope := by
  change L.inPlaceSlope.take 256=L.inPlaceSlope
  rw [←L.inPlaceSlope_length hw,List.take_length]

theorem inPlaceKaratsuba_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    L.inPlaceKaratsuba.wires.Nodup := by
  apply SquareSubLayout.fromPool_nodup _ _ _ (by rw [L.inPlaceBorrow_length hw]; omega)
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
  have hs := (List.take_sublist 256 L.inPlaceSlope).count_le q
  have hb := L.inPlaceBorrow_count q
  simp only [PointAddLayout.pointWires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

end ControlledPointLayout
end ECDSAAdd.Arithmetic
