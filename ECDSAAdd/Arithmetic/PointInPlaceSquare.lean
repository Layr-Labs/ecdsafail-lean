import ECDSAAdd.Arithmetic.PointKaratsubaLayout
import ECDSAAdd.Arithmetic.SquareSubSpec

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 专用平方只改变当前 x；整个 P 与斜率输入均恢复。 -/
theorem pointInPlaceSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (A X : Nat) (hX : X<p) (s : State) (m : List Bool)
    (ha : regValue L.inPlaceSlope s.basis=A) (hx : regValue L.point.x s.basis=X)
    (hc : regValue L.inPlaceBorrow s.basis=0) :
    (run (squareSub L.inPlaceKaratsuba) m s).phase=s.phase ∧
      regValue L.point.x (run (squareSub L.inPlaceKaratsuba) m s).basis=(X+p-(A*A)%p)%p ∧
      ∀q,q∉L.point.x → (run (squareSub L.inPlaceKaratsuba) m s).basis q=s.basis q := by
  have hp : SquareReduction.p=p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have ha' : regValue L.inPlaceKaratsuba.x s.basis=A := by rw [L.inPlaceKaratsuba_x hw]; exact ha
  have hx' : regValue L.inPlaceKaratsuba.out s.basis=X := hx
  have hz : regValue L.inPlaceKaratsuba.work s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    exact (regValue_zero _ _).mp hc q (L.inPlaceKaratsuba_work_subset hw hq)
  have spec := squareSub_spec L.inPlaceKaratsuba (L.inPlaceKaratsuba_widths hw)
    (L.inPlaceKaratsuba_nodup hw hn) A X (by simpa only [hp] using hX)
    s m ⟨⟨ha',hx'⟩,hz⟩
  refine ⟨spec.1,?_,?_⟩
  · simpa only [hp,pow_two] using spec.2.1.2
  · intro q hq
    exact squareSub_frame L.inPlaceKaratsuba (L.inPlaceKaratsuba_widths hw)
      (L.inPlaceKaratsuba_nodup hw hn) A X (by simpa only [hp] using hX)
      s m ha' hx' hz q hq

end ECDSAAdd.Arithmetic
