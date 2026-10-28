import ECDSAAdd.Arithmetic.PointInPlaceFlagSteps

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 有限常量的完整原地点加：包括输入分类、普通分支、角落写回和输出清标志。 -/
theorem pointInPlaceFinite_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointInPlaceBoundary L R b (fun _ => false)) (pointInPlaceFinite L (.some hc) cx cy)
      (PointInPlaceBoundary L (if b then R+.some hc else R) b (fun _ => false)) := by
  let C : Point := .some hc
  let O := inPlaceInfinity b R
  let D := inPlaceDouble b R C
  let I := inPlaceInversePoint b R C
  let G := inPlaceOrdinary b R C
  let H := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hH : H=(b && !pointEqual C (-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [H,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq]
    have hd := doubling_enabled_iff hc
    have he : pointEqual C (-C)=false ↔ C≠-C := by
      rw [Bool.eq_false_iff]
      exact not_congr (pointEqual_true_iff C (-C))
    exact and_congr_right (fun _ => hd.trans he.symm)
  have hD : (H && pointEqual R C)=D := by rw [hH]; rfl
  have h0 := pointFlag_doubleEnable L hw hn R b false false false false false cy
  simp only [Bool.false_xor] at h0
  have h1 := pointFlag_equalO L hw hn R 0 b false false false false H
  simp only [Bool.false_xor] at h1
  have h2 := pointFlag_equalD L hw hn R C b O false false false H
  simp only [Bool.false_xor,hD] at h2
  have h3 := pointFlag_equalI L hw hn R (-C) b O D false false H
  simp only [Bool.false_xor] at h3
  have h4 := pointFlag_generic L hw hn R b O D I false H
  simp only [Bool.false_xor] at h4
  have hread := inPlaceFlagState_read L hw hn O D I G H
  have h5 := pointBoundary_generic L hw hn R b (inPlaceFlagState L O D I G H) hc
    hread.2.2.2.2.1 hread.2.2.2.2.2.1
    (fun hg => (inPlaceOrdinary_true b R C hC).mp (hread.2.2.2.1.symm.trans hg) |>.2)
  rw [hread.2.2.2.1] at h5
  have h6 := pointBoundary_corners L hw hn R C hC b (inPlaceFlagState L O D I G H)
    hread.1 hread.2.1 hread.2.2.1
  have h7 := pointFlag_generic L hw hn S b O D I G H
  have hgclear : ((((G ^^ b) ^^ O) ^^ D) ^^ I)=false := by
    dsimp only [G,inPlaceOrdinary,O,D,I]
    generalize inPlaceInfinity b R=o, inPlaceDouble b R C=d, inPlaceInversePoint b R C=i
    cases b <;> cases o <;> cases d <;> cases i <;> rfl
  rw [hgclear] at h7
  have hf := inPlaceFlags_output b R C
  have h8 := pointFlag_equalO L hw hn S C b O D I false H
  rw [hf.1,Bool.xor_self] at h8
  have h9 := pointFlag_equalD L hw hn S (C+C) b false D I false H
  have hdo : (H && pointEqual S (C+C))=D := by rw [hH]; exact hf.2.1
  rw [hdo,Bool.xor_self] at h9
  have h10 := pointFlag_equalI L hw hn S 0 b false false I false H
  rw [hf.2.2,Bool.xor_self] at h10
  have h11 := pointFlag_doubleEnable L hw hn S b false false false false H cy
  simp only [show (H ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self H] at h11
  have hh := (((((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11)
  simpa only [pointInPlaceFinite,List.append_assoc,inPlaceFlagState_zero] using hh

end ECDSAAdd.Arithmetic
