import ECDSAAdd.Arithmetic.PointDialogFlagSteps
import ECDSAAdd.Arithmetic.PointDialogCorners

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem pointDialogFinite_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (pointDialogFinite L (.some hc) cx cy)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C))=decide (dialogExceptionEnabled C) := by
    simp [equal_simp,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simp]
  have hD : (K && pointEqual R C)=D := by rw [hK]; simp only [D,dialogDouble,equal_simp]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simp]
  have hH : (E && pointEqual R (dialogExceptionPoint C))=H := by
    simp [E,H,dialogException,dialogExceptionEnabled,equal_simp]
  have h0 := dialogFlag_doubleEnable L hn R b false false false false false false false cy
  simp only [Bool.false_xor] at h0
  have h1 := dialogFlag_exceptionEnable L hn R b false false false false false false K C
  rw [hE,Bool.false_xor] at h1
  have h2 := dialogFlag_equalO L hw hn R 0 b false false false false E false K
  rw [hO,Bool.false_xor] at h2
  have h3 := dialogFlag_equalD L hw hn R C b O false false false E false K
  rw [hD,Bool.false_xor] at h3
  have h4 := dialogFlag_equalI L hw hn R (-C) b O D false false E false K
  rw [hI,Bool.false_xor] at h4
  have h5 := dialogFlag_equalH L hw hn R (dialogExceptionPoint C) b O D I false E false K
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false E H K
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G E H K
  have h7 := dialogBoundary_generic L hw hn R b (dialogFlagState L O D I G E H K) hc
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := dialogBoundary_corners L hw hn R C hC b (dialogFlagState L O D I G E H K)
    read.1 read.2.1 read.2.2.1 read.2.2.2.2.2.1
  have h9 := dialogFlag_generic L hw hn S b O D I G E H K
  have hgclear : (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H)=false := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hgclear] at h9
  have hf := dialogFlags_output b R C
  have h10 := dialogFlag_equalO L hw hn S C b O D I false E H K
  simp only [equal_simp] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := dialogFlag_equalD L hw hn S (C+C) b false D I false E H K
  have hdo : (K && pointEqual S (C+C))=D := by
    rw [hK]; simpa only [equal_simp] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := dialogFlag_equalI L hw hn S 0 b false false I false E H K
  simp only [equal_simp] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h13 := dialogFlag_equalH L hw hn S (-C) b false false false false E H K
  have heout : (E && pointEqual S (-C))=H := by
    simpa [E,H,S,dialogExceptionEnabled,equal_simp] using hf.2.2.2
  rw [heout,Bool.xor_self] at h13
  have h14 := dialogFlag_exceptionEnable L hn S b false false false false E false K C
  rw [hE,show (E ^^ (b && decide (dialogExceptionEnabled C)))=false from Bool.xor_self E] at h14
  have h15 := dialogFlag_doubleEnable L hn S b false false false false false false K cy
  rw [show (K ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self K] at h15
  have h := ((((((((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).seq h13).seq h14).seq h15
  simpa only [pointDialogFinite,List.append_assoc,dialogFlagState_zero] using h

end ECDSAAdd.Arithmetic
