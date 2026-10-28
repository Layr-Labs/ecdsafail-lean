import ECDSAAdd.Arithmetic.ControlledPointStages

namespace ECDSAAdd.Arithmetic
open Secp256k1

def ControlledPointReady (L : ControlledPointLayout) (b : Bool) (R : Point)
    (OF : Bool) (OX OY : Nat) (s : BasisState) : Prop :=
  PointReady L.core R OF OX OY s ∧ PointControl L b s

/-- 任意目标位串的受控 XOR 引理；原地程序只对有限常量调用此辅助程序。 -/
theorem controlledPointAddOut_finite_ready (L : ControlledPointLayout) (h : L.Widths)
    (hn : L.wires.Nodup) (b : Bool) (R : Point) (cx cy : Fp)
    (hc : curve.toAffine.Nonsingular cx cy) (OF : Bool) (OX OY : Nat) :
    let C : Point := .some hc
    Triple (ControlledPointReady L b R OF OX OY) (controlledPointAddOut L C)
      (ControlledPointReady L b R (OF^^(b&&pointFinite (R+C)))
        (OX^^^(if b then pointX (R+C) else 0)) (OY^^^(if b then pointY (R+C) else 0))) := by
  dsimp only
  have hnc := L.core_nodup hn
  have hb := point_coordinates_lt R
  have hg : pointGeneric R cx=true → pointX R≠cx.val := fun hh => (pointGeneric_domain R cx hh).2
  have hs := pointCandidate_support L.core h cx cy
  have hf := pointFlags_support L.core h cx cy
  have hcompute := pointCandidate_compute_spec L.core h hnc (pointGeneric R cx) (pointX R) (pointY R) cx cy hb.1 hb.2 hg
  have hclear := pointCandidate_clear_spec L.core h hnc (pointGeneric R cx) (pointX R) (pointY R) cx cy hb.1 hb.2 hg
  have h1 := pointControl_frame L hn b (pointStage_flags L.core h hnc R cx cy OF OX OY)
    (by rw [hf.1]; exact L.flags_subset)
  have h2 := pointControl_frame L hn b (pointStage_candidate L.core h hnc R cx cy OF OX OY _ _ _ hs.1 hcompute)
    (by rw [hs.1]; exact L.candidate_subset h)
  have h3 := controlledPointStage_output L h hn b R cx cy hc OF OX OY
  have h4 := pointControl_frame L hn b (pointStage_candidate L.core h hnc R cx cy
    (OF^^(b&&pointFinite (R+.some hc))) (OX^^^(if b then pointX (R+.some hc) else 0))
    (OY^^^(if b then pointY (R+.some hc) else 0)) _ _ _ hs.2 hclear)
    (by rw [hs.2]; exact L.candidate_subset h)
  have h5 := pointControl_frame L hn b (pointStage_clearFlags L.core h hnc R cx cy
    (OF^^(b&&pointFinite (R+.some hc))) (OX^^^(if b then pointX (R+.some hc) else 0))
    (OY^^^(if b then pointY (R+.some hc) else 0)))
    (by rw [hf.2]; exact L.flags_subset)
  exact (((h1.seq h2).seq h3).seq h4).seq h5

end ECDSAAdd.Arithmetic
