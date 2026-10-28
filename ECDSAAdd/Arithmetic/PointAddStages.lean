import ECDSAAdd.Arithmetic.PointAddFrames

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 输出前后相同的分类与候选寄存器状态。 -/
def PointStage (L : PointAddLayout) (R : Point) (cx cy : Fp) (OF : Bool) (OX OY : Nat)
    (v : CandidateField → Nat) (s : BasisState) : Prop :=
  CandidateValues L v (pointGeneric R cx) s ∧
  PointBoundary L (pointFinite R)
    (pointFinite R && decide (pointX R=cx.val))
    (pointFinite R && decide (pointY R=(-cy).val)) (pointDouble R cx cy) OF OX OY s

theorem pointStage_candidate (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (cx cy : Fp) (OF : Bool) (OX OY : Nat)
    (v v' : CandidateField → Nat) (c : Program) (hs : wires c=L.candidateUsed.toFinset)
    (hc : Triple (CandidateValues L v (pointGeneric R cx)) c
      (CandidateValues L v' (pointGeneric R cx))) :
    Triple (PointStage L R cx cy OF OX OY v) c (PointStage L R cx cy OF OX OY v') := by
  intro s m hh
  obtain ⟨hp,hv⟩ := hc s m hh.1
  exact ⟨hp,hv,pointCandidate_frame L h hn c hs _ _ _ _ _ _ _ s m hh.2⟩

theorem pointStage_output (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy)
    (OF : Bool) (OX OY : Nat) :
    let C : Point := .some hc
    let V := candidateResult (pointGeneric R cx) (pointX R) (pointY R) cx.val cy.val
    Triple (PointStage L R cx cy OF OX OY V) (pointOutput L C)
      (PointStage L R cx cy (OF^^pointFinite (R+C)) (OX^^^pointX (R+C)) (OY^^^pointY (R+C)) V) := by
  dsimp only
  intro s m hs
  obtain ⟨hv,hb⟩ := hs
  have hh := pointOutput_correct L h hn (.some hc) s m
  have hx := h.words L.candidateX (by simp [PointAddLayout.words])
  have hy := h.words L.candidateY (by simp [PointAddLayout.words])
  have hbnd := candidateResult_xy_lt (pointGeneric R cx) (pointX R) (pointY R) cx cy
    (point_coordinates_lt R).1 (point_coordinates_lt R).2
  have hlow (r : List Wire) (hr : r.length=257) (V : Nat) (hV : V<p)
      (hv : regValue r s.basis=V) : regValue (r.take 256) s.basis=V := by
    have ht := regValue_low_iff (r.take 256) (r.drop 256) s.basis V
      (by simp only [List.length_take,hr]; exact lt_trans hV (by norm_num [p]))
    rw [List.take_append_drop] at ht
    exact (ht.mp hv).1
  have hX := hlow L.candidateX hx _ hbnd.1 (hv.1 .x)
  have hY := hlow L.candidateY hy _ hbnd.2 (hv.1 .y)
  rw [hX,hY,hv.2.2,hb.finite,hb.double] at hh
  have he := point_classification_xor R cx cy hc
  dsimp only at he
  have heF := congrArg Prod.fst he
  have heX := congrArg (fun t => t.2.1) he
  have heY := congrArg (fun t => t.2.2) he
  dsimp only at heF heX heY
  rw [heF,heX,heY] at hh
  exact ⟨hh.phase,hv.pointOutput hn hh,hb.pointOutput hn hh⟩

end ECDSAAdd.Arithmetic
