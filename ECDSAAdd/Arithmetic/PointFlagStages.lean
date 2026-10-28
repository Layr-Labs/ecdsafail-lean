import ECDSAAdd.Arithmetic.PointAddStages

namespace ECDSAAdd.Arithmetic
open Secp256k1

def PointReady (L : PointAddLayout) (R : Point) (OF : Bool) (OX OY : Nat) (s : BasisState) : Prop :=
  Holds.holds s L.input R ∧ s L.output.finite=OF ∧ regValue L.output.x s=OX ∧
    regValue L.output.y s=OY ∧ regValue L.work s=0

theorem PointBoundary.pointFlags {L : PointAddLayout} (hn : L.wires.Nodup)
    {F EX EY D OF : Bool} {OX OY : Nat} {s : BasisState}
    (hb : PointBoundary L F EX EY D OF OX OY s) (EX' EY' G' D' : Bool) :
    PointBoundary L F EX' EY' D' OF OX OY (pointFlagState L s EX' EY' G' D') := by
  have hd := (L.flags_disjoint hn).2
  have hf : L.input.finite∉L.flags := fun hm => List.disjoint_left.mp hd hm (by simp)
  have ho : ∀ w∈PointAddLayout.pointWires L.output,w∉L.flags := by
    intro w hw hm
    exact List.disjoint_left.mp hd hm (by simp [hw])
  have hh := pointFlagState_flags L (L.flags_disjoint hn).1 s EX' EY' G' D'
  refine ⟨(pointFlagState_outside L _ _ _ _ _ _ hf).trans hb.finite,hh.1,hh.2.1,hh.2.2.2,?_,?_,?_⟩
  · exact (pointFlagState_outside L _ _ _ _ _ _ (ho _ (by simp [PointAddLayout.pointWires]))).trans hb.outFinite
  · exact (regValue_congr _ _ _ (fun w hw => pointFlagState_outside L _ _ _ _ _ _
      (ho _ (by simp [PointAddLayout.pointWires,hw])))).trans hb.outX
  · exact (regValue_congr _ _ _ (fun w hw => pointFlagState_outside L _ _ _ _ _ _
      (ho _ (by simp [PointAddLayout.pointWires,hw])))).trans hb.outY

private theorem branch_generic (R : Point) (cx : Fp) :
    (pointFinite R && !(pointFinite R && decide (pointX R=cx.val)))=pointGeneric R cx := by
  cases h : pointFinite R <;> simp [pointGeneric,h]

private theorem branch_double (R : Point) (cx cy : Fp) :
    ((pointFinite R && decide (pointX R=cx.val)) &&
      !(pointFinite R && decide (pointY R=(-cy).val)))=pointDouble R cx cy := by
  cases h : pointFinite R <;> simp [pointDouble,h]

theorem pointStage_flags (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (cx cy : Fp) (OF : Bool) (OX OY : Nat) :
    Triple (PointReady L R OF OX OY) (pointFlagsCompute L cx cy)
      (PointStage L R cx cy OF OX OY (candidateInitial (pointX R) (pointY R))) := by
  intro s m hs
  obtain ⟨hi,hof,hox,hoy,hz⟩ := hs
  have hv := point_initial_values L R s.basis hi hz
  have hf := (point_holds _ _ _).mp hi
  have hflags : ∀ w∈L.flags,s.basis w=false :=
    fun w hw => (regValue_zero _ _).mp hz w (by simp [PointAddLayout.work,hw])
  have hb : PointBoundary L (pointFinite R) false false false OF OX OY s.basis :=
    ⟨hf.1,hflags _ (by simp [PointAddLayout.flags]),hflags _ (by simp [PointAddLayout.flags]),
      hflags _ (by simp [PointAddLayout.flags]),hof,hox,hoy⟩
  have he := pointFlagsCompute_correct L h hn cx cy s m hv.2.1 hflags
  dsimp only at he
  rw [hf.1,hf.2.1,hf.2.2,branch_generic,branch_double] at he
  rw [he]
  exact ⟨rfl,hv.pointFlags hn _ _ _ _,hb.pointFlags hn _ _ _ _⟩

theorem pointStage_clearFlags (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (cx cy : Fp) (OF : Bool) (OX OY : Nat) :
    Triple (PointStage L R cx cy OF OX OY (candidateInitial (pointX R) (pointY R)))
      (pointFlagsClear L cx cy) (PointReady L R OF OX OY) := by
  intro s m hs
  obtain ⟨hv,hb⟩ := hs
  have bx : pointX R<2^L.input.x.length := by rw [h.inputX]; exact lt_trans (point_coordinates_lt R).1 (by norm_num [p])
  have by' : pointY R<2^L.input.y.length := by rw [h.inputY]; exact lt_trans (point_coordinates_lt R).2 (by norm_num [p])
  have hx := (regValue_low_iff L.input.x [L.inputXHigh] s.basis (pointX R) bx).mp (hv.1 .inputX)
  have hy := (regValue_low_iff L.input.y [L.inputYHigh] s.basis (pointY R) by').mp (hv.1 .inputY)
  have hex : s.basis L.equalX=(s.basis L.input.finite && decide (regValue L.input.x s.basis=cx.val)) := by
    rw [hb.equalX,hb.finite,hx.1]
  have hey : s.basis L.equalNegY=(s.basis L.input.finite && decide (regValue L.input.y s.basis=(-cy).val)) := by
    rw [hb.equalNegY,hb.finite,hy.1]
  have hg : s.basis L.generic=(s.basis L.input.finite && !s.basis L.equalX) := by
    rw [hv.2.2,hb.finite,hb.equalX,branch_generic]
  have hd : s.basis L.double=(s.basis L.equalX && !s.basis L.equalNegY) := by
    rw [hb.double,hb.equalX,hb.equalNegY,branch_double]
  rw [pointFlagsClear_correct L h hn cx cy s m hv.2.1 hex hey hg hd]
  have hv' := hv.pointFlags hn false false false false
  have hb' := hb.pointFlags hn false false false false
  have hh := pointFlagState_flags L (L.flags_disjoint hn).1 s.basis false false false false
  have hz : ∀ w∈L.flags,pointFlagState L s.basis false false false false w=false := by
    intro w hw
    simp only [PointAddLayout.flags,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl <;> tauto
  have hr := point_initial_recover L h R false _ hv' hb'.finite hz
  exact ⟨rfl,hr.1,hb'.outFinite,hb'.outX,hb'.outY,hr.2⟩

end ECDSAAdd.Arithmetic
