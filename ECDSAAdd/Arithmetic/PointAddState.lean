import ECDSAAdd.Arithmetic.PointFlagProof
import ECDSAAdd.Arithmetic.PointCandidateSupport
import ECDSAAdd.Arithmetic.PointOutputProof

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 算术候选段之外保留的边界值；普通标志包含在 CandidateValues 中。 -/
structure PointBoundary (L : PointAddLayout) (F EX EY D OF : Bool) (OX OY : Nat)
    (s : BasisState) : Prop where
  finite : s L.input.finite=F
  equalX : s L.equalX=EX
  equalNegY : s L.equalNegY=EY
  double : s L.double=D
  outFinite : s L.output.finite=OF
  outX : regValue L.output.x s=OX
  outY : regValue L.output.y s=OY

def PointAddLayout.boundaryWires (L : PointAddLayout) : List Wire :=
  [L.input.finite,L.equalX,L.equalNegY,L.double]++PointAddLayout.pointWires L.output

theorem PointAddLayout.candidate_boundary_nodup (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup) :
  (L.candidateUsed++L.boundaryWires).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  have hx := (List.take_sublist 256 L.dx).count_le w
  have hy := (List.take_sublist 256 L.candidateY).count_le w
  have hdy := (List.take_sublist 256 L.dy).count_le w
  have hdelta := (List.take_sublist 256 L.delta).count_le w
  have hp := (L.candidatePool_sublist h).count_le w
  simp only [PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
    PointAddLayout.extendedX,PointAddLayout.extendedY,
    PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

theorem PointAddLayout.candidate_boundary_disjoint (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup) :
    L.candidateUsed.Disjoint L.boundaryWires :=
  (List.nodup_append'.mp (L.candidate_boundary_nodup h hn)).2.2

theorem PointBoundary.congr {L : PointAddLayout} {F EX EY D OF : Bool} {OX OY : Nat}
    {s t : BasisState} (h : PointBoundary L F EX EY D OF OX OY s)
    (he : ∀ w∈L.boundaryWires,t w=s w) : PointBoundary L F EX EY D OF OX OY t := by
  have hf := he L.input.finite (by simp [PointAddLayout.boundaryWires])
  have hx := he L.equalX (by simp [PointAddLayout.boundaryWires])
  have hy := he L.equalNegY (by simp [PointAddLayout.boundaryWires])
  have hd := he L.double (by simp [PointAddLayout.boundaryWires])
  have ho := he L.output.finite (by simp [PointAddLayout.boundaryWires,PointAddLayout.pointWires])
  refine ⟨hf.trans h.finite,hx.trans h.equalX,hy.trans h.equalNegY,hd.trans h.double,
    ho.trans h.outFinite,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => he w (by simp [PointAddLayout.boundaryWires,PointAddLayout.pointWires,hw]))).trans h.outX
  · exact (regValue_congr _ _ _ (fun w hw => he w (by simp [PointAddLayout.boundaryWires,PointAddLayout.pointWires,hw]))).trans h.outY

theorem pointCandidate_frame (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (c : Program) (hs : wires c=L.candidateUsed.toFinset)
    (F EX EY D OF : Bool) (OX OY : Nat) (s : State) (m : List Bool)
    (hb : PointBoundary L F EX EY D OF OX OY s.basis) :
    PointBoundary L F EX EY D OF OX OY (run c m s).basis := by
  apply hb.congr
  intro w hw
  apply run_preserves_outside
  rw [hs,List.mem_toFinset]
  exact fun hc => List.disjoint_left.mp (L.candidate_boundary_disjoint h hn) hc hw

/-- 点输入和工作区全零给出候选段的初态，包含输入的两个扩展最高位。 -/
theorem point_initial_values (L : PointAddLayout) (R : Point) (s : BasisState)
    (hi : Holds.holds s L.input R) (hz : regValue L.work s=0) :
    CandidateValues L (candidateInitial (pointX R) (pointY R)) false s := by
  obtain ⟨_,hx,hy⟩ := (point_holds _ _ _).mp hi
  have hz' := (regValue_zero _ _).mp hz
  have hX : s L.inputXHigh=false := hz' _ (by simp [PointAddLayout.work])
  have hY : s L.inputYHigh=false := hz' _ (by simp [PointAddLayout.work])
  constructor
  · intro f
    cases f
    · change regValue (L.input.x++[L.inputXHigh]) s=pointX R
      rw [regValue_append,hx]
      simp [regValue,hX]
    · change regValue (L.input.y++[L.inputYHigh]) s=pointY R
      rw [regValue_append,hy]
      simp [regValue,hY]
    all_goals
      change regValue _ s=0
      apply (regValue_zero _ _).mpr
      intro w hw
      exact hz' w (by simp_all [PointAddLayout.work,PointAddLayout.words,PointAddLayout.reg])
  · exact ⟨(regValue_zero _ _).mpr (fun w hw => hz' w (by simp [PointAddLayout.work,hw])),
      hz' _ (by simp [PointAddLayout.work,PointAddLayout.flags])⟩

theorem point_initial_recover (L : PointAddLayout) (h : L.Widths) (R : Point) (G : Bool) (s : BasisState)
    (hv : CandidateValues L (candidateInitial (pointX R) (pointY R)) G s)
    (hf : s L.input.finite=pointFinite R) (hz : ∀ w∈L.flags,s w=false) :
    Holds.holds s L.input R ∧ regValue L.work s=0 := by
  have bx : pointX R<2^L.input.x.length := by rw [h.inputX]; exact lt_trans (point_coordinates_lt R).1 (by norm_num [p])
  have by' : pointY R<2^L.input.y.length := by rw [h.inputY]; exact lt_trans (point_coordinates_lt R).2 (by norm_num [p])
  have hx := (regValue_low_iff L.input.x [L.inputXHigh] s (pointX R) bx).mp (hv.1 .inputX)
  have hy := (regValue_low_iff L.input.y [L.inputYHigh] s (pointY R) by').mp (hv.1 .inputY)
  refine ⟨(point_holds _ _ _).mpr ⟨hf,hx.1,hy.1⟩,?_⟩
  have hX : s L.inputXHigh=false := (regValue_zero _ _).mp hx.2 _ (by simp)
  have hY : s L.inputYHigh=false := (regValue_zero _ _).mp hy.2 _ (by simp)
  have hflags : regValue L.flags s=0 := (regValue_zero _ _).mpr hz
  have hvals := hv.1
  simp only [PointAddLayout.work,PointAddLayout.words,List.flatten_cons,List.flatten_nil,List.append_nil,
    regValue_append,hflags,hv.2.1,Nat.mul_zero,Nat.add_zero]
  have hdx := hvals .dx; have hdy := hvals .dy; have hs := hvals .slope
  have hsq := hvals .square; have ho := hvals .offset; have hxg := hvals .x
  have hd := hvals .delta; have hp := hvals .product; have hyg := hvals .y
  have hk := hvals .constant; have hdiv := hvals .divisor; have hinv := hvals .inverse
  simp only [PointAddLayout.reg,candidateInitial] at hdx hdy hs hsq ho hxg hd hp hyg hk hdiv hinv
  rw [hdx,hdy,hs,hsq,ho,hxg,hd,hp,hyg,hk,hdiv,hinv]
  simp [regValue,hX,hY]

end ECDSAAdd.Arithmetic
