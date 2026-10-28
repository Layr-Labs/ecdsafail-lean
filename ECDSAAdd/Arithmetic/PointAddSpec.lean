import ECDSAAdd.Arithmetic.PointFlagStages

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem pointAddOut_finite_ready (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy)
    (OF : Bool) (OX OY : Nat) :
    let C : Point := .some hc
    Triple (PointReady L R OF OX OY) (pointAddOut L C)
      (PointReady L R (OF^^pointFinite (R+C)) (OX^^^pointX (R+C)) (OY^^^pointY (R+C))) := by
  dsimp only
  have hb := point_coordinates_lt R
  have hg : pointGeneric R cx=true → pointX R≠cx.val := fun hh => (pointGeneric_domain R cx hh).2
  have hs := pointCandidate_support L h cx cy
  have hcompute := pointCandidate_compute_spec L h hn (pointGeneric R cx) (pointX R) (pointY R) cx cy hb.1 hb.2 hg
  have hclear := pointCandidate_clear_spec L h hn (pointGeneric R cx) (pointX R) (pointY R) cx cy hb.1 hb.2 hg
  have h1 := pointStage_flags L h hn R cx cy OF OX OY
  have h2 := pointStage_candidate L h hn R cx cy OF OX OY _ _ _ hs.1 hcompute
  have h3 := pointStage_output L h hn R cx cy hc OF OX OY
  have h4 := pointStage_candidate L h hn R cx cy (OF^^pointFinite (R+.some hc))
    (OX^^^pointX (R+.some hc)) (OY^^^pointY (R+.some hc)) _ _ _ hs.2 hclear
  have h5 := pointStage_clearFlags L h hn R cx cy (OF^^pointFinite (R+.some hc))
    (OX^^^pointX (R+.some hc)) (OY^^^pointY (R+.some hc))
  exact (((h1.seq h2).seq h3).seq h4).seq h5

theorem pointAddOut_zero_ready (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (OF : Bool) (OX OY : Nat) :
    Triple (PointReady L R OF OX OY) (pointAddOut L 0)
      (PointReady L R (OF^^pointFinite R) (OX^^^pointX R) (OY^^^pointY R)) := by
  intro s m hs
  obtain ⟨hi,hof,hox,hoy,hz⟩ := hs
  have hd := (L.output_interfaces hn).2.1
  have ee := pointCopy_correct L.input L.output hd (h.inputX.trans h.outputX.symm)
    (h.inputY.trans h.outputY.symm) s m
  change PointEffect L.output _ _ _ s (run (pointAddOut L 0) m s) at ee
  have hv := (point_holds _ _ _).mp hi
  have hinput := (List.nodup_append'.mp hd).2.2
  have hout : ∀ w∈L.work,w∉PointAddLayout.pointWires L.output := by
    intro w hw ho
    exact List.disjoint_left.mp (List.nodup_append'.mp hn).2.2
      (List.mem_append_right _ ho) hw
  have hr : Holds.holds (run (pointAddOut L 0) m s).basis L.input R := by
    apply (point_holds _ _ _).mpr
    exact ⟨(ee.outside _ (List.disjoint_left.mp hinput (by simp [PointAddLayout.pointWires]))).trans hv.1,
      (ee.reg _ (List.disjoint_left.mpr (fun w hw => List.disjoint_left.mp hinput (by simp [PointAddLayout.pointWires,hw])))).trans hv.2.1,
      (ee.reg _ (List.disjoint_left.mpr (fun w hw => List.disjoint_left.mp hinput (by simp [PointAddLayout.pointWires,hw])))).trans hv.2.2⟩
  refine ⟨ee.phase,hr,?_,?_,?_,?_⟩
  · rw [ee.finite,hof,hv.1]
  · rw [ee.x,hox,hv.2.1]
  · rw [ee.y,hoy,hv.2.2]
  · exact (ee.reg _ (List.disjoint_left.mpr hout)).trans hz

/-- 任意目标位串的完整 XOR 规格。输入仅要求合法曲线点，不含横坐标或分支前提。 -/
theorem pointAddOut_xor_spec (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (R C : Point) (OF : Bool) (OX OY : Nat) :
    {{ L.input=R,L.output.finite=OF,L.output.x=OX,L.output.y=OY,L.work=0 }} pointAddOut L C
    {{ L.input=R,L.output.finite=(OF^^pointFinite (R+C)),
       L.output.x=(OX^^^pointX (R+C)),L.output.y=(OY^^^pointY (R+C)),L.work=0 }} := by
  have hh : Triple (PointReady L R OF OX OY) (pointAddOut L C)
      (PointReady L R (OF^^pointFinite (R+C)) (OX^^^pointX (R+C)) (OY^^^pointY (R+C))) := by
    cases C with
    | zero =>
      change Triple _ (pointAddOut L (0 : Point))
        (PointReady L R (OF^^pointFinite (R+0)) (OX^^^pointX (R+0)) (OY^^^pointY (R+0)))
      simpa only [add_zero] using pointAddOut_zero_ready L h hn R OF OX OY
    | some hc => exact pointAddOut_finite_ready L h hn R _ _ hc OF OX OY
  simpa only [PointReady,and_assoc,Holds.holds] using hh

/-- 常用零输出形式：包括输入/常量/结果为 O、互逆点和倍点的全部情形。 -/
theorem pointAddOut_spec (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (R C : Point) :
    {{ L.input=R,L.output=(0 : Point),L.work=0 }} pointAddOut L C
    {{ L.input=R,L.output=(R+C),L.work=0 }} := by
  have hh := pointAddOut_xor_spec L h hn R C false 0 0
  apply Triple.conseq ?_ hh ?_
  · intro s hs
    obtain ⟨⟨hi,ho⟩,hz⟩ := hs
    have hv := (point_holds _ _ _).mp ho
    exact ⟨⟨⟨⟨hi,hv.1⟩,hv.2.1⟩,hv.2.2⟩,hz⟩
  · intro s hs
    obtain ⟨⟨⟨⟨hi,hf⟩,hx⟩,hy⟩,hz⟩ := hs
    refine ⟨⟨hi,(point_holds _ _ _).mpr ?_⟩,hz⟩
    simpa only [Bool.false_xor,Nat.zero_xor] using And.intro hf (And.intro hx hy)

end ECDSAAdd.Arithmetic
