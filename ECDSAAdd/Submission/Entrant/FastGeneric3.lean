import ECDSAAdd.Submission.Entrant.Generic3
import ECDSAAdd.Arithmetic.ParametricPointDialogSteps

/-! The generic block of `fastGeneric3` with each arithmetic stage replaced by
`farith`: the relabelled lane kernel without the compare-based zero repair,
between two copies of `x₀ ^= ¬finite`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog

def fastGeneric3 (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  fastConstAdd L L.point.x (-cx) ++ fastConstAdd L L.point.y (-cy) ++
  farith L false ++
  fastSquare L ++
  fastConstRefl L (3*cx-1) ++
  farith L true ++
  fastConstNeg L cx ++ fastConstAdd L L.point.y (-cy)

section Generic
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
attribute [local irreducible] run arith2 farith CompressedPointSquare.computableProgram fastSquare fastCandidate
  pointMeasuredSquareCandidate fastConstAdd fastConstNeg fastConstRefl

theorem fast3_generic_true (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0)
    (hfb : base L.point.finite = true) :
    Triple (PointDialogValues L X Y true base) (fastGeneric3 L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := fastStep_addX L hw hn X Y true base (-cx)
  have h2 := fastStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have nz (Z : Fp) (hz : Z ≠ 0) : base L.point.finite = decide (Z.val ≠ 0) := by
    rw [hfb]; symm; apply decide_eq_true; intro hv; exact hz ((ZMod.val_eq_zero Z).mp hv)
  have h3 := farith_step L hw hn (X-cx) (Y-cy) true base false
    (fun _=>sub_ne_zero.mpr hX) (nz _ (sub_ne_zero.mpr hX))
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := fast_step_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := fastStep_refl L hw hn (-1-((X-cx)-a*a)) a true base (3*cx-1)
  simp only [if_true] at h5
  have hd5 : 3*cx-1-(-1-((X-cx)-a*a))=d := by
    have e := hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [← e]; ring
  rw [hd5] at h5
  have h6 := farith_step L hw hn d a true base true (fun _=>hd) (nz _ hd)
  simp only [if_true] at h6
  have h7 := fastStep_negX L hw hn d (a*d) true base cx
  simp only [if_true] at h7
  have h8 := fastStep_addY L hw hn (cx-d) (a*d) true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h8
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at h7 h8
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h8
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simpa only [fastGeneric3,List.append_assoc] using h

theorem fast3_generic_false (X Y cx cy : Fp) (base : BasisState)
    (hfin : base L.point.finite = decide (X.val ≠ 0)) :
    Triple (PointDialogValues L X Y false base) (fastGeneric3 L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := fastStep_addX L hw hn X Y false base (-cx)
  have h2 := fastStep_addY L hw hn X Y false base (-cy)
  have h3 := farith_step L hw hn X Y false base false (by simp) hfin
  have h4 := fast_step_square L hw hn X Y false base
  have h5 := fastStep_refl L hw hn (-1-X) Y false base (3*cx-1)
  have h6 := farith_step L hw hn X Y false base true (by simp) hfin
  have h7 := fastStep_negX L hw hn X Y false base cx
  have h8 := fastStep_addY L hw hn X Y false base (-cy)
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 h7 h8
  rw [show -1-(-1-X)=X by ring] at h5
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simpa only [fastGeneric3,List.append_assoc] using h

theorem fast3_boundary_generic (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (fastGeneric3 L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    have hfin : s.basis L.point.finite = decide (((coordinates R).getD (0,0)).1.val ≠ 0) := by
      rw [hp.1, pointFinite_eq_x]; rfl
    obtain ⟨phase,hv⟩ := fast3_generic_false L hw hn _ _ cx cy s.basis hfin s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      have hfb : s.basis L.point.finite = true := hp.1
      obtain ⟨phase,hv⟩ := fast3_generic_true L hw hn x y cx cy s.basis den.1 den.2 hfb s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end Generic

section Resources
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw

theorem fastGeneric3_counts (cx cy : Fp) :
    toffoliCount (fastGeneric3 L cx cy)=2183103 ∧
    measurementCount (fastGeneric3 L cx cy)=1523652 := by
  have a k := fastConstAdd_counts L hw L.point.x (Or.inl rfl) k
  have b k := fastConstAdd_counts L hw L.point.y (Or.inr rfl) k
  have c := fastConstNeg_counts L hw cx
  have r := fastConstRefl_counts L hw (3*cx-1)
  have arith := arith3_counts L
  have pf : toffoliCount (pfix L) = 0 ∧ measurementCount (pfix L) = 0 := ⟨rfl, rfl⟩
  have square := fastSquare_counts L hw
  simp only [fastGeneric3,farith,toffoliCount_append,measurementCount_append,pf.1,pf.2,
    (a _).1,(a _).2,(b _).1,(b _).2,c.1,c.2,r.1,r.2,arith.1,arith.2.1,arith.2.2.1,arith.2.2.2,
    square.1,square.2]
  norm_num

include hn in
theorem fastGeneric3_physical (cx cy : Fp) : GatePhysical (fastGeneric3 L cx cy) := by
  have ax (k : Fp) := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c k.val
  have ay (k : Fp) := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) SquareReduction.c k.val
  have ng := FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have pf : GatePhysical (pfix L) := by
    intro i hi
    simp only [pfix, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · trivial
    · exact finite_ne_x0 L hw hn
    · trivial
  have di : GatePhysical (farith L false) := by
    simp only [farith, gatePhysical_append]; exact ⟨pf, arith3_physical L hw hn false, pf⟩
  have mu : GatePhysical (farith L true) := by
    simp only [farith, gatePhysical_append]; exact ⟨pf, arith3_physical L hw hn true, pf⟩
  have rf := FastConst.fastRefl_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p (3*cx-1).val
  have sq := fastSquare_physical L hw hn
  simp only [fastGeneric3,fastConstAdd,fastConstNeg,fastConstRefl,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di⟩,sq⟩,rf⟩,mu⟩,ng⟩,ay _⟩

theorem fastGeneric3_gateSlots_le (cx cy : Fp) :
    Challenge.gateSlots (fastGeneric3 L cx cy) ≤ 46300000 := by
  have ax (r : List Wire) (hr : r.length=256) (k : Fp) :=
    FastConst.fastAdd_gateSlots_le (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw r hr)
  have ng := FastConst.fastNeg_gateSlots_le (g:=L.core.generic) 256 p cx.val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a1 := ax L.point.x hw.inputX (-cx)
  have a2 := ax L.point.y hw.inputY (-cy)
  have a3 := FastConst.fastRefl_gateSlots_le (g:=L.core.generic) 256 p (3*cx-1).val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have d := arith3_gateSlots_le L false
  have e := arith3_gateSlots_le L true
  have pf : Challenge.gateSlots (pfix L) = 3 := rfl
  have f := fastSquare_gateSlots_le L hw
  simp only [fastGeneric3,farith,fastConstAdd,fastConstNeg,fastConstRefl,Challenge.gateSlots_append,pf]
  omega

end Resources

end ECDSAAdd.Entrant
