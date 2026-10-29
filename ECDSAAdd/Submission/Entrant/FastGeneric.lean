import ECDSAAdd.Submission.Entrant.FastConst
import ECDSAAdd.Submission.Entrant.SquareNR
import ECDSAAdd.Arithmetic.CompressedPointDialogSteps
import ECDSAAdd.Arithmetic.CompressedPointDialogResources
import ECDSAAdd.Arithmetic.SkywalkPointPhysical
import ECDSAAdd.Baselines.SkywalkSlots

/-! The Skywalk generic stage with every classical coordinate correction done
by the compare-first constant adder of `FastConst`.  The final reflection and
abscissa correction are fused into one `x ↦ cx - x` step, and the square's
final output reflection is absorbed into the `3cx` correction.  The division,
multiplication and square arithmetic are the unchanged Skywalk blocks. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog

def fastConstAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  FastConst.fastAdd (L.recoveryConstant r) L.core.generic SquareReduction.c k.val

def fastConstNeg (L : ControlledPointLayout) (k : Fp) : Program :=
  FastConst.fastNeg (L.recoveryConstant L.point.x) L.core.generic p k.val

def fastConstRefl (L : ControlledPointLayout) (k : Fp) : Program :=
  FastConst.fastRefl (L.recoveryConstant L.point.x) L.core.generic p k.val

def fastGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  fastConstAdd L L.point.x (-cx) ++ fastConstAdd L L.point.y (-cy) ++
  pointCompressedArithmetic L false ++
  squareNR L ++
  fastConstRefl L (3*cx-1) ++
  pointCompressedArithmetic L true ++
  fastConstNeg L cx ++ fastConstAdd L L.point.y (-cy)

private theorem sub_val' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
private theorem scratch_clean (r : List Wire) (s : State) (hc : regValue L.dialogPool s.basis=0) :
    let K := L.recoveryConstant r
    regValue K.src s.basis=0 ∧ s.basis K.flag=false ∧ (∀q∈K.carry,s.basis q=false) ∧
      s.basis K.cin=false := by
  intro K
  have aux (q : Wire) (hq : q∈K.src++K.carry++[K.high,K.cin,K.flag]) : s.basis q=false := by
    change q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag] at hq
    rw [L.recoveryConstant_pool hw r] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  exact ⟨(regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq])),aux _ (by simp),
    fun q hq => aux q (by simp [hq]),aux _ (by simp)⟩

theorem fastConstAdd_correct (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (X : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue r s.basis=X) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastConstAdd L r k) m s).phase=s.phase ∧
    regValue r (run (fastConstAdd L r k) m s).basis=(X+(if B then k.val else 0))%p ∧
    ∀q,q∉r → (run (fastConstAdd L r k) m s).basis q=s.basis q := by
  have len : r.length=256 := by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY
  have cl := scratch_clean L hw r s hc
  have result := FastConst.fastAdd_correct (L.recoveryConstant_nodup hw hn r hr) 256
    SquareReduction.c p k.val (L.recoveryConstant_widths hw r len) (by decide)
    (by norm_num [p,SquareReduction.c]) k.isLt X hX s m cl.1 hx cl.2.1 cl.2.2.1 cl.2.2.2
  simpa only [fastConstAdd,hb] using result

theorem fastConstNeg_correct (k : Fp) (X : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastConstNeg L k) m s).phase=s.phase ∧
    regValue L.point.x (run (fastConstNeg L k) m s).basis=(if B then (k.val+p-X)%p else X) ∧
    ∀q,q∉L.point.x → (run (fastConstNeg L k) m s).basis q=s.basis q := by
  have cl := scratch_clean L hw L.point.x s hc
  have result := FastConst.fastNeg_correct (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) 256
    p k.val (L.recoveryConstant_widths hw L.point.x hw.inputX) (by decide)
    (by norm_num [p]) k.isLt X hX s m cl.1 hx cl.2.1 cl.2.2.1 cl.2.2.2
  simpa only [fastConstNeg,hb] using result

theorem fastConstRefl_correct (k : Fp) (X : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastConstRefl L k) m s).phase=s.phase ∧
    regValue L.point.x (run (fastConstRefl L k) m s).basis=(if B then (k.val+p-X)%p else p-1-X) ∧
    ∀q,q∉L.point.x → (run (fastConstRefl L k) m s).basis q=s.basis q := by
  have cl := scratch_clean L hw L.point.x s hc
  have result := FastConst.fastRefl_correct (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) 256
    p k.val (L.recoveryConstant_widths hw L.point.x hw.inputX) (by decide)
    (by norm_num [p]) k.isLt X hX s m cl.1 hx cl.2.1 cl.2.2.1 cl.2.2.2
  simpa only [fastConstRefl,hb] using result

variable (X Y : Fp) (G : Bool) (base : BasisState)

theorem fastStep_addX (k : Fp) :
    Triple (PointDialogValues L X Y G base) (fastConstAdd L L.point.x k)
      (PointDialogValues L (X+(if G then k else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl)
    k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem fastStep_addY (k : Fp) :
    Triple (PointDialogValues L X Y G base) (fastConstAdd L L.point.y k)
      (PointDialogValues L X (Y+(if G then k else 0)) G base) := by
  intro s m v
  obtain ⟨hp,hy,hf⟩ := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl)
    k Y.val G Y.isLt s m v.generic v.y v.clean
  refine ⟨hp,v.withY hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt Y)] using hy

theorem fastStep_negX (k : Fp) :
    Triple (PointDialogValues L X Y G base) (fastConstNeg L k)
      (PointDialogValues L (if G then k-X else X) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastConstNeg_correct L hw hn k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G
  · simpa using hx
  · simp only [if_true]; rw [sub_val']; simpa using hx

omit hw hn in
private theorem refl_val (V : Fp) : (-1-V).val=p-1-V.val := by
  have hl : V.val<p := ZMod.val_lt V
  have hp : 1≤p := by norm_num [p]
  have cast : ((p-1-V.val : Nat) : Fp)=-1-V := by
    rw [Nat.cast_sub (by omega : V.val≤p-1),Nat.cast_sub hp]
    simp only [ZMod.natCast_self,Nat.cast_one,zero_sub,ZMod.natCast_zmod_val]
  rw [← cast,ZMod.val_natCast_of_lt (by omega)]

theorem fastStep_refl (k : Fp) :
    Triple (PointDialogValues L X Y G base) (fastConstRefl L k)
      (PointDialogValues L (if G then k-X else -1-X) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastConstRefl_correct L hw hn k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G
  · simp only [Bool.false_eq_true,if_false] at hx ⊢; rw [refl_val]; exact hx
  · simp only [if_true] at hx ⊢; rw [sub_val']; exact hx

theorem fastStep_square :
    Triple (PointDialogValues L X Y G base) (squareNR L)
      (PointDialogValues L (-1-(X-(if G then Y*Y else 0))) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := squareNR_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  rw [refl_val,sub_val']
  cases G
  · simpa using hx
  · simpa [ZMod.val_mul] using hx

end Correct

section Generic
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
attribute [local irreducible] run pointCompressedArithmetic CompressedPointSquare.computableProgram
  pointMeasuredSquareCandidate fastConstAdd fastConstNeg fastConstRefl squareNR

theorem fast_generic_true (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (fastGeneric L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := fastStep_addX L hw hn X Y true base (-cx)
  have h2 := fastStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := step_arithmetic L hw hn (X-cx) (Y-cy) true base false (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := fastStep_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := fastStep_refl L hw hn (-1-((X-cx)-a*a)) a true base (3*cx-1)
  simp only [if_true] at h5
  have hd5 : 3*cx-1-(-1-((X-cx)-a*a))=d := by
    have e := hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [← e]; ring
  rw [hd5] at h5
  have h6 := step_arithmetic L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have h7 := fastStep_negX L hw hn d (a*d) true base cx
  simp only [if_true] at h7
  have h8 := fastStep_addY L hw hn (cx-d) (a*d) true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h8
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at h7 h8
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h8
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simpa only [fastGeneric,List.append_assoc] using h

theorem fast_generic_false (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (fastGeneric L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := fastStep_addX L hw hn X Y false base (-cx)
  have h2 := fastStep_addY L hw hn X Y false base (-cy)
  have h3 := step_arithmetic L hw hn X Y false base false (by simp)
  have h4 := fastStep_square L hw hn X Y false base
  have h5 := fastStep_refl L hw hn (-1-X) Y false base (3*cx-1)
  have h6 := step_arithmetic L hw hn X Y false base true (by simp)
  have h7 := fastStep_negX L hw hn X Y false base cx
  have h8 := fastStep_addY L hw hn X Y false base (-cy)
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 h7 h8
  rw [show -1-(-1-X)=X by ring] at h5
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simpa only [fastGeneric,List.append_assoc] using h

theorem fast_boundary_generic (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (fastGeneric L cx cy)
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
    obtain ⟨phase,hv⟩ := fast_generic_false L hw hn _ _ cx cy s.basis s m values
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
      obtain ⟨phase,hv⟩ := fast_generic_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end Generic

section Resources
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem fastConstAdd_counts (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (fastConstAdd L r k)=766 ∧ measurementCount (fastConstAdd L r k)=767 := by
  have len : r.length=256 := by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY
  exact FastConst.fastAdd_counts 256 _ _ (L.recoveryConstant_widths hw r len) (by decide)

omit hn in
theorem fastConstNeg_counts (k : Fp) :
    toffoliCount (fastConstNeg L k)=766 ∧ measurementCount (fastConstNeg L k)=767 :=
  FastConst.fastNeg_counts 256 _ _ (L.recoveryConstant_widths hw L.point.x hw.inputX) (by decide)

omit hn in
omit hn in
theorem fastConstRefl_counts (k : Fp) :
    toffoliCount (fastConstRefl L k)=766 ∧ measurementCount (fastConstRefl L k)=767 :=
  FastConst.fastRefl_counts 256 _ _ (L.recoveryConstant_widths hw L.point.x hw.inputX) (by decide)

omit hn in
theorem fastGeneric_counts (cx cy : Fp) :
    toffoliCount (fastGeneric L cx cy)=2211487 ∧
    measurementCount (fastGeneric L cx cy)=1552034 := by
  have a k := fastConstAdd_counts L hw L.point.x (Or.inl rfl) k
  have b k := fastConstAdd_counts L hw L.point.y (Or.inr rfl) k
  have c := fastConstNeg_counts L hw cx
  have r := fastConstRefl_counts L hw (3*cx-1)
  have arith := pointCompressedArithmetic_counts L
  have square := squareNR_counts L hw
  simp only [fastGeneric,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,c.1,c.2,r.1,r.2,arith.1,arith.2.1,arith.2.2.1,arith.2.2.2,
    square.1,square.2]
  norm_num

omit hn in
theorem fastConst_sites (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).toFinset⊆(sites L).toFinset := by
  intro q hq
  have small := prefix_small L hw 515 (Nat.le_refl 515)
  have pool := L.recoveryConstant_pool hw r
  have hq' := List.mem_toFinset.mp hq
  have inpool (h : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ h
  apply List.mem_toFinset.mpr
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at hq'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at hq'
  have pl : q∈L.dialogPool.take 515 → q∈CompressedPointSquare.sharedPool L := fun h => small h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  simp only [sites,CompressedPointSquare.residents,PointAddLayout.pointWires,inPlaceFlags,
    List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
  rcases hr with rfl|rfl <;> tauto

theorem fastGeneric_support (cx cy : Fp) :
    wires (fastGeneric L cx cy)⊆(sites L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (fastConstAdd L r k)⊆(sites L).toFinset :=
    (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩).trans
      (fastConst_sites L hw r hr)
  have cn : wires (fastConstNeg L cx)⊆(sites L).toFinset :=
    (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConst_sites L hw L.point.x (Or.inl rfl))
  have cr : wires (fastConstRefl L (3*cx-1))⊆(sites L).toFinset :=
    (FastConst.fastRefl_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConst_sites L hw L.point.x (Or.inl rfl))
  have arith (b : Bool) := pointCompressedArithmetic_support L hw b
  have square := (squareNR_wires L).trans (CompressedPointSquare.computable_support L hw hn)
  simpa only [fastGeneric,wires_append,Finset.union_subset_iff,sites] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro
      (ca L.point.x (Or.inl rfl) (-cx)) (ca L.point.y (Or.inr rfl) (-cy)))
      (arith false)) square) cr) (arith true)) cn)
      (ca L.point.y (Or.inr rfl) (-cy))

theorem fastGeneric_physical (cx cy : Fp) : GatePhysical (fastGeneric L cx cy) := by
  have ax (k : Fp) := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c k.val
  have ay (k : Fp) := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) SquareReduction.c k.val
  have ng := FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have di := pointCompressedArithmetic_physical L hw hn false
  have mu := pointCompressedArithmetic_physical L hw hn true
  have rf := FastConst.fastRefl_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p (3*cx-1).val
  have sq := squareNR_physical L hw hn
  simp only [fastGeneric,fastConstAdd,fastConstNeg,fastConstRefl,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di⟩,sq⟩,rf⟩,mu⟩,ng⟩,ay _⟩

omit hn in
theorem fastGeneric_gateSlots_le (cx cy : Fp) :
    Challenge.gateSlots (fastGeneric L cx cy) ≤ 46300000 := by
  have ax (r : List Wire) (hr : r.length=256) (k : Fp) :=
    FastConst.fastAdd_gateSlots_le (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw r hr)
  have ng := FastConst.fastNeg_gateSlots_le (g:=L.core.generic) 256 p cx.val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a1 := ax L.point.x hw.inputX (-cx)
  have a2 := ax L.point.y hw.inputY (-cy)
  have a3 := FastConst.fastRefl_gateSlots_le (g:=L.core.generic) 256 p (3*cx-1).val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have d := Baselines.pointCompressedArithmetic_gateSlots_le L false
  have e := Baselines.pointCompressedArithmetic_gateSlots_le L true
  have f := squareNR_gateSlots_le L hw
  simp only [fastGeneric,fastConstAdd,fastConstNeg,fastConstRefl,Challenge.gateSlots_append]
  omega

end Resources

end ECDSAAdd.Entrant
