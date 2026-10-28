import ECDSAAdd.Arithmetic.PointInPlaceState

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [← Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y A : Fp) (G E Q : Bool)
include hw hn

theorem pointStep_addX (k : Fp) :
    Triple (PointInPlaceValues L X Y A G E Q) (pointInPlaceConstantAdd L L.point.x k)
      (PointInPlaceValues L (X+(if G then k else 0)) Y A G E Q) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointInPlaceConstantAdd_correct L hw hn L.point.x (Or.inl rfl) k X.val G X.isLt
    s m v.generic v.x v.borrow
  refine ⟨hp,v.withX hw hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem pointStep_addY (k : Fp) :
    Triple (PointInPlaceValues L X Y A G E Q) (pointInPlaceConstantAdd L L.point.y k)
      (PointInPlaceValues L X (Y+(if G then k else 0)) A G E Q) := by
  intro s m v
  obtain ⟨hp,hy,hf⟩ := pointInPlaceConstantAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt
    s m v.generic v.y v.borrow
  refine ⟨hp,v.withY hw hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt Y)] using hy

theorem pointStep_product :
    Triple (PointInPlaceValues L X Y A G E Q) (montMulAdd L.inPlaceMultiply p)
      (PointInPlaceValues L X (Y+A*X) A G E Q) ∧
    Triple (PointInPlaceValues L X Y A G E Q) (montMulSub L.inPlaceMultiply p)
      (PointInPlaceValues L X (Y-A*X) A G E Q) := by
  constructor
  · intro s m v
    obtain ⟨hp,hy,hf⟩ := (pointInPlaceProduct_correct L hw hn A.val X.val Y.val A.isLt X.isLt Y.isLt
      s m v.slope v.x v.y v.borrow).1
    exact ⟨hp,v.withY hw hn (by simpa only [ZMod.val_add,ZMod.val_mul] using hy) hf⟩
  · intro s m v
    obtain ⟨hp,hy,hf⟩ := (pointInPlaceProduct_correct L hw hn A.val X.val Y.val A.isLt X.isLt Y.isLt
      s m v.slope v.x v.y v.borrow).2
    exact ⟨hp,v.withY hw hn (by simpa only [sub_val,ZMod.val_mul] using hy) hf⟩

theorem pointStep_negate :
    Triple (PointInPlaceValues L X Y A G E Q) (pointInPlaceNegate L)
      (PointInPlaceValues L (if G then -X else X) Y A G E Q) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointInPlaceNegate_correct L hw hn X.val G X.isLt s m v.generic v.x v.borrow
  refine ⟨hp,v.withX hw hn ?_ hf⟩
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.neg_val'] using hx

theorem pointStep_square :
    Triple (PointInPlaceValues L X Y A G E Q)
      (squareSub L.inPlaceKaratsuba)
      (PointInPlaceValues L (X-A*A) Y A G E Q) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointInPlaceSquare_correct L hw hn A.val X.val X.isLt s m v.slope v.x v.borrow
  exact ⟨hp,v.withX hw hn (by simpa only [sub_val,ZMod.val_mul] using hx) hf⟩

theorem pointStep_divideAdd (hX : G=true → X≠0) :
    Triple (PointInPlaceValues L X Y A G E Q) (divideAdd (L.inPlaceDivide L.core.generic L.point.x L.point.y))
      (PointInPlaceValues L X Y (if G then A+Y/X else A) G E Q) := by
  have hd : G=true → X.val≠0 := by
    intro hg hx
    apply hX hg
    apply ZMod.val_injective p
    simpa only [ZMod.val_zero] using hx
  intro s m v
  have hwd := L.inPlaceDivide_widths hw L.core.generic _ _ hw.inputX hw.inputY
  have hnd := L.inPlaceDivide_nodup hw hn L.core.generic (by simp [inPlaceFlags])
  obtain ⟨hp,hv⟩ := divideAdd_spec _ hwd hnd X.val Y.val A.val G X.isLt Y.isLt A.isLt hd
    s m ⟨⟨⟨⟨v.generic,v.x⟩,v.y⟩,v.slope⟩,v.clean⟩
  have hf := divide_frame _ hwd hnd X.val Y.val A.val G X.isLt Y.isLt A.isLt hd
    s m v.generic v.x v.y v.slope v.clean
  refine ⟨hp,v.withSlope hw hn ?_ (fun q hq => (hf q hq).1)⟩
  have hval := hv.1.2
  change regValue L.inPlaceSlope _ = _ at hval
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.val_add,div_eq_mul_inv,
    ZMod.val_mul,ZMod.natCast_zmod_val,mul_comm] using hval

theorem pointStep_divideSub (hX : Q=true → X≠0) :
    Triple (PointInPlaceValues L X Y A G E Q) (divideSub (L.inPlaceDivide L.core.equalNegY L.point.x L.point.y))
      (PointInPlaceValues L X Y (if Q then A-Y/X else A) G E Q) := by
  have hd : Q=true → X.val≠0 := by
    intro hq hx
    apply hX hq
    apply ZMod.val_injective p
    simpa only [ZMod.val_zero] using hx
  intro s m v
  have hwd := L.inPlaceDivide_widths hw L.core.equalNegY _ _ hw.inputX hw.inputY
  have hnd := L.inPlaceDivide_nodup hw hn L.core.equalNegY (by simp [inPlaceFlags])
  obtain ⟨hp,hv⟩ := divideSub_spec _ hwd hnd X.val Y.val A.val Q X.isLt Y.isLt A.isLt hd
    s m ⟨⟨⟨⟨v.quotient,v.x⟩,v.y⟩,v.slope⟩,v.clean⟩
  have hf := divide_frame _ hwd hnd X.val Y.val A.val Q X.isLt Y.isLt A.isLt hd
    s m v.quotient v.x v.y v.slope v.clean
  refine ⟨hp,v.withSlope hw hn ?_ (fun q hq => (hf q hq).2)⟩
  have hval := hv.1.2
  change regValue L.inPlaceSlope _ = _ at hval
  cases Q <;> simpa only [Bool.false_eq_true,if_false,if_true,sub_val,div_eq_mul_inv,
    ZMod.val_mul,ZMod.natCast_zmod_val,mul_comm] using hval

end ECDSAAdd.Arithmetic
