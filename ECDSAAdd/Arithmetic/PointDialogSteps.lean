import ECDSAAdd.Arithmetic.PointDialogState

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1
private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState)
include hw hn

theorem dialogStep_addX (k : Fp) :
    Triple (PointDialogValues L X Y G base) (pointDialogConstantAdd L L.point.x k)
      (PointDialogValues L (X+(if G then k else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointDialogConstantAdd_correct L hw hn L.point.x (Or.inl rfl)
    k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem dialogStep_addY (k : Fp) :
    Triple (PointDialogValues L X Y G base) (pointDialogConstantAdd L L.point.y k)
      (PointDialogValues L X (Y+(if G then k else 0)) G base) := by
  intro s m v
  obtain ⟨hp,hy,hf⟩ := pointDialogConstantAdd_correct L hw hn L.point.y (Or.inr rfl)
    k Y.val G Y.isLt s m v.generic v.y v.clean
  refine ⟨hp,v.withY hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt Y)] using hy

theorem dialogStep_negate :
    Triple (PointDialogValues L X Y G base) (pointDialogNegate L)
      (PointDialogValues L (if G then -X else X) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointDialogNegate_correct L hw hn X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.neg_val'] using hx

theorem dialogStep_square :
    Triple (PointDialogValues L X Y G base) (pointDialogSquare L)
      (PointDialogValues L (X-(if G then Y*Y else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := pointDialogSquare_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa [sub_val,ZMod.val_mul,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem dialogStep_arithmetic (multiply : Bool) (hX : G=true → X≠0) :
    Triple (PointDialogValues L X Y G base)
      (pointOffsetBorrowedArithmetic L multiply)
      (PointDialogValues L X (if G then (if multiply then Y*X else Y/X) else Y) G base) := by
  intro s m v
  have hX0 : G=true → X.val≠0 := by
    intro hg hx; apply hX hg; apply ZMod.val_injective p; simpa using hx
  obtain ⟨hp,hy,hf⟩ := pointDialog_arithmetic_correct L hw hn multiply X.val Y.val G
    X.isLt hX0 Y.isLt s m v.generic v.x v.y v.clean
  refine ⟨hp,v.withY hn ?_ hf⟩
  cases G <;> cases multiply <;> simpa only [Bool.false_eq_true,if_false,if_true,ZMod.natCast_zmod_val] using hy

end ECDSAAdd.Arithmetic
