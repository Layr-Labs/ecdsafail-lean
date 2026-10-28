import ECDSAAdd.Arithmetic.ReplayLoopProof
import ECDSAAdd.Math.ValueReplay

namespace ECDSAAdd.Arithmetic
open Secp256k1

private theorem cast_halve (X : Nat) : (halveMod p X : Fp)=(X:Fp)/2 := by
  have h := halve_mod_correct p X (by decide : p%2=1)
  have ht : (2:Fp)≠0 := by decide
  apply (eq_div_iff ht).mpr
  simpa [mul_comm] using h

private theorem cast_submod (X Y : Nat) (hY : Y<p) :
    (((X+p-Y)%p : Nat):Fp)=(X:Fp)-(Y:Fp) := by
  rw [ZMod.natCast_mod,Nat.cast_sub (by omega),Nat.cast_add]
  simp

/-- 电路中的规范自然数函数与值走数学使用的域线性函数一致。 -/
theorem replayNatStep_field (C W S : Bool) (X Y : Nat) (hX : X<p) (hY : Y<p) :
    (((replayNatStep p C W S X Y).1:Fp),((replayNatStep p C W S X Y).2:Fp))=
      valueReplayStep C (W,S) ((X:Fp),(Y:Fp)) := by
  have hx := cast_submod X Y hY
  have hy := cast_submod Y X hX
  cases C <;> cases W <;> cases S <;>
    simp [replayNatStep,valueReplayStep,valueReplaySwap,cast_halve,hx,hy]

theorem replayNatUnstep_field (C W S : Bool) (X Y : Nat) :
    (((replayNatUnstep p C W S X Y).1:Fp),((replayNatUnstep p C W S X Y).2:Fp))=
      valueReplayUnstep C (W,S) ((X:Fp),(Y:Fp)) := by
  cases C <;> cases W <;> cases S <;>
    simp [replayNatUnstep,valueReplayUnstep,valueReplaySwap,Nat.cast_add,Nat.cast_mul]

/-- 物理记录带加上独立 i<K 活动判定，形成数学回放的控制序列。 -/
def replayControls (K i : Nat) (ref : BasisState) : List RoundRecord → List (Bool×(Bool×Bool))
  | [] => []
  | r::rs => (decide (i<K),(ref r.swap,ref r.subtract))::replayControls K (i+1) ref rs

theorem replayNatLoop_field (K i : Nat) (ref : BasisState) (rs : List RoundRecord)
    (X Y : Nat) (hX : X<p) (hY : Y<p) :
    (((replayNatLoop p K i ref rs (X,Y)).1:Fp),((replayNatLoop p K i ref rs (X,Y)).2:Fp))=
      valueReplay (replayControls K i ref rs) ((X:Fp),(Y:Fp)) := by
  induction rs generalizing i X Y with
  | nil => rfl
  | cons r rs ih =>
    have hb := replayNatStep_bound p X Y (decide (i<K)) (ref r.swap) (ref r.subtract) (by decide) hX hY
    have hh := ih (i+1) _ _ hb.1 hb.2
    simpa only [replayNatLoop,replayControls,valueReplay,replayNatStep_field _ _ _ X Y hX hY] using hh

theorem replayNatUnloop_field (K i : Nat) (ref : BasisState) (rs : List RoundRecord)
    (X Y : Nat) :
    (((replayNatUnloop p K i ref rs (X,Y)).1:Fp),((replayNatUnloop p K i ref rs (X,Y)).2:Fp))=
      valueReplayInverse (replayControls K i ref rs) ((X:Fp),(Y:Fp)) := by
  induction rs generalizing i X Y with
  | nil => rfl
  | cons r rs ih =>
    simp only [replayNatUnloop,replayControls,valueReplayInverse,replayNatUnstep_field,ih]

end ECDSAAdd.Arithmetic
