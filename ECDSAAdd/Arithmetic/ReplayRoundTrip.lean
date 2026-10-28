import ECDSAAdd.Arithmetic.ReplayField

namespace ECDSAAdd.Arithmetic
open Secp256k1

private theorem natPair_eq_of_field {x y : Nat × Nat}
    (hx : x.1 < p ∧ x.2 < p) (hy : y.1 < p ∧ y.2 < p)
    (he : ((x.1 : Fp), (x.2 : Fp)) = ((y.1 : Fp), (y.2 : Fp))) : x = y := by
  apply Prod.ext
  · have h := congrArg (fun z : Fp × Fp => z.1.val) he
    simpa only [ZMod.val_natCast_of_lt hx.1, ZMod.val_natCast_of_lt hy.1] using h
  · have h := congrArg (fun z : Fp × Fp => z.2.val) he
    simpa only [ZMod.val_natCast_of_lt hx.2, ZMod.val_natCast_of_lt hy.2] using h

/-- 规范载荷上，反回放单步恢复正回放前的两个自然数值。 -/
theorem replayNatUnstep_step (C W S : Bool) (X Y : Nat) (hX : X < p) (hY : Y < p) :
    replayNatUnstep p C W S (replayNatStep p C W S X Y).1
      (replayNatStep p C W S X Y).2 = (X, Y) := by
  have hb := replayNatStep_bound p X Y C W S (by decide) hX hY
  apply natPair_eq_of_field
    (replayNatUnstep_bound p _ _ C W S (by decide) hb.1 hb.2) ⟨hX, hY⟩
  rw [replayNatUnstep_field, replayNatStep_field C W S X Y hX hY,
    valueReplayUnstep_step]

/-- 正回放也恢复反回放前的规范载荷；控制位不受额外限制。 -/
theorem replayNatStep_unstep (C W S : Bool) (X Y : Nat) (hX : X < p) (hY : Y < p) :
    replayNatStep p C W S (replayNatUnstep p C W S X Y).1
      (replayNatUnstep p C W S X Y).2 = (X, Y) := by
  have hb := replayNatUnstep_bound p X Y C W S (by decide) hX hY
  apply natPair_eq_of_field
    (replayNatStep_bound p _ _ C W S (by decide) hb.1 hb.2) ⟨hX, hY⟩
  rw [replayNatStep_field C W S _ _ hb.1 hb.2, replayNatUnstep_field,
    valueReplayStep_unstep]

/-- 任意记录序列的正、反回放在规范载荷上互逆。 -/
theorem replayNatUnloop_loop (K i : Nat) (ref : BasisState) (rs : List RoundRecord)
    (X Y : Nat) (hX : X < p) (hY : Y < p) :
    replayNatUnloop p K i ref rs (replayNatLoop p K i ref rs (X,Y)) = (X,Y) := by
  have hb := replayNatLoop_bound p K i ref rs X Y (by decide) hX hY
  apply natPair_eq_of_field
    (replayNatUnloop_bound p K i ref rs _ _ (by decide) hb.1 hb.2) ⟨hX,hY⟩
  rw [replayNatUnloop_field, replayNatLoop_field K i ref rs X Y hX hY,
    valueReplayInverse_replay]

/-- 先反回放再正回放同样恢复规范载荷，包括零载荷。 -/
theorem replayNatLoop_unloop (K i : Nat) (ref : BasisState) (rs : List RoundRecord)
    (X Y : Nat) (hX : X < p) (hY : Y < p) :
    replayNatLoop p K i ref rs (replayNatUnloop p K i ref rs (X,Y)) = (X,Y) := by
  have hb := replayNatUnloop_bound p K i ref rs X Y (by decide) hX hY
  apply natPair_eq_of_field
    (replayNatLoop_bound p K i ref rs _ _ (by decide) hb.1 hb.2) ⟨hX,hY⟩
  rw [replayNatLoop_field K i ref rs _ _ hb.1 hb.2, replayNatUnloop_field,
    valueReplay_replayInverse]

/-- 两段均为前向执行的电路；任意测量记录下恢复相位、载荷、控制和零工作区。 -/
theorem replayCell_roundTrip_spec (active swap sub : Wire) (L : ModInPlaceLayout)
    (n X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hpn : p < 2^n)
    (hX : X < p) (hY : Y < p) :
    Triple (ReplayValues active swap sub L C W S X Y)
      (replayCell active swap sub L p ++ replayUncell active swap sub L p)
      (ReplayValues active swap sub L C W S X Y) := by
  have hb := replayNatStep_bound p X Y C W S (by decide) hX hY
  have h := (replayCell_spec active swap sub L n p X Y C W S hw hnd
    (by decide) hpn hX hY).seq
    (replayUncell_spec active swap sub L n p _ _ C W S hw hnd
      (by decide) hpn hb.1 hb.2)
  simpa only [replayNatUnstep_step C W S X Y hX hY] using h

/-- 反向次序的单格组合也恢复相位和全部公开寄存器断言。 -/
theorem replayUncell_roundTrip_spec (active swap sub : Wire) (L : ModInPlaceLayout)
    (n X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hpn : p < 2^n)
    (hX : X < p) (hY : Y < p) :
    Triple (ReplayValues active swap sub L C W S X Y)
      (replayUncell active swap sub L p ++ replayCell active swap sub L p)
      (ReplayValues active swap sub L C W S X Y) := by
  have hb := replayNatUnstep_bound p X Y C W S (by decide) hX hY
  have h := (replayUncell_spec active swap sub L n p X Y C W S hw hnd
    (by decide) hpn hX hY).seq
    (replayCell_spec active swap sub L n p _ _ C W S hw hnd
      (by decide) hpn hb.1 hb.2)
  simpa only [replayNatStep_unstep C W S X Y hX hY] using h

/-- 有效布局和剩余轮数内，正反循环恢复载荷、记录、外部线路及零工作区。 -/
theorem replayLoop_roundTrip_spec (L : ReplayLayout) (n K i : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (ref : BasisState) (X Y : Nat)
    (hpn : p < 2^n) (hX : X < p) (hY : Y < p)
    (hK : regValue L.counter.x ref = K) (hi : i + rs.length ≤ 512) :
    Triple (ReplayState L ref false X Y)
      (replayLoop L p i rs ++ replayUnloop L p i rs) (ReplayState L ref false X Y) := by
  have hb := replayNatLoop_bound p K i ref rs X Y (by decide) hX hY
  have h := (replayLoop_spec L n p K i rs hv ref X Y (by decide) hpn hX hY hK hi).seq
    (replayUnloop_spec L n p K i rs hv ref _ _ (by decide) hpn hb.1 hb.2 hK hi)
  simpa only [replayNatUnloop_loop K i ref rs X Y hX hY] using h

/-- 循环的反向次序具有相同的全记录恢复规格。 -/
theorem replayUnloop_roundTrip_spec (L : ReplayLayout) (n K i : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (ref : BasisState) (X Y : Nat)
    (hpn : p < 2^n) (hX : X < p) (hY : Y < p)
    (hK : regValue L.counter.x ref = K) (hi : i + rs.length ≤ 512) :
    Triple (ReplayState L ref false X Y)
      (replayUnloop L p i rs ++ replayLoop L p i rs) (ReplayState L ref false X Y) := by
  have hb := replayNatUnloop_bound p K i ref rs X Y (by decide) hX hY
  have h := (replayUnloop_spec L n p K i rs hv ref X Y (by decide) hpn hX hY hK hi).seq
    (replayLoop_spec L n p K i rs hv ref _ _ (by decide) hpn hb.1 hb.2 hK hi)
  simpa only [replayNatLoop_unloop K i ref rs X Y hX hY] using h

end ECDSAAdd.Arithmetic
