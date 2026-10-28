import ECDSAAdd.Arithmetic.ModularResources
import ECDSAAdd.Math.BitcoinCurve

namespace ECDSAAdd.Arithmetic

/-- secp256k1 的模数作为编译期常量；257 位布局保留候选差的符号信息。 -/
def fieldAdd (L : ModLayout) : Program := modAdd L p
def fieldSub (L : ModLayout) : Program := modSub L p

private theorem modulus_pos : 0 < p := by norm_num [p]
private theorem modulus_bound : p < 2^256 := by norm_num [p]

theorem fieldAdd_spec (L : ModLayout) (hnd : L.wires.Nodup) (hw : L.width = 256)
    (X Y O : Nat) (hX : X < p) (hY : Y < p) :
    {{ L.x = X, L.y = Y, L.out = O, L.work = 0 }} fieldAdd L
    {{ L.x = X, L.y = Y, L.out = (O ^^^ ((X+Y)%p)), L.work = 0 }} :=
  modAdd_spec L hnd p modulus_pos (hw ▸ modulus_bound) X Y O hX hY

theorem fieldSub_spec (L : ModLayout) (hnd : L.wires.Nodup) (hw : L.width = 256)
    (X Y O : Nat) (hX : X < p) (hY : Y < p) :
    {{ L.x = X, L.y = Y, L.out = O, L.work = 0 }} fieldSub L
    {{ L.x = X, L.y = Y, L.out = (O ^^^ ((X+p-Y)%p)), L.work = 0 }} :=
  modSub_spec L hnd p modulus_pos (hw ▸ modulus_bound) X Y O hX hY

/-- 零输出的常用形式：直接得到模 p 的和。 -/
theorem fieldAdd_zero_spec (L : ModLayout) (hnd : L.wires.Nodup) (hw : L.width = 256)
    (X Y : Nat) (hX : X < p) (hY : Y < p) :
    {{ L.x = X, L.y = Y, L.out = 0, L.work = 0 }} fieldAdd L
    {{ L.x = X, L.y = Y, L.out = ((X+Y)%p), L.work = 0 }} := by
  simpa only [Nat.zero_xor] using fieldAdd_spec L hnd hw X Y 0 hX hY

theorem fieldSub_zero_spec (L : ModLayout) (hnd : L.wires.Nodup) (hw : L.width = 256)
    (X Y : Nat) (hX : X < p) (hY : Y < p) :
    {{ L.x = X, L.y = Y, L.out = 0, L.work = 0 }} fieldSub L
    {{ L.x = X, L.y = Y, L.out = ((X+p-Y)%p), L.work = 0 }} := by
  simpa only [Nat.zero_xor] using fieldSub_spec L hnd hw X Y 0 hX hY

theorem fieldAdd_resources (L : ModLayout) (hnd : L.wires.Nodup) (hw : L.width = 256) :
    toffoliCount (fieldAdd L) = 1284 ∧ measurementCount (fieldAdd L) = 1028 ∧
    qubitCount (fieldAdd L) = 2057 := by
  simpa only [hw, fieldAdd] using modAdd_resources L hnd p

theorem fieldSub_resources (L : ModLayout) (hnd : L.wires.Nodup) (hw : L.width = 256) :
    toffoliCount (fieldSub L) = 1284 ∧ measurementCount (fieldSub L) = 1028 ∧
    qubitCount (fieldSub L) = 2057 := by
  simpa only [hw, fieldSub] using modSub_resources L hnd p

end ECDSAAdd.Arithmetic
