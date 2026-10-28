import ECDSAAdd.Arithmetic.Subtractor

namespace ECDSAAdd.Arithmetic

/-- 每位的四根线路只存一份，寄存器访问由此派生，长度天然一致。 -/
structure AdderLayout where
  bits : List AddBit
  cin : Wire

namespace AdderLayout

def width (L : AdderLayout) : Nat := L.bits.length
def x (L : AdderLayout) : List Wire := L.bits.map AddBit.x
def y (L : AdderLayout) : List Wire := L.bits.map AddBit.y
def out (L : AdderLayout) : List Wire := L.bits.map AddBit.out
def carry (L : AdderLayout) : List Wire := L.bits.map AddBit.carry
def wires (L : AdderLayout) : List Wire := L.cin :: addWires L.bits

end AdderLayout

def add (L : AdderLayout) : Program := rippleAdder L.bits L.cin
def sub (L : AdderLayout) : Program := rippleSubtractor L.bits L.cin

/-- 任意输出初值均可：异或写入模 2^n 的和，恢复输入、相位和进位工作线。 -/
theorem add_spec (L : AdderLayout) (hnd : L.wires.Nodup) (X Y O : Nat) (C : Bool) :
    {{ L.x = X, L.y = Y, L.cin = C, L.out = O, L.carry = 0 }} add L
    {{ L.x = X, L.y = Y, L.cin = C,
       L.out = (O ^^^ ((X + Y + C.toNat) % 2^L.width)), L.carry = 0 }} :=
  rippleAdder_xor_spec L.bits L.cin hnd X Y O C

/-- 任意输出初值均可：异或写入模 2^n 的差，恢复输入、相位和进位工作线。 -/
theorem sub_spec (L : AdderLayout) (hnd : L.wires.Nodup) (X Y O : Nat) :
    {{ L.x = X, L.y = Y, L.cin = false, L.out = O, L.carry = 0 }} sub L
    {{ L.x = X, L.y = Y, L.cin = false,
       L.out = (O ^^^ ((X + 2^L.width - Y) % 2^L.width)), L.carry = 0 }} :=
  rippleSubtractor_xor_spec L.bits L.cin hnd X Y O

/-- 已计算的和可以用同一个前向程序再次 XOR 清零，无需反转测量程序。 -/
theorem add_erase_spec (L : AdderLayout) (hnd : L.wires.Nodup) (X Y : Nat) (C : Bool) :
    {{ L.x = X, L.y = Y, L.cin = C,
       L.out = ((X + Y + C.toNat) % 2^L.width), L.carry = 0 }} add L
    {{ L.x = X, L.y = Y, L.cin = C, L.out = 0, L.carry = 0 }} := by
  simpa only [Nat.xor_self] using add_spec L hnd X Y ((X + Y + C.toNat) % 2^L.width) C

/-- 已计算的差可以用同一个前向减法程序再次 XOR 清零。 -/
theorem sub_erase_spec (L : AdderLayout) (hnd : L.wires.Nodup) (X Y : Nat) :
    {{ L.x = X, L.y = Y, L.cin = false,
       L.out = ((X + 2^L.width - Y) % 2^L.width), L.carry = 0 }} sub L
    {{ L.x = X, L.y = Y, L.cin = false, L.out = 0, L.carry = 0 }} := by
  simpa only [Nat.xor_self] using sub_spec L hnd X Y ((X + 2^L.width - Y) % 2^L.width)

/-- 同一加法程序调用两次，对任意输出初值均恢复所有寄存器及相位。 -/
theorem add_twice_spec (L : AdderLayout) (hnd : L.wires.Nodup) (X Y O : Nat) (C : Bool) :
    {{ L.x = X, L.y = Y, L.cin = C, L.out = O, L.carry = 0 }} (add L ++ add L)
    {{ L.x = X, L.y = Y, L.cin = C, L.out = O, L.carry = 0 }} := by
  have h := Triple.seq (add_spec L hnd X Y O C)
    (add_spec L hnd X Y (O ^^^ ((X + Y + C.toNat) % 2^L.width)) C)
  simpa only [Nat.xor_xor_cancel_right] using h

/-- 加法资源公式沿用同一个底层进位程序。 -/
theorem add_resources (L : AdderLayout) (hnd : L.wires.Nodup) :
    toffoliCount (add L) = L.width ∧ measurementCount (add L) = L.width ∧
    qubitCount (add L) = if L.bits.isEmpty then 0 else 4 * L.width + 1 :=
  ⟨rippleAdder_toffoliCount _ _, rippleAdder_measurementCount _ _, rippleAdder_qubitCount _ _ hnd⟩

/-- 减法资源公式沿用同一个底层补码程序。 -/
theorem sub_resources (L : AdderLayout) (hnd : L.wires.Nodup) :
    toffoliCount (sub L) = L.width ∧ measurementCount (sub L) = L.width ∧
    qubitCount (sub L) = 4 * L.width + 1 :=
  ⟨(rippleSubtractor_counts _ _).1, (rippleSubtractor_counts _ _).2,
    rippleSubtractor_qubitCount _ _ hnd⟩

end ECDSAAdd.Arithmetic
