import ECDSAAdd.Math.HalvingBijection

namespace ECDSAAdd

/-- 第 i 位处理之前的乘积前缀；i=n 时为零，i=0 时为完整乘积。 -/
def hornerValue (p X Y i : Nat) : Nat := (X*(Y/2^i))%p

theorem hornerValue_bound (p X Y i : Nat) (hp : 0<p) : hornerValue p X Y i<p :=
  Nat.mod_lt _ hp

theorem hornerValue_start (p X Y n : Nat) (hY : Y<2^n) : hornerValue p X Y n=0 := by
  simp [hornerValue,Nat.div_eq_of_lt hY]

theorem hornerValue_finish (p X Y : Nat) : hornerValue p X Y 0=(X*Y)%p := by
  simp [hornerValue]

/-- 逐位 Horner：先将高位前缀加倍，再按当前位加 X。 -/
theorem hornerValue_step (p X Y i : Nat) :
    (2*hornerValue p X Y (i+1)+X*((Y/2^i)%2))%p=hornerValue p X Y i := by
  have hd : Y/2^i=2*(Y/2^(i+1))+(Y/2^i)%2 := by
    rw [Nat.pow_succ,← Nat.div_div_eq_div_mul]
    omega
  unfold hornerValue
  conv_rhs => rw [hd]
  have he : X*(2*(Y/2^(i+1))+(Y/2^i)%2)=
      2*(X*(Y/2^(i+1)))+X*((Y/2^i)%2) := by ring
  rw [he]
  simp [Nat.add_mod,Nat.mul_mod]

/-- 减去本位贡献再模减半，恢复上一前缀；不用倒放带测量的门列。 -/
theorem hornerValue_unstep (p X Y i : Nat) (hp : p%2=1) (hX : X<p) :
    halveMod p ((hornerValue p X Y i+p-X*((Y/2^i)%2))%p)=hornerValue p X Y (i+1) := by
  have hpos : 0<p := by omega
  have hb : X*((Y/2^i)%2)≤p := by
    have hh := Nat.mod_lt (Y/2^i) (by decide : 0<2)
    have hle : (Y/2^i)%2≤1 := by omega
    have hm := Nat.mul_le_mul_left X hle
    omega
  have hs := hornerValue_step p X Y i
  have he : hornerValue p X Y i+p-X*((Y/2^i)%2)=
      hornerValue p X Y i+(p-X*((Y/2^i)%2)) := by omega
  rw [he,← hs,Nat.mod_add_mod]
  have hc : 2*hornerValue p X Y (i+1)+X*((Y/2^i)%2)+(p-X*((Y/2^i)%2))=
      2*hornerValue p X Y (i+1)+p := by omega
  rw [hc,Nat.add_mod_right]
  exact halve_double_mod p _ hp (hornerValue_bound p X Y (i+1) hpos)

end ECDSAAdd
