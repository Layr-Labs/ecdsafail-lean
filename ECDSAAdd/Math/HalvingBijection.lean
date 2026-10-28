import ECDSAAdd.Math.ModularHalving

namespace ECDSAAdd

/-- 规范代表元上的模加倍撤销模减半。 -/
theorem double_halve_mod (p r : Nat) (hp : p%2=1) (hr : r<p) :
    (2 * halveMod p r) % p = r := by
  unfold halveMod
  split_ifs with he
  · have hh : 2*(r/2) = r := by omega
    rw [hh, Nat.mod_eq_of_lt hr]
  · have hh : 2*((r+p)/2) = r+p := by omega
    rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

/-- 规范代表元上的模减半撤销模加倍。 -/
theorem halve_double_mod (p r : Nat) (hp : p%2=1) (hr : r<p) :
    halveMod p ((2*r)%p) = r := by
  by_cases h : 2*r<p
  · rw [Nat.mod_eq_of_lt h]
    simp [halveMod]
  · have hb : 2*r-p<p := by omega
    have hm : (2*r)%p = 2*r-p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hb]
    have ho : (2*r-p)%2 ≠ 0 := by omega
    rw [hm, halveMod, if_neg ho]
    omega

end ECDSAAdd
