import ECDSAAdd.Arithmetic.MontDigit

namespace ECDSAAdd.Arithmetic

theorem mont_drop_value (r : List Wire) (n : Nat) (hn : n≤r.length) (s : BasisState) :
    regValue (r.drop n) s=regValue r s/2^n := by
  have hh := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at hh
  have hl : regValue (r.take n) s<2^n := by
    simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [hh,Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),Nat.div_eq_of_lt hl,Nat.zero_add]

/-- 修改连续一段寄存器时，其余两段由逐线保持决定；历史按小端整数记录。 -/
theorem mont_replace_value (r : List Wire) (n k : Nat) (hn : n+k≤r.length) (hnd : r.Nodup)
    (s t : BasisState) (hkeep : ∀ w∈r, w∉(r.drop n).take k → t w=s w) :
    regValue r t=regValue r s%2^n + 2^n*(regValue ((r.drop n).take k) t+2^k*(regValue r s/2^(n+k))) := by
  have hn' : n≤r.length := by omega
  have hk : k≤(r.drop n).length := by simp only [List.length_drop]; omega
  have hsplit : r=r.take n++((r.drop n).take k++(r.drop n).drop k) := by simp
  have hsN : (r.take n++((r.drop n).take k++(r.drop n).drop k)).Nodup := by rwa [← hsplit]
  have hnA := List.nodup_append'.mp hsN
  have hnB := List.nodup_append'.mp hnA.2.1
  have hpre : regValue (r.take n) t=regValue (r.take n) s := by
    apply regValue_congr; intro w hw
    exact hkeep w ((List.take_sublist n r).subset hw) (fun hh => List.disjoint_left.mp hnA.2.2 hw (List.mem_append_left _ hh))
  have hpost : regValue ((r.drop n).drop k) t=regValue ((r.drop n).drop k) s := by
    apply regValue_congr; intro w hw
    exact hkeep w ((List.drop_sublist k (r.drop n)).trans (List.drop_sublist n r) |>.subset hw) (fun hh => List.disjoint_left.mp hnB.2.2 hh hw)
  have hv := regValue_append (r.take n) ((r.drop n).take k++(r.drop n).drop k) t
  rw [← hsplit,regValue_append,hpre,hpost,List.length_take,Nat.min_eq_left hn',
    List.length_take,Nat.min_eq_left hk,mont_low_value r n hn',List.drop_drop,
    mont_drop_value r (n+k) hn] at hv
  exact hv

/-- 前 k 个四位记录的整数恰为已定义的修正系数 Q_k，始终装得下 k 个窗口。 -/
theorem montgomeryQuotient_bound (p X Y k : Nat) : montgomeryQuotient p X Y k<16^k := by
  induction k with
  | zero => simp [montgomeryQuotient]
  | succ k ih =>
    simp only [montgomeryQuotient,Nat.pow_succ]
    have hm := Nat.mod_lt (montgomeryValue p X Y k+(Y/16^k%16)*X) (by decide : 0<16)
    have hmul := Nat.mul_le_mul_left (16^k) (show (montgomeryValue p X Y k+(Y/16^k%16)*X)%16≤15 by omega)
    omega

end ECDSAAdd.Arithmetic
