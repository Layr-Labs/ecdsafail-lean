import ECDSAAdd.Math.KaliskiInverse
import ECDSAAdd.Math.HalvingBijection

namespace ECDSAAdd

/-- v首次归零的分支将r加倍；其后的恒等轮保持偶数。 -/
theorem kaliski_terminal_even (q a t : Nat) :
    let z := kaliskiStep^[t] (kaliskiInit q a)
    z.v=0 → z.r%2=0 := by
  dsimp only
  induction t with
  | zero => simp [kaliskiInit]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    let z := kaliskiStep^[t] (kaliskiInit q a)
    change z.v=0 → z.r%2=0 at ih
    change (kaliskiStep z).v=0 → (kaliskiStep z).r%2=0
    unfold kaliskiStep
    split_ifs with hv hu he hc
    · exact ih
    · simp only; omega
    · simp
    · simp only; omega
    · simp

/-- 终态常量可清零出借，r保留可逆取负所需的正偶范围。 -/
theorem kaliski_terminal_values (q a n : Nat) (hq1 : 1<q) (ho : q%2=1)
    (hq : q<2^n) (ha0 : 0<a) (ha : a<q) (hcop : q.Coprime a) :
    let z := kaliskiStep^[2*n] (kaliskiInit q a)
    z.u=1 ∧ z.v=0 ∧ z.s=q ∧ 0<z.r ∧ z.r<2*q ∧ z.r%2=0 := by
  letI : NeZero q := ⟨by omega⟩
  letI : Fact (1<q) := ⟨hq1⟩
  let z := kaliskiStep^[2*n] (kaliskiInit q a)
  have ht := kaliski_terminates q a n (by omega) ha0 hq (ha.trans hq) hcop
  have hi := kaliski_iterate_invariant q a (2*n) _ (kaliski_init_invariant q a (by omega) hcop)
  have hb := kaliski_register_bounds q a (2*n) (by omega) hcop
  have hs : z.s=q := by
    have he := hi.2.2.1
    change z.u*z.s+z.v*z.r=q at he
    rw [ht.1,ht.2.1] at he
    simpa using he
  have hr : 0<z.r := by
    have hu : IsUnit (2 : ZMod q) :=
      (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ho))
    have hn := (hu.pow z.k).ne_zero
    have he := hi.2.2.2.2.1
    change (a : ZMod q)*z.r=-(z.u : ZMod q)*2^z.k at he
    rw [ht.2.1] at he
    by_contra hh
    have hz : z.r=0 := by omega
    simp [hz] at he
    exact hn he
  exact ⟨ht.2.1,ht.1,hs,hr,hb.2.2.1,kaliski_terminal_even q a (2*n) ht.1⟩

/-- 正偶系数先除2，再取负加倍；规范值保留完整系数的可恢复性。 -/
theorem negative_even_value (q R : Nat) (hR : 0<R)
    (hb : R<2*q) (he : R%2=0) :
    0<R/2 ∧ R/2<q ∧ q-R/2<q ∧
    (2*(q-R/2))%q = (-(R : ZMod q)).val := by
  have hh : 2*(R/2)=R := by omega
  have hr : R/2<q := by omega
  have hz : ((2*(q-R/2) : Nat) : ZMod q)=-(R : ZMod q) := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : R/2≤q),ZMod.natCast_self]
    have hc := congrArg (fun n : Nat => (n : ZMod q)) hh
    push_cast at hc
    linear_combination -hc
  have hv := congrArg ZMod.val hz
  rw [ZMod.val_natCast] at hv
  exact ⟨by omega,hr,by omega,hv⟩

/-- 模减半、取负再左旋精确恢复原始R，而非仅恢复R mod q。 -/
theorem negative_even_restore (q R : Nat) (ho : q%2=1) (hR : 0<R)
    (hb : R<2*q) (he : R%2=0) :
    halveMod q (-(R : ZMod q)).val=q-R/2 ∧
    2*(q-halveMod q (-(R : ZMod q)).val)=R := by
  have hv := negative_even_value q R hR hb he
  have hh := halve_double_mod q (q-R/2) ho hv.2.2.1
  rw [hv.2.2.2] at hh
  exact ⟨hh,by rw [hh]; omega⟩

end ECDSAAdd
