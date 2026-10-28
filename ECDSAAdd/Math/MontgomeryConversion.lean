import ECDSAAdd.Math.Montgomery

namespace ECDSAAdd

/-- 64个四位窗口覆盖256位；常数转换乘数用标准余数表示。 -/
def montgomeryRadix : Nat := 16^64

def montgomeryConversion (q : Nat) : Nat := montgomeryRadix^2%q

theorem montgomeryRadix_eq : montgomeryRadix=2^256 := by
  unfold montgomeryRadix
  rw [show (16:Nat)=2^4 from rfl,← Nat.pow_mul]

theorem montgomeryConversion_bound (q : Nat) (hq : 0<q) : montgomeryConversion q<q :=
  Nat.mod_lt _ hq

private theorem montgomery_cast_relation (q X Y : Nat) (hq : q%16=15) (hY : Y<montgomeryRadix) :
    ((montgomeryValue q X Y 64%q : Nat) : ZMod q)*(montgomeryRadix : ZMod q)=
      (X : ZMod q)*(Y : ZMod q) := by
  have hh := congrArg (fun n : Nat => (n : ZMod q)) (montgomeryValue_finish q X Y 64 hq hY)
  simp only [Nat.cast_mul,Nat.cast_add,ZMod.natCast_self,zero_mul,add_zero] at hh
  rw [mul_comm]
  simpa only [montgomeryRadix,ZMod.natCast_mod] using hh

/-- 两段Montgomery准备给出标准表示的乘积，不把表示转换成本藏在接口外。 -/
theorem montgomery_two_stages (q X Y : Nat) [Fact q.Prime]
    (hq : q%16=15) (hqr : q<montgomeryRadix) (hY : Y<montgomeryRadix) :
    montgomeryValue q (montgomeryConversion q) (montgomeryValue q X Y 64%q) 64%q=(X*Y)%q := by
  have hpos : 0<q := Nat.Prime.pos Fact.out
  have htwo : (2 : ZMod q)≠0 := by
    intro hh
    have hd : q∣2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using hh)
    have hle := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  have hr : (montgomeryRadix : ZMod q)≠0 := by
    rw [montgomeryRadix_eq,Nat.cast_pow,Nat.cast_ofNat]
    exact pow_ne_zero _ htwo
  let A := montgomeryValue q X Y 64%q
  let Z := montgomeryValue q (montgomeryConversion q) A 64%q
  have hA : A<q := Nat.mod_lt _ hpos
  have ha := montgomery_cast_relation q X Y hq hY
  have hz := montgomery_cast_relation q (montgomeryConversion q) A hq (lt_trans hA hqr)
  have hae : (A : ZMod q)=(X : ZMod q)*(Y : ZMod q)*(montgomeryRadix : ZMod q)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hr).mpr
    exact ha
  have hze : (Z : ZMod q)=(montgomeryConversion q : ZMod q)*(A : ZMod q)*(montgomeryRadix : ZMod q)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hr).mpr
    exact hz
  have hk : (montgomeryConversion q : ZMod q)=(montgomeryRadix : ZMod q)*(montgomeryRadix : ZMod q) := by
    simp only [montgomeryConversion,ZMod.natCast_mod,pow_two,Nat.cast_mul]
  rw [hk,hae,mul_comm ((montgomeryRadix : ZMod q)*(montgomeryRadix : ZMod q)),
    montgomery_standard_conversion (X : ZMod q) (Y : ZMod q) (montgomeryRadix : ZMod q) hr] at hze
  have hval := congrArg ZMod.val hze
  rw [ZMod.val_natCast,← Nat.cast_mul,ZMod.val_natCast,Nat.mod_eq_of_lt (show Z<q from Nat.mod_lt _ hpos)] at hval
  exact hval

end ECDSAAdd
