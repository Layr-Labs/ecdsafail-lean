import ECDSAAdd.Math.MontgomeryConversion
import ECDSAAdd.Math.KaliskiInverse

namespace ECDSAAdd

/-- 把Montgomery的R补偿直接编入K查表项；表对所有自然数K有定义。 -/
def inverseScaleFactor (q K : Nat) : Nat :=
  ((montgomeryRadix : ZMod q) * ((2 : ZMod q)⁻¹)^K).val

theorem inverseScaleFactor_bound (q K : Nat) (hq : 0<q) : inverseScaleFactor q K<q := by
  letI : NeZero q := ⟨by omega⟩
  exact ZMod.val_lt _

/-- 只要求奇数，不把一般模数偷换成素数域。 -/
theorem inverseScaleFactor_relation (q K : Nat) (ho : q%2=1) :
    (inverseScaleFactor q K : ZMod q)*(2 : ZMod q)^K=(montgomeryRadix : ZMod q) := by
  letI : NeZero q := ⟨by omega⟩
  have hu : IsUnit (2 : ZMod q) :=
    (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ho))
  rw [inverseScaleFactor,ZMod.natCast_zmod_val,mul_assoc,← mul_pow,
    ZMod.inv_mul_of_unit _ hu,one_pow,mul_one]

/-- 一段变量Montgomery就得到普通表示的缩放值，无第二段转换。 -/
theorem montgomery_inverseScaleFactor (q K N : Nat) (hq : q%16=15)
    (hN : N<montgomeryRadix) :
    montgomeryValue q (inverseScaleFactor q K) N 64%q =
      ((N : ZMod q)*((2 : ZMod q)⁻¹)^K).val := by
  have hpos : 0<q := by omega
  letI : NeZero q := ⟨by omega⟩
  have ho : q%2=1 := by omega
  have hu : IsUnit (2 : ZMod q) :=
    (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ho))
  have hr : IsUnit (montgomeryRadix : ZMod q) := by
    simpa only [montgomeryRadix_eq,Nat.cast_pow,Nat.cast_ofNat] using hu.pow 256
  let M := montgomeryValue q (inverseScaleFactor q K) N 64%q
  have rel : (M : ZMod q)*(montgomeryRadix : ZMod q)=
      (inverseScaleFactor q K : ZMod q)*(N : ZMod q) := by
    have h := congrArg (fun n : Nat => (n : ZMod q))
      (montgomeryValue_finish q (inverseScaleFactor q K) N 64 hq hN)
    simp only [Nat.cast_mul,Nat.cast_add,ZMod.natCast_self,zero_mul,add_zero] at h
    simpa only [M,montgomeryRadix,ZMod.natCast_mod,mul_comm] using h
  have he : (M : ZMod q)=(N : ZMod q)*((2 : ZMod q)⁻¹)^K := by
    apply hr.mul_left_inj.mp
    rw [rel,inverseScaleFactor,ZMod.natCast_zmod_val]
    ring
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt (show M<q from Nat.mod_lt _ hpos)] at hv
  exact hv

/-- 固定减半与表因子给出同一规范值，含K=0和K=rounds。 -/
theorem inverseScaleFactor_halving (q K rounds N : Nat) (ho : q%2=1)
    (hN : N<q) (hK : K≤rounds) :
    ((N : ZMod q)*((2 : ZMod q)⁻¹)^K).val=halveFixed q K rounds N := by
  letI : NeZero q := ⟨by omega⟩
  have hh := halveFixed_correct q K rounds N ho hN hK
  have hu : IsUnit (2 : ZMod q) :=
    (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ho))
  have he : (N : ZMod q)*((2 : ZMod q)⁻¹)^K=(halveFixed q K rounds N : ZMod q) := by
    rw [← hh.2,mul_assoc,← mul_pow,ZMod.mul_inv_of_unit _ hu,one_pow,mul_one]
  rw [he,ZMod.val_natCast_of_lt hh.1]

/-- 第一阶段末计数适合十位查表；完整范围含512。 -/
theorem kaliski_scale_count (q X : Nat) (hq : q<2^256) (hx0 : 0<X)
    (hx : X<q) (hcop : q.Coprime X) :
    (kaliskiStep^[512] (kaliskiInit q X)).k≤512 := by
  exact (kaliski_terminates q X 256 (by omega) hx0 hq (hx.trans hq) hcop).2.2

/-- 与原求逆数学陈述对接；新因子加单段Montgomery返回域逆元。 -/
theorem kaliski_montgomery_scale (q X : Nat) (hq16 : q%16=15) (hq : q<2^256)
    (hx0 : 0<X) (hx : X<q) (hcop : q.Coprime X) :
    let z := kaliskiStep^[512] (kaliskiInit q X)
    montgomeryValue q (inverseScaleFactor q z.k) (-(z.r : ZMod q)).val 64%q =
      ((X : ZMod q)⁻¹).val := by
  letI : NeZero q := ⟨by omega⟩
  dsimp only
  have ho : q%2=1 := by omega
  have hn : (-( (kaliskiStep^[512] (kaliskiInit q X)).r : ZMod q)).val<q := ZMod.val_lt _
  rw [montgomery_inverseScaleFactor q _ _ hq16 (hn.trans (by simpa only [montgomeryRadix_eq] using hq)),
    inverseScaleFactor_halving q _ 512 _ ho hn (kaliski_scale_count q X hq hx0 hx hcop)]
  exact kaliski_correct q X 256 ho hq hx0 (hx.trans hq) hcop

end ECDSAAdd
