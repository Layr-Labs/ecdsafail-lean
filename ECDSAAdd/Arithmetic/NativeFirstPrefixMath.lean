import ECDSAAdd.Math.SkywalkTrace
import ECDSAAdd.Math.BitcoinCurve

set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstPrefixMath
open SkywalkRails Secp256k1

/-- Mathematical input parity, matching the low bit of the canonical x word. -/
def oddBit (x : Int) : Bool := decide (x%2≠0)
def hValue (prime x : Int) : Int := x/2+(if oddBit x then (prime+1)/2 else 0)
def kValue (prime x : Int) : Int := if oddBit x then (x-prime)/2 else prime+x/2

def directTick (prime x : Int) : SkywalkRails.Tick :=
  ⟨hValue prime x,kValue prime x,!(oddBit x),oddBit x⟩

/-- This is the incumbent seeded state, not the rejected alternative(2x,p). -/
def initp (x : Nat) : SkywalkRails.State :=
  SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)

private theorem split_half (prime x : Int) (hp : prime%2=1) (hx : x%2≠0) :
    (x+prime)/2=x/2+(prime+1)/2 := by omega

/-- Exact original first signed tick: strict x<prime fixes the odd sign record. -/
theorem direct_step (prime x : Int) (hp : 0<prime) (hpo : prime%2=1)
    (hx0 : 0≤x) (hx : x<prime) :
    SkywalkRails.step (SkywalkRails.encode false false x prime)=directTick prime x := by
  by_cases he : x%2=0
  · rw [SkywalkRails.step_encode_even false false x prime hx0 hp hpo he]
    simp [directTick,hValue,kValue,oddBit,he,SkywalkRails.signed,add_comm]
  · rw [SkywalkRails.step_encode_odd false false x prime hx0 hp hpo he]
    have half := split_half prime x hpo he
    simp [directTick,hValue,kValue,oddBit,he,hx,half]

/-- Canonical H and signed K ranges are stated on the whole original domain. -/
theorem direct_bounds (prime x : Int) (hp : 0<prime) (hpo : prime%2=1)
    (hx0 : 0≤x) (hx : x<prime) :
    0≤hValue prime x ∧ hValue prime x<prime ∧
    -prime<kValue prime x ∧ kValue prime x<2*prime := by
  by_cases he : x%2=0
  · simp only [hValue,kValue,oddBit,he,ne_self_iff_false,decide_false,
      Bool.false_eq_true,if_false,add_zero]
    omega
  · have half := split_half prime x hpo he
    simp only [hValue,kValue,oddBit,he,not_false_eq_true,decide_true,if_true]
    omega

/-- No fabricated negative zero: H is nonnegative and K is negative exactly
on the odd input branch. G and S are the original first transcript values. -/
theorem direct_signs (prime x : Int) (hp : 0<prime) (hpo : prime%2=1)
    (hx0 : 0≤x) (hx : x<prime) :
    SkywalkRails.neg (hValue prime x)=false ∧
      SkywalkRails.neg (kValue prime x)=oddBit x := by
  have bounds := direct_bounds prime x hp hpo hx0 hx
  constructor
  · simp only [SkywalkRails.neg,show ¬hValue prime x<0 from by omega,decide_false]
  · by_cases he : x%2=0
    · have positive : 0<kValue prime x := by
        simp only [kValue,oddBit,he,ne_self_iff_false,decide_false,Bool.false_eq_true,if_false]
        omega
      simp [SkywalkRails.neg,oddBit,he,show ¬kValue prime x<0 from by omega]
    · have negative : kValue prime x<0 := by
        have literal : (x-prime)/2<0 := by omega
        simpa [kValue,oddBit,he] using literal
      simp [SkywalkRails.neg,oddBit,he,negative]

/-- The exact first tick's native orientation frame is inherited, not assumed. -/
theorem direct_frame (prime x : Int) (hp : 0<prime) (hpo : prime%2=1)
    (hx0 : 0≤x) (hx : x<prime) : SkywalkRails.Frame (directTick prime x) := by
  rw [←direct_step prime x hp hpo hx0 hx]
  exact SkywalkRails.step_frame false false x prime hx0 hp hpo

/-- Mathematical inverse reconstruction only. This does not erase a register
for free or replace the independently emitted measured inverse circuit. -/
theorem recover_x (prime x : Int) (_hp : 0<prime) (hpo : prime%2=1)
    (_hx0 : 0≤x) (_hx : x<prime) :
    (if oddBit x then 2*kValue prime x+prime else 2*hValue prime x)=x := by
  by_cases he : x%2=0
  · simp only [hValue,kValue,oddBit,he,ne_self_iff_false,decide_false,
      Bool.false_eq_true,if_false,add_zero]
    omega
  · have hxodd : x%2=1 := by omega
    have hd : (x-prime)%2=0 := by
      rw [Int.sub_emod,hxodd,hpo]
      norm_num
    have literal : 2*((x-prime)/2)+prime=x := by omega
    simpa [hValue,kValue,oddBit,he] using literal

private theorem prime_positive : 0<(ECDSAAdd.p : Int) := by norm_num [ECDSAAdd.p]
private theorem prime_odd : (ECDSAAdd.p : Int)%2=1 := by norm_num [ECDSAAdd.p]
private theorem prime_word_bound : (ECDSAAdd.p : Int)<(2^256 : Int) := by norm_num [ECDSAAdd.p]

/-- Closed equality against the actual incumbent secp seed/first tick. -/
theorem secp_first_step (x : Nat) (hx : x<ECDSAAdd.p) :
    SkywalkRails.step (initp x)=directTick (ECDSAAdd.p : Int) (x : Int) := by
  unfold initp
  exact direct_step _ _ prime_positive prime_odd (by omega) (by exact_mod_cast hx)

/-- H fits the n=256 output slice. K fits the native n+2 signed register;
all guard-bit/value claims still require the actual circuit frame theorem. -/
theorem secp_word_bounds (x : Nat) (hx : x<ECDSAAdd.p) :
    0≤hValue (ECDSAAdd.p : Int) (x : Int) ∧
      hValue (ECDSAAdd.p : Int) (x : Int)<(2^256 : Int) ∧
      -(2^257 : Int)<kValue (ECDSAAdd.p : Int) (x : Int) ∧
      kValue (ECDSAAdd.p : Int) (x : Int)<(2^257 : Int) := by
  have b := direct_bounds (ECDSAAdd.p : Int) (x : Int) prime_positive prime_odd
    (by omega) (by exact_mod_cast hx)
  have p := prime_word_bound
  constructor
  · exact b.1
  constructor
  · omega
  constructor <;> omega

/-- The zero input is covered by the prototype contract and preserves the
unique terminal sign, even though the point caller's divisor is nonzero. -/
theorem secp_zero : directTick (ECDSAAdd.p : Int) 0=⟨0,(ECDSAAdd.p : Int),true,false⟩ := by
  simp [directTick,hValue,kValue,oddBit]

end ECDSAAdd.Arithmetic.NativeFirstPrefixMath
#print axioms ECDSAAdd.Arithmetic.NativeFirstPrefixMath.direct_step
#print axioms ECDSAAdd.Arithmetic.NativeFirstPrefixMath.direct_bounds
#print axioms ECDSAAdd.Arithmetic.NativeFirstPrefixMath.direct_signs
#print axioms ECDSAAdd.Arithmetic.NativeFirstPrefixMath.direct_frame
#print axioms ECDSAAdd.Arithmetic.NativeFirstPrefixMath.recover_x
#print axioms ECDSAAdd.Arithmetic.NativeFirstPrefixMath.secp_first_step
#print axioms ECDSAAdd.Arithmetic.NativeFirstPrefixMath.secp_word_bounds
#print axioms ECDSAAdd.Arithmetic.NativeFirstPrefixMath.secp_zero
