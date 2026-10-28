import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Math.BitcoinPrimes
import Mathlib.Tactic

namespace ECDSAAdd.Arithmetic.BalancedField
open Secp256k1

/-- Radius of the unique balanced secp256k1 representative. -/
def q : Int := ((p : Int)-1)/2
def h : Int := (q+1)/2
def Centered (z : Int) : Prop := -q≤z ∧ z≤q

def centerFp (x : Fp) : Int :=
  if (x.val : Int)≤q then (x.val : Int) else (x.val : Int)-(p : Int)

def canonicalOfCenter (z : Int) : Nat :=
  (if z<0 then z+(p : Int) else z).toNat

def encodeWord (n : Nat) (z : Int) : Nat := (z % ((2^n : Nat) : Int)).toNat

def centerWord (x : Fp) : Nat := encodeWord 256 (centerFp x)
def ValidCenterWord (w : Nat) : Prop := w<2^256 ∧ Centered (signedDecode 256 w)

 theorem constants : 0<q ∧ (p : Int)=2*q+1 ∧ q%2=1 ∧ q=2*h-1 ∧
    0<h ∧ h<((2^254 : Nat) : Int) ∧ q+1<((2^255 : Nat) : Int) := by
  norm_num [q,h,p]

 theorem centerFp_bounds (x : Fp) : Centered (centerFp x) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hv := ZMod.val_lt x
  have hp := constants
  unfold Centered centerFp
  split_ifs <;> omega

 theorem centerFp_cast (x : Fp) : (centerFp x : Fp)=x := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  unfold centerFp
  split_ifs
  · simp
  · simp [Int.cast_sub]

 theorem centered_cast_unique (A B : Int) (ha : Centered A) (hb : Centered B)
    (he : (A : Fp)=(B : Fp)) : A=B := by
  have hp := constants
  have hm := (ZMod.intCast_eq_intCast_iff' A B p).mp he
  have hs : (A+q)%(p : Int)=(B+q)%(p : Int) := by
    calc
      _ = (A%(p : Int)+q%(p : Int))%(p : Int) := Int.add_emod _ _ _
      _ = (B%(p : Int)+q%(p : Int))%(p : Int) := by rw [hm]
      _ = (B+q)%(p : Int) := (Int.add_emod _ _ _).symm
  unfold Centered at ha hb
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hs
  omega

 theorem centerFp_of_center (z : Int) (hz : Centered z) : centerFp (z : Fp)=z :=
  centered_cast_unique _ _ (centerFp_bounds _) hz (centerFp_cast _)

 theorem centered_residue (z : Int) (hz : Centered z) :
    z%(p : Int)=(if z<0 then z+(p : Int) else z) := by
  have hp := constants
  unfold Centered at hz
  by_cases hn : z<0
  · rw [if_pos hn]
    have he : (z+(p : Int))%(p : Int)=z%(p : Int) := by simp
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at he
    exact he.symm
  · rw [if_neg hn]
    exact Int.emod_eq_of_lt (by omega) (by omega)

 theorem canonicalOfCenter_val (z : Int) (hz : Centered z) :
    canonicalOfCenter z=(z : Fp).val := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hv := ZMod.val_intCast z (n := p)
  rw [centered_residue z hz] at hv
  have hn : 0≤(if z<0 then z+(p : Int) else z) := by
    have hp := constants
    unfold Centered at hz
    split_ifs <;> omega
  have ht := Int.toNat_of_nonneg hn
  unfold canonicalOfCenter
  omega

 theorem canonical_center_inverse (x : Fp) : canonicalOfCenter (centerFp x)=x.val := by
  rw [canonicalOfCenter_val _ (centerFp_bounds x),centerFp_cast]

 theorem center_canonical_inverse (z : Int) (hz : Centered z) :
    centerFp (canonicalOfCenter z : Fp)=z := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  rw [canonicalOfCenter_val z hz,ZMod.natCast_zmod_val,centerFp_of_center z hz]

 theorem encodeWord_bound (n : Nat) (z : Int) : encodeWord n z<2^n := by
  have hm0 : 0<((2^n : Nat) : Int) := by positivity
  have hn := Int.emod_nonneg z (ne_of_gt hm0)
  have hh := Int.emod_lt_of_pos z hm0
  have ht := Int.toNat_of_nonneg hn
  unfold encodeWord
  omega

 theorem encodeWord_cast (n : Nat) (z : Int) :
    (encodeWord n z : Int)=z%((2^n : Nat) : Int) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

/-- The word interface is exact on the full signed interval, for any positive width. -/
 theorem decode_encodeWord (n : Nat) (hn : 0<n) (z : Int)
    (hz : -((2^(n-1) : Nat) : Int)≤z ∧ z<((2^(n-1) : Nat) : Int)) :
    signedDecode n (encodeWord n z)=z := by
  let H : Int := (2^(n-1) : Nat)
  let M : Int := (2^n : Nat)
  let D := signedDecode n (encodeWord n z)
  have hd := signedDecode_range n (encodeWord n z) hn (encodeWord_bound n z)
  have hm : D%M=z%M := by
    rw [signedDecode_emod,encodeWord_cast,Int.emod_emod]
  have hpow : M=2*H := by
    dsimp only [M,H]
    have he : n=(n-1)+1 := by omega
    conv_lhs => rw [he,pow_succ]
    push_cast
    ring
  have hs : (D+H)%M=(z+H)%M := by
    calc
      _ = (D%M+H%M)%M := Int.add_emod _ _ _
      _ = (z%M+H%M)%M := by rw [hm]
      _ = (z+H)%M := (Int.add_emod _ _ _).symm
  change -H≤D ∧ D<H at hd
  change -H≤z ∧ z<H at hz
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hs
  change D=z
  omega

 theorem encode_decodeWord (n w : Nat) (hw : w<2^n) :
    encodeWord n (signedDecode n w)=w := by
  unfold encodeWord
  rw [signedDecode_emod,←Int.natCast_emod,Nat.mod_eq_of_lt hw]
  simp

 theorem centerWord_decode (x : Fp) : signedDecode 256 (centerWord x)=centerFp x := by
  apply decode_encodeWord 256 (by omega)
  have hz := centerFp_bounds x
  have hp := constants
  unfold Centered at hz
  norm_num only [Nat.reduceSub]
  omega

 theorem centerWord_valid (x : Fp) : ValidCenterWord (centerWord x) :=
  ⟨encodeWord_bound _ _,by rw [centerWord_decode]; exact centerFp_bounds x⟩

 theorem validCenterWord_inverse (w : Nat) (hw : ValidCenterWord w) :
    centerWord (signedDecode 256 w : Fp)=w := by
  unfold centerWord
  rw [centerFp_of_center _ hw.2,encode_decodeWord _ _ hw.1]

 theorem validCenterWord_unique (w : Nat) (hw : ValidCenterWord w) (x : Fp)
    (he : (signedDecode 256 w : Fp)=x) : w=centerWord x := by
  rw [←he,validCenterWord_inverse w hw]

 theorem centerWord_sign (x : Fp) :
    2^255≤centerWord x ↔ centerFp x<0 := by
  have hh := centerWord_decode x
  have hb := encodeWord_bound 256 (centerFp x)
  unfold centerWord at hh ⊢
  unfold signedDecode at hh
  norm_num only [Nat.reduceSub] at hh
  split_ifs at hh <;> omega

end ECDSAAdd.Arithmetic.BalancedField

#print axioms ECDSAAdd.Arithmetic.BalancedField.q
#print axioms ECDSAAdd.Arithmetic.BalancedField.h
#print axioms ECDSAAdd.Arithmetic.BalancedField.Centered
#print axioms ECDSAAdd.Arithmetic.BalancedField.centerFp
#print axioms ECDSAAdd.Arithmetic.BalancedField.canonicalOfCenter
#print axioms ECDSAAdd.Arithmetic.BalancedField.encodeWord
#print axioms ECDSAAdd.Arithmetic.BalancedField.centerWord
#print axioms ECDSAAdd.Arithmetic.BalancedField.ValidCenterWord
#print axioms ECDSAAdd.Arithmetic.BalancedField.constants
#print axioms ECDSAAdd.Arithmetic.BalancedField.centerFp_bounds
#print axioms ECDSAAdd.Arithmetic.BalancedField.centerFp_cast
#print axioms ECDSAAdd.Arithmetic.BalancedField.centered_cast_unique
#print axioms ECDSAAdd.Arithmetic.BalancedField.centerFp_of_center
#print axioms ECDSAAdd.Arithmetic.BalancedField.centered_residue
#print axioms ECDSAAdd.Arithmetic.BalancedField.canonicalOfCenter_val
#print axioms ECDSAAdd.Arithmetic.BalancedField.canonical_center_inverse
#print axioms ECDSAAdd.Arithmetic.BalancedField.center_canonical_inverse
#print axioms ECDSAAdd.Arithmetic.BalancedField.encodeWord_bound
#print axioms ECDSAAdd.Arithmetic.BalancedField.encodeWord_cast
#print axioms ECDSAAdd.Arithmetic.BalancedField.decode_encodeWord
#print axioms ECDSAAdd.Arithmetic.BalancedField.encode_decodeWord
#print axioms ECDSAAdd.Arithmetic.BalancedField.centerWord_decode
#print axioms ECDSAAdd.Arithmetic.BalancedField.centerWord_valid
#print axioms ECDSAAdd.Arithmetic.BalancedField.validCenterWord_inverse
#print axioms ECDSAAdd.Arithmetic.BalancedField.validCenterWord_unique
#print axioms ECDSAAdd.Arithmetic.BalancedField.centerWord_sign
