import ECDSAAdd.Arithmetic.BalancedCleanupOffsetProgram
import ECDSAAdd.Arithmetic.BalancedCleanupCircuitViews

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
open BalancedField BalancedCircuit Secp256k1

/-- The unnormalized R word after prepareSign and the Clifford view. -/
def rawR (B : Bool) (R : Int) : Nat :=
  2*(magnitude R).toNat+(!(B ^^ negative R)).toNat

/-- Only Y receives the signed-to-unsigned top-bit bias. -/
def biasedY (B : Bool) (R Y : Int) : Nat :=
  (viewedY B R Y+((2^255 : Nat) : Int)).toNat

theorem offset_value : offset=2^31+488 := by norm_num [offset,sparseF]

/-- The bias omitted from R is exactly J. In particular h has scale 2^254. -/
theorem offset_relation : (offset : Int)=((2^255 : Nat) : Int)-2*h := by
  norm_num [offset,sparseF,h,q,p]

theorem offset_safety : 0 < offset ∧
    2*q+(offset : Int)+3 < ((2^256 : Nat) : Int) := by
  norm_num [offset,sparseF,q,p]

theorem insertedBit_cast (B : Bool) (R : Int) :
    ((!(B ^^ negative R)).toNat : Int)=insertBit B R := by
  cases hb : !(B ^^ negative R) <;> simp [insertBit,hb]

theorem negativeBit_cast (R : Int) :
    ((negative R).toNat : Int)=signBit R := by
  cases hb : negative R <;> simp [signBit,hb]

theorem insertedBit_bounds (B : Bool) (R : Int) :
    0 ≤ insertBit B R ∧ insertBit B R ≤ 1 := by
  unfold insertBit
  split_ifs <;> omega

theorem negativeBit_bounds (R : Int) :
    0 ≤ ((negative R).toNat : Int) ∧ ((negative R).toNat : Int) ≤ 1 := by
  cases hb : negative R <;> simp

theorem rawR_cast (B : Bool) (R : Int) (hr : Centered R) :
    (rawR B R : Int)=2*magnitude R+insertBit B R := by
  have hm := magnitude_bounds R hr
  simp only [rawR,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    Int.toNat_of_nonneg hm.1,insertedBit_cast]

/-- The offset addition is an ordinary unsigned sum on the entire centered
domain. Its physical modulo never wraps, including all endpoint ties. -/
theorem threshold_no_wrap (B : Bool) (R : Int) (hr : Centered R) :
    rawR B R+offset+2*(negative R).toNat < 2^256 := by
  have hm := magnitude_bounds R hr
  have hi := insertedBit_bounds B R
  have hn := negativeBit_bounds R
  have hs := offset_safety
  have limit : ((rawR B R+offset+2*(negative R).toNat : Nat) : Int) < ((2^256 : Nat) : Int) := by
    push_cast
    rw [rawR_cast B R hr]
    omega
  exact_mod_cast limit

theorem threshold_value (B : Bool) (R : Int) (hr : Centered R) :
    (((rawR B R+offset+2*(negative R).toNat)%2^256 : Nat) : Int)=
      comparisonLeft B R+((2^255 : Nat) : Int) := by
  rw [Nat.mod_eq_of_lt (threshold_no_wrap B R hr)]
  push_cast
  rw [rawR_cast B R hr,offset_relation,negativeBit_cast]
  unfold comparisonLeft normalizedR
  ring

theorem biasedY_bounds (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    0 ≤ viewedY B R Y+((2^255 : Nat) : Int) ∧
    viewedY B R Y+((2^255 : Nat) : Int) < ((2^256 : Nat) : Int) := by
  have bounds := comparison_view_bounds B R Y hr hy
  have hc := BalancedField.constants
  norm_num only [Nat.reducePow] at bounds hc ⊢
  omega

theorem biasedY_cast (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    (biasedY B R Y : Int)=viewedY B R Y+((2^255 : Nat) : Int) :=
  Int.toNat_of_nonneg (biasedY_bounds B R Y hr hy).1

theorem biasedY_word_bound (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    biasedY B R Y < 2^256 := by
  have hb := (biasedY_bounds B R Y hr hy).2
  rw [←biasedY_cast B R Y hr hy] at hb
  exact_mod_cast hb

/-- Exact full-domain replacement predicate for the actual offsetCarry
comparator. The proof covers both B values and both signs of R. -/
theorem comparison_predicate (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    biasedY B R Y < (rawR B R+offset+2*(negative R).toNat)%2^256 ↔
      q < |2*R-signedY B Y| := by
  have cast : biasedY B R Y < (rawR B R+offset+2*(negative R).toNat)%2^256 ↔
      (biasedY B R Y : Int) < (((rawR B R+offset+2*(negative R).toNat)%2^256 : Nat) : Int) := by omega
  rw [cast,biasedY_cast B R Y hr hy,threshold_value B R hr]
  have interval := cleanup_interval_identity B R Y hr hy
  constructor
  · intro hcmp
    apply interval.mpr
    omega
  · intro hout
    have hcmp := interval.mp hout
    omega

/-- Chain's mapped constant is J+2*Lower, with One=0. Addition order
agrees exactly with its already proved full-width arithmetic predicate. -/
theorem chain_predicate (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    biasedY B R Y < (offset+2*(negative R).toNat+rawR B R)%2^256 ↔
      q < |2*R-signedY B Y| := by
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    comparison_predicate B R Y hr hy

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.threshold_no_wrap
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.threshold_value
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.biasedY_cast
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.comparison_predicate
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.chain_predicate
