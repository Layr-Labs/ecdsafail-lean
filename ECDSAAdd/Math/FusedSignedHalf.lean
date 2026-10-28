import ECDSAAdd.Math.BitcoinPrimes
import Mathlib.Tactic

/-!
Exact fused signed half blueprint, derived from the incumbent's signed-sum/fold
architecture (public snapshot 1c185d) and the verified local SignedWord and
SkywalkSignedModAdd interfaces. No finite carry/compare windows are assumed.
-/
namespace ECDSAAdd.FusedSignedHalf
open Secp256k1

def bit (b : Bool) : Int := if b then 1 else 0

def signedSum (b : Bool) (X Y : Nat) : Int := (X : Int)+(if b then -(Y : Int) else (Y : Int))
def parity (s : Int) : Bool := decide (s%2=1)
def reduction (p : Nat) (s : Int) : Bool := decide (¬(0≤s ∧ s<(p : Int)))
def normalizedParity (p : Nat) (s : Int) : Bool := parity s ^^ reduction p s

def correction (p : Nat) (b : Bool) (s : Int) : Int :=
  bit (normalizedParity p s)+(if b then bit (reduction p s) else -bit (reduction p s))
def canonicalSum (p : Nat) (b : Bool) (s : Int) : Int :=
  s+(if b then bit (reduction p s)*(p : Int) else -bit (reduction p s)*(p : Int))
def evenLift (p : Nat) (b : Bool) (s : Int) : Int := s+correction p b s*(p : Int)
def result (p : Nat) (b : Bool) (X Y : Nat) : Nat := (evenLift p b (signedSum b X Y)/2).toNat

def RawDomain (p : Nat) (b : Bool) (s : Int) : Prop :=
  if b then -(p : Int)<s ∧ s<(p : Int) else 0≤s ∧ s<2*(p : Int)

theorem signedSum_domain (p X Y : Nat) (b : Bool) (hX : X<p) (hY : Y<p) :
    RawDomain p b (signedSum b X Y) := by
  cases b <;> simp only [RawDomain,signedSum,Bool.false_eq_true,if_false,if_true] <;> omega

theorem parity_value (s : Int) : s%2=bit (parity s) := by
  by_cases hs : s%2=1
  · simp [parity,bit,hs]
  · have hz : s%2=0 := by omega
    simp [parity,bit,hz]

theorem canonicalSum_bounds (p : Nat) (b : Bool) (s : Int) (hd : RawDomain p b s) :
    0≤canonicalSum p b s ∧ canonicalSum p b s<(p : Int) := by
  cases b
  · simp only [RawDomain,Bool.false_eq_true,if_false] at hd
    by_cases hs : s<(p : Int)
    · simp [canonicalSum,reduction,bit,hd.1,hs]
    · simp [canonicalSum,reduction,bit,hd.1,hs]
      omega
  · simp only [RawDomain,if_true] at hd
    by_cases hs : 0≤s
    · simp [canonicalSum,reduction,bit,hs,hd.2]
    · simp [canonicalSum,reduction,bit,hs]
      omega

theorem evenLift_eq_canonicalSum (p : Nat) (b : Bool) (s : Int) :
    evenLift p b s=canonicalSum p b s+bit (normalizedParity p s)*(p : Int) := by
  cases b <;> simp [evenLift,canonicalSum,correction] <;> ring

/-- The normalized parity is exact even at raw sum zero and modulus boundaries. -/
theorem normalizedParity_value (p : Nat) (b : Bool) (s : Int) (hp : p%2=1) :
    canonicalSum p b s%2=bit (normalizedParity p s) := by
  have hs := parity_value s
  have hpi : (p : Int)%2=1 := by omega
  cases b <;> cases ha : parity s <;> cases hh : reduction p s <;>
    simp only [canonicalSum,normalizedParity,bit,ha,hh,Bool.false_eq_true,if_false,if_true,
      Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] at hs ⊢ <;> omega

/-- The one correction produces an even positive lift below 2p, without wrap assumptions. -/
theorem evenLift_spec (p : Nat) (b : Bool) (s : Int) (hp : p%2=1) (hd : RawDomain p b s) :
    0≤evenLift p b s ∧ evenLift p b s<2*(p : Int) ∧ evenLift p b s%2=0 := by
  have hz := canonicalSum_bounds p b s hd
  have hq := normalizedParity_value p b s hp
  have hpi : (p : Int)%2=1 := by omega
  rw [evenLift_eq_canonicalSum]
  cases he : normalizedParity p s <;> simp only [bit,he,Bool.false_eq_true,if_false,if_true] at hq ⊢ <;> omega

/-- Exact natural representative and doubled-value equation. -/
theorem result_spec (p X Y : Nat) (b : Bool) (hp : p%2=1) (hX : X<p) (hY : Y<p) :
    result p b X Y<p ∧ 2*(result p b X Y : Int)=evenLift p b (signedSum b X Y) := by
  have he := evenLift_spec p b (signedSum b X Y) hp (signedSum_domain p X Y b hX hY)
  have hn : 0≤evenLift p b (signedSum b X Y)/2 := by omega
  have ht := Int.toNat_of_nonneg hn
  simp only [result]
  omega

/-- Copying the raw signed guard gives a quadratic flag with a local phase correction. -/
theorem signedGuard_copy (p : Nat) (b : Bool) (s : Int) (hd : RawDomain p b s) :
    decide (s<0)=(b && reduction p s) := by
  cases b
  · simp only [RawDomain,Bool.false_eq_true,if_false] at hd
    simp [show ¬s<0 by omega]
  · simp only [RawDomain,if_true] at hd
    by_cases hs : s<0
    · simp [reduction,hs,show ¬0≤s by omega]
    · simp [reduction,hs,show 0≤s by omega,hd.2]

/-- Two ANDs plus the signed guard copy give mutually exclusive 0,+p,+2p,-p selectors. -/
theorem selector_identity (b a h : Bool) :
    let j := b && h
    let l := a && h
    let m := a && j
    bit (a ^^ l ^^ m)+2*bit (j ^^ m)-bit (l ^^ m)=bit (a ^^ h)+(if b then bit h else -bit h) := by
  cases b <;> cases a <;> cases h <;> decide

theorem selector_exclusive (b a h : Bool) :
    let j := b && h
    let l := a && h
    let m := a && j
    ((a ^^ l ^^ m) && (j ^^ m))=false ∧
      ((a ^^ l ^^ m) && (l ^^ m))=false ∧ ((j ^^ m) && (l ^^ m))=false := by
  cases b <;> cases a <;> cases h <;> decide

def halfThreshold (p : Nat) : Nat := (p+1)/2

theorem normalizedParity_recovery (p X Y : Nat) (b : Bool) (hp : p%2=1)
    (hX : X<p) (hY : Y<p) :
    normalizedParity p (signedSum b X Y)=decide (halfThreshold p≤result p b X Y) := by
  have hr := result_spec p X Y b hp hX hY
  have hz := canonicalSum_bounds p b (signedSum b X Y) (signedSum_domain p X Y b hX hY)
  have he := evenLift_eq_canonicalSum p b (signedSum b X Y)
  cases hq : normalizedParity p (signedSum b X Y)
  · simp only [bit,hq,Bool.false_eq_true,if_false] at he
    have hl : ¬halfThreshold p≤result p b X Y := by unfold halfThreshold; omega
    simp [hl]
  · simp only [bit,hq,if_true] at he
    have hl : halfThreshold p≤result p b X Y := by unfold halfThreshold; omega
    simp [hl]

/-- The n-bit source-dependent threshold; no source value or source parity is discarded. -/
def threshold (p : Nat) (b q : Bool) (Y : Nat) : Nat :=
  if b then (if q then p-Y/2 else halfThreshold p-(Y/2+Y%2))
  else (if q then halfThreshold p+Y/2 else Y/2+Y%2)

theorem threshold_bounds (p Y : Nat) (b q : Bool) (hp : p%2=1) (hY : Y<p) :
    threshold p b q Y≤p := by
  cases b <;> cases q <;> simp only [threshold,halfThreshold,Bool.false_eq_true,if_false,if_true] <;> omega

/-- Exact recovery of the old normalization flag from output/source and the live normalized parity. -/
theorem reduction_recovery (p X Y R : Nat) (b q h : Bool) (hp : p%2=1)
    (hX : X<p) (hY : Y<p)
    (he : 2*(R : Int)=signedSum b X Y+bit q*(p : Int)+(if b then bit h*(p : Int) else -bit h*(p : Int))) :
    h=(decide (R<threshold p b q Y) ^^ b) := by
  have hi : (R<threshold p b q Y) ↔ (h ^^ b)=true := by
    cases b <;> cases q <;> cases h <;>
      simp [signedSum,bit,threshold,halfThreshold] at he ⊢ <;> omega
  have hb : decide (R<threshold p b q Y)=(h ^^ b) := by
    cases hh : (h ^^ b)
    · have hn : ¬R<threshold p b q Y := by
        intro hc
        have ht := hi.mp hc
        simp [hh] at ht
      simp [hn]
    · have hy : R<threshold p b q Y := hi.mpr hh
      simp [hy]
  calc
    h=((h ^^ b) ^^ b) := by cases h <;> cases b <;> rfl
    _=(decide (R<threshold p b q Y) ^^ b) := congrArg (fun v : Bool => v ^^ b) hb.symm

/-- Integer source constant for the threshold word; its gate load uses two AND selectors. -/
def thresholdConstant (p : Nat) (b q : Bool) (Y : Nat) : Int :=
  bit (b ^^ q)*(halfThreshold p : Int)+bit (b && q)*((p : Int)+1)+
    bit ((!q) && (parity (Y : Int) ^^ b))

theorem threshold_constant_identity (p Y : Nat) (b q : Bool) (hp : p%2=1) (hY : Y<p) :
    (threshold p b q Y : Int)=
      (if b then -1-(Y/2 : Int) else (Y/2 : Int))+thresholdConstant p b q Y := by
  have he := parity_value (Y : Int)
  cases b <;> cases q <;> cases hy : parity (Y : Int) <;>
    simp [threshold,thresholdConstant,halfThreshold,bit,hy] at he ⊢ <;> omega

/-- Fixed-modulus facts that justify the cheap XOR constant load and exact low-three-bit omission. -/
theorem secp_halfThreshold_even : halfThreshold ECDSAAdd.p%2=0 := by
  norm_num [halfThreshold,ECDSAAdd.p]

theorem secp_halfThreshold_multiple_eight : halfThreshold ECDSAAdd.p%8=0 := by
  norm_num [halfThreshold,ECDSAAdd.p]

/-- The even lift is congruent to the raw signed sum for every coefficient. -/
theorem evenLift_cast (p : Nat) (b : Bool) (s : Int) :
    (evenLift p b s : ZMod p)=(s : ZMod p) := by
  simp only [evenLift,Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,mul_zero,add_zero]

private theorem fp_two_nonzero : (2 : Fp)≠0 := by decide

/-- The canonical result is exactly the signed Fp half, including X=0, Y=0 and ties. -/
theorem field_identity (X Y : Nat) (b : Bool) (hX : X<ECDSAAdd.p) (hY : Y<ECDSAAdd.p) :
    (result ECDSAAdd.p b X Y : Fp)=
      ((X : Fp)+(if b then -(Y : Fp) else (Y : Fp)))/2 := by
  have ho : ECDSAAdd.p%2=1 := by norm_num [ECDSAAdd.p]
  have hr := result_spec ECDSAAdd.p X Y b ho hX hY
  have hh := congrArg (fun z : Int => (z : Fp)) hr.2
  simp only [Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] at hh
  rw [evenLift_cast] at hh
  apply (eq_div_iff fp_two_nonzero).mpr
  cases b
  · simpa [signedSum,mul_comm] using hh
  · simpa [signedSum,mul_comm] using hh


end ECDSAAdd.FusedSignedHalf
