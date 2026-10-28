import ECDSAAdd.Arithmetic.BalancedFieldHalf

namespace ECDSAAdd.Arithmetic.BalancedField

def negative (R : Int) : Bool := decide (R<0)
def magnitude (R : Int) : Int := if negative R then -R-1 else R
def signBit (R : Int) : Int := if negative R then 1 else 0
def normalizedR (R : Int) : Int := magnitude R-h+signBit R
def viewedY (s : Bool) (R Y : Int) : Int := if s ^^ negative R then -Y-1 else Y
def insertBit (s : Bool) (R : Int) : Int := if !(s ^^ negative R) then 1 else 0
def comparisonLeft (s : Bool) (R : Int) : Int := 2*normalizedR R+insertBit s R

 theorem magnitude_bounds (R : Int) (hr : Centered R) : 0≤magnitude R ∧ magnitude R≤q := by
  unfold Centered at hr
  by_cases hn : R<0 <;> simp [magnitude,negative,hn] <;> omega

 theorem normalizedR_bounds (R : Int) (hr : Centered R) :
    -h≤normalizedR R ∧ normalizedR R<h := by
  have hp := constants
  unfold Centered at hr
  by_cases hn : R<0 <;> simp [normalizedR,magnitude,signBit,negative,hn] <;> omega

 theorem normalizedR_lowword_decode (R : Int) (hr : Centered R) :
    signedDecode 255 (encodeWord 255 (normalizedR R))=normalizedR R := by
  apply decode_encodeWord 255 (by omega)
  have hb := normalizedR_bounds R hr
  have hp := constants
  norm_num only [Nat.reduceSub]
  omega

 theorem comparison_view_bounds (s : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) :
    -(q+1)≤comparisonLeft s R ∧ comparisonLeft s R≤q ∧
    -(q+1)≤viewedY s R Y ∧ viewedY s R Y≤q := by
  have hb := normalizedR_bounds R hr
  have hp := constants
  unfold Centered at hr hy
  cases s <;> by_cases hn : R<0 <;>
    simp [comparisonLeft,normalizedR,magnitude,signBit,insertBit,viewedY,negative,hn] <;> omega

/-- Full-domain direct interval identity, including strict endpoint ties. -/
 theorem cleanup_interval_identity (s : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) :
    q < |2*R-signedY s Y| ↔ viewedY s R Y<comparisonLeft s R := by
  have hp := constants
  have hle : |2*R-signedY s Y|≤q ↔ -q≤2*R-signedY s Y ∧ 2*R-signedY s Y≤q := abs_le
  have hout : q < |2*R-signedY s Y| ↔
      ¬(-q≤2*R-signedY s Y ∧ 2*R-signedY s Y≤q) := by omega
  rw [hout]
  unfold Centered at hr hy
  cases s <;> by_cases hn : R<0 <;>
    simp [comparisonLeft,normalizedR,magnitude,signBit,insertBit,viewedY,negative,signedY,hn] <;> omega

 theorem cleanup_originalParity (s : Bool) (X Y : Int)
    (hx : Centered X) (hy : Centered Y) :
    originalParity (rawSum s X Y)=
      decide (viewedY s (halfResult (rawSum s X Y)) Y<
        comparisonLeft s (halfResult (rawSum s X Y))) := by
  have hr := (halfResult_spec _ (rawSum_bounds s X Y hx hy)).1
  have hi := (halfResult_parity_interval s X Y hx hy).trans
    (cleanup_interval_identity s _ Y hr hy)
  by_cases ht : rawSum s X Y%2≠0
  · have hc := hi.mp ht
    simp [originalParity,ht,hc]
  · have hc : ¬viewedY s (halfResult (rawSum s X Y)) Y<
        comparisonLeft s (halfResult (rawSum s X Y)) := fun hc => ht (hi.mpr hc)
    simp [originalParity,ht,hc]

/-- The low(n−1) adder computes the exact normalized residue; its dividend
is nonnegative and the subtraction cannot underflow. -/
 theorem normalizedR_lowword_arithmetic (R : Int) (hr : Centered R) :
    h.toNat≤(magnitude R).toNat+2^255 ∧
    encodeWord 255 (normalizedR R)=
      (((magnitude R).toNat+2^255-h.toNat+(negative R).toNat)%2^255) := by
  have hb := magnitude_bounds R hr
  have hp := constants
  have hm := Int.toNat_of_nonneg hb.1
  have hh := Int.toNat_of_nonneg (show 0≤h by omega)
  have hsafe : h.toNat≤(magnitude R).toNat+2^255 := by
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hm hh ⊢
    omega
  refine ⟨hsafe,?_⟩
  have hbit : ((negative R).toNat : Int)=signBit R := by
    cases he : negative R <;> simp [signBit,he]
  apply Int.ofNat_inj.mp
  rw [encodeWord_cast,Int.natCast_emod]
  rw [Nat.cast_add,Nat.cast_sub hsafe,Nat.cast_add,hm,hh,hbit]
  have he : magnitude R+((2^255 : Nat) : Int)-h+signBit R=
      normalizedR R+((2^255 : Nat) : Int) := by unfold normalizedR; ring
  rw [he]
  simp

 theorem comparison_words_decode (s : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) :
    signedDecode 256 (encodeWord 256 (comparisonLeft s R))=comparisonLeft s R ∧
    signedDecode 256 (encodeWord 256 (viewedY s R Y))=viewedY s R Y := by
  have hb := comparison_view_bounds s R Y hr hy
  have hp := constants
  constructor <;> apply decode_encodeWord 256 (by omega) <;>
    norm_num only [Nat.reduceSub] <;> omega

end ECDSAAdd.Arithmetic.BalancedField

#print axioms ECDSAAdd.Arithmetic.BalancedField.negative
#print axioms ECDSAAdd.Arithmetic.BalancedField.magnitude
#print axioms ECDSAAdd.Arithmetic.BalancedField.signBit
#print axioms ECDSAAdd.Arithmetic.BalancedField.normalizedR
#print axioms ECDSAAdd.Arithmetic.BalancedField.viewedY
#print axioms ECDSAAdd.Arithmetic.BalancedField.insertBit
#print axioms ECDSAAdd.Arithmetic.BalancedField.comparisonLeft
#print axioms ECDSAAdd.Arithmetic.BalancedField.magnitude_bounds
#print axioms ECDSAAdd.Arithmetic.BalancedField.normalizedR_bounds
#print axioms ECDSAAdd.Arithmetic.BalancedField.normalizedR_lowword_decode
#print axioms ECDSAAdd.Arithmetic.BalancedField.comparison_view_bounds
#print axioms ECDSAAdd.Arithmetic.BalancedField.cleanup_interval_identity
#print axioms ECDSAAdd.Arithmetic.BalancedField.cleanup_originalParity
#print axioms ECDSAAdd.Arithmetic.BalancedField.normalizedR_lowword_arithmetic
#print axioms ECDSAAdd.Arithmetic.BalancedField.comparison_words_decode
