import ECDSAAdd.Arithmetic.BalancedFieldABI

namespace ECDSAAdd.Arithmetic.BalancedField
open Secp256k1

def signedY (s : Bool) (Y : Int) : Int := if s then -Y else Y
def rawSum (s : Bool) (X Y : Int) : Int := X+signedY s Y
def originalParity (T : Int) : Bool := decide (T%2≠0)

/-- Odd sums are translated by one modulus so their halves are balanced. -/
def evenLift (T : Int) : Int :=
  if T%2=0 then T else if 0≤T then T-(p : Int) else T+(p : Int)
def halfResult (T : Int) : Int := evenLift T/2

 theorem signedY_bounds (s : Bool) (Y : Int) (hy : Centered Y) : Centered (signedY s Y) := by
  cases s <;> simp only [signedY,Bool.false_eq_true,if_false,if_true] <;>
    unfold Centered at hy ⊢ <;> omega

 theorem rawSum_bounds (s : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    -(2*q)≤rawSum s X Y ∧ rawSum s X Y≤2*q := by
  have hs := signedY_bounds s Y hy
  unfold Centered at hx hs
  unfold rawSum
  omega

 theorem evenLift_spec (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    -(2*q)≤evenLift T ∧ evenLift T≤2*q ∧ evenLift T%2=0 := by
  have hp := constants
  unfold evenLift
  split_ifs <;> omega

 theorem halfResult_spec (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    Centered (halfResult T) ∧ 2*halfResult T=evenLift T := by
  have he := evenLift_spec T ht
  unfold halfResult Centered
  omega

 theorem evenLift_cast (T : Int) : (evenLift T : Fp)=(T : Fp) := by
  unfold evenLift
  split_ifs <;> simp [Int.cast_sub,Int.cast_add]

 theorem originalParity_value (T : Int) : T%2=(if originalParity T then 1 else 0) := by
  by_cases he : T%2=0
  · simp [originalParity,he]
  · simp [originalParity,he]
    omega

 theorem halfResult_sign (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    decide (halfResult T<0)=(decide (T<0) ^^ originalParity T) := by
  classical
  have hd := (halfResult_spec T ht).2
  have hp := constants
  by_cases ho : T%2=0
  · rw [evenLift,if_pos ho] at hd
    have he : (halfResult T<0) ↔ T<0 := by omega
    simpa [originalParity,ho] using congrArg (fun P : Prop => decide P) (propext he)
  · rw [evenLift,if_neg ho] at hd
    by_cases hn : T<0
    · rw [if_neg (show ¬0≤T by omega)] at hd
      have hr : ¬halfResult T<0 := by omega
      simp [originalParity,ho,hn,hr]
    · rw [if_pos (show 0≤T by omega)] at hd
      have hr : halfResult T<0 := by omega
      simp [originalParity,ho,hn,hr]

 theorem halfResult_field (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    (halfResult T : Fp)=(T : Fp)/2 := by
  have hd := (halfResult_spec T ht).2
  have hc := congrArg (fun z : Int => (z : Fp)) hd
  change ((2*halfResult T : Int) : Fp)=((evenLift T : Int) : Fp) at hc
  rw [Int.cast_mul,Int.cast_ofNat,evenLift_cast] at hc
  have htwo : (2 : Fp)≠0 := by decide
  apply (eq_div_iff htwo).mpr
  simpa only [mul_comm] using hc

 theorem halfResult_center (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    halfResult T=centerFp ((T : Fp)/2) := by
  rw [←halfResult_field T ht,centerFp_of_center _ (halfResult_spec T ht).1]

/-- Exact signed-half result on every balanced input pair and either sign. -/
 theorem signedHalf_contract (s : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y) :
    Centered (halfResult (rawSum s X Y)) ∧
    halfResult (rawSum s X Y)=
      centerFp (((X : Fp)+(if s then -(Y : Fp) else (Y : Fp)))/2) ∧
    2*halfResult (rawSum s X Y)=evenLift (rawSum s X Y) := by
  have hr := halfResult_spec (rawSum s X Y) (rawSum_bounds s X Y hx hy)
  refine ⟨hr.1,?_,hr.2⟩
  have hc := halfResult_center (rawSum s X Y) (rawSum_bounds s X Y hx hy)
  cases s <;> simpa [rawSum,signedY] using hc

/-- The original oddness can be recovered from the updated payload and
unchanged source. No sampling, carry window or convergence assumption appears. -/
 theorem halfResult_parity_interval (s : Bool) (X Y : Int)
    (hx : Centered X) (hy : Centered Y) :
    (rawSum s X Y%2≠0) ↔ q < |2*halfResult (rawSum s X Y)-signedY s Y| := by
  have hd := (halfResult_spec _ (rawSum_bounds s X Y hx hy)).2
  have hp := constants
  have hs : rawSum s X Y=X+signedY s Y := rfl
  unfold Centered at hx
  by_cases ho : rawSum s X Y%2=0
  · rw [evenLift,if_pos ho] at hd
    have hv : 2*halfResult (rawSum s X Y)-signedY s Y=X := by
      omega
    rw [hv]
    have ha : |X|≤q := abs_le.mpr hx
    omega
  · rw [evenLift,if_neg ho] at hd
    by_cases hn : 0≤rawSum s X Y
    · rw [if_pos hn] at hd
      have hv : 2*halfResult (rawSum s X Y)-signedY s Y=X-(p : Int) := by
        omega
      rw [hv,abs_of_neg (show X-(p : Int)<0 by omega)]
      omega
    · rw [if_neg hn] at hd
      have hv : 2*halfResult (rawSum s X Y)-signedY s Y=X+(p : Int) := by
        omega
      rw [hv,abs_of_nonneg (show 0≤X+(p : Int) by omega)]
      omega

 theorem centeredFp_signedHalf (s : Bool) (X Y : Fp) :
    halfResult (rawSum s (centerFp X) (centerFp Y))=
      centerFp ((X+(if s then -Y else Y))/2) := by
  have hh := (signedHalf_contract s (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y)).2.1
  simpa only [centerFp_cast] using hh

end ECDSAAdd.Arithmetic.BalancedField

#print axioms ECDSAAdd.Arithmetic.BalancedField.signedY
#print axioms ECDSAAdd.Arithmetic.BalancedField.rawSum
#print axioms ECDSAAdd.Arithmetic.BalancedField.originalParity
#print axioms ECDSAAdd.Arithmetic.BalancedField.evenLift
#print axioms ECDSAAdd.Arithmetic.BalancedField.halfResult
#print axioms ECDSAAdd.Arithmetic.BalancedField.signedY_bounds
#print axioms ECDSAAdd.Arithmetic.BalancedField.rawSum_bounds
#print axioms ECDSAAdd.Arithmetic.BalancedField.evenLift_spec
#print axioms ECDSAAdd.Arithmetic.BalancedField.halfResult_spec
#print axioms ECDSAAdd.Arithmetic.BalancedField.evenLift_cast
#print axioms ECDSAAdd.Arithmetic.BalancedField.halfResult_field
#print axioms ECDSAAdd.Arithmetic.BalancedField.halfResult_center
#print axioms ECDSAAdd.Arithmetic.BalancedField.signedHalf_contract
#print axioms ECDSAAdd.Arithmetic.BalancedField.halfResult_parity_interval
#print axioms ECDSAAdd.Arithmetic.BalancedField.centeredFp_signedHalf

#print axioms ECDSAAdd.Arithmetic.BalancedField.originalParity_value
#print axioms ECDSAAdd.Arithmetic.BalancedField.halfResult_sign
