import ECDSAAdd.Submission.Entrant.FrontierEntrySignMath
import ECDSAAdd.Arithmetic.BalancedFoldMath

/-! Unary entry half arithmetic. The caller starts with a centered target
and a zero source; these lemmas do not replace an unequal-input cell. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryHalf5
open Arithmetic BalancedCircuit BalancedField Secp256k1

def correction (H U : Bool) : Int :=
  if H then (if U then -q-1 else q+1) else (if U then q else -q)

def sourceBit (i : Nat) (P H U : Bool) : Bool :=
  let a := P && H
  let d := P && U
  let e := a && U
  if i=0 then P ^^ a else if i=1 ∨ i=2 then d ^^ e else
    if i=3 then P ^^ d ^^ e else
      if i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=31 ∨ i=255 then P ^^ d ^^ a else d ^^ a

def virtualSource (P H U : Bool) : Nat :=
  (List.range 256).foldr (fun i acc => (sourceBit i P H U).toNat+2*acc) 0

theorem virtualSource_value (P H U : Bool) :
    virtualSource P H U=encodeWord 256 (if P then correction H U else 0) := by
  cases P <;> cases H <;> cases U <;> decide

theorem unary_half_formula (U : Bool) (Y : Int) (hy : Centered Y) :
    halfResult (signedY U Y)=
      (if U then -(Y/2) else Y/2)+(if originalParity Y then correction (negative Y) U else 0) := by
  have hT := signedY_bounds U Y hy
  have hp := constants
  have hR := (halfResult_spec (signedY U Y) (by unfold Centered at hT; omega)).2
  have negParity : (-Y)%2=Y%2 := by omega
  by_cases he : Y%2=0
  · have ie : signedY U Y%2=0 := by cases U <;> simp [signedY,negParity,he]
    rw [evenLift,if_pos ie] at hR
    cases U <;> simp [signedY,originalParity,he] at hR ⊢ <;> omega
  · have ie : signedY U Y%2≠0 := by cases U <;> simp [signedY,negParity,he]
    rw [evenLift,if_neg ie] at hR
    cases U <;> by_cases hn : Y<0
    all_goals
      simp only [signedY,Bool.false_eq_true,if_false,if_true] at hR ⊢
      simp [originalParity,negative,correction,he,hn]
      split_ifs at hR <;> omega


def threshold : Nat := q.toNat/2
def literalValue : Nat := 2^255-1-threshold

theorem threshold_relation : q=2*(threshold : Int)+1 := by norm_num [threshold,q,p]

theorem threshold_bound : threshold<2^255-1 := by decide

theorem literal_bound : literalValue<2^255 := by unfold literalValue; have b := threshold_bound; omega

theorem carry_predicate (R : Int) :
    decide (2^255≤(magnitude R).toNat+literalValue+(negative R).toNat)=decide (threshold<R.natAbs) := by
  have ms := DiagonalParity5.magnitude_sign R
  have tb := threshold_bound
  have equal : (2^255≤(magnitude R).toNat+literalValue+(negative R).toNat) ↔ threshold<R.natAbs := by
    unfold literalValue
    omega
  simp only [equal]

theorem half_parity (Y : Int) (hy : Centered Y) :
    originalParity Y=decide (threshold<(halfResult Y).natAbs) := by
  have z : Centered (0:Int) := by have := constants; unfold Centered; omega
  have h := halfResult_parity_interval false Y 0 hy z
  have t := threshold_relation
  have a := Int.natCast_natAbs (halfResult Y)
  simp only [rawSum,signedY,Bool.false_eq_true,if_false,add_zero,sub_zero,mul_zero] at h
  rw [abs_mul] at h
  norm_num only [Int.reduceAbs] at h
  apply decide_eq_decide.mpr
  change (Y%2≠0) ↔ threshold<(halfResult Y).natAbs
  omega

end ECDSAAdd.Entrant.EntryHalf5
