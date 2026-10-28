import ECDSAAdd.Arithmetic.Paper935.Fold32Constants
import Mathlib.Data.ZMod.Basic

namespace ECDSAAdd.Arithmetic.Paper935

/-- Pure mathematical fold of a magnitude, retaining its high contribution.
This definition does not emit a circuit or allocate a register. -/
def wideMagnitudeFold (a : Nat) : Nat := a%2^256+(a/2^256)*(2^32+977)

/-- High 24 bits and low 256 bits suffice for the stipulated magnitude bound. -/
theorem wideMagnitudeFold_parts (a : Nat) (ha : a<2^280) :
    a%2^256<2^256 ∧ a/2^256<2^24 := by
  have low := Nat.mod_lt a (show 0<2^256 by positivity)
  constructor
  · exact low
  · rw [Nat.div_lt_iff_lt_mul (show 0<2^256 by positivity)]
    calc
      a < 2^280 := ha
      _ = 2^24*2^256 := by decide +kernel

theorem wideMagnitudeFold_bound (a : Nat) (ha : a<2^280) :
    wideMagnitudeFold a<2*fold32Prime := by
  obtain ⟨lo,hi⟩ := wideMagnitudeFold_parts a ha
  norm_num [wideMagnitudeFold,fold32Prime] at *
  omega

/-- Exact integer bookkeeping, stronger than a modular congruence. -/
theorem wideMagnitudeFold_decomposition (a : Nat) :
    a=wideMagnitudeFold a+(a/2^256)*fold32Prime := by
  have h := Nat.mod_add_div a (2^256)
  norm_num [wideMagnitudeFold,fold32Prime] at *
  nlinarith only [h]

theorem wideMagnitudeFold_mod (a : Nat) :
    (wideMagnitudeFold a : ZMod fold32Prime)=(a : ZMod fold32Prime) := by
  have h := congrArg (fun n : Nat => (n : ZMod fold32Prime)) (wideMagnitudeFold_decomposition a)
  simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] using h.symm

/-- Reflection modulo 2p, with zero handled separately to keep the bound strict. -/
def wideReflect (a : Nat) : Nat := if a=0 then 0 else 2*fold32Prime-a

theorem wideReflect_bound (a : Nat) (ha : a<2*fold32Prime) :
    wideReflect a<2*fold32Prime := by
  unfold wideReflect
  split_ifs <;> omega

theorem wideReflect_mod (a : Nat) (ha : a<2*fold32Prime) :
    (wideReflect a : ZMod fold32Prime)=-(a : ZMod fold32Prime) := by
  by_cases hz : a=0
  · subst a
    simp [wideReflect]
  · have sum : wideReflect a+a=2*fold32Prime := by
      rw [wideReflect,if_neg hz]
      omega
    have h := congrArg (fun n : Nat => (n : ZMod fold32Prime)) sum
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_self,mul_zero] using h

/-- Route-neutral mathematical input for the bounded reduction component. -/
def wideSignedFold (z : Int) : Nat :=
  if z<0 then wideReflect (wideMagnitudeFold z.natAbs) else wideMagnitudeFold z.natAbs

theorem wideSignedFold_bound (z : Int) (hz : z.natAbs<2^280) :
    wideSignedFold z<2*fold32Prime := by
  unfold wideSignedFold
  split_ifs
  · exact wideReflect_bound _ (wideMagnitudeFold_bound _ hz)
  · exact wideMagnitudeFold_bound _ hz

theorem wideSignedFold_mod (z : Int) (hz : z.natAbs<2^280) :
    (wideSignedFold z : ZMod fold32Prime)=(z : ZMod fold32Prime) := by
  unfold wideSignedFold
  split_ifs with negative
  · rw [wideReflect_mod _ (wideMagnitudeFold_bound _ hz),wideMagnitudeFold_mod]
    have h : (z.natAbs : Int)=-z := by rw [Int.natCast_natAbs,abs_of_neg negative]
    have cast := congrArg (fun n : Int => (n : ZMod fold32Prime)) h
    simp only [Int.cast_natCast,Int.cast_neg] at cast
    rw [cast,neg_neg]
  · rw [wideMagnitudeFold_mod]
    have h : (z.natAbs : Int)=z := by rw [Int.natCast_natAbs,abs_of_nonneg (by omega)]
    simpa only [Int.cast_natCast] using congrArg (fun n : Int => (n : ZMod fold32Prime)) h

/-- Multiplication by either sign preserves the magnitude hypothesis. -/
theorem wideSignedFold_signed (negate : Bool) (v : Int) (hv : v.natAbs<2^280) :
    let z := if negate then -v else v
    wideSignedFold z<2*fold32Prime ∧
      (wideSignedFold z : ZMod fold32Prime)=(z : ZMod fold32Prime) := by
  have h : (if negate then -v else v).natAbs<2^280 := by
    cases negate <;> simpa only [Bool.false_eq_true,if_false,if_true,Int.natAbs_neg] using hv
  exact ⟨wideSignedFold_bound _ h,wideSignedFold_mod _ h⟩

end ECDSAAdd.Arithmetic.Paper935
