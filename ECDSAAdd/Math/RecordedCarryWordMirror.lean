import ECDSAAdd.Arithmetic.RecordedRailRippleInvariant

namespace ECDSAAdd.Math.RecordedCarryWordMirror
open Arithmetic RecordedRailRipple

/-- Little-endian sum and carry words describe ordinary binary addition.
These are mathematical definitions, not replacements for circuit execution. -/
def sumBits : List Bool → List Bool → Bool → List Bool
  | a::as,b::bs,c => sumBit a b c :: sumBits as bs (carryFn a b c)
  | _,_,_ => []

def carryBits : List Bool → List Bool → Bool → List Bool
  | a::as,b::bs,c => carryFn a b c :: carryBits as bs (carryFn a b c)
  | _,_,_ => []

theorem mirror_bit_carry (a b c : Bool) :
    carryFn a (!(sumBit a b c)) c=carryFn a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem mirror_bit_sum (a b c : Bool) :
    sumBit a (!(sumBit a b c)) c=(!b) := by
  cases a <;> cases b <;> cases c <;> decide

/-- The complemented sum lets the mirror reconstruct every original carry,
including all chunk boundaries at which the original qubit was released. -/
theorem mirror_carries (a b : List Bool) (cin : Bool) :
    carryBits a ((sumBits a b cin).map (!·)) cin=carryBits a b cin := by
  induction a generalizing b cin with
  | nil => rfl
  | cons a as ih =>
    cases b with
    | nil => rfl
    | cons b bs =>
      simp only [sumBits,List.map_cons,carryBits,mirror_bit_carry]
      rw [ih]

/-- Complete arithmetic forward/mirror identity, with the source unchanged and
the same carry-in. Neither measurement outcome is equated to another one. -/
theorem mirror_sum (a b : List Bool) (cin : Bool) (width : a.length=b.length) :
    sumBits a ((sumBits a b cin).map (!·)) cin=b.map (!·) := by
  induction a generalizing b cin with
  | nil =>
    have bn : b=[] := List.eq_nil_of_length_eq_zero (by simpa using width.symm)
    subst b
    rfl
  | cons a as ih =>
    cases b with
    | nil => simp at width
    | cons b bs =>
      have h : as.length=bs.length := by simpa using width
      simp only [sumBits,List.map_cons,mirror_bit_sum,mirror_bit_carry]
      rw [ih bs _ h]

/-- A fixed inventory of old outcomes induces the same phase debt on the
reconstructed carries. This does not assume the debt to be zero. -/
def debt : List (Option Nat) → List Bool → List Bool → Bool
  | some j::slots,m,c::cs => (m.getD j false && c) ^^ debt slots m cs
  | none::slots,m,_::cs => debt slots m cs
  | _,_,_ => false

theorem mirror_debt (a b : List Bool) (cin : Bool)
    (slots : List (Option Nat)) (m : List Bool) :
    debt slots m (carryBits a ((sumBits a b cin).map (!·)) cin)=
      debt slots m (carryBits a b cin) := by
  rw [mirror_carries]

end ECDSAAdd.Math.RecordedCarryWordMirror
#print axioms ECDSAAdd.Math.RecordedCarryWordMirror.mirror_carries
#print axioms ECDSAAdd.Math.RecordedCarryWordMirror.mirror_sum
#print axioms ECDSAAdd.Math.RecordedCarryWordMirror.mirror_debt
