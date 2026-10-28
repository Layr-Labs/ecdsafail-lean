import ECDSAAdd.Arithmetic.RecordedRailApplyProgram

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply
open RecordedRailRipple ECDSAAdd.Math.RecordedCarryWordMirror

def wordValue : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*wordValue bs

theorem wordValue_map (r : List Wire) (bits : BasisState) :
    wordValue (r.map bits)=regValue r bits := by
  induction r with
  | nil => rfl
  | cons q qs ih => rw [List.map_cons,wordValue,RecordedRailVented.reg_cons,ih]

theorem wordValue_lt (xs : List Bool) : wordValue xs<2^xs.length := by
  induction xs with
  | nil => simp [wordValue]
  | cons b bs ih =>
    simp only [wordValue,List.length_cons,Nat.pow_succ]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem wordValue_injective (xs ys : List Bool) (width : xs.length=ys.length)
    (value : wordValue xs=wordValue ys) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    have hn : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using width.symm)
    exact hn.symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at width
    | cons y ys =>
      have head : x=y := by
        simp only [wordValue] at value
        cases x <;> cases y <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
      have tail : wordValue xs=wordValue ys := by
        simp only [wordValue] at value
        rw [head] at value
        omega
      have lengths : xs.length=ys.length := by simpa using width
      rw [head,ih ys lengths tail]

theorem sumBits_length (a b : List Bool) (cin : Bool) (width : a.length=b.length) :
    (sumBits a b cin).length=a.length := by
  induction a generalizing b cin with
  | nil => rfl
  | cons x xs ih =>
    cases b with
    | nil => simp at width
    | cons y ys =>
      simp only [sumBits,List.length_cons]
      rw [ih ys _ (by simpa using width)]

theorem sumBits_value (a b : List Bool) (cin : Bool) (width : a.length=b.length) :
    wordValue (sumBits a b cin)=(wordValue a+wordValue b+cin.toNat)%2^a.length := by
  induction a generalizing b cin with
  | nil => simp [sumBits,wordValue,Nat.mod_one]
  | cons x xs ih =>
    cases b with
    | nil => simp at width
    | cons y ys =>
      simp only [sumBits,wordValue,List.length_cons]
      rw [ih ys _ (by simpa using width)]
      have h := sum_value_step x y cin (wordValue xs) (wordValue ys) xs.length
      simpa only [carryFn_eq] using h

/-- Numeric output of actual forward gates determines every target bit. -/
theorem mapped_sum (a b : List Wire) (original out : BasisState) (cin : Bool)
    (width : a.length=b.length)
    (value : regValue b out=(regValue a original+regValue b original+cin.toNat)%2^b.length) :
    b.map out=sumBits (a.map original) (b.map original) cin := by
  have mapWidths : (a.map original).length=(b.map original).length := by
    simpa only [List.length_map] using width
  apply wordValue_injective
  · rw [sumBits_length (a.map original) (b.map original) cin mapWidths]
    simpa only [List.length_map] using width.symm
  · rw [wordValue_map,sumBits_value (a.map original) (b.map original) cin mapWidths,
      wordValue_map,wordValue_map]
    simpa only [List.length_map,width] using value

def endCarry : List Bool → List Bool → Bool → Bool
  | [],[],c => c
  | a::as,b::bs,c => endCarry as bs (carryFn a b c)
  | _,_,_ => false

/-- Full little-endian word including the final carry is the exact sum. -/
theorem full_word_value (a b : List Bool) (cin : Bool) (width : a.length=b.length) :
    wordValue (sumBits a b cin)+2^a.length*(endCarry a b cin).toNat=
      wordValue a+wordValue b+cin.toNat := by
  induction a generalizing b cin with
  | nil =>
    have bn : b=[] := List.eq_nil_of_length_eq_zero (by simpa using width.symm)
    subst b
    simp [sumBits,wordValue,endCarry]
  | cons x xs ih =>
    cases b with
    | nil => simp at width
    | cons y ys =>
      have tail := ih ys (carryFn x y cin) (by simpa using width)
      have low := RecordedRailVented.bit_sum x y cin
      have sx : sumBit x y cin=((y ^^ x) ^^ cin) := by cases x <;> cases y <;> cases cin <;> rfl
      simp only [sumBits,wordValue,endCarry,List.length_cons,Nat.pow_succ]
      calc
        _=(sumBit x y cin).toNat+2*(wordValue (sumBits xs ys (carryFn x y cin))+
          2^xs.length*(endCarry xs ys (carryFn x y cin)).toNat) := by ring
        _=(sumBit x y cin).toNat+2*(wordValue xs+wordValue ys+(carryFn x y cin).toNat) := by rw [tail]
        _=_ := by rw [sx]; omega

theorem carry_getD (a b : List Bool) (cin : Bool) (i : Nat)
    (ai : i<a.length) (bi : i<b.length) :
    (carryBits a b cin).getD i false=endCarry (a.take (i+1)) (b.take (i+1)) cin := by
  induction i generalizing a b cin with
  | zero =>
    cases a with
    | nil => simp at ai
    | cons x xs =>
      cases b with
      | nil => simp at bi
      | cons y ys => simp [carryBits,endCarry]
  | succ i ih =>
    cases a with
    | nil => simp at ai
    | cons x xs =>
      cases b with
      | nil => simp at bi
      | cons y ys =>
        simpa only [carryBits,List.getD_cons_succ,List.take_succ_cons,endCarry] using
          ih xs ys (carryFn x y cin) (by simpa using ai) (by simpa using bi)

/-- Ordinary carry at a prefix is its overflow predicate, on original bits. -/
theorem carry_overflow (a b : List Bool) (cin : Bool) (i : Nat)
    (width : a.length=b.length) (ai : i<a.length) :
    (carryBits a b cin).getD i false=
      decide (2^(i+1) ≤ wordValue (a.take (i+1))+wordValue (b.take (i+1))+cin.toNat) := by
  have bi : i<b.length := by omega
  rw [carry_getD a b cin i ai bi]
  have sizes : (a.take (i+1)).length=(b.take (i+1)).length := by simp [width]
  have al : (a.take (i+1)).length=i+1 := by
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.succ_le_of_lt ai)
  have full := full_word_value (a.take (i+1)) (b.take (i+1)) cin sizes
  have low := wordValue_lt (sumBits (a.take (i+1)) (b.take (i+1)) cin)
  rw [sumBits_length (a.take (i+1)) (b.take (i+1)) cin sizes,al] at low
  rw [al] at full
  cases hc : endCarry (a.take (i+1)) (b.take (i+1)) cin with
  | false =>
    simp only [hc,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at full
    have hn : ¬(2^(i+1) ≤ wordValue (a.take (i+1))+wordValue (b.take (i+1))+cin.toNat) := by omega
    simp [hn]
  | true =>
    simp only [hc,Bool.toNat_true,Nat.mul_one] at full
    have bound : 2^(i+1) ≤ wordValue (a.take (i+1))+wordValue (b.take (i+1))+cin.toNat := by omega
    simp [bound]

end ECDSAAdd.Arithmetic.RecordedRailApply
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply.mapped_sum
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply.carry_overflow
