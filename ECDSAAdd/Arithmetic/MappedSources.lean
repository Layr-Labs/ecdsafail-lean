import ECDSAAdd.Arithmetic.MappedAdder
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- An optional external control; an absent control enables the literal. -/
def mappedEnabled (c : Option Wire) (s : BasisState) : Bool := (c.map s).getD true

def mappedConstantBit (c : Option Wire) (b : Bool) : MappedBit :=
  if b then {wire:=c,flip:=c.isNone} else {wire:=none,flip:=false}

def mappedConstant : Option Wire → Nat → Nat → List MappedBit
  | _,0,_ => []
  | c,n+1,k => mappedConstantBit c (decide (k%2=1))::mappedConstant c n (k/2)

def mappedRead (xs : List Wire) (flip : Bool := false) : List MappedBit :=
  xs.map (fun q => {wire:=some q,flip:=flip})

theorem mappedConstantBit_value (c : Option Wire) (b : Bool) (s : BasisState) :
    (mappedConstantBit c b).value s=if b then mappedEnabled c s else false := by
  cases c <;> cases b <;> simp [mappedConstantBit,MappedBit.value,mappedEnabled]

theorem mappedConstant_length (c : Option Wire) (n k : Nat) :
    (mappedConstant c n k).length=n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [mappedConstant,ih]

theorem mappedConstant_value (c : Option Wire) (n k : Nat) (s : BasisState)
    (hk : k<2^n) :
    mappedValue (mappedConstant c n k) s=if mappedEnabled c s then k else 0 := by
  induction n generalizing k with
  | zero =>
    have h : k=0 := by simpa using hk
    simp [mappedConstant,mappedValue,h]
  | succ n ih =>
    have hd : k/2<2^n := by rw [Nat.pow_succ] at hk; omega
    rw [mappedConstant,mappedValue,mappedConstantBit_value,ih _ hd]
    have split := Nat.mod_add_div k 2
    have small := Nat.mod_lt k (by decide : 0<2)
    cases he : mappedEnabled c s <;> by_cases odd : k%2=1 <;>
      simp [he,odd] <;> omega

theorem mappedConstant_wires (c : Option Wire) (n k : Nat) :
    ∀q∈mappedWires (mappedConstant c n k),q∈c := by
  induction n generalizing k with
  | zero => simp [mappedConstant,mappedWires]
  | succ n ih =>
    intro q hq
    simp only [mappedConstant,mappedWires,List.flatMap_cons,List.mem_append] at hq
    rcases hq with head|tail
    · by_cases odd : k%2=1
      · simpa [mappedConstantBit,odd] using head
      · simp [mappedConstantBit,odd] at head
    · exact ih _ q tail

theorem mappedRead_value (xs : List Wire) (s : BasisState) :
    mappedValue (mappedRead xs false) s=regValue xs s := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    simp [mappedRead,mappedValue,MappedBit.value,regValue,ih,Bool.toNat,Bool.cond_eq_ite]
    simpa [mappedRead,regValue] using ih

theorem mappedRead_complement (xs : List Wire) (s : BasisState) :
    mappedValue (mappedRead xs true) s=2^xs.length-1-regValue xs s := by
  have eq : mappedValue (mappedRead xs true) s=regValue xs (fun q => !s q) := by
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp [mappedRead,mappedValue,MappedBit.value,regValue,ih,Bool.toNat,Bool.cond_eq_ite]
      simpa [mappedRead,regValue] using ih
  rw [eq,regValue_complement]

theorem mappedRead_wires (xs : List Wire) (flip : Bool) :
    mappedWires (mappedRead xs flip)=xs := by
  induction xs with
  | nil => rfl
  | cons q qs ih => simpa [mappedRead,mappedWires] using congrArg (List.cons q) ih

theorem mappedValue_append (xs ys : List MappedBit) (s : BasisState) :
    mappedValue (xs++ys) s=mappedValue xs s+2^xs.length*mappedValue ys s := by
  induction xs with
  | nil => simp [mappedValue]
  | cons x xs ih => simp [mappedValue,ih,Nat.pow_succ]; ring

/-- Repeated wires are immutable reads, so this diagonal source needs no
128/129-bit mask register in addition to the controlled square input. -/
def mappedDiagonal (xs : List Wire) : List MappedBit :=
  mappedRead xs false++mappedRead (xs.take (xs.length-1)) true++[{wire:=none,flip:=false}]

theorem mappedDiagonal_length (xs : List Wire) (hn : 0<xs.length) :
    (mappedDiagonal xs).length=2*xs.length := by
  simp [mappedDiagonal,mappedRead]
  omega

theorem mappedRead_length (xs : List Wire) (flip : Bool) :
    (mappedRead xs flip).length=xs.length := by simp [mappedRead]

theorem mappedDiagonal_value (xs : List Wire) (s : BasisState) :
    mappedValue (mappedDiagonal xs) s=regValue xs s+
      2^xs.length*(2^(xs.length-1)-1-regValue (xs.take (xs.length-1)) s) := by
  simp only [mappedDiagonal,mappedValue_append,mappedRead_value,mappedRead_complement,
    mappedRead_length,mappedValue,MappedBit.value,Option.map_none,Option.getD_none,
    Bool.xor_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
  rw [List.length_take,Nat.min_eq_left (by omega)]

def mappedConstAdd (c : Option Wire) (ys carry : List Wire) (cin : Wire) (k : Nat) : Program :=
  mappedAdd (mappedConstant c ys.length k) ys carry cin

theorem mappedConstAdd_counts (c : Option Wire) (ys carry : List Wire) (cin : Wire) (k : Nat)
    (hc : carry.length+1=ys.length) :
    toffoliCount (mappedConstAdd c ys carry cin k)=ys.length-1 ∧
    measurementCount (mappedConstAdd c ys carry cin k)=ys.length-1 :=
  mappedAdd_counts _ _ _ _ (mappedConstant_length _ _ _) hc

theorem mappedConstAdd_correct (c : Option Wire) (ys carry : List Wire) (cin : Wire) (k : Nat)
    (hn : (cin::(ys++carry)).Nodup) (ha : ∀q∈c,q∉cin::(ys++carry))
    (hc : carry.length+1=ys.length) (hk : k<2^ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (mappedConstAdd c ys carry cin k) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (mappedConstAdd c ys carry cin k) m s).basis q=s.basis q) ∧
    regValue ys (run (mappedConstAdd c ys carry cin k) m s).basis=
      ((if mappedEnabled c s.basis then k else 0)+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length := by
  obtain ⟨hp,he,hv⟩ := mappedAdd_correct (mappedConstant c ys.length k) ys carry cin hn
    (fun q hq => ha q (mappedConstant_wires _ _ _ q hq)) (mappedConstant_length _ _ _) hc s m hclean
  exact ⟨hp,he,by simpa [mappedConstant_value _ _ _ _ hk] using hv⟩

end ECDSAAdd.Arithmetic
