import ECDSAAdd.Arithmetic.CuccaroAdder
import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.MaskedConstant
import ECDSAAdd.Framework.UnitaryControl

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def constantWeight : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,k => (if k%2=1 then 1 else 0)+constantWeight n (k/2)

theorem xorConstant_cnotCount (r : List Wire) (k : Nat) :
    cnotCount (xorConstant r k)=0 := by
  induction r generalizing k with
  | nil => rfl
  | cons q r ih =>
    by_cases h : k%2=1 <;> simp [xorConstant,h,cnotCount,ih]

theorem maskedConstant_cnotCount (c : Wire) (r : List Wire) (k : Nat) :
    cnotCount (maskedConstant c r k)=constantWeight r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons q r ih =>
    by_cases h : k%2=1 <;> simp [maskedConstant,constantWeight,h,cnotCount,ih]

theorem notRegister_cnotCount (r : List Wire) : cnotCount (notRegister r)=0 := by
  induction r with
  | nil => rfl
  | cons q r ih =>
    change cnotCount (Instr.X q::notRegister r)=0
    exact ih

theorem copyRegister_none_cnotCount (a b : List Wire) (hl : a.length=b.length) :
    cnotCount (copyRegister none a b)=a.length := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [copyRegister,cnotCount]
  | cons x a ih =>
    cases b with
    | nil => simp at hl
    | cons y b =>
      have h := ih b (by simpa using hl)
      simp [copyRegister,copyGate,cnotCount,h,Nat.add_comm]

theorem cuccaroAdd_cnotCount (a b : List Wire) (cin : Wire)
    (hl : a.length=b.length) :
    cnotCount (cuccaroAdd a b cin)=if a.length=0 then 0 else 4*a.length-2 := by
  induction a generalizing b cin with
  | nil => cases b <;> simp_all [cuccaroAdd,cnotCount]
  | cons x a ih =>
    cases a with
    | nil =>
      cases b with
      | nil => simp at hl
      | cons y b =>
        have hb : b=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        subst b
        rfl
    | cons x' a =>
      cases b with
      | nil => simp at hl
      | cons y b =>
        cases b with
        | nil => simp at hl
        | cons y' b =>
          have h := ih (y'::b) x (by simpa using hl)
          simp only [cuccaroAdd,cnotCount_append,cuccaroMaj,cuccaroUma,
            cnotCount,List.length_cons,h]
          simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
          omega

theorem cuccaroSub_cnotCount (a b : List Wire) (cin : Wire)
    (hl : a.length=b.length) :
    cnotCount (cuccaroSub a b cin)=if a.length=0 then 0 else 4*a.length-2 := by
  simp only [cuccaroSub,cnotCount_append,notRegister_cnotCount,
    cuccaroAdd_cnotCount a b cin hl,Nat.zero_add,Nat.add_zero]

end ECDSAAdd.Arithmetic
