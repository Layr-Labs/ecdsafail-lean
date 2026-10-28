import Mathlib.Tactic
import ECDSAAdd.Framework.Hoare
import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- Arithmetic effect of a false-controlled complement/add/complement row.
`M` is the low-half radix and the row word has modulus `2*M`. -/
theorem signed_false_row_value (A S M : Nat) (hM : 0<M)
    (hA : A<2*M) (hS : S<M) :
    2*M-1-((((M-1-A%M)+M*(A/M))+S)%(2*M))=
      (A+M-S)%(2*M) := by
  have hsplit : A%M+M*(A/M)=A := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div A M)
  have hr : A%M<M := Nat.mod_lt A hM
  have hhi : A/M<2 := (Nat.div_lt_iff_lt_mul hM).2 (by simpa [Nat.mul_comm] using hA)
  have hq : A/M=0 ∨ A/M=1 := by
    cases he : A/M with
    | zero => exact Or.inl rfl
    | succ q => exact Or.inr (by omega)
  rcases hq with hq|hq
  · have hP : (M-1-A%M)+M*(A/M)+S<2*M := by rw [hq]; simp; omega
    have hQ : A+M-S<2*M := by rw [← hsplit,hq]; simp; omega
    rw [Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hQ]
    have ha : A=A%M := by rw [hq] at hsplit; simpa using hsplit.symm
    simp only [hq]
    simp only [Nat.mul_zero,Nat.add_zero]
    omega
  · rw [hq] at hsplit
    simp at hsplit
    have ha : A=A%M+M := by omega
    by_cases hs : S≤A%M
    · have hP : (M-1-A%M)+M*(A/M)+S<2*M := by rw [hq]; simp; omega
      have hQ : 2*M≤A+M-S := by omega
      have hQ2 : A+M-S-2*M<2*M := by omega
      rw [Nat.mod_eq_of_lt hP,Nat.mod_eq_sub_mod hQ,Nat.mod_eq_of_lt hQ2]
      simp only [hq]
      simp only [Nat.mul_one]
      omega
    · have hP : 2*M≤(M-1-A%M)+M*(A/M)+S := by rw [hq]; simp; omega
      have hP2 : (M-1-A%M)+M*(A/M)+S-2*M<2*M := by rw [hq]; simp; omega
      have hQ : A+M-S<2*M := by omega
      rw [Nat.mod_eq_sub_mod hP,Nat.mod_eq_of_lt hP2,Nat.mod_eq_of_lt hQ]
      simp only [hq]
      simp only [Nat.mul_one]
      omega

theorem signed_true_row_value (A S M : Nat) :
    (A+S+1)%(2*M)=(A+S+1)%(2*M) := rfl

def signedDeltaValue (c : Wire) (xs : List Wire) (base : BasisState) : Nat :=
  if base c then regValue xs base+1 else 2^xs.length-regValue xs base

def signedRowsValue : List Wire → BasisState → Nat
  | [], _ => 0
  | _::[], _ => 0
  | c::d::tail, base =>
      2*signedDeltaValue c (d::tail) base+4*signedRowsValue (d::tail) base

theorem signedRowsValue_congr (xs : List Wire) (s t : BasisState)
    (h : ∀w∈xs,s w=t w) : signedRowsValue xs s=signedRowsValue xs t := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    cases xs with
    | nil => rfl
    | cons d tail =>
      have hc := h c (by simp)
      have hr : regValue (d::tail) s=regValue (d::tail) t :=
        regValue_congr _ _ _ (fun w hw => h w (by simp [hw]))
      have hi := ih (fun w hw => h w (by simp [hw]))
      simp [signedRowsValue,signedDeltaValue,hc,hr,hi]

theorem signedDeltaValue_bound (c : Wire) (xs : List Wire) (base : BasisState) :
    signedDeltaValue c xs base≤2^xs.length := by
  have h := regValue_lt xs base
  simp only [signedDeltaValue]
  split <;> omega

/-- All signed rows fit below the untouched top product bit.  The stronger
subtracted term is what leaves room for an arbitrary clean low-half prefix. -/
theorem signedRowsValue_bound (xs : List Wire) (base : BasisState) (hn : 1≤xs.length) :
    signedRowsValue xs base≤2^(2*xs.length-1)-2^xs.length := by
  induction xs with
  | nil => simp at hn
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedRowsValue]
    | cons d tail =>
      let rest := d::tail
      have hk : 1≤rest.length := by simp [rest]
      have hi := ih hk
      have hd := signedDeltaValue_bound c rest base
      have hp1 : 2^(rest.length+1)=2*2^rest.length := by rw [Nat.pow_succ]; omega
      have he : 2*(rest.length+1)-1=(2*rest.length-1)+2 := by omega
      have hp2 : 2^(2*(rest.length+1)-1)=4*2^(2*rest.length-1) := by
        rw [he,Nat.pow_add]
        norm_num [Nat.mul_comm]
      have hpow : 2^rest.length≤2^(2*rest.length-1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      simp only [signedRowsValue,List.length_cons]
      change 2*signedDeltaValue c rest base+4*signedRowsValue rest base≤
        2^(2*(rest.length+1)-1)-2^(rest.length+1)
      change signedRowsValue rest base≤2^(2*rest.length-1)-2^rest.length at hi
      rw [hp1,hp2]
      omega

end ECDSAAdd.Arithmetic
