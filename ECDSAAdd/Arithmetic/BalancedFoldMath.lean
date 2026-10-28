import ECDSAAdd.Arithmetic.BalancedFieldCircuitProgram
import ECDSAAdd.Arithmetic.BalancedFieldHalf

set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic.BalancedFold
open BalancedField BalancedCircuit

def modulusWord : Nat := 2^256

/-- The upper 256 source bits of the sparse correction, without a bank. -/
def virtualSource (u v : Bool) : Nat :=
  (List.range 256).foldr (fun i acc =>
    (if sparseF.testBit (i+1) then u else v).toNat+2*acc) 0

def selectedSource (u v : Bool) : Nat :=
  if u then (sparseF-1)/2 else if v then modulusWord-(sparseF+1)/2 else 0

/-- Finite fixed-modulus calculation by ordinary kernel reduction. -/
theorem virtualSource_value (u v : Bool) (hn : ¬(u && v)=true) :
    virtualSource u v=selectedSource u v := by
  cases u <;> cases v
  · decide
  · decide
  · decide
  · simp at hn

private theorem mapped_list_value (is : List Nat) (L : BalancedCircuit.Layout) (s : BasisState) :
    mappedValue (is.map (fun i =>
      {wire:=some (if sparseF.testBit (i+1) then L.plus else L.minus),flip:=false})++
      [{wire:=none,flip:=false}]) s=
    is.foldr (fun i acc =>
      (if sparseF.testBit (i+1) then s L.plus else s L.minus).toNat+2*acc) 0 := by
  induction is with
  | nil => simp [mappedValue,MappedBit.value]
  | cons i is ih =>
    simp only [List.map_cons,List.cons_append,mappedValue,List.foldr_cons]
    rw [ih]
    cases hb : sparseF.testBit (i+1) <;> simp [MappedBit.value,hb]

theorem foldBits_value (L : BalancedCircuit.Layout) (s : BasisState)
    (hn : ¬(s L.plus && s L.minus)=true) :
    mappedValue (foldBits L) s=selectedSource (s L.plus) (s L.minus) := by
  rw [foldBits,mapped_list_value]
  exact virtualSource_value _ _ hn

/-- Encoding on one complete positive and negative modulus interval. -/
theorem encode_shift (n : Nat) (z : Int)
    (hz : -((2^n : Nat) : Int)≤z ∧ z<((2^n : Nat) : Int)) :
    (encodeWord n z : Int)=z+(if z<0 then ((2^n : Nat) : Int) else 0) := by
  rw [encodeWord_cast]
  by_cases hn : z<0
  · rw [if_pos hn]
    have he : (z+((2^n : Nat) : Int))%((2^n : Nat) : Int)=
        z%((2^n : Nat) : Int) := by simp
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at he
    exact he.symm
  · rw [if_neg hn,Int.emod_eq_of_lt (by omega) hz.2]
    omega

def minusController (T : Int) : Bool := originalParity T && decide (T<0)
def plusController (T : Int) : Bool := originalParity T && !decide (T<0)

theorem controllers_exclusive (T : Int) :
    ¬(plusController T && minusController T)=true := by
  unfold plusController minusController
  cases originalParity T <;> cases decide (T<0) <;> decide

/-- A physical bit-256 toggle, using the proved raw-word sign. -/
def toggledWord (T : Int) : Nat :=
  if originalParity T then
    if decide (T<0) then encodeWord 257 T-modulusWord else encodeWord 257 T+modulusWord
  else encodeWord 257 T

/-- The cleared low bit is omitted, and a clean extra top bit is appended
before the exact mapped add with the original parity as carry-in. -/
def foldedSum (T : Int) : Nat :=
  toggledWord T/2+selectedSource (plusController T) (minusController T)+
    (originalParity T).toNat

private theorem raw_encoding (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    (encodeWord 257 T : Int)=T+(if T<0 then ((2^257 : Nat) : Int) else 0) := by
  apply encode_shift
  norm_num [q,ECDSAAdd.p] at ht ⊢
  omega

theorem raw_sign (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    encodeWord 257 T/modulusWord=(decide (T<0)).toNat := by
  have hr := raw_encoding T ht
  by_cases hn : T<0 <;> norm_num [hn,modulusWord,q,ECDSAAdd.p] at hr ht ⊢ <;> omega

private theorem fixed_relations :
    modulusWord=2*(2^255) ∧ (2^257 : Nat)=4*(2^255) ∧
    (sparseF+1)/2=(sparseF-1)/2+1 ∧
    (ECDSAAdd.p : Int)=2*((2^255 : Nat) : Int)-2*(((sparseF-1)/2 : Nat) : Int)-1 ∧
    (sparseF-1)/2+1≤2*(2^255) := by decide

private theorem generic_bound (Q T : Int) (H K : Nat)
    (hp : 2*Q+1=2*(H : Int)-2*(K : Int)-1) (ht : -(2*Q)≤T ∧ T≤2*Q) :
    -2*(H : Int)<T ∧ T<2*(H : Int) := by omega

private theorem generic_parity (H U : Nat) (T : Int) (a s : Bool)
    (hu : (U : Int)=T+(if s then 4*(H : Int) else 0))
    (ht : -2*(H : Int)<T ∧ T<2*(H : Int)) (hp : T%2=(a.toNat : Int)) :
    (if a then if s then U-2*H else U+2*H else U)%2=a.toNat := by
  cases a <;> cases s <;> simp at hu hp ⊢ <;> omega

theorem toggled_parity (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T%2=(originalParity T).toNat := by
  obtain ⟨hm,hw,hk,hp,hkb⟩ := fixed_relations
  have raw := raw_encoding T ht
  rw [hw] at raw
  have raw' : (encodeWord 257 T : Int)=T+
      (if decide (T<0) then 4*((2^255 : Nat) : Int) else 0) := by
    by_cases hn : T<0 <;>
      simp only [hn,decide_true,decide_false,if_true,if_false,Nat.cast_mul,Nat.cast_ofNat] at raw ⊢ <;>
      exact raw
  have bound := generic_bound q T (2^255) ((sparseF-1)/2)
    ((constants.2.1).symm.trans hp) ht
  have par : T%2=((originalParity T).toNat : Int) := by
    have h := originalParity_value T
    cases ha : originalParity T <;> simpa [ha] using h
  simpa only [toggledWord,hm] using generic_parity (2^255) (encodeWord 257 T)
    T (originalParity T) (decide (T<0)) raw' bound par

theorem cleared_low_word (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    toggledWord T=2*(toggledWord T/2)+(originalParity T).toNat := by
  have h := Nat.mod_add_div (toggledWord T) 2
  rw [toggled_parity T ht] at h
  omega

private theorem generic_fold (H K U E : Nat) (T R : Int) (a s : Bool)
    (hk : K+1≤2*H) (ht : -2*(H : Int)<T ∧ T<2*(H : Int))
    (hu : (U : Int)=T+(if s then 4*(H : Int) else 0))
    (he : (E : Int)=R+(if s ^^ a then 2*(H : Int) else 0))
    (hr : 2*R=T+(if a then if s then 2*(H : Int)-2*(K : Int)-1
      else -(2*(H : Int)-2*(K : Int)-1) else 0)) :
    (if a then if s then U-2*H else U+2*H else U)/2+
      (if a && !s then K else if a && s then 2*H-K-1 else 0)+a.toNat=
      E+2*H*(a && s).toNat := by
  cases a <;> cases s <;> simp at hu he hr ⊢ <;> omega

/-- Generic arithmetic is proved before fixed constants are instantiated,
so no enormous numerical omega certificate enters the kernel. -/
theorem foldedSum_value (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    foldedSum T=encodeWord 256 (halfResult T)+modulusWord*(minusController T).toNat := by
  obtain ⟨hm,hw,hk,hp,hkb⟩ := fixed_relations
  have raw := raw_encoding T ht
  rw [hw] at raw
  have raw' : (encodeWord 257 T : Int)=T+
      (if decide (T<0) then 4*((2^255 : Nat) : Int) else 0) := by
    by_cases hn : T<0 <;>
      simp only [hn,decide_true,decide_false,if_true,if_false,Nat.cast_mul,Nat.cast_ofNat] at raw ⊢ <;>
      exact raw
  have hs := halfResult_spec T ht
  have result := encode_shift 256 (halfResult T) (by
    have h := hs.1
    norm_num [Centered,q,ECDSAAdd.p] at h ⊢
    omega)
  have hi : (if halfResult T<0 then ((2^256 : Nat) : Int) else 0)=
      (if decide (T<0) ^^ originalParity T then ((2^256 : Nat) : Int) else 0) := by
    rw [←halfResult_sign T ht]
    by_cases hn : halfResult T<0 <;> simp [hn]
  rw [hi,show (2^256 : Nat)=2*(2^255) from hm] at result
  simp only [Nat.cast_mul,Nat.cast_ofNat] at result
  have half : 2*halfResult T=T+(if originalParity T then
      if decide (T<0) then (ECDSAAdd.p : Int) else -(ECDSAAdd.p : Int) else 0) := by
    have h := hs.2
    by_cases ho : T%2=0 <;> by_cases hn : T<0
    all_goals simp [evenLift,originalParity,ho,hn,show (0≤T)↔¬T<0 by omega,
      sub_eq_add_neg] at h ⊢; exact h
  rw [hp] at half
  have bound := generic_bound q T (2^255) ((sparseF-1)/2)
    ((constants.2.1).symm.trans hp) ht
  have g := generic_fold (2^255) ((sparseF-1)/2) (encodeWord 257 T)
    (encodeWord 256 (halfResult T)) T (halfResult T) (originalParity T) (decide (T<0))
    hkb bound raw' result half
  simpa only [foldedSum,toggledWord,selectedSource,plusController,minusController,
    hm,hk,Nat.sub_sub] using g

theorem foldedSum_low (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    foldedSum T%modulusWord=encodeWord 256 (halfResult T) := by
  have hb := encodeWord_bound 256 (halfResult T)
  norm_num at hb
  rw [foldedSum_value T ht]
  simp [Nat.add_mod,Nat.mul_mod,modulusWord,Nat.mod_eq_of_lt hb]

theorem foldedSum_cout (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    foldedSum T/modulusWord=(minusController T).toNat := by
  have hv := foldedSum_value T ht
  have hb := encodeWord_bound 256 (halfResult T)
  cases hc : minusController T <;> norm_num [hc,modulusWord] at hv hb ⊢ <;> omega

theorem foldedSum_bound (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    foldedSum T<2^257 := by
  have hv := foldedSum_value T ht
  have hb := encodeWord_bound 256 (halfResult T)
  cases hc : minusController T <;> norm_num [hc,modulusWord] at hv hb ⊢ <;> omega

end ECDSAAdd.Arithmetic.BalancedFold

#print axioms ECDSAAdd.Arithmetic.BalancedFold.virtualSource_value
#print axioms ECDSAAdd.Arithmetic.BalancedFold.foldBits_value
#print axioms ECDSAAdd.Arithmetic.BalancedFold.encode_shift
#print axioms ECDSAAdd.Arithmetic.BalancedFold.controllers_exclusive
#print axioms ECDSAAdd.Arithmetic.BalancedFold.raw_sign
#print axioms ECDSAAdd.Arithmetic.BalancedFold.toggled_parity
#print axioms ECDSAAdd.Arithmetic.BalancedFold.cleared_low_word
#print axioms ECDSAAdd.Arithmetic.BalancedFold.foldedSum_value
#print axioms ECDSAAdd.Arithmetic.BalancedFold.foldedSum_low
#print axioms ECDSAAdd.Arithmetic.BalancedFold.foldedSum_cout
#print axioms ECDSAAdd.Arithmetic.BalancedFold.foldedSum_bound
