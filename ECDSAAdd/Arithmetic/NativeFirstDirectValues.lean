import ECDSAAdd.Arithmetic.NativeFirstDirectProgram

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect

def hScalar (inverse odd : Bool) : Nat :=
  (List.range 253).foldr (fun j acc =>
    (if (if inverse then 2^256-hConstant else hConstant).testBit (j+3)
      then odd else false).toNat+2*acc) 0

def kScalar (inverse odd : Bool) : Nat :=
  (List.range 257).foldr (fun j acc =>
    (if odd then (kConstant inverse true).testBit (j+1)
      else (kConstant inverse false).testBit (j+1)).toNat+2*acc) 0

/-- Fixed modulus bit constants are reduced by the Lean kernel, not native_decide. -/
theorem hScalar_value (inverse odd : Bool) :
    hScalar inverse odd=if odd then
      (if inverse then 2^256-hConstant else hConstant)/8 else 0 := by
  cases inverse <;> cases odd <;> decide

theorem kScalar_value (inverse odd : Bool) :
    kScalar inverse odd=kConstant inverse odd/2 := by
  cases inverse <;> cases odd <;> decide

private theorem h_list_value (is : List Nat) (flag : Wire) (inverse : Bool)
    (s : BasisState) :
    mappedValue (is.map (fun j =>
      if (if inverse then 2^256-hConstant else hConstant).testBit (j+3)
      then ({wire:=some flag,flip:=false} : MappedBit)
      else {wire:=none,flip:=false})) s=
      is.foldr (fun j acc =>
        (if (if inverse then 2^256-hConstant else hConstant).testBit (j+3)
          then s flag else false).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih]
    cases h : (if inverse then 2^256-hConstant else hConstant).testBit (j+3) <;>
      simp [h,MappedBit.value]

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem k_list_value (is : List Nat) (flag : Wire) (inverse : Bool)
    (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (kConstant inverse false).testBit (j+1)
      let b := (kConstant inverse true).testBit (j+1)
      if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc =>
        (if s flag then (kConstant inverse true).testBit (j+1)
          else (kConstant inverse false).testBit (j+1)).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem hBits_value (w : Nat → Wire) (inverse : Bool) (s : BasisState) :
    mappedValue (hBits w inverse) s=if s (w 1028) then
      (if inverse then 2^256-hConstant else hConstant)/8 else 0 := by
  rw [hBits,h_list_value]
  exact hScalar_value inverse (s (w 1028))

theorem kBits_value (w : Nat → Wire) (inverse : Bool) (s : BasisState) :
    mappedValue (kBits w inverse) s=kConstant inverse (s (w 1028))/2 := by
  rw [kBits,k_list_value]
  exact kScalar_value inverse (s (w 1028))

theorem hConstant_low_zero : hConstant%8=0 := by decide
theorem kConstant_low_one (inverse odd : Bool) : kConstant inverse odd%2=1 := by
  cases inverse <;> cases odd <;> decide

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.hScalar_value
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kScalar_value
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.hBits_value
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kBits_value
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.hConstant_low_zero
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kConstant_low_one
