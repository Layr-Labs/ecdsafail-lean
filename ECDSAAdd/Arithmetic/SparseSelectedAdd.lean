import ECDSAAdd.Arithmetic.MappedAdder

set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- Repeated immutable controller wires plus one literal-zero high bit.
No controller bank or One register is materialized. -/
def sparseSelectedBits (controllers : List Wire) : List MappedBit :=
  controllers.map (fun q => {wire:=some q,flip:=false})++[{wire:=none,flip:=false}]

/-- Retain overflow in the zero high bit. This variant uses n clean carry
wires, n Toffolis and n measurements, one extra measurement versus the
updated-bit prototype. The existing field layout supplies that spare carry. -/
def sparseSelectedRetainedAdd (controllers xs carry : List Wire) (cin cout : Wire) : Program :=
  mappedAdd (sparseSelectedBits controllers) (xs++[cout]) carry cin

theorem sparseSelectedBits_length (controllers : List Wire) :
    (sparseSelectedBits controllers).length=controllers.length+1 := by
  simp [sparseSelectedBits]

theorem sparseSelectedBits_wires (controllers : List Wire) :
    mappedWires (sparseSelectedBits controllers)=controllers := by
  induction controllers with
  | nil => rfl
  | cons q qs ih =>
    change q::mappedWires (sparseSelectedBits qs)=q::qs
    rw [ih]

theorem sparseSelectedBits_value (controllers : List Wire) (bits : BasisState) :
    mappedValue (sparseSelectedBits controllers) bits=regValue controllers bits := by
  induction controllers with
  | nil => simp [sparseSelectedBits,mappedValue,MappedBit.value,regValue]
  | cons q qs ih =>
    simpa [sparseSelectedBits,mappedValue,MappedBit.value,regValue,Bool.toNat,Bool.cond_eq_ite] using
      congrArg (fun a => (bits q).toNat+2*a) ih

theorem sparseSelectedRetainedAdd_counts (controllers xs carry : List Wire) (cin cout : Wire)
    (hl : controllers.length=xs.length) (hc : carry.length=xs.length) :
    toffoliCount (sparseSelectedRetainedAdd controllers xs carry cin cout)=xs.length ∧
    measurementCount (sparseSelectedRetainedAdd controllers xs carry cin cout)=xs.length := by
  have h := mappedAdd_counts (sparseSelectedBits controllers) (xs++[cout]) carry cin
    (by simp [sparseSelectedBits_length,hl]) (by simp [hc])
  simpa [sparseSelectedRetainedAdd] using h

theorem sparseSelectedRetainedAdd_wires (controllers xs carry : List Wire) (cin cout : Wire) :
    wires (sparseSelectedRetainedAdd controllers xs carry cin cout)⊆
      (cout::cin::(controllers++xs++carry)).toFinset := by
  have h := mappedAdd_wires_subset (sparseSelectedBits controllers) (xs++[cout]) carry cin
  rw [sparseSelectedBits_wires] at h
  apply h.trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton,or_assoc] at hq ⊢
  tauto

end ECDSAAdd.Arithmetic
