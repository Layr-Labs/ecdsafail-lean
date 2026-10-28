import ECDSAAdd.Arithmetic.RecordedRailRippleProof
import ECDSAAdd.Arithmetic.RecordedRailRippleLayout

namespace ECDSAAdd.Arithmetic.RecordedRailRipple

/-- Numeric port alignment establishes the complete emitted ripple contract;
the caller never supplies an assumed arithmetic or phase result. -/
theorem unsignedContract_of_aligned (a b work : List Wire) (slots : List (Option Nat))
    (h : Aligned a b work slots) (prev : Option Wire) :
    UnsignedContract a b prev work slots :=
  unsignedContract_of_shape a b work slots (aligned_shape a b work slots h)

/-- Whole-ripple resources include the carry-in, every output/source site and
every old-record correction operand. These are component, not stage, counts. -/
theorem certificate256 (a b work : List Wire) (slots : List (Option Nat))
    (aligned : Aligned a b work slots) (width : a.length=256)
    (prev : Option Wire) :
    recordedToffoliCount (ripple a b prev work slots)=255 ∧
    recordedMeasurementCount (ripple a b prev work slots)=254 ∧
    (recordedWires (ripple a b prev work slots)).card ≤767 := by
  have counts := aligned_counts a b work slots aligned prev
  have support := ripple_site_bound a b work slots (aligned_shape a b work slots aligned) prev
  have hp : prev.toList.length ≤1 := by cases prev <;> simp
  rcases aligned with ⟨_,hb,hw,_⟩
  rw [width] at counts
  exact ⟨counts.1,counts.2,by omega⟩

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.unsignedContract_of_aligned
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.certificate256
