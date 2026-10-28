import ECDSAAdd.Arithmetic.RecordedRailRippleProgram

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple
open RecordedRailCarry

/-- Pure list-shape certificate for the emitted normal wrapped recursion.
It constrains layouts and record slots, never quantum input values or phases. -/
inductive Shape : List Wire → List Wire → List Wire → List (Option Nat) → Prop
  | one (a b : Wire) : Shape [a] [b] [] []
  | two (a0 a1 b0 b1 : Wire) : Shape [a0,a1] [b0,b1] [] []
  | step (a0 a1 a2 b0 b1 b2 c : Wire) (as bs cs : List Wire)
      (d : Option Nat) (ds : List (Option Nat))
      (tail : Shape (a1::a2::as) (b1::b2::bs) cs ds) :
      Shape (a0::a1::a2::as) (b0::b1::b2::bs) (c::cs) (d::ds)

private theorem compute_counts (a b : Wire) (prev : Option Wire) (c : Wire) :
    recordedToffoliCount (embedRecorded (carryStep a b prev c))=1 ∧
    recordedMeasurementCount (embedRecorded (carryStep a b prev c))=0 := by
  cases prev <;> simp [carryStep,embedRecorded,recordedToffoliCount,
    recordedMeasurementCount,toffoliCount,measurementCount]

private theorem unwind_counts (a b : Wire) (prev : Option Wire) (c : Wire) :
    recordedToffoliCount (embedRecorded (unwindStep a b prev c))=0 ∧
    recordedMeasurementCount (embedRecorded (unwindStep a b prev c))=1 := by
  cases prev <;> simp [unwindStep,embedRecorded,recordedToffoliCount,
    recordedMeasurementCount,toffoliCount,measurementCount]

/-- Width-exact instruction count, including every optional old-record phase
and every independently measured fresh unwind outcome. -/
theorem ripple_counts (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) (prev : Option Wire) :
    recordedToffoliCount (ripple a b prev work slots)=a.length-1 ∧
    recordedMeasurementCount (ripple a b prev work slots)=a.length-2 := by
  induction shape generalizing prev with
  | one a b => simpa only [ripple,List.length_cons,List.length_nil] using top_counts a b prev
  | two a0 a1 b0 b1 =>
    simpa only [ripple,List.length_cons,List.length_nil] using terminal_counts a0 a1 b0 b1 prev
  | step a0 a1 a2 b0 b1 b2 c as bs cs d ds shape ih =>
    have head := compute_counts a0 b0 prev c
    have last := unwind_counts a0 b0 prev c
    have old := oldCorrection_counts c d
    have tail := ih (some c)
    simp only [ripple,recordedToffoliCount_append,recordedMeasurementCount_append,
      head.1,head.2,last.1,last.2,old.1,old.2,tail.1,tail.2,List.length_cons]
    constructor <;> omega

/-- All emitted sites are finite and explicit; correction operands are included. -/
def sites (a b : List Wire) (prev : Option Wire) (work : List Wire) : Finset Wire :=
  (prev.toList++a++b++work).toFinset

/-- Layout lengths implied by the recursive certificate. Numeric Aligned-to-Shape
conversion remains a separate finite-list obligation for the general caller. -/
theorem shape_lengths (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) :
    0<a.length ∧ b.length=a.length ∧ work.length=a.length-2 ∧ slots.length=work.length := by
  induction shape with
  | one a b => simp
  | two a0 a1 b0 b1 => simp
  | step a0 a1 a2 b0 b1 b2 c as bs cs d ds shape ih =>
    simp only [List.length_cons] at *
    omega

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.ripple_counts
