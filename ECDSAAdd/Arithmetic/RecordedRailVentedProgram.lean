import ECDSAAdd.Arithmetic.RecordedRailRippleProofLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailVented
open RecordedRailCarry

/-- Literal vented top action, after the top carry was computed and its two
controls dressed: restore the source, then write the target low sum. -/
def topFinish (a b : Wire) : Option Wire → Program
  | none => [.CX a b]
  | some p => [.CX p a,.CX a b]

def top (a b cout : Wire) (prev : Option Wire) : RecordedProgram :=
  embedRecorded (carryStep a b prev cout ++ topFinish a b prev)

/-- Literal pinned9db normal vented rail: compute all width carries, retain
cout, finish the top, and fresh-MX unwind only the width-minus-one owned rails.
This forward scope has no saved old-record corrections. -/
def vented : List Wire → List Wire → Option Wire → List Wire → Wire → RecordedProgram
  | [a], [b], prev, [], cout => top a b cout prev
  | a0::a1::as, b0::b1::bs, prev, c::cs, cout =>
      embedRecorded (carryStep a0 b0 prev c) ++
      vented (a1::as) (b1::bs) (some c) cs cout ++
      embedRecorded (unwindStep a0 b0 prev c)
  | _, _, _, _, _ => []

/-- Structural nonempty equal-width port certificate. -/
inductive Shape : List Wire → List Wire → List Wire → Prop
  | one (a b : Wire) : Shape [a] [b] []
  | step (a0 a1 b0 b1 c : Wire) (as bs cs : List Wire)
      (tail : Shape (a1::as) (b1::bs) cs) : Shape (a0::a1::as) (b0::b1::bs) (c::cs)

def Aligned (a b work : List Wire) : Prop :=
  0<a.length ∧ b.length=a.length ∧ work.length=a.length-1

theorem shape_lengths (a b work : List Wire) (shape : Shape a b work) : Aligned a b work := by
  induction shape with
  | one a b => simp [Aligned]
  | step a0 a1 b0 b1 c as bs cs shape ih =>
    simp only [Aligned,List.length_cons] at ih ⊢
    omega

theorem aligned_shape (a b work : List Wire) (h : Aligned a b work) : Shape a b work := by
  induction a generalizing b work with
  | nil => simp [Aligned] at h
  | cons a0 rest ih =>
    obtain ⟨ha,hb,hw⟩ := h
    cases rest with
    | nil =>
      cases b with
      | nil => simp at hb
      | cons b0 bs =>
        have bn : bs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hb; omega)
        have wn : work=[] := List.eq_nil_of_length_eq_zero (by change work.length=0 at hw; exact hw)
        subst bs; subst work
        exact Shape.one a0 b0
    | cons a1 as =>
      cases b with
      | nil => simp at hb
      | cons b0 bs =>
        cases bs with
        | nil => simp only [List.length_cons,List.length_nil] at hb; omega
        | cons b1 bs =>
          cases work with
          | nil => simp only [List.length_cons,List.length_nil] at hw; omega
          | cons c cs =>
            apply Shape.step
            apply ih
            simp only [Aligned,List.length_cons] at ⊢
            simp only [List.length_cons] at hb hw
            omega

theorem top_counts (a b cout : Wire) (prev : Option Wire) :
    recordedToffoliCount (top a b cout prev)=1 ∧ recordedMeasurementCount (top a b cout prev)=0 := by
  cases prev <;> simp [top,topFinish,carryStep,embedRecorded,recordedToffoliCount,
    recordedMeasurementCount,toffoliCount,measurementCount]

theorem counts (a b work : List Wire) (shape : Shape a b work) (prev : Option Wire) (cout : Wire) :
    recordedToffoliCount (vented a b prev work cout)=a.length ∧
    recordedMeasurementCount (vented a b prev work cout)=a.length-1 := by
  induction shape generalizing prev with
  | one a b => simpa only [vented,List.length_cons,List.length_nil] using top_counts a b cout prev
  | step a0 a1 b0 b1 c as bs cs shape ih =>
    have high := ih (some c)
    simp only [vented,recordedToffoliCount_append,recordedMeasurementCount_append]
    cases prev <;> simp [carryStep,unwindStep,embedRecorded,recordedToffoliCount,
      recordedMeasurementCount,toffoliCount,measurementCount,high,List.length_cons]
    all_goals omega

def sites (a b work : List Wire) (prev : Option Wire) (cout : Wire) : Finset Wire :=
  (prev.toList++a++b++work++[cout]).toFinset

/-- The actual emitted support contains only declared real sites. No zero
source, ancilla extension, or other ghost operand enters this program. -/
theorem support (a b work : List Wire) (shape : Shape a b work) (prev : Option Wire) (cout : Wire) :
    recordedWires (vented a b prev work cout) ⊆ sites a b work prev cout := by
  induction shape generalizing prev with
  | one a b =>
    cases prev <;> simp [vented,top,topFinish,carryStep,embedRecorded,recordedWires,
      RecordedInstr.quantumWires,Instr.wires,sites,Finset.insert_subset_iff]
  | step a0 a1 b0 b1 c as bs cs shape ih =>
    have high := ih (some c)
    have inclusion : sites (a1::as) (b1::bs) cs (some c) cout ⊆
        sites (a0::a1::as) (b0::b1::bs) (c::cs) prev cout := by
      intro q hq
      simp only [sites,List.mem_toFinset,List.mem_append,List.mem_cons,
        Option.toList_some,List.not_mem_nil,or_false] at hq ⊢
      tauto
    have tail := high.trans inclusion
    simp only [vented,recordedWires_append,Finset.union_subset_iff]
    cases prev <;>
      simp [carryStep,unwindStep,embedRecorded,recordedWires,RecordedInstr.quantumWires,
        Instr.wires,correctionWires,sites,Finset.insert_subset_iff] at tail ⊢
    all_goals exact tail

theorem wellFormed (a b work : List Wire) (shape : Shape a b work) (prev : Option Wire)
    (cout : Wire) (cursor : Nat) : RecordedWellFormedAt cursor (vented a b prev work cout) := by
  induction shape generalizing prev cursor with
  | one a b => exact embedRecorded_wellFormed _ _
  | step a0 a1 b0 b1 c as bs cs shape ih =>
    simpa only [vented,RecordedWellFormedAt_append,embedRecorded_wellFormed,
      carry_measurements,Nat.add_zero,true_and,and_true] using ih (some c) cursor

end ECDSAAdd.Arithmetic.RecordedRailVented
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.aligned_shape
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.counts
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.support
