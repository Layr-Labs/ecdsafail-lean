import ECDSAAdd.Arithmetic.RecordedRailRippleInvariant
import ECDSAAdd.Arithmetic.RecordedRailRippleResources

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple
open RecordedRailCarry

/-- Numeric port lengths suffice for the emitted recursion. No caller must
assume a semantic property merely to obtain a resource or layout certificate. -/
theorem aligned_shape (a b work : List Wire) (slots : List (Option Nat))
    (h : Aligned a b work slots) : Shape a b work slots := by
  induction a generalizing b work slots with
  | nil => simp [Aligned] at h
  | cons a0 rest ih =>
    rcases h with ⟨ha,hb,hw,hd⟩
    cases rest with
    | nil =>
      cases b with
      | nil => simp at hb
      | cons b0 bs =>
        have bnil : bs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hb; omega)
        have wnil : work=[] := List.eq_nil_of_length_eq_zero (by change work.length=0 at hw; exact hw)
        have dnil : slots=[] := List.eq_nil_of_length_eq_zero (by rw [wnil] at hd; simpa using hd)
        subst bs; subst work; subst slots
        exact Shape.one a0 b0
    | cons a1 tail =>
      cases b with
      | nil => simp at hb
      | cons b0 bs =>
        cases bs with
        | nil => simp at hb
        | cons b1 bt =>
          cases tail with
          | nil =>
            have bnil : bt=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hb; omega)
            have wnil : work=[] := List.eq_nil_of_length_eq_zero (by change work.length=0 at hw; exact hw)
            have dnil : slots=[] := List.eq_nil_of_length_eq_zero (by rw [wnil] at hd; simpa using hd)
            subst bt; subst work; subst slots
            exact Shape.two a0 a1 b0 b1
          | cons a2 as =>
            cases bt with
            | nil => simp only [List.length_cons,List.length_nil] at hb; omega
            | cons b2 bs =>
              cases work with
              | nil => simp only [List.length_cons,List.length_nil] at hw; omega
              | cons c cs =>
                cases slots with
                | nil => simp at hd
                | cons d ds =>
                  apply Shape.step
                  apply ih
                  simp only [Aligned,List.length_cons] at ⊢
                  simp only [List.length_cons] at hb hw hd
                  omega

theorem aligned_counts (a b work : List Wire) (slots : List (Option Nat))
    (h : Aligned a b work slots) (prev : Option Wire) :
    recordedToffoliCount (ripple a b prev work slots)=a.length-1 ∧
    recordedMeasurementCount (ripple a b prev work slots)=a.length-2 :=
  ripple_counts a b work slots (aligned_shape a b work slots h) prev

/-- The explicit whole-ripple support includes all source, output, carry-in
and temporary carry sites, including every deferred correction operand. -/
theorem ripple_support (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) (prev : Option Wire) :
    recordedWires (ripple a b prev work slots) ⊆ sites a b prev work := by
  induction shape generalizing prev with
  | one a b =>
    cases prev <;> simp [ripple,topStep,embedRecorded,recordedWires,
      RecordedInstr.quantumWires,Instr.wires,sites,Finset.insert_subset_iff]
  | two a0 a1 b0 b1 =>
    cases prev <;> simp [ripple,terminalStep,embedRecorded,recordedWires,
      RecordedInstr.quantumWires,Instr.wires,sites,Finset.insert_subset_iff]
  | step a0 a1 a2 b0 b1 b2 c as bs cs d ds shape ih =>
    have high := ih (some c)
    have inclusion : sites (a1::a2::as) (b1::b2::bs) (some c) cs ⊆
        sites (a0::a1::a2::as) (b0::b1::b2::bs) prev (c::cs) := by
      intro q hq
      simp only [sites,List.mem_toFinset,List.mem_append,List.mem_cons,
        Option.toList_some,List.not_mem_nil,or_false] at hq ⊢
      tauto
    have tail := high.trans inclusion
    simp only [ripple,recordedWires_append,Finset.union_subset_iff]
    cases prev <;> cases d <;>
      simp [carryStep,unwindStep,oldCorrection,embedRecorded,recordedWires,
        RecordedInstr.quantumWires,Instr.wires,correctionWires,sites,Finset.insert_subset_iff] at tail ⊢
    all_goals exact tail

/-- Every deferred reference in this closed mirror belongs to the earlier
prefix. Fresh unwind measurements advance the cursor without replacing it. -/
theorem ripple_wellFormed (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) (prev : Option Wire) (cursor : Nat)
    (earlier : ∀j∈slots.filterMap id,j<cursor) :
    RecordedWellFormedAt cursor (ripple a b prev work slots) := by
  induction shape generalizing prev cursor with
  | one a b => exact embedRecorded_wellFormed _ _
  | two a0 a1 b0 b1 => exact embedRecorded_wellFormed _ _
  | step a0 a1 a2 b0 b1 b2 c as bs cs d ds shape ih =>
    have older : ∀j∈ds.filterMap id,j<cursor := by
      intro j hj
      apply earlier j
      cases d <;> simp [hj]
    have tail := ih (some c) cursor older
    have old : RecordedWellFormedAt
        (cursor+recordedMeasurementCount (ripple (a1::a2::as) (b1::b2::bs) (some c) cs ds))
        (oldCorrection c d) := by
      cases d with
      | none => trivial
      | some j =>
        have hj : j<cursor := earlier j (by simp)
        simp only [oldCorrection,RecordedWellFormedAt]
        exact ⟨by omega,trivial⟩
    simpa only [ripple,RecordedWellFormedAt_append,embedRecorded_wellFormed,
      recordedMeasurementCount_append,carry_measurements,(oldCorrection_counts c d).2,
      Nat.add_zero,Nat.zero_add,true_and,and_true] using And.intro tail old

/-- The single shared carry ladder has a transparent quantum-site bound.
Classical record ordinals contribute no hidden quantum positions. -/
theorem ripple_site_bound (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) (prev : Option Wire) :
    (recordedWires (ripple a b prev work slots)).card ≤
      a.length+b.length+work.length+prev.toList.length := by
  have h := Finset.card_le_card (ripple_support a b work slots shape prev)
  have bound := List.toFinset_card_le (prev.toList++a++b++work)
  simp only [sites] at h
  simp only [List.length_append] at bound
  omega

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.aligned_shape
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.ripple_support
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.ripple_wellFormed
