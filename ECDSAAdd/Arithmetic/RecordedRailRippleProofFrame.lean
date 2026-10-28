import ECDSAAdd.Arithmetic.RecordedRailRippleInvariant
import ECDSAAdd.Arithmetic.RecordedRailRippleResources

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple
open RecordedRailCarry

/-- A suffix inherits literal layout uniqueness. -/
theorem suffix_nodup (headPrefix suffix : List Wire) (h : (headPrefix++suffix).Nodup) :
    suffix.Nodup := by
  induction headPrefix with
  | nil => simpa using h
  | cons x xs ih => exact ih (List.nodup_cons.mp h).2

/-- A named layout site cannot occur later in its literal layout. -/
theorem middle_not_mem (headPrefix suffix : List Wire) (q : Wire)
    (h : (headPrefix++q::suffix).Nodup) : q∉suffix :=
  (List.nodup_cons.mp (suffix_nodup headPrefix (q::suffix) h)).1

/-- Phase debt is a function only of the original source bits. -/
theorem phaseDebt_congr (a b : List Wire) (incoming : Bool) (slots : List (Option Nat))
    (bits other : BasisState) (m : List Bool)
    (ha : ∀q∈a,bits q=other q) (hb : ∀q∈b,bits q=other q) :
    phaseDebt a b incoming slots bits m=phaseDebt a b incoming slots other m := by
  induction a generalizing b incoming slots with
  | nil => rfl
  | cons a0 as ih =>
    cases as with
    | nil => rfl
    | cons a1 as =>
      cases as with
      | nil => rfl
      | cons a2 as =>
        cases b with
        | nil => rfl
        | cons b0 bs =>
          cases bs with
          | nil => rfl
          | cons b1 bs =>
            cases bs with
            | nil => rfl
            | cons b2 bs =>
              cases slots with
              | nil => rfl
              | cons d ds =>
                simp only [phaseDebt,ha a0 (by simp),hb b0 (by simp)]
                congr 1
                exact ih (b1::b2::bs) _ ds
                  (fun q hq => ha q (by simp [hq]))
                  (fun q hq => hb q (by simp [hq]))

/-- Dressed head state produced by the literal source carry compute. -/
def computedBits (a b c : Wire) (prev : Option Wire) (bits : BasisState) : BasisState :=
  writeBit (writeBit (writeBit bits a (bits a ^^ incomingValue prev bits))
    b (bits b ^^ incomingValue prev bits)) c
    (carryFn (bits a) (bits b) (incomingValue prev bits))

theorem carryStep_state (a b c : Wire) (prev : Option Wire)
    (nd : (prev.toList++[a,b,c]).Nodup) (bits : BasisState) (phase : Bool)
    (m : List Bool) (hc : bits c=false) :
    run (carryStep a b prev c) m ⟨phase,bits⟩=⟨phase,computedBits a b c prev bits⟩ := by
  cases prev with
  | none =>
    simp only [Option.toList_none,List.nil_append] at nd
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd
    obtain ⟨⟨hab,hac⟩,hbc⟩ := nd
    apply State.extensionality
    · rfl
    · funext q
      by_cases ha : q=a <;> by_cases hb : q=b <;> by_cases hk : q=c <;>
        simp_all [carryStep,run,computedBits,incomingValue,carryFn,writeBit,Function.update]
  | some p =>
    have hn : [a,b,p,c].Nodup := by
      simpa [List.nodup_cons,List.mem_cons,not_or,and_assoc,and_left_comm,and_comm,
        ne_comm] using nd
    rw [carryStep_some a b p c hn ⟨phase,bits⟩ m hc]
    rfl

/-- Optional old correction cancels the original record debt before fresh MX. -/
theorem oldCorrection_state (c : Wire) (slot : Option Nat) (bits : BasisState)
    (phase : Bool) (m : List Bool) (cursor : Nat) :
    runWithTape (oldCorrection c slot) m cursor
      ⟨phase ^^ recordDebt slot m (bits c),bits⟩=⟨phase,bits⟩ := by
  cases slot with
  | none => simp [oldCorrection,recordDebt,runWithTape]
  | some j => exact RecordedCarryPhase.recorded_Z_cancel phase (bits c) m j cursor bits c rfl

/-- Uniform unwind theorem with arbitrary spectator state and optional carry-in. -/
theorem unwind_state (a b c : Wire) (prev : Option Wire)
    (nd : (prev.toList++[a,b,c]).Nodup) (bits : BasisState) (phase : Bool)
    (m : List Bool)
    (hc : bits c=((bits a && bits b) ^^ incomingValue prev bits)) :
    run (unwindStep a b prev c) m ⟨phase,bits⟩=
      ⟨phase,writeBit (writeBit (writeBit bits c false)
        a (bits a ^^ incomingValue prev bits))
        b (bits b ^^ (bits a ^^ incomingValue prev bits))⟩ := by
  cases prev with
  | none =>
    simp only [Option.toList_none,List.nil_append] at nd
    have hcn : bits c=(bits a && bits b) := by simpa only [incomingValue,Bool.xor_false] using hc
    have h := unwindStep_none a b c nd ⟨phase,bits⟩ m hcn
    rw [h]
    have hac : a≠c := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
        not_or,not_false_eq_true,and_true] at nd
      exact nd.1.2
    congr 1
    funext q
    by_cases ha : q=a <;> by_cases hb : q=b <;> by_cases hk : q=c <;>
      simp_all [incomingValue,writeBit,Function.update]
  | some p =>
    have hn : [a,b,p,c].Nodup := by
      simpa [List.nodup_cons,List.mem_cons,not_or,and_assoc,and_left_comm,and_comm,
        ne_comm] using nd
    exact unwindStep_some a b p c hn ⟨phase,bits⟩ m hc

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.phaseDebt_congr
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.carryStep_state
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.oldCorrection_state
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.unwind_state
