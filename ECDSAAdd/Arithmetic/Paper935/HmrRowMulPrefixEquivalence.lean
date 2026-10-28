import ECDSAAdd.Arithmetic.Paper935.HmrSourceNormalization
import Mathlib.Data.List.Induction
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulSourcePrograms
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulSpec
namespace ECDSAAdd.Arithmetic.Paper935

def rowMulPrefixAtomEq : RecordedInstr → RecordedInstr → Bool
  | .gate (.CCX a b c), .gate (.CCX x y z) => c == z && ((a == x && b == y) || (a == y && b == x))
  | a,b => a == b

theorem rowMulPrefixAtomEq_sound (a b : RecordedInstr) (h : rowMulPrefixAtomEq a b = true)
    (ctx : RecordedContext) (s : State) : runRecorded [a] ctx s = runRecorded [b] ctx s := by
  cases a with
  | phaseFromRecord k cs =>
    have e : RecordedInstr.phaseFromRecord k cs = b := by simpa [rowMulPrefixAtomEq] using h
    subst b
    rfl
  | gate ai =>
    cases b with
    | phaseFromRecord k cs =>
      cases ai <;> simp [rowMulPrefixAtomEq] at h
    | gate bi =>
      cases ai <;> cases bi <;> simp_all [rowMulPrefixAtomEq]
      rcases h.2 with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · simp_all
      · simp_all [runRecorded, runWithTape, recordedMeasurementCount, measurementCount, run, Bool.and_comm]

def rowMulPrefixPairSwap : RecordedInstr → RecordedInstr → Bool
  | .gate (.CX a t), .gate (.CX b u) => t == u && (a != t && b != t)
  | _,_ => false

theorem rowMulPrefixPairSwap_sound (a b : RecordedInstr) (h : rowMulPrefixPairSwap a b = true)
    (ctx : RecordedContext) (s : State) : runRecorded [a,b] ctx s = runRecorded [b,a] ctx s := by
  cases a with
  | phaseFromRecord k cs => simp [rowMulPrefixPairSwap] at h
  | gate ai =>
    cases b with
    | phaseFromRecord k cs => cases ai <;> simp [rowMulPrefixPairSwap] at h
    | gate bi =>
      cases ai <;> cases bi <;> simp_all [rowMulPrefixPairSwap]
      rename_i a t b u
      rcases h with ⟨eq,ha,hb⟩
      subst u
      apply Prod.ext
      · change run [.CX a t, .CX b t] (ctx.tape.drop ctx.cursor) s =
          run [.CX b t, .CX a t] (ctx.tape.drop ctx.cursor) s
        exact rowMul_cx_same_target a b t ha hb s _
      · rfl

def rowMulPrefixEq : RecordedProgram → RecordedProgram → Bool
  | [],[] => true
  | a::as,b::bs =>
    if rowMulPrefixAtomEq a b then rowMulPrefixEq as bs else
    match as,bs with
    | c::cs,d::ds => rowMulPrefixAtomEq a d && (rowMulPrefixAtomEq c b && (rowMulPrefixPairSwap a c && rowMulPrefixEq cs ds))
    | _,_ => false
  | _,_ => false

theorem rowMulPrefixEq_sound (p : RecordedProgram) : ∀ q, rowMulPrefixEq p q = true →
    ∀ ctx s, runRecorded p ctx s = runRecorded q ctx s := by
  induction p using List.twoStepInduction with
  | nil =>
    intro q h ctx s
    cases q with
    | nil => rfl
    | cons b bs => simp [rowMulPrefixEq] at h
  | singleton a =>
    intro q h ctx s
    cases q with
    | nil => simp [rowMulPrefixEq] at h
    | cons b bs =>
      cases bs with
      | nil =>
        have hab : rowMulPrefixAtomEq a b = true := by simpa [rowMulPrefixEq] using h
        exact rowMulPrefixAtomEq_sound a b hab ctx s
      | cons d ds => simp [rowMulPrefixEq] at h
  | cons_cons a c ps ih ihCons =>
    intro q h ctx s
    cases q with
    | nil => simp [rowMulPrefixEq] at h
    | cons b bs =>
      by_cases hab : rowMulPrefixAtomEq a b = true
      · have tail : rowMulPrefixEq (c::ps) bs = true := by
          cases bs <;> simpa only [rowMulPrefixEq, if_pos hab] using h
        change runRecorded ([a] ++ (c::ps)) ctx s = runRecorded ([b] ++ bs) ctx s
        rw [runRecorded_append, runRecorded_append, rowMulPrefixAtomEq_sound a b hab ctx s]
        exact ihCons c bs tail _ _
      · cases bs with
        | nil => simp [rowMulPrefixEq, hab] at h
        | cons d ds =>
          have parts : rowMulPrefixAtomEq a d = true ∧ rowMulPrefixAtomEq c b = true ∧
              rowMulPrefixPairSwap a c = true ∧ rowMulPrefixEq ps ds = true := by
            simpa only [rowMulPrefixEq, if_neg hab, Bool.and_eq_true] using h
          obtain ⟨had,hcb,hpair,htail⟩ := parts
          have pair : runRecorded [a,c] ctx s = runRecorded [b,d] ctx s := by
            calc
              _ = runRecorded [c,a] ctx s := rowMulPrefixPairSwap_sound a c hpair ctx s
              _ = runRecorded [b,d] ctx s := by
                change runRecorded ([c] ++ [a]) ctx s = runRecorded ([b] ++ [d]) ctx s
                rw [runRecorded_append, runRecorded_append, rowMulPrefixAtomEq_sound c b hcb ctx s]
                exact rowMulPrefixAtomEq_sound a d had _ _
          change runRecorded ([a,c] ++ ps) ctx s = runRecorded ([b,d] ++ ds) ctx s
          rw [runRecorded_append, runRecorded_append, pair]
          exact ih ds htail _ _

theorem rowMulPrefixEq_measurements (p q : RecordedProgram) (h : rowMulPrefixEq p q = true) :
    recordedMeasurementCount p = recordedMeasurementCount q := by
  have e := congrArg (fun r : State × RecordedContext => r.2.cursor)
    (rowMulPrefixEq_sound p q h ⟨[], 0⟩ ⟨false, fun _ => false⟩)
  simpa only [runRecorded_cursor, Nat.zero_add] using e

/-- The first two actual source-template uses, including their recorded instructions. -/
def rowMulSourcePrefix (ports : Array Wire) (start : Nat) (uses : List RowMulTemplateUse) :=
  (uses.take 2).flatMap (rowMulInstantiate ports start)
/-- Existing lift and fold programs placed using the ordered source ports. -/
def rowMulLegacyPrefix (ports : Array Wire) :=
  let w := rowMulPort ports 0
  embedRecorded (placedMagnitude
    (fusedPlacementMap ((0 :: List.range' 1 280 ++ List.range' 793 24).map w)) false ++
    placedRowFold (fusedPlacementMap (fusedFoldPlacement ((List.range' 1 280).map w)
      ((List.range' 537 256).map w) ((List.range' 793 24).map w))) false)
private theorem s2_checked : rowMulPrefixEq
    (rowMulSourcePrefix s2ForwardPorts s2ForwardMeasurementStart s2ForwardUses)
    (rowMulLegacyPrefix s2ForwardPorts) = true := by decide +kernel
private theorem s6_checked : rowMulPrefixEq
    (rowMulSourcePrefix s6ForwardPorts s6ForwardMeasurementStart s6ForwardUses)
    (rowMulLegacyPrefix s6ForwardPorts) = true := by decide +kernel
theorem s2ForwardPrefix_run (ctx : RecordedContext) (s : State) :
    runRecorded (rowMulSourcePrefix s2ForwardPorts s2ForwardMeasurementStart s2ForwardUses) ctx s =
    runRecorded (rowMulLegacyPrefix s2ForwardPorts) ctx s := rowMulPrefixEq_sound _ _ s2_checked ctx s
theorem s6ForwardPrefix_run (ctx : RecordedContext) (s : State) :
    runRecorded (rowMulSourcePrefix s6ForwardPorts s6ForwardMeasurementStart s6ForwardUses) ctx s =
    runRecorded (rowMulLegacyPrefix s6ForwardPorts) ctx s := rowMulPrefixEq_sound _ _ s6_checked ctx s
theorem s2ForwardPrefix_measurements :
    recordedMeasurementCount (rowMulSourcePrefix s2ForwardPorts s2ForwardMeasurementStart s2ForwardUses) =
    recordedMeasurementCount (rowMulLegacyPrefix s2ForwardPorts) :=
  rowMulPrefixEq_measurements _ _ s2_checked

theorem s6ForwardPrefix_measurements :
    recordedMeasurementCount (rowMulSourcePrefix s6ForwardPorts s6ForwardMeasurementStart s6ForwardUses) =
    recordedMeasurementCount (rowMulLegacyPrefix s6ForwardPorts) :=
  rowMulPrefixEq_measurements _ _ s6_checked

end ECDSAAdd.Arithmetic.Paper935
