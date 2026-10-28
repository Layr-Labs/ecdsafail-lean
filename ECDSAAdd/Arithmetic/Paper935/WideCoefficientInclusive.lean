import ECDSAAdd.Arithmetic.Paper935.WideCoefficientInput
import ECDSAAdd.Arithmetic.Paper935.ExitWidths
import ECDSAAdd.Arithmetic.Paper935.DecoderWindow

namespace ECDSAAdd.Arithmetic.Paper935

/-- The minimum signed value has magnitude exactly 2^280. -/
theorem wideMagnitudeFold_parts_le (a : Nat) (ha : a≤2^280) :
    a%2^256<2^256 ∧ a/2^256≤2^24 := by
  refine ⟨Nat.mod_lt _ (by positivity),?_⟩
  have h := Nat.div_le_div_right (c := 2^256) ha
  have endpoint : 2^280 / 2^256 = (2^24 : Nat) := by decide +kernel
  simpa only [endpoint] using h

theorem wideMagnitudeFold_bound_le (a : Nat) (ha : a≤2^280) :
    wideMagnitudeFold a<2*fold32Prime := by
  obtain ⟨lo,hi⟩ := wideMagnitudeFold_parts_le a ha
  norm_num [wideMagnitudeFold,fold32Prime] at *
  omega

theorem wideSignedFold_bound_le (z : Int) (hz : z.natAbs≤2^280) :
    wideSignedFold z<2*fold32Prime := by
  unfold wideSignedFold
  split_ifs
  · exact wideReflect_bound _ (wideMagnitudeFold_bound_le _ hz)
  · exact wideMagnitudeFold_bound_le _ hz

theorem wideSignedFold_mod_le (z : Int) (hz : z.natAbs≤2^280) :
    (wideSignedFold z : ZMod fold32Prime)=(z : ZMod fold32Prime) := by
  unfold wideSignedFold
  split_ifs with negative
  · rw [wideReflect_mod _ (wideMagnitudeFold_bound_le _ hz),wideMagnitudeFold_mod]
    have h : (z.natAbs : Int)=-z := by rw [Int.natCast_natAbs,abs_of_neg negative]
    have cast := congrArg (fun n : Int => (n : ZMod fold32Prime)) h
    simp only [Int.cast_natCast,Int.cast_neg] at cast
    rw [cast,neg_neg]
  · rw [wideMagnitudeFold_mod]
    have h : (z.natAbs : Int)=z := by rw [Int.natCast_natAbs,abs_of_nonneg (by omega)]
    simpa only [Int.cast_natCast] using congrArg (fun n : Int => (n : ZMod fold32Prime)) h

/-- Multiplication by either sign preserves the magnitude hypothesis. -/
theorem wideSignedFold_signed_le (negate : Bool) (v : Int) (hv : v.natAbs≤2^280) :
    let z := if negate then -v else v
    wideSignedFold z<2*fold32Prime ∧
      (wideSignedFold z : ZMod fold32Prime)=(z : ZMod fold32Prime) := by
  have h : (if negate then -v else v).natAbs≤2^280 := by
    cases negate <;> simpa only [Bool.false_eq_true,if_false,if_true,Int.natAbs_neg] using hv
  exact ⟨wideSignedFold_bound_le _ h,wideSignedFold_mod_le _ h⟩

theorem fold32PlacedReduce_wide_input_le (f : Wire → Wire) (hf : Function.Injective f)
    (z : Int) (hz : z.natAbs≤2^280) (s : State) (m : List Bool)
    (ready : Fold32PlacedReady f s.basis) (enabled : s.basis (f 0)=true)
    (flag : s.basis (f 290)=false)
    (encoded : regValue (fold32Word.map f) s.basis=wideSignedFold z) :
    let out := run (fold32PlacedReduce f) m s
    regValue (fold32Word.map f) out.basis<fold32Prime ∧
    (regValue (fold32Word.map f) out.basis : ZMod fold32Prime)=(z : ZMod fold32Prime) ∧
    Fold32PlacedReady f out.basis ∧
    out.basis (f 290)=decide (wideSignedFold z<fold32Prime) ∧
    out.basis (f 0)=true ∧ out.phase=s.phase := by
  have bound : regValue (fold32Word.map f) s.basis<2*fold32Prime := by
    rw [encoded]
    exact wideSignedFold_bound_le z hz
  have h := fold32PlacedReduce_contract f hf s m ready enabled flag bound
  dsimp only at h ⊢
  rw [encoded] at h
  refine ⟨?_,?_,h.2.1,h.2.2.1,h.2.2.2⟩
  · rw [h.1]
    exact Nat.mod_lt _ (by norm_num [fold32Prime])
  · rw [h.1,ZMod.natCast_mod]
    exact wideSignedFold_mod_le z hz


/-- Width alone includes the most negative two's-complement value. -/
theorem WindowRow.value_natAbs_le (r : WindowRow) (s : BasisState) :
    (r.value s).natAbs≤2^r.payload.length := by
  have h := r.value_fits s
  unfold PayloadFits at h
  have habs : |r.value s|≤((2^r.payload.length : Nat) : Int) :=
    abs_le.mpr ⟨h.1, le_of_lt h.2⟩
  rw [← Int.natCast_natAbs] at habs
  exact_mod_cast habs

/-- Actual compiler exit geometry discharges the inclusive fold hypothesis. -/
theorem compileAuthorWalk_exit_fv_natAbs_le (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (s : BasisState) :
    ((walkExitBank walkSeedBank slots).fv.value s).natAbs≤2^280 := by
  have width := (compileAuthorWalk_exit_widths slots compiled).2.2.1
  have bound := (walkExitBank walkSeedBank slots).fv.value_natAbs_le s
  simpa only [width] using bound

theorem compileAuthorWalk_exit_fv_fold (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (s : BasisState) (negate : Bool) :
    let v := (walkExitBank walkSeedBank slots).fv.value s
    let z := if negate then -v else v
    wideSignedFold z<2*fold32Prime ∧
      (wideSignedFold z : ZMod fold32Prime)=(z : ZMod fold32Prime) :=
  wideSignedFold_signed_le negate _ (compileAuthorWalk_exit_fv_natAbs_le slots compiled s)

end ECDSAAdd.Arithmetic.Paper935
