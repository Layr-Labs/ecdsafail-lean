import ECDSAAdd.Arithmetic.RecordedRailDeferRolling
import ECDSAAdd.Arithmetic.RecordedRailMirrorDebt

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer
open ECDSAAdd.Math.RecordedCarryWordMirror

private theorem none_debt (n : Nat) (m carry : List Bool) :
    debt (List.replicate n none) m carry=false := by
  induction n generalizing carry with
  | zero => rfl
  | succ n ih => cases carry <;> simp [List.replicate_succ,debt,ih]

private theorem none_filter (n : Nat) :
    (List.replicate n (none : Option Nat)).filterMap id=[] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

/-- The final wrapped chunk uses only the prefix of the same real bank, with
no old-record corrections. Its complete result comes from actual ripple gates. -/
theorem wrapped_result (a b bank : List Wire) (incoming unused : Wire)
    (bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : RecordedRailVented.Ready a b (some incoming) bank unused bits) :
    RecordedRailRipple.UnsignedResult a b (bank.take (a.length-2)) (some incoming) bits phase
      (runWithTape (RecordedRailRipple.ripple a b (some incoming) (bank.take (a.length-2))
        (List.replicate (a.length-2) none)) m cursor ⟨phase,bits⟩) := by
  obtain ⟨align,nd,clean,_⟩ := ready
  let work := bank.take (a.length-2)
  let slots : List (Option Nat) := List.replicate (a.length-2) none
  have workLength : work.length=a.length-2 := by
    simp only [work,List.length_take]
    apply Nat.min_eq_left
    have bankLength := align.2.2
    omega
  have aligned : RecordedRailRipple.Aligned a b work slots :=
    ⟨align.1,align.2.1,workLength,by simp [slots,workLength]⟩
  have ndWork : ([incoming]++a++b++work).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    have split := congrArg (List.count q) (List.take_append_drop (a.length-2) bank)
    simp only [List.count_append] at split
    simp only [Option.toList_some,List.count_cons,List.count_append,List.count_nil,work] at h ⊢
    omega
  have cleanWork : ∀q∈work,bits q=false := by
    intro q hq
    exact clean q (List.mem_of_mem_take hq)
  have readyWork : RecordedRailRipple.Ready a b (some incoming) work slots bits cursor :=
    ⟨aligned,ndWork,cleanWork,by simp [slots,none_filter]⟩
  have shape := RecordedRailRipple.aligned_shape a b work slots aligned
  have noPhase : RecordedRailRipple.phaseDebt a b (RecordedRailRipple.incomingValue (some incoming) bits)
      slots bits m=false := by
    rw [RecordedRailRipple.phaseDebt_word a b work slots shape]
    exact none_debt (a.length-2) m _
  have result := RecordedRailRipple.unsignedContract_of_aligned a b work slots aligned
    (some incoming) bits phase m cursor readyWork
  simpa only [noPhase,Bool.xor_false,work,slots] using result

/-- Actual last wrapped word and following bare MX. The old boundary's own
measurement creates the final saved debt; no old outcome repairs this MX. -/
theorem finish_state (a b bank : List Wire) (incoming unused : Wire)
    (bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : RecordedRailVented.Ready a b (some incoming) bank unused bits) :
    let r := runWithTape (RecordedRailRipple.ripple a b (some incoming) (bank.take (a.length-2))
      (List.replicate (a.length-2) none)) m cursor ⟨phase,bits⟩
    runWithTape (finish a b bank incoming) m cursor ⟨phase,bits⟩=
      ⟨phase ^^ (m.getD (cursor+(a.length-2)) false && bits incoming),writeBit r.basis incoming false⟩ := by
  let work := bank.take (a.length-2)
  let slots : List (Option Nat) := List.replicate (a.length-2) none
  let r := runWithTape (RecordedRailRipple.ripple a b (some incoming) work slots) m cursor ⟨phase,bits⟩
  have result := wrapped_result a b bank incoming unused bits phase m cursor ready
  obtain ⟨hp,ha,hvalue,houtside,hwork⟩ := result
  change r.phase=phase at hp
  have hni : incoming∉b := by
    have first := List.nodup_cons.mp (by simpa only [Option.toList_some,List.singleton_append,List.append_assoc] using ready.2.1)
    intro h
    exact first.1 (by simp [h])
  have hi : r.basis incoming=bits incoming := houtside incoming hni
  have lengths : (bank.take (a.length-2)).length=a.length-2 := by
    simp only [List.length_take]
    apply Nat.min_eq_left
    have h := ready.1.2.2
    omega
  have aligned : RecordedRailRipple.Aligned a b work slots :=
    ⟨ready.1.1,ready.1.2.1,lengths,by simp [slots,lengths,work]⟩
  have counts := RecordedRailRipple.aligned_counts a b work slots aligned (some incoming)
  dsimp only
  rw [finish,runWithTape_append]
  change runWithTape (bareMX incoming) m
    (cursor+recordedMeasurementCount (RecordedRailRipple.ripple a b (some incoming) work slots)) r=_
  rw [counts.2,bare_state,hp,hi]

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.wrapped_result
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.finish_state
