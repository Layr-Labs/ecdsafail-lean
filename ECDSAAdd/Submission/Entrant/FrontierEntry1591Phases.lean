import ECDSAAdd.Submission.Entrant.FrontierEntry1591PhaseProgram
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Boundary

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1
attribute [local irreducible] run wires NewStackOB5.stackForwardT NewStackOB5.stackReverseT
  FrontierEntry1591Native.forward FrontierEntry1591Native.inverse skywalkArithmeticClear firstPhase lastPhase

private theorem compose_records (N F C First : Program)
    (shape : First=N++(F++C)) (s : State) (m : List Bool) (P : State → Prop)
    (step : ∀mn mf mc,P (run C mc (run F mf (run N mn s)))) :
    P (run First m s) := by
  rw [shape,run_append,run_append]
  exact step _ _ _

private theorem compose_roundtrip (N F C R I : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀ mn mf md,run R md (run F mf (run N mn s))=run N mn s)
    (native : ∀ mn mi,run I mi (run N mn s)=s) :
    run (C++(R++I)) mr (run (N++(F++C)) mp s)=s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]
  exact native _ _

theorem phases_roundtrip (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run lastPhase mr (run firstPhase mp s)=s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run NewStackOB5.stackReverseT md (run NewStackOB5.stackForwardT mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s :=
    NewStackOB5.stack_roundtrip hn hlo x hx0 hx _ mf md
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [firstPhase,lastPhase] using compose_roundtrip
    (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT (skywalkArithmeticClear base)
    NewStackOB5.stackReverseT (FrontierEntry1591Native.inverse base) s mp mr clearM twice stack
    (fun mn mi => FrontierEntry1591Native.inverse_roundtrip base hn x y hx s mn mi input)

theorem raw_result (Field : Program) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (value : Nat)
    (input : SkywalkArithmeticInput base x y s.basis)
    (fieldResult : ∀mp mf,
      let before := run firstPhase mp s
      let after := run Field mf before
      after.phase=before.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=before.basis q) :
    let out := run (FrontierEntry1591Native.kernel firstPhase Field lastPhase) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have all := run_three_states firstPhase Field lastPhase
    (fun initial out => initial=s → out.phase=s.phase ∧
      regValue (wireBlock base 2056 256) out.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q) (by
      intro initial before after out mp mf mr h1 h2 h3 eq
      subst initial
      have result := fieldResult mp mf
      dsimp only at result
      rw [h1,h2] at result
      have rt : run lastPhase mr before=s := by
        rw [←h1]
        exact phases_roundtrip hn hlo x y hx0 hx s mp mr input
      exact sandwich_states firstPhase lastPhase first_pool last_pool s before after out mp mr
        value h1 h3 rt result) s m
  simpa only [FrontierEntry1591Native.kernel,List.append_assoc] using all rfl

theorem first_work_free : base 1797∉wires firstPhase := by
  have f : base 1797∉wires NewStackOB5.stackForwardT := by
    rw [NewStackOB5.stackForwardT_support_eq]
    exact FrontierEntry1591Native.stack_work_free.1
  simpa only [firstPhase,wires_append,Finset.mem_union,not_or] using
    And.intro (FrontierEntry1591Native.avoids_work base base_pool_nodup).1
      (And.intro f FrontierEntry1591Native.clear_work_free)

theorem first_work_zero (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    (run firstPhase m s).basis (base 1797)=false :=
  (run_preserves_outside _ m s _ first_work_free).trans
    (FrontierEntry1591Native.caller_clean base hn x y s input).1

theorem first_clean (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    ∀q∈FrontierEntry1591Native.workSites,(run firstPhase m s).basis q=false := by
  refine compose_records (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT
    (skywalkArithmeticClear base) firstPhase (by unfold firstPhase;rfl) s m
    (fun out => ∀q∈FrontierEntry1591Native.workSites,out.basis q=false) ?_
  intro mn mf mc
  have stage := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input
  have bits := NewStackOB5.forward_clear_zero hn x hx0 hx
    (run (FrontierEntry1591Native.forward base) mn s) mf mc stage
  intro q hq
  simp only [FrontierEntry1591Native.workSites,List.mem_toFinset,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact bits.1
  · exact bits.2.1
  · exact bits.2.2

theorem first_parity (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    let out := run firstPhase m s
    out.basis (base 1543)=TraceParity5.parity (payloadControls.map out.basis) := by
  refine compose_records (FrontierEntry1591Native.forward base) NewStackOB5.stackForwardT
    (skywalkArithmeticClear base) firstPhase (by unfold firstPhase;rfl) s m
    (fun out => out.basis (base 1543)=TraceParity5.parity (payloadControls.map out.basis)) ?_
  intro mn mf mc
  exact forward_clear_parity hn hlo x hx0 hx
    (run (FrontierEntry1591Native.forward base) mn s) mf mc
    (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)

end ECDSAAdd.Entrant.FrontierEntry1591Kernel
