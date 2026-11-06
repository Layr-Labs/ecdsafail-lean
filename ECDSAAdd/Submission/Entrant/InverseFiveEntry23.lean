import ECDSAAdd.Submission.Entrant.InverseFive23

namespace ECDSAAdd.Entrant.InverseFiveEntry23
open ECDSAAdd Arithmetic MappedCompressed Challenge History5 OB5
open Rolling1588.Integer FrontierEntry1591Callers DirectSkywalk
open InverseFive23
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  InverseFive23.stackReverse15 InverseFive23.lastPhase15 Rolling1588.reverse

private theorem compose_roundtrip15 (N F C R I : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀mn mf md,run R md (run F mf (run N mn s))=run N mn s)
    (native : ∀mn mi,run I mi (run N mn s)=s) :
    run (C++(R++I)) mr (run (N++(F++C)) mp s)=s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]
  exact native _ _

theorem phases_roundtrip15 (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (lastPhase15 isA) mr (run (Rolling1588TickGap.firstPhase isA) mp s)=s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run (stackReverse15 isA) md (run (Rolling1588TickGap.stackForward isA) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s :=
    stack_roundtrip15 isA hn hlo x hx0 hx _ mf md
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [Rolling1588TickGap.firstPhase,Rolling1588TickGap.tailPhase,lastPhase15,List.append_assoc] using
    compose_roundtrip15 (FrontierEntry1591Native.forward base) (Rolling1588TickGap.stackForward isA)
      (skywalkArithmeticClear base) (stackReverse15 isA)
      (FrontierEntry1591NativeH.inverse base) s mp mr clearM twice stack
      (fun mn mi=>FrontierEntry1591NativeH.inverse_roundtrip base hn x y hx s mn mi input)

open ECDSAAdd.Entrant.Rolling1588Lifetime
private theorem phase_sites_split :
    phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem phase_kernel_rebind (P F Q : Program) (s : State) (m : List Bool)
    (input : ∀q∈phaseSites,s.basis q=false)
    (firstFree : ∀q∈phaseHosts,q∉wires P)
    (firstClean : ∀records,∀q∈FrontierEntry1591Native.workSites,
      (run P records s).basis q=false)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (lastFree : ∀q∈phaseHosts,q∉wires Q)
    (output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel P F Q) m s).basis q=false) :
    run (renameProgram phaseHost P++(F++renameProgram phaseHost Q)) m s=
      run (FrontierEntry1591Native.kernel P F Q) m s := by
  let mp := m.take (measurementCount P)
  let rest := m.drop (measurementCount P)
  let mf := rest.take (measurementCount F)
  let mr := rest.drop (measurementCount F)
  let before := run P mp s
  let after := run F mf before
  have finalClean : ∀q∈phaseSites,(run Q mr after).basis q=false := by
    simpa only [FrontierEntry1591Native.kernel,run_append] using output
  have lastInput : ∀q∈phaseSites,after.basis q=false := by
    intro q hq
    rw [phase_sites_split] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_split];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_split] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_split];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last


private theorem phase_numerator_away (q : Wire) (hq : q∈phaseSites) :
    q∉wireBlock base 2056 256 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact OwnPlusHost.not_block _ 2056 256 (by omega)

/-- The field changes A into B. Its output is compared with a B encoding
of the same raw integer history before the B inverse is applied. -/
theorem raw_result_of_roundtrip (a b : Bool) (F : Program) (s : State) (m : List Bool)
    (value : Nat)
    (roundtrip : ∀mp mr,run (lastPhase15 b) mr (run (firstPhase b) mp s)=s)
    (fieldResult : ∀mp mf,
      let beforeA := run (firstPhase a) mp s
      let beforeB := run (firstPhase b) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (FrontierEntry1591Native.kernel (firstPhase a) F (lastPhase15 b)) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have firstPool : wires (firstPhase b)⊆(skywalkPoolWires base).toFinset := by
    rw [first_support_eq]
    exact FrontierEntry1591Kernel.first_pool
  have lastPool : wires (lastPhase15 b)⊆(skywalkPoolWires base).toFinset :=
    last_pool15 b
  have all := run_three_states (firstPhase a) F (lastPhase15 b)
    (fun initial out=>initial=s → out.phase=s.phase ∧
      regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q) (by
      intro initial beforeA after out mp mf mr h1 h2 h3 eq
      subst initial
      have result := fieldResult mp mf
      dsimp only at result
      rw [h1,h2] at result
      exact FrontierEntry1591Kernel.sandwich_states (firstPhase b) (lastPhase15 b) firstPool lastPool s
        (run (firstPhase b) mp s) after out mp mr value rfl h3 (roundtrip mp mr) result) s m
  simpa only [FrontierEntry1591Native.kernel,List.append_assoc] using all rfl



theorem kernel_result15 (a b : Bool) (F : Program) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool) (value : Nat)
    (input : SkywalkArithmeticInput base x y s.basis)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (fieldResult : ∀mp mf,
      let beforeA := run (firstPhase a) mp s
      let beforeB := run (firstPhase b) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (renameProgram phaseHost (firstPhase a)++
      (F++renameProgram phaseHost (lastPhase15 b))) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have rt (mp mr : List Bool) : run (lastPhase15 b) mr (run (firstPhase b) mp s)=s := by
    rw [←Rolling1588TickGap.first_run_eq b hn x y hx0 hx s mp input]
    exact phases_roundtrip15 b hn hlo x y hx0 hx s mp mr input
  have raw := raw_result_of_roundtrip a b F s m value rt fieldResult
  have clean := caller_phase_clean x y s input
  have output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (firstPhase a) F (lastPhase15 b)) m s).basis q=false := by
    intro q hq
    exact (raw.2.2 q (phase_numerator_away q hq)).trans (clean q hq)
  have same := phase_kernel_rebind (firstPhase a) F (lastPhase15 b) s m clean
    (first_hosts_free a) (fun records => Rolling1588Lifetime.first_clean a hn hlo x y hx0 hx s records input)
    fieldFree (last_hosts_free15 b) output
  dsimp only
  rw [same]
  exact raw

open ECDSAAdd.Entrant.Rolling1588 ECDSAAdd.Entrant.FrontierEntry1591Callers ECDSAAdd.Arithmetic.BalancedField
def oldKernel15 (a b : Bool) (F : Program) : Program :=
  renameProgram phaseHost (Rolling1588.firstPhase a) ++
    (F ++ renameProgram phaseHost (lastPhase15 b))
def kernel15 (a b : Bool) (F : Program) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase a) ++
    (F ++ renameProgram phaseHost (lastPhase15 b))
def entryKernel15 : Program := kernel15 true false entryFieldHosted
def exitKernel15 : Program := kernel15 false true exitFieldHosted

theorem old_entry_correct15 : EntryCorrect (oldKernel15 true false entryFieldHosted) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  obtain ⟨out,outEq⟩ : ∃out : State,run (oldKernel15 true false entryFieldHosted) m t=out := ⟨_,rfl⟩
  have actualInput := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  have result := kernel_result15 true false entryFieldHosted hn hlo
    x _ hx0 hx t m (Y/(x:Fp)).val actualInput entryFieldHosted_work_free
    (fun mp mf=>entry_boundary hn hlo ho hf x Y hx0 hx s t mp mf input hg hs phase same half)
  change (run (oldKernel15 true false entryFieldHosted) m t).phase=t.phase ∧
    regValue (wireBlock base 2056 256) (run (oldKernel15 true false entryFieldHosted) m t).basis=(Y/(x:Fp)).val ∧
    ∀q,q∉wireBlock base 2056 256 → (run (oldKernel15 true false entryFieldHosted) m t).basis q=t.basis q at result
  rw [outEq] at result
  have conclusion : out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(Y/(x:Fp)).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q :=
    ⟨result.1.trans phase,result.2.1,fun q hq=>(result.2.2 q hq).trans (same q hq)⟩
  dsimp only
  rw [outEq]
  simpa only [skywalkArithmeticResult,if_true] using conclusion

theorem old_exit_correct15 : ExitCorrect (oldKernel15 false true exitFieldHosted) := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have result := kernel_result15 false true exitFieldHosted hn hlo
    x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input exitFieldHosted_work_free
    (fun mp mf=>exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  simpa only [oldKernel15,skywalkArithmeticNumerator] using result

theorem kernel_first_eq15 (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel15 a b F) m s = run (oldKernel15 a b F) m s := by
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase a)) =
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics a).2.1]
  rw [kernel15,oldKernel15,
    run_append (renameProgram phaseHost (Rolling1588TickGap.firstPhase a)),
    run_append (renameProgram phaseHost (Rolling1588.firstPhase a)),records,
    Rolling1588TickGap.first_hosted_run_eq a hn x y hx0 hx s _ input]

theorem entry_correct15 : EntryCorrect entryKernel15 := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [entryKernel15,kernel_first_eq15 true false entryFieldHosted hn x _ hx0 hx t m actual]
  exact old_entry_correct15 hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half

theorem exit_correct15 : ExitCorrect exitKernel15 := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  rw [exitKernel15,kernel_first_eq15 false true exitFieldHosted hn x _ hx0 hx s m input]
  exact old_exit_correct15 hn hlo ho hf x Y hx0 hx s m input hg hs

theorem kernel_physical15 (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel15 a b F) := by
  simpa only [kernel15,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (Rolling1588TickGap.first_physical a))
      (And.intro field (Rolling1588Lifetime.phase_physical _ (last_physical15 b)))

theorem entry_physical15 : GatePhysical entryKernel15 := by
  simpa only [entryKernel15] using
    kernel_physical15 true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exit_physical15 : GatePhysical exitKernel15 := by
  simpa only [exitKernel15] using
    kernel_physical15 false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

theorem hosted_extra530 (b : Bool) :
    wires (renameProgram phaseHost (lastPhase15 b)) ⊆
      wires (renameProgram phaseHost (Rolling1588.lastPhase b)) ∪ {530} := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (last_extra15 b hv) with old | extra
  · apply Finset.mem_union_left
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨v,old,rfl⟩
  · simp only [Finset.mem_singleton] at extra
    subst v
    apply Finset.mem_union_right
    simp only [Finset.mem_singleton]
    decide +kernel

theorem kernel_extra530 (a b : Bool) (F : Program) :
    wires (kernel15 a b F) ⊆ wires (Rolling1588TickGap.kernel a b F) ∪ {530} := by
  have hsub := hosted_extra530 b
  intro q h
  simp only [kernel15,wires_append,Finset.mem_union] at h
  simp only [Rolling1588TickGap.kernel,wires_append,Finset.mem_union,Finset.mem_singleton]
  rcases h with hfirst | hfield | hlast
  · exact Or.inl (Or.inl hfirst)
  · exact Or.inl (Or.inr (Or.inl hfield))
  · rcases Finset.mem_union.mp (hsub hlast) with hold | hextra
    · exact Or.inl (Or.inr (Or.inr hold))
    · exact Or.inr (Finset.mem_singleton.mp hextra)

theorem extra_logical530 : (530:Wire) ∈ OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨514,?_,by decide +kernel⟩
  simp [OB5Support.logicalIndices]

theorem entry_support530 : wires entryKernel15 ⊆ OB5Support.logicalSites := by
  intro q hq
  have h := kernel_extra530 true false Rolling1588.entryFieldHosted hq
  rcases Finset.mem_union.mp h with old | extra
  · exact Rolling1588TickGap.entryKernel_support old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_logical530

theorem exit_support530 : wires exitKernel15 ⊆ OB5Support.logicalSites := by
  intro q hq
  have h := kernel_extra530 false true Rolling1588.exitFieldHosted hq
  rcases Finset.mem_union.mp h with old | extra
  · exact Rolling1588TickGap.exitKernel_support old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_logical530


end ECDSAAdd.Entrant.InverseFiveEntry23
