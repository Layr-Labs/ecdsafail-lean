import ECDSAAdd.Submission.Entrant.MainPart06
import ECDSAAdd.Submission.Entrant.ExitOnly

set_option Elab.async false

-- ===== Exit-side merged tick (ExitMerge) in the multiplication kernel =====
section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ExitMergeKernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog
attribute [local irreducible] run wires

/-! ### Placement of the merged exit circuit in the unhosted phase coordinates -/

def pi : Equiv.Perm Wire := E1QubitPlacement.rho.trans E1QubitPlacement.nativeSwap

def piN (i : Nat) : Nat :=
  if E1QubitPlacement.rhoN i=1797 then 511 else if E1QubitPlacement.rhoN i=511 then 1797
  else E1QubitPlacement.rhoN i

theorem pi_base (i : Nat) : pi (base i)=base (piN i) := by
  change E1QubitPlacement.nativeSwap (E1QubitPlacement.rho (base i))=_
  rw [E1QubitPlacement.rho_base]
  unfold E1QubitPlacement.nativeSwap
  rw [E1QubitPlacement.swap_base]
  unfold piN
  rfl

/-- The merged exit circuit, placed like the direct first tick. -/
def x1 (k : Nat) : Program := renameProgram pi (ExitMerge.program base (base 2400) k)

/-- The exit last phase with the inverse tick and the controlled negation merged. -/
def lastX (k : Nat) : Program :=
  skywalkArithmeticClear base ++ Rolling1588.stackReverse true ++ x1 k

def negDiv (k x : Nat) (G : Bool) : Nat := if G then (k+p-x)%p else x

theorem forward_placed :
    FrontierEntry1591Native.forward base=renameProgram pi (NativeFirstDirect.forward base) := by
  have e := E1QubitPlacement.rho_fix E1QubitPlacement.nativeSwap
  change renameProgram (fun q => E1QubitPlacement.nativeSwap (E1QubitPlacement.rho q))
    (NativeFirstDirect.forward base)=renameProgram E1QubitPlacement.nativeSwap
      (NativeFirstDirect.forward base) at e
  rw [show renameProgram pi (NativeFirstDirect.forward base)=renameProgram
    (fun q => E1QubitPlacement.nativeSwap (E1QubitPlacement.rho q)) (NativeFirstDirect.forward base) from rfl,e]
  rfl

theorem mem_pool_iff (q : Wire) : q∈skywalkPoolWires base ↔ ∃ i, i < 1798 ∧ q=base i := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hi
    exact ⟨i,by omega,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem piN_lt (i : Nat) (hi : i < 1798) : piN i < 1798 := by
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

theorem pi_pool (q : Wire) (hq : q∈skywalkPoolWires base) : pi q∈skywalkPoolWires base := by
  obtain ⟨i,hi,rfl⟩ := (mem_pool_iff q).mp hq
  rw [pi_base]
  exact (mem_pool_iff _).mpr ⟨_,piN_lt i hi,rfl⟩

theorem pi_out (r : Wire) (h : r∉skywalkPoolWires base) : pi r=r := by
  have ne (i : Nat) (hi : i < 1798) : r≠base i := fun e => h ((mem_pool_iff r).mpr ⟨i,hi,e⟩)
  simp only [pi,Equiv.trans_apply,E1QubitPlacement.rho,E1QubitPlacement.nativeSwap,
    Equiv.swap_apply_of_ne_of_ne (ne 511 (by omega)) (ne 725 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 721 (by omega)) (ne 723 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 722 (by omega)) (ne 724 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 1797 (by omega)) (ne 511 (by omega))]

theorem pi_symm_pool (q : Wire) (hq : q∈skywalkPoolWires base) : pi.symm q∈skywalkPoolWires base := by
  by_contra h
  have e := pi_out (pi.symm q) h
  rw [Equiv.apply_symm_apply] at e
  rw [←e] at h
  exact h hq

theorem piN_kR (i : Nat) (hi : 770 ≤ i ∧ i < 1028) : piN i=i := by
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

theorem pi_kR (q : Wire) (hq : q∈wireBlock base 770 258) : pi q=q := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [pi_base,piN_kR i (by omega)]

theorem pi_symm_kR (q : Wire) (hq : q∈wireBlock base 770 258) : pi.symm q=q := by
  have := pi_kR q hq
  rw [←this,Equiv.symm_apply_apply,this]

theorem pi_fix (i : Nat) (hi : i < 258 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1797) ∨ i=2400) :
    pi (base i)=base i := by
  rw [pi_base]; congr 1
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

/-! ### The merged exit circuit on the image of the placed first tick

Every state comparison below goes through `pull_basis`/`pull_phase` rewrites, so the kernel never
has to evaluate a concrete program to see through `pullState`. -/

theorem pull_basis (f : Wire → Wire) (t : State) (q : Wire) : (pullState f t).basis q=t.basis (f q) := rfl
theorem pull_phase (f : Wire → Wire) (t : State) : (pullState f t).phase=t.phase := rfl
theorem x1_eq (k : Nat) : x1 k=renameProgram pi (ExitMerge.program base (base 2400) k) := rfl

theorem x1_run (k : Nat) (hk : k < p) (x y : Nat) (hx : x < p) (s v : State) (mn r : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis)
    (hphase : v.phase=(run (FrontierEntry1591Native.forward base) mn s).phase)
    (hpool : ∀q∈skywalkPoolWires base,v.basis q=(run (FrontierEntry1591Native.forward base) mn s).basis q) :
    (run (x1 k) r v).phase=s.phase ∧
    regValue (wireBlock base 770 258) (run (x1 k) r v).basis=negDiv k x (v.basis (base 2400)) ∧
    (∀q∈skywalkPoolWires base,q∉wireBlock base 770 258 → (run (x1 k) r v).basis q=s.basis q) ∧
    (∀q,q∉skywalkPoolWires base → (run (x1 k) r v).basis q=v.basis q) := by
  rw [x1_eq]
  have rr := run_rename pi pi.injective (ExitMerge.program base (base 2400) k) r v
  have fr := run_rename pi pi.injective (NativeFirstDirect.forward base) mn s
  rw [←forward_placed] at fr
  have sh : (i : Nat) → (hi : i < 2314) → (hdx : ¬(770 ≤ i ∧ i < 1026)) → (hdy : ¬(2056 ≤ i ∧ i < 2312)) →
      s.basis (base i)=false := by
    intro i hi hdx hdy
    apply input.2.2
    · exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
    · intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
      simp only [List.mem_range'_1] at hj
      have := base_injective e; omega
    · intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
      simp only [List.mem_range'_1] at hj
      have := base_injective e; omega
  have izero (i : Nat) (hi : i < 1798) (hx' : ¬(770 ≤ i ∧ i < 1026)) : (pullState pi s).basis (base i)=false := by
    rw [pull_basis,pi_base]
    have h1 := piN_lt i hi
    apply sh _ (by omega) _ (by omega)
    unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega
  have blk0 (a n : Nat) (h : a+n ≤ 1798) (hd : a+n ≤ 770 ∨ 1026 ≤ a) :
      regValue (wireBlock base a n) (pullState pi s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact izero i (by omega) (by omega)
  have hxr : regValue (wireBlock base 770 256) (pullState pi s).basis=x := by
    rw [regValue_congr _ _ s.basis (fun q hq => by
      rw [pull_basis,pi_kR q (E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) q hq)])]
    exact input.1
  have seed : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 x (pullState pi s).basis := by
    refine ⟨blk0 0 258 (by omega) (by omega),?_,blk0 1540 257 (by omega) (by omega),
      izero 1797 (by omega) (by omega),izero 1028 (by omega) (by omega),izero 1797 (by omega) (by omega)⟩
    change regValue (E1Merge.kR base) (pullState pi s).basis=x
    rw [E1Merge.kR_x base base_pool_nodup,show E1Merge.xR base=wireBlock base 770 256 from rfl,hxr,
      blk0 1026 2 (by omega) (by omega)]
    simp
  have fpool : ∀q∈skywalkPoolWires base,
      (pullState pi v).basis q=(run (NativeFirstDirect.forward base) mn (pullState pi s)).basis q := by
    intro q hq
    rw [←fr,pull_basis,pull_basis]
    exact hpool _ (pi_pool q hq)
  have fphase : (pullState pi v).phase=(run (NativeFirstDirect.forward base) mn (pullState pi s)).phase := by
    rw [←fr,pull_phase,pull_phase]; exact hphase
  have pr := ExitMerge.program_run base (base 2400) base_pool_nodup E1QubitPlacement.g2400 k hk x hx
    (pullState pi s) (pullState pi v) mn r seed (blk0 1029 256 (by omega) (by omega))
    (izero 514 (by omega) (by omega)) (izero 721 (by omega) (by omega)) (izero 722 (by omega) (by omega))
    fphase fpool
  rw [←rr] at pr
  obtain ⟨p1,p2,p3,p4⟩ := pr
  rw [pull_phase,pull_phase] at p1
  rw [pull_basis,pi_fix 2400 (by omega)] at p2
  refine ⟨p1,?_,?_,?_⟩
  · rw [regValue_congr _ _ (pullState pi (run (renameProgram pi (ExitMerge.program base (base 2400) k)) r v)).basis
      (fun q hq => by rw [pull_basis,pi_kR q hq])]
    exact p2
  · intro q hq hk'
    have hs : pi.symm q∉E1Merge.kR base := fun h => hk' (by
      have e := pi_kR _ h; rw [Equiv.apply_symm_apply] at e; rw [e]; exact h)
    have h3 := p3 _ (pi_symm_pool q hq) hs
    rw [pull_basis,pull_basis,Equiv.apply_symm_apply] at h3
    exact h3
  · intro q hq
    have hs : pi.symm q∉skywalkPoolWires base := fun h => hq (by
      have := pi_pool _ h; rwa [Equiv.apply_symm_apply] at this)
    have h4 := p4 _ hs
    rw [pull_basis,pull_basis,Equiv.apply_symm_apply] at h4
    exact h4

/-! ### Kernel with the merged exit: unhosted form -/

private theorem compose_half (N F C R : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀mn mf md,run R md (run F mf (run N mn s))=run N mn s) :
    run (C++R) mr (run (N++(F++C)) mp s)=run N (mp.take (measurementCount N)) s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]

theorem prefix_roundtrip (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (skywalkArithmeticClear base ++ Rolling1588.stackReverse true) mr
        (run (Rolling1588.firstPhase true) mp s)=
      run (FrontierEntry1591Native.forward base)
        (mp.take (measurementCount (FrontierEntry1591Native.forward base))) s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run (Rolling1588.stackReverse true) md (run (Rolling1588.stackForward true) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s :=
    Rolling1588.stack_roundtrip true hn hlo x hx0 hx _ mf md
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [Rolling1588.firstPhase,List.append_assoc] using
    compose_half (FrontierEntry1591Native.forward base) (Rolling1588.stackForward true)
      (skywalkArithmeticClear base) (Rolling1588.stackReverse true) s mp mr clearM twice stack

theorem prefix_pool :
    wires (skywalkArithmeticClear base ++ Rolling1588.stackReverse true)⊆(skywalkPoolWires base).toFinset := by
  have h : wires (Rolling1588Lifetime.lastPhase true)⊆(skywalkPoolWires base).toFinset := by
    rw [Rolling1588Lifetime.last_support_eq true]
    exact FrontierEntry1591Kernel.last_pool
  intro q hq
  apply h
  simp only [Rolling1588Lifetime.lastPhase,Rolling1588.lastPhase,wires_append,Finset.mem_union] at hq ⊢
  tauto

theorem first_pool (isA : Bool) : wires (Rolling1588.firstPhase isA)⊆(skywalkPoolWires base).toFinset := by
  have h := first_support_eq isA
  simp only [Rolling1588Lifetime.firstPhase] at h
  rw [h]; exact FrontierEntry1591Kernel.first_pool

theorem g_not_pool : base 2400∉skywalkPoolWires base := E1QubitPlacement.g2400

theorem num_not_pool (q : Wire) (hq : q∈skywalkPoolWires base) : q∉wireBlock base 2056 256 := by
  obtain ⟨i,hi,rfl⟩ := (mem_pool_iff q).mp hq
  intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj; have := base_injective e; omega

theorem kR_pool (q : Wire) (hq : q∈wireBlock base 770 258) : q∈skywalkPoolWires base := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact (mem_pool_iff _).mpr ⟨i,by omega,rfl⟩

theorem rawX (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      regValue (wireBlock base 770 258) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉wireBlock base 2056 256 → q∉wireBlock base 770 258 → out.basis q=s.basis q := by
  intro out
  obtain ⟨mp,mf,mr,eqOut⟩ : ∃ mp mf mr,
      out=run (lastX k) mr (run F mf (run (Rolling1588.firstPhase false) mp s)) :=
    ⟨_,_,_,by
      show run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s=_
      rw [FrontierEntry1591Native.kernel,run_append,run_append]⟩
  obtain ⟨r1,r2,r3⟩ := fieldResult mp mf
  generalize hAfter : run F mf (run (Rolling1588.firstPhase false) mp s)=after at eqOut r1 r2 r3
  generalize hBefore : run (Rolling1588.firstPhase true) mp s=beforeB at r1 r2 r3
  have eqOut2 : out=run (x1 k)
      (mr.drop (measurementCount (skywalkArithmeticClear base ++ Rolling1588.stackReverse true)))
      (run (skywalkArithmeticClear base ++ Rolling1588.stackReverse true)
        (mr.take (measurementCount (skywalkArithmeticClear base ++ Rolling1588.stackReverse true))) after) := by
    rw [eqOut,show lastX k=(skywalkArithmeticClear base ++ Rolling1588.stackReverse true)++x1 k from rfl,
      run_append]
  have agree := pool_run_agrees (skywalkArithmeticClear base ++ Rolling1588.stackReverse true)
    (skywalkPoolWires base).toFinset prefix_pool
    (mr.take (measurementCount (skywalkArithmeticClear base ++ Rolling1588.stackReverse true))) after beforeB r1
    (fun q hq => r3 q (num_not_pool q (List.mem_toFinset.mp hq)))
  generalize hv : run (skywalkArithmeticClear base ++ Rolling1588.stackReverse true)
    (mr.take (measurementCount (skywalkArithmeticClear base ++ Rolling1588.stackReverse true))) after=v
    at eqOut2 agree
  have vB := prefix_roundtrip hn hlo x y hx0 hx s mp
    (mr.take (measurementCount (skywalkArithmeticClear base ++ Rolling1588.stackReverse true))) input
  rw [hBefore] at vB
  rw [vB] at agree
  have xr := x1_run k hk x y hx s v _
    (mr.drop (measurementCount (skywalkArithmeticClear base ++ Rolling1588.stackReverse true))) input agree.1
    (fun q hq => agree.2 q (List.mem_toFinset.mpr hq))
  rw [←eqOut2] at xr
  obtain ⟨o1,o2,o3,o4⟩ := xr
  have offA (q : Wire) (hq : q∉skywalkPoolWires base) : v.basis q=after.basis q := by
    rw [←hv]
    exact run_preserves_outside _ _ after q (fun h => hq (List.mem_toFinset.mp (prefix_pool h)))
  have offB (q : Wire) (hq : q∉skywalkPoolWires base) : beforeB.basis q=s.basis q := by
    rw [←hBefore]
    exact run_preserves_outside _ _ s q (fun h => hq (List.mem_toFinset.mp (first_pool true h)))
  have g2056 : base 2400∉wireBlock base 2056 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have gv : v.basis (base 2400)=s.basis (base 2400) := by
    rw [offA _ g_not_pool,r3 _ g2056,offB _ g_not_pool]
  have numOut (q : Wire) (hq : q∈wireBlock base 2056 256) : out.basis q=after.basis q := by
    have np : q∉skywalkPoolWires base := fun h => num_not_pool q h hq
    rw [o4 q np,offA q np]
  refine ⟨o1,?_,?_,?_⟩
  · rw [regValue_congr _ _ after.basis numOut]; exact r2
  · rw [o2,gv]
  · intro q h1 h2
    by_cases hp : q∈skywalkPoolWires base
    · exact o3 q hp h2
    · rw [o4 q hp,offA q hp,r3 q h1,offB q hp]

/-! ### Kernel with the merged exit: hosted form -/

private theorem phase_sites_split' : phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem rebind (P F Q : Program) (s : State) (m : List Bool)
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
    rw [phase_sites_split'] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_split'];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_split'] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_split'];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last

theorem x1_hosts_free (k : Nat) (q : Wire) (hq : q∈phaseHosts) : q∉wires (x1 k) := by
  intro h
  rw [x1_eq,renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
  obtain ⟨i,rfl,hi⟩ := E1QubitPlacement.S_cases _ (ExitMerge.program_support base (base 2400) k ha)
  rw [pi_base] at hq
  simp only [phaseHosts,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with e|e|e <;> have := base_injective e <;> unfold piN E1QubitPlacement.rhoN at this <;>
    split_ifs at this <;> omega

theorem lastX_hosts_free (k : Nat) (q : Wire) (hq : q∈phaseHosts) : q∉wires (lastX k) := by
  have old := last_hosts_free true q hq
  simp only [Rolling1588Lifetime.lastPhase,Rolling1588.lastPhase,wires_append,Finset.mem_union,not_or] at old
  simp only [lastX,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨old.1.1,old.1.2⟩,x1_hosts_free k q hq⟩

theorem top_zero (t : BasisState) (h : regValue (wireBlock base 770 258) t < 2^256) :
    ∀q∈wireBlock base 1026 2,t q=false := by
  have sp := E1Merge.kR_x base base_pool_nodup t
  change regValue (wireBlock base 770 258) t=_ at sp
  apply (regValue_zero _ _).mp
  by_contra hne
  have : 1 ≤ regValue (wireBlock base 1026 2) t := Nat.one_le_iff_ne_zero.mpr hne
  have : 2^256 ≤ 2^256*regValue (wireBlock base 1026 2) t := Nat.le_mul_of_pos_right _ this
  omega

theorem negDiv_lt (k x : Nat) (G : Bool) (hx : x < p) : negDiv k x G < p := by
  unfold negDiv; split
  · exact Nat.mod_lt _ (by norm_num [p])
  · exact hx

theorem p_lt : p < 2^256 := by norm_num [p]

theorem sites_not_num (q : Wire) (hq : q∈phaseSites) : q∉wireBlock base 2056 256 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  intro h; obtain ⟨j,hj,e'⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  rcases hq with e|e|e|e|e|e <;> rw [e] at e' <;> have := base_injective e' <;> omega

theorem sites_not_kR (q : Wire) (hq : q∈phaseSites) (h26 : q≠base 1026) : q∉wireBlock base 770 258 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  intro h; obtain ⟨j,hj,e'⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  rcases hq with e|e|e|e|e|e
  · exact h26 e
  all_goals (rw [e] at e'; have := base_injective e'; omega)

theorem hostedX (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (integerBoundary : ∀mn mf,
      run (Rolling1588.stackForward false) mf (run (FrontierEntry1591Native.forward base) mn s)=
        pullState (OB5.sig 511) (run (Rolling1588.allEncode base false 102) []
          (run (W.compactSkywalkForward base 1 511) []
            (run (FrontierEntry1591Native.forward base) mn s))))
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (renameProgram phaseHost (Rolling1588.firstPhase false)++
      (F++renameProgram phaseHost (lastX k))) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      regValue (wireBlock base 770 258) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉wireBlock base 2056 256 → q∉wireBlock base 770 258 → out.basis q=s.basis q := by
  have raw := rawX F k hk hn hlo x y hx0 hx s m value input fieldResult
  have clean := caller_phase_clean x y s input
  obtain ⟨o1,o2,o3,o4⟩ := raw
  have output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s).basis q=false := by
    intro q hq
    have hq' := hq
    simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq'
    by_cases h26 : q=base 1026
    · subst h26
      apply top_zero _ (by rw [o3]; exact (negDiv_lt k x _ hx).trans p_lt)
      exact List.mem_map.mpr ⟨1026,by simp only [List.mem_range'_1]; omega,rfl⟩
    · rw [o4 q (sites_not_num q hq) (sites_not_kR q hq h26)]
      exact clean q hq
  have same := rebind (Rolling1588.firstPhase false) F (lastX k) s m clean (first_hosts_free false)
    (fun records => first_clean_of_boundary false hn x y hx0 hx s records input integerBoundary)
    fieldFree (lastX_hosts_free k) output
  dsimp only
  rw [same]
  exact ⟨o1,o2,o3,o4⟩

/-! ### The TickGap exit kernel with the merged exit -/

def kernelX (k : Nat) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase false)++
    (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k))

def ExitNegCorrect (K : Program) (k : Nat) : Prop := ∀
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false),
    let out := run K m s
    out.phase=s.phase ∧ regValue (skywalkArithmeticNumerator base) out.basis=centerWord (Y*(x:Fp)/2) ∧
      regValue (skywalkArithmeticDivisor base) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉skywalkArithmeticNumerator base → q∉skywalkArithmeticDivisor base → out.basis q=s.basis q

private theorem append_run_eq' (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernelX_correct (k : Nat) (hk : k < p) : ExitNegCorrect (kernelX k) k := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase false))=
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase false)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics false).2.1]
  have eq := append_run_eq' _ _ (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k)) s m records
    (fun r => Rolling1588TickGap.first_hosted_run_eq false hn x Y.val hx0 hx s r input)
  have res := hostedX Rolling1588.exitFieldHosted k hk hn hlo x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input
    (fun mn mf => Rolling1588.stackForward_boundary false hn hlo x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x Y.val hx0 hx s mn input))
    Rolling1588.exitFieldHosted_work_free
    (fun mp mf => Rolling1588.exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  dsimp only at res ⊢
  rw [kernelX,eq]
  obtain ⟨o1,o2,o3,o4⟩ := res
  have tz := top_zero _ (by rw [o3]; exact (negDiv_lt k x _ hx).trans p_lt)
  have sp := E1Merge.kR_x base base_pool_nodup
    (run (renameProgram phaseHost (Rolling1588.firstPhase false)++
      (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k))) m s).basis
  change regValue (wireBlock base 770 258) _=regValue (wireBlock base 770 256) _+_ at sp
  rw [o3,(regValue_zero _ _).mpr tz] at sp
  refine ⟨o1,o2,by simp only [skywalkArithmeticDivisor]; omega,?_⟩
  intro q h1 h2
  by_cases hk' : q∈wireBlock base 770 258
  · have top : q∈wireBlock base 1026 2 := by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk'
      simp only [List.mem_range'_1] at hi
      refine List.mem_map.mpr ⟨i,?_,rfl⟩
      simp only [List.mem_range'_1]
      by_contra hc
      exact h2 (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)
    rw [tz q top]
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp top
    simp only [List.mem_range'_1] at hi
    exact (input.2.2 _ (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩) h2 h1).symm
  · exact o4 q h1 hk'

/-! ### Point-layout transfer -/

theorem wordTransferX (L : ControlledPointLayout) (f : Wire → Wire) (k : Nat)
    (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (gSite : base 2400∈domain)
    (X : Nat) (Y : Fp) (R : Nat)
    (s : State) (m : List Bool)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (P : Program) (programSites : wires P⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      t.basis (base 2409)=false → t.basis (base 2410)=false →
      (run P records t).phase=t.phase ∧
      regValue (skywalkArithmeticNumerator base) (run P records t).basis=R ∧
      regValue (skywalkArithmeticDivisor base) (run P records t).basis=negDiv k X (t.basis (base 2400)) ∧
      ∀ q,q∉skywalkArithmeticNumerator base → q∉skywalkArithmeticDivisor base →
        (run P records t).basis q=t.basis q) :
    (run (renameProgram f P) m s).phase=s.phase ∧
    regValue L.point.y (run (renameProgram f P) m s).basis=R ∧
    regValue L.point.x (run (renameProgram f P) m s).basis=negDiv k X (s.basis L.core.generic) ∧
      ∀q,q∉L.point.y → q∉L.point.x → (run (renameProgram f P) m s).basis q=s.basis q := by
  let t := ECDSAAdd.Entrant.selInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,ECDSAAdd.Entrant.selInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,ECDSAAdd.Entrant.selInput,if_neg used]
  have strong := P_spec t m input (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective P programSites m t s rfl inputBits
  have tg : t.basis (base 2400)=s.basis L.core.generic := by rw [inputBits _ gSite,controlMap]
  refine ⟨transfer.1.trans strong.1,?_,?_,?_⟩
  · rw [←numeratorMap]
    exact (ECDSAAdd.Entrant.selRegMap f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · rw [←divisorMap,←tg]
    exact (ECDSAAdd.Entrant.selRegMap f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dxSites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.2.1
  · intro q outY outX
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      have awayY : a∉skywalkArithmeticNumerator base := by
        intro mem; apply outY; rw [←numeratorMap]; exact List.mem_map.mpr ⟨a,mem,rfl⟩
      have awayX : a∉skywalkArithmeticDivisor base := by
        intro mem; apply outX; rw [←divisorMap]; exact List.mem_map.mpr ⟨a,mem,rfl⟩
      exact (transfer.2 a ha).trans ((strong.2.2.2 a awayY awayX).trans (inputBits a ha))
    · exact run_rename_pool_outside f domain P programSites m s q image

theorem lx_support (k : Nat) : wires (lastX k)⊆wires (Rolling1588.lastPhase true)∪wires (x1 k) := by
  intro q hq
  simp only [lastX,Rolling1588.lastPhase,wires_append,Finset.mem_union] at hq ⊢
  tauto

theorem x1_logical (k : Nat) : wires (x1 k)⊆(E1QubitPlacement.S).image pi := by
  rw [x1_eq,renameProgram_support]
  exact Finset.image_subset_image (ExitMerge.program_support base (base 2400) k)

theorem host_pi (q : Wire) : phaseHost (pi q)=E1QubitPlacement.sig (E1QubitPlacement.rho q) := rfl

theorem hostedX1_logical (k : Nat) :
    wires (renameProgram phaseHost (x1 k))⊆OB5Support.logicalSites := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (x1_logical k ha)
  obtain ⟨i,rfl,hi⟩ := E1QubitPlacement.S_cases b hb
  rw [host_pi,E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range i hi)

theorem kernelX_support (k : Nat) : wires (kernelX k)⊆OB5Support.logicalSites := by
  have old := Rolling1588TickGap.exitKernel_support
  intro q hq
  simp only [kernelX,wires_append,Finset.mem_union,renameProgram_support] at hq
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,wires_append,
    renameProgram_support] at old
  rcases hq with h|h|h
  · exact old (Finset.mem_union_left _ h)
  · exact old (Finset.mem_union_right _ (Finset.mem_union_left _ h))
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rcases Finset.mem_union.mp (lx_support k ha) with h1|h1
    · exact old (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,h1,rfl⟩)))
    · exact hostedX1_logical k (by rw [renameProgram_support]; exact Finset.mem_image.mpr ⟨a,h1,rfl⟩)

def HalfMultiplyNegCorrect (L : ControlledPointLayout) (P : Program) (k : Nat) : Prop :=
  ∀(X Y : Nat),X < p → 0 < X → Y < p → ∀(s : State)(m : List Bool),
    regValue L.point.x s.basis=X → regValue L.point.y s.basis=Y → regValue L.dialogPool s.basis=0 →
    (run P m s).phase=s.phase ∧
    regValue L.point.y (run P m s).basis=centerWord (((Y:Fp)*(X:Fp))/2) ∧
    regValue L.point.x (run P m s).basis=negDiv k X (s.basis L.core.generic) ∧
    ∀q,q∉L.point.y → q∉L.point.x → (run P m s).basis q=s.basis q

theorem exitX_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k < p) :
    HalfMultiplyNegCorrect L (FrontierEntry1591Callers.exit (kernelX k) L) k := by
  intro X Y hX hX0 hY s m hx hy hc
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,
    selectorG,selectorS,zeroFlag⟩
  have dx : (wireBlock base 770 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have dy : (wireBlock base 2056 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have gSite : base 2400∈OB5Support.logicalSites := by
    have := E1QubitPlacement.sw_logical 2400 (by unfold E1QubitPlacement.Rng; omega)
    simpa [E1QubitPlacement.sw] using this
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have result := wordTransferX L (wireFn2 L) k OB5Support.logicalSites
    (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
      (ArithmeticOB5.logical_sub_old hb) eq)
    divisorMap numeratorMap controlMap
    (fun q hq used hx hy => sharedWork q hq (ArithmeticOB5.logical_sub_old used) hx hy)
    selectorG selectorS dx dy gSite X (Y:Fp) (centerWord (((Y:Fp)*(X:Fp))/2))
    s m hx (hy.trans yValue.symm) hc
    (kernelX k) (kernelX_support k)
    (fun t records input hg hs => kernelX_correct k hk
      config.1 above config.2.1 config.2.2 X (Y:Fp) hX0 hX t records input hg hs)
  simpa only [FrontierEntry1591Callers.exit] using result

private theorem sub_val'' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

/-! ### Point step: the multiplication kernel with the merged negation, then `exitY` -/

theorem fusedMultiplyX_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++ExitFusionResearch.exitY L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m v
  let n := measurementCount P
  let a := run P (m.take n) s
  have hp : 0 < X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have half := correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h => finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h => finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have genY : L.core.generic∉L.point.y :=
    fun h => finGeneric_not_xy L hn (List.mem_append_right _ h)
  have genX : L.core.generic∉L.point.x :=
    fun h => finGeneric_not_xy L hn (List.mem_append_left _ h)
  have ag : a.basis L.core.generic=G := (half.2.2.2 _ genY genX).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq => half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av : regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  have out := ExitFusionResearch.exitY_correct L hw hn ((Y*X)/2) k a (m.drop n) av ac
  let b := run (ExitFusionResearch.exitY L k) (m.drop n) a
  have phase : b.phase=s.phase := out.1.trans half.1
  have xy (q : Wire) (hq : q∈L.point.x) : q∉L.point.y := by
    intro h
    have nd := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have p1 := List.count_pos_iff.mpr hq
    have p2 := List.count_pos_iff.mpr h
    simp only [ControlledPointLayout.dialogUsedWires,PointAddLayout.pointWires,List.count_append,
      List.count_cons] at nd
    omega
  have frame (q : Wire) (hy : q∉L.point.y) (hx : q∉L.point.x) : b.basis q=s.basis q :=
    (out.2.2 q hy).trans (half.2.2.2 q hy hx)
  have twice : 2*((Y*X)/2)=Y*X := by
    have two : (2:Fp)≠0 := by decide
    field_simp
  have bv : regValue L.point.y b.basis=(Y*X-(if G then k else 0)).val := by
    rw [out.2.1,ag,twice]
  have bx : regValue L.point.x b.basis=(if G then cx-X else X).val := by
    rw [regValue_congr _ _ a.basis (fun q hq => out.2.2 q (xy q hq)),half.2.2.1,v.generic]
    cases G
    · rfl
    · simp only [negDiv,if_true]; rw [sub_val'']
  rw [run_append]
  change b.phase=s.phase ∧ PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin b.basis
  refine ⟨phase,bx,bv,?_,?_,?_⟩
  · exact (frame _ genY genX).trans v.generic
  · rw [←v.clean]
    exact regValue_congr _ _ _ (fun q hq => frame q (poolY q hq) (poolX q hq))
  · intro q hq
    exact (frame q (fun h => hq (List.mem_append_right _ h)) (fun h => hq (List.mem_append_left _ h))).trans
      (v.rest q hq)

def restXX (L : ControlledPointLayout) (k : Nat) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k)))

theorem exit_splitX (L : ControlledPointLayout) (k : Nat) :
    FrontierEntry1591Callers.exit (kernelX k) L=E1QubitPlacement.tickF L++restXX L k := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,kernelX,Rolling1588TickGap.firstPhase,restXX,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

/-! ### Resources of the merged exit inside the stage -/

theorem x1_counts (k : Nat) : toffoliCount (x1 k)=770 ∧ measurementCount (x1 k)=1027 := by
  rw [x1_eq,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  exact ExitMerge.program_counts base (base 2400) k

theorem x1_slots (k : Nat) : Challenge.gateSlots (x1 k) ≤ 22000 := by
  rw [x1_eq,Baselines.rename_gateSlots]
  exact ExitMerge.program_slots base (base 2400) k

theorem x1_physical (k : Nat) : GatePhysical (x1 k) := by
  rw [x1_eq]
  exact gatePhysical_rename pi pi.injective _
    (ExitMerge.program_physical base (base 2400) base_pool_nodup E1QubitPlacement.g2400 k)

theorem restXX_metrics (L : ControlledPointLayout) (k : Nat) :
    toffoliCount (restXX L k)+256=toffoliCount (ReflectionE1TickGap.restX L)+770 ∧
    measurementCount (restXX L k)+508=measurementCount (ReflectionE1TickGap.restX L)+1027 ∧
    Challenge.gateSlots (restXX L k) ≤ Challenge.gateSlots (ReflectionE1TickGap.restX L)+22000 := by
  have c := x1_counts k
  have sl := x1_slots k
  have i := (FrontierEntry1591Native.counts base).2.2
  simp only [restXX,ReflectionE1TickGap.restX,lastX,Rolling1588.lastPhase,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

theorem restXX_support (L : ControlledPointLayout) (k : Nat) :
    wires (restXX L k)⊆wires (ReflectionE1TickGap.restX L)∪
      wires (renameProgram (wireFn2 L) (renameProgram phaseHost (x1 k))) := by
  intro q hq
  simp only [restXX,ReflectionE1TickGap.restX,lastX,Rolling1588.lastPhase,renameProgram_support,
    wires_append,Finset.image_union,Finset.mem_union] at hq ⊢
  tauto

theorem placedX1_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Nat) :
    wires (renameProgram (wireFn2 L) (renameProgram phaseHost (x1 k)))⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ (hostedX1_logical k)

theorem hostedX1_labels (k : Nat) (q : Wire) (hq : q∈wires (renameProgram phaseHost (x1 k))) :
    ∃ j, q=base (E1QubitPlacement.sw (E1QubitPlacement.rhoN j)) ∧
      (j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j=721 ∨ j=722 ∨ j=2400) := by
  rw [renameProgram_support] at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (x1_logical k ha)
  obtain ⟨j,rfl,hj⟩ := E1QubitPlacement.S_cases b hb
  exact ⟨j,by rw [host_pi,E1QubitPlacement.rho_base,E1QubitPlacement.sig_base],hj⟩

theorem kernelX_physical (k : Nat) : GatePhysical (kernelX k) := by
  have old := Rolling1588TickGap.exitKernel_physical
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,gatePhysical_append] at old
  have last := Rolling1588.lastPhase_physical true
  simp only [Rolling1588.lastPhase,gatePhysical_append] at last
  have lx : GatePhysical (lastX k) := by
    simp only [lastX,gatePhysical_append]; exact ⟨last.1,x1_physical k⟩
  simp only [kernelX,gatePhysical_append]
  exact ⟨old.1,old.2.1,gatePhysical_rename phaseHost phaseHost.injective _ lx⟩

theorem restXX_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Nat) :
    GatePhysical (restXX L k) := by
  have physical := FrontierEntry1591Native.placed_physical L hw hn (kernelX k) (kernelX_support k)
    (kernelX_physical k)
  have e : GatePhysical (FrontierEntry1591Callers.exit (kernelX k) L) := by
    unfold FrontierEntry1591Callers.exit; exact physical
  rw [exit_splitX,gatePhysical_append] at e
  exact e.2

theorem sw760 (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j=721 ∨ j=722 ∨ j=2400) :
    E1QubitPlacement.sw (E1QubitPlacement.rhoN j)≠760 := by
  have range:=E1QubitPlacement.rhoN_range j hj
  generalize E1QubitPlacement.rhoN j=i at range ⊢
  unfold E1QubitPlacement.Rng at range
  unfold E1QubitPlacement.sw
  split_ifs <;> omega

theorem kernelX_760_free (k : Nat) : base 760∉wires (kernelX k) := by
  have old := Rolling1588TickGap.exitKernel_760_free
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,wires_append,
    renameProgram_support,Finset.mem_union,not_or] at old
  simp only [kernelX,wires_append,renameProgram_support,Finset.mem_union,not_or]
  refine ⟨old.1,old.2.1,?_⟩
  intro h
  obtain ⟨a,ha,e⟩ := Finset.mem_image.mp h
  rcases Finset.mem_union.mp (lx_support k ha) with h1|h1
  · exact old.2.2 (Finset.mem_image.mpr ⟨a,h1,e⟩)
  · obtain ⟨j,e',hj⟩ := hostedX1_labels k (phaseHost a) (by
      rw [renameProgram_support]; exact Finset.mem_image.mpr ⟨a,h1,rfl⟩)
    rw [e] at e'
    exact sw760 j hj (base_injective e').symm

end ECDSAAdd.Entrant.ExitMergeKernel

end -- exit merge section

