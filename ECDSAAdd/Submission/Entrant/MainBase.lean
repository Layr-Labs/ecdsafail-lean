import ECDSAAdd.Submission.Entrant.FrontierMain
import ECDSAAdd.Submission.Entrant.Terminal23Core

-- Adapted public peer module: ParityXExitInverse23Kernel
section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ParityXExitInverse23Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog
attribute [local irreducible] run wires InverseFive23.stackReverse15 InverseFour15.stackReverse15 InverseFive23.lastPhase15

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
def x1 (k : Nat) : Program := renameProgram pi (ParityXExit.programAll base (base 2400) k)

/-- The exit last phase with the inverse tick and the controlled negation merged. -/
def lastX (k : Nat) : Program :=
  skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true ++ x1 k

theorem x1_has530x (k:Nat) : (530:Wire)∈wires (x1 k) := by
  rw [x1,renameProgram_support]
  apply Finset.mem_image.mpr
  refine ⟨base 514,?_,?_⟩
  · have F:base 514∈wires (ExitMerge.fPart base (base 2400) k):=by
      simp only [ExitMerge.fPart,wires_append,Finset.mem_union]
      right
      simp [wires,Instr.wires]
    unfold ParityXExit.programAll
    split_ifs <;> simp only [ParityXExit.programOdd,ParityXExit.programEven,wires_append,Finset.mem_union] <;> tauto
  · rw [pi_base]
    decide +kernel


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
theorem x1_eq (k : Nat) : x1 k=renameProgram pi (ParityXExit.programAll base (base 2400) k) := rfl

theorem x1_run (k : Nat) (hk : k < p) (x y : Nat) (hx : x < p) (s v : State) (mn r : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis)
    (hphase : v.phase=(run (FrontierEntry1591Native.forward base) mn s).phase)
    (hpool : ∀q∈skywalkPoolWires base,v.basis q=(run (FrontierEntry1591Native.forward base) mn s).basis q) :
    (run (x1 k) r v).phase=s.phase ∧
    regValue (wireBlock base 770 258) (run (x1 k) r v).basis=negDiv k x (v.basis (base 2400)) ∧
    (∀q∈skywalkPoolWires base,q∉wireBlock base 770 258 → (run (x1 k) r v).basis q=s.basis q) ∧
    (∀q,q∉skywalkPoolWires base → (run (x1 k) r v).basis q=v.basis q) := by
  rw [x1_eq]
  have rr := run_rename pi pi.injective (ParityXExit.programAll base (base 2400) k) r v
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
  have pr := ParityXExit.programAll_run k hk x hx
    (pullState pi s) (pullState pi v) mn r seed (blk0 1029 256 (by omega) (by omega))
    (izero 514 (by omega) (by omega)) (izero 721 (by omega) (by omega)) (izero 722 (by omega) (by omega))
    fphase fpool
  rw [←rr] at pr
  obtain ⟨p1,p2,p3,p4⟩ := pr
  rw [pull_phase,pull_phase] at p1
  rw [pull_basis,pi_fix 2400 (by omega)] at p2
  refine ⟨p1,?_,?_,?_⟩
  · rw [regValue_congr _ _ (pullState pi (run (renameProgram pi (ParityXExit.programAll base (base 2400) k)) r v)).basis
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
    run (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true) mr
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
      run (InverseFive23.stackReverse15 true) md (run (Rolling1588.stackForward true) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s := by
    have first := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input
    rw [← Rolling1588TickGap.stackForward_run_eq true x hx0 hx _ mf first]
    exact InverseFive23.stack_roundtrip15 true hn hlo x hx0 hx _ mf md first
  simpa only [Rolling1588.firstPhase,List.append_assoc] using
    compose_half (FrontierEntry1591Native.forward base) (Rolling1588.stackForward true)
      (skywalkArithmeticClear base) (InverseFive23.stackReverse15 true) s mp mr clearM twice stack

theorem prefix_pool :
    wires (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)⊆(skywalkPoolWires base).toFinset := by
  intro q hq
  apply InverseFive23.last_pool15 true
  simp only [InverseFive23.lastPhase15,wires_append,Finset.mem_union] at hq ⊢
  exact Or.inl hq

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
      (mr.drop (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)))
      (run (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)
        (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) after) := by
    rw [eqOut,show lastX k=(skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)++x1 k from rfl,
      run_append]
  have agree := pool_run_agrees (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)
    (skywalkPoolWires base).toFinset prefix_pool
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) after beforeB r1
    (fun q hq => r3 q (num_not_pool q (List.mem_toFinset.mp hq)))
  generalize hv : run (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) after=v
    at eqOut2 agree
  have vB := prefix_roundtrip hn hlo x y hx0 hx s mp
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) input
  rw [hBefore] at vB
  rw [vB] at agree
  have xr := x1_run k hk x y hx s v _
    (mr.drop (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) input agree.1
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
  obtain ⟨i,rfl,hi⟩ := E1QubitPlacement.S_cases _ (ExitMerge.program_support base (base 2400) k (ParityXExit.programAll_wires base (base 2400) k ha))
  rw [pi_base] at hq
  simp only [phaseHosts,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with e|e|e <;> have := base_injective e <;> unfold piN E1QubitPlacement.rhoN at this <;>
    split_ifs at this <;> omega

theorem lastX_hosts_free (k : Nat) (q : Wire) (hq : q∈phaseHosts) : q∉wires (lastX k) := by
  have old := InverseFive23.last_hosts_free15 true q hq
  simp only [InverseFive23.lastPhase15,wires_append,Finset.mem_union,not_or] at old
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

set_option linter.unusedVariables false in
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

theorem lx_support (k : Nat) : wires (lastX k) ⊆ wires (Rolling1588.lastPhase true) ∪ wires (x1 k) := by
  intro q hq
  simp only [lastX,wires_append,Finset.mem_union] at hq
  rcases hq with (hc | hs) | hx
  · have h : q ∈ wires (InverseFive23.lastPhase15 true) := by
      simp only [InverseFive23.lastPhase15,wires_append,Finset.mem_union]
      exact Or.inl (Or.inl hc)
    rcases Finset.mem_union.mp (InverseFive23.last_extra15 true h) with old | extra
    · exact Finset.mem_union_left _ old
    · simp only [Finset.mem_singleton] at extra
      subst q
      exact Finset.mem_union_right _ (x1_has530x k)
  · have h : q ∈ wires (InverseFive23.lastPhase15 true) := by
      simp only [InverseFive23.lastPhase15,wires_append,Finset.mem_union]
      exact Or.inl (Or.inr hs)
    rcases Finset.mem_union.mp (InverseFive23.last_extra15 true h) with old | extra
    · exact Finset.mem_union_left _ old
    · simp only [Finset.mem_singleton] at extra
      subst q
      exact Finset.mem_union_right _ (x1_has530x k)
  · exact Finset.mem_union_right _ hx

theorem x1_logical (k : Nat) : wires (x1 k)⊆(E1QubitPlacement.S).image pi := by
  rw [x1_eq,renameProgram_support]
  exact Finset.image_subset_image ((ParityXExit.programAll_wires base (base 2400) k).trans
    (ExitMerge.program_support base (base 2400) k))

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

theorem x1_counts (k : Nat) : toffoliCount (x1 k)=766 ∧ measurementCount (x1 k)=1027 := by
  rw [x1_eq,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  have h:=ParityXExit.programAll_counts base (base 2400) k
  have old:=ExitMerge.program_counts base (base 2400) k
  omega

theorem x1_slots (k : Nat) : Challenge.gateSlots (x1 k) ≤ 22000 := by
  rw [x1_eq,Baselines.rename_gateSlots]
  exact (ParityXExit.programAll_counts base (base 2400) k).2.2.trans
    (ExitMerge.program_slots base (base 2400) k)

theorem x1_physical (k : Nat) : GatePhysical (x1 k) := by
  rw [x1_eq]
  exact gatePhysical_rename pi pi.injective _
    (ParityXExit.programAll_physical k)

theorem restXX_metrics (L : ControlledPointLayout) (k : Nat) :
    toffoliCount (restXX L k)+255=toffoliCount (ReflectionE1TickGap.restX L)+767 ∧
    measurementCount (restXX L k)+508=measurementCount (ReflectionE1TickGap.restX L)+1027 ∧
    Challenge.gateSlots (restXX L k) ≤ Challenge.gateSlots (ReflectionE1TickGap.restX L)+23235 := by
  have c := x1_counts k
  have rev := InverseFive23.reverse_metrics_new true
  have sl := x1_slots k
  have i := FrontierEntry1591NativeH.counts base
  simp only [restXX,ReflectionE1TickGap.restX,lastX,Rolling1588.lastPhase,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

theorem restXX_support (L : ControlledPointLayout) (k : Nat) :
    wires (restXX L k)⊆wires (ReflectionE1TickGap.restX L)∪
      wires (renameProgram (wireFn2 L) (renameProgram phaseHost (x1 k))) := by
  have sub := Finset.image_subset_image (f := wireFn2 L) (Finset.image_subset_image (f := phaseHost) (lx_support k))
  simp only [Finset.image_union] at sub
  intro q hq
  simp only [restXX,ReflectionE1TickGap.restX,renameProgram_support,
    wires_append,Finset.image_union,Finset.mem_union] at hq ⊢
  have imp : q ∈ ((wires (lastX k)).image phaseHost |>.image (wireFn2 L)) →
      q ∈ ((wires (Rolling1588.lastPhase true)).image phaseHost |>.image (wireFn2 L)) ∨
        q ∈ ((wires (x1 k)).image phaseHost |>.image (wireFn2 L)) := by
    intro h
    exact Finset.mem_union.mp (sub h)
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
  have last := InverseFive23.last_physical15 true
  simp only [InverseFive23.lastPhase15,gatePhysical_append] at last
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


theorem restXX_delta (L:ControlledPointLayout) (k:Nat) :
    toffoliCount (restXX L k)+2=toffoliCount (ExitMergeKernel.restXX L k) ∧
    measurementCount (restXX L k)=measurementCount (ExitMergeKernel.restXX L k) ∧
    Challenge.gateSlots (restXX L k)≤Challenge.gateSlots (ExitMergeKernel.restXX L k)+151 := by
  have h:=ParityXExit.programAll_counts base (base 2400) k
  have inverse:=InverseFive23.stack_delta true
  simp only [restXX,ExitMergeKernel.restXX,lastX,ExitMergeKernel.lastX,x1,ExitMergeKernel.x1,
    toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

theorem restXX_subset (L:ControlledPointLayout) (k:Nat) :
    wires (restXX L k)⊆wires (ExitMergeKernel.restXX L k) := by
  have x1sub:wires (x1 k)⊆wires (ExitMergeKernel.x1 k):=by
    simp only [x1,ExitMergeKernel.x1,renameProgram_support]
    exact Finset.image_subset_image (ParityXExit.programAll_wires base (base 2400) k)
  have last:wires (lastX k)⊆wires (ExitMergeKernel.lastX k):=by
    have stack:=InverseFive23.stack_subset true
    simp only [lastX,ExitMergeKernel.lastX,wires_append]
    gcongr
  have host:wires (renameProgram phaseHost (lastX k))⊆
      wires (renameProgram phaseHost (ExitMergeKernel.lastX k)):=by
    simp only [renameProgram_support]
    exact Finset.image_subset_image last
  have inner:=Finset.union_subset_union
    (Finset.Subset.refl (wires (renameProgram phaseHost (Rolling1588TickGap.tailPhase false))))
    (Finset.union_subset_union (Finset.Subset.refl (wires Rolling1588.exitFieldHosted)) host)
  simpa only [restXX,ExitMergeKernel.restXX,renameProgram_support,wires_append] using
    Finset.image_subset_image (f:=wireFn2 L) inner

end ECDSAAdd.Entrant.ParityXExitInverse23Kernel

end

-- Adapted public peer module: ParityStageXInverse23
section

namespace ECDSAAdd.Entrant.ParityStageXInverse23
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap OB5 Rolling1588Lifetime ParityCarry ParityConvert ParityUniform ParityXEntry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  InverseFour15.lastPhase15 InverseFour15.stackReverse15 InverseFour15.reverseTail15 Rolling1588TickGap.tailPhase
def restEntry (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true) ++
      (Rolling1588.entryFieldHosted ++ renameProgram phaseHost (InverseFour15.lastPhase15 false)))

def entryRef (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky ++ E1QubitPlacement.entryM L kx ++ restEntry L

theorem entry_split_ref (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry InverseFour15.entryKernel15 L = E1QubitPlacement.tickF L ++ restEntry L := by
  have tick := E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base)) = E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,InverseFour15.entryKernel15,InverseFour15.kernel15,
    Rolling1588TickGap.firstPhase,restEntry,renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem entryRef_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryRef L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX L hw hn X Y G origin kx
  have divide := division_step InverseFour15.entryKernel15 InverseFour15.entry_support530
    InverseFour15.entry_correct15 L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior := add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky ++ E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx ++ fusedY L ky ++ E1QubitPlacement.tickF L)
    (R:=restEntry L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryRef,division,entry_split_ref,List.append_assoc] using prior


def entryStageAll (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  entryYAll L ky++entryXAll L kx++restEntry L

theorem entryStageAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (s : State) (m : List Bool) (hX:regValue L.point.x s.basis=X.val)
    (hY:regValue L.point.y s.basis=Y.val) (hc : regValue L.dialogPool s.basis=0) :
    run (entryStageAll L kx ky) m s=run (entryRef L kx ky) m s := by
  have cm:measurementCount (entryYAll L ky)=measurementCount (fusedY L ky) :=
    (entryYAll_counts L hw ky).2.1.trans (fusedY_counts L hw ky).2.symm
  have first:=prefix_eq (entryYAll L ky) (fusedY L ky) (entryXAll L kx++restEntry L) s m cm
      (entryYAll_eq L hw hn Y ky s m hY hc)
  have fy:=fusedY_correct L hw hn Y ky s (m.take (measurementCount (fusedY L ky))) hY hc
  let t:=run (fusedY L ky) (m.take (measurementCount (fusedY L ky))) s
  have tx:regValue L.point.x t.basis=X.val:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)),hX]
  have tc:regValue L.dialogPool t.basis=0:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)),hc]
  have second:=prefix_eq (entryXAll L kx) (E1QubitPlacement.entryM L kx) (restEntry L)
    t (m.drop (measurementCount (fusedY L ky))) (entryXAll_counts L kx).2.1
    (entryXAll_eq L hw hn X kx t _ tx tc)
  change run ((entryYAll L ky++entryXAll L kx)++restEntry L) m s=_
  rw [List.append_assoc,first]
  simpa only [entryRef,List.append_assoc,run_append,t] using second

theorem entryStageAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState) (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStageAll L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  intro s m hs
  rw [entryStageAll_eq L hw hn X Y kx ky s m hs.x hs.y hs.clean]
  exact entryRef_step L hw hn X Y kx ky G origin hx s m hs

theorem multiplyExitAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ParityXExitInverse23Kernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (P++exitYAll L k) m s=run (P++ExitFusionResearch.exitY L k) m s := by
  let n:=measurementCount P
  let a:=run P (m.take n) s
  have hp:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have half:=correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have ac:regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq=>half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av:regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  rw [run_append,run_append]
  exact exitYAll_eq L hw hn ((Y*X)/2) k a (m.drop n) (m.drop n) av ac

theorem multiplyExitAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ParityXExitInverse23Kernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++exitYAll L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m hs
  rw [multiplyExitAll_eq L hw hn P cx correct X Y k G origin hX s m hs]
  exact ParityXExitInverse23Kernel.fusedMultiplyX_step L hw hn P cx correct X Y k G origin hX s m hs

def secondStageAll (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  ReflectionE1TickGapLow48.squareEntry L k++ParityXExitInverse23Kernel.restXX L cx.val++exitYAll L cy

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
open ReflectionE1TickGapLow48
theorem secondStageAll_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageAll L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=multiplyExitAll_step L hw hn
    (FrontierEntry1591Callers.exit (ParityXExitInverse23Kernel.kernelX cx.val) L) cx
    (ParityXExitInverse23Kernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageAll,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ParityXExitInverse23Kernel.restXX L cx.val++exitYAll L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ParityXExitInverse23Kernel.exit_splitX,List.append_assoc,Z] using prior

end

def genericAll (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStageAll L (-cx) (-cy)++secondStageAll L (ReflectionE1.correction cx) cy cx

def genericRef (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryRef L (-cx) (-cy)++ReflectionE1TickGapLow48.secondStageX L (ReflectionE1.correction cx) cy cx

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (genericAll L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageAll_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (genericAll L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageAll_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second



end


theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+5=toffoliCount (genericRef L cx cy) ∧
    measurementCount (genericAll L cx cy)=measurementCount (genericRef L cx cy) ∧
    gateSlots (genericAll L cx cy)≤gateSlots (genericRef L cx cy)+151 := by
  have r:=ParityXExitInverse23Kernel.restXX_delta L cx.val
  have x:=entryXAll_counts L (-cx)
  have a:=entryYAll_counts L hw (-cy)
  have aa:=fusedY_counts L hw (-cy)
  have b:=exitYAll_counts L hw cy
  have bb:=ExitFusionResearch.exitY_counts L hw cy
  simp only [genericAll,genericRef,entryStageAll,entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem generic_toffoli (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+5=toffoliCount (genericRef L cx cy) := by
  have h:=generic_counts L hw cx cy
  omega

theorem generic_wires (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (genericAll L cx cy)⊆wires (genericRef L cx cy) := by
  have r:=ParityXExitInverse23Kernel.restXX_subset L cx.val
  have a:=entryYAll_wires L hw (-cy)
  have b:=exitYAll_wires L hw cy
  simp only [genericAll,genericRef,entryStageAll,entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union a (entryXAll_wires L (-cx))) (Finset.Subset.refl _))
    (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) r) b)

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp)
    (h : GatePhysical (genericRef L cx cy)) : GatePhysical (genericAll L cx cy) := by
  simp only [genericRef,entryRef,ReflectionE1TickGapLow48.secondStageX,gatePhysical_append] at h
  simp only [genericAll,entryStageAll,secondStageAll,gatePhysical_append]
  exact ⟨⟨⟨entryYAll_physical L hw hn (-cy),entryXAll_physical L hw hn (-cx)⟩,h.1.2⟩,
    ⟨⟨h.2.1.1,ParityXExitInverse23Kernel.restXX_physical L hw hn cx.val⟩,exitYAll_physical L hw hn cy⟩⟩

end ECDSAAdd.Entrant.ParityStageXInverse23

end

-- Adapted public peer module: ParityStageBothInverse23
section

namespace ECDSAAdd.Entrant.ParityStageBothInverse23
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap OB5 Rolling1588Lifetime ParityCarry ParityConvert ParityUniform ParityXEntry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  InverseFive23.lastPhase15 InverseFive23.stackReverse15 InverseFive23.reverseTail15 Rolling1588TickGap.tailPhase
attribute [local irreducible] InverseFour15.lastPhase15 InverseFour15.stackReverse15
  InverseFour15.reverseTail15 Rolling1588.entryFieldHosted

def restEntry (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true) ++
      (Rolling1588.entryFieldHosted ++ renameProgram phaseHost (InverseFive23.lastPhase15 false)))

def entryRef (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky ++ E1QubitPlacement.entryM L kx ++ restEntry L

theorem entry_split_ref (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry InverseFiveEntry23.entryKernel15 L = E1QubitPlacement.tickF L ++ restEntry L := by
  have tick := E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base)) = E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,InverseFiveEntry23.entryKernel15,InverseFiveEntry23.kernel15,
    Rolling1588TickGap.firstPhase,restEntry,renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem entryRef_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryRef L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX L hw hn X Y G origin kx
  have divide := division_step InverseFiveEntry23.entryKernel15 InverseFiveEntry23.entry_support530
    InverseFiveEntry23.entry_correct15 L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior := add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky ++ E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx ++ fusedY L ky ++ E1QubitPlacement.tickF L)
    (R:=restEntry L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryRef,division,entry_split_ref,List.append_assoc] using prior


def entryStageAll (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  entryYAll L ky++entryXAll L kx++restEntry L

theorem entryStageAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (s : State) (m : List Bool) (hX:regValue L.point.x s.basis=X.val)
    (hY:regValue L.point.y s.basis=Y.val) (hc : regValue L.dialogPool s.basis=0) :
    run (entryStageAll L kx ky) m s=run (entryRef L kx ky) m s := by
  have cm:measurementCount (entryYAll L ky)=measurementCount (fusedY L ky) :=
    (entryYAll_counts L hw ky).2.1.trans (fusedY_counts L hw ky).2.symm
  have first:=prefix_eq (entryYAll L ky) (fusedY L ky) (entryXAll L kx++restEntry L) s m cm
      (entryYAll_eq L hw hn Y ky s m hY hc)
  have fy:=fusedY_correct L hw hn Y ky s (m.take (measurementCount (fusedY L ky))) hY hc
  let t:=run (fusedY L ky) (m.take (measurementCount (fusedY L ky))) s
  have tx:regValue L.point.x t.basis=X.val:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)),hX]
  have tc:regValue L.dialogPool t.basis=0:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)),hc]
  have second:=prefix_eq (entryXAll L kx) (E1QubitPlacement.entryM L kx) (restEntry L)
    t (m.drop (measurementCount (fusedY L ky))) (entryXAll_counts L kx).2.1
    (entryXAll_eq L hw hn X kx t _ tx tc)
  change run ((entryYAll L ky++entryXAll L kx)++restEntry L) m s=_
  rw [List.append_assoc,first]
  simpa only [entryRef,List.append_assoc,run_append,t] using second

theorem entryStageAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState) (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStageAll L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  intro s m hs
  rw [entryStageAll_eq L hw hn X Y kx ky s m hs.x hs.y hs.clean]
  exact entryRef_step L hw hn X Y kx ky G origin hx s m hs

theorem multiplyExitAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ParityXExitInverse23Kernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (P++exitYAll L k) m s=run (P++ExitFusionResearch.exitY L k) m s := by
  let n:=measurementCount P
  let a:=run P (m.take n) s
  have hp:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have half:=correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have ac:regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq=>half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av:regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  rw [run_append,run_append]
  exact exitYAll_eq L hw hn ((Y*X)/2) k a (m.drop n) (m.drop n) av ac

theorem multiplyExitAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ParityXExitInverse23Kernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++exitYAll L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m hs
  rw [multiplyExitAll_eq L hw hn P cx correct X Y k G origin hX s m hs]
  exact ParityXExitInverse23Kernel.fusedMultiplyX_step L hw hn P cx correct X Y k G origin hX s m hs

def secondStageAll (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  ReflectionE1TickGapLow48.squareEntry L k++ParityXExitInverse23Kernel.restXX L cx.val++exitYAll L cy

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
open ReflectionE1TickGapLow48
theorem secondStageAll_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageAll L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=multiplyExitAll_step L hw hn
    (FrontierEntry1591Callers.exit (ParityXExitInverse23Kernel.kernelX cx.val) L) cx
    (ParityXExitInverse23Kernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageAll,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ParityXExitInverse23Kernel.restXX L cx.val++exitYAll L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ParityXExitInverse23Kernel.exit_splitX,List.append_assoc,Z] using prior

end

def genericAll (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStageAll L (-cx) (-cy)++secondStageAll L (ReflectionE1.correction cx) cy cx

def genericRef (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ParityStageXInverse23.entryRef L (-cx) (-cy)++ReflectionE1TickGapLow48.secondStageX L (ReflectionE1.correction cx) cy cx

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (genericAll L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageAll_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (genericAll L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageAll_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second



end


theorem last_delta (b : Bool) :
    toffoliCount (InverseFive23.lastPhase15 b)+1=toffoliCount (InverseFour15.lastPhase15 b) ∧
    measurementCount (InverseFive23.lastPhase15 b)=measurementCount (InverseFour15.lastPhase15 b) ∧
    gateSlots (InverseFive23.lastPhase15 b)=gateSlots (InverseFour15.lastPhase15 b)+151 := by
  have h:=InverseFive23.stack_delta b
  simp only [InverseFive23.lastPhase15,InverseFour15.lastPhase15,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  omega

theorem rest_delta (L : ControlledPointLayout) :
    toffoliCount (restEntry L)+1=toffoliCount (ParityStageXInverse23.restEntry L) ∧
    measurementCount (restEntry L)=measurementCount (ParityStageXInverse23.restEntry L) ∧
    gateSlots (restEntry L)=gateSlots (ParityStageXInverse23.restEntry L)+151 := by
  have h:=last_delta false
  simp only [restEntry,ParityStageXInverse23.restEntry,toffoliCount_append,
    measurementCount_append,gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,rename_gateSlots]
  omega

theorem nested_support (f g : Wire→Wire) (P Q R S : Program) (h : wires R⊆wires S) :
    wires (renameProgram f (P++(Q++renameProgram g R)))⊆
      wires (renameProgram f (P++(Q++renameProgram g S))) := by
  simp only [renameProgram_support,wires_append]
  exact Finset.image_mono f (Finset.union_subset_union (Finset.Subset.refl _) 
    (Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono g h)))

theorem rest_subset (L : ControlledPointLayout) :
    wires (restEntry L)⊆wires (ParityStageXInverse23.restEntry L) :=
  nested_support (wireFn2 L) phaseHost
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true)) Rolling1588.entryFieldHosted
    (InverseFive23.lastPhase15 false) (InverseFour15.lastPhase15 false) (InverseFive23.last_subset false)

theorem rest_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restEntry L) := by
  have p := placed_physical InverseFiveEntry23.entryKernel15 InverseFiveEntry23.entry_support530
    InverseFiveEntry23.entry_physical15 L hw hn
  have entryP : GatePhysical (FrontierEntry1591Callers.entry InverseFiveEntry23.entryKernel15 L) := by
    simpa only [FrontierEntry1591Callers.entry] using p
  rw [entry_split_ref,gatePhysical_append] at entryP
  exact entryP.2

theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+6=toffoliCount (genericRef L cx cy) ∧
    measurementCount (genericAll L cx cy)=measurementCount (genericRef L cx cy) ∧
    gateSlots (genericAll L cx cy)≤gateSlots (genericRef L cx cy)+302 := by
  have e:=rest_delta L
  have r:=ParityXExitInverse23Kernel.restXX_delta L cx.val
  have x:=entryXAll_counts L (-cx)
  have a:=entryYAll_counts L hw (-cy)
  have aa:=fusedY_counts L hw (-cy)
  have b:=exitYAll_counts L hw cy
  have bb:=ExitFusionResearch.exitY_counts L hw cy
  simp only [genericAll,genericRef,entryStageAll,ParityStageXInverse23.entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem generic_toffoli (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+6=toffoliCount (genericRef L cx cy) := by
  have h:=generic_counts L hw cx cy
  omega

theorem generic_wires (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (genericAll L cx cy)⊆wires (genericRef L cx cy) := by
  have r:=ParityXExitInverse23Kernel.restXX_subset L cx.val
  have a:=entryYAll_wires L hw (-cy)
  have b:=exitYAll_wires L hw cy
  simp only [genericAll,genericRef,entryStageAll,ParityStageXInverse23.entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union a (entryXAll_wires L (-cx))) (rest_subset L))
    (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) r) b)

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp)
    (h : GatePhysical (genericRef L cx cy)) : GatePhysical (genericAll L cx cy) := by
  simp only [genericRef,ParityStageXInverse23.entryRef,ReflectionE1TickGapLow48.secondStageX,gatePhysical_append] at h
  simp only [genericAll,entryStageAll,secondStageAll,gatePhysical_append]
  exact ⟨⟨⟨entryYAll_physical L hw hn (-cy),entryXAll_physical L hw hn (-cx)⟩,rest_physical L hw hn⟩,
    ⟨⟨h.2.1.1,ParityXExitInverse23Kernel.restXX_physical L hw hn cx.val⟩,exitYAll_physical L hw hn cy⟩⟩

end ECDSAAdd.Entrant.ParityStageBothInverse23

end

-- Adapted public peer module: ParityFinalBothInverse23XY
section

namespace ECDSAAdd.Entrant.ParityFinalBothInverse23XY
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  ParityStageBothInverse23.genericAll Entry530.generic530

theorem reference_eq (L : ControlledPointLayout) (cx cy : Fp) :
    ParityStageBothInverse23.genericRef L cx cy=Entry530.generic530 L cx cy := by
  simp only [ParityStageBothInverse23.genericRef,Entry530.generic530,
    ParityStageXInverse23.entryRef,Entry530.entryStage530,
    ParityStageXInverse23.restEntry,Entry530.restE530]

theorem gen_block_run (P : Program) (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      P (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          P))))) m t).basis q = t.basis q := by
  have hw := layout_widths
  have hn := layout_nodup
  have tinv := tauM_invol layout hn
  have einv := swapE_invol layout hw hn
  have dinv := swapD_invol layout hw hn
  have uinv : ∀ q, Wrapper5.U layout (Wrapper5.U layout q) = q := fun q => Equiv.swap_apply_self _ _ _
  have gflag : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have sflag : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have eflag : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have dflag : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have tauM_def : ∀ q, tauM layout q =
      if q = layout.core.generic then layout.genericSelect else
        if q = layout.genericSelect then layout.core.generic else q := fun q => rfl
  -- tauM fixes everything off the two generic flags
  have tfix : ∀ q, q ≠ layout.core.generic → q ≠ layout.genericSelect → tauM layout q = q := by
    intro q h1 h2; rw [tauM_def q, if_neg h1, if_neg h2]
  have pclean : ∀ q ∈ layout.dialogPool, t.basis q = false :=
    fun q hq => (regValue_zero _ _).mp hclean q hq
  have pne (q : Wire) (hq : q ∈ layout.dialogPool) : q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => pool_not_flag q hq (e ▸ gflag), fun e => pool_not_flag q hq (e ▸ sflag)⟩
  have xyne (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => flags_not_point _ gflag (e ▸ hq), fun e => flags_not_point _ sflag (e ▸ hq)⟩
  have fne : layout.point.finite ≠ layout.core.generic ∧ layout.point.finite ≠ layout.genericSelect :=
    ⟨fun e => finite_not_flag.1 (e ▸ gflag), fun e => finite_not_flag.1 (e ▸ sflag)⟩
  -- the generic block in its own frame
  generalize ht' : pullState (tauM layout) t = t'
  have t'def : ∀ q, t'.basis q = t.basis (tauM layout q) := by intro q; rw [← ht']; rfl
  have t'x : ∀ q ∈ layout.point.x ++ layout.point.y, t'.basis q = t.basis q := by
    intro q hq; rw [t'def, tfix q (xyne q hq).1 (xyne q hq).2]
  have v : PointDialogValues layout X Y G t'.basis t'.basis := by
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [← hx]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_left _ hq)
    · rw [← hy]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_right _ hq)
    · rw [t'def, tauM_def, if_pos rfl]; exact hg
    · apply (regValue_zero _ _).mpr
      intro q hq
      rw [t'def, tfix q (pne q hq).1 (pne q hq).2]; exact pclean q hq
  have hb : t'.basis layout.point.finite = false := by
    rw [t'def, tfix _ fne.1 fne.2]; exact hf
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn P
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) P) m t' = R0
    at ph0 v0
  have R0clean : ∀ q ∈ layout.dialogPool, R0.basis q = false :=
    fun q hq => (regValue_zero _ _).mp v0.clean q hq
  -- U swaps two clean pool sites
  have u684 := Square5Placement.pool_member layout hw 684 (by omega)
  have u717 := Square5Placement.pool_member layout hw 717 (by omega)
  have U_def : ∀ q, Wrapper5.U layout q = if q = layout.core.poolWire 684 then layout.core.poolWire 717
      else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
    intro q
    show (Equiv.swap _ _) q = _
    rw [Equiv.swap_apply_def]
  have R1 : run (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P)) m t' = R0 := by
    rw [run_rename_noop _ uinv]
    · exact hR0
    · apply swap_sym _ _ _ U_def
      have a : t'.basis (layout.core.poolWire 684) = false := by
        rw [t'def, tfix _ (pne _ u684).1 (pne _ u684).2]; exact pclean _ u684
      have b : t'.basis (layout.core.poolWire 717) = false := by
        rw [t'def, tfix _ (pne _ u717).1 (pne _ u717).2]; exact pclean _ u717
      rw [a, b]
    · rw [hR0]
      apply swap_sym _ _ _ U_def
      rw [R0clean _ u684, R0clean _ u717]
  -- tauM is the real swap between the generic flag and the generic select
  have R2 : run (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_invol _ tinv, ht', R1]
  -- R0 off the point registers equals the pulled start
  have R0rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → R0.basis q = t'.basis q := v0.rest
  have tq_off : ∀ q, q ∉ layout.point.x ++ layout.point.y → tauM layout q ∉ layout.point.x ++ layout.point.y := by
    intro q hq
    rw [tauM_def]
    split_ifs
    · exact flags_not_point _ sflag
    · exact flags_not_point _ gflag
    · exact hq
  have R2rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → (pullState (tauM layout) R0).basis q = t.basis q := by
    intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, R0rest _ (tq_off q hq), t'def, tinv]
  -- swapE and swapD act on clean wires before and after
  have spE := spare_pool layout hw
  have spD := spareD_pool layout hw
  have E_def : ∀ q, swapE layout q = if q = layout.core.equalNegY then spareWire layout
      else if q = spareWire layout then layout.core.equalNegY else q := fun q => rfl
  have D_def : ∀ q, swapD layout q = if q = layout.doubleSelect then spareD layout
      else if q = spareD layout then layout.doubleSelect else q := fun q => rfl
  have R2E : (pullState (tauM layout) R0).basis layout.core.equalNegY = false := by
    rw [R2rest _ (flags_not_point _ eflag)]; exact hE
  have R2Es : (pullState (tauM layout) R0).basis (spareWire layout) = false := by
    rw [R2rest _ (pool_not_point _ spE)]; exact pclean _ spE
  have R2D : (pullState (tauM layout) R0).basis layout.doubleSelect = false := by
    rw [R2rest _ (flags_not_point _ dflag)]; exact hD
  have R2Ds : (pullState (tauM layout) R0).basis (spareD layout) = false := by
    rw [R2rest _ (pool_not_point _ spD)]; exact pclean _ spD
  have R3 : run (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P)))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ dinv _ _ _ (swap_sym _ _ _ D_def _ (by rw [hD, pclean _ spD]))
      (by rw [R3]; exact swap_sym _ _ _ D_def _ (by rw [R2D, R2Ds])), R3]
  rw [R4]
  refine ⟨?_, ?_, ?_, R2rest⟩
  · have e1 : (pullState (tauM layout) R0).phase = R0.phase := rfl
    rw [e1, ph0, ← ht']; rfl
  · rw [← v0.x]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_left _ hq)).1 (xyne q (List.mem_append_left _ hq)).2]
  · rw [← v0.y]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_right _ hq)).1 (xyne q (List.mem_append_right _ hq)).2]

def genBlockOpt (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ParityStageBothInverse23.genericAll L cx cy))
def finiteProgramOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlockOpt L cx cy))) ++ InputSentinel.outStage L C
def wrapperOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgramOpt L C cx cy)

open Classical in
theorem finite_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgramOpt layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgramOpt layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgramOpt
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlockOpt layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlockOpt
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ParityStageBothInverse23.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ParityStageBothInverse23.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) x y x y false
        (fun base' => ParityStageBothInverse23.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperOpt layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run hc b R s m hs
  unfold wrapperOpt
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h



theorem rename_wires_sub (f : Wire → Wire) (P Q : Program) (h : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  simp only [renameProgram_support]
  exact Finset.image_subset_image h

theorem wrapper_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆wires (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have h:=ParityStageBothInverse23.generic_wires layout layout_widths cx cy
  rw [reference_eq] at h
  have b:=rename_wires_sub (Wrapper5.U layout) _ _ (rename_wires_sub (swapF layout) _ _ h)
  have m:=rename_wires_sub (swapD layout) _ _ (rename_wires_sub (swapE layout) _ _
    (rename_wires_sub (tauM layout) _ _ b))
  unfold wrapperOpt InputSentinel530.wrapper530
  apply rename_wires_sub
  simp only [finiteProgramOpt,InputSentinel530.finiteProgram530,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) m) (Finset.Subset.refl _)

theorem support_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆layout.dialogUsedWires.toFinset :=
  (wrapper_support hc).trans (InputSentinel530.support_used530 hc)

theorem wrapper_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperOpt layout (.some hc) cx cy)+6=
      toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    measurementCount (wrapperOpt layout (.some hc) cx cy)=
      measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    gateSlots (wrapperOpt layout (.some hc) cx cy)≤
      gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)+302 := by
  have t:=ParityStageBothInverse23.generic_toffoli layout layout_widths cx cy
  have h:=ParityStageBothInverse23.generic_counts layout layout_widths cx cy
  rw [reference_eq] at t h
  simp only [wrapperOpt,finiteProgramOpt,genBlockOpt,InputSentinel530.wrapper530,
    InputSentinel530.finiteProgram530,InputSentinel530.genBlock530,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega
theorem wrapper_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperOpt layout (.some hc) cx cy) := by
  have old:GatePhysical (ParityStageBothInverse23.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0:=ParityStageBothInverse23.generic_physical layout layout_widths layout_nodup cx cy old
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapperOpt
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgramOpt,genBlockOpt,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,InputSentinel.outStage_physical hc⟩

open Classical in
theorem full_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperOpt layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programOpt (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperOpt layout C cx cy

def entryOpt : Challenge.Entry := fun C=>normalizeProgram (programOpt C)
def boundsOpt : Challenge.Bounds := ⟨2150282,1498370,1587,50251236⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150282 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150288 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150282
    omega

theorem program_measurements (C : Point) : measurementCount (programOpt C)≤1498370 := by
  cases C with
  | zero=>simp [programOpt,measurementCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_measurements530 (.some hc)
    have delta:=(wrapper_metrics hc).2.1
    change measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370
    omega

theorem program_qubits (C : Point) : qubits (programOpt C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=InputSentinel530.program_qubits530 (.some hc)
    change qubits (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) (wrapper_support hc)

theorem program_physical (C : Point) : GatePhysical (programOpt C) := by
  cases C with
  | zero=>simp [programOpt,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical hc

theorem program_slots (C : Point) : gateSlots (programOpt C)≤50251236 := by
  cases C with
  | zero=>simp [programOpt]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_slots530 (.some hc)
    have delta:=(wrapper_metrics hc).2.2
    change gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤50250934 at old
    change gateSlots (wrapperOpt layout (.some hc) cx cy)≤50251236
    omega

theorem certificateOpt : Challenge.Certificate entryOpt boundsOpt where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programOpt C))≤1498370
    rw [normalize_measurements];exact program_measurements C
  qubits_le C:=by
    change qubits (normalizeProgram (programOpt C))≤1587
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C:=by
    change gateSlots (normalizeProgram (programOpt C))≤50251236
    rw [normalize_slots];exact program_slots C

end ECDSAAdd.Entrant.ParityFinalBothInverse23XY

end

-- Adapted public peer module: ParityFinalBothInverse23Out
section

namespace ECDSAAdd.Entrant.ParityFinalBothInverse23Out
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  ParityStageBothInverse23.genericAll Entry530.generic530

theorem reference_eq (L : ControlledPointLayout) (cx cy : Fp) :
    ParityStageBothInverse23.genericRef L cx cy=Entry530.generic530 L cx cy :=
  ParityFinalBothInverse23XY.reference_eq L cx cy

abbrev gen_block_run := ParityFinalBothInverse23XY.gen_block_run

def genBlockOpt (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ParityStageBothInverse23.genericAll L cx cy))
def finiteProgramOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlockOpt L cx cy))) ++ OutputOpt.outStage L C
def wrapperOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgramOpt L C cx cy)

open Classical in
theorem finite_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgramOpt layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgramOpt layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgramOpt
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := OutputOpt.outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlockOpt layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlockOpt
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ParityStageBothInverse23.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ParityStageBothInverse23.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run (ParityStageBothInverse23.genericAll layout cx cy) x y x y false
        (fun base' => ParityStageBothInverse23.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperOpt layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run hc b R s m hs
  unfold wrapperOpt
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h



theorem rename_wires_sub (f : Wire → Wire) (P Q : Program) (h : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  simp only [renameProgram_support]
  exact Finset.image_subset_image h

theorem wrapper_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆wires (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have h:=ParityStageBothInverse23.generic_wires layout layout_widths cx cy
  rw [reference_eq] at h
  have b:=rename_wires_sub (Wrapper5.U layout) _ _ (rename_wires_sub (swapF layout) _ _ h)
  have m:=rename_wires_sub (swapD layout) _ _ (rename_wires_sub (swapE layout) _ _
    (rename_wires_sub (tauM layout) _ _ b))
  unfold wrapperOpt InputSentinel530.wrapper530
  apply rename_wires_sub
  simp only [finiteProgramOpt,InputSentinel530.finiteProgram530,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) m)
    (OutputOpt.outStage_subset layout (.some hc))

theorem support_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆layout.dialogUsedWires.toFinset :=
  (wrapper_support hc).trans (InputSentinel530.support_used530 hc)

theorem wrapper_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperOpt layout (.some hc) cx cy)+7=
      toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    measurementCount (wrapperOpt layout (.some hc) cx cy)=
      measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    gateSlots (wrapperOpt layout (.some hc) cx cy)≤
      gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)+314 := by
  have A:=ParityFinalBothInverse23XY.wrapper_metrics hc
  have B:=OutputOpt.outStage_metrics hc
  simp only [wrapperOpt,finiteProgramOpt,genBlockOpt,ParityFinalBothInverse23XY.wrapperOpt,
    ParityFinalBothInverse23XY.finiteProgramOpt,ParityFinalBothInverse23XY.genBlockOpt,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots] at A ⊢
  omega

theorem wrapper_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperOpt layout (.some hc) cx cy) := by
  have old:GatePhysical (ParityStageBothInverse23.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0:=ParityStageBothInverse23.generic_physical layout layout_widths layout_nodup cx cy old
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapperOpt
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgramOpt,genBlockOpt,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,OutputOpt.outStage_physical hc⟩

open Classical in
theorem full_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperOpt layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programOpt (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperOpt layout C cx cy

def entryOpt : Challenge.Entry := fun C=>normalizeProgram (programOpt C)
def boundsOpt : Challenge.Bounds := ⟨2150281,1498370,1587,50251248⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150281 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150288 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150281
    omega

theorem program_measurements (C : Point) : measurementCount (programOpt C)≤1498370 := by
  cases C with
  | zero=>simp [programOpt,measurementCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_measurements530 (.some hc)
    have delta:=(wrapper_metrics hc).2.1
    change measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370
    omega

theorem program_qubits (C : Point) : qubits (programOpt C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=InputSentinel530.program_qubits530 (.some hc)
    change qubits (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) (wrapper_support hc)

theorem program_physical (C : Point) : GatePhysical (programOpt C) := by
  cases C with
  | zero=>simp [programOpt,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical hc

theorem program_slots (C : Point) : gateSlots (programOpt C)≤50251248 := by
  cases C with
  | zero=>simp [programOpt]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_slots530 (.some hc)
    have delta:=(wrapper_metrics hc).2.2
    change gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤50250934 at old
    change gateSlots (wrapperOpt layout (.some hc) cx cy)≤50251248
    omega

theorem certificateOpt : Challenge.Certificate entryOpt boundsOpt where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programOpt C))≤1498370
    rw [normalize_measurements];exact program_measurements C
  qubits_le C:=by
    change qubits (normalizeProgram (programOpt C))≤1587
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C:=by
    change gateSlots (normalizeProgram (programOpt C))≤50251248
    rw [normalize_slots];exact program_slots C

end ECDSAAdd.Entrant.ParityFinalBothInverse23Out

end

section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
/-! Pure comparison facts for the classifier chain. MSB-first scan equals the numeric order, and the
XOR of prefix differences over positions where the constant bit is clear equals the same scan. -/

namespace ECDSAAdd.Entrant.PrefixCompare

/-- MSB-first strict comparison of `x` and `a` over the listed bit positions. -/
def gtBits (x a : Nat) : List Nat → Bool
  | [] => false
  | i :: l => (x.testBit i && !a.testBit i) || ((x.testBit i == a.testBit i) && gtBits x a l)

/-- The chain form. `e` is the running prefix, `mt i` the match literal at position `i`.
Only positions whose constant bit is clear contribute, each as `e ^^ e'`. -/
def xorForm (a : Nat) (mt : Nat → Bool) : Bool → List Nat → Bool
  | _, [] => false
  | e, i :: l =>
    (if a.testBit i then false else (e ^^ (e && mt i))) ^^ xorForm a mt (e && mt i) l

theorem xorForm_false (a : Nat) (mt : Nat → Bool) (l : List Nat) : xorForm a mt false l = false := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [xorForm, Bool.false_and, ih]
    cases a.testBit i <;> rfl

/-- When the literals are genuine matches against `a`, the chain form is the gated scan. -/
theorem xorForm_eq (x a : Nat) (mt : Nat → Bool) (l : List Nat) (e : Bool)
    (h : ∀ i ∈ l, mt i = (x.testBit i == a.testBit i)) :
    xorForm a mt e l = (e && gtBits x a l) := by
  induction l generalizing e with
  | nil => simp [xorForm, gtBits]
  | cons i l ih =>
    have hi := h i (List.mem_cons_self ..)
    have hl : ∀ j ∈ l, mt j = (x.testBit j == a.testBit j) :=
      fun j hj => h j (List.mem_cons_of_mem _ hj)
    simp only [xorForm, gtBits, ih _ hl, hi]
    cases hx : x.testBit i <;> cases ha : a.testBit i <;> cases e <;> simp

theorem testBit_of_div (x i : Nat) : x.testBit i = decide (x / 2^i % 2 = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

/-- Splitting off the top bit of a residue. -/
theorem mod_succ (x n : Nat) :
    x % 2^(n+1) = x % 2^n + 2^n * (if x.testBit n then 1 else 0) := by
  have h := Nat.mod_pow_succ (x := x) (b := 2) (k := n)
  rw [h, testBit_of_div]
  have : x / 2^n % 2 = 0 ∨ x / 2^n % 2 = 1 := by omega
  rcases this with e | e <;> simp [e]

/-- Numeric meaning of the scan over all positions below `n`, top first. -/
theorem gtBits_range (x a n : Nat) :
    gtBits x a (List.range n).reverse = decide (a % 2^n < x % 2^n) := by
  induction n with
  | zero => simp [gtBits, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, gtBits, ih]
    rw [mod_succ x n, mod_succ a n]
    have hx : x % 2^n < 2^n := Nat.mod_lt _ (by exact Nat.two_pow_pos n)
    have ha : a % 2^n < 2^n := Nat.mod_lt _ (by exact Nat.two_pow_pos n)
    cases bx : x.testBit n <;> cases ba : a.testBit n <;> simp <;> omega

theorem gtBits_full (x a n : Nat) (hx : x < 2^n) (ha : a < 2^n) :
    gtBits x a (List.range n).reverse = decide (a < x) := by
  rw [gtBits_range, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt ha]

theorem gtBits_append (x a : Nat) (l r : List Nat) :
    gtBits x a (l ++ r) =
      (gtBits x a l || ((l.all fun i => x.testBit i == a.testBit i) && gtBits x a r)) := by
  induction l with
  | nil => simp [gtBits]
  | cons i l ih =>
    simp only [List.cons_append, gtBits, ih, List.all_cons]
    cases (x.testBit i && !a.testBit i) <;> cases (x.testBit i == a.testBit i) <;>
      cases gtBits x a l <;> simp


/-- Two-pivot segmented formula. `eh`, `el` are the running prefixes above the pivots. -/
def formula (x a : Nat) (mt : Nat → Bool) (top mid low : List Nat) (hi lo : Nat) : Bool :=
  let eh := top.all mt
  let el := eh && mid.all mt
  let dh := x.testBit hi != a.testBit hi
  let dl := x.testBit lo != a.testBit lo
  xorForm a mt true top ^^ (eh && (x.testBit hi && !a.testBit hi)) ^^
    (!dh && (xorForm a mt eh mid ^^ (el && (x.testBit lo && !a.testBit lo)) ^^
      (!dl && xorForm a mt el low)))

theorem all_congr' (l : List Nat) (f g : Nat → Bool) (h : ∀ i ∈ l, f i = g i) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.all_cons, h i (List.mem_cons_self ..),
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

theorem gt_all_false (x a : Nat) (l : List Nat) :
    gtBits x a l = true → (l.all fun i => x.testBit i == a.testBit i) = false := by
  induction l with
  | nil => simp [gtBits]
  | cons i l ih =>
    intro h
    simp only [gtBits] at h
    simp only [List.all_cons]
    by_cases e : x.testBit i = a.testBit i
    · have hg : gtBits x a l = true := by
        rw [e] at h
        cases ha : a.testBit i <;> simp_all
      rw [ih hg, Bool.and_false]
    · have : (x.testBit i == a.testBit i) = false := by simpa using e
      rw [this, Bool.false_and]

theorem formula_eq (x a : Nat) (mt : Nat → Bool) (top mid low : List Nat) (hi lo : Nat)
    (ht : ∀ i ∈ top, mt i = (x.testBit i == a.testBit i))
    (hm : x.testBit hi = a.testBit hi → ∀ i ∈ mid, mt i = (x.testBit i == a.testBit i))
    (hl : x.testBit hi = a.testBit hi → x.testBit lo = a.testBit lo →
      ∀ i ∈ low, mt i = (x.testBit i == a.testBit i)) :
    formula x a mt top mid low hi lo = gtBits x a (top ++ hi :: mid ++ lo :: low) := by
  have eT : top.all mt = top.all (fun i => x.testBit i == a.testBit i) := all_congr' _ _ _ ht
  have gT := gt_all_false x a top
  have gM := gt_all_false x a mid
  have xT := xorForm_eq x a mt top true ht
  simp only [Bool.true_and] at xT
  simp only [formula, xT, eT]
  rw [List.append_assoc, gtBits_append]
  simp only [List.cons_append, gtBits]
  clear eT xT ht
  generalize (top.all fun i => x.testBit i == a.testBit i) = AT at gT ⊢
  generalize gtBits x a top = GT at gT ⊢
  cases hb : (x.testBit hi == a.testBit hi)
  · -- high pivot differs: the rest is gated off
    have hd : (x.testBit hi != a.testBit hi) = true := by simpa [bne] using hb
    simp [hd]
    cases GT <;> cases AT <;> cases x.testBit hi <;> cases a.testBit hi <;> simp_all
  · have he : x.testBit hi = a.testBit hi := by simpa using hb
    have hm' := hm he
    have eM : mid.all mt = mid.all (fun i => x.testBit i == a.testBit i) := all_congr' _ _ _ hm'
    have xM := fun e => xorForm_eq x a mt mid e hm'
    have hd : (x.testBit hi != a.testBit hi) = false := by simp [he]
    simp only [hd, Bool.not_false, Bool.true_and, eM, xM, gtBits_append]
    simp only [gtBits]
    clear xM eM hm' hm
    generalize (mid.all fun i => x.testBit i == a.testBit i) = AM at gM ⊢
    generalize gtBits x a mid = GM at gM ⊢
    cases hc : (x.testBit lo == a.testBit lo)
    · have hd2 : (x.testBit lo != a.testBit lo) = true := by simpa [bne] using hc
      simp only [hd2, Bool.not_true, Bool.false_and, Bool.xor_false]
      rw [he]
      cases GT <;> cases AT <;> cases GM <;> cases AM <;>
        cases x.testBit lo <;> cases a.testBit lo <;> cases a.testBit hi <;> simp_all
    · have he2 : x.testBit lo = a.testBit lo := by simpa using hc
      have hd2 : (x.testBit lo != a.testBit lo) = false := by simp [he2]
      simp only [hd2, Bool.not_false, Bool.true_and, xorForm_eq x a mt low _ (hl he he2)]
      rw [he, he2]
      cases GT <;> cases AT <;> cases GM <;> cases AM <;>
        cases gtBits x a low <;> cases a.testBit lo <;> cases a.testBit hi <;> simp_all


end ECDSAAdd.Entrant.PrefixCompare

namespace ECDSAAdd.Entrant.InputSentinel.Tri
open ECDSAAdd.Entrant.PrefixCompare
variable {t : Tri}

/-- Above both pivots every pattern's target is `A`. -/
theorem tgt_top (v : t.Valid) (i : Nat) (h1 : t.r1 < i) (h2 : t.r2 < i) (p : Bool × Bool) :
    t.tgt i p = t.A.testBit i := by
  have bs := (firstDiff_top t.B t.S v.hB v.hS v.BS).2.2 i h1
  have aw : t.A.testBit i = t.B.testBit i ∨ t.A.testBit i = t.S.testBit i := by
    cases ro : t.role1
    · left
      have er2 : t.r2 = firstDiff t.A t.B := by simp [r2, ro]
      exact (firstDiff_top t.A t.B v.hA v.hB v.AB).2.2 i (er2 ▸ h2)
    · right
      have er2 : t.r2 = firstDiff t.A t.S := by simp [r2, ro]
      exact (firstDiff_top t.A t.S v.hA v.hS v.AS).2.2 i (er2 ▸ h2)
  have ab : t.A.testBit i = t.B.testBit i := by
    rcases aw with e | e
    · exact e
    · rw [e, bs]
  have as' : t.A.testBit i = t.S.testBit i := by rw [ab, bs]
  unfold tgt
  rw [← ab, ← as']
  repeat' split
  all_goals simp


/-- Low segment: both pivots match, so the pattern is `A`'s. -/
theorem tgt_low (i : Nat) (p : Bool × Bool) (hp : p = t.pat t.A) : t.tgt i p = t.A.testBit i := by
  unfold tgt; rw [if_pos hp]

/-- Finite core of the middle segment. `w` is the partner word sharing the high pivot with `A`,
`o` the other one. Written against the three-way target, in both orders of the two words. -/
theorem mid_core : ∀ a1 a2 b1 b2 s1 s2 ai bi si p1 p2 : Bool,
    ((a1 = s1 ∧ b1 ≠ s1 ∧ a2 ≠ s2 ∧ ai = si ∧ p1 = a1) ∨
     (a1 ≠ s1 ∧ b1 ≠ s1 ∧ a2 ≠ b2 ∧ ai = bi ∧ p1 = a1) ∨
     (bi = si ∧ b2 = s2 ∧ a2 ≠ s2 ∧ p2 = a2)) →
    (if (p1, p2) = (a1, a2) then ai else if (p1, p2) = (b1, b2) then bi
      else if (p1, p2) = (s1, s2) then si else ai ^^ bi ^^ si) = ai := by
  intro a1 a2 b1 b2 s1 s2 ai bi si p1 p2 h
  rcases h with ⟨e1, n1, n2, e2, e3⟩ | ⟨n0, n1, n2, e2, e3⟩ | ⟨e1, e2, n1, e3⟩
  · subst e1 e2 e3
    cases p1 <;> cases p2 <;> cases a2 <;> cases b1 <;> cases s2 <;> cases b2 <;> simp_all
  · subst e2 e3
    cases p1 <;> cases p2 <;> cases a2 <;> cases b2 <;> cases s1 <;> cases s2 <;> cases b1 <;>
      simp_all
  · subst e1 e2 e3
    cases p1 <;> cases p2 <;> cases a1 <;> cases b1 <;> cases s1 <;> cases b2 <;> cases ai <;>
      cases bi <;> simp_all

/-- Middle segment, high pivot `r1`. -/
theorem tgt_mid1 (v : t.Valid) (i : Nat) (hlo : t.r2 < i) (p : Bool × Bool)
    (hp : p.1 = t.A.testBit t.r1) : t.tgt i p = t.A.testBit i := by
  have bs := (firstDiff_top t.B t.S v.hB v.hS v.BS).2.1
  have er1 : t.r1 = firstDiff t.B t.S := rfl
  rw [← er1] at bs
  obtain ⟨p1, p2⟩ := p
  unfold tgt pat
  apply mid_core
  cases ro : t.role1
  · have er2 : t.r2 = firstDiff t.A t.B := by simp [r2, ro]
    have d := (firstDiff_top t.A t.B v.hA v.hB v.AB).2
    rw [← er2] at d
    have ne : t.A.testBit t.r1 ≠ t.S.testBit t.r1 := by simpa [role1] using ro
    exact Or.inr (Or.inl ⟨ne, bs, d.1, d.2 i hlo, hp⟩)
  · have er2 : t.r2 = firstDiff t.A t.S := by simp [r2, ro]
    have d := (firstDiff_top t.A t.S v.hA v.hS v.AS).2
    rw [← er2] at d
    have eq : t.A.testBit t.r1 = t.S.testBit t.r1 := by simpa [role1] using ro
    exact Or.inl ⟨eq, bs, d.1, d.2 i hlo, hp⟩

/-- Middle segment, high pivot `r2`. -/
theorem tgt_mid2 (v : t.Valid) (i : Nat) (hlo : t.r1 < i) (hhi : t.r1 < t.r2) (p : Bool × Bool)
    (hp : p.2 = t.A.testBit t.r2) : t.tgt i p = t.A.testBit i := by
  have above := (firstDiff_top t.B t.S v.hB v.hS v.BS).2.2
  have er1 : t.r1 = firstDiff t.B t.S := rfl
  rw [← er1] at above
  obtain ⟨p1, p2⟩ := p
  unfold tgt pat
  apply mid_core
  refine Or.inr (Or.inr ⟨above i hlo, above _ hhi, ?_, hp⟩)
  cases ro : t.role1
  · have er2 : t.r2 = firstDiff t.A t.B := by simp [r2, ro]
    have d := (firstDiff_top t.A t.B v.hA v.hB v.AB).2.1
    rw [← er2] at d
    rw [← above _ hhi]; exact d
  · have er2 : t.r2 = firstDiff t.A t.S := by simp [r2, ro]
    have d := (firstDiff_top t.A t.S v.hA v.hS v.AS).2.1
    rw [← er2] at d
    exact d


/-- High and low pivot. -/
def hi (t : Tri) : Nat := max t.r1 t.r2
def lo (t : Tri) : Nat := min t.r1 t.r2

/-- Descending positions strictly between `b` and `c`, that is `c-1` down to `b+1`. -/
def seg (b c : Nat) : List Nat := (List.range' (b+1) (c-b-1)).reverse

def topL (t : Tri) : List Nat := seg t.hi 256
def midL (t : Tri) : List Nat := seg t.lo t.hi
def lowL (t : Tri) : List Nat := (List.range t.lo).reverse

theorem mem_seg (b c i : Nat) : i ∈ seg b c ↔ b < i ∧ i < c := by
  simp only [seg, List.mem_reverse, List.mem_range'_1]
  omega

theorem range_split (l h : Nat) (hl : l < h) (hh : h < 256) :
    (List.range 256).reverse = seg h 256 ++ h :: seg l h ++ l :: (List.range l).reverse := by
  have a1 : h :: List.range' (h+1) (256-h-1) = List.range' h (256-h) := by
    rw [show 256-h = (256-h-1)+1 by omega, List.range'_succ]
    simp
  have a2 : List.range' (l+1) (h-l-1) ++ List.range' h (256-h) = List.range' (l+1) (256-l-1) := by
    have := List.range'_append_1 (s := l+1) (m := h-l-1) (n := 256-h)
    rw [show l+1+(h-l-1) = h by omega, show (h-l-1)+(256-h) = 256-l-1 by omega] at this
    simpa using this
  have a3 : l :: List.range' (l+1) (256-l-1) = List.range' l (256-l) := by
    rw [show 256-l = (256-l-1)+1 by omega, List.range'_succ]
    simp
  have a4 : List.range' 0 l ++ List.range' l (256-l) = List.range' 0 256 := by
    have := List.range'_append_1 (s := 0) (m := l) (n := 256-l)
    rw [show 0+l = l by omega, show l+(256-l) = 256 by omega] at this
    simpa using this
  have e : List.range 256 = List.range l ++ (l :: (List.range' (l+1) (h-l-1) ++
      (h :: List.range' (h+1) (256-h-1)))) := by
    rw [a1, a2, a3, List.range_eq_range' (n := l), a4, List.range_eq_range']
  rw [e]
  simp [seg, List.reverse_append]


theorem r1_lt (v : t.Valid) : t.r1 < 256 := (firstDiff_top t.B t.S v.hB v.hS v.BS).1

theorem r2_lt (v : t.Valid) : t.r2 < 256 := by
  cases ro : t.role1
  · have er2 : t.r2 = firstDiff t.A t.B := by simp [r2, ro]
    rw [er2]; exact (firstDiff_top t.A t.B v.hA v.hB v.AB).1
  · have er2 : t.r2 = firstDiff t.A t.S := by simp [r2, ro]
    rw [er2]; exact (firstDiff_top t.A t.S v.hA v.hS v.AS).1

/-- The chain formula is the strict comparison with `A`. -/
theorem formula_compare (v : t.Valid) (hne : t.r1 ≠ t.r2) (x : Nat) (hx : x < 2^256) :
    let p := (x.testBit t.r1, x.testBit t.r2)
    formula x t.A (fun i => x.testBit i == t.tgt i p) t.topL t.midL t.lowL t.hi t.lo =
      decide (t.A < x) := by
  intro p
  have h1 := r1_lt v
  have h2 := r2_lt v
  have hlh : t.lo < t.hi := by simp only [hi, lo]; omega
  have hh : t.hi < 256 := by simp only [hi]; omega
  rw [formula_eq, topL, midL, lowL, ← range_split _ _ hlh hh, gtBits_full x t.A 256 hx v.hA]
  · intro i hi'
    have := (mem_seg _ _ _).mp hi'
    simp only [hi] at this
    rw [tgt_top v i (by omega) (by omega)]
  · intro he i hi'
    have := (mem_seg _ _ _).mp hi'
    by_cases c : t.r2 < t.r1
    · have eh : t.hi = t.r1 := by simp only [hi]; omega
      have el : t.lo = t.r2 := by simp only [lo]; omega
      rw [eh] at he this
      rw [el] at this
      rw [tgt_mid1 v i this.1 p he]
    · have c' : t.r1 < t.r2 := by omega
      have eh : t.hi = t.r2 := by simp only [hi]; omega
      have el : t.lo = t.r1 := by simp only [lo]; omega
      rw [eh] at he this
      rw [el] at this
      rw [tgt_mid2 v i this.1 c' p he]
  · intro he he2 i _
    have : p = t.pat t.A := by
      by_cases c : t.r2 < t.r1
      · have eh : t.hi = t.r1 := by simp only [hi]; omega
        have el : t.lo = t.r2 := by simp only [lo]; omega
        rw [eh] at he; rw [el] at he2
        simp [p, pat, he, he2]
      · have eh : t.hi = t.r2 := by simp only [hi]; omega
        have el : t.lo = t.r1 := by simp only [lo]; omega
        rw [eh] at he; rw [el] at he2
        simp [p, pat, he, he2]
    rw [tgt_low i p this]

end ECDSAAdd.Entrant.InputSentinel.Tri

/-! Generic semantics of `zeroWith`: fill the prefixes, run the inner program, clear. -/
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

/-- Basis after the descending ANDs: each work wire holds its running prefix. -/
def fill : Wire → List ZeroBit → BasisState → BasisState
  | _, [], st => st
  | c, b :: bs, st =>
    fill b.work bs (writeBit st b.work (st b.work ^^ (st c && !st b.input)))

/-- The last chain wire. -/
def lastWire : Wire → List ZeroBit → Wire
  | c, [] => c
  | _, b :: bs => lastWire b.work bs

/-- Basis after the erases: every work wire false. -/
def clear : List ZeroBit → BasisState → BasisState
  | [], st => st
  | b :: bs, st => writeBit (clear bs st) b.work false

theorem fill_outside (c : Wire) (bs : List ZeroBit) (st : BasisState) (q : Wire)
    (h : ∀ b ∈ bs, b.work ≠ q) : fill c bs st q = st q := by
  induction bs generalizing c st with
  | nil => rfl
  | cons b bs ih =>
    simp only [fill]
    rw [ih _ _ (fun d hd => h d (by simp [hd]))]
    have : q ≠ b.work := fun e => h b (by simp) e.symm
    simp [writeBit, this]

theorem clear_outside (bs : List ZeroBit) (st : BasisState) (q : Wire)
    (h : ∀ b ∈ bs, b.work ≠ q) : clear bs st q = st q := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [clear]
    have : q ≠ b.work := fun e => h b (by simp) e.symm
    simp only [writeBit, Function.update_apply, this, if_false]
    exact ih (fun d hd => h d (by simp [hd]))

theorem run_no_measure (p : Program) (hp : measurementCount p = 0) (m : List Bool) (s : State) :
    run p m s = run p [] s := by
  rw [← run_take p m s, hp]
  simp

theorem zeroWith_fill (T : Wire → Program) (c : Wire) (bs : List ZeroBit)
    (hnd : (c :: bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b ∈ bs, s.basis b.work = false) (B : State)
    (hB : ∀ m', run (T (lastWire c bs)) m' ⟨s.phase, fill c bs s.basis⟩ = B)
    (hkeep : ∀ q ∈ c :: bs.flatMap ZeroBit.wires, B.basis q = fill c bs s.basis q) :
    run (zeroWith T c bs) m s = ⟨B.phase, clear bs B.basis⟩ := by
  induction bs generalizing c s m with
  | nil =>
    simp only [zeroWith, clear]
    exact (show run (T c) m s = B from hB m).trans rfl
  | cons b bs ih =>
    have hnames : (c :: b.input :: b.work :: bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    obtain ⟨⟨hci, hcw, hcR⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
    have hchild : (b.work :: bs.flatMap ZeroBit.wires).Nodup := List.nodup_cons.mpr ⟨hwR, hR⟩
    let q := s.basis c && !s.basis b.input
    let t : State := ⟨s.phase, writeBit s.basis b.work q⟩
    have hp : run (chainAnd c b.input b.work) m s = t := by
      rw [chainAnd_run c b.input b.work hci hiw]
      simp [t, q, hz b (by simp), writeBit]
    have htail (d : ZeroBit) (hd : d ∈ bs) : d.work ≠ b.work ∧ d.input ≠ b.work := by
      constructor <;> intro he <;> apply hwR <;>
        apply List.mem_flatMap.mpr <;> refine ⟨d, hd, ?_⟩ <;> simp [ZeroBit.wires, he]
    have hz' : ∀ d ∈ bs, t.basis d.work = false := by
      intro d hd
      simpa [t, writeBit, (htail d hd).1] using hz d (by simp [hd])
    have hin (d : ZeroBit) (hd : d ∈ bs) (w : Wire) (hw : w = c ∨ w = b.input ∨ w = b.work) :
        d.work ≠ w := by
      have dm : d.work ∈ bs.flatMap ZeroBit.wires :=
        List.mem_flatMap.mpr ⟨d, hd, by simp [ZeroBit.wires]⟩
      rcases hw with e | e | e <;> intro he <;> subst e
      · exact hcR (he ▸ dm)
      · exact hiR (he ▸ dm)
      · exact hwR (he ▸ dm)
    have hfill : fill c (b :: bs) s.basis = fill b.work bs t.basis := by
      simp [fill, t, q, hz b (by simp)]
    have hB' : ∀ m', run (T (lastWire b.work bs)) m' ⟨t.phase, fill b.work bs t.basis⟩ = B := by
      intro m'
      have := hB m'
      rw [hfill] at this
      exact this
    have hkeep' : ∀ w ∈ b.work :: bs.flatMap ZeroBit.wires, B.basis w = fill b.work bs t.basis w := by
      intro w hw
      rw [← hfill]
      apply hkeep w
      simp only [List.mem_cons, List.flatMap_cons, List.mem_append, ZeroBit.wires] at hw ⊢
      simp only [List.not_mem_nil, or_false]
      tauto
    have ihr : ∀ m', run (zeroWith T b.work bs) m' t = ⟨B.phase, clear bs B.basis⟩ :=
      fun m' => ih b.work hchild t m' hz' hB' hkeep'
    have hF : ∀ w, (w = c ∨ w = b.input ∨ w = b.work) →
        (clear bs B.basis) w = t.basis w := by
      intro w hw
      rw [clear_outside bs _ w (fun d hd => hin d hd w hw)]
      have hk := hkeep w (by
        rcases hw with e | e | e <;> subst e <;> simp [ZeroBit.wires])
      rw [hk, hfill, fill_outside b.work bs _ w (fun d hd => hin d hd w hw)]
    have hq : (clear bs B.basis) b.work =
        ((clear bs B.basis) c && !(clear bs B.basis) b.input) := by
      rw [hF _ (Or.inr (Or.inr rfl)), hF _ (Or.inl rfl), hF _ (Or.inr (Or.inl rfl))]
      simp [t, q, writeBit, hcw, hiw]
    change run (chainAnd c b.input b.work ++ zeroWith T b.work bs ++
      chainErase c b.input b.work) m s = _
    rw [run_append, run_take, run_append, run_take, hp, ihr]
    rw [chainErase_run c b.input b.work hci hiw hcw _ _ hq]
    simp only [clear]

theorem clear_write (bs : List ZeroBit) (st : BasisState) (P : Wire) (v : Bool)
    (h : ∀ b ∈ bs, b.work ≠ P) : clear bs (writeBit st P v) = writeBit (clear bs st) P v := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [clear]
    rw [ih (fun d hd => h d (by simp [hd]))]
    have hne : b.work ≠ P := h b (by simp)
    funext q
    by_cases q1 : q = b.work
    · subst q1; simp [writeBit, hne]
    · by_cases q2 : q = P
      · subst q2; simp [writeBit, Ne.symm hne]
      · simp [writeBit, q1, q2]

/-- Appending `E`, which only writes `P` at the state `T` reaches, adds that write to the run. -/
theorem zeroWith_extract (T : Wire → Program) (E : Program) (c : Wire) (bs : List ZeroBit)
    (hnd : (c :: bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b ∈ bs, s.basis b.work = false) (B : State)
    (hB : ∀ m', run (T (lastWire c bs)) m' ⟨s.phase, fill c bs s.basis⟩ = B)
    (hkeep : ∀ q ∈ c :: bs.flatMap ZeroBit.wires, B.basis q = fill c bs s.basis q)
    (P : Wire) (v : Bool) (hE : ∀ m', run E m' B = ⟨B.phase, writeBit B.basis P v⟩)
    (hP : P ∉ c :: bs.flatMap ZeroBit.wires) :
    run (zeroWith (fun w => T w ++ E) c bs) m s =
      ⟨(run (zeroWith T c bs) m s).phase, writeBit (run (zeroWith T c bs) m s).basis P v⟩ := by
  have ho := zeroWith_fill T c bs hnd s m hz B hB hkeep
  have hw : ∀ b ∈ bs, b.work ≠ P := by
    intro b hb e
    apply hP
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires, e]⟩
  have hn := zeroWith_fill (fun w => T w ++ E) c bs hnd s m hz ⟨B.phase, writeBit B.basis P v⟩
    (by
      intro m'
      show run (T (lastWire c bs) ++ E) m' _ = _
      rw [run_append, run_take, hB, hE])
    (by
      intro q hq
      have hne : q ≠ P := fun e => hP (e ▸ hq)
      simpa [writeBit, hne] using hkeep q hq)
  rw [hn, ho]
  simp only [clear_write bs _ P v hw]


/-- Compute, one Toffoli into the target, then uncompute. -/
theorem sandwich (pre : Program) (hp : ∀ i ∈ pre, ProperGate i) (G F P : Wire)
    (hPw : P ∉ wires pre) (hGP : G ≠ P) (hFP : F ≠ P) (s : State) (m : List Bool) :
    run (pre ++ (.CCX G F P :: pre.reverse)) m s =
      ⟨s.phase, writeBit s.basis P
        (s.basis P ^^ ((run pre [] s).basis G && (run pre [] s).basis F))⟩ := by
  have hmc : measurementCount pre = 0 := properProgram_measurementCount pre hp
  rw [run_append, run_take]
  rw [run_no_measure pre hmc m s]
  set r := run pre [] s with hr
  simp only [run]
  set v := r.basis G && r.basis F with hv
  set r' : State := ⟨r.phase, writeBit r.basis P (r.basis P ^^ v)⟩ with hr'
  have hback : run pre.reverse [] r = s := run_reverse_proper pre hp s [] []
  have hprop : ProperProgram pre.reverse := by
    intro i hi; exact hp i (List.mem_reverse.mp hi)
  have hmr : measurementCount pre.reverse = 0 := by rw [measurementCount_reverse]; exact hmc
  rw [run_no_measure pre.reverse hmr]
  have hcong := run_proper_congr pre.reverse hprop r' r [] [] rfl (by
    intro q hq
    have : q ≠ P := by
      intro e; subst e; exact hPw (by simpa [wires_reverse] using hq)
    simp [r', writeBit, this])
  rw [hback] at hcong
  have hrP : r.basis P = s.basis P := run_preserves_outside pre [] s P hPw
  apply State.extensionality
  · exact hcong.1
  · funext q
    by_cases hq : q ∈ wires pre
    · have hne : q ≠ P := fun e => hPw (e ▸ hq)
      have := hcong.2 q (by simpa [wires_reverse] using hq)
      rw [this]
      simp [writeBit, hne]
    · have hq' : q ∉ wires pre.reverse := by simpa [wires_reverse] using hq
      rw [run_preserves_outside _ _ _ q hq']
      by_cases hne : q = P
      · subst hne; simp [r', writeBit, hrP]
      · have : r.basis q = s.basis q := run_preserves_outside pre [] s q hq
        simp [r', writeBit, hne, this]


/-- Toggle `acc` by the prefix differences at positions whose constant bit is clear. -/
def xorAcc (a : Nat) (acc : Wire) : List (Nat × Wire × Wire) → Program
  | [] => []
  | (i, p, c) :: r => (if a.testBit i then [] else [.CX p acc, .CX c acc]) ++ xorAcc a acc r

def accVal (a : Nat) (st : BasisState) : List (Nat × Wire × Wire) → Bool
  | [] => false
  | (i, p, c) :: r => (if a.testBit i then false else (st p ^^ st c)) ^^ accVal a st r

/-- Wires of a segment hold the running prefix. -/
def Chain (st : BasisState) (mt : Nat → Bool) : Bool → List (Nat × Wire × Wire) → Prop
  | _, [] => True
  | e, (i, p, c) :: r => st p = e ∧ st c = (e && mt i) ∧ Chain st mt (e && mt i) r

theorem accVal_chain (a : Nat) (st : BasisState) (mt : Nat → Bool) (e : Bool)
    (T : List (Nat × Wire × Wire)) (h : Chain st mt e T) :
    accVal a st T = PrefixCompare.xorForm a mt e (T.map (·.1)) := by
  induction T generalizing e with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    obtain ⟨h1, h2, h3⟩ := h
    simp only [accVal, List.map_cons, PrefixCompare.xorForm, ih _ h3, h1, h2]

theorem accVal_write (a : Nat) (st : BasisState) (t : Wire) (v : Bool)
    (T : List (Nat × Wire × Wire)) (h : ∀ x ∈ T, x.2.1 ≠ t ∧ x.2.2 ≠ t) :
    accVal a (writeBit st t v) T = accVal a st T := by
  induction T with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    have hx := h (i, p, c) (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only [accVal, hr]
    simp [writeBit, hx.1, hx.2]

/-- Toggle `t` by `v`. -/
def xw (s : State) (t : Wire) (v : Bool) : State := ⟨s.phase, writeBit s.basis t (s.basis t ^^ v)⟩

theorem run_xorAcc (a : Nat) (acc : Wire) (T : List (Nat × Wire × Wire))
    (h : ∀ x ∈ T, x.2.1 ≠ acc ∧ x.2.2 ≠ acc) (s : State) (m : List Bool) :
    run (xorAcc a acc T) m s = xw s acc (accVal a s.basis T) := by
  induction T generalizing s with
  | nil =>
    simp only [xorAcc, run, accVal, xw]
    apply State.extensionality <;> simp [writeBit]
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    have hx := h (i, p, c) (by simp)
    have hr := fun s => ih (fun y hy => h y (by simp [hy])) s
    simp only at hx
    have hr' := fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases hb : a.testBit i
    · simp only [xorAcc, accVal, hb]
      simp only [Bool.false_eq_true, if_false, List.cons_append, List.nil_append, run]
      rw [hr]
      simp only [xw]
      apply State.extensionality
      · rfl
      · funext q
        rw [accVal_write a _ acc _ r hr', accVal_write a _ acc _ r hr']
        by_cases e : q = acc
        · subst e; simp [writeBit, hx.2]
        · simp [writeBit, e]
    · simp only [xorAcc, accVal, hb, if_true, List.nil_append, Bool.false_xor]
      exact hr s

/-- `v ^= (x == aL) & u ^ e & x & !aL`. When `aL` is false the two products form a
multiplexer on `x`, which is `u ^ x & (u ^ e)`, so one Toffoli covers both. -/
def muxAnd (aL : Bool) (e x u v : Wire) : Program :=
  if aL then [.CCX x u v] else [.CX e u, .CCX x u v, .CX e u, .CX u v]

theorem mux_value (x u e : Bool) :
    ((x && (u ^^ e)) ^^ u) = (((x == false) && u) ^^ (e && (x && !false))) := by
  cases x <;> cases u <;> cases e <;> rfl

theorem run_muxAnd (aL : Bool) (e x u v : Wire) (heu : e ≠ u) (hxu : x ≠ u) (hxv : x ≠ v)
    (huv : u ≠ v) (hev : e ≠ v) (s : State) (m : List Bool) :
    run (muxAnd aL e x u v) m s =
      xw s v (((s.basis x == aL) && s.basis u) ^^ (s.basis e && (s.basis x && !aL))) := by
  cases aL
  · simp only [muxAnd, run, xw, Bool.false_eq_true, if_false]
    apply State.extensionality
    · rfl
    · funext q
      by_cases e1 : q = v
      · subst e1
        rw [← mux_value]
        simp [writeBit, Function.update_apply, hxv.symm, huv.symm, hev.symm, hxu, heu, huv, hxv, hev,
          Bool.xor_assoc]
      · by_cases e2 : q = u
        · subst e2
          simp [writeBit, Function.update_apply, e1, heu, hxu, Ne.symm heu, hev, Bool.xor_assoc]
        · simp [writeBit, Function.update_apply, e1, e2]
  · simp only [muxAnd, run, xw, if_true]
    apply State.extensionality
    · rfl
    · funext q; simp

/-- The extraction body, before the single Toffoli into the parked wire. -/
def pre (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) : Program :=
  [.X one] ++ (xorAcc a U low ++ (muxAnd aL el xlo U V ++ (xorAcc a V mid ++
    (muxAnd aH eh xhi V F ++ xorAcc a F top))))

theorem run_cat (p q : Program) (hp : measurementCount p = 0) (m : List Bool) (s : State) :
    run (p ++ q) m s = run q m (run p [] s) := by
  rw [run_append, run_take, run_no_measure p hp m s, hp]
  simp

theorem xorAcc_mc (a : Nat) (acc : Wire) (T : List (Nat × Wire × Wire)) :
    measurementCount (xorAcc a acc T) = 0 := by
  induction T with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    simp only [xorAcc, measurementCount_append, ih]
    cases a.testBit i <;> simp [measurementCount]

theorem muxAnd_mc (aL : Bool) (e x u v : Wire) : measurementCount (muxAnd aL e x u v) = 0 := by
  cases aL <;> simp [muxAnd, measurementCount]

theorem pre_bool (A L C M E T : Bool) :
    (((A && ((L ^^ C) ^^ M)) ^^ E) ^^ T) = ((A && (L ^^ M ^^ C)) ^^ T ^^ E) := by
  cases A <;> cases L <;> cases C <;> cases M <;> cases E <;> cases T <;> rfl

/-- Value of `F` after `pre`, read off the state with `one` set. -/
theorem pre_F (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let st := writeBit s.basis one (!s.basis one)
    (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis F =
      (((st xhi == aH) && (((st xlo == aL) && accVal a st low) ^^ accVal a st mid ^^
        (st el && (st xlo && !aL)))) ^^ accVal a st top ^^ (st eh && (st xhi && !aH))) := by
  intro st
  have sU : st U = false := by simp [st, writeBit, hoU.symm, hU]
  have sV : st V = false := by simp [st, writeBit, hoV.symm, hV]
  have sF : st F = false := by simp [st, writeBit, hoF.symm, hF]
  have tl : ∀ x ∈ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  have tm : ∀ x ∈ mid, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  have tt : ∀ x ∈ top, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  simp only [pre]
  rw [run_cat _ _ rfl, run_cat _ _ (xorAcc_mc ..), run_cat _ _ (muxAnd_mc ..),
    run_cat _ _ (xorAcc_mc ..), run_cat _ _ (muxAnd_mc ..)]
  have h1 : run [Instr.X one] [] s = ⟨s.phase, st⟩ := rfl
  rw [h1]
  clear_value st
  rw [run_xorAcc a U low (fun x hx => (tl x hx).1)]
  rw [run_muxAnd aL el xlo U V heU hlU hlV hUV heV]
  rw [run_xorAcc a V mid (fun x hx => (tm x hx).2.1)]
  rw [run_muxAnd aH eh xhi V F hEV hhV hhF hVF hEF]
  rw [run_xorAcc a F top (fun x hx => (tt x hx).2.2)]
  have aMU : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b U v) mid = accVal a b mid :=
    fun b v => accVal_write a b U v mid (fun x hx => (tm x hx).1)
  have aMV : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b V v) mid = accVal a b mid :=
    fun b v => accVal_write a b V v mid (fun x hx => (tm x hx).2.1)
  have aTU : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b U v) top = accVal a b top :=
    fun b v => accVal_write a b U v top (fun x hx => (tt x hx).1)
  have aTV : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b V v) top = accVal a b top :=
    fun b v => accVal_write a b V v top (fun x hx => (tt x hx).2.1)
  have aTF : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b F v) top = accVal a b top :=
    fun b v => accVal_write a b F v top (fun x hx => (tt x hx).2.2)
  simp only [xw, aMU, aMV, aTU, aTV, aTF]
  simp only [writeBit, Function.update_self, Function.update_of_ne hVF.symm,
    Function.update_of_ne hUF.symm, Function.update_of_ne hhF, Function.update_of_ne hEF,
    Function.update_of_ne hEV, Function.update_of_ne hEU]
  simp only [Function.update_apply, hhU, hhV, hlU, hlV, heU, heV, hEU, hEV, hEF, hUV.symm, hVF.symm,
    hUF.symm, if_false, if_true, sU, sV, sF, Bool.false_xor, Bool.xor_false]
  exact pre_bool _ _ _ _ _ _


/-- Pair positions with their chain wires, each entry holding the prefix before and after it. -/
def tri : Wire → List Nat → List ZeroBit → List (Nat × Wire × Wire)
  | p, i :: l, b :: bs => (i, p, b.work) :: tri b.work l bs
  | _, _, _ => []

theorem chain_fill (mt : Nat → Bool) (c : Wire) (l : List Nat) (bs : List ZeroBit) (st : BasisState)
    (e : Bool) (hlen : l.length = bs.length)
    (hnd : (c :: bs.flatMap ZeroBit.wires).Nodup)
    (hz : ∀ b ∈ bs, st b.work = false) (hc : st c = e)
    (hmt : ∀ k (hk : k < l.length), mt l[k] = !st (bs[k]'(hlen ▸ hk)).input) :
    Chain (fill c bs st) mt e (tri c l bs) := by
  induction l generalizing c bs st e with
  | nil => cases bs with
    | nil => trivial
    | cons _ _ => simp at hlen
  | cons i l ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hnames : (c :: b.input :: b.work :: bs.flatMap ZeroBit.wires).Nodup := hnd
      have hni := hnames
      simp only [List.nodup_cons, List.mem_cons, not_or] at hni
      obtain ⟨⟨hci, hcw, hcR⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
      have hlen' : l.length = bs.length := by simpa using hlen
      have hm0 : mt i = !st b.input := hmt 0 (by simp)
      have hwk (d : ZeroBit) (hd : d ∈ bs) (w : Wire) (hw : w = c ∨ w = b.work) : d.work ≠ w := by
        have dm : d.work ∈ bs.flatMap ZeroBit.wires :=
          List.mem_flatMap.mpr ⟨d, hd, by simp [ZeroBit.wires]⟩
        rcases hw with e' | e' <;> intro he <;> subst e'
        · exact hcR (he ▸ dm)
        · exact hwR (he ▸ dm)
      have hin (d : ZeroBit) (hd : d ∈ bs) : d.input ≠ b.work ∧ d.work ≠ b.work := by
        constructor <;> intro he <;> apply hwR <;>
          apply List.mem_flatMap.mpr <;> refine ⟨d, hd, ?_⟩ <;> simp [ZeroBit.wires, he]
      let st' := writeBit st b.work (st b.work ^^ (st c && !st b.input))
      have hb : st' b.work = (e && mt i) := by
        simp [st', writeBit, hz b (by simp), hc, hm0]
      have hcc : st' c = st c := by simp [st', writeBit, hcw]
      simp only [tri, fill]
      refine ⟨?_, ?_, ?_⟩
      · rw [fill_outside _ _ _ _ (fun d hd => hwk d hd c (Or.inl rfl))]
        exact hcc.trans hc
      · rw [fill_outside _ _ _ _ (fun d hd => hwk d hd b.work (Or.inr rfl))]; exact hb
      · apply ih b.work bs st' _ hlen' (List.nodup_cons.mpr ⟨hwR, hR⟩)
        · intro d hd
          have := hz d (by simp [hd])
          simp [st', writeBit, (hin d hd).2, this]
        · exact hb
        · intro k hk
          have h1 := hmt (k+1) (by simpa using hk)
          simp only [List.getElem_cons_succ] at h1
          rw [h1]
          have hne := (hin bs[k] (List.getElem_mem _)).1
          simp [st', writeBit, hne]

/-- End wire of a segment. -/
def endW : Wire → List (Nat × Wire × Wire) → Wire
  | p, [] => p
  | _, (_, _, c) :: r => endW c r

theorem chain_append (st : BasisState) (mt : Nat → Bool) (e : Bool)
    (A B : List (Nat × Wire × Wire)) (h : Chain st mt e (A ++ B)) :
    Chain st mt e A ∧ Chain st mt (e && (A.map (·.1)).all mt) B := by
  induction A generalizing e with
  | nil => simpa [Chain] using h
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    obtain ⟨h1, h2, h3⟩ := h
    have := ih _ h3
    refine ⟨⟨h1, h2, this.1⟩, ?_⟩
    simpa [Bool.and_assoc] using this.2

theorem chain_end (st : BasisState) (mt : Nat → Bool) (e : Bool) (p : Wire)
    (A : List (Nat × Wire × Wire)) (h : Chain st mt e A) (hp : st p = e) :
    st (endW p A) = (e && (A.map (·.1)).all mt) := by
  induction A generalizing e p with
  | nil => simp [endW, hp]
  | cons x r ih =>
    obtain ⟨i, q, c⟩ := x
    obtain ⟨h1, h2, h3⟩ := h
    simp only [endW, List.map_cons, List.all_cons]
    rw [ih _ _ h3 h2]
    simp [Bool.and_assoc]


open PrefixCompare InputSentinel.Tri in
/-- `pre` leaves the comparison with `A` in `F`, given the chain wires and pivots. -/
theorem F_value (tr : InputSentinel.Tri) (v : tr.Valid) (hne : tr.r1 ≠ tr.r2) (x : Nat)
    (hx : x < 2^256) (one U V F xhi xlo : Wire)
    (Tt Tm Tl : List (Nat × Wire × Wire))
    (hmt : Tt.map (·.1) = tr.topL) (hmm : Tm.map (·.1) = tr.midL) (hml : Tl.map (·.1) = tr.lowL)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : endW (endW one Tt) Tm ≠ U) (heV : endW (endW one Tt) Tm ≠ V)
    (heF : endW (endW one Tt) Tm ≠ F)
    (hEU : endW one Tt ≠ U) (hEV : endW one Tt ≠ V) (hEF : endW one Tt ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ Tt ++ Tm ++ Tl, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false)
    (hone : s.basis one = false)
    (hxh : s.basis xhi = x.testBit tr.hi) (hxl : s.basis xlo = x.testBit tr.lo)
    (hc : Chain (writeBit s.basis one true)
      (fun i => x.testBit i == tr.tgt i (x.testBit tr.r1, x.testBit tr.r2)) true (Tt ++ (Tm ++ Tl))) :
    (run (pre tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F xlo xhi
      (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl) [] s).basis F = decide (tr.A < x) := by
  have base := pre_F tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F xlo xhi
    (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF
    hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  simp only [hone, Bool.not_false] at base
  rw [base, ← formula_compare v hne x hx]
  set st := writeBit s.basis one true with hst
  set mt := fun i => x.testBit i == tr.tgt i (x.testBit tr.r1, x.testBit tr.r2) with hmtd
  obtain ⟨cT, cR⟩ := chain_append st mt true Tt _ hc
  obtain ⟨cM, cL⟩ := chain_append st mt _ Tm Tl cR
  have s1 : st one = true := by simp [hst, writeBit]
  have eE := chain_end st mt true one Tt cT s1
  have eL := chain_end st mt _ _ Tm cM eE
  have sh : st xhi = x.testBit tr.hi := by simp [hst, writeBit, hho, hxh]
  have sl : st xlo = x.testBit tr.lo := by simp [hst, writeBit, hlo, hxl]
  rw [accVal_chain _ _ mt _ _ cT, accVal_chain _ _ mt _ _ cM, accVal_chain _ _ mt _ _ cL]
  simp only [formula, hmt, hmm, hml, sh, sl, eE, eL, Bool.true_and]
  generalize xorForm tr.A mt (tr.topL.all mt && tr.midL.all mt) tr.lowL = q3
  generalize xorForm tr.A mt (tr.topL.all mt) tr.midL = q2
  generalize xorForm tr.A mt true tr.topL = q1
  generalize tr.topL.all mt = q4
  generalize tr.midL.all mt = q5
  generalize x.testBit tr.hi = q6
  generalize x.testBit tr.lo = q7
  generalize tr.A.testBit tr.hi = q8
  generalize tr.A.testBit tr.lo = q9
  cases q1 <;> cases q2 <;> cases q3 <;> cases q4 <;> cases q5 <;> cases q6 <;> cases q7 <;>
    cases q8 <;> cases q9 <;> rfl

section Shape
open InputSentinel ParityEven

theorem lastWire_mem (c : Wire) (bs : List ZeroBit) :
    lastWire c bs = c ∨ ∃ b ∈ bs, lastWire c bs = b.work := by
  induction bs generalizing c with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    rcases ih b.work with e | ⟨d, hd, e⟩
    · exact Or.inr ⟨b, by simp, e⟩
    · exact Or.inr ⟨d, by simp [hd], e⟩

theorem fill_last (c : Wire) (bs : List ZeroBit) (st : BasisState)
    (hnd : (c :: bs.flatMap ZeroBit.wires).Nodup) (hz : ∀ b ∈ bs, st b.work = false) :
    fill c bs st (lastWire c bs) = (st c && bs.all (fun b => !st b.input)) := by
  induction bs generalizing c st with
  | nil => simp [fill, lastWire]
  | cons b bs ih =>
    have hnames : (c :: b.input :: b.work :: bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    obtain ⟨⟨hci, hcw, hcR⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
    have hchild : (b.work :: bs.flatMap ZeroBit.wires).Nodup := List.nodup_cons.mpr ⟨hwR, hR⟩
    have htail (d : ZeroBit) (hd : d ∈ bs) : d.work ≠ b.work ∧ d.input ≠ b.work := by
      constructor <;> intro he <;> apply hwR <;>
        apply List.mem_flatMap.mpr <;> refine ⟨d, hd, ?_⟩ <;> simp [ZeroBit.wires, he]
    simp only [fill, lastWire]
    rw [ih b.work _ hchild (by
      intro d hd
      simp [writeBit, (htail d hd).1, hz d (by simp [hd])])]
    have e1 : ∀ d ∈ bs, (!writeBit st b.work (st b.work ^^ (st c && !st b.input)) d.input) = !st d.input := by
      intro d hd; simp [writeBit, (htail d hd).2]
    have e2 : bs.all (fun d => !writeBit st b.work (st b.work ^^ (st c && !st b.input)) d.input) =
        bs.all (fun d => !st d.input) := by
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      exact forall₂_congr (fun d hd => by rw [e1 d hd])
    rw [e2]
    simp [writeBit, hz b (by simp), List.all_cons, Bool.and_assoc]

theorem chain_congr (st st' : BasisState) (mt : Nat → Bool) (e : Bool)
    (T : List (Nat × Wire × Wire)) (h : ∀ x ∈ T, st x.2.1 = st' x.2.1 ∧ st x.2.2 = st' x.2.2)
    (c : Chain st mt e T) : Chain st' mt e T := by
  induction T generalizing e with
  | nil => trivial
  | cons x r ih =>
    obtain ⟨i, p, q⟩ := x
    obtain ⟨c1, c2, c3⟩ := c
    have hx := h (i, p, q) (by simp)
    exact ⟨hx.1 ▸ c1, hx.2 ▸ c2, ih _ (fun y hy => h y (by simp [hy])) c3⟩

theorem endW_mem (p : Wire) (T : List (Nat × Wire × Wire)) :
    endW p T = p ∨ ∃ x ∈ T, endW p T = x.2.2 := by
  induction T generalizing p with
  | nil => exact Or.inl rfl
  | cons x r ih =>
    obtain ⟨i, q, c⟩ := x
    rcases ih c with e | ⟨y, hy, e⟩
    · exact Or.inr ⟨(i, q, c), by simp, e⟩
    · exact Or.inr ⟨y, by simp [hy], e⟩

theorem wrap_run (R Xg suf Z : Program) (hR : measurementCount R = 0) (hX : measurementCount Xg = 0)
    (m : List Bool) (s : State) :
    run (R ++ (Xg ++ (Z ++ suf))) m s =
      run suf (m.drop (measurementCount Z)) (run Z m (run Xg [] (run R [] s))) := by
  rw [run_append, hR, List.drop_zero, List.take_zero, run_append, hX, List.drop_zero, List.take_zero,
    run_append, run_take]

/-- The chain state inside the classifier, with the effect of an appended program. -/
theorem shape_state (tr : Tri) (v : tr.Valid) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t : Wire)
    (w : Nat → Wire) (i0 : Nat) (it : List Nat) (work : List Wire)
    (hPn : ((i0 :: it).map w).Nodup) (x1P : xr1 ∉ (i0 :: it).map w) (x2P : xr2 ∉ (i0 :: it).map w)
    (hused : [xr1, xr2, y0, c, f, g, g1, wB, t].Nodup)
    (hextP : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w)
    (hwl : (it.map w).length = work.length) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, g1, wB, t])
    (s : State)
    (hg : s.basis g = false)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) &&
      decide ((s.basis xr1, s.basis xr2) = tr.pat tr.S))) :
    ∃ B s2 : State,
      s2.phase = s.phase ∧ (∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q) ∧
      s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) ∧
      (∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2))) ∧
      (∀ q, q ≠ f → q ≠ g → B.basis q = fill (w i0) (zeroPorts (it.map w) work) s2.basis q) ∧
      B.phase = s.phase ∧ B.basis f = false ∧
      (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup ∧
      (∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false) ∧
      B.basis g = (s.basis g ^^ genOut tr yb
        ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2))
        (s.basis xr1) (s.basis xr2) (s.basis y0) (s.basis c) (s.basis f)) ∧
      ∀ (E : Program) (pk : Wire) (val : Bool), (∀ m', run E m' B = put B pk val) →
        pk ∉ (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires) →
        pk ∉ wires ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)) → ∀ m,
        run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
          (zeroWith (fun h => tail tr yb xr1 xr2 y0 c f g g1 wB t h ++ E) (w i0) (zeroPorts (it.map w) work) ++
          ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s =
        put (run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
          (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) (zeroPorts (it.map w) work) ++
          ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s) pk val := by
  have hlw : (i0 :: it).map w = w i0 :: it.map w := rfl
  have p0l : w i0 ∈ (i0 :: it).map w := by simp
  have usedNotP : ∀ q ∈ [xr1, xr2, y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | hq
    · exact x1P
    · exact x2P
    · exact hextP q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have itNe : ∀ i ∈ it, w i ≠ w i0 := by
    intro i hi e
    rw [hlw] at hPn
    exact (List.nodup_cons.mp hPn).1 (e ▸ List.mem_map_of_mem hi)
  have R1 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P [] s
  generalize hs1 : run (tr.remapList xr1 xr2 w (i0 :: it)) [] s = s1 at R1
  have e2 : run [Instr.X (w i0)] [] s1 = ⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ := by
    simp [run]
  generalize hs2 : (⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ : State) = s2 at e2
  have s2ph : s2.phase = s.phase := by rw [← hs2]; exact R1.1
  have s2out : ∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q := by
    intro q hq
    have hq0 : q ≠ w i0 := fun e => hq (e ▸ p0l)
    rw [← hs2]; simp [writeBit, Function.update, hq0, R1.2.1 q hq]
  have s2p0 : s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) := by
    rw [← hs2]; simp only [writeBit, Function.update_self]
    rw [R1.2.2 i0 (by simp)]
    cases s.basis (w i0) <;> cases tr.tgt i0 (s.basis xr1, s.basis xr2) <;> rfl
  have s2it : ∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2)) := by
    intro i hi
    rw [← hs2]; simp only [writeBit]
    rw [Function.update_of_ne (itNe i hi), R1.2.2 i (by simp [hi])]
  have k1 : s2.basis xr1 = s.basis xr1 := s2out xr1 x1P
  have k2 : s2.basis xr2 = s.basis xr2 := s2out xr2 x2P
  have zp := zeroPorts_maps (it.map w) work hwl
  have huV : (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    have hall : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
        it.all (fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
      have : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
          ((zeroPorts (it.map w) work).map ZeroBit.input).all (fun q => !s2.basis q) := by
        rw [List.all_map]; rfl
      rw [this, zp.1, List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      apply forall₂_congr
      intro i hi
      simp only [Function.comp_apply, s2it i hi]
      cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> simp
    rw [hall, s2p0]
    simp [List.all_cons]
  have hcu : w i0 ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := fun h => usedNotP _ h p0l
  have hperm := zeroPorts_perm (it.map w) work hwl
  have hnd : (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp (hperm.mem_iff.mp hm) with h | h
      · obtain ⟨i, hi, e⟩ := List.mem_map.mp h
        exact itNe i hi e
      · exact (hdisj _ h).1 p0l
    · apply hperm.symm.nodup_iff.mp
      apply List.nodup_append.mpr
      refine ⟨(List.nodup_cons.mp (hlw ▸ hPn)).2, hwn, ?_⟩
      intro a ha b hb e
      subst e
      exact (hdisj a hb).1 (by rw [hlw]; exact List.mem_cons_of_mem _ ha)
  have hdis' : ∀ b ∈ zeroPorts (it.map w) work, b.input ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := by
    intro b hb
    have hin : b.input ∈ it.map w := by
      have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    exact ⟨fun h => usedNotP _ h (by rw [hlw]; exact List.mem_cons_of_mem _ hin), (hdisj _ hwk).2⟩
  have hz3 : ∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false := by
    intro b hb
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    rw [s2out _ (hdisj _ hwk).1]; exact hz.1 _ hwk
  set bs := zeroPorts (it.map w) work with hbs
  set V := (i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2) with hV
  set last := lastWire (w i0) bs with hlast
  set st := fill (w i0) bs s2.basis with hst
  have lastU : last ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := by
    rcases lastWire_mem (w i0) bs with e | ⟨b, hb, e⟩
    · rw [hlast, e]; exact hcu
    · rw [hlast, e]; exact (hdis' b hb).2
  have stU : ∀ q ∈ [xr1, xr2, y0, c, f, g, g1, wB, t], st q = s.basis q := by
    intro q hq
    rw [hst, fill_outside (w i0) bs _ q (fun b hb e => (hdis' b hb).2 (e ▸ hq)), s2out q (usedNotP q hq)]
  have stL : st last = V := by
    rw [hst, hlast, fill_last (w i0) bs _ hnd hz3, huV]
  have hnd10 : [last, xr1, xr2, y0, c, f, g, g1, wB, t].Nodup := List.nodup_cons.mpr ⟨lastU, hused⟩
  have hfg : f ≠ g := by intro e; rw [e] at hused; simp at hused
  let B : State := ⟨s2.phase, writeBit (writeBit st f false) g (st g ^^
    genOut tr yb (st last) (st xr1) (st xr2) (st y0) (st c) (st f))⟩
  have hB : ∀ m', run (tail tr yb xr1 xr2 y0 c f g g1 wB t last) m' ⟨s2.phase, st⟩ = B := by
    intro m'
    exact tail_run tr v yb last xr1 xr2 y0 c f g g1 wB t hnd10 ⟨s2.phase, st⟩ m'
      (by rw [show (⟨s2.phase, st⟩ : State).basis g = st g from rfl, stU g (by simp)]; exact hg)
      (by
        refine ⟨?_, ?_, ?_⟩
        · rw [show (⟨s2.phase, st⟩ : State).basis g1 = st g1 from rfl, stU g1 (by simp)]; exact hz.2.1
        · rw [show (⟨s2.phase, st⟩ : State).basis wB = st wB from rfl, stU wB (by simp)]; exact hz.2.2.1
        · rw [show (⟨s2.phase, st⟩ : State).basis t = st t from rfl, stU t (by simp)]; exact hz.2.2.2)
      (by
        show st f = !(st last && decide ((st xr1, st xr2) = tr.pat tr.S))
        rw [stL, stU f (by simp), stU xr1 (by simp), stU xr2 (by simp)]; exact hf)
  have Boff : ∀ q, q ≠ f → q ≠ g → B.basis q = st q := by
    intro q h1 h2
    simp [B, writeBit, h1, h2]
  have Bf : B.basis f = false := by simp [B, writeBit, hfg]
  refine ⟨B, s2, s2ph, s2out, s2p0, s2it, Boff, s2ph, Bf, hnd, hz3, ?_, ?_⟩
  · show writeBit (writeBit st f false) g _ g = _
    simp only [writeBit, Function.update_self]
    rw [stL, stU g (by simp), stU xr1 (by simp), stU xr2 (by simp), stU y0 (by simp), stU c (by simp),
      stU f (by simp)]
  · intro E pk val hE hpk hsuf m
    have hkeep : ∀ q ∈ w i0 :: bs.flatMap ZeroBit.wires, B.basis q = st q := by
      intro q hq
      have hqu : q ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := by
        rcases List.mem_cons.mp hq with e | h
        · rw [e]; exact hcu
        · obtain ⟨b, hb, hw⟩ := List.mem_flatMap.mp h
          simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with e | e
          · rw [e]; exact (hdis' b hb).1
          · rw [e]; exact (hdis' b hb).2
      exact Boff q (fun e => hqu (by simp [e])) (fun e => hqu (by simp [e]))
    have Z := zeroWith_extract (tail tr yb xr1 xr2 y0 c f g g1 wB t) E (w i0) bs hnd s2 m hz3 B hB hkeep
      pk val hE hpk
    have mR : measurementCount (tr.remapList xr1 xr2 w (i0 :: it)) = 0 := remapList_mc _ _ _ _ _
    have mX : measurementCount [Instr.X (w i0)] = 0 := rfl
    have mS : measurementCount ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)) = 0 := by
      rw [measurementCount_append, mX, mR]
    rw [wrap_run _ _ _ _ mR mX, wrap_run _ _ _ _ mR mX, hs1, e2]
    change run (zeroWith (fun h => tail tr yb xr1 xr2 y0 c f g g1 wB t h ++ E) (w i0) bs) m s2 =
      put (run (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) bs) m s2) pk val at Z
    rw [Z, run_no_measure _ mS (List.drop _ m), run_no_measure _ mS (List.drop _ m), run_put _ _ _ _ _ hsuf]

/-- A wire outside the triples and the named ports is outside `pre`. -/
theorem xorAcc_not (a : Nat) (acc q : Wire) (T : List (Nat × Wire × Wire)) (h1 : q ≠ acc)
    (h2 : ∀ x ∈ T, q ≠ x.2.1 ∧ q ≠ x.2.2) : q ∉ wires (xorAcc a acc T) := by
  induction T with
  | nil => simp [xorAcc, wires]
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    have hx := h2 (i, p, c) (by simp)
    have hr := ih (fun y hy => h2 y (by simp [hy]))
    simp only [xorAcc, wires_append, Finset.mem_union, not_or]
    refine ⟨?_, hr⟩
    split_ifs
    · simp [wires]
    · simp [wires, Instr.wires, h1, hx.1, hx.2]

theorem xorAcc_proper (a : Nat) (acc : Wire) (T : List (Nat × Wire × Wire))
    (h : ∀ x ∈ T, x.2.1 ≠ acc ∧ x.2.2 ≠ acc) : ProperProgram (xorAcc a acc T) := by
  induction T with
  | nil => simp [xorAcc, ProperProgram]
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    have hx := h (i, p, c) (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only [xorAcc]
    rw [properProgram_append]
    refine ⟨?_, hr⟩
    split_ifs
    · simp [ProperProgram]
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hx.1
      · exact hx.2

theorem pre_proper (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hlV : xlo ≠ V) (hUV : U ≠ V) (hhF : xhi ≠ F) (hVF : V ≠ F) (heU : el ≠ U) (hEV : eh ≠ V)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F)) :
    ProperProgram (pre a aL aH one U V F xlo xhi el eh top mid low) := by
  have mt : ∀ x ∈ top, x ∈ top ++ mid ++ low := fun x h => by simp [h]
  have mm : ∀ x ∈ mid, x ∈ top ++ mid ++ low := fun x h => by simp [h]
  have ml : ∀ x ∈ low, x ∈ top ++ mid ++ low := fun x h => by simp [h]
  have mux : ∀ (b : Bool) (e x u v : Wire), e ≠ u → x ≠ v → u ≠ v → ProperProgram (muxAnd b e x u v) := by
    intro b e x u v h1 h2 h3
    cases b <;> simp [muxAnd, ProperProgram, ProperGate, h1, h2, h3]
  simp only [pre, properProgram_append]
  refine ⟨by simp [ProperProgram, ProperGate], xorAcc_proper _ _ _ (fun x h => (hT x (ml x h)).1),
    mux _ _ _ _ _ heU hlV hUV, xorAcc_proper _ _ _ (fun x h => (hT x (mm x h)).2.1),
    mux _ _ _ _ _ hEV hhF hVF, xorAcc_proper _ _ _ (fun x h => (hT x (mt x h)).2.2)⟩

theorem pre_not (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (q : Wire)
    (h : q ≠ one ∧ q ≠ U ∧ q ≠ V ∧ q ≠ F ∧ q ≠ xlo ∧ q ≠ xhi ∧ q ≠ el ∧ q ≠ eh)
    (hT : ∀ x ∈ top ++ mid ++ low, q ≠ x.2.1 ∧ q ≠ x.2.2) :
    q ∉ wires (pre a aL aH one U V F xlo xhi el eh top mid low) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have mt : ∀ x ∈ top, q ≠ x.2.1 ∧ q ≠ x.2.2 := fun x hx => hT x (by simp [hx])
  have mm : ∀ x ∈ mid, q ≠ x.2.1 ∧ q ≠ x.2.2 := fun x hx => hT x (by simp [hx])
  have ml : ∀ x ∈ low, q ≠ x.2.1 ∧ q ≠ x.2.2 := fun x hx => hT x (by simp [hx])
  have mux : ∀ (b : Bool) (e x u v : Wire), q ≠ e → q ≠ x → q ≠ u → q ≠ v →
      q ∉ wires (muxAnd b e x u v) := by
    intro b e x u v a1 a2 a3 a4
    cases b <;> simp [muxAnd, wires, Instr.wires, a1, a2, a3, a4]
  simp only [pre, wires_append, Finset.mem_union, not_or]
  exact ⟨by simp [wires, Instr.wires, h1], xorAcc_not _ _ _ _ h2 ml, mux _ _ _ _ _ h7 h5 h2 h3,
    xorAcc_not _ _ _ _ h3 mm, mux _ _ _ _ _ h8 h6 h3 h4, xorAcc_not _ _ _ _ h4 mt⟩

theorem tri_fst (c : Wire) (l : List Nat) (bs : List ZeroBit) (h : l.length = bs.length) :
    (tri c l bs).map (·.1) = l := by
  induction l generalizing c bs with
  | nil => cases bs <;> simp [tri]
  | cons i l ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [tri, List.map_cons, List.cons.injEq, true_and]
      exact ih _ _ (by simpa using h)

theorem tri_wires (c : Wire) (l : List Nat) (bs : List ZeroBit) :
    ∀ x ∈ tri c l bs, (x.2.1 = c ∨ ∃ b ∈ bs, x.2.1 = b.work) ∧ ∃ b ∈ bs, x.2.2 = b.work := by
  induction l generalizing c bs with
  | nil => cases bs <;> simp [tri]
  | cons i l ih =>
    cases bs with
    | nil => simp [tri]
    | cons b bs =>
      intro x hx
      simp only [tri, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨Or.inl rfl, b, by simp, rfl⟩
      · obtain ⟨h1, d, hd, h2⟩ := ih b.work bs x hx
        refine ⟨?_, d, by simp [hd], h2⟩
        rcases h1 with e | ⟨d', hd', e⟩
        · exact Or.inr ⟨b, by simp, e⟩
        · exact Or.inr ⟨d', by simp [hd'], e⟩

/-- The non-pivot positions, top to bottom, split at the two pivots. -/
theorem idx_cat (t : Tri) (hne : t.r1 ≠ t.r2) (h1 : t.r1 < 256) (h2 : t.r2 < 256) :
    t.idx = t.topL ++ (t.midL ++ t.lowL) := by
  have hl : t.lo < t.hi := by simp only [Tri.lo, Tri.hi]; omega
  have hh : t.hi < 256 := by simp only [Tri.hi]; omega
  have key : ∀ i, (decide (i ≠ t.r1 ∧ i ≠ t.r2) = true) ↔ (i ≠ t.hi ∧ i ≠ t.lo) := by
    intro i
    simp only [decide_eq_true_eq, Tri.hi, Tri.lo]
    omega
  have keep : ∀ l : List Nat, (∀ i ∈ l, i ≠ t.hi ∧ i ≠ t.lo) →
      l.filter (fun i => decide (i ≠ t.r1 ∧ i ≠ t.r2)) = l := by
    intro l hl'
    exact List.filter_eq_self.mpr (fun i hi => (key i).mpr (hl' i hi))
  have nh : ¬ ((fun i => decide (i ≠ t.r1 ∧ i ≠ t.r2)) t.hi = true) := fun e => ((key _).mp e).1 rfl
  have nl : ¬ ((fun i => decide (i ≠ t.r1 ∧ i ≠ t.r2)) t.lo = true) := fun e => ((key _).mp e).2 rfl
  unfold Tri.idx
  rw [Tri.range_split t.lo t.hi hl hh, List.filter_append, List.filter_append,
    List.filter_cons_of_neg (p := fun i => decide (i ≠ t.r1 ∧ i ≠ t.r2)) nh,
    List.filter_cons_of_neg (p := fun i => decide (i ≠ t.r1 ∧ i ≠ t.r2)) nl, keep _ ?_, keep _ ?_, keep _ ?_]
  · rw [List.append_assoc]; rfl
  · intro i hi
    have : i < t.lo := by simpa using hi
    omega
  · intro i hi
    have := (Tri.mem_seg _ _ _).mp hi
    omega
  · intro i hi
    have := (Tri.mem_seg _ _ _).mp hi
    omega

/-- Chain triples of the zero test. -/
def triples (xs work : List Wire) (one : Wire) : List Nat → List (Nat × Wire × Wire)
  | [] => []
  | i0 :: it => (i0, one, xs.getD i0 0) ::
      tri (xs.getD i0 0) it (zeroPorts (it.map (fun i => xs.getD i 0)) work)

/-- The extraction prefix of the classifier. -/
def preOf (tr : Tri) (xs work : List Wire) (one U V F : Wire) : Program :=
  pre tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F (xs.getD tr.lo 0) (xs.getD tr.hi 0)
    (endW (endW one ((triples xs work one tr.idx).take tr.topL.length))
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length))
    (endW one ((triples xs work one tr.idx).take tr.topL.length))
    ((triples xs work one tr.idx).take tr.topL.length)
    (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length)
    ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length))


theorem xorAcc_tc (a : Nat) (acc : Wire) (T : List (Nat × Wire × Wire)) :
    toffoliCount (xorAcc a acc T) = 0 := by
  induction T with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    simp only [xorAcc, toffoliCount_append, ih]
    split_ifs <;> simp [toffoliCount]

theorem xorAcc_slots (a : Nat) (acc : Wire) (T : List (Nat × Wire × Wire)) :
    Challenge.gateSlots (xorAcc a acc T) ≤ 2 * T.length := by
  induction T with
  | nil => simp [xorAcc, Challenge.gateSlots]
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    simp only [xorAcc, Challenge.gateSlots_append, List.length_cons]
    split_ifs <;> simp [Challenge.gateSlots, Challenge.instructionSlots] at ih ⊢ <;> omega

theorem pre_counts (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    toffoliCount (pre a aL aH one U V F xlo xhi el eh top mid low) ≤ 2 ∧
    measurementCount (pre a aL aH one U V F xlo xhi el eh top mid low) = 0 ∧
    Challenge.gateSlots (pre a aL aH one U V F xlo xhi el eh top mid low) ≤
      2 * (top.length + mid.length + low.length) + 9 := by
  have mt : ∀ (b : Bool) (e x u v : Wire), toffoliCount (muxAnd b e x u v) = 1 := by
    intro b e x u v; cases b <;> simp [muxAnd, toffoliCount]
  have ms : ∀ (b : Bool) (e x u v : Wire), Challenge.gateSlots (muxAnd b e x u v) ≤ 4 := by
    intro b e x u v
    cases b <;> simp [muxAnd, Challenge.gateSlots, Challenge.instructionSlots]
  have s1 := xorAcc_slots a U low
  have s2 := xorAcc_slots a V mid
  have s3 := xorAcc_slots a F top
  have l1 := ms aL el xlo U V
  have l2 := ms aH eh xhi V F
  have t1 := mt aL el xlo U V
  have t2 := mt aH eh xhi V F
  refine ⟨?_, ?_, ?_⟩
  · simp only [pre, toffoliCount_append, xorAcc_tc]
    simp only [toffoliCount]
    omega
  · simp only [pre, measurementCount_append, xorAcc_mc, muxAnd_mc]
    rfl
  · simp only [pre, Challenge.gateSlots_append]
    simp only [Challenge.gateSlots, Challenge.instructionSlots, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at s1 s2 s3 l1 l2 ⊢
    omega


end Shape
end ECDSAAdd.Entrant.ZeroFill
