import ECDSAAdd.Submission.Entrant.FrontierMain
import ECDSAAdd.Submission.Entrant.Terminal23Core

-- Adapted public 3aa2d8a9 phase-erasure primitives; exact all-record semantics.
section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd

def parityAt (basis : BasisState) : List Wire → Bool
  | [] => false
  | w :: ws => basis w ^^ parityAt basis ws

theorem correctZs (ws : List Wire) (s : State) :
    correct (ws.map Correction.Z) s = ⟨s.phase ^^ parityAt s.basis ws, s.basis⟩ := by
  induction ws generalizing s with
  | nil => simp [correct, parityAt]
  | cons w ws ih =>
    simp only [List.map_cons, correct, ih, parityAt]
    congr 1
    exact Bool.xor_assoc _ _ _

theorem parityAt_update (basis : BasisState) (t : Wire) (ws : List Wire)
    (h : ∀ w ∈ ws, w ≠ t) : parityAt (writeBit basis t false) ws = parityAt basis ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [parityAt]
    rw [show writeBit basis t false w = basis w by simpa [writeBit] using (Function.update_of_ne (h w (by simp)) false basis)]
    rw [ih (fun w hw => h w (by simp [hw]))]

theorem eraseLinear (ws : List Wire) (t : Wire) (s : State) (m : List Bool)
    (h : ∀ w ∈ ws, w ≠ t) (hv : s.basis t = parityAt s.basis ws) :
    run [.measureX t [] (ws.map Correction.Z)] m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  cases hm : m.headD false
  · simp only [run, measureAndCorrect, hm, Bool.false_eq_true, if_false, correct, Bool.false_and, Bool.xor_false]
  · simp only [run, measureAndCorrect, hm, if_true, Bool.true_and, correctZs]
    rw [parityAt_update _ _ _ h, hv]
    simp
theorem eraseTwoProductsLinear (a b c d t : Wire) (ws : List Wire)
    (ha : a ≠ t) (hb : b ≠ t) (hc : c ≠ t) (hd : d ≠ t)
    (h : ∀ w ∈ ws, w ≠ t) (s : State) (m : List Bool)
    (hv : s.basis t = ((s.basis a && s.basis b) ^^ (s.basis c && s.basis d) ^^ parityAt s.basis ws)) :
    run [.measureX t [] ([.CZ a b, .CZ c d] ++ ws.map Correction.Z)] m s =
      ⟨s.phase, writeBit s.basis t false⟩ := by
  cases hm : m.headD false
  · simp only [run, measureAndCorrect, hm, Bool.false_eq_true, if_false, correct, Bool.false_and, Bool.xor_false]
  · simp only [run, measureAndCorrect, hm, if_true, Bool.true_and, List.cons_append, correct,
      writeBit, Function.update_of_ne ha, Function.update_of_ne hb, Function.update_of_ne hc,
      Function.update_of_ne hd, correctZs]
    simp only [List.nil_append, correctZs]
    have hp := parityAt_update s.basis t ws h
    simp only [writeBit] at hp
    rw [hp, hv]
    cases s.phase <;> cases s.basis a <;> cases s.basis b <;> cases s.basis c <;> cases s.basis d <;> cases parityAt s.basis ws <;> simp_all

theorem eraseOneProductLinear (a b t : Wire) (ws : List Wire)
    (ha : a ≠ t) (hb : b ≠ t) (h : ∀ w ∈ ws, w ≠ t) (s : State) (m : List Bool)
    (hv : s.basis t = ((s.basis a && s.basis b) ^^ parityAt s.basis ws)) :
    run [.measureX t [] ([.CZ a b] ++ ws.map Correction.Z)] m s =
      ⟨s.phase, writeBit s.basis t false⟩ := by
  cases hm : m.headD false
  · simp only [run, measureAndCorrect, hm, Bool.false_eq_true, if_false, correct, Bool.false_and, Bool.xor_false]
  · simp only [run, measureAndCorrect, hm, if_true, Bool.true_and, List.cons_append, correct,
      writeBit, Function.update_of_ne ha, Function.update_of_ne hb]
    simp only [List.nil_append, correctZs]
    have hp := parityAt_update s.basis t ws h
    simp only [writeBit] at hp
    rw [hp, hv]
    cases s.phase <;> cases s.basis a <;> cases s.basis b <;> cases parityAt s.basis ws <;> simp_all

def compareCorrections (bit : Bool) (x v e : Wire) (ws : List Wire) : List Correction :=
  (if bit then [.CZ x v] else [.CZ x v, .CZ e x, .Z v]) ++ ws.map Correction.Z

theorem eraseCompareAccumulator (bit : Bool) (x v e t : Wire) (ws : List Wire)
    (hx : x ≠ t) (hv : v ≠ t) (he : e ≠ t) (h : ∀ w ∈ ws, w ≠ t)
    (s : State) (m : List Bool)
    (ht : s.basis t = (((s.basis x == bit) && s.basis v) ^^ parityAt s.basis ws ^^
      (s.basis e && (s.basis x && !bit)))) :
    run [.measureX t [] (compareCorrections bit x v e ws)] m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  cases bit
  · have hws : ∀ w ∈ v::ws, w ≠ t := by simpa using And.intro hv h
    have ht' : s.basis t = ((s.basis x && s.basis v) ^^ (s.basis e && s.basis x) ^^ parityAt s.basis (v::ws)) := by
      simp only [parityAt]
      rw [ht]
      cases s.basis x <;> cases s.basis v <;> cases s.basis e <;> cases parityAt s.basis ws <;> simp_all
    simpa [compareCorrections] using eraseTwoProductsLinear x v e x t (v::ws) hx hv he hx hws s m ht'
  · have ht' : s.basis t = ((s.basis x && s.basis v) ^^ parityAt s.basis ws) := by
      rw [ht]
      cases s.basis x <;> cases s.basis v <;> cases s.basis e <;> cases parityAt s.basis ws <;> simp_all
    simpa [compareCorrections] using eraseOneProductLinear x v t ws hx hv h s m ht'

end ECDSAAdd
end


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
def boundsOpt : Challenge.Bounds := ⟨2150254,1498370,1587,50251236⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150254 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150260 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150254
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
def boundsOpt : Challenge.Bounds := ⟨2150253,1498370,1587,50251248⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150253 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150260 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150253
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

/-- Measured F cleanup adapted from published 681ebd80; the current MUX prefix is retained. -/
def mxPreV (a : Nat) (aL : Bool) (one U V xlo el : Wire) (mid low : List (Nat × Wire × Wire)) :
    Program :=
  [.X one] ++ (xorAcc a U low ++ (muxAnd aL el xlo U V ++ xorAcc a V mid))

def mxPartF (a : Nat) (aH : Bool) (V F xhi eh : Wire) (top : List (Nat × Wire × Wire)) : Program :=
  muxAnd aH eh xhi V F ++ xorAcc a F top

theorem mx_pre_split (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    pre a aL aH one U V F xlo xhi el eh top mid low =
      mxPreV a aL one U V xlo el mid low ++ mxPartF a aH V F xhi eh top := by
  simp only [pre, mxPreV, mxPartF, List.append_assoc]

def mxVal (a : Nat) (aH : Bool) (V xhi eh : Wire) (top : List (Nat × Wire × Wire))
    (b : BasisState) : Bool :=
  ((b xhi == aH) && b V) ^^ accVal a b top ^^ (b eh && (b xhi && !aH))

theorem mx_partF_run (a : Nat) (aH : Bool) (V F xhi eh : Wire) (top : List (Nat × Wire × Wire))
    (heV : eh ≠ V) (hxV : xhi ≠ V) (hxF : xhi ≠ F) (hVF : V ≠ F) (heF : eh ≠ F)
    (hT : ∀ x ∈ top, x.2.1 ≠ F ∧ x.2.2 ≠ F) (s : State) (m : List Bool) :
    run (mxPartF a aH V F xhi eh top) m s =
      ⟨s.phase, writeBit s.basis F (s.basis F ^^ mxVal a aH V xhi eh top s.basis)⟩ := by
  have aT : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b F v) top = accVal a b top :=
    fun b v => accVal_write a b F v top hT
  simp only [writeBit] at aT
  rw [mxPartF, run_cat _ _ (muxAnd_mc ..), run_muxAnd aH eh xhi V F heV hxV hxF hVF heF,
    run_xorAcc a F top hT]
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq : q = F
    · subst q
      simp only [xw, writeBit, Function.update_self, mxVal, aT]
      simp only [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
    · simp only [xw, writeBit, Function.update_of_ne hq]

def mxZ (a : Nat) : List (Nat × Wire × Wire) → List Correction
  | [] => []
  | (i, p, c) :: r => (if a.testBit i then [] else [.Z p, .Z c]) ++ mxZ a r

def mxCorr (a : Nat) (aH : Bool) (V xhi eh : Wire) (top : List (Nat × Wire × Wire)) :
    List Correction :=
  (if aH then [.CZ xhi V] else [.Z V, .CZ xhi V, .CZ eh xhi]) ++ mxZ a top

theorem mx_correct_cat (c d : List Correction) (s : State) :
    correct (c ++ d) s = correct d (correct c s) := by
  induction c generalizing s with
  | nil => rfl
  | cons x c ih => cases x <;> simp only [List.cons_append, correct, ih]

theorem mx_correct_z (a : Nat) (T : List (Nat × Wire × Wire)) (s : State) :
    correct (mxZ a T) s = ⟨s.phase ^^ accVal a s.basis T, s.basis⟩ := by
  induction T generalizing s with
  | nil => cases s; simp [mxZ, correct, accVal]
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    simp only [mxZ, accVal, mx_correct_cat]
    cases hb : a.testBit i
    · simp [correct, ih, Bool.xor_assoc]
    · simp [correct, ih]

theorem mx_erase_run (a : Nat) (aH : Bool) (V F xhi eh : Wire) (top : List (Nat × Wire × Wire))
    (hxF : xhi ≠ F) (hVF : V ≠ F) (heF : eh ≠ F) (hT : ∀ x ∈ top, x.2.1 ≠ F ∧ x.2.2 ≠ F)
    (s : State) (m : List Bool) (known : s.basis F = mxVal a aH V xhi eh top s.basis) :
    run [.measureX F [] (mxCorr a aH V xhi eh top)] m s = ⟨s.phase, writeBit s.basis F false⟩ := by
  have aT : accVal a (writeBit s.basis F false) top = accVal a s.basis top :=
    accVal_write a s.basis F false top hT
  apply State.extensionality
  · cases hm : m.headD false
    · simp only [run, measureAndCorrect, hm, Bool.false_and, Bool.false_eq_true, if_false, correct,
        Bool.xor_false]
    · simp only [run, measureAndCorrect, hm, Bool.true_and, ite_true, mxCorr, mx_correct_cat,
        mx_correct_z, correct_basis, aT]
      cases aH
      · simp only [Bool.false_eq_true, if_false, correct, writeBit, Function.update_of_ne hxF,
          Function.update_of_ne hVF, Function.update_of_ne heF]
        rw [known]
        simp only [mxVal]
        generalize s.phase = ph, s.basis xhi = x1, s.basis V = v1, s.basis eh = e1,
          accVal a s.basis top = ac
        cases ph <;> cases x1 <;> cases v1 <;> cases e1 <;> cases ac <;> rfl
      · simp only [if_true, ite_true, correct, writeBit, Function.update_of_ne hxF,
          Function.update_of_ne hVF]
        rw [known]
        simp only [mxVal]
        generalize s.phase = ph, s.basis xhi = x1, s.basis V = v1, s.basis eh = e1,
          accVal a s.basis top = ac
        cases ph <;> cases x1 <;> cases v1 <;> cases e1 <;> cases ac <;> rfl
  · simp only [run, measureAndCorrect, correct_basis]

theorem mx_accVal_congr (a : Nat) (b c : BasisState) (T : List (Nat × Wire × Wire))
    (h : ∀ y ∈ T, b y.2.1 = c y.2.1 ∧ b y.2.2 = c y.2.2) : accVal a b T = accVal a c T := by
  induction T with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨i, p, q⟩ := x
    have hx := h (i, p, q) (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only at hx
    simp only [accVal, hx.1, hx.2, hr]

theorem mx_val_congr (a : Nat) (aH : Bool) (V xhi eh : Wire) (top : List (Nat × Wire × Wire))
    (b c : BasisState) (hV : b V = c V) (hx : b xhi = c xhi) (he : b eh = c eh)
    (hT : ∀ y ∈ top, b y.2.1 = c y.2.1 ∧ b y.2.2 = c y.2.2) :
    mxVal a aH V xhi eh top b = mxVal a aH V xhi eh top c := by
  simp only [mxVal, hV, hx, he, mx_accVal_congr a b c top hT]

theorem mx_preV_not (a : Nat) (aL : Bool) (one U V xlo el : Wire)
    (mid low : List (Nat × Wire × Wire)) (q : Wire)
    (h : q ≠ one ∧ q ≠ U ∧ q ≠ V ∧ q ≠ xlo ∧ q ≠ el)
    (hT : ∀ x ∈ mid ++ low, q ≠ x.2.1 ∧ q ≠ x.2.2) :
    q ∉ wires (mxPreV a aL one U V xlo el mid low) := by
  obtain ⟨h1, h2, h3, h5, h7⟩ := h
  have mm : ∀ x ∈ mid, q ≠ x.2.1 ∧ q ≠ x.2.2 := fun x hx => hT x (by simp [hx])
  have ml : ∀ x ∈ low, q ≠ x.2.1 ∧ q ≠ x.2.2 := fun x hx => hT x (by simp [hx])
  have mx : q ∉ wires (muxAnd aL el xlo U V) := by
    cases aL <;> simp [muxAnd, wires, Instr.wires, h2, h3, h5, h7]
  simp only [mxPreV, wires_append, Finset.mem_union, not_or]
  exact ⟨by simp [wires, Instr.wires, h1], xorAcc_not _ _ _ _ h2 ml, mx,
    xorAcc_not _ _ _ _ h3 mm⟩

theorem mx_cw_append (c d : List Correction) :
    correctionWires (c ++ d) = correctionWires c ∪ correctionWires d := by
  induction c with
  | nil => simp [correctionWires]
  | cons x c ih => cases x <;> simp [correctionWires, ih, Finset.union_assoc]

theorem mx_z_sub (a : Nat) (acc : Wire) (T : List (Nat × Wire × Wire)) :
    correctionWires (mxZ a T) ⊆ wires (xorAcc a acc T) := by
  induction T with
  | nil => simp [mxZ, correctionWires]
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    intro q hq
    have ih' : q ∈ correctionWires (mxZ a r) → q ∈ wires (xorAcc a acc r) := fun h => ih h
    cases hb : a.testBit i <;>
      simp [mxZ, xorAcc, hb, mx_cw_append, correctionWires, wires, Instr.wires] at hq ⊢ <;>
      tauto

theorem mx_corr_sub (a : Nat) (aH : Bool) (V F xhi eh : Wire) (top : List (Nat × Wire × Wire)) :
    correctionWires (mxCorr a aH V xhi eh top) ⊆ wires (mxPartF a aH V F xhi eh top) := by
  intro q hq
  have z : q ∈ correctionWires (mxZ a top) → q ∈ wires (xorAcc a F top) :=
    fun h => mx_z_sub a F top h
  cases aH <;> simp [mxCorr, mxPartF, mx_cw_append, correctionWires, muxAnd, wires,
    Instr.wires] at hq ⊢ <;> tauto

theorem mx_unwind (Q : Program) (hq : ProperProgram Q) (P : Wire) (hPQ : P ∉ wires Q)
    (s : State) (x : Bool) :
    run Q.reverse [] ⟨(run Q [] s).phase, writeBit (run Q [] s).basis P x⟩ =
      ⟨s.phase, writeBit s.basis P x⟩ := by
  have hback : run Q.reverse [] (run Q [] s) = s := run_reverse_proper Q hq s [] []
  have hprop : ProperProgram Q.reverse := properProgram_reverse Q hq
  have hcong := run_proper_congr Q.reverse hprop
    ⟨(run Q [] s).phase, writeBit (run Q [] s).basis P x⟩ (run Q [] s) [] [] rfl (by
      intro q hq'
      have : q ≠ P := by
        intro e; subst e; exact hPQ (by simpa [wires_reverse] using hq')
      simp [writeBit, this])
  rw [hback] at hcong
  apply State.extensionality
  · exact hcong.1
  · funext q
    by_cases hq' : q ∈ wires Q
    · have hne : q ≠ P := fun e => hPQ (e ▸ hq')
      rw [hcong.2 q (by simpa [wires_reverse] using hq')]
      simp [writeBit, hne]
    · have hq'' : q ∉ wires Q.reverse := by simpa [wires_reverse] using hq'
      rw [run_preserves_outside _ _ _ q hq'']
      by_cases hne : q = P
      · subst hne; simp [writeBit]
      · have : (run Q [] s).basis q = s.basis q := run_preserves_outside Q [] s q hq'
        simp [writeBit, hne, this]

theorem mx_sandwich (Q R : Program) (hq : ProperProgram Q) (hRm : measurementCount R = 0)
    (G F P : Wire) (E : Instr) (fv : BasisState → Bool)
    (hPQ : P ∉ wires Q) (hFQ : F ∉ wires Q) (hFP : F ≠ P)
    (hR : ∀ t : State, run R [] t = ⟨t.phase, writeBit t.basis F (t.basis F ^^ fv t.basis)⟩)
    (s : State) (hsF : s.basis F = false)
    (hE : ∀ (m' : List Bool) (t : State), t.basis F = fv (run Q [] s).basis →
      (∀ q, q ≠ P → q ≠ F → t.basis q = (run Q [] s).basis q) →
      run [E] m' t = ⟨t.phase, writeBit t.basis F false⟩)
    (m : List Bool) :
    run ((Q ++ R) ++ (.CCX G F P :: E :: Q.reverse)) m s =
      ⟨s.phase, writeBit s.basis P
        (s.basis P ^^ ((run (Q ++ R) [] s).basis G && (run (Q ++ R) [] s).basis F))⟩ := by
  have hQm : measurementCount Q = 0 := properProgram_measurementCount Q hq
  have hQRm : measurementCount (Q ++ R) = 0 := by rw [measurementCount_append, hQm, hRm]
  have hmr : measurementCount Q.reverse = 0 := by rw [measurementCount_reverse]; exact hQm
  have r1F : (run Q [] s).basis F = false := (run_preserves_outside Q [] s F hFQ).trans hsF
  have r1P : (run Q [] s).basis P = s.basis P := run_preserves_outside Q [] s P hPQ
  have hr : run (Q ++ R) [] s = ⟨(run Q [] s).phase,
      writeBit (run Q [] s).basis F ((run Q [] s).basis F ^^ fv (run Q [] s).basis)⟩ := by
    rw [run_cat Q R hQm, hR]
  have rP : (run (Q ++ R) [] s).basis P = s.basis P := by
    rw [hr]
    simp only [writeBit, Function.update_of_ne (Ne.symm hFP)]
    exact r1P
  have tF : (run [Instr.CCX G F P] [] (run (Q ++ R) [] s)).basis F = fv (run Q [] s).basis := by
    simp only [run, writeBit, Function.update_of_ne hFP]
    rw [hr]
    simp only [writeBit, Function.update_self, r1F, Bool.false_xor]
  have tO : ∀ q, q ≠ P → q ≠ F →
      (run [Instr.CCX G F P] [] (run (Q ++ R) [] s)).basis q = (run Q [] s).basis q := by
    intro q hqP hqF
    simp only [run, writeBit, Function.update_of_ne hqP]
    rw [hr]
    simp only [writeBit, Function.update_of_ne hqF]
  rw [run_cat (Q ++ R) _ hQRm]
  change run ([Instr.CCX G F P] ++ ([E] ++ Q.reverse)) m (run (Q ++ R) [] s) = _
  rw [run_cat [Instr.CCX G F P] _ rfl, run_append [E] Q.reverse, run_no_measure Q.reverse hmr,
    hE _ _ tF tO]
  have hu : (⟨(run [Instr.CCX G F P] [] (run (Q ++ R) [] s)).phase,
      writeBit (run [Instr.CCX G F P] [] (run (Q ++ R) [] s)).basis F false⟩ : State) =
      ⟨(run Q [] s).phase, writeBit (run Q [] s).basis P
        (s.basis P ^^ ((run (Q ++ R) [] s).basis G && (run (Q ++ R) [] s).basis F))⟩ := by
    apply State.extensionality
    · simp only [run]
      rw [hr]
    · funext q
      by_cases hqF : q = F
      · rw [hqF]
        simp only [writeBit, Function.update_self, Function.update_of_ne hFP, r1F]
      · by_cases hqP : q = P
        · rw [hqP]
          simp only [run, writeBit, Function.update_self, Function.update_of_ne (Ne.symm hFP), rP]
        · simp only [writeBit, Function.update_of_ne hqF, Function.update_of_ne hqP]
          exact tO q hqP hqF
  rw [hu]
  exact mx_unwind Q hq P hPQ s _

def mxPreVOf (tr : Tri) (xs work : List Wire) (one U V : Wire) : Program :=
  mxPreV tr.A (tr.A.testBit tr.lo) one U V (xs.getD tr.lo 0)
    (endW (endW one ((triples xs work one tr.idx).take tr.topL.length))
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length))
    (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length)
    ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length))

def mxPartFOf (tr : Tri) (xs work : List Wire) (one V F : Wire) : Program :=
  mxPartF tr.A (tr.A.testBit tr.hi) V F (xs.getD tr.hi 0)
    (endW one ((triples xs work one tr.idx).take tr.topL.length))
    ((triples xs work one tr.idx).take tr.topL.length)

def mxCorrOf (tr : Tri) (xs work : List Wire) (one V : Wire) : List Correction :=
  mxCorr tr.A (tr.A.testBit tr.hi) V (xs.getD tr.hi 0)
    (endW one ((triples xs work one tr.idx).take tr.topL.length))
    ((triples xs work one tr.idx).take tr.topL.length)

theorem mx_preOf_split (tr : Tri) (xs work : List Wire) (one U V F : Wire) :
    preOf tr xs work one U V F = mxPreVOf tr xs work one U V ++ mxPartFOf tr xs work one V F := by
  unfold preOf mxPreVOf mxPartFOf
  exact mx_pre_split _ _ _ _ _ _ _ _ _ _ _ _ _ _


theorem toffoli_reverse (p : Program) : toffoliCount p.reverse = toffoliCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    rw [List.reverse_cons, toffoliCount_append, ih]
    cases i <;> simp [toffoliCount]
    omega
theorem slots_reverse (p : Program) : Challenge.gateSlots p.reverse = Challenge.gateSlots p := by
  simp [Challenge.gateSlots, List.sum_reverse, List.map_reverse]
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

/- Measured F and V cleanup adapted from authenticated public 3aa2d8a9 helpers only. -/
namespace MeasuredFV
open Arithmetic

open ECDSAAdd

def correctionWires (a : Nat) : List (Nat × Wire × Wire) → List Wire
  | [] => []
  | (i,p,c)::rest => (if a.testBit i then [] else [p,c]) ++ correctionWires a rest

def parityAt (basis : BasisState) : List Wire → Bool
  | [] => false
  | w::ws => basis w ^^ parityAt basis ws

theorem correctionWires_parity (a : Nat) (basis : BasisState) (ts : List (Nat × Wire × Wire)) :
    parityAt basis (correctionWires a ts) = accVal a basis ts := by
  induction ts with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨i,p,c⟩ := v
    cases h : a.testBit i <;> simp [correctionWires, parityAt, accVal, h, ih, Bool.xor_assoc]
theorem accVal_congr_research (a : Nat) (s t : BasisState) (ts : List (Nat × Wire × Wire))
    (h : ∀ x ∈ ts, s x.2.1 = t x.2.1 ∧ s x.2.2 = t x.2.2) :
    accVal a s ts = accVal a t ts := by
  induction ts with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i,p,c⟩ := x
    have hp := h (i,p,c) (by simp)
    have hr : ∀ x ∈ xs, s x.2.1 = t x.2.1 ∧ s x.2.2 = t x.2.2 := by
      intro x hx
      exact h x (by simp [hx])
    simp only [accVal]
    rw [hp.1, hp.2, ih hr]


open Arithmetic

theorem pre_U_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let st := writeBit s.basis one (!s.basis one)
    (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis U = accVal a st low := by
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


  simp [hVF, hUV, hUF]


theorem pre_V_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let st := writeBit s.basis one (!s.basis one)
    (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis V =
      (((st xlo == aL) && accVal a st low) ^^ accVal a st mid ^^ (st el && (st xlo && !aL))) := by
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


  simp [hVF, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]


theorem pre_outside_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (q : Wire)
    (hqU : q ≠ U) (hqV : q ≠ V) (hqF : q ≠ F)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let st := writeBit s.basis one (!s.basis one)
    (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis q = st q := by
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


  simp [hVF, hqU, hqV, hqF]



open Arithmetic

theorem pre_invariants_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    t.basis F = (((t.basis xhi == aH) && t.basis V) ^^ parityAt t.basis (correctionWires a top) ^^
       (t.basis eh && (t.basis xhi && !aH))) ∧
    t.basis V = (((t.basis xlo == aL) && t.basis U) ^^ parityAt t.basis (correctionWires a mid) ^^
       (t.basis el && (t.basis xlo && !aL))) := by
  let st := writeBit s.basis one (!s.basis one)
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  have out (q : Wire) (qu : q ≠ U) (qv : q ≠ V) (qf : q ≠ F) : t.basis q = st q := by
    exact pre_outside_research a aL aH one U V F xlo xhi el eh top mid low q qu qv qf
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hu : t.basis U = accVal a st low := by
    exact pre_U_research a aL aH one U V F xlo xhi el eh top mid low
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hv : t.basis V = (((st xlo == aL) && accVal a st low) ^^ accVal a st mid ^^ (st el && (st xlo && !aL))) := by
    exact pre_V_research a aL aH one U V F xlo xhi el eh top mid low
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hf : t.basis F = (((st xhi == aH) && (((st xlo == aL) && accVal a st low) ^^ accVal a st mid ^^
    (st el && (st xlo && !aL)))) ^^ accVal a st top ^^ (st eh && (st xhi && !aH))) := by
    exact pre_F a aL aH one U V F xlo xhi el eh top mid low
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have htop : accVal a t.basis top = accVal a st top := by
    apply accVal_congr_research
    intro x hx
    have h := hT x (by simp [hx])
    exact ⟨out x.2.1 h.1.1 h.2.1.1 h.2.2.1, out x.2.2 h.1.2 h.2.1.2 h.2.2.2⟩
  have hmid : accVal a t.basis mid = accVal a st mid := by
    apply accVal_congr_research
    intro x hx
    have h := hT x (by simp [hx])
    exact ⟨out x.2.1 h.1.1 h.2.1.1 h.2.2.1, out x.2.2 h.1.2 h.2.1.2 h.2.2.2⟩
  have hh := out xhi hhU hhV hhF
  have he := out eh hEU hEV hEF
  have hl := out xlo hlU hlV hlF
  have hel := out el heU heV heF
  change t.basis F = (((t.basis xhi == aH) && t.basis V) ^^ parityAt t.basis (correctionWires a top) ^^
       (t.basis eh && (t.basis xhi && !aH))) ∧
    t.basis V = (((t.basis xlo == aL) && t.basis U) ^^ parityAt t.basis (correctionWires a mid) ^^
       (t.basis el && (t.basis xlo && !aL)))
  constructor
  · simpa only [correctionWires_parity, htop, hh, he, hv] using hf
  · simpa only [correctionWires_parity, hmid, hl, hel, hu] using hv

open Arithmetic

def clearFV (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) : Program :=
  [.measureX F [] (compareCorrections aH xhi V eh (correctionWires a top)),
   .measureX V [] (compareCorrections aL xlo U el (correctionWires a mid))]

theorem clearFV_counts (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) :
    toffoliCount (clearFV a aL aH U V F xlo xhi el eh top mid) = 0 ∧
      measurementCount (clearFV a aL aH U V F xlo xhi el eh top mid) = 2 := by
  simp [clearFV, toffoliCount, measurementCount]
theorem clearFV_correct (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) (s : State) (m : List Bool)
    (hhF : xhi ≠ F) (hVF : V ≠ F) (hEF : eh ≠ F)
    (hlV : xlo ≠ V) (hUV : U ≠ V) (heV : el ≠ V)
    (hlF : xlo ≠ F) (hUF : U ≠ F) (heF : el ≠ F)
    (htop : ∀ w ∈ correctionWires a top, w ≠ F)
    (hmidV : ∀ w ∈ correctionWires a mid, w ≠ V)
    (hmidF : ∀ w ∈ correctionWires a mid, w ≠ F)
    (hf : s.basis F = (((s.basis xhi == aH) && s.basis V) ^^
       ECDSAAdd.parityAt s.basis (correctionWires a top) ^^ (s.basis eh && (s.basis xhi && !aH))))
    (hv : s.basis V = (((s.basis xlo == aL) && s.basis U) ^^
       ECDSAAdd.parityAt s.basis (correctionWires a mid) ^^ (s.basis el && (s.basis xlo && !aL)))) :
    run (clearFV a aL aH U V F xlo xhi el eh top mid) m s =
       ⟨s.phase, writeBit (writeBit s.basis F false) V false⟩ := by
  unfold clearFV
  change run ([.measureX F [] (compareCorrections aH xhi V eh (correctionWires a top))] ++
    [.measureX V [] (compareCorrections aL xlo U el (correctionWires a mid))]) m s = _
  rw [run_append]
  rw [eraseCompareAccumulator aH xhi V eh F (correctionWires a top) hhF hVF hEF htop s _ hf]
  have hv' : (writeBit s.basis F false) V =
      ((((writeBit s.basis F false) xlo == aL) && (writeBit s.basis F false) U) ^^
      ECDSAAdd.parityAt (writeBit s.basis F false) (correctionWires a mid) ^^
      ((writeBit s.basis F false) el && ((writeBit s.basis F false) xlo && !aL))) := by
    rw [parityAt_update s.basis F (correctionWires a mid) hmidF]
    simpa [writeBit, Function.update_of_ne hVF, Function.update_of_ne hlF,
      Function.update_of_ne hUF, Function.update_of_ne heF] using hv
  exact eraseCompareAccumulator aL xlo U el V (correctionWires a mid) hlV hUV heV hmidV
    ⟨s.phase, writeBit s.basis F false⟩ _ hv'


open Arithmetic

theorem correctionWires_off_research (a : Nat) (ts : List (Nat × Wire × Wire)) (q : Wire)
    (h : ∀ x ∈ ts, x.2.1 ≠ q ∧ x.2.2 ≠ q) :
    ∀ w ∈ correctionWires a ts, w ≠ q := by
  induction ts with
  | nil => simp [correctionWires]
  | cons x xs ih =>
    obtain ⟨i,p,c⟩ := x
    have hp := h (i,p,c) (by simp)
    have hr : ∀ x ∈ xs, x.2.1 ≠ q ∧ x.2.2 ≠ q := by
      intro x hx; exact h x (by simp [hx])
    intro w hw
    cases hb : a.testBit i
    · simp [correctionWires, hb] at hw
      rcases hw with rfl | rfl | hw
      · exact hp.1
      · exact hp.2
      · exact ih hr w hw
    · simp [correctionWires, hb] at hw
      exact ih hr w hw

theorem pre_then_clearFV_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    run (pre a aL aH one U V F xlo xhi el eh top mid low ++
       clearFV a aL aH U V F xlo xhi el eh top mid) m s =
       ⟨t.phase, writeBit (writeBit t.basis F false) V false⟩ := by
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  have inv := pre_invariants_research a aL aH one U V F xlo xhi el eh top mid low
    hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have ht : ∀ w ∈ correctionWires a top, w ≠ F := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.2
  have hmv : ∀ w ∈ correctionWires a mid, w ≠ V := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.1
  have hmf : ∀ w ∈ correctionWires a mid, w ≠ F := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.2
  rw [run_cat _ _ (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.1]
  have eqParity (b : BasisState) (ws : List Wire) : parityAt b ws = ECDSAAdd.parityAt b ws := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [parityAt, ECDSAAdd.parityAt, ih]
  have invF : t.basis F = (((t.basis xhi == aH) && t.basis V) ^^ ECDSAAdd.parityAt t.basis (correctionWires a top) ^^ (t.basis eh && (t.basis xhi && !aH))) := by
    simpa only [eqParity] using inv.1
  have invV : t.basis V = (((t.basis xlo == aL) && t.basis U) ^^ ECDSAAdd.parityAt t.basis (correctionWires a mid) ^^ (t.basis el && (t.basis xlo && !aL))) := by
    simpa only [eqParity] using inv.2
  exact clearFV_correct a aL aH U V F xlo xhi el eh top mid t m
    hhF hVF hEF hlV hUV heV hlF hUF heF ht hmv hmf invF invV


open Arithmetic

theorem parityAt_updateAny_research (basis : BasisState) (t : Wire) (v : Bool) (ws : List Wire)
    (h : ∀ w ∈ ws, w ≠ t) : ECDSAAdd.parityAt (writeBit basis t v) ws = ECDSAAdd.parityAt basis ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [ECDSAAdd.parityAt]
    rw [show writeBit basis t v w = basis w by simpa [writeBit] using (Function.update_of_ne (h w (by simp)) v basis)]
    rw [ih (fun w hw => h w (by simp [hw]))]

theorem ccx_clearFV_correct (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh g pk : Wire)
    (top mid : List (Nat × Wire × Wire)) (s : State) (m : List Bool)
    (hhF : xhi ≠ F) (hVF : V ≠ F) (hEF : eh ≠ F)
    (hlV : xlo ≠ V) (hUV : U ≠ V) (heV : el ≠ V)
    (hlF : xlo ≠ F) (hUF : U ≠ F) (heF : el ≠ F)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htop : ∀ w ∈ correctionWires a top, w ≠ F)
    (hmidV : ∀ w ∈ correctionWires a mid, w ≠ V)
    (hmidF : ∀ w ∈ correctionWires a mid, w ≠ F)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (hf : s.basis F = (((s.basis xhi == aH) && s.basis V) ^^
       ECDSAAdd.parityAt s.basis (correctionWires a top) ^^ (s.basis eh && (s.basis xhi && !aH))))
    (hv : s.basis V = (((s.basis xlo == aL) && s.basis U) ^^
       ECDSAAdd.parityAt s.basis (correctionWires a mid) ^^ (s.basis el && (s.basis xlo && !aL)))) :
    run ([.CCX g F pk] ++ clearFV a aL aH U V F xlo xhi el eh top mid) m s =
      ⟨s.phase, writeBit (writeBit (writeBit s.basis pk (s.basis pk ^^ (s.basis g && s.basis F))) F false) V false⟩ := by
  let v := s.basis pk ^^ (s.basis g && s.basis F)
  let t : State := ⟨s.phase, writeBit s.basis pk v⟩
  have hf' : t.basis F = (((t.basis xhi == aH) && t.basis V) ^^
       ECDSAAdd.parityAt t.basis (correctionWires a top) ^^ (t.basis eh && (t.basis xhi && !aH))) := by
    dsimp [t]
    rw [parityAt_updateAny_research s.basis pk v (correctionWires a top) htopP]
    simpa [writeBit, Function.update_of_ne hFp, Function.update_of_ne hVp,
      Function.update_of_ne hXp, Function.update_of_ne hEp] using hf
  have hv' : t.basis V = (((t.basis xlo == aL) && t.basis U) ^^
       ECDSAAdd.parityAt t.basis (correctionWires a mid) ^^ (t.basis el && (t.basis xlo && !aL))) := by
    dsimp [t]
    rw [parityAt_updateAny_research s.basis pk v (correctionWires a mid) hmidP]
    simpa [writeBit, Function.update_of_ne hVp, Function.update_of_ne hUp,
      Function.update_of_ne hxp, Function.update_of_ne hep] using hv
  rw [run_cat _ _ rfl]
  change run (clearFV a aL aH U V F xlo xhi el eh top mid) m t = _
  exact clearFV_correct a aL aH U V F xlo xhi el eh top mid t m hhF hVF hEF
    hlV hUV heV hlF hUF heF htop hmidV hmidF hf' hv'

open Arithmetic

theorem pre_ccx_clearFV_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (g pk : Wire)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    run (pre a aL aH one U V F xlo xhi el eh top mid low ++
      ([.CCX g F pk] ++ clearFV a aL aH U V F xlo xhi el eh top mid)) m s =
      ⟨t.phase, writeBit (writeBit (writeBit t.basis pk (t.basis pk ^^ (t.basis g && t.basis F))) F false) V false⟩ := by
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  have inv := pre_invariants_research a aL aH one U V F xlo xhi el eh top mid low
    hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have ht : ∀ w ∈ correctionWires a top, w ≠ F := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.2
  have hmv : ∀ w ∈ correctionWires a mid, w ≠ V := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.1
  have hmf : ∀ w ∈ correctionWires a mid, w ≠ F := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.2
  have eqParity (b : BasisState) (ws : List Wire) : parityAt b ws = ECDSAAdd.parityAt b ws := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [parityAt, ECDSAAdd.parityAt, ih]
  have invF : t.basis F = (((t.basis xhi == aH) && t.basis V) ^^ ECDSAAdd.parityAt t.basis (correctionWires a top) ^^ (t.basis eh && (t.basis xhi && !aH))) := by
    simpa only [eqParity] using inv.1
  have invV : t.basis V = (((t.basis xlo == aL) && t.basis U) ^^ ECDSAAdd.parityAt t.basis (correctionWires a mid) ^^ (t.basis el && (t.basis xlo && !aL))) := by
    simpa only [eqParity] using inv.2
  rw [run_cat _ _ (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.1]
  exact ccx_clearFV_correct a aL aH U V F xlo xhi el eh g pk top mid t m
    hhF hVF hEF hlV hUV heV hlF hUF heF hFp hVp hUp hxp hXp hep hEp ht hmv hmf htopP hmidP invF invV

open Arithmetic

def finishUOne (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire)) : Program :=
  xorAcc a U low ++ [.X one]

theorem finishUOne_correct (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire))
    (hone : one ≠ U) (hLow : ∀ x ∈ low, x.2.1 ≠ U ∧ x.2.2 ≠ U)
    (s : State) (m : List Bool) (hU : s.basis U = accVal a s.basis low) :
    run (finishUOne a one U low) m s =
      ⟨s.phase, writeBit (writeBit s.basis U false) one (!s.basis one)⟩ := by
  unfold finishUOne
  rw [run_cat _ _ (xorAcc_mc a U low), run_xorAcc a U low hLow]
  simp [xw, run, hU, writeBit, Function.update_of_ne hone]

theorem finishUOne_counts (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire)) :
    toffoliCount (finishUOne a one U low) = 0 ∧ measurementCount (finishUOne a one U low) = 0 := by
  simp [finishUOne, toffoliCount_append, measurementCount_append, xorAcc_tc, xorAcc_mc, toffoliCount, measurementCount]

open Arithmetic

def fastExtract (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) : Program :=
  pre a aL aH one U V F xlo xhi el eh top mid low ++
    ([.CCX g F pk] ++ clearFV a aL aH U V F xlo xhi el eh top mid ++ finishUOne a one U low)

theorem fastExtract_counts (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    toffoliCount (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) ≤ 3 ∧
    measurementCount (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) = 2 := by
  have hp := pre_counts a aL aH one U V F xlo xhi el eh top mid low
  have hc := clearFV_counts a aL aH U V F xlo xhi el eh top mid
  have hf := finishUOne_counts a one U low
  simp only [fastExtract, toffoliCount_append, measurementCount_append, toffoliCount, measurementCount,
    hc.1, hc.2, hf.1, hf.2]
  omega
theorem fastExtract_post (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (g pk : Wire)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (honeP : one ≠ pk)
    (hlowP : ∀ x ∈ low, x.2.1 ≠ pk ∧ x.2.2 ≠ pk)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    let r : State := ⟨t.phase, writeBit (writeBit (writeBit t.basis pk (t.basis pk ^^ (t.basis g && t.basis F))) F false) V false⟩
    run (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) m s =
      ⟨r.phase, writeBit (writeBit r.basis U false) one (!r.basis one)⟩ := by
  let st := writeBit s.basis one (!s.basis one)
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  let r : State := ⟨t.phase, writeBit (writeBit (writeBit t.basis pk (t.basis pk ^^ (t.basis g && t.basis F))) F false) V false⟩
  have out (q : Wire) (qu : q ≠ U) (qv : q ≠ V) (qf : q ≠ F) : t.basis q = st q := by
    exact pre_outside_research a aL aH one U V F xlo xhi el eh top mid low q qu qv qf
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hu : t.basis U = accVal a st low := by
    exact pre_U_research a aL aH one U V F xlo xhi el eh top mid low
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hlow : ∀ x ∈ low, x.2.1 ≠ U ∧ x.2.2 ≠ U := by
    intro x hx
    exact (hT x (by simp [hx])).1
  have hacc : accVal a r.basis low = accVal a st low := by
    apply accVal_congr_research
    intro x hx
    have h := hT x (by simp [hx])
    have hp := hlowP x hx
    constructor
    · change writeBit (writeBit (writeBit t.basis pk _) F false) V false x.2.1 = st x.2.1
      rw [show writeBit (writeBit (writeBit t.basis pk _) F false) V false x.2.1 = t.basis x.2.1 by
        simp [writeBit, Function.update_of_ne h.2.1.1, Function.update_of_ne h.2.2.1, Function.update_of_ne hp.1]]
      exact out x.2.1 h.1.1 h.2.1.1 h.2.2.1
    · change writeBit (writeBit (writeBit t.basis pk _) F false) V false x.2.2 = st x.2.2
      rw [show writeBit (writeBit (writeBit t.basis pk _) F false) V false x.2.2 = t.basis x.2.2 by
        simp [writeBit, Function.update_of_ne h.2.1.2, Function.update_of_ne h.2.2.2, Function.update_of_ne hp.2]]
      exact out x.2.2 h.1.2 h.2.1.2 h.2.2.2
  have hrU : r.basis U = accVal a r.basis low := by
    rw [hacc, ←hu]
    simp [r, writeBit, Function.update_of_ne hUV, Function.update_of_ne hUF, Function.update_of_ne hUp]
  have hm : measurementCount (pre a aL aH one U V F xlo xhi el eh top mid low ++
      ([.CCX g F pk] ++ clearFV a aL aH U V F xlo xhi el eh top mid)) = 2 := by
    simp [measurementCount_append, (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.1,
      (clearFV_counts a aL aH U V F xlo xhi el eh top mid).2, measurementCount]
  unfold fastExtract
  rw [←List.append_assoc, run_append]
  rw [pre_ccx_clearFV_research a aL aH one U V F xlo xhi el eh top mid low g pk
    hFp hVp hUp hxp hXp hep hEp htopP hmidP hUV hUF hVF hlU hlV hlF hhU hhV hhF
    heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s _ hU hV hF]
  exact finishUOne_correct a one U low hoU hlow r _ hrU

theorem fastExtract_semantics (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (g pk : Wire)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (honeP : one ≠ pk)
    (hlowP : ∀ x ∈ low, x.2.1 ≠ pk ∧ x.2.2 ≠ pk)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    run (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) m s =
      ⟨s.phase, writeBit s.basis pk (s.basis pk ^^ (t.basis g && t.basis F))⟩ := by
  let st := writeBit s.basis one (!s.basis one)
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  let r : State := ⟨t.phase, writeBit (writeBit (writeBit t.basis pk (t.basis pk ^^ (t.basis g && t.basis F))) F false) V false⟩
  have out (q : Wire) (qu : q ≠ U) (qv : q ≠ V) (qf : q ≠ F) : t.basis q = st q := by
    exact pre_outside_research a aL aH one U V F xlo xhi el eh top mid low q qu qv qf
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hone : t.basis one = !s.basis one := by
    simpa [st, writeBit] using out one hoU hoV hoF
  have hpk : t.basis pk = s.basis pk := by
    simpa [st, writeBit, Function.update_of_ne honeP.symm] using out pk hUp.symm hVp.symm hFp.symm
  have hphase : t.phase = s.phase := by
    exact ECDSAAdd.FiniteUnitary.run_phase _
      (pre_proper a aL aH one U V F xlo xhi el eh top mid low hlV hUV hhF hVF heU hEV hT) s []
  dsimp [t] at hone hpk
  rw [fastExtract_post a aL aH one U V F xlo xhi el eh top mid low g pk
    hFp hVp hUp hxp hXp hep hEp htopP hmidP honeP hlowP hUV hUF hVF hlU hlV hlF hhU hhV hhF
    heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s m hU hV hF]
  apply State.extensionality
  · exact hphase
  · funext q
    by_cases qU : q = U
    · subst q
      simp [r, writeBit, Function.update_apply, hU, hUp, hUV, hUF, hoU, hoU.symm, hUp.symm, honeP, honeP.symm, hoV, hoF, hone]
    · by_cases qV : q = V
      · subst q
        simp [r, writeBit, Function.update_apply, hV, hVp, hUV, hVF, hoV, hoV.symm, hVp.symm, honeP, honeP.symm, hoU, hoF, hone]
      · by_cases qF : q = F
        · subst q
          simp [r, writeBit, Function.update_apply, hF, hFp, hUF, hVF, hoF, hoF.symm, hFp.symm, honeP, honeP.symm, hoU, hoV, hone]
        · by_cases qo : q = one
          · subst q
            simp [r, writeBit, Function.update_apply, hoU, hoV, hoF, honeP, honeP.symm, hUp, hVp, hFp, hone]
          · by_cases qp : q = pk
            · subst q
              simp [r, writeBit, Function.update_apply, hUp, hVp, hFp, hUp.symm, hVp.symm, hFp.symm, honeP, honeP.symm, hpk]
            · have hq := out q qU qV qF
              have hs : t.basis q = s.basis q := by simpa [st, writeBit, Function.update_of_ne qo] using hq
              dsimp [t] at hs
              simp [r, writeBit, Function.update_apply, qU, qV, qF, qo, qp, hs]

theorem fastExtract_equiv (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (g pk : Wire)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (hPw : pk ∉ wires (pre a aL aH one U V F xlo xhi el eh top mid low))
    (hGP : g ≠ pk)
    (honeP : one ≠ pk)
    (hlowP : ∀ x ∈ low, x.2.1 ≠ pk ∧ x.2.2 ≠ pk)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m mOld : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    run (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) m s =
      run (pre a aL aH one U V F xlo xhi el eh top mid low ++
        (.CCX g F pk :: (pre a aL aH one U V F xlo xhi el eh top mid low).reverse)) mOld s := by
  rw [fastExtract_semantics a aL aH one U V F xlo xhi el eh top mid low g pk
    hFp hVp hUp hxp hXp hep hEp htopP hmidP honeP hlowP hUV hUF hVF hlU hlV hlF hhU hhV hhF
    heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s m hU hV hF]
  symm
  exact sandwich _ (pre_proper a aL aH one U V F xlo xhi el eh top mid low hlV hUV hhF hVF heU hEV hT)
    g F pk hPw hGP hFp s mOld

theorem proper_gatePhysical_research (p : Program) (hp : ProperProgram p) : Arithmetic.GatePhysical p := by
  intro i hi
  have h := hp i hi
  cases i <;> simp_all [RecordedQuantum.PhysicalInstr, ProperGate]

theorem fastExtract_physical (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hPre : ProperProgram (pre a aL aH one U V F xlo xhi el eh top mid low))
    (hGP : g ≠ pk) (hFP : F ≠ pk)
    (hLow : ∀ x ∈ low, x.2.1 ≠ U ∧ x.2.2 ≠ U) :
    Arithmetic.GatePhysical (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) := by
  have hpre := proper_gatePhysical_research _ hPre
  have hl := proper_gatePhysical_research _ (xorAcc_proper a U low hLow)
  have hcc : Arithmetic.GatePhysical [.CCX g F pk] := by
    simp [Arithmetic.GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hGP, hFP]
  have hclear : Arithmetic.GatePhysical (clearFV a aL aH U V F xlo xhi el eh top mid) := by
    simp [clearFV, Arithmetic.GatePhysical, RecordedQuantum.PhysicalInstr]
  have hfin : Arithmetic.GatePhysical (finishUOne a one U low) := by
    unfold finishUOne
    rw [Arithmetic.gatePhysical_append]
    exact ⟨hl, by simp [Arithmetic.GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]⟩
  simpa only [fastExtract, Arithmetic.gatePhysical_append] using And.intro hpre (And.intro (And.intro hcc hclear) hfin)


open Arithmetic

theorem correctionWires_length_research (a : Nat) (ts : List (Nat × Wire × Wire)) :
    (correctionWires a ts).length ≤ 2 * ts.length := by
  induction ts with
  | nil => simp [correctionWires]
  | cons x xs ih =>
    obtain ⟨i,p,c⟩ := x
    cases hb : a.testBit i <;> simp [correctionWires, hb] at ih ⊢ <;> omega

theorem compareCorrections_length_research (bit : Bool) (x v e : Wire) (ws : List Wire) :
    (compareCorrections bit x v e ws).length ≤ 3 + ws.length := by
  cases bit <;> simp [compareCorrections]
  omega

theorem clearFV_slots_research (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) :
    Challenge.gateSlots (clearFV a aL aH U V F xlo xhi el eh top mid) ≤ 8 + 2 * (top.length + mid.length) := by
  have ht := correctionWires_length_research a top
  have hm := correctionWires_length_research a mid
  have hc1 := compareCorrections_length_research aH xhi V eh (correctionWires a top)
  have hc2 := compareCorrections_length_research aL xlo U el (correctionWires a mid)
  simp only [clearFV, Challenge.gateSlots, Challenge.instructionSlots, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_nil, Nat.add_zero]
  omega

theorem finishUOne_slots_research (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire)) :
    Challenge.gateSlots (finishUOne a one U low) ≤ 2 * low.length + 1 := by
  have h := xorAcc_slots a U low
  unfold finishUOne
  rw [Challenge.gateSlots_append]
  have hx : Challenge.gateSlots [.X one] = 1 := rfl
  rw [hx]
  omega

theorem fastExtract_slots_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    Challenge.gateSlots (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) ≤
      4 * (top.length + mid.length + low.length) + 19 := by
  have hp := (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.2
  have hc := clearFV_slots_research a aL aH U V F xlo xhi el eh top mid
  have hf := finishUOne_slots_research a one U low
  unfold fastExtract
  simp only [Challenge.gateSlots_append]
  have hcc : Challenge.gateSlots [.CCX g F pk] = 1 := rfl
  rw [hcc]
  omega
theorem correctionWires_in_research (a : Nat) (ts : List (Nat × Wire × Wire)) (W : Finset Wire)
    (h : ∀ x ∈ ts, x.2.1 ∈ W ∧ x.2.2 ∈ W) : ∀ w ∈ correctionWires a ts, w ∈ W := by
  induction ts with
  | nil => simp [correctionWires]
  | cons x xs ih =>
    obtain ⟨i,p,c⟩ := x
    have hp := h (i,p,c) (by simp)
    have hr : ∀ x ∈ xs, x.2.1 ∈ W ∧ x.2.2 ∈ W := by intro x hx; exact h x (by simp [hx])
    intro w hw
    cases hb : a.testBit i
    · simp [correctionWires, hb] at hw
      rcases hw with rfl | rfl | hw
      · exact hp.1
      · exact hp.2
      · exact ih hr w hw
    · simp [correctionWires, hb] at hw
      exact ih hr w hw

theorem zCorrections_sub_research (ws : List Wire) (W : Finset Wire) (h : ∀ w ∈ ws, w ∈ W) :
    ECDSAAdd.correctionWires (ws.map Correction.Z) ⊆ W := by
  induction ws with
  | nil => simp [ECDSAAdd.correctionWires]
  | cons w ws ih =>
    have hw : w ∈ W := h w (by simp)
    have hr : ∀ x ∈ ws, x ∈ W := by intro x hx; exact h x (by simp [hx])
    simp only [List.map_cons, ECDSAAdd.correctionWires, Finset.union_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hw, ih hr⟩

theorem compareCorrections_sub_research (bit : Bool) (x v e : Wire) (ws : List Wire) (W : Finset Wire)
    (hx : x ∈ W) (hv : v ∈ W) (he : e ∈ W) (hws : ∀ w ∈ ws, w ∈ W) :
    ECDSAAdd.correctionWires (compareCorrections bit x v e ws) ⊆ W := by
  have hz := zCorrections_sub_research ws W hws
  cases bit <;> simp [compareCorrections, ECDSAAdd.correctionWires, Finset.union_subset_iff,
    Finset.insert_subset_iff, hx, hv, he, hz]

theorem clearFV_sub_research (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) (W : Finset Wire)
    (hU : U ∈ W) (hV : V ∈ W) (hF : F ∈ W) (hlo : xlo ∈ W) (hhi : xhi ∈ W)
    (hel : el ∈ W) (heh : eh ∈ W)
    (htop : ∀ x ∈ top, x.2.1 ∈ W ∧ x.2.2 ∈ W) (hmid : ∀ x ∈ mid, x.2.1 ∈ W ∧ x.2.2 ∈ W) :
    wires (clearFV a aL aH U V F xlo xhi el eh top mid) ⊆ W := by
  have ht := compareCorrections_sub_research aH xhi V eh (correctionWires a top) W hhi hV heh
    (correctionWires_in_research a top W htop)
  have hm := compareCorrections_sub_research aL xlo U el (correctionWires a mid) W hlo hU hel
    (correctionWires_in_research a mid W hmid)
  simp [clearFV, wires, Instr.wires, ECDSAAdd.correctionWires, Finset.union_subset_iff,
    Finset.insert_subset_iff, hF, hV, ht, hm]

theorem xorAcc_sub_research (a : Nat) (U : Wire) (ts : List (Nat × Wire × Wire)) (W : Finset Wire)
    (hU : U ∈ W) (hT : ∀ x ∈ ts, x.2.1 ∈ W ∧ x.2.2 ∈ W) : wires (xorAcc a U ts) ⊆ W := by
  intro q hq
  apply Classical.byContradiction
  intro hn
  have qu : q ≠ U := fun e => hn (e ▸ hU)
  have ht : ∀ x ∈ ts, q ≠ x.2.1 ∧ q ≠ x.2.2 := by
    intro x hx
    exact ⟨fun e => hn (e ▸ (hT x hx).1), fun e => hn (e ▸ (hT x hx).2)⟩
  exact xorAcc_not a U q ts qu ht hq

theorem finishUOne_sub_research (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire)) (W : Finset Wire)
    (hone : one ∈ W) (hU : U ∈ W) (hlow : ∀ x ∈ low, x.2.1 ∈ W ∧ x.2.2 ∈ W) :
    wires (finishUOne a one U low) ⊆ W := by
  unfold finishUOne
  rw [wires_append]
  exact Finset.union_subset (xorAcc_sub_research a U low W hU hlow) (by simp [wires, Instr.wires, hone])


/-- A known product can be erased with its exact immediate phase correction. -/
theorem eraseKnownProduct_eq (g f pk : Wire) (gp : g ≠ pk) (fp : f ≠ pk)
    (s : State) (m : List Bool) (known : s.basis pk = (s.basis g && s.basis f)) :
    run [.measureX pk [] [.CZ g f]] m s = run [.CCX g f pk] [] s := by
  have h := ECDSAAdd.eraseOneProductLinear g f pk [] gp fp (by simp) s m
    (by simpa [ECDSAAdd.parityAt] using known)
  simp only [List.map_nil, List.append_nil] at h
  rw [h]
  simp [run, known]

/-- Output-only variant: its caller must prove that the parked bit already equals the product. -/
def outputFastExtract (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) : Program :=
  pre a aL aH one U V F xlo xhi el eh top mid low ++
    ([.measureX pk [] [.CZ g F]] ++ clearFV a aL aH U V F xlo xhi el eh top mid ++ finishUOne a one U low)

theorem outputFastExtract_equiv (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) (gp : g ≠ pk) (fp : F ≠ pk)
    (s : State) (m : List Bool)
    (known : (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis pk =
      ((run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis g &&
       (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis F)) :
    run (outputFastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) m s =
      run (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) (m.drop 1) s := by
  let P := pre a aL aH one U V F xlo xhi el eh top mid low
  let Z := clearFV a aL aH U V F xlo xhi el eh top mid ++ finishUOne a one U low
  have hm : measurementCount P = 0 := (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.1
  have eq : run (P ++ ([.measureX pk [] [.CZ g F]] ++ Z)) m s =
      run (P ++ ([.CCX g F pk] ++ Z)) (m.drop 1) s := by
    rw [run_cat P _ hm, run_cat P _ hm, run_append]
    simp only [measurementCount]
    rw [eraseKnownProduct_eq g F pk gp fp (run P [] s) (m.take 1) known, run_cat [Instr.CCX g F pk] Z rfl]
  simpa only [P, Z, outputFastExtract, fastExtract, List.append_assoc] using eq

theorem outputFastExtract_counts (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    toffoliCount (outputFastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) ≤ 2 ∧
      measurementCount (outputFastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) = 3 := by
  have hp := pre_counts a aL aH one U V F xlo xhi el eh top mid low
  have hc := clearFV_counts a aL aH U V F xlo xhi el eh top mid
  have hf := finishUOne_counts a one U low
  simp only [outputFastExtract, toffoliCount_append, measurementCount_append, toffoliCount,
    measurementCount, hc.1, hc.2, hf.1, hf.2]
  omega

theorem outputFastExtract_slots (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    Challenge.gateSlots (outputFastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) =
      Challenge.gateSlots (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) + 1 := by
  simp [outputFastExtract, fastExtract, Challenge.gateSlots_append, Challenge.gateSlots,
    Challenge.instructionSlots]
  omega

theorem outputFastExtract_wires (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    wires (outputFastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) =
      wires (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) := by
  unfold outputFastExtract fastExtract
  ext q
  simp only [wires_append, wires, Instr.wires, ECDSAAdd.correctionWires, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty, or_false]
  tauto

theorem outputFastExtract_physical (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hPre : ProperProgram (pre a aL aH one U V F xlo xhi el eh top mid low))
    (hGP : g ≠ pk) (hFP : F ≠ pk)
    (hLow : ∀ x ∈ low, x.2.1 ≠ U ∧ x.2.2 ≠ U) :
    Arithmetic.GatePhysical (outputFastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) := by
  have hp := fastExtract_physical a aL aH one U V F xlo xhi el eh g pk top mid low hPre hGP hFP hLow
  simp only [fastExtract, Arithmetic.gatePhysical_append] at hp
  unfold outputFastExtract
  simp only [Arithmetic.gatePhysical_append]
  exact ⟨hp.1, ⟨⟨by simp [Arithmetic.GatePhysical, RecordedQuantum.PhysicalInstr], hp.2.1.2⟩, hp.2.2⟩⟩

theorem xorFalse_eq (a b : Bool) (h : (a ^^ b) = false) : a = b := by
  cases a <;> cases b <;> simp_all

end MeasuredFV

/-- Coherent comparison extractor retained for source-level bisection. -/
def extractCoherent (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire) : Program :=
  preOf tr xs work one U V F ++ (.CCX g F pk :: (preOf tr xs work one U V F).reverse)

/-- Measure only F, immediately restore its quadratic phase, then unwind the F-free prefix. -/
def extractFOnly (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire) : Program :=
  preOf tr xs work one U V F ++
    (.CCX g F pk :: .measureX F [] (mxCorrOf tr xs work one V) :: (mxPreVOf tr xs work one U V).reverse)

def extract (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire) : Program :=
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  MeasuredFV.fastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl

def extractOutput (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire) : Program :=
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  MeasuredFV.outputFastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl

/-- The classifier with the comparison extracted from its chain. -/
def classifierF (tr : Tri) (yb : Bool) (xs work : List Wire) (y0 c f g g1 wB t one U V F pk : Wire) :
    Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
        extract tr xs work one U V F pk g)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

theorem remapList_not (t : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) (q : Wire)
    (h1 : q ≠ xr1) (h2 : q ≠ xr2) (h3 : q ∉ l.map w) : q ∉ wires (t.remapList xr1 xr2 w l) := by
  induction l with
  | nil => simp [Tri.remapList, wires]
  | cons i l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h3
    have hr := ih h3.2
    have hb : q ∉ wires (t.remapBit xr1 xr2 (w i) i) := by
      simp only [Tri.remapBit, wires_append, Finset.mem_union, not_or]
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp [wires, Instr.wires, h1, h2, h3.1]
    simp only [Tri.remapList, List.flatMap_cons, wires_append, Finset.mem_union, not_or] at hr ⊢
    exact ⟨hb, hr⟩

theorem classifierF_run (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, g1, wB, t].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ xs ∧ q ∉ work)
    (htmp : [one, U, V, F, pk].Nodup)
    (htx : ∀ q ∈ [one, U, V, F, pk], q ∉ xs ∧ q ∉ work ∧ q ≠ g)
    (s : State) (m : List Bool)
    (hg : s.basis g = false)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(matchBit tr xs s.basis &&
      decide ((s.basis (xs.getD tr.r1 0), s.basis (xs.getD tr.r2 0)) = tr.pat tr.S)))
    (hto : ∀ q ∈ [one, U, V, F, pk], q ≠ f → s.basis q = false)
    (x : Nat) (hx : x < 2^256) (xbit : ∀ i, i < 256 → s.basis (xs.getD i 0) = x.testBit i) :
    run (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) m s =
      put (run (classifier tr yb xs work y0 c f g g1 wB t) m s) pk
        ((run (classifier tr yb xs work y0 c f g g1 wB t) m s).basis g && decide (tr.A < x)) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  set w : Nat → Wire := fun i => xs.getD i 0 with hw
  set xr1 := w tr.r1 with hx1
  set xr2 := w tr.r2 with hx2
  set P := tr.idx.map w with hP
  have winj : ∀ i j, i < 256 → j < 256 → w i = w j → i = j := by
    intro i j hi hj e
    simp only [hw] at e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact hxs.getElem_inj_iff.mp e
  have wmem : ∀ i, i < 256 → w i ∈ xs := by
    intro i hi; simp only [hw]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hPn : P.Nodup := by
    apply List.Nodup.map_on _ ix.1
    intro i hi j hj e; exact winj i j (ix.2.2.2.2 i hi) (ix.2.2.2.2 j hj) e
  have memP : ∀ q, q ∈ P ↔ ∃ i ∈ tr.idx, w i = q := by intro q; simp [hP]
  have x1P : xr1 ∉ P := by
    rw [memP]; rintro ⟨i, hi, e⟩
    exact ix.2.2.1 (winj i tr.r1 (ix.2.2.2.2 i hi) pv.1 e ▸ hi)
  have x2P : xr2 ∉ P := by
    rw [memP]; rintro ⟨i, hi, e⟩
    exact ix.2.2.2.1 (winj i tr.r2 (ix.2.2.2.2 i hi) pv.2.1 e ▸ hi)
  have x12 : xr1 ≠ xr2 := fun e => pv.2.2.1 (winj _ _ pv.1 pv.2.1 e)
  have Psub : ∀ q ∈ P, q ∈ xs := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := (memP q).mp hq; exact wmem i (ix.2.2.2.2 i hi)
  have hPl : P.length = 254 := by simp [hP, ix.2.1]
  obtain ⟨i0, it, hidx⟩ : ∃ i0 it, tr.idx = i0 :: it := by
    have hl := ix.2.1
    cases h : tr.idx with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  have hP0 : P = w i0 :: it.map w := by simp [hP, hidx]
  set p0 := w i0 with hp0
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have zp := zeroPorts_maps (it.map w) work (by rw [hitl, hwl])
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, g1, wB, t]) : q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    refine ⟨fun hp => h.1 (Psub q hp), h.2, fun e => h.1 (e ▸ wmem _ pv.1), fun e => h.1 (e ▸ wmem _ pv.2.1)⟩
  have hused : [xr1, xr2, y0, c, f, g, g1, wB, t].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨x12, ?_⟩
      have := fun q hq => (extx q hq).2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      exact ⟨fun e => this y0 (Or.inl rfl) e.symm, fun e => this c (by tauto) e.symm,
        fun e => this f (by tauto) e.symm, fun e => this g (by tauto) e.symm,
        fun e => this g1 (by tauto) e.symm, fun e => this wB (by tauto) e.symm,
        fun e => this t (by tauto) e.symm⟩
    · intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      have h2 := fun q hq => (extx q hq).2.2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases hm with e | e | e | e | e | e | e
      · exact h2 y0 (Or.inl rfl) e.symm
      · exact h2 c (by tauto) e.symm
      · exact h2 f (by tauto) e.symm
      · exact h2 g (by tauto) e.symm
      · exact h2 g1 (by tauto) e.symm
      · exact h2 wB (by tauto) e.symm
      · exact h2 t (by tauto) e.symm
  have hlP : (i0 :: it).map w = P := by rw [hP0]; rfl
  have hPn' : ((i0 :: it).map w).Nodup := by rw [hlP]; exact hPn
  have x1P' : xr1 ∉ (i0 :: it).map w := by rw [hlP]; exact x1P
  have x2P' : xr2 ∉ (i0 :: it).map w := by rw [hlP]; exact x2P
  have hextP : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w := by
    intro q hq; rw [hlP]; exact (extx q hq).1
  have hdisj' : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := by
    intro q hq
    refine ⟨fun hm => hdisj q hq (Psub q (by rw [← hlP]; exact hm)), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (e | e | e)
    · exact hdisj q hq (e ▸ wmem _ pv.1)
    · exact hdisj q hq (e ▸ wmem _ pv.2.1)
    · exact (hextx q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)).2 hq
  have hmb : matchBit tr xs s.basis =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    simp only [matchBit, hidx]; rfl
  have hf' : s.basis f = !(((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) &&
      decide ((s.basis xr1, s.basis xr2) = tr.pat tr.S)) := by rw [← hmb]; exact hf
  obtain ⟨B, s2, s2ph, s2out, s2p0, s2it, Boff, Bph, Bf, chnd, chz, Bg, main⟩ :=
    shape_state tr v yb xr1 xr2 y0 c f g g1 wB t w i0 it work hPn' x1P' x2P' hused hextP
      (by rw [hitl, hwl]) hwn hdisj' s hg hz hf'
  have oldrun := classifier_run tr v yb xs work y0 c f g g1 wB t hxs hlen hwl hwn hdisj hext hextx s m hg hz hf
  have hG : (run (classifier tr yb xs work y0 c f g g1 wB t) m s).basis g = B.basis g := by
    rw [oldrun, Bg, hmb]
    simp only [tailEff, writeBit, Function.update_self]
    rfl
  set bs := zeroPorts (it.map w) work with hbs
  -- list structure
  have tmpM (q : Wire) (hq : q ∈ [one, U, V, F, pk]) (i : Nat) (hi : i < 256) : q ≠ w i :=
    fun e => (htx q hq).1 (e ▸ wmem i hi)
  have bsW : ∀ b ∈ bs, b.work ∈ work := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
  have bsI : ∀ b ∈ bs, b.input ∈ it.map w := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
  have hlenbs : it.length = bs.length := by
    have h1 : (bs.map ZeroBit.input).length = (it.map w).length := by rw [zp.1]
    simpa using h1.symm
  have hT : triples xs work one tr.idx = (i0, one, p0) :: tri p0 it bs := by rw [hidx]; rfl
  set T := triples xs work one tr.idx with hTdef
  have hsplit := idx_cat tr pv.2.2.1 pv.1 pv.2.1
  have hTm : T.map (·.1) = tr.topL ++ (tr.midL ++ tr.lowL) := by
    rw [← hsplit, hT, hidx, List.map_cons, tri_fst p0 it bs hlenbs]
  set Tt := T.take tr.topL.length with hTt
  set Tm := (T.drop tr.topL.length).take tr.midL.length with hTmm
  set Tl := T.drop (tr.topL.length + tr.midL.length) with hTl
  have mt : Tt.map (·.1) = tr.topL := by
    rw [hTt, List.map_take, hTm, List.take_left' rfl]
  have mm : Tm.map (·.1) = tr.midL := by
    rw [hTmm, List.map_take, List.map_drop, hTm, List.drop_left' rfl, List.take_left' rfl]
  have ml : Tl.map (·.1) = tr.lowL := by
    rw [hTl, List.map_drop, hTm, ← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl]
  have cat : Tt ++ (Tm ++ Tl) = T := by
    have e1 : Tm ++ Tl = T.drop tr.topL.length := by
      rw [hTl, ← List.drop_drop]; exact List.take_append_drop _ _
    rw [e1]; exact List.take_append_drop _ _
  have memT : ∀ y ∈ Tt ++ Tm ++ Tl, y ∈ T := by
    intro y hy; rw [← cat]; simpa [List.append_assoc] using hy
  -- all chain wires
  have triW : ∀ y ∈ T, (y.2.1 = one ∨ y.2.1 = p0 ∨ y.2.1 ∈ work) ∧ (y.2.2 = p0 ∨ y.2.2 ∈ work) := by
    intro y hy
    rw [hT] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨h1, b, hb, h2⟩ := tri_wires _ _ _ y hy
      refine ⟨?_, Or.inr (h2 ▸ bsW b hb)⟩
      rcases h1 with e | ⟨d, hd, e⟩
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (e ▸ bsW d hd))
  have p0x : p0 ∈ xs := wmem i0 (ix.2.2.2.2 i0 (by rw [hidx]; simp))
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at htmp
  obtain ⟨⟨oU, oV, oF, oP⟩, ⟨UV, UF, UP⟩, ⟨VF, VP⟩, FP⟩ := htmp
  have tmp1 : ∀ q ∈ [U, V, F, pk], q ≠ one := by
    intro q hq e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with e1 | e1 | e1 | e1
    · exact oU (e.symm.trans e1)
    · exact oV (e.symm.trans e1)
    · exact oF (e.symm.trans e1)
    · exact oP (e.symm.trans e1)
  have tmpIn : ∀ q ∈ [U, V, F, pk], q ∈ [one, U, V, F, pk] := fun q hq => List.mem_cons_of_mem _ hq
  have offT : ∀ q ∈ [U, V, F, pk], ∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q := by
    intro q hq y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := (htx q (tmpIn q hq)).1
    have a2 := (htx q (tmpIn q hq)).2.1
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact (tmp1 q hq).symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have gnot := extx g (by simp)
  have gone : g ≠ one := fun e => (htx one (by simp)).2.2 e.symm
  have offG : ∀ y ∈ T, y.2.1 ≠ g ∧ y.2.2 ≠ g := by
    intro y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := (hextx g (by simp)).1
    have a2 := gnot.2.1
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact gone.symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have endOff : ∀ (A : List (Nat × Wire × Wire)) (p q : Wire), (∀ y ∈ A, y ∈ T) → p ≠ q →
      (∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q) → endW p A ≠ q := by
    intro A p q hA hp hy
    rcases endW_mem p A with e | ⟨y, h, e⟩
    · rw [e]; exact hp
    · rw [e]; exact (hy y (hA y h)).2
  have inTt : ∀ y ∈ Tt, y ∈ T := fun y h => List.mem_of_mem_take h
  have inTm : ∀ y ∈ Tm, y ∈ T := fun y h => List.mem_of_mem_drop (List.mem_of_mem_take h)
  have mU : U ∈ [U, V, F, pk] := by simp
  have mV : V ∈ [U, V, F, pk] := by simp
  have mF : F ∈ [U, V, F, pk] := by simp
  have mP : pk ∈ [U, V, F, pk] := by simp
  have h1l : tr.lo < 256 := by simp only [Tri.lo]; omega
  have h1h : tr.hi < 256 := by simp only [Tri.hi]; omega
  have nx (q : Wire) (hq : q ∈ [U, V, F, pk]) (i : Nat) (hi : i < 256) : w i ≠ q :=
    (tmpM q (tmpIn q hq) i hi).symm
  have eO := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tt one q inTt (tmp1 q hq).symm (offT q hq)
  have eM := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tm (endW one Tt) q inTm (eO q hq) (offT q hq)
  have hTall : ∀ y ∈ Tt ++ Tm ++ Tl, (y.2.1 ≠ U ∧ y.2.2 ≠ U) ∧ (y.2.1 ≠ V ∧ y.2.2 ≠ V) ∧
      (y.2.1 ≠ F ∧ y.2.2 ≠ F) := fun y hy =>
    ⟨offT U mU y (memT y hy), offT V mV y (memT y hy), offT F mF y (memT y hy)⟩
  have Pp : ProperProgram (preOf tr xs work one U V F) :=
    pre_proper _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nx V mV _ h1l) UV (nx F mF _ h1h) VF (eM U mU) (eO V mV) hTall
  have pkNot : pk ∉ wires (preOf tr xs work one U V F) := by
    apply pre_not
    · exact ⟨tmp1 pk mP, Ne.symm UP, Ne.symm VP, Ne.symm FP, (nx pk mP _ h1l).symm, (nx pk mP _ h1h).symm,
        (eM pk mP).symm, (eO pk mP).symm⟩
    · intro y hy
      have := offT pk mP y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have gNot : g ∉ wires (preOf tr xs work one U V F) := by
    have gU : g ≠ U := fun e => (htx U (by simp)).2.2 e.symm
    have gV : g ≠ V := fun e => (htx V (by simp)).2.2 e.symm
    have gF : g ≠ F := fun e => (htx F (by simp)).2.2 e.symm
    apply pre_not
    · refine ⟨gone, gU, gV, gF, ?_, ?_, ?_, ?_⟩
      · exact fun e => (hextx g (by simp)).1 (e ▸ wmem _ h1l)
      · exact fun e => (hextx g (by simp)).1 (e ▸ wmem _ h1h)
      · exact (endOff Tm (endW one Tt) g inTm (endOff Tt one g inTt gone.symm offG) offG).symm
      · exact (endOff Tt one g inTt gone.symm offG).symm
    · intro y hy
      have := offG y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have wNot : ∀ q, q ∉ work → ∀ b ∈ bs, b.work ≠ q := fun q hq b hb e => hq (e ▸ bsW b hb)
  have tmpP : ∀ q ∈ [one, U, V, F, pk], q ∉ (i0 :: it).map w := fun q hq h =>
    (htx q hq).1 (Psub q (by rw [← hlP]; exact h))
  have Bt : ∀ q ∈ [one, U, V, F, pk], B.basis q = false := by
    intro q hq
    by_cases qf : q = f
    · rw [qf]; exact Bf
    · rw [Boff q qf (htx q hq).2.2, fill_outside _ _ _ q (wNot q (htx q hq).2.1),
        s2out q (tmpP q hq)]
      exact hto q hq qf
  have pivB (i : Nat) (hi : i = tr.r1 ∨ i = tr.r2) : B.basis (w i) = x.testBit i := by
    have hi256 : i < 256 := by rcases hi with rfl | rfl <;> [exact pv.1; exact pv.2.1]
    have nP : w i ∉ (i0 :: it).map w := by
      rcases hi with rfl | rfl <;> [exact x1P'; exact x2P']
    have nW : w i ∉ work := fun h => hdisj _ h (wmem i hi256)
    have nf : w i ≠ f := fun e => (hextx f (by simp)).1 (e ▸ wmem i hi256)
    have ng : w i ≠ g := fun e => (hextx g (by simp)).1 (e ▸ wmem i hi256)
    rw [Boff _ nf ng, fill_outside _ _ _ _ (wNot _ nW), s2out _ nP]
    exact xbit i hi256
  have hiP : tr.hi = tr.r1 ∨ tr.hi = tr.r2 := by simp only [Tri.hi]; omega
  have loP : tr.lo = tr.r1 ∨ tr.lo = tr.r2 := by simp only [Tri.lo]; omega
  have hxr1 : s.basis xr1 = x.testBit tr.r1 := xbit _ pv.1
  have hxr2 : s.basis xr2 = x.testBit tr.r2 := xbit _ pv.2.1
  let mtf : Nat → Bool := fun i => x.testBit i == tr.tgt i (x.testBit tr.r1, x.testBit tr.r2)
  have i0m : i0 ∈ tr.idx := by rw [hidx]; simp
  have itm : ∀ i ∈ it, i ∈ tr.idx := fun i hi => by rw [hidx]; simp [hi]
  have p0ne : one ≠ p0 := fun e => (htx one (by simp)).1 (e ▸ p0x)
  have p0f : p0 ≠ f := fun e => (hextx f (by simp)).1 (e ▸ p0x)
  have p0g : p0 ≠ g := fun e => (hextx g (by simp)).1 (e ▸ p0x)
  have p0W : p0 ∉ work := fun h => hdisj _ h p0x
  have hc0 : s2.basis p0 = mtf i0 := by
    rw [s2p0, hxr1, hxr2, xbit i0 (ix.2.2.2.2 i0 i0m)]
  have hchain : Chain (writeBit B.basis one true) mtf true (Tt ++ (Tm ++ Tl)) := by
    rw [cat, hT]
    refine ⟨by simp [writeBit], ?_, ?_⟩
    · simp only [writeBit, Function.update_apply, Ne.symm p0ne, if_false, Bool.true_and]
      rw [Boff _ p0f p0g, fill_outside _ _ _ _ (wNot _ p0W), hc0]
    · have hmt : ∀ k (hk : k < it.length), mtf it[k] = !s2.basis (bs[k]'(hlenbs ▸ hk)).input := by
        intro k hk
        have hin : (bs[k]'(hlenbs ▸ hk)).input = w it[k] := by
          have e1 : (bs.map ZeroBit.input)[k]'(by simpa using hlenbs ▸ hk) = (bs[k]'(hlenbs ▸ hk)).input := by
            simp
          have e2 : (it.map w)[k]'(by simpa using hk) = w it[k] := by simp
          rw [← e1, ← e2]
          exact List.getElem_of_eq zp.1 _
        have im : it[k] ∈ it := List.getElem_mem _
        rw [hin, s2it _ im, hxr1, hxr2, xbit _ (ix.2.2.2.2 _ (itm _ im))]
        simp only [mtf]
        cases x.testBit it[k] <;> cases tr.tgt it[k] (x.testBit tr.r1, x.testBit tr.r2) <;> rfl
      have cf := chain_fill mtf p0 it bs s2.basis (true && mtf i0) hlenbs chnd chz (by simpa using hc0) hmt
      apply chain_congr _ _ _ _ _ _ cf
      intro y hy
      have hyw := tri_wires _ _ _ y hy
      have side : ∀ q, (q = p0 ∨ ∃ b ∈ bs, q = b.work) →
          fill p0 bs s2.basis q = writeBit B.basis one true q := by
        intro q hq
        have qx : q ∈ xs ∨ q ∈ work := by
          rcases hq with e | ⟨b, hb, e⟩
          · exact Or.inl (e ▸ p0x)
          · exact Or.inr (e ▸ bsW b hb)
        have nf : q ≠ f := by
          intro e
          rcases qx with h | h
          · exact (hextx f (by simp)).1 (e ▸ h)
          · exact (hextx f (by simp)).2 (e ▸ h)
        have ng : q ≠ g := by
          intro e
          rcases qx with h | h
          · exact (hextx g (by simp)).1 (e ▸ h)
          · exact (hextx g (by simp)).2 (e ▸ h)
        have no : q ≠ one := by
          intro e
          rcases qx with h | h
          · exact (htx one (by simp)).1 (e ▸ h)
          · exact (htx one (by simp)).2.1 (e ▸ h)
        simp only [writeBit, Function.update_apply, no, if_false]
        exact (Boff q nf ng).symm
      exact ⟨side _ hyw.1, side _ (Or.inr hyw.2)⟩
  have nlo (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.lo ≠ q := nx q hq _ h1l
  have nhi (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.hi ≠ q := nx q hq _ h1h
  have FV := F_value tr v pv.2.2.1 x hx one U V F (w tr.hi) (w tr.lo) Tt Tm Tl mt mm ml UV UF VF
    (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
    (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
    (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l)) (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h))
    hTall B (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp)) (Bt one (by simp))
    (pivB _ hiP) (pivB _ loP) hchain
  have gpk : g ≠ pk := fun e => (htx pk (by simp)).2.2 e.symm
  have hE : ∀ m', run (extract tr xs work one U V F pk g) m' B =
      put B pk (B.basis pk ^^ ((run (preOf tr xs work one U V F) [] B).basis g &&
        (run (preOf tr xs work one U V F) [] B).basis F)) :=
    by
      intro m'
      have htpk : ∀ z ∈ MeasuredFV.correctionWires tr.A Tt, z ≠ pk := by
        apply MeasuredFV.correctionWires_off_research
        intro y hy
        exact offT pk mP y (inTt y hy)
      have hmpk : ∀ z ∈ MeasuredFV.correctionWires tr.A Tm, z ≠ pk := by
        apply MeasuredFV.correctionWires_off_research
        intro y hy
        exact offT pk mP y (inTm y hy)
      have hlpk : ∀ y ∈ Tl, y.2.1 ≠ pk ∧ y.2.2 ≠ pk := by
        intro y hy
        exact offT pk mP y (memT y (by simp [hy]))
      have fast := MeasuredFV.fastExtract_semantics tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi)
        one U V F (w tr.lo) (w tr.hi) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl g pk
        FP VP UP (nlo pk mP) (nhi pk mP) (eM pk mP) (eO pk mP) htpk hmpk oP hlpk UV UF VF
        (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
        (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
        (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l))
        (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h)) hTall B m'
        (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp))
      simpa only [extract, preOf, hTt, hTmm, hTl, hTdef, hw, put] using fast
  have hRg : (run (preOf tr xs work one U V F) [] B).basis g = B.basis g :=
    run_preserves_outside _ [] B g gNot
  have hval : (B.basis pk ^^ ((run (preOf tr xs work one U V F) [] B).basis g &&
      (run (preOf tr xs work one U V F) [] B).basis F)) = (B.basis g && decide (tr.A < x)) := by
    have e : (run (preOf tr xs work one U V F) [] B).basis F = decide (tr.A < x) := FV
    rw [Bt pk (by simp), hRg, e, Bool.false_xor]
  rw [hval] at hE
  have hpk1 : pk ∉ (p0 :: bs.flatMap ZeroBit.wires) := by
    intro h
    rcases List.mem_cons.mp h with e | h
    · exact (htx pk (by simp)).1 (e ▸ p0x)
    · obtain ⟨b, hb, hw'⟩ := List.mem_flatMap.mp h
      simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with e | e
      · obtain ⟨i, hi, e2⟩ := List.mem_map.mp (bsI b hb)
        exact (htx pk (by simp)).1 (e ▸ e2 ▸ wmem i (ix.2.2.2.2 i (itm i hi)))
      · exact (htx pk (by simp)).2.1 (e ▸ bsW b hb)
  have hpk2 : pk ∉ wires ([.X p0] ++ tr.remapList xr1 xr2 w (i0 :: it)) := by
    rw [wires_append]
    simp only [Finset.mem_union, not_or]
    refine ⟨?_, remapList_not tr xr1 xr2 w _ pk (nx pk mP _ pv.1).symm (nx pk mP _ pv.2.1).symm (tmpP pk (by simp))⟩
    have np : pk ≠ p0 := (nx pk mP i0 (ix.2.2.2.2 i0 i0m)).symm
    simp [wires, Instr.wires, np]
  have M := main (extract tr xs work one U V F pk g) pk _ hE hpk1 hpk2 m
  have hprog : classifier tr yb xs work y0 c f g g1 wB t =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [classifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  have hprogF : classifierF tr yb xs work y0 c f g g1 wB t one U V F pk =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (fun h => tail tr yb xr1 xr2 y0 c f g g1 wB t h ++ extract tr xs work one U V F pk g)
        (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [classifierF, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hG, hprogF, hprog]
  exact M






theorem triples_length (xs work : List Wire) (one : Wire) (l : List Nat) :
    (triples xs work one l).length ≤ l.length := by
  cases l with
  | nil => simp [triples]
  | cons i0 it =>
    have h : ∀ (c : Wire) (l : List Nat) (bs : List ZeroBit), (tri c l bs).length ≤ l.length := by
      intro c l bs
      induction l generalizing c bs with
      | nil => cases bs <;> simp [tri]
      | cons i l ih =>
        cases bs with
        | nil => simp [tri]
        | cons b bs =>
          simp only [tri, List.length_cons]
          have := ih b.work bs
          omega
    simp only [triples, List.length_cons]
    have := h (xs.getD i0 0) it (zeroPorts (it.map (fun i => xs.getD i 0)) work)
    omega

theorem mx_preV_counts (a : Nat) (aL : Bool) (one U V xlo el : Wire)
    (mid low : List (Nat × Wire × Wire)) :
    toffoliCount (mxPreV a aL one U V xlo el mid low) = 1 ∧
    measurementCount (mxPreV a aL one U V xlo el mid low) = 0 ∧
    Challenge.gateSlots (mxPreV a aL one U V xlo el mid low) ≤ 2 * (mid.length + low.length) + 5 := by
  have s1 := xorAcc_slots a U low
  have s2 := xorAcc_slots a V mid
  have mt : toffoliCount (muxAnd aL el xlo U V) = 1 := by
    cases aL <;> simp [muxAnd, toffoliCount]
  have ms : Challenge.gateSlots (muxAnd aL el xlo U V) ≤ 4 := by
    cases aL <;> simp [muxAnd, Challenge.gateSlots, Challenge.instructionSlots]
  refine ⟨?_, ?_, ?_⟩
  · simp only [mxPreV, toffoliCount_append, xorAcc_tc, mt, toffoliCount]
  · simp only [mxPreV, measurementCount_append, xorAcc_mc, muxAnd_mc]; rfl
  · simp only [mxPreV, Challenge.gateSlots_append]
    simp only [Challenge.gateSlots, Challenge.instructionSlots, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at s1 s2 ms ⊢
    omega

theorem mx_z_length (a : Nat) (T : List (Nat × Wire × Wire)) :
    (mxZ a T).length ≤ 2 * T.length := by
  induction T with
  | nil => simp [mxZ]
  | cons x r ih =>
    obtain ⟨i, p, c⟩ := x
    simp only [mxZ, List.length_append, List.length_cons]
    split_ifs <;> simp only [List.length_nil, List.length_cons] <;> omega

theorem mx_corr_length (a : Nat) (aH : Bool) (V xhi eh : Wire) (top : List (Nat × Wire × Wire)) :
    (mxCorr a aH V xhi eh top).length ≤ 3 + 2 * top.length := by
  have := mx_z_length a top
  unfold mxCorr
  rw [List.length_append]
  cases aH <;> simp <;> omega

theorem extract_counts (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire) :
    toffoliCount (extract tr xs work one U V F pk g) ≤ 3 ∧
    measurementCount (extract tr xs work one U V F pk g) = 2 ∧
    Challenge.gateSlots (extract tr xs work one U V F pk g) ≤ 1037 := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have hcounts := MeasuredFV.fastExtract_counts tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
  have hslots := MeasuredFV.fastExtract_slots_research tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
  have ix := Tri.idx_facts v
  have hl := triples_length xs work one tr.idx
  rw [ix.2.1] at hl
  have hsum : Tt.length + Tm.length + Tl.length ≤ 254 := by
    dsimp [Tt,Tm,Tl,T]
    simp only [List.length_take, List.length_drop]
    omega
  let P := MeasuredFV.fastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl
  change Challenge.gateSlots P ≤ 4 * (Tt.length + Tm.length + Tl.length) + 19 at hslots
  change toffoliCount P ≤ 3 ∧ measurementCount P = 2 ∧ Challenge.gateSlots P ≤ 1037
  exact ⟨hcounts.1, hcounts.2, by omega⟩theorem extractOutput_equiv (tr : Tri) (xs work : List Wire) (one U V F pk g : Wire)
    (gp : g ≠ pk) (fp : F ≠ pk) (s : State) (m : List Bool)
    (known : (run (preOf tr xs work one U V F) [] s).basis pk =
      ((run (preOf tr xs work one U V F) [] s).basis g && (run (preOf tr xs work one U V F) [] s).basis F)) :
    run (extractOutput tr xs work one U V F pk g) m s =
      run (extract tr xs work one U V F pk g) (m.drop 1) s := by
  exact MeasuredFV.outputFastExtract_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gp fp s m known

theorem extractOutput_counts (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire) :
    toffoliCount (extractOutput tr xs work one U V F pk g) ≤ 2 ∧
    measurementCount (extractOutput tr xs work one U V F pk g) = 3 ∧
    Challenge.gateSlots (extractOutput tr xs work one U V F pk g) ≤ 1038 := by
  have hp := extract_counts tr v xs work one U V F pk g
  have hc := MeasuredFV.outputFastExtract_counts tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi)
    one U V F (xs.getD tr.lo 0) (xs.getD tr.hi 0)
    (endW (endW one ((triples xs work one tr.idx).take tr.topL.length))
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length))
    (endW one ((triples xs work one tr.idx).take tr.topL.length)) g pk
    ((triples xs work one tr.idx).take tr.topL.length)
    (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length)
    ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length))
  have he := MeasuredFV.outputFastExtract_slots tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi)
    one U V F (xs.getD tr.lo 0) (xs.getD tr.hi 0)
    (endW (endW one ((triples xs work one tr.idx).take tr.topL.length))
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length))
    (endW one ((triples xs work one tr.idx).take tr.topL.length)) g pk
    ((triples xs work one tr.idx).take tr.topL.length)
    (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length)
    ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length))
  change Challenge.gateSlots (extractOutput tr xs work one U V F pk g) =
    Challenge.gateSlots (extract tr xs work one U V F pk g) + 1 at he
  exact ⟨hc.1, hc.2, by omega⟩


theorem classifierF_counts (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hwl : work.length = 253) :
    toffoliCount (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) ≤ 259 ∧
    measurementCount (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) = 259 ∧
    Challenge.gateSlots (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) ≤ 3361 + 1037 := by
  obtain ⟨i0, it, hidx, hitl⟩ := InputSentinel.idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have ec := extract_counts tr v xs work one U V F pk g
  have zc := zeroWith_counts_general
    (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
      extract tr xs work one U V F pk g) (3 + toffoliCount (extract tr xs work one U V F pk g)) 6
    (fun h => by
      have tc := InputSentinel.tail_counts tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h
      rw [toffoliCount_append, measurementCount_append, tc.1, tc.2, ec.2.1]
      exact ⟨rfl, rfl⟩)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc
  have zs := InputSentinel.zeroWith_slots
    (fun h => tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h ++
      extract tr xs work one U V F pk g)
    (Challenge.gateSlots (decodeT tr yb) + Challenge.gateSlots (extract tr xs work one U V F pk g))
    (fun h => by
      rw [Challenge.gateSlots_append, InputSentinel.tail_slots])
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := InputSentinel.remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := InputSentinel.decodeT_slots tr yb
  have rt := InputSentinel.remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold classifierF
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append, rt, rm, zc.1, zc.2, zs]
  refine ⟨?_, by simp [measurementCount], ?_⟩
  · have := ec.1
    simp [toffoliCount]
    omega
  · have := ec.2.2
    simp only [Challenge.gateSlots, Challenge.instructionSlots, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at rs ds this ⊢
    omega

theorem triples_wires (xs work : List Wire) (one : Wire) (l : List Nat) (hl : ∀ i ∈ l, i < 256)
    (hlen : xs.length = 256) :
    ∀ y ∈ triples xs work one l, (y.2.1 = one ∨ y.2.1 ∈ xs ∨ y.2.1 ∈ work) ∧ (y.2.2 ∈ xs ∨ y.2.2 ∈ work) := by
  cases l with
  | nil => simp [triples]
  | cons i0 it =>
    have p0x : xs.getD i0 0 ∈ xs := by
      have := hl i0 (by simp)
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    intro y hy
    simp only [triples, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨Or.inl rfl, Or.inl p0x⟩
    · obtain ⟨h1, b, hb, h2⟩ := tri_wires _ _ _ y hy
      have w1 := (zeroPorts_mem _ _ b hb).2
      refine ⟨?_, Or.inr (h2 ▸ w1)⟩
      rcases h1 with e | ⟨d, hd, e⟩
      · exact Or.inr (Or.inl (e ▸ p0x))
      · exact Or.inr (Or.inr (e ▸ (zeroPorts_mem _ _ d hd).2))

/-- Facts every wire of the chain shares with a wire off the chain. -/
theorem preOf_off (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F q : Wire)
    (hlen : xs.length = 256) (hx : q ∉ xs) (hw : q ∉ work) (ho : q ≠ one) :
    let T := triples xs work one tr.idx
    (∀ y ∈ T, q ≠ y.2.1 ∧ q ≠ y.2.2) ∧
    q ≠ endW one (T.take tr.topL.length) ∧
    q ≠ endW (endW one (T.take tr.topL.length)) ((T.drop tr.topL.length).take tr.midL.length) ∧
    q ≠ xs.getD tr.lo 0 ∧ q ≠ xs.getD tr.hi 0 := by
  intro T
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have tw := triples_wires xs work one tr.idx ix.2.2.2.2 hlen
  have off : ∀ y ∈ T, q ≠ y.2.1 ∧ q ≠ y.2.2 := by
    intro y hy
    obtain ⟨a, b⟩ := tw y hy
    refine ⟨?_, ?_⟩
    · rcases a with e | e | e
      · rw [e]; exact ho
      · exact fun E => hx (E ▸ e)
      · exact fun E => hw (E ▸ e)
    · rcases b with e | e
      · exact fun E => hx (E ▸ e)
      · exact fun E => hw (E ▸ e)
  have e1 : q ≠ endW one (T.take tr.topL.length) := by
    rcases endW_mem one (T.take tr.topL.length) with e | ⟨y, h, e⟩
    · rw [e]; exact ho
    · rw [e]; exact (off y (List.mem_of_mem_take h)).2
  have e2 : q ≠ endW (endW one (T.take tr.topL.length)) ((T.drop tr.topL.length).take tr.midL.length) := by
    rcases endW_mem (endW one (T.take tr.topL.length)) ((T.drop tr.topL.length).take tr.midL.length) with
      e | ⟨y, h, e⟩
    · rw [e]; exact e1
    · rw [e]; exact (off y (List.mem_of_mem_drop (List.mem_of_mem_take h))).2
  have mem (i : Nat) (hi : i < 256) : xs.getD i 0 ∈ xs := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hlo : tr.lo < 256 := by simp only [Tri.lo]; have := pv.1; have := pv.2.1; omega
  have hhi : tr.hi < 256 := by simp only [Tri.hi]; have := pv.1; have := pv.2.1; omega
  exact ⟨off, e1, e2, fun E => hx (E ▸ mem _ hlo), fun E => hx (E ▸ mem _ hhi)⟩

theorem preOf_proper (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F : Wire)
    (hlen : xs.length = 256) (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) :
    ProperProgram (preOf tr xs work one U V F) := by
  obtain ⟨u1, u2, u3, u4, u5⟩ := preOf_off tr v xs work one U V F U hlen hU.1 hU.2.1 hU.2.2
  obtain ⟨v1, v2, v3, v4, v5⟩ := preOf_off tr v xs work one U V F V hlen hV.1 hV.2.1 hV.2.2
  obtain ⟨f1, f2, f3, f4, f5⟩ := preOf_off tr v xs work one U V F F hlen hF.1 hF.2.1 hF.2.2
  have memT : ∀ y ∈ ((triples xs work one tr.idx).take tr.topL.length) ++
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length) ++
      ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length)),
      y ∈ triples xs work one tr.idx := by
    intro y hy
    simp only [List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    · exact List.mem_of_mem_drop h
  exact pre_proper _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Ne.symm v4) UV (Ne.symm f5) VF (Ne.symm u3) (Ne.symm v2)
    (fun y hy => ⟨⟨Ne.symm (u1 y (memT y hy)).1, Ne.symm (u1 y (memT y hy)).2⟩,
      ⟨Ne.symm (v1 y (memT y hy)).1, Ne.symm (v1 y (memT y hy)).2⟩,
      ⟨Ne.symm (f1 y (memT y hy)).1, Ne.symm (f1 y (memT y hy)).2⟩⟩)

theorem preOf_sub (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F : Wire)
    (hlen : xs.length = 256) (W : Finset Wire) (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) :
    wires (preOf tr xs work one U V F) ⊆ W := by
  intro q hq
  apply Classical.byContradiction
  intro hn
  have nx : q ∉ xs := fun h => hn (hx q h)
  have nw : q ∉ work := fun h => hn (hw q h)
  have no : q ≠ one := fun e => hn (e ▸ h1)
  obtain ⟨o1, o2, o3, o4, o5⟩ := preOf_off tr v xs work one U V F q hlen nx nw no
  have memT : ∀ y ∈ ((triples xs work one tr.idx).take tr.topL.length) ++
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length) ++
      ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length)),
      y ∈ triples xs work one tr.idx := by
    intro y hy
    simp only [List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    · exact List.mem_of_mem_drop h
  exact pre_not _ _ _ _ _ _ _ _ _ _ _ _ _ _ q
    ⟨no, fun e => hn (e ▸ h2), fun e => hn (e ▸ h3), fun e => hn (e ▸ h4), o4, o5, o3, o2⟩
    (fun y hy => o1 y (memT y hy)) hq

theorem extract_sub (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire)
    (hlen : xs.length = 256) (W : Finset Wire) (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) (h5 : pk ∈ W) (h6 : g ∈ W) :
    wires (extract tr xs work one U V F pk g) ⊆ W := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have ix := Tri.idx_facts v
  have pv := Tri.pivots v
  have hAll : ∀ y ∈ T, y.2.1 ∈ W ∧ y.2.2 ∈ W := by
    intro y hy
    have h := triples_wires xs work one tr.idx ix.2.2.2.2 hlen y hy
    constructor
    · rcases h.1 with e | e | e
      · rw [e]; exact h1
      · exact hx _ e
      · exact hw _ e
    · rcases h.2 with e | e
      · exact hx _ e
      · exact hw _ e
  have htop : ∀ y ∈ Tt, y.2.1 ∈ W ∧ y.2.2 ∈ W := fun y hy => hAll y (List.mem_of_mem_take hy)
  have hmid : ∀ y ∈ Tm, y.2.1 ∈ W ∧ y.2.2 ∈ W := fun y hy => hAll y (List.mem_of_mem_drop (List.mem_of_mem_take hy))
  have hlow : ∀ y ∈ Tl, y.2.1 ∈ W ∧ y.2.2 ∈ W := fun y hy => hAll y (List.mem_of_mem_drop hy)
  have heh : endW one Tt ∈ W := by
    rcases endW_mem one Tt with e | ⟨y, hy, e⟩
    · rw [e]; exact h1
    · rw [e]; exact (htop y hy).2
  have hel : endW (endW one Tt) Tm ∈ W := by
    rcases endW_mem (endW one Tt) Tm with e | ⟨y, hy, e⟩
    · rw [e]; exact heh
    · rw [e]; exact (hmid y hy).2
  have hloN : tr.lo < 256 := by simp only [Tri.lo]; omega
  have hhiN : tr.hi < 256 := by simp only [Tri.hi]; omega
  have hlo : xs.getD tr.lo 0 ∈ W := by
    apply hx
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hhi : xs.getD tr.hi 0 ∈ W := by
    apply hx
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hpre : wires (pre tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl) ⊆ W := by
    exact preOf_sub tr v xs work one U V F hlen W hx hw h1 h2 h3 h4
  have hcc : wires [.CCX g F pk] ⊆ W := by simp [wires, Instr.wires, Finset.insert_subset_iff, h4, h5, h6]
  have hclear := MeasuredFV.clearFV_sub_research tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm W h2 h3 h4 hlo hhi hel heh htop hmid
  have hfinish := MeasuredFV.finishUOne_sub_research tr.A one U Tl W h1 h2 hlow
  change wires (MeasuredFV.fastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl) ⊆ W
  simp only [MeasuredFV.fastExtract, wires_append, Finset.union_subset_iff]
  exact ⟨hpre, ⟨⟨hcc, hclear⟩, hfinish⟩⟩

theorem extractOutput_sub (tr : Tri) (v : tr.Valid) (xs work : List Wire) (one U V F pk g : Wire)
    (hlen : xs.length = 256) (W : Finset Wire) (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) (h5 : pk ∈ W) (h6 : g ∈ W) :
    wires (extractOutput tr xs work one U V F pk g) ⊆ W := by
  have he := MeasuredFV.outputFastExtract_wires tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi)
    one U V F (xs.getD tr.lo 0) (xs.getD tr.hi 0)
    (endW (endW one ((triples xs work one tr.idx).take tr.topL.length))
      (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length))
    (endW one ((triples xs work one tr.idx).take tr.topL.length)) g pk
    ((triples xs work one tr.idx).take tr.topL.length)
    (((triples xs work one tr.idx).drop tr.topL.length).take tr.midL.length)
    ((triples xs work one tr.idx).drop (tr.topL.length + tr.midL.length))
  change wires (extractOutput tr xs work one U V F pk g) = wires (extract tr xs work one U V F pk g) at he
  rw [he]
  exact extract_sub tr v xs work one U V F pk g hlen W hx hw h1 h2 h3 h4 h5 h6

theorem zeroWith_app_physical (T : Wire → Program) (E : Program) (hE : GatePhysical E) :
    ∀ (c : Wire) (bs : List ZeroBit), GatePhysical (zeroWith T c bs) →
      GatePhysical (zeroWith (fun h => T h ++ E) c bs) := by
  intro c bs
  induction bs generalizing c with
  | nil =>
    intro h
    simp only [zeroWith, gatePhysical_append] at h ⊢
    exact ⟨h, hE⟩
  | cons b bs ih =>
    intro h
    simp only [zeroWith, gatePhysical_append] at h ⊢
    exact ⟨⟨h.1.1, ih b.work h.1.2⟩, h.2⟩

theorem zeroWith_app_wires (T : Wire → Program) (E : Program) :
    ∀ (c : Wire) (bs : List ZeroBit),
      wires (zeroWith (fun h => T h ++ E) c bs) ⊆ wires (zeroWith T c bs) ∪ wires E := by
  intro c bs
  induction bs generalizing c with
  | nil => simp [zeroWith, wires_append]
  | cons b bs ih =>
    simp only [zeroWith, wires_append]
    intro q hq
    have i := ih b.work (a := q)
    simp only [Finset.mem_union] at hq i ⊢
    tauto

theorem extract_physical (tr : Tri) (v : tr.Valid) (xs work : List Wire)
    (one U V F pk g : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : g ≠ pk) :
    GatePhysical (extract tr xs work one U V F pk g) := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have Pp := preOf_proper tr v xs work one U V F hlen hU hV hF UV VF
  have off := (preOf_off tr v xs work one U V F U hlen hU.1 hU.2.1 hU.2.2).1
  have hLow : ∀ x ∈ Tl, x.2.1 ≠ U ∧ x.2.2 ≠ U := by
    intro x hx
    have h := off x (List.mem_of_mem_drop hx)
    exact ⟨h.1.symm, h.2.symm⟩
  have hPre : ProperProgram (pre tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl) := by
    exact Pp
  change GatePhysical (MeasuredFV.fastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl)
  exact MeasuredFV.fastExtract_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPre gp Fp hLow

theorem extractOutput_physical (tr : Tri) (v : tr.Valid) (xs work : List Wire)
    (one U V F pk g : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : g ≠ pk) :
    GatePhysical (extractOutput tr xs work one U V F pk g) := by
  let T := triples xs work one tr.idx
  let Tt := T.take tr.topL.length
  let Tm := (T.drop tr.topL.length).take tr.midL.length
  let Tl := T.drop (tr.topL.length + tr.midL.length)
  have Pp := preOf_proper tr v xs work one U V F hlen hU hV hF UV VF
  have off := (preOf_off tr v xs work one U V F U hlen hU.1 hU.2.1 hU.2.2).1
  have hLow : ∀ x ∈ Tl, x.2.1 ≠ U ∧ x.2.2 ≠ U := by
    intro x hx
    have h := off x (List.mem_of_mem_drop hx)
    exact ⟨h.1.symm, h.2.symm⟩
  have hPre : ProperProgram (pre tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl) := by
    exact Pp
  change GatePhysical (MeasuredFV.outputFastExtract tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi) one U V F
    (xs.getD tr.lo 0) (xs.getD tr.hi 0) (endW (endW one Tt) Tm) (endW one Tt) g pk Tt Tm Tl)
  exact MeasuredFV.outputFastExtract_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPre gp Fp hLow

theorem classifierF_physical (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : g ≠ pk)
    (old : GatePhysical (classifier tr yb xs work y0 c f g g1 wB t)) :
    GatePhysical (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) := by
  have hE := extract_physical tr v xs work one U V F pk g hlen hU hV hF UV VF Fp gp
  unfold classifier at old
  simp only [gatePhysical_append] at old
  unfold classifierF
  simp only [gatePhysical_append]
  exact ⟨old.1, old.2.1, zeroWith_app_physical _ _ hE _ _ old.2.2.1, old.2.2.2⟩

theorem classifierF_wires (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t one U V F pk : Wire) (hlen : xs.length = 256) (W : Finset Wire)
    (hc : wires (classifier tr yb xs work y0 c f g g1 wB t) ⊆ W)
    (hx : ∀ q ∈ xs, q ∈ W) (hw : ∀ q ∈ work, q ∈ W)
    (h1 : one ∈ W) (h2 : U ∈ W) (h3 : V ∈ W) (h4 : F ∈ W) (h5 : pk ∈ W) (h6 : g ∈ W) :
    wires (classifierF tr yb xs work y0 c f g g1 wB t one U V F pk) ⊆ W := by
  have E := extract_sub tr v xs work one U V F pk g hlen W hx hw h1 h2 h3 h4 h5 h6
  unfold classifier at hc
  simp only [wires_append, Finset.union_subset_iff] at hc
  unfold classifierF
  simp only [wires_append, Finset.union_subset_iff]
  exact ⟨hc.1, hc.2.1, (zeroWith_app_wires _ _ _ _).trans (Finset.union_subset hc.2.2.1 E), hc.2.2.2⟩

end Shape

end ECDSAAdd.Entrant.ZeroFill

end

section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FlagEntry
open Arithmetic Challenge RecordedQuantum NativeFirstDirect MappedCompressed
open ParityXEntry E1Merge E1WholeKAdd52Research Secp256k1 ControlledPointLayout
open ParityCarry ParityConvert ParityEven EntryFuseArithmetic ParityUniform

/-- Two CNOTs moving a set bit from `pk` to the clean wire `a`. -/
def swp (pk a : Wire) : Program := [.CX pk a, .CX a pk]

theorem swp_run (pk a : Wire) (hne : pk ≠ a) (s : State) (m : List Bool)
    (ha : s.basis a = false) :
    run (swp pk a) m s = put (put s pk false) a (s.basis pk) := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases q1 : q = pk
    · subst q1; simp [swp, run, put, writeBit, hne, ha]
    · by_cases q2 : q = a
      · subst q2; simp [swp, run, put, writeBit, Ne.symm hne, ha]
      · simp [swp, run, put, writeBit, q1, q2]

/-- Two renamed runs agree when their pulled runs agree and the states agree off the image. -/
theorem rename_eq2 (f : Wire → Wire) (S : Finset Wire) (inj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    (P Q : Program) (hP : wires P ⊆ S) (hQ : wires Q ⊆ S) (a b ta tb : State) (m1 m2 : List Bool)
    (hpa : ta.phase = a.phase) (hma : ∀ q ∈ S, ta.basis q = a.basis (f q))
    (hpb : tb.phase = b.phase) (hmb : ∀ q ∈ S, tb.basis q = b.basis (f q))
    (eq : run P m1 ta = run Q m2 tb) (hout : ∀ q, q ∉ S.image f → a.basis q = b.basis q) :
    run (renameProgram f P) m1 a = run (renameProgram f Q) m2 b := by
  have A := run_rename_pool f S inj P hP m1 ta a hpa hma
  have B := run_rename_pool f S inj Q hQ m2 tb b hpb hmb
  rw [eq] at A
  apply State.extensionality
  · exact A.1.trans B.1.symm
  funext q
  by_cases im : q ∈ S.image f
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp im
    exact (A.2 c hc).trans (B.2 c hc).symm
  · rw [run_rename_pool_outside f S P hP m1 a q im, run_rename_pool_outside f S Q hQ m2 b q im]
    exact hout q im

/-- The comparison leaves the flag and nothing else. -/
theorem compare_post (k X : Nat) (hk : k < ECDSAAdd.p) (hX : X < ECDSAAdd.p) (s : State) (m : List Bool)
    (hx : regValue (xR base) s.basis = X) (hs : regValue (srcR base) s.basis = 0)
    (hf : s.basis (base 514) = false) (hc : s.basis (base 513) = false)
    (hcarry : ∀ q ∈ cR base, s.basis q = false) :
    run (comparePart base (base 2400) k) m s =
      put s (base 514) (if s.basis (base 2400) then decide (EntryFuseArithmetic.prime ≤ X + k) else false) := by
  let K := compareLayout base
  have hw := compareLayout_widths base
  have hn := compareLayout_nodup
  have primeBound : X < EntryFuseArithmetic.prime := by rw [EntryFuse.prime_eq_secp]; exact hX
  have kBound : k < EntryFuseArithmetic.prime := by rw [EntryFuse.prime_eq_secp]; exact hk
  have pc : EntryFuseArithmetic.prime + complement = 2^256 := by
    norm_num [EntryFuseArithmetic.prime, modulus, complement]
  have initial : FastConst.Frame K s.basis 0 X false s.basis := ⟨hs, hx, hf, by intro q hq; rfl⟩
  have pre := EntryFuse.comparePrefix_correct hn 256 hw s.basis hcarry hc complement
    EntryFuseArithmetic.prime k X pc kBound primeBound s m initial
  have oe : comparePart base (base 2400) k = EntryFuse.comparePrefix K (base 2400) complement k := by
    rw [comparePart_eq]
    simp only [K, comparePrefixOld, loadNot, unloadNot, EntryFuse.comparePrefix, List.append_assoc]
  rw [oe]
  obtain ⟨ph, fr1, fr2, fr3, fr4⟩ := pre
  apply State.extensionality
  · exact ph
  · funext q
    by_cases q1 : q = base 514
    · subst q1
      have : (run (EntryFuse.comparePrefix K (base 2400) complement k) m s).basis K.flag = _ := fr3
      simpa [put, writeBit, K, compareLayout] using this
    · have r : (put s (base 514) (if s.basis (base 2400) then decide (EntryFuseArithmetic.prime ≤ X + k) else false)).basis q = s.basis q := by
        simp [put, writeBit, q1]
      rw [r]
      by_cases q2 : q ∈ K.src
      · exact (regValue_eq_iff K.src _ _).mp (fr1.trans hs.symm) q q2
      by_cases q3 : q ∈ K.out
      · exact (regValue_eq_iff K.out _ _).mp (fr2.trans hx.symm) q q3
      apply fr4
      simp only [FastConst.mutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨q2, q3⟩, q1⟩

/-- The X entry with the comparison replaced by reading the flag from `pk`. -/
def entryXNew (L : ControlledPointLayout) (pk : Wire) (k : Fp) : Program :=
  if k.val % 2 = 1 then
    swp pk (E1QubitPlacement.pmapR L (base 514)) ++
      renameProgram (E1QubitPlacement.pmapR L) (tailX base (base 2400) k.val)
  else
    renameProgram (E1QubitPlacement.pmapR L) [.CCX (base 2400) (base 770) (base 721)] ++
      (swp pk (E1QubitPlacement.pmapR L (base 514)) ++
        renameProgram (E1QubitPlacement.pmapR L) (evenTail k.val))

/-- Facts about the pulled state that the X entry needs. -/
structure Pulled (t : State) (X : Nat) : Prop where
  xval : regValue (xR base) t.basis = X
  src : regValue (srcR base) t.basis = 0
  f514 : t.basis (base 514) = false
  f513 : t.basis (base 513) = false
  f721 : t.basis (base 721) = false
  f1028 : t.basis (base 1028) = false
  carry : ∀ q ∈ cR base, t.basis q = false

theorem tailX_S (k : Nat) : wires (tailX base (base 2400) k) ⊆ E1QubitPlacement.S := by
  have h := E1QubitPlacement.merged_S k
  rw [merged_split, wires_append] at h
  exact Finset.union_subset_right h

theorem compare_S (k : Nat) : wires (comparePart base (base 2400) k) ⊆ E1QubitPlacement.S := by
  have h := E1QubitPlacement.merged_S k
  rw [merged_split, wires_append] at h
  exact Finset.union_subset_left h

theorem evenTail_S (k : Nat) : wires (evenTail k) ⊆ E1QubitPlacement.S :=
  (evenTail_wires k).trans (tailX_S k)

theorem run_pad (A B : Program) (m : List Bool) (s : State) :
    run (A ++ B) (List.replicate (measurementCount A) false ++ m) s =
      run B m (run A (List.replicate (measurementCount A) false) s) := by
  rw [run_append]
  congr 1
  · simp
  · rw [← run_take A _ s]
    congr 1
    simp

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pulled_facts (X : Fp) (u : State) (hx : regValue L.point.x u.basis = X.val)
    (hc : regValue L.dialogPool u.basis = 0) :
    Pulled (pullState (E1QubitPlacement.pmapR L) u) X.val := by
  have pool := E1QubitPlacement.pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := E1QubitPlacement.pmapR L
  let t := pullState F u
  have clean (q : Wire) (hq : q ∈ E1QubitPlacement.S) (notx : q ∉ wireBlock base 770 256)
      (notg : q ≠ base 2400) : t.basis q = false := hzero _ (pool q hq notx notg)
  have inS (i : Nat) (hi : i < 515 ∨ i = 721 ∨ i = 1028) : base i ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i (by omega))
  have notx (i : Nat) (hi : i < 770 ∨ 1026 ≤ i) : base i ∉ wireBlock base 770 256 := by
    intro H
    obtain ⟨j, hj, e⟩ := List.mem_map.mp H
    have E := base_injective e
    simp only [List.mem_range'_1] at hj
    omega
  have cl (i : Nat) (hi : i < 515 ∨ i = 721 ∨ i = 1028) : t.basis (base i) = false :=
    clean _ (inS i hi) (notx i (by omega)) (fun E => by have e := base_injective E; omega)
  refine ⟨?_, ?_, cl 514 (by omega), cl 513 (by omega), cl 721 (by simp), cl 1028 (by simp), ?_⟩
  · change regValue (wireBlock base 770 256) (fun q => u.basis (F q)) = X.val
    rw [E1QubitPlacement.regValue_pull, E1QubitPlacement.pmap_x L hw hn, hx]
  · apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (Or.inl (by omega))
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (Or.inl (by omega))

/-- Renamed comparison: only the flag wire changes. -/
theorem compare_rename (X k : Fp) (u : State) (hx : regValue L.point.x u.basis = X.val)
    (hc : regValue L.dialogPool u.basis = 0) (m : List Bool) :
    run (renameProgram (E1QubitPlacement.pmapR L) (comparePart base (base 2400) k.val)) m u =
      put u (E1QubitPlacement.pmapR L (base 514))
        (if u.basis L.core.generic then decide (prime ≤ X.val + k.val) else false) := by
  have P := pulled_facts L hw hn X u hx hc
  have inj := E1QubitPlacement.pmap_inj L hw hn
  let F := E1QubitPlacement.pmapR L
  let t := pullState F u
  have s514 : base 514 ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 514 (by omega))
  have C := compare_post k.val X.val k.isLt X.isLt t m P.xval P.src P.f514 P.f513 P.carry
  have tg : t.basis (base 2400) = u.basis L.core.generic := by
    change u.basis (F (base 2400)) = _
    have e : F (base 2400) = L.core.generic := E1QubitPlacement.pmap_g L hw hn
    rw [e]
  rw [tg] at C
  have A := run_rename_pool F E1QubitPlacement.S inj _ (compare_S k.val) m t u rfl (by intro q hq; rfl)
  rw [C] at A
  apply State.extensionality
  · exact A.1
  funext q
  by_cases im : q ∈ E1QubitPlacement.S.image F
  · obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp im
    rw [A.2 c hc']
    by_cases e : c = base 514
    · subst e; simp [put, writeBit, F]
    · have ne : F c ≠ F (base 514) := fun E => e (inj _ hc' _ s514 E)
      simp only [put, writeBit, Function.update_apply, e, if_false]
      show u.basis (F c) = _
      simp [F, ne]
  · rw [run_rename_pool_outside F E1QubitPlacement.S _ (compare_S k.val) m u q im]
    have ne : q ≠ F (base 514) := fun e => im (e ▸ Finset.mem_image_of_mem F s514)
    simp [put, writeBit, F] at ne ⊢
    simp [ne]

theorem entryXNew_run (pk : Wire) (X k : Fp) (u : State)
    (hx : regValue L.point.x u.basis = X.val) (hc : regValue L.dialogPool u.basis = 0)
    (hpk : pk ∈ L.dialogPool) (h514 : pk ≠ E1QubitPlacement.pmapR L (base 514))
    (h721 : pk ≠ E1QubitPlacement.pmapR L (base 721))
    (h770 : pk ≠ E1QubitPlacement.pmapR L (base 770))
    (h2400 : pk ≠ E1QubitPlacement.pmapR L (base 2400)) (m : List Bool) :
    run (entryXNew L pk k) m
        (put u pk (if u.basis L.core.generic then decide (prime ≤ X.val + k.val) else false)) =
      run (entryXAll L k)
        (List.replicate (measurementCount (comparePart base (base 2400) k.val)) false ++ m) u := by
  have inj := E1QubitPlacement.pmap_inj L hw hn
  have P := pulled_facts L hw hn X u hx hc
  set F := E1QubitPlacement.pmapR L with hFdef
  set f : Bool := if u.basis L.core.generic then decide (prime ≤ X.val + k.val) else false with hf
  let n := measurementCount (comparePart base (base 2400) k.val)
  let W := put u (F (base 514)) f
  have upk : u.basis pk = false := (regValue_zero _ _).mp hc pk hpk
  have u514 : u.basis (F (base 514)) = false := P.f514
  have u721 : u.basis (F (base 721)) = false := P.f721
  have u1028 : u.basis (F (base 1028)) = false := P.f1028
  have s514 : base 514 ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 514 (by omega))
  have s721 : base 721 ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 721 (by omega))
  have s1028 : base 1028 ∈ E1QubitPlacement.S :=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 1028 (by omega))
  have ctl := (tail_control_wires k.val).trans (tailX_S k.val)
  have s2400 : base 2400 ∈ E1QubitPlacement.S := ctl (by simp)
  have s770 : base 770 ∈ E1QubitPlacement.S := ctl (by simp)
  have Fne (i j : Nat) (hi : base i ∈ E1QubitPlacement.S) (hj : base j ∈ E1QubitPlacement.S)
      (hij : i ≠ j) : F (base i) ≠ F (base j) :=
    fun E => hij (base_injective (inj _ hi _ hj E))
  -- the old side
  have old : run (entryXAll L k) (List.replicate n false ++ m) u =
      run (renameProgram F (tailX base (base 2400) k.val)) m W := by
    rw [entryXAll_eq L hw hn X k u _ hx hc]
    change run (renameProgram F (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val)) _ u = _
    rw [merged_split]
    have e : renameProgram F (comparePart base (base 2400) k.val ++ tailX base (base 2400) k.val) =
        renameProgram F (comparePart base (base 2400) k.val) ++
          renameProgram F (tailX base (base 2400) k.val) := by
      simp [renameProgram, List.map_append]
    have cnt : measurementCount (renameProgram F (comparePart base (base 2400) k.val)) = n :=
      (renameProgram_counts _ _).2
    rw [e]
    have pad := run_pad (renameProgram F (comparePart base (base 2400) k.val))
      (renameProgram F (tailX base (base 2400) k.val)) m u
    rw [cnt] at pad
    rw [pad, compare_rename L hw hn X k u hx hc]
  rw [old]
  unfold entryXNew
  simp only [← hFdef]
  have mz : measurementCount (swp pk (F (base 514))) = 0 := by simp [swp, measurementCount]
  by_cases he : k.val % 2 = 1
  · rw [if_pos he, run_append, run_take]
    rw [mz, List.drop_zero]
    congr 1
    rw [swp_run pk _ h514 _ _ (by simpa [put, writeBit, Ne.symm h514] using u514)]
    apply State.extensionality
    · rfl
    funext q
    by_cases q1 : q = F (base 514)
    · subst q1; simp [put, writeBit, W, h514]
    · by_cases q2 : q = pk
      · subst q2; simp [put, writeBit, W, q1, upk]
      · simp [put, writeBit, W, q1, q2]
  · rw [if_neg he]
    have even : k.val % 2 = 0 := by omega
    let A := u.basis (F (base 2400)) && u.basis (F (base 770))
    let v := put u pk f
    have n7a : F (base 514) ≠ F (base 721) := Fne 514 721 s514 s721 (by decide)
    have n7b : F (base 514) ≠ F (base 2400) := Fne 514 2400 s514 s2400 (by decide)
    have n7c : F (base 514) ≠ F (base 770) := Fne 514 770 s514 s770 (by decide)
    have n7d : F (base 514) ≠ F (base 1028) := Fne 514 1028 s514 s1028 (by decide)
    have n7e : F (base 721) ≠ F (base 2400) := Fne 721 2400 s721 s2400 (by decide)
    have n7f : F (base 721) ≠ F (base 770) := Fne 721 770 s721 s770 (by decide)
    have c1 : ∀ mm, run (renameProgram F [.CCX (base 2400) (base 770) (base 721)]) mm v =
        put v (F (base 721)) A := by
      intro mm
      apply State.extensionality
      · rfl
      funext q
      by_cases q1 : q = F (base 721)
      · subst q1
        simp [renameProgram, renameInstr, run, put, writeBit, v, A, u721, Ne.symm h721, n7e, n7f,
          Ne.symm h2400, Ne.symm h770, h721, h2400, h770]
      · simp [renameProgram, renameInstr, run, put, writeBit, v, q1]
    have mc1 : measurementCount (renameProgram F [.CCX (base 2400) (base 770) (base 721)]) = 0 := by
      simp [renameProgram, renameInstr, measurementCount]
    rw [run_append, run_take, mc1, List.drop_zero, c1, run_append, run_take, mz, List.drop_zero]
    rw [swp_run pk _ h514 _ _ (by simp [put, writeBit, v, Ne.symm h514, n7a, u514])]
    have s3 : put (put (put v (F (base 721)) A) pk false) (F (base 514))
        ((put v (F (base 721)) A).basis pk) = put W (F (base 721)) A := by
      apply State.extensionality
      · rfl
      funext q
      by_cases q1 : q = F (base 514)
      · subst q1; simp [put, writeBit, W, v, h721, n7a, h514]
      · by_cases q2 : q = pk
        · subst q2; simp [put, writeBit, W, v, q1, upk, h721]
        · by_cases q3 : q = F (base 721)
          · subst q3; simp [put, writeBit, W, v, q1, q2]
          · simp [put, writeBit, W, v, q1, q2, q3]
    rw [s3]
    let tW := pullState F W
    have tg : tW.basis (base 2400) = u.basis (F (base 2400)) := by
      change W.basis (F (base 2400)) = _
      simp [W, put, writeBit, Ne.symm n7b]
    have tx : tW.basis (base 770) = u.basis (F (base 770)) := by
      change W.basis (F (base 770)) = _
      simp [W, put, writeBit, Ne.symm n7c]
    have ta : tW.basis (base 721) = false := by
      change W.basis (F (base 721)) = _
      simp [W, put, writeBit, Ne.symm n7a, u721]
    have tp : tW.basis (base 1028) = false := by
      change W.basis (F (base 1028)) = _
      simp [W, put, writeBit, Ne.symm n7d, u1028]
    have t514 : tW.basis (base 514) = f := by
      change W.basis (F (base 514)) = _
      simp [W, put, writeBit]
    have gen : F (base 2400) = L.core.generic := E1QubitPlacement.pmap_g L hw hn
    have wrap : tW.basis (base 514) = true → tW.basis (base 2400) = true := by
      intro h
      rw [t514] at h
      rw [tg, gen]
      cases hg : u.basis L.core.generic
      · simp [hf, hg] at h
      · rfl
    have key := evenTail_eq k.val even tW m ta tp wrap
    rw [tg, tx] at key
    symm
    apply rename_eq2 F E1QubitPlacement.S inj _ _ (tailX_S k.val) (evenTail_S k.val) W
      (put W (F (base 721)) A) tW (put tW (base 721) A) m m rfl (fun q _ => rfl) rfl
    · intro q hq
      by_cases e : q = base 721
      · subst e; simp [put, writeBit]
      · have ne : F q ≠ F (base 721) := fun E => e (inj _ hq _ s721 E)
        simp only [put, writeBit, Function.update_apply, e, ne, if_false]
        rfl
    · exact key.symm
    · intro q hq
      have ne : q ≠ F (base 721) := fun e => hq (e ▸ Finset.mem_image_of_mem F s721)
      simp [put, writeBit, ne]

end

/-- The new program from `s'` tracks the old one from `s` under the padded measurement list. -/
structure Pad (P' P : Program) (s' s : State) (pad : List Bool → List Bool) : Prop where
  run_eq : ∀ d, run P' d s' = run P (pad d) s
  drop_eq : ∀ d, (pad d).drop (measurementCount P) = d.drop (measurementCount P')

theorem run_false (p : Program) (m : List Bool) (j : Nat) (s : State) :
    run p (m ++ List.replicate j false) s = run p m s := by
  induction p generalizing m j s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t => simp only [run]; exact ih _ _ _
    | CX c t => simp only [run]; exact ih _ _ _
    | CCX a b t => simp only [run]; exact ih _ _ _
    | measureX t c₀ c₁ =>
      simp only [run]
      cases m with
      | nil =>
        cases j with
        | zero => rfl
        | succ j =>
          simp only [List.nil_append, List.replicate_succ, List.headD_cons, List.tail_cons,
            List.headD_nil, List.tail_nil]
          exact (ih [] j _)
      | cons b m =>
        simp only [List.cons_append, List.headD_cons, List.tail_cons]
        exact ih m j _

/-- Exactly `c` entries that act like `d` on a program with `c` measurements. -/
def pfx (c : Nat) (d : List Bool) : List Bool := (d ++ List.replicate c false).take c

theorem pfx_length (c : Nat) (d : List Bool) : (pfx c d).length = c := by
  simp [pfx]

theorem run_pfx (p : Program) (d : List Bool) (s : State) :
    run p (pfx (measurementCount p) d) s = run p d s := by
  rw [pfx, run_take, run_false]

theorem Pad.append {P' P : Program} {s' s : State} {pad : List Bool → List Bool}
    (h : Pad P' P s' s pad) (B : Program) : Pad (P' ++ B) (P ++ B) s' s pad := by
  constructor
  · intro d
    rw [run_append, run_take, run_append, run_take, h.drop_eq, h.run_eq]
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, h.drop_eq, List.drop_drop]

theorem Pad.prefix (A' A P' P : Program) (s' s : State) (pad : List Bool → List Bool)
    (hc : measurementCount A' = measurementCount A)
    (h : ∀ d, Pad P' P (run A' d s') (run A d s) pad) :
    Pad (A' ++ P') (A ++ P) s' s
      (fun d => pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))) := by
  have tk : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))).take
      (measurementCount A) = pfx (measurementCount A) d := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))).drop
      (measurementCount A) = pad (d.drop (measurementCount A)) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx, hc]
    exact (h d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h d).drop_eq, hc,
      List.drop_drop]

theorem Pad.prefixMeas (A' A P' P : Program) (s' s : State) (pad : List Bool → List Bool)
    (h : ∀ d, Pad P' P (run A' d s') (run A d s) pad) :
    Pad (A' ++ P') (A ++ P) s' s
      (fun d => pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))) := by
  have tk : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))).take
      (measurementCount A) = pfx (measurementCount A) d := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))).drop
      (measurementCount A) = pad (d.drop (measurementCount A')) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx]
    exact (h d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h d).drop_eq,
      List.drop_drop]

/-- Renaming carries a padded run when the extra wire is fixed. -/
theorem Pad.rename (f : Wire → Wire) (inj : Function.Injective f) (pk : Wire) (hfix : f pk = pk)
    (P' P : Program) (hw : pk ∈ wires P') (t : State) (v : Bool) (pad : List Bool → List Bool)
    (h : Pad P' P (put (pullState f t) pk v) (pullState f t) pad) :
    Pad (renameProgram f P') (renameProgram f P) (put t pk v) t pad := by
  constructor
  · intro d
    apply rename_eq2 f (wires P' ∪ wires P) (fun a _ b _ e => inj e) P' P
      Finset.subset_union_left Finset.subset_union_right (put t pk v) t
      (put (pullState f t) pk v) (pullState f t) d (pad d) rfl ?_ rfl (fun _ _ => rfl) (h.run_eq d)
    · intro q hq
      have ne : q ≠ pk := by
        intro e; subst e
        exact hq (Finset.mem_image.mpr ⟨q, Finset.mem_union_left _ hw, hfix⟩)
      simp [put, writeBit, ne]
    · intro q _
      by_cases e : q = pk
      · subst e; simp [put, writeBit, hfix]
      · have ne : f q ≠ pk := fun E => e (inj (E.trans hfix.symm))
        simp only [put, writeBit, Function.update_apply, e, ne, if_false]
        rfl
  · intro d
    rw [(renameProgram_counts _ _).2, (renameProgram_counts _ _).2]
    exact h.drop_eq d

/-- The pool site that holds the comparison flag between the input stage and the X entry. -/
def pkW (L : ControlledPointLayout) : Wire := L.core.poolWire 724

def genericNew (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ((entryYAll L (-cy) ++ entryXNew L (pkW L) (-cx)) ++ ParityStageBothInverse23.restEntry L) ++
    ParityStageBothInverse23.secondStageAll L (ReflectionE1.correction cx) cy cx

theorem entryXNew_measure (L : ControlledPointLayout) (pk : Wire) (k : Fp) :
    measurementCount (entryXAll L k) =
      measurementCount (comparePart base (base 2400) k.val) + measurementCount (entryXNew L pk k) := by
  have o := (entryXAll_counts L k).2.1
  have e : measurementCount (E1QubitPlacement.entryM L k) =
      measurementCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val) := by
    unfold E1QubitPlacement.entryM
    exact (renameProgram_counts _ _).2
  rw [o, e, merged_split, measurementCount_append]
  unfold entryXNew
  have sw0 : ∀ a, measurementCount (swp pk a) = 0 := by intro a; simp [swp, measurementCount]
  split_ifs
  · rw [measurementCount_append, sw0, (renameProgram_counts _ _).2]; omega
  · rw [measurementCount_append, measurementCount_append, sw0, (renameProgram_counts _ _).2,
      (renameProgram_counts _ _).2, (evenTail_counts _).2.1]
    simp [measurementCount]

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem pk_pool : pkW L ∈ L.dialogPool := Square5Placement.pool_member L hw 724 (by omega)

theorem pool_take (n i : Nat) (hn' : n ≤ 2613) (hi : n ≤ i) (hi2 : i < 2613) :
    L.core.poolWire i ∉ L.dialogPool.take n := by
  rw [pool_block L hw n hn']
  intro h
  obtain ⟨j, hj, e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  have := pool_inj L hw hn j i (by omega) hi2 e
  omega

theorem pk_not_K : pkW L ∉ (L.recoveryConstant L.point.y).wires := by
  have hp := pk_pool L hw
  have not512 : pkW L ∉ L.dialogPool.take 512 := pool_take L hw hn 512 724 (by omega) (by omega) (by omega)
  have split : L.dialogPool.take 512 = L.dialogPool.take 256 ++ (L.dialogPool.drop 256).take 256 := by
    rw [show (512:Nat) = 256 + 256 from rfl, List.take_add]
  rw [split] at not512
  simp only [List.mem_append, not_or] at not512
  have ne (i : Nat) (hi : i < 2613) (hne : i ≠ 724) : pkW L ≠ L.core.poolWire i :=
    fun e => hne (pool_inj L hw hn i 724 hi (by omega) e.symm)
  intro h3
  change pkW L ∈ L.dialogPool.take 256 ++ L.point.y ++ (L.dialogPool.drop 256).take 256 ++
    [L.core.poolWire 512, L.core.poolWire 513, L.core.poolWire 514] at h3
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h3
  rcases h3 with ((e | e) | e) | e | e | e
  · exact not512.1 e
  · exact ((E1QubitPlacement.lay L hw hn _).2.1 hp).2 e
  · exact not512.2 e
  · exact ne 512 (by omega) (by omega) e
  · exact ne 513 (by omega) (by omega) e
  · exact ne 514 (by omega) (by omega) e

theorem pk_not_Y (k : Fp) (hg : pkW L ≠ L.core.generic) : pkW L ∉ wires (entryYAll L k) := by
  intro h
  have sub := (entryYAll_wires L hw k).trans (EntryFuse.fusedY_support L hw k)
  have h2 := Finset.mem_of_subset sub h
  rcases List.mem_cons.mp (List.mem_toFinset.mp h2) with e | e
  · exact hg e
  · exact pk_not_K L hw hn e

theorem pk_ne_flag : pkW L ≠ E1QubitPlacement.pmapR L (base 514) := by
  have e : E1QubitPlacement.pmapR L (base 514) = L.core.poolWire 514 := by
    unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
    rw [E1QubitPlacement.rho_base, E1QubitPlacement.sig_base]
    rfl
  rw [e]
  exact fun E => absurd (pool_inj L hw hn 724 514 (by omega) (by omega) E) (by omega)

theorem pk_ne_high : pkW L ≠ E1QubitPlacement.pmapR L (base 721) := by
  have e : E1QubitPlacement.pmapR L (base 721) = L.core.poolWire 723 := by
    unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
    rw [E1QubitPlacement.rho_base, E1QubitPlacement.sig_base]
    rfl
  rw [e]
  exact fun E => absurd (pool_inj L hw hn 724 723 (by omega) (by omega) E) (by omega)

theorem pk_ne_x : pkW L ≠ E1QubitPlacement.pmapR L (base 770) := by
  have hp := pk_pool L hw
  intro E
  apply ((E1QubitPlacement.lay L hw hn _).2.1 hp).1
  rw [E, ← E1QubitPlacement.pmap_x L hw hn]
  exact List.mem_map.mpr ⟨base 770, List.mem_map.mpr ⟨770, by simp [List.mem_range'_1], rfl⟩, rfl⟩

theorem generic_pad (cx cy X Y : Fp) (s : State)
    (hX : regValue L.point.x s.basis = X.val) (hY : regValue L.point.y s.basis = Y.val)
    (hc : regValue L.dialogPool s.basis = 0) (hg : pkW L ≠ L.core.generic) :
    Pad (genericNew L cx cy) (ParityStageBothInverse23.genericAll L cx cy)
      (put s (pkW L) (if s.basis L.core.generic then decide (prime ≤ X.val + (-cx).val) else false)) s
      (fun d => pfx (measurementCount (entryYAll L (-cy))) d ++
        (List.replicate (measurementCount (comparePart base (base 2400) (-cx).val)) false ++
          d.drop (measurementCount (entryYAll L (-cy))))) := by
  have inner := Pad.prefix (entryYAll L (-cy)) (entryYAll L (-cy)) (entryXNew L (pkW L) (-cx))
    (entryXAll L (-cx))
    (put s (pkW L) (if s.basis L.core.generic then decide (prime ≤ X.val + (-cx).val) else false)) s
    (fun d => List.replicate (measurementCount (comparePart base (base 2400) (-cx).val)) false ++ d) rfl (by
      intro d
      rw [run_put _ _ _ _ _ (pk_not_Y L hw hn _ hg)]
      have eY := entryYAll_eq L hw hn Y (-cy) s d hY hc
      have fy := EntryFuse.fusedY_correct L hw hn Y (-cy) s d hY hc
      rw [eY]
      generalize hu : run (EntryFuse.fusedY L (-cy)) d s = u at fy
      have tx : regValue L.point.x u.basis = X.val := by
        rw [regValue_congr _ _ s.basis (fun q hq => fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)), hX]
      have tc : regValue L.dialogPool u.basis = 0 := by
        rw [regValue_congr _ _ s.basis (fun q hq => fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)), hc]
      have tg : u.basis L.core.generic = s.basis L.core.generic :=
        fy.2.2 _ ((E1QubitPlacement.lay L hw hn _).2.2 rfl).2
      rw [← tg]
      constructor
      · intro d'
        exact entryXNew_run L hw hn (pkW L) X (-cx) u tx tc (pk_pool L hw) (pk_ne_flag L hw hn)
          (pk_ne_high L hw hn) (pk_ne_x L hw hn)
          (by rw [E1QubitPlacement.pmap_g L hw hn]; exact hg) d'
      · intro d'
        rw [entryXNew_measure L (pkW L) (-cx), ← List.drop_drop, List.drop_left' (by simp)])
  exact (inner.append _).append _

end

end ECDSAAdd.Entrant.FlagEntry

namespace ECDSAAdd.Entrant.FlagTop
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out

attribute [local irreducible] layout

/-- The composite wire map of the generic block. -/
def rho (L : ControlledPointLayout) (q : Wire) : Wire :=
  swapD L (swapE L (tauM L (Wrapper5.U L (swapF L q))))

theorem ren_eq (L : ControlledPointLayout) (P : Program) :
    renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L)
      (renameProgram (Wrapper5.U L) (renameProgram (swapF L) P)))) = renameProgram (rho L) P := by
  simp only [renameProgram_comp]
  rfl

theorem rho_injective : Function.Injective (rho layout) := by
  have hw := layout_widths
  have hn := layout_nodup
  intro a b e
  exact swapF_injective layout hw hn ((Wrapper5.U layout).injective
    (tauM_injective layout hn (swapE_injective layout hw hn (swapD_injective layout hw hn e))))

theorem flags_nodup : layout.inPlaceFlags.Nodup := by
  have hD := layout.dialogUsed_nodup layout_nodup
  unfold ControlledPointLayout.dialogUsedWires at hD
  exact (List.nodup_append.mp (List.nodup_append.mp hD).1).2.1

theorem U_apply (q : Wire) : Wrapper5.U layout q =
    if q = layout.core.poolWire 684 then layout.core.poolWire 717
    else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
  show (Equiv.swap _ _) q = _
  rw [Equiv.swap_apply_def]

theorem tauM_apply (q : Wire) : tauM layout q =
    if q = layout.core.generic then layout.genericSelect else
      if q = layout.genericSelect then layout.core.generic else q := rfl
theorem E_apply (q : Wire) : swapE layout q =
    if q = layout.core.equalNegY then spareWire layout
    else if q = spareWire layout then layout.core.equalNegY else q := rfl
theorem D_apply (q : Wire) : swapD layout q =
    if q = layout.doubleSelect then spareD layout
    else if q = spareD layout then layout.doubleSelect else q := rfl
theorem F_apply (q : Wire) : swapF layout q =
    if q = layout.point.finite then finSpare layout
    else if q = finSpare layout then layout.point.finite else q := rfl

/-- Off the wires the five swaps move, `rho` is the identity. -/
theorem rho_fix (q : Wire) (h1 : q ≠ layout.point.finite) (h2 : q ≠ finSpare layout)
    (h3 : q ≠ layout.core.poolWire 684) (h4 : q ≠ layout.core.poolWire 717)
    (h5 : q ≠ layout.core.generic) (h6 : q ≠ layout.genericSelect)
    (h7 : q ≠ layout.core.equalNegY) (h8 : q ≠ layout.doubleSelect) (h9 : q ≠ spareD layout) :
    rho layout q = q := by
  have h3' : q ≠ spareWire layout := h3
  unfold rho
  rw [F_apply, if_neg h1, if_neg h2, U_apply, if_neg h3, if_neg h4, tauM_apply, if_neg h5, if_neg h6,
    E_apply, if_neg h7, if_neg h3', D_apply, if_neg h8, if_neg h9]

theorem point_fix (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) : rho layout q = q := by
  have hw := layout_widths
  have flag (w : Wire) (hw' : w ∈ layout.inPlaceFlags) : q ≠ w := fun e => flags_not_point _ hw' (e ▸ hq)
  have pool (w : Wire) (hw' : w ∈ layout.dialogPool) : q ≠ w := fun e => pool_not_point _ hw' (e ▸ hq)
  apply rho_fix
  · exact fun e => finite_not_flag.2 (e ▸ hq)
  · exact pool _ (finSpare_pool layout hw)
  · exact pool _ (Square5Placement.pool_member layout hw 684 (by omega))
  · exact pool _ (Square5Placement.pool_member layout hw 717 (by omega))
  · exact flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pool _ (spareD_pool layout hw)

theorem rho_generic : rho layout layout.core.generic = layout.genericSelect := by
  have hw := layout_widths
  have hn := layout_nodup
  have fn := flags_nodup
  simp only [ControlledPointLayout.inPlaceFlags, List.nodup_cons, List.mem_cons, not_or,
    List.not_mem_nil, or_false] at fn
  have gp (q : Wire) (hq : q ∈ layout.dialogPool) : layout.core.generic ≠ q :=
    fun e => pool_not_flag _ hq (e ▸ by simp [ControlledPointLayout.inPlaceFlags])
  have sp (q : Wire) (hq : q ∈ layout.dialogPool) : layout.genericSelect ≠ q :=
    fun e => pool_not_flag _ hq (e ▸ by simp [ControlledPointLayout.inPlaceFlags])
  unfold rho
  rw [F_apply, if_neg (Ne.symm (fin_ne_generic layout hn)),
    if_neg (gp _ (finSpare_pool layout hw)),
    U_apply, if_neg (gp _ (Square5Placement.pool_member layout hw 684 (by omega))),
    if_neg (gp _ (Square5Placement.pool_member layout hw 717 (by omega))),
    tauM_apply, if_pos rfl, E_apply, if_neg (by tauto), if_neg (sp _ (spare_pool layout hw)),
    D_apply, if_neg (by tauto), if_neg (sp _ (spareD_pool layout hw))]

/-- Pool sites pull back to the clean flags and pool sites. -/
theorem rho_pool (t : State) (hf : t.basis layout.point.finite = false)
    (hE : t.basis layout.core.equalNegY = false) (hD : t.basis layout.doubleSelect = false)
    (hclean : regValue layout.dialogPool t.basis = 0) (q : Wire) (hq : q ∈ layout.dialogPool) :
    t.basis (rho layout q) = false := by
  have hw := layout_widths
  have hn := layout_nodup
  have pc : ∀ a ∈ layout.dialogPool, t.basis a = false := fun a ha => (regValue_zero _ _).mp hclean a ha
  have fn := flags_nodup
  simp only [ControlledPointLayout.inPlaceFlags, List.nodup_cons, List.mem_cons, not_or,
    List.not_mem_nil, or_false] at fn
  have pf (a : Wire) (ha : a ∈ layout.dialogPool) (b : Wire) (hb : b ∈ layout.inPlaceFlags) : a ≠ b :=
    fun e => pool_not_flag a ha (e ▸ hb)
  have pfin (a : Wire) (ha : a ∈ layout.dialogPool) : a ≠ layout.point.finite :=
    fun e => (out_pool_off a ha).1 e
  have fl (b : Wire) (hb : b ∈ layout.inPlaceFlags) : layout.point.finite ≠ b :=
    fun e => finite_not_flag.1 (e ▸ hb)
  have mE : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have mD : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have mG : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have mS : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have s1 := finSpare_pool layout hw
  have s2 := Square5Placement.pool_member layout hw 684 (by omega)
  have s3 := Square5Placement.pool_member layout hw 717 (by omega)
  have s4 := spareD_pool layout hw
  have s5 := spare_pool layout hw
  -- the last three swaps on a pool site
  have last (a : Wire) (ha : a ∈ layout.dialogPool) :
      t.basis (swapD layout (swapE layout (tauM layout a))) = false := by
    rw [tauM_apply, if_neg (pf a ha _ mG), if_neg (pf a ha _ mS), E_apply, if_neg (pf a ha _ mE)]
    by_cases e1 : a = spareWire layout
    · rw [if_pos e1, D_apply, if_neg (by tauto), if_neg (Ne.symm (pf _ s4 _ mE))]
      exact hE
    · rw [if_neg e1, D_apply, if_neg (pf a ha _ mD)]
      by_cases e2 : a = spareD layout
      · rw [if_pos e2]; exact hD
      · rw [if_neg e2]; exact pc a ha
  unfold rho
  rw [F_apply, if_neg (pfin q hq)]
  by_cases e0 : q = finSpare layout
  · rw [if_pos e0, U_apply, if_neg (fun e => pfin _ s2 e.symm), if_neg (fun e => pfin _ s3 e.symm),
      tauM_apply, if_neg (fl _ mG), if_neg (fl _ mS), E_apply, if_neg (fl _ mE),
      if_neg (fun e => pfin _ s5 e.symm), D_apply, if_neg (fl _ mD), if_neg (fun e => pfin _ s4 e.symm)]
    exact hf
  · rw [if_neg e0]
    have ua : Wrapper5.U layout q ∈ layout.dialogPool := by
      rw [U_apply]
      split_ifs
      · exact s3
      · exact s2
      · exact hq
    exact last _ ua

theorem pk_ne_pool (i : Nat) (hi : i < 2613) (hne : i ≠ 724) : pkW layout ≠ layout.core.poolWire i :=
  fun e => hne (pool_inj layout layout_widths layout_nodup i 724 hi (by omega) e.symm)

theorem pk_flag (b : Wire) (hb : b ∈ layout.inPlaceFlags) : pkW layout ≠ b :=
  fun e => pool_not_flag _ (pk_pool layout layout_widths) (e ▸ hb)

theorem rho_pk : rho layout (pkW layout) = pkW layout := by
  apply rho_fix
  · exact (out_pool_off _ (pk_pool layout layout_widths)).1
  · exact pk_ne_pool 1400 (by omega) (by omega)
  · exact pk_ne_pool 684 (by omega) (by omega)
  · exact pk_ne_pool 717 (by omega) (by omega)
  · exact pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact pk_ne_pool 1540 (by omega) (by omega)

/-- Everything `genericNew` needs of the pulled state. -/
theorem pulled_values (t : State) (X Y : Fp) (G : Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false) (hD : t.basis layout.doubleSelect = false)
    (hclean : regValue layout.dialogPool t.basis = 0) :
    regValue layout.point.x (pullState (rho layout) t).basis = X.val ∧
    regValue layout.point.y (pullState (rho layout) t).basis = Y.val ∧
    (pullState (rho layout) t).basis layout.core.generic = G ∧
    regValue layout.dialogPool (pullState (rho layout) t).basis = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hx]; apply regValue_congr; intro q hq
    change t.basis (rho layout q) = _
    rw [point_fix q (List.mem_append_left _ hq)]
  · rw [← hy]; apply regValue_congr; intro q hq
    change t.basis (rho layout q) = _
    rw [point_fix q (List.mem_append_right _ hq)]
  · change t.basis (rho layout _) = _
    rw [rho_generic, hg]
  · apply (regValue_zero _ _).mpr
    intro q hq
    exact rho_pool t hf hE hD hclean q hq

end ECDSAAdd.Entrant.FlagTop

end

section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FlagTop
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out ZeroFill ParityEven
  ParityUniform E1Merge NativeFirstDirect MappedCompressed ParityXEntry

attribute [local irreducible] layout

/-- The input stage with the comparison flag extracted into `pk`. -/
def stageNew (L : ControlledPointLayout) (C : Point) (pk : Wire) : Program :=
  FiniteFlagInterval.zrep L ++
  classifierF (triOf C) (yBit (dialogExceptionPoint C)) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0)
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) L.point.finite pk

theorem stageNew_run [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary L R b (fun _ => false) s.basis)
    (pk : Wire) (hpP : pk ∈ L.dialogPool) (hpW : pk ∉ L.dialogPool.take 253)
    (h3 : pk ≠ L.dialogPool.getD 253 0) (h4 : pk ≠ L.dialogPool.getD 254 0)
    (h5 : pk ≠ L.dialogPool.getD 255 0) (h6 : pk ≠ L.point.finite) (h7 : pk ≠ L.genericSelect)
    (h8 : pk ∉ L.point.x) :
    run (stageNew L (.some hc) pk) m s =
      put (run (stage L (.some hc)) m s) pk
        ((run (stage L (.some hc)) m s).basis L.genericSelect &&
          decide ((triOf (.some hc)).A < codeX R)) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout L hw hn
  have hp := (point_holds _ _ _).mp hs.point
  have v := triOf_valid hc
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have hpl := dialogPool_length L hw
  have Z := FiniteFlagInterval.zrep_run L hw hn s m
  unfold stageNew stage
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize hs1 : run (FiniteFlagInterval.zrep L) m s = s1 at Z ⊢
  have fx : L.point.finite ∉ L.point.x := (hextx _ (by simp)).1
  have gx : L.genericSelect ∉ L.point.x := (hextx _ (by simp)).1
  have hX : regValue L.point.x s1.basis = codeX R := by
    rw [Z.2.2, hp.2.1, hp.1]
    unfold codeX
    cases hf : pointFinite R
    · have hx0 : pointX R = 0 := by
        cases R with
        | zero => rfl
        | some h => simp [pointFinite] at hf
      simp [hx0]
    · simp
  have xbit : ∀ i, i < 256 → s1.basis (L.point.x.getD i 0) = (codeX R).testBit i := by
    intro i hi
    rw [← hX]; exact (LocalWireModel.reg_bit L.point.x s1.basis i (by rw [hxl]; exact hi)).symm
  have s1f : s1.basis L.point.finite = pointFinite R := (Z.2.1 _ fx).trans hp.1
  have s1g : s1.basis L.genericSelect = false := (Z.2.1 _ gx).trans
    (hs.flags _ (by simp [ControlledPointLayout.inPlaceFlags]))
  have s1p : ∀ q, q ∈ L.dialogPool → q ∉ L.point.x → s1.basis q = false := by
    intro q hq hx; rw [Z.2.1 _ hx]; exact (regValue_zero _ _).mp hs.clean q hq
  have pget (i : Nat) (hi : i < 2613) : L.dialogPool.getD i 0 ∈ L.dialogPool := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hz : (∀ q ∈ L.dialogPool.take 253, s1.basis q = false) ∧
      s1.basis (L.dialogPool.getD 253 0) = false ∧ s1.basis (L.dialogPool.getD 254 0) = false ∧
      s1.basis (L.dialogPool.getD 255 0) = false :=
    ⟨fun q hq => s1p q (List.mem_of_mem_take hq) (hdisj q hq),
      s1p _ (pget 253 (by omega)) (hextx _ (by simp)).1,
      s1p _ (pget 254 (by omega)) (hextx _ (by simp)).1,
      s1p _ (pget 255 (by omega)) (hextx _ (by simp)).1⟩
  have G := glue hc b R
  have hmb : matchBit (triOf (.some hc)) L.point.x s1.basis =
      (triOf (.some hc)).idx.all (fun i => (codeX R).testBit i ==
        (triOf (.some hc)).tgt i ((codeX R).testBit (triOf (.some hc)).r1,
          (codeX R).testBit (triOf (.some hc)).r2)) := by
    unfold matchBit
    rw [xbit _ pv.1, xbit _ pv.2.1, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    apply forall₂_congr
    intro i hi
    rw [xbit i (ix.2.2.2.2 i hi)]
  have hf' : s1.basis L.point.finite = !(matchBit (triOf (.some hc)) L.point.x s1.basis &&
      decide ((s1.basis (L.point.x.getD (triOf (.some hc)).r1 0),
        s1.basis (L.point.x.getD (triOf (.some hc)).r2 0)) = (triOf (.some hc)).pat (triOf (.some hc)).S)) := by
    rw [s1f, hmb, xbit _ pv.1, xbit _ pv.2.1]
    exact G.1
  have hx256 : codeX R < 2^256 := by
    unfold codeX
    split_ifs
    · exact pairCode_lt R
    · exact lt_trans FiniteFlagInterval.sentinel_lt (by norm_num [p])
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at hext
  obtain ⟨-, -, ⟨f1, f2, f3, f4⟩, ⟨g2, g3, g4⟩, ⟨a1, a2⟩, a3⟩ := hext
  have htmp : [L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0,
      L.point.finite, pk].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true, and_self]
    exact ⟨⟨a1, a2, Ne.symm f2, Ne.symm h3⟩, ⟨a3, Ne.symm f3, Ne.symm h4⟩, ⟨Ne.symm f4, Ne.symm h5⟩,
      Ne.symm h6⟩
  have htx : ∀ q ∈ [L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0,
      L.point.finite, pk], q ∉ L.point.x ∧ q ∉ L.dialogPool.take 253 ∧ q ≠ L.genericSelect := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm g2⟩
    · exact ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm g3⟩
    · exact ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm g4⟩
    · exact ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, f1⟩
    · exact ⟨h8, hpW, h7⟩
  have hto : ∀ q ∈ [L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0,
      L.point.finite, pk], q ≠ L.point.finite → s1.basis q = false := by
    intro q hq hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hz.2.1
    · exact hz.2.2.1
    · exact hz.2.2.2
    · exact absurd rfl hne
    · exact s1p _ hpP h8
  exact classifierF_run (triOf (.some hc)) v _ L.point.x (L.dialogPool.take 253) (yLow L) L.control
    L.point.finite L.genericSelect _ _ _ _ _ _ _ pk hxn hxl hwl hwn hdisj
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
        and_true, not_false_eq_true, and_self]
      have e := (stage_layout L hw hn).2.2.2.2.2.1
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
        and_true, not_false_eq_true, and_self] at e
      exact e)
    hextx htmp htx s1 _ s1g hz hf' hto (codeX R) hx256 xbit

/-- The comparison flag of the X entry, in the classifier's terms. -/
theorem flag_eq [DecidableEq Point] {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (R : Point) (X : Fp) (hX : X.val = codeX R) :
    (dialogOrdinary b R (.some hc) && decide ((triOf (.some hc)).A < codeX R)) =
      (if dialogOrdinary b R (.some hc) then
        decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false) := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have hxv : codeX (.some hr : Point) = x.val := rfl
      have hA : (triOf (.some hc)).A = cx.val := rfl
      have ne : x.val ≠ cx.val := fun e => den.1 (ZMod.val_injective _ e)
      have c0 : cx ≠ 0 := curve_x_ne_zero hc
      have nv : (-cx).val = p - cx.val := by
        rw [ZMod.neg_val, if_neg c0]
      have clt : cx.val < p := cx.isLt
      rw [hG, if_pos rfl, Bool.true_and, hxv, hA, hX, hxv, nv, EntryFuse.prime_eq_secp]
      apply decide_eq_decide.mpr
      omega
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp

theorem stageNew_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (pk : Wire) :
    toffoliCount (stageNew layout (.some hc) pk) ≤ 259 ∧
    measurementCount (stageNew layout (.some hc) pk) = 259 ∧
    Challenge.gateSlots (stageNew layout (.some hc) pk) ≤ 3619 + 1037 := by
  have c := classifierF_counts (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) layout.point.finite pk (by simp [dialogPool_length layout layout_widths])
  have z := FiniteFlagInterval.zrep_counts layout
  have zs := FiniteFlagInterval.zrep_slots layout layout_widths
  unfold stageNew
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append, z.1, z.2]
  have c1 := c.1
  have c2 := c.2.1
  have c3 := c.2.2
  refine ⟨by omega, by omega, by omega⟩

theorem stageNew_measure {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (pk : Wire) :
    measurementCount (stageNew layout (.some hc) pk) = measurementCount (stage layout (.some hc)) + 2 := by
  rw [(stageNew_counts hc pk).2.1, (stage_counts hc).2.1]

def finiteNew (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  stageNew L C (pkW L) ++ renameProgram (rho L) (genericNew L cx cy) ++ OutputOpt.outStage L C

def wrapperNew (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteNew L C cx cy)

theorem pk_wires (cx cy : Fp) : pkW layout ∈ wires (genericNew layout cx cy) := by
  have h : pkW layout ∈ wires (entryXNew layout (pkW layout) (-cx)) := by
    unfold entryXNew
    split_ifs
    · rw [wires_append]
      exact Finset.mem_union_left _ (by simp [swp, wires, Instr.wires])
    · rw [wires_append, wires_append]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simp [swp, wires, Instr.wires]))
  unfold genericNew
  simp only [wires_append, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr h))

theorem pk_stage :
    pkW layout ∈ layout.dialogPool ∧ pkW layout ∉ layout.dialogPool.take 253 ∧
    pkW layout ≠ layout.dialogPool.getD 253 0 ∧ pkW layout ≠ layout.dialogPool.getD 254 0 ∧
    pkW layout ≠ layout.dialogPool.getD 255 0 ∧ pkW layout ≠ layout.point.finite ∧
    pkW layout ≠ layout.genericSelect ∧ pkW layout ∉ layout.point.x := by
  have hw := layout_widths
  have hn := layout_nodup
  have hp := pk_pool layout hw
  have n256 : pkW layout ∉ layout.dialogPool.take 256 :=
    pool_take layout hw hn 256 724 (by omega) (by omega) (by omega)
  have ne (i : Nat) (hi : i < 256) : pkW layout ≠ layout.dialogPool.getD i 0 :=
    fun e => n256 (e ▸ pool_take_mem i hi)
  have tk : pkW layout ∉ layout.dialogPool.take 253 :=
    pool_take layout hw hn 253 724 (by omega) (by omega) (by omega)
  refine ⟨hp, tk, ne 253 (by omega), ne 254 (by omega), ne 255 (by omega),
    (out_pool_off _ hp).1, (out_pool_off _ hp).2.1, ?_⟩
  exact fun h => pool_not_point _ hp (List.mem_append_left _ h)

open Classical in
theorem finite_pad {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    ∃ pad, Pad (finiteNew layout (.some hc) cx cy) (finiteProgramOpt layout (.some hc) cx cy) s s pad := by
  have hgen : pkW layout ≠ layout.core.generic :=
    pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  have key : ∀ d, Pad (renameProgram (rho layout) (genericNew layout cx cy))
      (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (genBlockOpt layout cx cy))))
      (run (stageNew layout (.some hc) (pkW layout)) d s) (run (stage layout (.some hc)) d s)
      (fun d => pfx (measurementCount (entryYAll layout (-cy))) d ++
        (List.replicate (measurementCount (comparePart base (base 2400) (-cx).val)) false ++
          d.drop (measurementCount (entryYAll layout (-cy))))) := by
    intro d
    obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s d hs
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := pk_stage
    rw [stageNew_run layout layout_widths layout_nodup hc b R s d hs (pkW layout) p1 p2 p3 p4 p5 p6 p7 p8]
    have hp := (point_holds _ _ _).mp hs.point
    generalize ht1 : run (stage layout (.some hc)) d s = t1 at m1 m2 m3 m4 m5 ⊢
    have gsx := gsel_off
    have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
        (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
    have t1y : regValue layout.point.y t1.basis = pointY R := by
      rw [← hp.2.2]; apply regValue_congr; intro q hq
      exact m5 q (y_not_x layout layout_nodup q hq)
        (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
    have hE : t1.basis layout.core.equalNegY = false := by
      obtain ⟨a, b', c, d'⟩ := out_off layout.core.equalNegY (by simp)
      rw [t1off _ a b' c d']; exact hs.flags _ (by simp [flags_list])
    have hD : t1.basis layout.doubleSelect = false := by
      obtain ⟨a, b', c, d'⟩ := out_off layout.doubleSelect (by simp)
      rw [t1off _ a b' c d']; exact hs.flags _ (by simp [flags_list])
    have hclean : regValue layout.dialogPool t1.basis = 0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
      rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
        (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
      exact (regValue_zero _ _).mp hs.clean q hq
    obtain ⟨X, Y, hXv, hYv⟩ : ∃ X Y : Fp, X.val = codeX R ∧ Y.val = pointY R := by
      cases R with
      | zero => exact ⟨(FiniteFlagInterval.sentinel : Fp), 0, FiniteFlagInterval.sentinel_val, rfl⟩
      | @some x y hr => exact ⟨x, y, rfl, rfl⟩
    rw [m4, flag_eq hc b R X hXv]
    unfold genBlockOpt
    rw [ren_eq]
    apply Pad.rename (rho layout) rho_injective (pkW layout) rho_pk _ _ (pk_wires cx cy)
    have pvv := pulled_values t1 X Y (dialogOrdinary b R (.some hc)) (m2.trans hXv.symm)
      (t1y.trans hYv.symm) m3 m4 hE hD hclean
    have gp := generic_pad layout layout_widths layout_nodup cx cy X Y _ pvv.1 pvv.2.1 pvv.2.2.2 hgen
    rw [pvv.2.2.1] at gp
    exact gp
  have h := Pad.prefixMeas _ _ _ _ s s _ key
  exact ⟨_, h.append (OutputOpt.outStage layout (.some hc))⟩

open Classical in
theorem finite_run_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteNew layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteNew layout (.some hc) cx cy) m s).basis := by
  obtain ⟨pad, h⟩ := finite_pad hc b R s hs
  rw [h.run_eq m]
  exact finite_run hc b R s (pad m) hs

open Classical in
theorem wrapper_spec_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperNew layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run_new hc b R s m hs
  unfold wrapperNew
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h

theorem pk_eq (L : ControlledPointLayout) : pkW L = E1QubitPlacement.pmapR L (base 722) := by
  unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
  rw [E1QubitPlacement.rho_base, E1QubitPlacement.sig_base]
  rfl

theorem tailX_flags (k : Nat) : base 514 ∈ wires (tailX base (base 2400) k) ∧
    base 722 ∈ wires (tailX base (base 2400) k) := by
  simp only [tailX, prodPart, wires_append, Finset.mem_union]
  simp [wires, Instr.wires]

theorem evenTail_flags (k : Nat) : base 514 ∈ wires (evenTail k) ∧ base 722 ∈ wires (evenTail k) := by
  simp only [evenTail, wires_append, Finset.mem_union]
  simp [wires, Instr.wires]

theorem entryXNew_wires (L : ControlledPointLayout) (k : Fp) :
    wires (entryXNew L (pkW L) k) ⊆ wires (entryXAll L k) := by
  set F := E1QubitPlacement.pmapR L with hF
  have img : ∀ a, a ∈ wires (mergedAll k.val) → F a ∈ wires (entryXAll L k) := by
    intro a ha
    unfold entryXAll
    rw [renameProgram_support]
    exact Finset.mem_image_of_mem _ ha
  have sub : ∀ P : Program, wires P ⊆ wires (mergedAll k.val) →
      wires (renameProgram F P) ⊆ wires (entryXAll L k) := by
    intro P hP q hq
    rw [renameProgram_support] at hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact img a (hP ha)
  have swW : ∀ a b : Wire, a ∈ wires (entryXAll L k) → b ∈ wires (entryXAll L k) →
      wires (swp a b) ⊆ wires (entryXAll L k) := by
    intro a b ha hb
    simp [swp, wires, Instr.wires, Finset.insert_subset_iff, ha, hb]
  unfold entryXNew
  split_ifs with he
  · have inc : wires (tailX base (base 2400) k.val) ⊆ wires (mergedAll k.val) := by
      unfold mergedAll mergedOdd
      rw [if_pos he, if_pos he, wires_append]
      exact Finset.subset_union_right
    have f := tailX_flags k.val
    rw [wires_append]
    refine Finset.union_subset (swW _ _ ?_ (img _ (inc f.1))) (sub _ inc)
    rw [pk_eq L]
    exact img _ (inc f.2)
  · have inc : wires (evenTail k.val) ⊆ wires (mergedAll k.val) := by
      unfold mergedAll
      rw [if_neg he]
      unfold mergedEven
      rw [wires_append]
      exact Finset.subset_union_right
    have inc0 : wires [Instr.CCX (base 2400) (base 770) (base 721)] ⊆ wires (mergedAll k.val) := by
      unfold mergedAll
      rw [if_neg he]
      unfold mergedEven
      rw [wires_append, wires_append]
      exact Finset.subset_union_left.trans Finset.subset_union_left
    have f := evenTail_flags k.val
    rw [wires_append, wires_append]
    refine Finset.union_subset (sub _ inc0) (Finset.union_subset (swW _ _ ?_ (img _ (inc f.1))) (sub _ inc))
    rw [pk_eq L]
    exact img _ (inc f.2)

theorem genericNew_wires (L : ControlledPointLayout) (cx cy : Fp) :
    wires (genericNew L cx cy) ⊆ wires (ParityStageBothInverse23.genericAll L cx cy) := by
  simp only [genericNew, ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll,
    wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _) (entryXNew_wires L (-cx))) (Finset.Subset.refl _))
    (Finset.Subset.refl _)

theorem entryXNew_toffoli (L : ControlledPointLayout) (pk : Wire) (k : Fp) :
    toffoliCount (entryXNew L pk k) + 255 = toffoliCount (entryXAll L k) := by
  have o := (entryXAll_counts L k).1
  have e : toffoliCount (E1QubitPlacement.entryM L k) =
      toffoliCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val) := by
    unfold E1QubitPlacement.entryM
    exact (renameProgram_counts _ _).1
  have cp : toffoliCount (comparePart base (base 2400) k.val) = 256 := by
    have c := (compareLt_counts none (srcR base) (xR base) (cR base) (base 513) (base 514)
      (by simp [srcR, xR, wireBlock_length]) (by simp [cR, xR, wireBlock_length])).1
    have lx : (xR base).length = 256 := by simp [xR, wireBlock_length]
    rw [lx] at c
    simp only [comparePart, toffoliCount_append, (maskedConstant_counts _ _ _).1,
      (notRegister_counts _).1, c]
    rfl
  rw [e, merged_split, toffoliCount_append, cp] at o
  have sw0 : toffoliCount (swp pk (E1QubitPlacement.pmapR L (base 514))) = 0 := by
    simp [swp, toffoliCount]
  unfold entryXNew
  split_ifs
  · rw [toffoliCount_append, sw0, (renameProgram_counts _ _).1]; omega
  · rw [toffoliCount_append, toffoliCount_append, sw0, (renameProgram_counts _ _).1,
      (renameProgram_counts _ _).1]
    have t := (evenTail_counts k.val).1
    have c1 : toffoliCount [Instr.CCX (base 2400) (base 770) (base 721)] = 1 := by simp [toffoliCount]
    omega

theorem entryXNew_slots (L : ControlledPointLayout) (pk : Wire) (k : Fp) :
    Challenge.gateSlots (entryXNew L pk k) ≤ Challenge.gateSlots (entryXAll L k) + 2 := by
  have sw2 : Challenge.gateSlots (swp pk (E1QubitPlacement.pmapR L (base 514))) = 2 := by
    simp [swp, Challenge.gateSlots, Challenge.instructionSlots]
  have eo : Challenge.gateSlots (entryXAll L k) = Challenge.gateSlots (mergedAll k.val) := by
    unfold entryXAll
    exact rename_gateSlots _ _
  rw [eo]
  unfold entryXNew mergedAll
  split_ifs with he
  · unfold mergedOdd
    rw [if_pos he, Challenge.gateSlots_append, Challenge.gateSlots_append, sw2, rename_gateSlots]
    omega
  · unfold mergedEven
    rw [Challenge.gateSlots_append, Challenge.gateSlots_append, Challenge.gateSlots_append,
      Challenge.gateSlots_append, sw2, rename_gateSlots, rename_gateSlots]
    omega

theorem entryXNew_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (pk : Wire) (k : Fp) (h514 : pk ≠ E1QubitPlacement.pmapR L (base 514)) :
    GatePhysical (entryXNew L pk k) := by
  have inj := E1QubitPlacement.pmap_inj L hw hn
  have old := E1AffineEndpoints52Research.Forward.merged_physical base (base 2400)
    base_pool_nodup E1QubitPlacement.g2400 k.val
  rw [merged_split, gatePhysical_append] at old
  have tP := old.2
  have swP : GatePhysical (swp pk (E1QubitPlacement.pmapR L (base 514))) := by
    simp [swp, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, h514, Ne.symm h514]
  have lift : ∀ P : Program, wires P ⊆ E1QubitPlacement.S → GatePhysical P →
      GatePhysical (renameProgram (E1QubitPlacement.pmapR L) P) := by
    intro P hP hp
    exact gatePhysical_rename_support _ P (fun a ha b hb e => inj a (hP ha) b (hP hb) e) hp
  have ctl := (tail_control_wires k.val).trans (tailX_S k.val)
  unfold entryXNew
  split_ifs
  · rw [gatePhysical_append]
    exact ⟨swP, lift _ (tailX_S k.val) tP⟩
  · simp only [gatePhysical_append]
    refine ⟨lift _ ?_ ?_, swP, lift _ (evenTail_S k.val) (evenTail_physical k.val tP)⟩
    · simp only [wires, Instr.wires, Finset.union_empty]
      exact ctl
    · simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, base]

abbrev ioSet : Finset Wire := (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset

theorem finiteOpt_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteProgramOpt layout (.some hc) cx cy) =
      wires (stage layout (.some hc)) ∪
        wires (renameProgram (rho layout) (ParityStageBothInverse23.genericAll layout cx cy)) ∪
        wires (OutputOpt.outStage layout (.some hc)) := by
  unfold finiteProgramOpt genBlockOpt
  rw [ren_eq, wires_append, wires_append]

/-- Every wire of the new input stage is an input wire or already in the old program. -/
theorem stageNew_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (stageNew layout (.some hc) (pkW layout)) ⊆
      ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
  have st := stage_support hc
  have mem := stage_wires_mem hc
  have hstage : wires (stage layout (.some hc)) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inl (Or.inl hq))
  have pkIn : pkW layout ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    refine Or.inr (Or.inl (Or.inr ?_))
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_of_subset (genericNew_wires layout cx cy) (pk_wires cx cy), rho_pk⟩
  have mx : ∀ q ∈ layout.point.x, q ∈ ioSet := by
    intro q hq
    simp [ioSet, PointAddLayout.pointWires, hq]
  have mf : layout.point.finite ∈ ioSet := by simp [ioSet, PointAddLayout.pointWires]
  have tk : ∀ q ∈ layout.dialogPool.take 253, q ∈ layout.dialogPool.take 256 := by
    intro q hq
    have hpl := dialogPool_length layout layout_widths
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    rw [← e]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  have pool256 : ∀ q ∈ layout.dialogPool.take 256,
      q ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) :=
    fun q hq => hstage (mem.1 q hq)
  have gsel : layout.genericSelect ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) :=
    hstage mem.2
  have hcl : wires (classifier (triOf (.some hc)) (yBit (dialogExceptionPoint (.some hc))) layout.point.x
      (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
      (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)) ⊆
      ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    apply hstage
    unfold stage
    rw [wires_append]
    exact Finset.mem_union_right _ hq
  have hz : wires (FiniteFlagInterval.zrep layout) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    apply hstage
    unfold stage
    rw [wires_append]
    exact Finset.mem_union_left _ hq
  unfold stageNew
  rw [wires_append]
  refine Finset.union_subset hz ?_
  exact classifierF_wires _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ layout_widths.inputX _ hcl
    (fun q hq => Finset.mem_union_left _ (mx q hq)) (fun q hq => pool256 q (tk q hq))
    (pool256 _ (pool_take_mem 253 (by omega))) (pool256 _ (pool_take_mem 254 (by omega)))
    (pool256 _ (pool_take_mem 255 (by omega))) (Finset.mem_union_left _ mf) pkIn gsel

theorem finiteNew_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteNew layout (.some hc) cx cy) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
  have s := stageNew_wires (cx := cx) (cy := cy) hc
  unfold finiteNew
  rw [wires_append, wires_append]
  refine Finset.union_subset (Finset.union_subset s ?_) ?_
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    refine Or.inr (Or.inl (Or.inr ?_))
    rw [renameProgram_support]
    exact Finset.mem_image_of_mem _ (Finset.mem_of_subset (genericNew_wires layout cx cy) ha)
  · intro q hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inr hq)

theorem wrapperNew_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperNew layout (.some hc) cx cy) ⊆ ioSet ∪ wires (wrapperOpt layout (.some hc) cx cy) := by
  have k := finiteNew_wires (cx := cx) (cy := cy) hc
  have hw := layout_widths
  have fixIO : ∀ q ∈ ioSet, Wrapper5.U layout q = q := by
    intro q hq
    have hq' := List.mem_toFinset.mp hq
    have np := io_not_pool q hq'
    have n1 : q ≠ layout.core.poolWire 684 := by
      intro e; apply np; rw [e]; exact Square5Placement.pool_member layout hw 684 (by omega)
    have n2 : q ≠ layout.core.poolWire 717 := by
      intro e; apply np; rw [e]; exact Square5Placement.pool_member layout hw 717 (by omega)
    rw [U_apply, if_neg n1, if_neg n2]
  unfold wrapperNew wrapperOpt
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (k ha) with h | h
  · rw [fixIO a h]; exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

theorem support_used_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperNew layout (.some hc) cx cy) ⊆ layout.dialogUsedWires.toFinset := by
  refine (wrapperNew_wires hc).trans (Finset.union_subset ?_ (support_used hc))
  intro q hq
  apply List.mem_toFinset.mpr
  unfold ControlledPointLayout.dialogUsedWires
  simp only [List.mem_append]
  have := List.mem_toFinset.mp hq
  simp only [List.mem_append] at this
  tauto

theorem stageNew_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (stageNew layout (.some hc) (pkW layout)) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout layout layout_widths layout_nodup
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := pk_stage
  have old := classifier_physical (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) hxl hwl hxn hwn hdisj hext hextx
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at hext
  obtain ⟨-, -, ⟨f1, f2, f3, f4⟩, -, ⟨a1, a2⟩, a3⟩ := hext
  unfold stageNew
  rw [gatePhysical_append]
  refine ⟨FiniteFlagInterval.zrep_physical layout layout_nodup, ?_⟩
  exact classifierF_physical _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl
    ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm a1⟩
    ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, Ne.symm a2⟩
    ⟨(hextx _ (by simp)).1, (hextx _ (by simp)).2, f2⟩ a3 (Ne.symm f4) (Ne.symm p6) (Ne.symm p7) old

theorem wrapper_physical_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperNew layout (.some hc) cx cy) := by
  have old : GatePhysical (ParityStageBothInverse23.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0 := ParityStageBothInverse23.generic_physical layout layout_widths layout_nodup cx cy old
  simp only [ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll,
    gatePhysical_append] at p0
  have g : GatePhysical (genericNew layout cx cy) := by
    simp only [genericNew, gatePhysical_append]
    exact ⟨⟨⟨p0.1.1.1, entryXNew_physical layout layout_widths layout_nodup _ _
      (pk_ne_flag layout layout_widths layout_nodup)⟩, p0.1.2⟩, p0.2⟩
  unfold wrapperNew
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteNew, gatePhysical_append]
  exact ⟨⟨stageNew_physical hc, gatePhysical_rename _ rho_injective _ g⟩, OutputOpt.outStage_physical hc⟩

theorem genericNew_counts (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (genericNew L cx cy) + 255 = toffoliCount (ParityStageBothInverse23.genericAll L cx cy) ∧
    measurementCount (genericNew L cx cy) ≤ measurementCount (ParityStageBothInverse23.genericAll L cx cy) ∧
    Challenge.gateSlots (genericNew L cx cy) ≤
      Challenge.gateSlots (ParityStageBothInverse23.genericAll L cx cy) + 2 := by
  have t := entryXNew_toffoli L (pkW L) (-cx)
  have m := entryXNew_measure L (pkW L) (-cx)
  have s := entryXNew_slots L (pkW L) (-cx)
  simp only [genericNew, ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
  omega

theorem wrapperNew_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperNew layout (.some hc) cx cy) + 252 ≤
      toffoliCount (wrapperOpt layout (.some hc) cx cy) ∧
    measurementCount (wrapperNew layout (.some hc) cx cy) ≤
      measurementCount (wrapperOpt layout (.some hc) cx cy) + 2 ∧
    Challenge.gateSlots (wrapperNew layout (.some hc) cx cy) ≤
      Challenge.gateSlots (wrapperOpt layout (.some hc) cx cy) + 4658 := by
  have g := genericNew_counts layout cx cy
  have s := stageNew_counts hc (pkW layout)
  have o := stage_counts hc
  simp only [wrapperNew, wrapperOpt, finiteNew, finiteProgramOpt, genBlockOpt,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append,
    (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, rename_gateSlots]
  omega

open Classical in
theorem full_spec_new {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperNew layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec_new hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used_new hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programNew (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperNew layout C cx cy

def entryNew : Challenge.Entry := fun C=>normalizeProgram (programNew C)
def boundsNew : Challenge.Bounds := ⟨2150001,1498372,1587,50255906⟩

theorem program_correct_new (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programNew C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programNew,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec_new hc b R) (support_used_new hc)

theorem program_toffoli_new (C : Point) : toffoliCount (programNew C)≤2150001 := by
  cases C with
  | zero=>simp [programNew,toffoliCount]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_toffoli (.some hc)
    have delta:=(wrapperNew_metrics hc).1
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤_ at old
    change toffoliCount (wrapperNew layout (.some hc) cx cy)≤2150001
    omega

theorem program_measurements_new (C : Point) : measurementCount (programNew C)≤1498372 := by
  cases C with
  | zero=>simp [programNew,measurementCount]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_measurements (.some hc)
    have delta:=(wrapperNew_metrics hc).2.1
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperNew layout (.some hc) cx cy)≤1498372
    omega

theorem program_qubits_new (C : Point) : qubits (programNew C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_qubits (.some hc)
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperNew layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact Finset.mem_union_left _ h
    · rcases Finset.mem_union.mp (wrapperNew_wires hc h) with e | e
      · exact Finset.mem_union_left _ (io_mem q (List.mem_toFinset.mp e))
      · exact Finset.mem_union_right _ e

theorem program_physical_new (C : Point) : GatePhysical (programNew C) := by
  cases C with
  | zero=>simp [programNew,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical_new hc

theorem program_slots_new (C : Point) : Challenge.gateSlots (programNew C)≤50255906 := by
  cases C with
  | zero=>simp [programNew]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_slots (.some hc)
    have delta:=(wrapperNew_metrics hc).2.2
    change Challenge.gateSlots (wrapperOpt layout (.some hc) cx cy)≤50251248 at old
    change Challenge.gateSlots (wrapperNew layout (.some hc) cx cy)≤50255906
    omega

theorem certificateNew : Challenge.Certificate entryNew boundsNew where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct_new C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical_new C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli_new C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programNew C))≤1498372
    rw [normalize_measurements];exact program_measurements_new C
  qubits_le C:=by
    change qubits (normalizeProgram (programNew C))≤1587
    rw [normalize_qubits];exact program_qubits_new C
  gateSlots_le C:=by
    change Challenge.gateSlots (normalizeProgram (programNew C))≤50255906
    rw [normalize_slots];exact program_slots_new C

end ECDSAAdd.Entrant.FlagTop

end

section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
section
namespace ECDSAAdd.Entrant.ParityXExit
open Arithmetic Challenge RecordedQuantum NativeFirstDirect MappedCompressed E1Merge ExitMerge ParityCarry ParityConvert ParityEven
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The X exit up to the flag erase, the same for both parities of `k`. -/
def prefixAll (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  ExitMerge.fPart w g k++ExitMerge.eraseH w++ExitMerge.addPart w g k++
    rotateLeft (kR w)++ExitMerge.parBack w g k

/-- The X exit with the flag parked instead of erased. -/
def programN (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  prefixAll w g k++ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722)

theorem prefixAll_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC base,b0 q=false) (h1797 : b0 (base 1797)=false) :
    let G := b0 (base 2400)
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF base b0 (2*H+(!par).toNat) K 0 par false false false) (prefixAll base (base 2400) k)
      (MF base b0 0 Y 0 false (G && decide (k<X)) false false) := by
  intro G par H K Y
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  have gm := g_mut base (base 2400) hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by norm_num)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have s1 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par false false false (base 2400) (base 1028) 721 (by omega) G par
    (g_ne base hn (base 2400) hg 721 (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH base hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX base hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false (base 2400) G (g_ne base hn (base 2400) hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
  rw [←a3] at s4
  have s5 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 (base 2400)=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (base 514) (base 1028) 722 (by omega) f par
    (w_ne base hn _ _ (by omega) (by omega) (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  have s7 := stepW0Back base hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH base hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack base hn b0 K 0 par f (G && par) (f && par)
  have s10 := stepNegK base (base 2400) hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX base (base 2400) hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg] at s11
  have kWord : (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 := by
    rw [Nat.add_comm]; exact a5
  have s12 := stepKAddZero4 base hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par)
    hac h1797 Y a6 kWord
  rw [kWord] at s12
  have s13 := stepLoadKX base (base 2400) hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp base hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepMeasGp base (base 2400) hn b0 0 (Y/2) 0 par f false gm (g_ne base hn (base 2400) hg 721 (by omega))
  have s16 := stepRotL base hn b0 0 (Y/2) 0 par f false false (by rw [p_val] at a6; omega)
  have s17 := stepParBack base (base 2400) hn b0 k (Y/2) par f hg
  rw [show b0 (base 2400)=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  have t:=s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq s17)))))))))))))))
  unfold prefixAll ExitMerge.fPart ExitMerge.eraseH ExitMerge.addPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem MF_put_fp (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b : BasisState) (H X T : Nat)
    (par f gp fp v : Bool) (s : State) (hs : MF w b H X T par f gp fp s.basis) :
    MF w b H X T par f gp v (put s (w 722) v).basis := by
  have h := stepBit w hn b H X T par f gp fp s (put s (w 722) v) 722 (by omega) hs
    (fun q hq => by simp [put,writeBit,hq])
  simpa [put,writeBit] using h

theorem MF_put_f (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b : BasisState) (H X T : Nat)
    (par f gp fp v : Bool) (s : State) (hs : MF w b H X T par f gp fp s.basis) :
    MF w b H X T par v gp fp (put s (w 514) v).basis := by
  have h := stepBit w hn b H X T par f gp fp s (put s (w 514) v) 514 (by omega) hs
    (fun q hq => by simp [put,writeBit,hq])
  simpa [put,writeBit] using h

theorem swpStep (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b0 : BasisState) (H X T : Nat)
    (par f : Bool) :
    Triple (MF w b0 H X T par f false false)
      (ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722))
      (MF w b0 H X T par false false f) := by
  intro s m hs
  have ne : w 514≠w 722 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  rw [ECDSAAdd.Entrant.FlagEntry.swp_run _ _ ne s m hs.2.2.2.2.2.2.1]
  have h1 := MF_put_f w hn b0 H X T par f false false false s hs
  have h2 := MF_put_fp w hn b0 H X T par false false false (s.basis (w 514)) _ h1
  rw [hs.2.2.2.2.1] at h2 ⊢
  exact ⟨rfl,h2⟩

theorem programN_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC base,b0 q=false) (h1797 : b0 (base 1797)=false) :
    let G := b0 (base 2400)
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF base b0 (2*H+(!par).toNat) K 0 par false false false) (programN base (base 2400) k)
      (MF base b0 0 Y 0 false false false (G && decide (k<X))) := by
  intro G par H K Y
  exact (prefixAll_triple k hk b0 X hX hac h1797).seq (swpStep base base_pool_nodup b0 0 Y 0 false _)

/-- The parked exit ends in the old exit's state plus the flag on `w 722`. -/
theorem programN_pw (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (initial field : State) (mF m m' : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 X initial.basis)
    (ht : regValue (tR base) initial.basis=0) (h514 : initial.basis (base 514)=false)
    (h721 : initial.basis (base 721)=false) (h722 : initial.basis (base 722)=false)
    (hphase : field.phase=(run (NativeFirstDirect.forward base) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires base,
      field.basis q=(run (NativeFirstDirect.forward base) mF initial).basis q) :
    run (programN base (base 2400) k) m field =
      put (run (programAll base (base 2400) k) m' field) (base 722)
        (field.basis (base 2400) && decide (k<X)) := by
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec base hn X hX initial mF hin
  have e770 : initial.basis (base 770)=decide (X%2=1) := by
    have sp := kR_split base hn initial.basis
    have hb : regValue (kR base) initial.basis=X := hin.b
    rw [hb] at sp
    cases h : initial.basis (base 770) <;> simp [h] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  have inPool (a n : Nat) (ha : a+n≤1798) : ∀q∈wireBlock base a n,q∈skywalkPoolWires base :=
    blk_sub base a n 0 1798 (by omega) ha
  have wPool (i : Nat) (hi : i<1798) : base i∈skywalkPoolWires base :=
    List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have keepI (i : Nat) (hi : i < 1798) (h1 : 257 ≤ i) (h2 : i < 770 ∨ 1028 < i) :
      field.basis (base i)=initial.basis (base i) := by
    rw [hpool _ (wPool i hi)]
    apply zrest
    simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨nb base hn i 0 257 hi (by omega) (by omega),nb base hn i 770 258 hi (by omega) (by omega)⟩,
      w_ne base hn i 1028 hi (by omega) (by omega)⟩
  have hR0 : regValue (hR base) field.basis=
      2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat := by
    rw [regValue_congr (hR base) field.basis _ (fun q hq => hpool q (inPool 0 258 (by omega) q hq))]
    exact zh
  have kR0 : regValue (kR base) field.basis=(X/2+kConstant false (decide (X%2=1)))%2^258 := by
    rw [regValue_congr (kR base) field.basis _ (fun q hq => hpool q (inPool 770 258 (by omega) q hq))]
    exact zk
  have tR0 : regValue (tR base) field.basis=0 := by
    rw [regValue_congr (tR base) field.basis initial.basis (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact keepI i (by omega) (by omega) (by omega))]
    exact ht
  have f1028 : field.basis (base 1028)=decide (X%2=1) := (hpool _ (wPool 1028 (by omega))).trans z1028
  have f514 : field.basis (base 514)=false := (keepI 514 (by omega) (by omega) (by omega)).trans h514
  have f721 : field.basis (base 721)=false := (keepI 721 (by omega) (by omega) (by omega)).trans h721
  have f722 : field.basis (base 722)=false := (keepI 722 (by omega) (by omega) (by omega)).trans h722
  have hac : ∀q∈aC base,field.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [keepI i (by omega) (by omega) (by omega)]
    exact (regValue_zero _ _).mp hin.carry _ hq
  have h1797 : field.basis (base 1797)=false := (keepI 1797 (by omega) (by omega) (by omega)).trans hin.cin
  have mf0 : MF base field.basis (2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat)
      ((X/2+kConstant false (decide (X%2=1)))%2^258) 0 (decide (X%2=1)) false false false field.basis :=
    ⟨hR0,kR0,tR0,f1028,f514,f721,f722,fun _ _ => rfl⟩
  obtain ⟨n1,n2⟩ := programN_triple k hk field.basis X hX hac h1797 field m mf0
  obtain ⟨o1,o2⟩ := programAll_triple k hk field.basis X hX hac h1797 field m' mf0
  have o4 := MF_put_fp base hn field.basis _ _ _ _ _ _ _ (field.basis (base 2400) && decide (k<X)) _ o2
  apply State.extensionality
  · exact n1.trans o1.symm
  · exact MF_unique base _ _ _ _ _ _ _ _ _ _ n2 o4

theorem fPart_g (w : Nat → Wire) (g : Wire) (k : Nat) : g ∈ wires (ExitMerge.fPart w g k) := by
  have h : g ∈ wires [Instr.CCX g (w 1028) (w 721)] := by simp [wires,Instr.wires]
  unfold ExitMerge.fPart
  simp only [wires_append,Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))

theorem fin_add {P M X Y G : Finset Wire} (m : M ⊆ (X ∪ Y) ∪ G) : P ∪ M ⊆ ((P ∪ X) ∪ Y) ∪ G := by
  intro q h
  have m' := @m q
  simp only [Finset.mem_union] at h m' ⊢
  tauto

theorem fin_pre {A B C D E K R G : Finset Wire} (a : C ⊆ K ∪ G) (z : G ⊆ A) :
    (((A ∪ B) ∪ C) ∪ D) ∪ E ⊆ ((((A ∪ B) ∪ K) ∪ D) ∪ E) ∪ R := by
  intro q h
  have a' := @a q
  have z' := @z q
  simp only [Finset.mem_union] at h a' ⊢
  tauto

theorem meas_sub (a b c d g : Wire) :
    wires [Instr.measureX a [] [Correction.CZ b c], Instr.measureX d [] [Correction.CZ g c]] ⊆
      (wires [Instr.measureX a [] [Correction.CZ b c]] ∪ wires [Instr.CX b d, Instr.measureX a [] []]) ∪ {g} := by
  intro q h
  simp [wires,Instr.wires,correctionWires] at h ⊢
  tauto

theorem addPart_sub (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (ExitMerge.addPart w g k) ⊆ wires (addPartKeep w g k) ∪ {g} := by
  simp only [ExitMerge.addPart,addPartKeep,wires_append]
  exact fin_add (meas_sub (w 722) (w 514) (w 1028) (w 721) g)

theorem prefix_sub (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (prefixAll w g k) ⊆ wires (programAll w g k) := by
  unfold programAll
  split_ifs with he
  · simp only [programOdd,prefixAll,wires_append]
    exact Finset.subset_union_left
  · simp only [prefixAll,programEven,wires_append]
    exact fin_pre (addPart_sub w g k) (Finset.singleton_subset_iff.mpr (fPart_g w g k))

theorem eraseF_toffoli (w : Nat → Wire) (g : Wire) (k : Nat) : toffoliCount (eraseF w g k) = 255 := by
  have e1 := eraseLtChain_counts (tR w) (xR w) (hC3 w) (w 1797) (w 514)
    (by simp [xR,tR,wireBlock_length]) (by simp [hC3,xR,wireBlock_length])
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  rw [lx] at e1
  simp only [eraseF,toffoliCount_append,(maskedConstant_counts _ _ _).1,(notRegister_counts _).1,e1.1]

theorem programN_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (programN w g k) + 254 = toffoliCount (programAll w g k) ∧
    measurementCount (programN w g k) ≤ measurementCount (programAll w g k) ∧
    gateSlots (programN w g k) ≤ gateSlots (programAll w g k) + 2 := by
  have sw1 : toffoliCount (ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722)) = 0 := by
    simp [ECDSAAdd.Entrant.FlagEntry.swp,toffoliCount]
  have sw2 : measurementCount (ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722)) = 0 := by
    simp [ECDSAAdd.Entrant.FlagEntry.swp,measurementCount]
  have sw3 : gateSlots (ECDSAAdd.Entrant.FlagEntry.swp (w 514) (w 722)) = 2 := by
    simp [ECDSAAdd.Entrant.FlagEntry.swp,gateSlots,instructionSlots]
  have f := eraseF_toffoli w g k
  have a := addPartKeep_counts w g k
  have o := eraseOdd_counts w g k
  have ev := eraseEven_counts w g k
  unfold programAll programN
  split_ifs
  · simp only [programOdd,prefixAll,toffoliCount_append,measurementCount_append,gateSlots_append,sw1,sw2,sw3]
    omega
  · simp only [programEven,prefixAll,toffoliCount_append,measurementCount_append,gateSlots_append,sw1,sw2,sw3]
    omega

theorem programN_physical (k : Nat) : GatePhysical (programN base (base 2400) k) := by
  have old:=ExitMerge.program_physical base (base 2400) base_pool_nodup E1QubitPlacement.g2400 k
  simp only [ExitMerge.program,gatePhysical_append] at old
  have hn := base_pool_nodup
  have ne : base 514≠base 722 := w_ne base hn _ _ (by omega) (by omega) (by omega)
  have sw : GatePhysical (ECDSAAdd.Entrant.FlagEntry.swp (base 514) (base 722)) := by
    simp [ECDSAAdd.Entrant.FlagEntry.swp,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ne,Ne.symm ne]
  simp only [programN,prefixAll,gatePhysical_append]
  exact ⟨old.1,sw⟩

end ECDSAAdd.Entrant.ParityXExit
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ParityXExitInverse23Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog ParityEven
attribute [local irreducible] run wires InverseFive23.stackReverse15 InverseFour15.stackReverse15 InverseFive23.lastPhase15

/-- The merged exit with the flag parked, placed like `x1`. -/
def x1N (k : Nat) : Program := renameProgram pi (ParityXExit.programN base (base 2400) k)

def lastXN (k : Nat) : Program :=
  skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true ++ x1N k

/-- Where the parked flag sits in the unhosted coordinates. -/
def pkP : Wire := base 724

theorem pi_722 : pi (base 722) = pkP := by
  rw [pi_base]; rfl

theorem x1N_pw (k : Nat) (hk : k < p) (x y : Nat) (hx : x < p) (s v : State) (mn r r' : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis)
    (hphase : v.phase=(run (FrontierEntry1591Native.forward base) mn s).phase)
    (hpool : ∀q∈skywalkPoolWires base,v.basis q=(run (FrontierEntry1591Native.forward base) mn s).basis q) :
    run (x1N k) r v = put (run (x1 k) r' v) pkP (v.basis (base 2400) && decide (k<x)) := by
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
  have pr := ParityXExit.programN_pw k hk x hx
    (pullState pi s) (pullState pi v) mn r r' seed (blk0 1029 256 (by omega) (by omega))
    (izero 514 (by omega) (by omega)) (izero 721 (by omega) (by omega)) (izero 722 (by omega) (by omega))
    fphase fpool
  have rrN := run_rename pi pi.injective (ParityXExit.programN base (base 2400) k) r v
  have rrO := run_rename pi pi.injective (ParityXExit.programAll base (base 2400) k) r' v
  rw [←rrN,←rrO,pull_basis,pi_fix 2400 (by omega)] at pr
  change pullState pi (run (x1N k) r v) = put (pullState pi (run (x1 k) r' v)) (base 722) _ at pr
  apply State.extensionality
  · have h0 := congrArg State.phase pr
    exact h0
  · funext q
    have h := congrFun (congrArg State.basis pr) (pi.symm q)
    rw [pull_basis,Equiv.apply_symm_apply] at h
    rw [h]
    by_cases e : q = pkP
    · subst e
      have e2 : pi.symm pkP = base 722 := by rw [←pi_722]; simp
      simp [put,writeBit,e2]
    · have e2 : pi.symm q ≠ base 722 := fun h' => e (by rw [←pi_722,←h']; simp)
      simp [put,writeBit,e,e2,pull_basis]

theorem rawN (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastXN k)) m s =
      put (run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s) pkP
        (s.basis (base 2400) && decide (k<x)) := by
  obtain ⟨mp,mf,mr,eqN,eqO⟩ : ∃ mp mf mr,
      run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastXN k)) m s=
        run (lastXN k) mr (run F mf (run (Rolling1588.firstPhase false) mp s)) ∧
      run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s=
        run (lastX k) mr (run F mf (run (Rolling1588.firstPhase false) mp s)) :=
    ⟨_,_,_,by rw [FrontierEntry1591Native.kernel,run_append,run_append],
      by rw [FrontierEntry1591Native.kernel,run_append,run_append]⟩
  obtain ⟨r1,r2,r3⟩ := fieldResult mp mf
  rw [eqN,eqO]
  generalize hAfter : run F mf (run (Rolling1588.firstPhase false) mp s)=after at r1 r2 r3 ⊢
  generalize hBefore : run (Rolling1588.firstPhase true) mp s=beforeB at r1 r2 r3
  rw [show lastXN k=(skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)++x1N k from rfl,
    show lastX k=(skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)++x1 k from rfl,
    run_append (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true),
    run_append (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)]
  have agree := pool_run_agrees (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)
    (skywalkPoolWires base).toFinset prefix_pool
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) after beforeB r1
    (fun q hq => r3 q (num_not_pool q (List.mem_toFinset.mp hq)))
  generalize hv : run (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true)
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) after=v
    at agree ⊢
  have vB := prefix_roundtrip hn hlo x y hx0 hx s mp
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFive23.stackReverse15 true))) input
  rw [hBefore] at vB
  rw [vB] at agree
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
  rw [←gv]
  exact x1N_pw k hk x y hx s v _ _ _ input agree.1 (fun q hq => agree.2 q (List.mem_toFinset.mpr hq))

theorem programN_sub (k : Nat) :
    wires (ParityXExit.programN base (base 2400) k) ⊆ wires (ParityXExit.programAll base (base 2400) k) := by
  have pre := ParityXExit.prefix_sub base (base 2400) k
  have f514 : base 514 ∈ wires (ExitMerge.fPart base (base 2400) k) := by
    simp only [ExitMerge.fPart,wires_append,Finset.mem_union]
    right
    simp [wires,Instr.wires]
  have f722 : base 722 ∈ wires (ExitMerge.fPart base (base 2400) k) := by
    simp only [ExitMerge.fPart,wires_append,Finset.mem_union]
    right
    simp [wires,Instr.wires]
  have fp : wires (ExitMerge.fPart base (base 2400) k) ⊆ wires (ParityXExit.prefixAll base (base 2400) k) := by
    simp only [ParityXExit.prefixAll,wires_append]
    intro q hq
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl hq)))
  unfold ParityXExit.programN
  rw [wires_append]
  refine Finset.union_subset pre ?_
  intro q hq
  have hq' : q = base 722 ∨ q = base 514 := by
    simpa [ECDSAAdd.Entrant.FlagEntry.swp,wires,Instr.wires] using hq
  rcases hq' with rfl | rfl
  · exact pre (fp f722)
  · exact pre (fp f514)

theorem x1N_sub (k : Nat) : wires (x1N k) ⊆ wires (x1 k) := by
  rw [x1N,x1,renameProgram_support,renameProgram_support]
  exact Finset.image_subset_image (programN_sub k)

theorem lastXN_sub (k : Nat) : wires (lastXN k) ⊆ wires (lastX k) := by
  simp only [lastXN,lastX,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (x1N_sub k)

theorem kernelXN_sub_aux (k : Nat) :
    wires (renameProgram phaseHost (lastXN k)) ⊆ wires (renameProgram phaseHost (lastX k)) := by
  rw [renameProgram_support,renameProgram_support]
  exact Finset.image_subset_image (lastXN_sub k)

def kernelXN (k : Nat) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase false)++
    (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastXN k))

theorem kernelXN_sub (k : Nat) : wires (kernelXN k) ⊆ wires (kernelX k) := by
  simp only [kernelXN,kernelX,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.Subset.refl _) (kernelXN_sub_aux k))

theorem pk_not_sites : pkP∉phaseSites := by
  intro hq
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,pkP] at hq
  rcases hq with e|e|e|e|e|e <;> have := base_injective e <;> omega

private theorem phase_sites_splitN : phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem rebindN (P F Q : Program) (s : State) (m : List Bool)
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
    rw [phase_sites_splitN] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_splitN];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_splitN] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_splitN];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last

theorem hostedN (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
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
    run (renameProgram phaseHost (Rolling1588.firstPhase false)++
        (F++renameProgram phaseHost (lastXN k))) m s =
      put (run (renameProgram phaseHost (Rolling1588.firstPhase false)++
        (F++renameProgram phaseHost (lastX k))) m s) pkP (s.basis (base 2400) && decide (k<x)) := by
  have raw := rawX F k hk hn hlo x y hx0 hx s m value input fieldResult
  have rn := rawN F k hk hn hlo x y hx0 hx s m value input fieldResult
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
  have outputN : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastXN k)) m s).basis q=false := by
    intro q hq
    have ne : q≠pkP := fun e => pk_not_sites (e ▸ hq)
    rw [rn]
    simpa [put,writeBit,ne] using output q hq
  have sameO := rebindN (Rolling1588.firstPhase false) F (lastX k) s m clean (first_hosts_free false)
    (fun records => first_clean_of_boundary false hn x y hx0 hx s records input integerBoundary)
    fieldFree (lastX_hosts_free k) output
  have sameN := rebindN (Rolling1588.firstPhase false) F (lastXN k) s m clean (first_hosts_free false)
    (fun records => first_clean_of_boundary false hn x y hx0 hx s records input integerBoundary)
    fieldFree (fun q hq h => lastX_hosts_free k q hq (lastXN_sub k h)) outputN
  rw [sameN,sameO,rn]

private theorem append_run_eqN (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernelXN_pw (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg : s.basis (base 2409)=false) (hs : s.basis (base 2410)=false) :
    run (kernelXN k) m s = put (run (kernelX k) m s) pkP (s.basis (base 2400) && decide (k<x)) := by
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase false))=
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase false)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics false).2.1]
  have eqO := append_run_eqN _ _ (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k)) s m records
    (fun r => Rolling1588TickGap.first_hosted_run_eq false hn x Y.val hx0 hx s r input)
  have eqN := append_run_eqN _ _ (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastXN k)) s m records
    (fun r => Rolling1588TickGap.first_hosted_run_eq false hn x Y.val hx0 hx s r input)
  have res := hostedN Rolling1588.exitFieldHosted k hk hn hlo x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input
    (fun mn mf => Rolling1588.stackForward_boundary false hn hlo x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x Y.val hx0 hx s mn input))
    Rolling1588.exitFieldHosted_work_free
    (fun mp mf => Rolling1588.exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  rw [kernelXN,kernelX,eqN,eqO]
  exact res

theorem kernelXN_support (k : Nat) : wires (kernelXN k)⊆OB5Support.logicalSites :=
  (kernelXN_sub k).trans (kernelX_support k)

theorem wordTransferN (L : ControlledPointLayout) (f : Wire → Wire) (k : Nat)
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
    (gSite : base 2400∈domain) (pkD : pkP∈domain)
    (X : Nat) (Y : Fp)
    (s : State) (m : List Bool)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (PN PO : Program) (supN : wires PN⊆domain) (supO : wires PO⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      t.basis (base 2409)=false → t.basis (base 2410)=false →
      run PN records t = put (run PO records t) pkP (t.basis (base 2400) && decide (k<X))) :
    run (renameProgram f PN) m s =
      put (run (renameProgram f PO) m s) (f pkP) (s.basis L.core.generic && decide (k<X)) := by
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
  have pw := P_spec t m input (zero _ selectorG) (zero _ selectorS)
  have trN := run_rename_pool f domain injective PN supN m t s rfl inputBits
  have trO := run_rename_pool f domain injective PO supO m t s rfl inputBits
  have tg : t.basis (base 2400)=s.basis L.core.generic := by rw [inputBits _ gSite,controlMap]
  rw [tg] at pw
  apply State.extensionality
  · rw [trN.1,pw]; exact trO.1.symm
  · funext q
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      rw [trN.2 a ha,pw]
      by_cases e : a=pkP
      · subst e; simp [put,writeBit]
      · have ne : f a≠f pkP := fun h => e (injective a ha pkP pkD h)
        simp only [put,writeBit,Function.update_apply,if_neg e,if_neg ne]
        exact (trO.2 a ha).symm
    · have ne : q≠f pkP := fun h => image (h ▸ Finset.mem_image_of_mem _ pkD)
      rw [run_rename_pool_outside f domain PN supN m s q image]
      simp only [put,writeBit,Function.update_apply,if_neg ne]
      rw [run_rename_pool_outside f domain PO supO m s q image]

theorem exitN_pw (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k < p) (X Y : Nat) (hX : X < p) (hX0 : 0 < X) (hY : Y < p)
    (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (FrontierEntry1591Callers.exit (kernelXN k) L) m s =
      put (run (FrontierEntry1591Callers.exit (kernelX k) L) m s) (wireFn2 L pkP)
        (s.basis L.core.generic && decide (k<X)) := by
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
  have pkD : pkP∈OB5Support.logicalSites := by
    have := E1QubitPlacement.sw_logical 724 (by unfold E1QubitPlacement.Rng; omega)
    simpa [E1QubitPlacement.sw,pkP] using this
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have result := wordTransferN L (wireFn2 L) k OB5Support.logicalSites
    (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
      (ArithmeticOB5.logical_sub_old hb) eq)
    divisorMap numeratorMap controlMap
    (fun q hq used hx hy => sharedWork q hq (ArithmeticOB5.logical_sub_old used) hx hy)
    selectorG selectorS dx dy gSite pkD X (Y:Fp) s m hx (hy.trans yValue.symm) hc
    (kernelXN k) (kernelX k) (kernelXN_support k) (kernelX_support k)
    (fun t records input hg hs => kernelXN_pw k hk
      config.1 above config.2.1 config.2.2 X (Y:Fp) hX0 hX t records input hg hs)
  simpa only [FrontierEntry1591Callers.exit] using result

def restXXN (L : ControlledPointLayout) (k : Nat) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastXN k)))

theorem exit_splitN (L : ControlledPointLayout) (k : Nat) :
    FrontierEntry1591Callers.exit (kernelXN k) L=E1QubitPlacement.tickF L++restXXN L k := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,kernelXN,Rolling1588TickGap.firstPhase,restXXN,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem pk_wire (L : ControlledPointLayout) : wireFn2 L pkP = ECDSAAdd.Entrant.FlagEntry.pkW L := by
  rw [ECDSAAdd.Entrant.FlagTop.pk_eq L]
  unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
  rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  rfl

theorem x1N_counts (k : Nat) :
    toffoliCount (x1N k) + 254 = toffoliCount (x1 k) ∧ measurementCount (x1N k) ≤ measurementCount (x1 k) ∧
    Challenge.gateSlots (x1N k) ≤ Challenge.gateSlots (x1 k) + 2 := by
  have h := ParityXExit.programN_counts base (base 2400) k
  simp only [x1N,x1,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  exact h

theorem restXXN_counts (L : ControlledPointLayout) (k : Nat) :
    toffoliCount (restXXN L k) + 254 = toffoliCount (restXX L k) ∧
    measurementCount (restXXN L k) ≤ measurementCount (restXX L k) ∧
    Challenge.gateSlots (restXXN L k) ≤ Challenge.gateSlots (restXX L k) + 2 := by
  have h := x1N_counts k
  simp only [restXXN,restXX,lastXN,lastX,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    Baselines.rename_gateSlots]
  omega

theorem restXXN_sub (L : ControlledPointLayout) (k : Nat) : wires (restXXN L k) ⊆ wires (restXX L k) := by
  simp only [restXXN,restXX,wires_append,renameProgram_support]
  apply Finset.image_subset_image
  apply Finset.union_subset_union (Finset.Subset.refl _)
  apply Finset.union_subset_union (Finset.Subset.refl _)
  exact Finset.image_subset_image (lastXN_sub k)

theorem x1N_physical (k : Nat) : GatePhysical (x1N k) :=
  gatePhysical_rename pi pi.injective _ (ParityXExit.programN_physical k)

theorem kernelXN_physical (k : Nat) : GatePhysical (kernelXN k) := by
  have old := Rolling1588TickGap.exitKernel_physical
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,gatePhysical_append] at old
  have last := InverseFive23.last_physical15 true
  simp only [InverseFive23.lastPhase15,gatePhysical_append] at last
  have lx : GatePhysical (lastXN k) := by
    simp only [lastXN,gatePhysical_append]; exact ⟨last.1,x1N_physical k⟩
  simp only [kernelXN,gatePhysical_append]
  exact ⟨old.1,old.2.1,gatePhysical_rename phaseHost phaseHost.injective _ lx⟩

theorem restXXN_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Nat) :
    GatePhysical (restXXN L k) := by
  have physical := FrontierEntry1591Native.placed_physical L hw hn (kernelXN k) (kernelXN_support k)
    (kernelXN_physical k)
  have e : GatePhysical (FrontierEntry1591Callers.exit (kernelXN k) L) := by
    unfold FrontierEntry1591Callers.exit; exact physical
  rw [exit_splitN,gatePhysical_append] at e
  exact e.2

end ECDSAAdd.Entrant.ParityXExitInverse23Kernel
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FlagExit
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out ParityEven ParityUniform

/-- The new program from `s'` ends in the old program's state from `s`, plus one write. -/
structure PadP (P' P : Program) (s' s : State) (pad : List Bool → List Bool) (w : Wire) (v : Bool) : Prop where
  run_eq : ∀ d, run P' d s' = put (run P (pad d) s) w v
  drop_eq : ∀ d, (pad d).drop (measurementCount P) = d.drop (measurementCount P')

theorem PadP.of_same {P' P : Program} {s' s : State} {w : Wire} {v : Bool}
    (h : ∀ r, run P' r s' = put (run P r s) w v) :
    PadP P' P s' s (fun r => pfx (measurementCount P) r ++ r.drop (measurementCount P')) w v := by
  have tk : ∀ (r x : List Bool), (pfx (measurementCount P) r ++ x).take (measurementCount P) =
      pfx (measurementCount P) r := by
    intro r x
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ (r x : List Bool), (pfx (measurementCount P) r ++ x).drop (measurementCount P) = x := by
    intro r x
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    have e : run P (pfx (measurementCount P) d ++ d.drop (measurementCount P')) s = run P d s := by
      rw [← run_take, tk, run_pfx]
    rw [h d, e]
  · intro d
    exact dr _ _

theorem PadP.append {P' P : Program} {s' s : State} {pad : List Bool → List Bool} {w : Wire} {v : Bool}
    (h : PadP P' P s' s pad w v) (R : Program) (hw : w ∉ wires R) :
    PadP (P' ++ R) (P ++ R) s' s pad w v := by
  constructor
  · intro d
    rw [run_append, run_take, h.run_eq, run_put _ _ _ _ _ hw, run_append, run_take, h.drop_eq]
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, h.drop_eq, List.drop_drop]

theorem PadP.prefix (A' A P' P : Program) (s' s : State) (pad : List Bool → List Bool) (w : Wire) (v : Bool)
    (hc : measurementCount A' = measurementCount A)
    (h : ∀ d, PadP P' P (run A' d s') (run A d s) pad w v) :
    PadP (A' ++ P') (A ++ P) s' s
      (fun d => pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))) w v := by
  have tk : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))).take
      (measurementCount A) = pfx (measurementCount A) d := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A))).drop
      (measurementCount A) = pad (d.drop (measurementCount A)) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx, hc]
    exact (h d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h d).drop_eq, hc,
      List.drop_drop]

/-- A padded head followed by a written tail. -/
theorem PadP.prefixMeas (A' A P' P : Program) (s' s : State) (pad : List Bool → List Bool) (w : Wire) (v : Bool)
    (h : ∀ d, PadP P' P (run A' d s') (run A d s) pad w v) :
    PadP (A' ++ P') (A ++ P) s' s
      (fun d => pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))) w v := by
  have tk : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))).take
      (measurementCount A) = pfx (measurementCount A) d := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) d ++ pad (d.drop (measurementCount A'))).drop
      (measurementCount A) = pad (d.drop (measurementCount A')) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx]
    exact (h d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h d).drop_eq,
      List.drop_drop]

/-- A padded head followed by a written tail. -/
theorem PadP.cat {A' A B' B : Program} {s' s : State} {pad1 pad2 : List Bool → List Bool} {w : Wire} {v : Bool}
    (h1 : Pad A' A s' s pad1)
    (h3 : ∀ d, PadP B' B (run A' d s') (run A (pad1 d) s) pad2 w v) :
    PadP (A' ++ B') (A ++ B) s' s
      (fun d => pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))) w v := by
  have tk : ∀ d, (pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))).take
      (measurementCount A) = pfx (measurementCount A) (pad1 d) := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))).drop
      (measurementCount A) = pad2 (d.drop (measurementCount A')) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, run_append A, tk, dr, run_pfx]
    exact (h3 d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h3 d).drop_eq,
      List.drop_drop]

/-- A written head followed by a tail that consumes the write. -/
theorem Pad.ofP {A' A B' B : Program} {s' s : State} {pad1 pad2 : List Bool → List Bool} {w : Wire} {v : Bool}
    (h1 : PadP A' A s' s pad1 w v)
    (h2 : ∀ d, Pad B' B (put (run A (pad1 d) s) w v) (run A (pad1 d) s) pad2) :
    Pad (A' ++ B') (A ++ B) s' s
      (fun d => pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))) := by
  have tk : ∀ d, (pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))).take
      (measurementCount A) = pfx (measurementCount A) (pad1 d) := by
    intro d
    rw [List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length])]
  have dr : ∀ d, (pfx (measurementCount A) (pad1 d) ++ pad2 (d.drop (measurementCount A'))).drop
      (measurementCount A) = pad2 (d.drop (measurementCount A')) := by
    intro d
    rw [List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length])]
    rfl
  constructor
  · intro d
    rw [run_append, run_take, h1.run_eq, run_append A, tk, dr, run_pfx]
    exact (h2 d).run_eq _
  · intro d
    rw [measurementCount_append, measurementCount_append, ← List.drop_drop, dr, (h2 d).drop_eq,
      List.drop_drop]

/-- Renaming carries a written run when the written wire is fixed. -/
theorem PadP.rename (f : Wire → Wire) (inj : Function.Injective f) (pk : Wire) (hfix : f pk = pk)
    (P' P : Program) (hw : pk ∈ wires P') (t : State) (e v : Bool) (pad : List Bool → List Bool)
    (h : PadP P' P (put (pullState f t) pk e) (pullState f t) pad pk v) :
    PadP (renameProgram f P') (renameProgram f P) (put t pk e) t pad pk v := by
  constructor
  · intro d
    have S := wires P' ∪ wires P
    have A := run_rename_pool f (wires P' ∪ wires P) (fun a _ b _ eq => inj eq) P' Finset.subset_union_left d
      (put (pullState f t) pk e) (put t pk e) rfl (by
        intro q _
        by_cases eq : q = pk
        · subst eq; simp [put, writeBit, hfix]
        · have ne : f q ≠ pk := fun E => eq (inj (E.trans hfix.symm))
          simp only [put, writeBit, Function.update_apply, eq, ne, if_false]
          rfl)
    have B := run_rename_pool f (wires P' ∪ wires P) (fun a _ b _ eq => inj eq) P Finset.subset_union_right
      (pad d) (pullState f t) t rfl (fun _ _ => rfl)
    rw [h.run_eq d] at A
    apply State.extensionality
    · exact A.1.trans B.1.symm
    funext q
    by_cases im : q ∈ (wires P' ∪ wires P).image f
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp im
      rw [A.2 c hc]
      by_cases eq : c = pk
      · subst eq; simp [put, writeBit, hfix]
      · have ne : f c ≠ pk := fun E => eq (inj (E.trans hfix.symm))
        simp only [put, writeBit, Function.update_apply, eq, ne, if_false]
        exact (B.2 c hc).symm
    · have ne : q ≠ pk := by
        intro E; subst E
        exact im (Finset.mem_image.mpr ⟨q, Finset.mem_union_left _ hw, hfix⟩)
      rw [run_rename_pool_outside f (wires P' ∪ wires P) P' Finset.subset_union_left d _ q im]
      simp only [put, writeBit, Function.update_apply, ne, if_false]
      rw [run_rename_pool_outside f (wires P' ∪ wires P) P Finset.subset_union_right (pad d) t q im]
  · intro d
    rw [(renameProgram_counts _ _).2, (renameProgram_counts _ _).2]
    exact h.drop_eq d

theorem flag_out (a b : Fp) : decide (a.val < b.val) = decide (a.val < (a-b).val) := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have sv : (a-b).val=(a.val+p-b.val)%p := by
    rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
    rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt b))]
  have ha : a.val < p := ZMod.val_lt a
  have hb : b.val < p := ZMod.val_lt b
  rw [sv]
  apply decide_eq_decide.mpr
  by_cases h : a.val < b.val
  · have e : (a.val+p-b.val)%p = a.val+p-b.val := Nat.mod_eq_of_lt (by omega)
    rw [e]; omega
  · have e : (a.val+p-b.val)%p = a.val-b.val := by
      have e2 : a.val+p-b.val = (a.val-b.val)+p := by omega
      rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]; omega

theorem run_pre (A B : Program) (r : List Bool) (w : State) :
    run (A ++ B) (pfx (measurementCount A) [] ++ r) w = run B r (run A [] w) := by
  rw [run_append,
    List.take_append_of_le_length (by rw [pfx_length]), List.take_of_length_le (by rw [pfx_length]),
    List.drop_append_of_le_length (by rw [pfx_length]), List.drop_of_length_le (by rw [pfx_length]),
    run_pfx]
  rfl

section Second
open ParityXExitInverse23Kernel ParityStageBothInverse23 ReflectionE1TickGapLow48 ParityXEntry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pk_not_exitY (k : Fp) (hg : pkW L ≠ L.core.generic) : pkW L ∉ wires (exitYAll L k) := by
  intro h
  have sub := (exitYAll_wires L hw k).trans (ExitFusionResearch.exitY_support L hw k)
  have h2 := Finset.mem_of_subset sub h
  rcases List.mem_cons.mp (List.mem_toFinset.mp h2) with e | e
  · exact hg e
  · exact pk_not_K L hw hn e

theorem rest_pw (k cx X Y : Fp) (G : Bool) (origin : BasisState) (s : State)
    (hs : PointDialogValues L X Y G origin s.basis)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) (d r : List Bool) :
    run (restXXN L cx.val) r (run (squareEntry L k) d s) =
      put (run (restXX L cx.val) r (run (squareEntry L k) d s)) (pkW L)
        (G && decide (cx.val < (X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
          (if G then k else 0)).val)) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  obtain ⟨-,vW⟩ := (square.seq add) s [] hs
  generalize hwd : run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k) [] s = w at vW
  have eu : run (squareEntry L k) d s = run (E1QubitPlacement.tickF L) [] w := by
    rw [squareEntry_base L hw hn k X Y G origin s d [] hs, run_append, ← hwd]
    simp only [List.take_nil, List.drop_nil]
  have hpos : 0 < (Z+(if G then k else 0)).val :=
    Nat.pos_of_ne_zero (fun hz => hx ((ZMod.val_eq_zero _).mp hz))
  have e1 := exitN_pw L hw hn cx.val cx.isLt (Z+(if G then k else 0)).val Y.val (ZMod.val_lt _) hpos
    (ZMod.val_lt _) w (pfx (measurementCount (E1QubitPlacement.tickF L)) [] ++ r) vW.x vW.y vW.clean
  rw [exit_splitN,exit_splitX,run_pre,run_pre,← eu,vW.generic,pk_wire] at e1
  exact e1

def restPad (L : ControlledPointLayout) (k : Nat) : List Bool → List Bool :=
  fun r => pfx (measurementCount (restXX L k)) r ++ r.drop (measurementCount (restXXN L k))

def secondStageN (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  squareEntry L k ++ restXXN L cx.val ++ exitYAll L cy

def padS (L : ControlledPointLayout) (k cx : Fp) : List Bool → List Bool :=
  fun d => pfx (measurementCount (squareEntry L k)) d ++
    restPad L cx.val (d.drop (measurementCount (squareEntry L k)))

theorem second_padp (k cy cx X Y : Fp) (G : Bool) (origin : BasisState) (s : State)
    (hs : PointDialogValues L X Y G origin s.basis) (hg : pkW L ≠ L.core.generic)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    PadP (secondStageN L k cy cx) (secondStageAll L k cy cx) s s (padS L k cx) (pkW L)
      (G && decide (cx.val < (X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
        (if G then k else 0)).val)) := by
  have h := PadP.prefix (squareEntry L k) (squareEntry L k) (restXXN L cx.val) (restXX L cx.val) s s
    (restPad L cx.val) (pkW L) _ rfl
    (fun d => PadP.of_same (fun r => rest_pw L hw hn k cx X Y G origin s hs hx d r))
  exact h.append (exitYAll L cy) (pk_not_exitY L hw hn cy hg)

def genericN (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ((entryYAll L (-cy) ++ entryXNew L (pkW L) (-cx)) ++ restEntry L) ++
    secondStageN L (ReflectionE1.correction cx) cy cx

def padE (L : ControlledPointLayout) (cy cx : Fp) : List Bool → List Bool :=
  fun d => pfx (measurementCount (entryYAll L (-cy))) d ++
    (List.replicate (measurementCount (E1Merge.comparePart MappedCompressed.base (MappedCompressed.base 2400) (-cx).val)) false ++
      d.drop (measurementCount (entryYAll L (-cy))))

theorem head_pad (cx cy X Y : Fp) (s : State)
    (hX : regValue L.point.x s.basis = X.val) (hY : regValue L.point.y s.basis = Y.val)
    (hc : regValue L.dialogPool s.basis = 0) (hg : pkW L ≠ L.core.generic) :
    Pad ((entryYAll L (-cy) ++ entryXNew L (pkW L) (-cx)) ++ restEntry L)
      (entryStageAll L (-cx) (-cy))
      (put s (pkW L) (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false)) s
      (padE L cy cx) := by
  have inner := Pad.prefix (entryYAll L (-cy)) (entryYAll L (-cy)) (entryXNew L (pkW L) (-cx))
    (entryXAll L (-cx))
    (put s (pkW L) (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false)) s
    (fun d => List.replicate (measurementCount (E1Merge.comparePart MappedCompressed.base (MappedCompressed.base 2400) (-cx).val)) false ++ d) rfl (by
      intro d
      rw [run_put _ _ _ _ _ (pk_not_Y L hw hn _ hg)]
      have eY := entryYAll_eq L hw hn Y (-cy) s d hY hc
      have fy := EntryFuse.fusedY_correct L hw hn Y (-cy) s d hY hc
      rw [eY]
      generalize hu : run (EntryFuse.fusedY L (-cy)) d s = u at fy
      have tx : regValue L.point.x u.basis = X.val := by
        rw [regValue_congr _ _ s.basis (fun q hq => fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)), hX]
      have tc : regValue L.dialogPool u.basis = 0 := by
        rw [regValue_congr _ _ s.basis (fun q hq => fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)), hc]
      have tg : u.basis L.core.generic = s.basis L.core.generic :=
        fy.2.2 _ ((E1QubitPlacement.lay L hw hn _).2.2 rfl).2
      rw [← tg]
      constructor
      · intro d'
        exact entryXNew_run L hw hn (pkW L) X (-cx) u tx tc (pk_pool L hw) (pk_ne_flag L hw hn)
          (pk_ne_high L hw hn) (pk_ne_x L hw hn)
          (by rw [E1QubitPlacement.pmap_g L hw hn]; exact hg) d'
      · intro d'
        rw [entryXNew_measure L (pkW L) (-cx), ← List.drop_drop, List.drop_left' (by simp)])
  exact inner.append _

def padG (L : ControlledPointLayout) (cx cy : Fp) : List Bool → List Bool :=
  fun d => pfx (measurementCount (entryStageAll L (-cx) (-cy))) (padE L cy cx d) ++
    padS L (ReflectionE1.correction cx) cx
      (d.drop (measurementCount ((entryYAll L (-cy) ++ entryXNew L (pkW L) (-cx)) ++ restEntry L)))

theorem generic_padp_true (X Y cx cy : Fp) (s : State) (e : Bool)
    (hv : PointDialogValues L X Y true s.basis s.basis)
    (he : e = (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) (hg : pkW L ≠ L.core.generic) :
    PadP (genericN L cx cy) (genericAll L cx cy) (put s (pkW L) e) s (padG L cx cy) (pkW L)
      (decide (cx.val < (genericX X Y cx cy).val)) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hvv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) true s.basis
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hvv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have head := head_pad L hw hn cx cy X Y s hv.x hv.y hv.clean hg
  rw [← he] at head
  have hc := PadP.cat (B' := secondStageN L (ReflectionE1.correction cx) cy cx)
    (B := secondStageAll L (ReflectionE1.correction cx) cy cx) (pad2 := padS L (ReflectionE1.correction cx) cx)
    (w := pkW L) (v := decide (cx.val < d.val)) head (by
      intro q
      rw [head.run_eq q]
      obtain ⟨-,v1⟩ := first s (padE L cy cx q) hv
      have sp := second_padp L hw hn (ReflectionE1.correction cx) cy cx (X-cx) a true s.basis _ v1 hg
        (by simpa only [if_true,hd4] using hd)
      simp only [if_true,hd4,Bool.true_and] at sp
      exact sp)
  have fo := flag_out cx d
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at fo
  rw [← fo]
  exact hc

theorem generic_padp_false (X Y cx cy : Fp) (s : State) (e : Bool)
    (hv : PointDialogValues L X Y false s.basis s.basis)
    (he : e = (if s.basis L.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hX : X≠0) (hg : pkW L ≠ L.core.generic) :
    PadP (genericN L cx cy) (genericAll L cx cy) (put s (pkW L) e) s (padG L cx cy) (pkW L) false := by
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) false s.basis
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  simp only [Bool.false_eq_true,if_false,add_zero] at first
  have head := head_pad L hw hn cx cy X Y s hv.x hv.y hv.clean hg
  rw [← he] at head
  exact PadP.cat (B' := secondStageN L (ReflectionE1.correction cx) cy cx)
    (B := secondStageAll L (ReflectionE1.correction cx) cy cx) (pad2 := padS L (ReflectionE1.correction cx) cx)
    (w := pkW L) (v := false) head (by
      intro q
      rw [head.run_eq q]
      obtain ⟨-,v1⟩ := first s (padE L cy cx q) hv
      have sp := second_padp L hw hn (ReflectionE1.correction cx) cy cx X (Y/X) false s.basis _ v1 hg
        (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
      simpa only [Bool.false_and] using sp)

end Second

end ECDSAAdd.Entrant.FlagExit
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OutFlag
open Arithmetic Challenge RecordedQuantum MeasuredCodec5 Baselines InputSentinel Secp256k1 ControlledPointLayout
  ZeroFill OutputOpt ParityEven

theorem zeroWith_extract_pre (T : Wire → Program) (E : Program) (c : Wire) (bs : List ZeroBit)
    (hnd : (c :: bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b ∈ bs, s.basis b.work = false) (B : State)
    (hB : ∀ m', run (T (lastWire c bs)) m' ⟨s.phase, fill c bs s.basis⟩ = B)
    (hkeep : ∀ q ∈ c :: bs.flatMap ZeroBit.wires, B.basis q = fill c bs s.basis q)
    (P : Wire) (v : Bool)
    (hE : ∀ m', run E m' ⟨s.phase, fill c bs s.basis⟩ = put ⟨s.phase, fill c bs s.basis⟩ P v)
    (hT : P ∉ wires (T (lastWire c bs)))
    (hP : P ∉ c :: bs.flatMap ZeroBit.wires) :
    run (zeroWith (fun w => E ++ T w) c bs) m s =
      ⟨(run (zeroWith T c bs) m s).phase, writeBit (run (zeroWith T c bs) m s).basis P v⟩ := by
  have ho := zeroWith_fill T c bs hnd s m hz B hB hkeep
  have hw : ∀ b ∈ bs, b.work ≠ P := by
    intro b hb e
    apply hP
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires, e]⟩
  have hn := zeroWith_fill (fun w => E ++ T w) c bs hnd s m hz ⟨B.phase, writeBit B.basis P v⟩
    (by
      intro m'
      show run (E ++ T (lastWire c bs)) m' _ = _
      rw [run_append, hE, run_put _ _ _ _ _ hT, hB]
      rfl)
    (by
      intro q hq
      have hne : q ≠ P := fun e => hP (e ▸ hq)
      simpa [writeBit, hne] using hkeep q hq)
  rw [hn, ho]
  simp only [clear_write bs _ P v hw]

theorem oshape_state (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (w : Nat → Wire) (i0 : Nat) (it : List Nat) (work : List Wire)
    (hPn : ((i0 :: it).map w).Nodup) (x1P : xr1 ∉ (i0 :: it).map w) (x2P : xr2 ∉ (i0 :: it).map w)
    (hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w)
    (hwl : (it.map w).length = work.length) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (s : State)
    (hz : ∀ q ∈ work, s.basis q = false)
    (hp : OutputOpt.otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis) :
    ∃ s2 : State,
      s2.phase = s.phase ∧ (∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q) ∧
      s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) ∧
      (∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2))) ∧
      (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup ∧
      (∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false) ∧
      ∀ (E : Program) (pk : Wire) (val : Bool),
        (∀ m', run E m' ⟨s2.phase, fill (w i0) (zeroPorts (it.map w) work) s2.basis⟩ =
          put ⟨s2.phase, fill (w i0) (zeroPorts (it.map w) work) s2.basis⟩ pk val) →
        pk ∉ (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires) →
        pk ∉ wires ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)) →
        pk ∉ wires (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
          (lastWire (w i0) (zeroPorts (it.map w) work))) → ∀ m,
        run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([Instr.X (w i0)] ++
          (zeroWith (fun h => E ++ OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) (w i0)
            (zeroPorts (it.map w) work) ++
          ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s =
        put (run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([Instr.X (w i0)] ++
          (zeroWith (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
          ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s) pk val := by
  have hlw : (i0 :: it).map w = w i0 :: it.map w := rfl
  have p0l : w i0 ∈ (i0 :: it).map w := by simp
  have usedNotP : ∀ q ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w := by
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
  have hcu : w i0 ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := fun h => usedNotP _ h p0l
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
  have hdis' : ∀ b ∈ zeroPorts (it.map w) work, b.input ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
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
    rw [s2out _ (hdisj _ hwk).1]; exact hz _ hwk
  set bs := zeroPorts (it.map w) work with hbs
  set V := (i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2) with hV
  set last := lastWire (w i0) bs with hlast
  set st := fill (w i0) bs s2.basis with hst
  have lastU : last ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    rcases lastWire_mem (w i0) bs with e | ⟨b, hb, e⟩
    · rw [hlast, e]; exact hcu
    · rw [hlast, e]; exact (hdis' b hb).2
  have stU : ∀ q ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], st q = s.basis q := by
    intro q hq
    rw [hst, fill_outside (w i0) bs _ q (fun b hb e => (hdis' b hb).2 (e ▸ hq)), s2out q (usedNotP q hq)]
  have stL : st last = V := by
    rw [hst, hlast, fill_last (w i0) bs _ hnd hz3, huV]
  have hnd10 : [last, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup := List.nodup_cons.mpr ⟨lastU, hused⟩
  have hnd13 : [last, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup := List.nodup_cons.mpr ⟨lastU, hused⟩
  have hp' : OutputOpt.otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u (st last) st := by
    rw [stL]
    unfold OutputOpt.otailPre at hp ⊢
    rw [stU f (by simp), stU t1 (by simp), stU t2 (by simp), stU u (by simp), stU g (by simp),
      stU c (by simp), stU O (by simp), stU D (by simp), stU H (by simp), stU y0 (by simp),
      stU xr1 (by simp), stU xr2 (by simp)]
    exact hp
  let B : State := ⟨s2.phase, OutputOpt.otailEff tr xr1 xr2 f g O D H (st last) st⟩
  have hB : ∀ m', run (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u last) m' ⟨s2.phase, st⟩ = B :=
    fun m' => OutputOpt.otail_run tr v yc y2c e last xr1 xr2 y0 c f g O D H t1 t2 u hnd13 ⟨s2.phase, st⟩ m' hp'
  refine ⟨s2, s2ph, s2out, s2p0, s2it, hnd, hz3, ?_⟩
  intro E pk val hE hpk hsuf hT m
  have hkeep : ∀ q ∈ w i0 :: bs.flatMap ZeroBit.wires, B.basis q = st q := by
    intro q hq
    have hqu : q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
      rcases List.mem_cons.mp hq with e | h
      · rw [e]; exact hcu
      · obtain ⟨b, hb, hw⟩ := List.mem_flatMap.mp h
        simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with e | e
        · rw [e]; exact (hdis' b hb).1
        · rw [e]; exact (hdis' b hb).2
    show OutputOpt.otailEff tr xr1 xr2 f g O D H (st last) st q = st q
    rw [OutputOpt.otailEff_apply]
    have n1 : q ≠ H := fun e => hqu (by simp [e])
    have n2 : q ≠ D := fun e => hqu (by simp [e])
    have n3 : q ≠ O := fun e => hqu (by simp [e])
    have n4 : q ≠ g := fun e => hqu (by simp [e])
    have n5 : q ≠ f := fun e => hqu (by simp [e])
    simp [n1, n2, n3, n4, n5]
  have Z := zeroWith_extract_pre (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) E (w i0) bs hnd s2 m hz3
    B hB hkeep pk val hE hT hpk
  have mR : measurementCount (tr.remapList xr1 xr2 w (i0 :: it)) = 0 := remapList_mc _ _ _ _ _
  have mX : measurementCount [Instr.X (w i0)] = 0 := rfl
  have mS : measurementCount ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)) = 0 := by
    rw [measurementCount_append, mX, mR]
  rw [wrap_run _ _ _ _ mR mX, wrap_run _ _ _ _ mR mX, hs1, e2]
  change run (zeroWith (fun h => E ++ OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) (w i0) bs) m s2 =
    put (run (zeroWith (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) bs) m s2) pk val at Z
  rw [Z, run_no_measure _ mS (List.drop _ m), run_no_measure _ mS (List.drop _ m), run_put _ _ _ _ _ hsuf]

def Gc (c g O D H W : Wire) : Program := [.CX c W, .CX g W, .CX O W, .CX D W, .CX H W]

theorem Gc_run (c g O D H W : Wire) (h1 : c ≠ W) (h2 : g ≠ W) (h3 : O ≠ W) (h4 : D ≠ W) (h5 : H ≠ W)
    (s : State) (m : List Bool) :
    run (Gc c g O D H W) m s =
      put s W (s.basis W ^^ (s.basis c ^^ s.basis g ^^ s.basis O ^^ s.basis D ^^ s.basis H)) := by
  apply State.extensionality
  · rfl
  funext q
  by_cases e : q = W
  · subst e
    simp [Gc, run, put, writeBit, Function.update_apply, h1, h2, h3, h4, h5]
  · simp [Gc, run, put, writeBit, Function.update_apply, e]

/-- The output classifier with the wrap flag cleared from its chain. -/
def oclassifierF (tr : Tri) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) : Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (fun h => (Gc c g O D H W ++ (extractOutput tr xs work one U V F pk W ++ Gc c g O D H W)) ++
        OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

theorem oclassifierF_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ xs ∧ q ∉ work)
    (htmp : [one, U, V, F, pk].Nodup)
    (htx : ∀ q ∈ [one, U, V, F, pk], q ∉ xs ∧ q ∉ work ∧ q ≠ W)
    (hWx : W ∉ xs ∧ W ∉ work) (hWe : c ≠ W ∧ g ≠ W ∧ O ≠ W ∧ D ≠ W ∧ H ≠ W)
    (hpkE : pk ∉ [y0, c, f, g, O, D, H, t1, t2, u])
    (s : State) (m : List Bool)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis f = false ∧ s.basis t1 = false ∧
      s.basis t2 = false ∧ s.basis u = false)
    (hfl : s.basis g = (s.basis c && oX tr tr.S xs s.basis) ∧
      s.basis O = (s.basis c && oX tr tr.A xs s.basis && (s.basis y0 == yc)) ∧
      s.basis D = (s.basis c && oX tr tr.B xs s.basis && (s.basis y0 == y2c)) ∧
      s.basis H = (e && s.basis c && oX tr tr.A xs s.basis && (s.basis y0 != yc)))
    (hto : ∀ q ∈ [one, U, V, F], s.basis q = false) (hW0 : s.basis W = false)
    (x : Nat) (hx : x < 2^256) (xbit : ∀ i, i < 256 → s.basis (xs.getD i 0) = x.testBit i)
    (hKnownPark : s.basis pk = ((s.basis c ^^ s.basis g ^^ s.basis O ^^ s.basis D ^^ s.basis H) && decide (tr.A < x))) :
    run (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) m s =
      put (run (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) m s) pk
        (s.basis pk ^^ ((s.basis c ^^ s.basis g ^^ s.basis O ^^ s.basis D ^^ s.basis H) &&
          decide (tr.A < x))) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  set w : Nat → Wire := fun i => xs.getD i 0 with hw
  set xr1 := w tr.r1 with hx1
  set xr2 := w tr.r2 with hx2
  set P := tr.idx.map w with hP
  have winj : ∀ i j, i < 256 → j < 256 → w i = w j → i = j := by
    intro i j hi hj heq
    simp only [hw] at heq
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
    exact hxs.getElem_inj_iff.mp heq
  have wmem : ∀ i, i < 256 → w i ∈ xs := by
    intro i hi; simp only [hw]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hPn : P.Nodup := by
    apply List.Nodup.map_on _ ix.1
    intro i hi j hj heq; exact winj i j (ix.2.2.2.2 i hi) (ix.2.2.2.2 j hj) heq
  have memP : ∀ q, q ∈ P ↔ ∃ i ∈ tr.idx, w i = q := by intro q; simp [hP]
  have x1P : xr1 ∉ P := by
    rw [memP]; rintro ⟨i, hi, heq⟩
    exact ix.2.2.1 (winj i tr.r1 (ix.2.2.2.2 i hi) pv.1 heq ▸ hi)
  have x2P : xr2 ∉ P := by
    rw [memP]; rintro ⟨i, hi, heq⟩
    exact ix.2.2.2.1 (winj i tr.r2 (ix.2.2.2.2 i hi) pv.2.1 heq ▸ hi)
  have x12 : xr1 ≠ xr2 := fun heq => pv.2.2.1 (winj _ _ pv.1 pv.2.1 heq)
  have Psub : ∀ q ∈ P, q ∈ xs := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := (memP q).mp hq; exact wmem i (ix.2.2.2.2 i hi)
  have hPl : P.length = 254 := by simp [hP, ix.2.1]
  obtain ⟨i0, it, hidx⟩ : ∃ i0 it, tr.idx = i0 :: it := by
    have hl := ix.2.1
    cases h : tr.idx with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  have hP0 : P = w i0 :: it.map w := by simp [hP, hidx]
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, O, D, H, t1, t2, u]) :
      q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    exact ⟨fun hp => h.1 (Psub q hp), h.2, fun heq => h.1 (heq ▸ wmem _ pv.1),
      fun heq => h.1 (heq ▸ wmem _ pv.2.1)⟩
  have hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨x12, ?_⟩
      have := fun q hq => (extx q hq).2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      exact ⟨fun heq => this y0 (Or.inl rfl) heq.symm, fun heq => this c (by tauto) heq.symm,
        fun heq => this f (by tauto) heq.symm, fun heq => this g (by tauto) heq.symm,
        fun heq => this O (by tauto) heq.symm, fun heq => this D (by tauto) heq.symm,
        fun heq => this H (by tauto) heq.symm, fun heq => this t1 (by tauto) heq.symm,
        fun heq => this t2 (by tauto) heq.symm, fun heq => this u (by tauto) heq.symm⟩
    · intro hm
      exact (extx xr2 hm).2.2.2 rfl
  have hlP : (i0 :: it).map w = P := by rw [hP0]; rfl
  have hPn' : ((i0 :: it).map w).Nodup := by rw [hlP]; exact hPn
  have x1P' : xr1 ∉ (i0 :: it).map w := by rw [hlP]; exact x1P
  have x2P' : xr2 ∉ (i0 :: it).map w := by rw [hlP]; exact x2P
  have hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w := by
    intro q hq; rw [hlP]; exact (extx q hq).1
  have hdisj' : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    intro q hq
    refine ⟨fun hm => hdisj q hq (Psub q (by rw [← hlP]; exact hm)), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (heq | heq | heq)
    · exact hdisj q hq (heq ▸ wmem _ pv.1)
    · exact hdisj q hq (heq ▸ wmem _ pv.2.1)
    · exact (hextx q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)).2 hq
  have hmb : matchBit tr xs s.basis =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    simp only [matchBit, hidx]; rfl
  have hoX : ∀ K, oX tr K xs s.basis = tX tr K
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2))
      (s.basis xr1) (s.basis xr2) := by
    intro K; simp only [oX, tX, ← hmb]; rfl
  have hp : OutputOpt.otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis := by
    unfold OutputOpt.otailPre
    rw [← hoX, ← hoX, ← hoX]
    exact ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2, hfl.1, hfl.2.1, hfl.2.2.1, hfl.2.2.2⟩
  obtain ⟨s2, s2ph, s2out, s2p0, s2it, chnd, chz, main⟩ :=
    oshape_state tr v yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u w i0 it work hPn' x1P' x2P' hused hextP
      (by rw [hitl, hwl]) hwn hdisj' s hz.1 hp
  have zp := zeroPorts_maps (it.map w) work (by rw [hitl, hwl])
  set p0 := w i0 with hp0
  set Gv := (s.basis c ^^ s.basis g ^^ s.basis O ^^ s.basis D ^^ s.basis H) with hGv
  set bs := zeroPorts (it.map w) work with hbs
  obtain ⟨F0, hF0⟩ : ∃ F0 : State, F0 = ⟨s2.phase, fill p0 bs s2.basis⟩ := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : State, B = put F0 W Gv := ⟨_, rfl⟩
  have Boff : ∀ q, q ≠ W → B.basis q = fill p0 bs s2.basis q := by
    intro q hq; rw [hBd, hF0]; simp [put, writeBit, hq]
  have tmpM (q : Wire) (hq : q ∈ [one, U, V, F, pk]) (i : Nat) (hi : i < 256) : q ≠ w i :=
    fun e => (htx q hq).1 (e ▸ wmem i hi)
  have bsW : ∀ b ∈ bs, b.work ∈ work := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
  have bsI : ∀ b ∈ bs, b.input ∈ it.map w := by
    intro b hb
    have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
  have hlenbs : it.length = bs.length := by
    have h1 : (bs.map ZeroBit.input).length = (it.map w).length := by rw [zp.1]
    simpa using h1.symm
  have hT : triples xs work one tr.idx = (i0, one, p0) :: tri p0 it bs := by rw [hidx]; rfl
  set T := triples xs work one tr.idx with hTdef
  have hsplit := idx_cat tr pv.2.2.1 pv.1 pv.2.1
  have hTm : T.map (·.1) = tr.topL ++ (tr.midL ++ tr.lowL) := by
    rw [← hsplit, hT, hidx, List.map_cons, tri_fst p0 it bs hlenbs]
  set Tt := T.take tr.topL.length with hTt
  set Tm := (T.drop tr.topL.length).take tr.midL.length with hTmm
  set Tl := T.drop (tr.topL.length + tr.midL.length) with hTl
  have mt : Tt.map (·.1) = tr.topL := by
    rw [hTt, List.map_take, hTm, List.take_left' rfl]
  have mm : Tm.map (·.1) = tr.midL := by
    rw [hTmm, List.map_take, List.map_drop, hTm, List.drop_left' rfl, List.take_left' rfl]
  have ml : Tl.map (·.1) = tr.lowL := by
    rw [hTl, List.map_drop, hTm, ← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl]
  have cat : Tt ++ (Tm ++ Tl) = T := by
    have e1 : Tm ++ Tl = T.drop tr.topL.length := by
      rw [hTl, ← List.drop_drop]; exact List.take_append_drop _ _
    rw [e1]; exact List.take_append_drop _ _
  have memT : ∀ y ∈ Tt ++ Tm ++ Tl, y ∈ T := by
    intro y hy; rw [← cat]; simpa [List.append_assoc] using hy
  -- all chain wires
  have triW : ∀ y ∈ T, (y.2.1 = one ∨ y.2.1 = p0 ∨ y.2.1 ∈ work) ∧ (y.2.2 = p0 ∨ y.2.2 ∈ work) := by
    intro y hy
    rw [hT] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨h1, b, hb, h2⟩ := tri_wires _ _ _ y hy
      refine ⟨?_, Or.inr (h2 ▸ bsW b hb)⟩
      rcases h1 with e | ⟨d, hd, e⟩
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (e ▸ bsW d hd))
  have p0x : p0 ∈ xs := wmem i0 (ix.2.2.2.2 i0 (by rw [hidx]; simp))
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at htmp
  obtain ⟨⟨oU, oV, oF, oP⟩, ⟨UV, UF, UP⟩, ⟨VF, VP⟩, FP⟩ := htmp
  have tmp1 : ∀ q ∈ [U, V, F, pk], q ≠ one := by
    intro q hq e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with e1 | e1 | e1 | e1
    · exact oU (e.symm.trans e1)
    · exact oV (e.symm.trans e1)
    · exact oF (e.symm.trans e1)
    · exact oP (e.symm.trans e1)
  have tmpIn : ∀ q ∈ [U, V, F, pk], q ∈ [one, U, V, F, pk] := fun q hq => List.mem_cons_of_mem _ hq
  have offT : ∀ q ∈ [U, V, F, pk], ∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q := by
    intro q hq y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := (htx q (tmpIn q hq)).1
    have a2 := (htx q (tmpIn q hq)).2.1
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact (tmp1 q hq).symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have gone : W ≠ one := fun e => (htx one (by simp)).2.2 e.symm
  have offG : ∀ y ∈ T, y.2.1 ≠ W ∧ y.2.2 ≠ W := by
    intro y hy
    obtain ⟨h1, h2⟩ := triW y hy
    have a1 := hWx.1
    have a2 := hWx.2
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e | e
      · rw [e]; exact gone.symm
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
    · rcases h2 with e | e
      · rw [e]; exact fun E => a1 (E ▸ p0x)
      · exact fun E => a2 (E ▸ e)
  have endOff : ∀ (A : List (Nat × Wire × Wire)) (p q : Wire), (∀ y ∈ A, y ∈ T) → p ≠ q →
      (∀ y ∈ T, y.2.1 ≠ q ∧ y.2.2 ≠ q) → endW p A ≠ q := by
    intro A p q hA hp hy
    rcases endW_mem p A with e | ⟨y, h, e⟩
    · rw [e]; exact hp
    · rw [e]; exact (hy y (hA y h)).2
  have inTt : ∀ y ∈ Tt, y ∈ T := fun y h => List.mem_of_mem_take h
  have inTm : ∀ y ∈ Tm, y ∈ T := fun y h => List.mem_of_mem_drop (List.mem_of_mem_take h)
  have mU : U ∈ [U, V, F, pk] := by simp
  have mV : V ∈ [U, V, F, pk] := by simp
  have mF : F ∈ [U, V, F, pk] := by simp
  have mP : pk ∈ [U, V, F, pk] := by simp
  have h1l : tr.lo < 256 := by simp only [Tri.lo]; omega
  have h1h : tr.hi < 256 := by simp only [Tri.hi]; omega
  have nx (q : Wire) (hq : q ∈ [U, V, F, pk]) (i : Nat) (hi : i < 256) : w i ≠ q :=
    (tmpM q (tmpIn q hq) i hi).symm
  have eO := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tt one q inTt (tmp1 q hq).symm (offT q hq)
  have eM := fun (q : Wire) (hq : q ∈ [U, V, F, pk]) =>
    endOff Tm (endW one Tt) q inTm (eO q hq) (offT q hq)
  have hTall : ∀ y ∈ Tt ++ Tm ++ Tl, (y.2.1 ≠ U ∧ y.2.2 ≠ U) ∧ (y.2.1 ≠ V ∧ y.2.2 ≠ V) ∧
      (y.2.1 ≠ F ∧ y.2.2 ≠ F) := fun y hy =>
    ⟨offT U mU y (memT y hy), offT V mV y (memT y hy), offT F mF y (memT y hy)⟩
  have Pp : ProperProgram (preOf tr xs work one U V F) :=
    pre_proper _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nx V mV _ h1l) UV (nx F mF _ h1h) VF (eM U mU) (eO V mV) hTall
  have pkNot : pk ∉ wires (preOf tr xs work one U V F) := by
    apply pre_not
    · exact ⟨tmp1 pk mP, Ne.symm UP, Ne.symm VP, Ne.symm FP, (nx pk mP _ h1l).symm, (nx pk mP _ h1h).symm,
        (eM pk mP).symm, (eO pk mP).symm⟩
    · intro y hy
      have := offT pk mP y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have gNot : W ∉ wires (preOf tr xs work one U V F) := by
    have gU : W ≠ U := fun e => (htx U (by simp)).2.2 e.symm
    have gV : W ≠ V := fun e => (htx V (by simp)).2.2 e.symm
    have gF : W ≠ F := fun e => (htx F (by simp)).2.2 e.symm
    apply pre_not
    · refine ⟨gone, gU, gV, gF, ?_, ?_, ?_, ?_⟩
      · exact fun e => hWx.1 (e ▸ wmem _ h1l)
      · exact fun e => hWx.1 (e ▸ wmem _ h1h)
      · exact (endOff Tm (endW one Tt) W inTm (endOff Tt one W inTt gone.symm offG) offG).symm
      · exact (endOff Tt one W inTt gone.symm offG).symm
    · intro y hy
      have := offG y (memT y hy)
      exact ⟨this.1.symm, this.2.symm⟩
  have wNot : ∀ q, q ∉ work → ∀ b ∈ bs, b.work ≠ q := fun q hq b hb e => hq (e ▸ bsW b hb)
  have tmpP : ∀ q ∈ [one, U, V, F, pk], q ∉ (i0 :: it).map w := fun q hq h =>
    (htx q hq).1 (Psub q (by rw [← hlP]; exact h))
  have Bt : ∀ q ∈ [one, U, V, F], B.basis q = false := by
    intro q hq
    have hq' : q ∈ [one, U, V, F, pk] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with h | h | h | h <;> simp [h]
    rw [Boff q (htx q hq').2.2, fill_outside _ _ _ q (wNot q (htx q hq').2.1), s2out q (tmpP q hq')]
    exact hto q hq
  have pivB (i : Nat) (hi : i = tr.r1 ∨ i = tr.r2) : B.basis (w i) = x.testBit i := by
    have hi256 : i < 256 := by rcases hi with rfl | rfl <;> [exact pv.1; exact pv.2.1]
    have nP : w i ∉ (i0 :: it).map w := by
      rcases hi with rfl | rfl <;> [exact x1P'; exact x2P']
    have nW : w i ∉ work := fun h => hdisj _ h (wmem i hi256)
    have ng : w i ≠ W := fun e => hWx.1 (e ▸ wmem i hi256)
    rw [Boff _ ng, fill_outside _ _ _ _ (wNot _ nW), s2out _ nP]
    exact xbit i hi256
  have hiP : tr.hi = tr.r1 ∨ tr.hi = tr.r2 := by simp only [Tri.hi]; omega
  have loP : tr.lo = tr.r1 ∨ tr.lo = tr.r2 := by simp only [Tri.lo]; omega
  have hxr1 : s.basis xr1 = x.testBit tr.r1 := xbit _ pv.1
  have hxr2 : s.basis xr2 = x.testBit tr.r2 := xbit _ pv.2.1
  let mtf : Nat → Bool := fun i => x.testBit i == tr.tgt i (x.testBit tr.r1, x.testBit tr.r2)
  have i0m : i0 ∈ tr.idx := by rw [hidx]; simp
  have itm : ∀ i ∈ it, i ∈ tr.idx := fun i hi => by rw [hidx]; simp [hi]
  have p0ne : one ≠ p0 := fun e => (htx one (by simp)).1 (e ▸ p0x)
  have p0g : p0 ≠ W := fun e => hWx.1 (e ▸ p0x)
  have p0W : p0 ∉ work := fun h => hdisj _ h p0x
  have hc0 : s2.basis p0 = mtf i0 := by
    rw [s2p0, hxr1, hxr2, xbit i0 (ix.2.2.2.2 i0 i0m)]
  have hchain : Chain (writeBit B.basis one true) mtf true (Tt ++ (Tm ++ Tl)) := by
    rw [cat, hT]
    refine ⟨by simp [writeBit], ?_, ?_⟩
    · simp only [writeBit, Function.update_apply, Ne.symm p0ne, if_false, Bool.true_and]
      rw [Boff _ p0g, fill_outside _ _ _ _ (wNot _ p0W), hc0]
    · have hmt : ∀ k (hk : k < it.length), mtf it[k] = !s2.basis (bs[k]'(hlenbs ▸ hk)).input := by
        intro k hk
        have hin : (bs[k]'(hlenbs ▸ hk)).input = w it[k] := by
          have e1 : (bs.map ZeroBit.input)[k]'(by simpa using hlenbs ▸ hk) = (bs[k]'(hlenbs ▸ hk)).input := by
            simp
          have e2 : (it.map w)[k]'(by simpa using hk) = w it[k] := by simp
          rw [← e1, ← e2]
          exact List.getElem_of_eq zp.1 _
        have im : it[k] ∈ it := List.getElem_mem _
        rw [hin, s2it _ im, hxr1, hxr2, xbit _ (ix.2.2.2.2 _ (itm _ im))]
        simp only [mtf]
        cases x.testBit it[k] <;> cases tr.tgt it[k] (x.testBit tr.r1, x.testBit tr.r2) <;> rfl
      have cf := chain_fill mtf p0 it bs s2.basis (true && mtf i0) hlenbs chnd chz (by simpa using hc0) hmt
      apply chain_congr _ _ _ _ _ _ cf
      intro y hy
      have hyw := tri_wires _ _ _ y hy
      have side : ∀ q, (q = p0 ∨ ∃ b ∈ bs, q = b.work) →
          fill p0 bs s2.basis q = writeBit B.basis one true q := by
        intro q hq
        have qx : q ∈ xs ∨ q ∈ work := by
          rcases hq with e | ⟨b, hb, e⟩
          · exact Or.inl (e ▸ p0x)
          · exact Or.inr (e ▸ bsW b hb)
        have ng : q ≠ W := by
          intro e
          rcases qx with h | h
          · exact hWx.1 (e ▸ h)
          · exact hWx.2 (e ▸ h)
        have no : q ≠ one := by
          intro e
          rcases qx with h | h
          · exact (htx one (by simp)).1 (e ▸ h)
          · exact (htx one (by simp)).2.1 (e ▸ h)
        simp only [writeBit, Function.update_apply, no, if_false]
        exact (Boff q ng).symm
      exact ⟨side _ hyw.1, side _ (Or.inr hyw.2)⟩
  have nlo (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.lo ≠ q := nx q hq _ h1l
  have nhi (q : Wire) (hq : q ∈ [U, V, F, pk]) : w tr.hi ≠ q := nx q hq _ h1h
  have FV := F_value tr v pv.2.2.1 x hx one U V F (w tr.hi) (w tr.lo) Tt Tm Tl mt mm ml UV UF VF
    (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
    (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
    (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l)) (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h))
    hTall B (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp)) (Bt one (by simp))
    (pivB _ hiP) (pivB _ loP) hchain
  have gpk : W ≠ pk := fun e => (htx pk (by simp)).2.2 e.symm
  have hE : ∀ m', run (extractOutput tr xs work one U V F pk W) m' B =
      put B pk (B.basis pk ^^ ((run (preOf tr xs work one U V F) [] B).basis W &&
        (run (preOf tr xs work one U V F) [] B).basis F)) :=
    by
      intro m'
      have htpk : ∀ z ∈ MeasuredFV.correctionWires tr.A Tt, z ≠ pk := by
        apply MeasuredFV.correctionWires_off_research
        intro y hy
        exact offT pk mP y (inTt y hy)
      have hmpk : ∀ z ∈ MeasuredFV.correctionWires tr.A Tm, z ≠ pk := by
        apply MeasuredFV.correctionWires_off_research
        intro y hy
        exact offT pk mP y (inTm y hy)
      have hlpk : ∀ y ∈ Tl, y.2.1 ≠ pk ∧ y.2.2 ≠ pk := by
        intro y hy
        exact offT pk mP y (memT y (by simp [hy]))
      have pkB : B.basis pk = s.basis pk := by
        rw [Boff pk (htx pk (by simp)).2.2,
          fill_outside _ _ _ pk (wNot pk (htx pk (by simp)).2.1), s2out pk (tmpP pk (by simp))]
      have hFP : (run (preOf tr xs work one U V F) [] B).basis F = decide (tr.A < x) := FV
      have hWP : (run (preOf tr xs work one U V F) [] B).basis W = Gv := by
        rw [run_preserves_outside _ [] B W gNot, hBd]; simp [put, writeBit]
      have known : (run (preOf tr xs work one U V F) [] B).basis pk =
          ((run (preOf tr xs work one U V F) [] B).basis W &&
           (run (preOf tr xs work one U V F) [] B).basis F) := by
        rw [run_preserves_outside _ [] B pk pkNot, pkB, hFP, hWP]
        exact hKnownPark
      rw [extractOutput_equiv tr xs work one U V F pk W gpk FP B m' known]
      have fast := MeasuredFV.fastExtract_semantics tr.A (tr.A.testBit tr.lo) (tr.A.testBit tr.hi)
        one U V F (w tr.lo) (w tr.hi) (endW (endW one Tt) Tm) (endW one Tt) Tt Tm Tl W pk
        FP VP UP (nlo pk mP) (nhi pk mP) (eM pk mP) (eO pk mP) htpk hmpk oP hlpk UV UF VF
        (nlo U mU) (nlo V mV) (nlo F mF) (nhi U mU) (nhi V mV) (nhi F mF)
        (eM U mU) (eM V mV) (eM F mF) (eO U mU) (eO V mV) (eO F mF) oU oV oF
        (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1l))
        (fun e => (htx one (by simp)).1 (e ▸ wmem _ h1h)) hTall B (m'.drop 1)
        (Bt U (by simp)) (Bt V (by simp)) (Bt F (by simp))
      simpa only [extract, preOf, hTt, hTmm, hTl, hTdef, hw, put] using fast
  have FVe : (run (preOf tr xs work one U V F) [] B).basis F = decide (tr.A < x) := FV
  have hRW : (run (preOf tr xs work one U V F) [] B).basis W = Gv := by
    rw [run_preserves_outside _ [] B W gNot, hBd]; simp [put, writeBit]
  simp only [FVe, hRW] at hE
  have rd (q : Wire) (hx' : q ∉ xs) (hw' : q ∉ work) : F0.basis q = s.basis q := by
    rw [hF0]
    show fill p0 bs s2.basis q = s.basis q
    rw [fill_outside _ _ _ q (wNot q hw'), s2out q (fun h => hx' (Psub q (by rw [← hlP]; exact h)))]
  have rq (q : Wire) (hq : q ∈ [y0, c, f, g, O, D, H, t1, t2, u]) : F0.basis q = s.basis q := rd q (hextx q hq).1 (hextx q hq).2
  have pkx := htx pk (by simp)
  have Wf : F0.basis W = false := by rw [rd W hWx.1 hWx.2]; exact hW0
  have Pf : F0.basis pk = s.basis pk := rd pk pkx.1 pkx.2.1
  have pkW : pk ≠ W := pkx.2.2
  obtain ⟨eC, eG, eO, eD, eH⟩ := hWe
  have cpk : c ≠ pk := fun e => hpkE (by simp [e])
  have gpk' : g ≠ pk := fun e => hpkE (by simp [e])
  have Opk : O ≠ pk := fun e => hpkE (by simp [e])
  have Dpk : D ≠ pk := fun e => hpkE (by simp [e])
  have Hpk : H ≠ pk := fun e => hpkE (by simp [e])
  set val := (s.basis pk ^^ (Gv && decide (tr.A < x))) with hval
  have hEf : ∀ m', run (Gc c g O D H W ++ (extractOutput tr xs work one U V F pk W ++ Gc c g O D H W)) m' F0 =
      put F0 pk val := by
    intro m'
    rw [run_append, Gc_run c g O D H W eC eG eO eD eH, run_append]
    have e1 : (put F0 W (F0.basis W ^^ (F0.basis c ^^ F0.basis g ^^ F0.basis O ^^ F0.basis D ^^ F0.basis H))) = B := by
      rw [Wf, rq c (by simp), rq g (by simp), rq O (by simp), rq D (by simp), rq H (by simp),
        Bool.false_xor, hBd]
    rw [e1, hE, Gc_run c g O D H W eC eG eO eD eH]
    have bpk : B.basis pk = s.basis pk := by rw [← Pf, hBd]; simp [put, writeBit, pkW]
    rw [bpk]
    apply State.extensionality
    · rw [hBd]; rfl
    funext q
    by_cases q1 : q = W
    · subst q1
      rw [hBd]
      simp [put, writeBit, Function.update_apply, Ne.symm pkW, eC, eG, eO, eD, eH, cpk, gpk', Opk, Dpk, Hpk,
        rq c (by simp), rq g (by simp), rq O (by simp), rq D (by simp), rq H (by simp), Wf, hGv]
    · by_cases q2 : q = pk
      · subst q2; rw [hBd]; simp [put, writeBit, q1, hval]
      · rw [hBd]; simp [put, writeBit, q1, q2]
  have hpk1 : pk ∉ (p0 :: bs.flatMap ZeroBit.wires) := by
    intro h
    rcases List.mem_cons.mp h with e | h
    · exact pkx.1 (e ▸ p0x)
    · obtain ⟨b, hb, hw'⟩ := List.mem_flatMap.mp h
      simp only [ZeroBit.wires, List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with e | e
      · obtain ⟨i, hi, e2⟩ := List.mem_map.mp (bsI b hb)
        exact pkx.1 (e ▸ e2 ▸ wmem i (ix.2.2.2.2 i (itm i hi)))
      · exact pkx.2.1 (e ▸ bsW b hb)
  have hpk2 : pk ∉ wires ([Instr.X p0] ++ tr.remapList xr1 xr2 w (i0 :: it)) := by
    rw [wires_append]
    simp only [Finset.mem_union, not_or]
    refine ⟨?_, remapList_not tr xr1 xr2 w _ pk (nx pk mP _ pv.1).symm (nx pk mP _ pv.2.1).symm (tmpP pk (by simp))⟩
    have np : pk ≠ p0 := (nx pk mP i0 (ix.2.2.2.2 i0 i0m)).symm
    simp [wires, Instr.wires, np]
  have hpk3 : pk ∉ wires (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u (lastWire p0 bs)) := by
    intro h
    have hm := OutputOpt.otailL_support tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u _ h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with e1 | e1 | e1 | hm
    · apply hpk1
      rcases lastWire_mem p0 bs with e2 | ⟨b, hb, e2⟩
      · rw [e1, e2]; exact List.mem_cons_self
      · rw [e1, e2]
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
    · exact (nx pk mP _ pv.1) e1.symm
    · exact (nx pk mP _ pv.2.1) e1.symm
    · exact hpkE (by simpa using hm)
  rw [hF0] at hEf
  have M := main _ pk val hEf hpk1 hpk2 hpk3 m
  have hprog : OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([Instr.X (w i0)] ++
      (zeroWith (OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
      ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [OutputOpt.oclassifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  have hprogF : oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([Instr.X (w i0)] ++
      (zeroWith (fun h => (Gc c g O D H W ++ (extractOutput tr xs work one U V F pk W ++ Gc c g O D H W)) ++
          OutputOpt.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h)
        (w i0) (zeroPorts (it.map w) work) ++
      ([Instr.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [oclassifierF, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hprogF, hprog]
  exact M

theorem pf_sum (tr : Tri) (yc n r1 r2 y0 : Bool) :
    ((predFlags tr yc n r1 r2 y0).1 ^^ (predFlags tr yc n r1 r2 y0).2.1 ^^
      (predFlags tr yc n r1 r2 y0).2.2.1 ^^ (predFlags tr yc n r1 r2 y0).2.2.2) = n := by
  unfold predFlags
  split_ifs
  · dsimp only
    generalize (r1 == tr.B.testBit tr.r1) = a
    generalize (r2 == tr.S.testBit tr.r2) = b
    generalize (y0 == yc) = c
    cases n <;> cases a <;> cases b <;> cases c <;> rfl
  · dsimp only
    generalize (r1 == tr.S.testBit tr.r1) = a
    generalize (r2 == tr.B.testBit tr.r2) = b
    generalize (y0 == yc) = c
    cases n <;> cases a <;> cases b <;> cases c <;> rfl

/-- The pool site that carries the generic flag while the wrap flag is cleared. -/
def wW (L : ControlledPointLayout) : Wire := L.core.poolWire 723

theorem out_flag_wires :
    [layout.dialogPool.getD 253 0, layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0,
      layout.point.finite, FlagEntry.pkW layout].Nodup ∧
    (∀ q ∈ [layout.dialogPool.getD 253 0, layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0,
      layout.point.finite, FlagEntry.pkW layout],
      q ∉ layout.point.x ∧ q ∉ layout.dialogPool.take 253 ∧ q ≠ wW layout) ∧
    (wW layout ∉ layout.point.x ∧ wW layout ∉ layout.dialogPool.take 253) ∧
    (layout.control ≠ wW layout ∧ layout.genericSelect ≠ wW layout ∧ parkWire layout ≠ wW layout ∧
      layout.doubleSelect ≠ wW layout ∧ layout.core.equalNegY ≠ wW layout) ∧
    FlagEntry.pkW layout ∉ [yLow layout, layout.control, layout.point.finite, layout.genericSelect,
      parkWire layout, layout.doubleSelect, layout.core.equalNegY, layout.dialogPool.getD 253 0,
      layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0] ∧
    FlagEntry.pkW layout ∈ layout.dialogPool ∧ wW layout ∈ layout.dialogPool ∧
    FlagEntry.pkW layout ≠ parkWire layout ∧ wW layout ≠ parkWire layout ∧
    layout.dialogPool.getD 253 0 ≠ parkWire layout ∧ layout.dialogPool.getD 254 0 ≠ parkWire layout ∧
    layout.dialogPool.getD 255 0 ≠ parkWire layout := by
  decide +kernel

open Classical in
/-- The state the old output stage hands to its classifier. -/
theorem out_mid {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s0 : State) (hs : PointDialogBoundary layout R b (fun _ => false) s0.basis) (t : State) (m : List Bool)
    (htx : regValue layout.point.x t.basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (hty : regValue layout.point.y t.basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (htf : t.basis layout.point.finite = false)
    (htg : t.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (htr : ∀ q, q ∉ layout.point.x → q ∉ layout.point.y → q ≠ layout.point.finite →
      q ≠ layout.genericSelect → t.basis q = s0.basis q) :
    ∃ u : State, u = run (ocorners layout (.some hc))
        (List.drop (measurementCount (predecL (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect
          layout.control (layout.point.x.getD (triOf (.some hc)).r1 0)
          (layout.point.x.getD (triOf (.some hc)).r2 0) (yLow layout) (parkWire layout)
          layout.doubleSelect layout.core.equalNegY)) m)
        (run (predecL (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect
          layout.control (layout.point.x.getD (triOf (.some hc)).r1 0)
          (layout.point.x.getD (triOf (.some hc)).r2 0) (yLow layout) (parkWire layout)
          layout.doubleSelect layout.core.equalNegY) m t) ∧
      regValue layout.point.x u.basis = codeX (if b then R + .some hc else R) ∧
      (∀ q ∈ layout.dialogPool, q ≠ parkWire layout → u.basis q = false) ∧
      u.basis layout.point.finite = false ∧
      (u.basis layout.genericSelect = (u.basis layout.control &&
          oX (triOf (.some hc)) (triOf (.some hc)).S layout.point.x u.basis) ∧
        u.basis (parkWire layout) = (u.basis layout.control &&
          oX (triOf (.some hc)) (triOf (.some hc)).A layout.point.x u.basis &&
          (u.basis (yLow layout) == yBit (.some hc))) ∧
        u.basis layout.doubleSelect = (u.basis layout.control &&
          oX (triOf (.some hc)) (triOf (.some hc)).B layout.point.x u.basis &&
          (u.basis (yLow layout) == yBit ((.some hc : Point) + .some hc))) ∧
        u.basis layout.core.equalNegY = (exceptionBit (.some hc) && u.basis layout.control &&
          oX (triOf (.some hc)) (triOf (.some hc)).A layout.point.x u.basis &&
          (u.basis (yLow layout) != yBit (.some hc)))) ∧
      dialogOrdinary b R (.some hc) = (u.basis layout.control ^^ u.basis layout.genericSelect ^^
        u.basis (parkWire layout) ^^ u.basis layout.doubleSelect ^^ u.basis layout.core.equalNegY) := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hnC : -C ≠ 0 := neg_ne_zero.mpr hC
  have hCn : C ≠ -C := (doubling_enabled_iff hc).mp (of_decide_eq_true (cy_ne_neg hc))
  have h2C : C + C ≠ 0 := fun e => hCn (eq_neg_of_add_eq_zero_left e)
  have v : (triOf C).Valid := triOf_valid hc
  have pv := Tri.pivots v
  obtain ⟨fx6n, fx6x, fx10n, fx10x, parkP, parkY, p253, p254, p255⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  set xr1 := layout.point.x.getD (triOf C).r1 0 with hxr1
  set xr2 := layout.point.x.getD (triOf C).r2 0 with hxr2
  have x1m : xr1 ∈ layout.point.x := by
    rw [hxr1, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x2m : xr2 ∈ layout.point.x := by
    rw [hxr2, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x12 : xr1 ≠ xr2 := by
    intro e
    rw [hxr1, hxr2, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact pv.2.2.1 ((List.Nodup.getElem_inj_iff hxn).mp e)
  have hnd8 : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY].Nodup := by
    have hperm : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY].Perm
        ([xr1, xr2] ++ [layout.genericSelect, layout.control, yLow layout, parkWire layout,
          layout.doubleSelect, layout.core.equalNegY]) := by
      show (([layout.genericSelect, layout.control] ++ [xr1, xr2]) ++ [yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY]).Perm
        (([xr1, xr2] ++ [layout.genericSelect, layout.control]) ++ [yLow layout, parkWire layout,
          layout.doubleSelect, layout.core.equalNegY])
      exact List.perm_append_comm.append_right _
    apply hperm.nodup_iff.mpr
    rw [List.nodup_append]
    refine ⟨by simp [x12], fx6n, ?_⟩
    intro a ha b hb e
    subst e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact fx6x _ hb x1m
    · exact fx6x _ hb x2m
  -- reads of the post-generic state
  have off (q : Wire) (hq : q ∈ [layout.control, layout.infinitySelect, layout.doubleSelect, layout.core.generic,
      layout.core.equalX, layout.core.equalNegY, layout.core.double, parkWire layout]) :
      t.basis q = s0.basis q := by
    obtain ⟨a, b', c, d⟩ := out_off q hq
    exact htr q a b' c d
  have flag0 (q : Wire) (hq : q ∈ layout.inPlaceFlags) : s0.basis q = false := hs.flags q hq
  have pool0 (q : Wire) (hq : q ∈ layout.dialogPool) : s0.basis q = false :=
    (regValue_zero _ _).mp hs.clean q hq
  have tpool (q : Wire) (hq : q ∈ layout.dialogPool) : t.basis q = false := by
    obtain ⟨a, b', -, -, -⟩ := out_pool_off q hq
    rw [htr q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) a b']
    exact pool0 q hq
  have hb0 : t.basis layout.control = b := by rw [off _ (by simp)]; exact hs.control
  have hz1 : t.basis (parkWire layout) = false ∧ t.basis layout.doubleSelect = false ∧
      t.basis layout.core.equalNegY = false := by
    refine ⟨tpool _ parkP, ?_, ?_⟩
    · rw [off _ (by simp)]; exact flag0 _ (by simp [flags_list])
    · rw [off _ (by simp)]; exact flag0 _ (by simp [flags_list])
  have hx1v : t.basis xr1 = (codeX (if dialogOrdinary b R C then R + C else R)).testBit (triOf C).r1 := by
    rw [← htx, LocalWireModel.reg_bit _ _ _ (by omega)]
  have hx2v : t.basis xr2 = (codeX (if dialogOrdinary b R C then R + C else R)).testBit (triOf C).r2 := by
    rw [← htx, LocalWireModel.reg_bit _ _ _ (by omega)]
  have hy0v : t.basis (yLow layout) = yBit (if dialogOrdinary b R C then R + C else R) := by
    rw [yLow_bit t.basis, hty, pointY_bit0]
  have pfv : predFlags (triOf C) (yBit C) (t.basis layout.genericSelect ^^ t.basis layout.control)
      (t.basis xr1) (t.basis xr2) (t.basis (yLow layout)) =
      (dialogInfinity b R, dialogDouble b R C, dialogException b R C, dialogInversePoint b R C) := by
    rw [htg, hb0, hx1v, hx2v, hy0v]; exact predFlags_dialog hc b R
  rw [predecL_run (triOf C) (yBit C) _ _ _ _ _ _ _ _ hnd8 t m hz1, pfv]
  -- stage 2: corners
  generalize ht1 : (⟨t.phase, writeBit (writeBit (writeBit (writeBit t.basis layout.genericSelect
    (dialogInversePoint b R C)) (parkWire layout) (dialogInfinity b R)) layout.doubleSelect
    (dialogDouble b R C)) layout.core.equalNegY (dialogException b R C)⟩ : State) = t1
  obtain ⟨gp, gd, gh, pd, ph, dh⟩ := out_ne
  have t1off (q : Wire) (h1 : q ≠ layout.genericSelect) (h2 : q ≠ parkWire layout) (h3 : q ≠ layout.doubleSelect)
      (h4 : q ≠ layout.core.equalNegY) : t1.basis q = t.basis q := by
    rw [← ht1]; simp [writeBit, Function.update, h1, h2, h3, h4]
  have t1g : t1.basis layout.genericSelect = dialogInversePoint b R C := by
    rw [← ht1]; simp [writeBit, Function.update, gp, gd, gh]
  have t1p : t1.basis (parkWire layout) = dialogInfinity b R := by
    rw [← ht1]; simp [writeBit, Function.update, pd, ph]
  have t1d : t1.basis layout.doubleSelect = dialogDouble b R C := by
    rw [← ht1]; simp [writeBit, Function.update, dh]
  have t1h : t1.basis layout.core.equalNegY = dialogException b R C := by
    rw [← ht1]; simp [writeBit, Function.update]
  have t1ph : t1.phase = t.phase := by rw [← ht1]
  have notw (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.genericSelect ∧ q ≠ parkWire layout ∧ q ≠ layout.doubleSelect ∧ q ≠ layout.core.equalNegY := by
    refine ⟨fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq), fun e => pool_not_point _ parkP (e ▸ hq),
      fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq), fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq)⟩
  have t1x : regValue layout.point.x t1.basis = regValue layout.point.x t.basis := by
    apply regValue_congr; intro q hq
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_left _ hq)
    exact t1off q a b' c d
  have t1y : regValue layout.point.y t1.basis = regValue layout.point.y t.basis := by
    apply regValue_congr; intro q hq
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_right _ hq)
    exact t1off q a b' c d
  -- stage 2: corners
  obtain ⟨c1, c2, c3, c4⟩ := ocorners_run layout layout_widths layout_nodup C t1
    (List.drop (measurementCount (predecL (triOf C) (yBit C) layout.genericSelect layout.control xr1 xr2
      (yLow layout) (parkWire layout) layout.doubleSelect layout.core.equalNegY)) m)
  generalize ht2 : run (ocorners layout C) (List.drop (measurementCount (predecL (triOf C) (yBit C)
    layout.genericSelect layout.control xr1 xr2 (yLow layout) (parkWire layout) layout.doubleSelect
    layout.core.equalNegY)) m) t1 = t2 at c1 c2 c3 c4 ⊢
  have cv := corners_value hc b R
  rw [t1x, htx, t1p, t1d, t1g, t1h, cv.1] at c2
  rw [t1y, hty, t1p, t1d, t1g, t1h, cv.2] at c3
  set S := if b then R + C else R with hSdef
  have t2off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) : t2.basis q = t1.basis q := c4 q hx hy
  have offxy (q : Wire) (hq : q ∈ layout.dialogPool) : q ∉ layout.point.x ∧ q ∉ layout.point.y :=
    ⟨fun h => pool_not_point q hq (List.mem_append_left _ h), fun h => pool_not_point q hq (List.mem_append_right _ h)⟩
  have flxy (q : Wire) (hq : q ∈ layout.inPlaceFlags) : q ∉ layout.point.x ∧ q ∉ layout.point.y :=
    ⟨fun h => flags_not_point q hq (List.mem_append_left _ h), fun h => flags_not_point q hq (List.mem_append_right _ h)⟩
  have t2pool (q : Wire) (hq : q ∈ layout.dialogPool) (hp : q ≠ parkWire layout) : t2.basis q = false := by
    obtain ⟨a, b'⟩ := offxy q hq
    obtain ⟨-, g1, d1, h1, -⟩ := out_pool_off q hq
    rw [t2off q a b', t1off q g1 hp d1 h1]; exact tpool q hq
  have t2ctl : t2.basis layout.control = b := by
    obtain ⟨a, b', -, -⟩ := out_off layout.control (by simp)
    rw [t2off _ a b', t1off _ (by decide) (by decide) (by decide) (by decide)]; exact hb0
  have t2f : t2.basis layout.point.finite = false := by
    have hfx := finite_not_flag.2
    rw [t2off _ (fun h => hfx (List.mem_append_left _ h)) (fun h => hfx (List.mem_append_right _ h)),
      t1off _ (by decide) (by decide) (by decide) (by decide)]; exact htf
  have t2y0 : t2.basis (yLow layout) = yBit S := by rw [yLow_bit t2.basis, c3, pointY_bit0]
  have gF := flxy layout.genericSelect (by simp [flags_list])
  have dF := flxy layout.doubleSelect (by simp [flags_list])
  have hF := flxy layout.core.equalNegY (by simp [flags_list])
  have pF := offxy (parkWire layout) parkP
  have t2g : t2.basis layout.genericSelect = dialogInversePoint b R C := by rw [t2off _ gF.1 gF.2, t1g]
  have t2p : t2.basis (parkWire layout) = dialogInfinity b R := by rw [t2off _ pF.1 pF.2, t1p]
  have t2d : t2.basis layout.doubleSelect = dialogDouble b R C := by rw [t2off _ dF.1 dF.2, t1d]
  have t2h : t2.basis layout.core.equalNegY = dialogException b R C := by rw [t2off _ hF.1 hF.2, t1h]
  -- the match bits on the output abscissa
  have oS : oX (triOf C) (triOf C).S layout.point.x t2.basis = decide (S = 0) := by
    rw [oX_eq _ v _ hxl _ _ v.hS (Tri.tgt_S v), c2]
    exact decide_eq_decide.mpr (code_sentinel S)
  have oA : oX (triOf C) (triOf C).A layout.point.x t2.basis = decide (codeX S = pointX C) := by
    rw [oX_eq _ v _ hxl _ _ v.hA (Tri.tgt_A), c2]; rfl
  have oB : oX (triOf C) (triOf C).B layout.point.x t2.basis = decide (codeX S = pointX (C + C)) := by
    rw [oX_eq _ v _ hxl _ _ v.hB (Tri.tgt_B v), c2]
    have e : (triOf C).B = pointX (C + C) := by
      show pointX (dialogExceptionPoint C) = _
      unfold dialogExceptionPoint; exact DHClass.pointX_neg _
    rw [e]
  have fo := dialogFlags_output b R C
  dsimp only at fo
  have hwl' : (layout.dialogPool.take 253).length = 253 := hwl
  have hfl : t2.basis layout.genericSelect = (t2.basis layout.control && oX (triOf C) (triOf C).S layout.point.x t2.basis) ∧
      t2.basis (parkWire layout) = (t2.basis layout.control && oX (triOf C) (triOf C).A layout.point.x t2.basis &&
        (t2.basis (yLow layout) == yBit C)) ∧
      t2.basis layout.doubleSelect = (t2.basis layout.control && oX (triOf C) (triOf C).B layout.point.x t2.basis &&
        (t2.basis (yLow layout) == yBit (C + C))) ∧
      t2.basis layout.core.equalNegY = (exceptionBit C && t2.basis layout.control &&
        oX (triOf C) (triOf C).A layout.point.x t2.basis && (t2.basis (yLow layout) != yBit C)) := by
    rw [t2g, t2p, t2d, t2h, t2ctl, oS, oA, oB, t2y0]
    have bmC := bool_match S C hC
    have bm2 := bool_match S (C + C) h2C
    have bmN := bool_match S (-C) hnC
    have e1 : (yBit S != yBit C) = (yBit S == yBit (-C)) := by
      rw [yBit_neg hc]; cases yBit S <;> cases yBit (.some hc : Point) <;> rfl
    have e2 : pointX C = pointX (-C) := (DHClass.pointX_neg C).symm
    have hdec : decide (C ≠ -C) = true := decide_eq_true hCn
    refine ⟨fo.2.2.1.symm, ?_, ?_, ?_⟩
    · rw [← fo.1, Bool.and_assoc, bmC]
    · rw [← fo.2.1, hdec, Bool.and_true, Bool.and_assoc, bm2]
    · rw [← fo.2.2.2, e1, e2, exc_bit]
      by_cases hen : dialogExceptionEnabled C
      · have h1 : decide (dialogExceptionEnabled C) = true := decide_eq_true hen
        have h2 : decide (dialogExceptionPoint C ≠ 0 ∧ dialogExceptionPoint C ≠ C ∧
            dialogExceptionPoint C ≠ -C) = true := decide_eq_true hen
        rw [h1, h2, Bool.and_true, Bool.true_and, Bool.and_assoc, bmN]
      · have h1 : decide (dialogExceptionEnabled C) = false := decide_eq_false hen
        have h2 : decide (dialogExceptionPoint C ≠ 0 ∧ dialogExceptionPoint C ≠ C ∧
            dialogExceptionPoint C ≠ -C) = false := decide_eq_false hen
        rw [h1, h2]; simp
  refine ⟨t2, rfl, c2, t2pool, t2f, hfl, ?_⟩
  have hsum := pf_sum (triOf C) (yBit C) (t.basis layout.genericSelect ^^ t.basis layout.control)
    (t.basis xr1) (t.basis xr2) (t.basis (yLow layout))
  rw [pfv, htg, hb0] at hsum
  dsimp only at hsum
  rw [t2ctl, t2g, t2p, t2d, t2h]
  revert hsum
  generalize dialogOrdinary b R C = G0
  generalize dialogInfinity b R = a0
  generalize dialogDouble b R C = a1
  generalize dialogException b R C = a2
  generalize dialogInversePoint b R C = a3
  cases G0 <;> cases b <;> cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> decide

theorem oX_congr (tr : Tri) (v : tr.Valid) (K : Nat) (xs : List Wire) (hlen : xs.length = 256)
    (st st' : BasisState) (h : ∀ q ∈ xs, st q = st' q) : oX tr K xs st = oX tr K xs st' := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have mem (i : Nat) (hi : i < 256) : xs.getD i 0 ∈ xs := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have e1 := h _ (mem _ pv.1)
  have e2 := h _ (mem _ pv.2.1)
  unfold oX matchBit
  rw [e1, e2]
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  apply forall₂_congr
  intro i hi
  rw [h _ (mem i (ix.2.2.2.2 i hi))]

/-- The output stage with the wrap flag cleared from its chain. -/
def outNew (L : ControlledPointLayout) (C : Point) : Program :=
  predecL (triOf C) (yBit C) L.genericSelect L.control (L.point.x.getD (triOf C).r1 0)
    (L.point.x.getD (triOf C).r2 0) (yLow L) (parkWire L) L.doubleSelect L.core.equalNegY ++
  ocorners L C ++
  oclassifierF (triOf C) (yBit C) (yBit (C + C)) (exceptionBit C) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect (parkWire L) L.doubleSelect L.core.equalNegY
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) (wW L)
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) L.point.finite
    (FlagEntry.pkW L) ++
  FiniteFlagInterval.zrep L

theorem oclassifierF_counts (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) (hwl : work.length = 253) :
    toffoliCount (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) ≤
      toffoliCount (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) + 2 ∧
    measurementCount (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) =
      measurementCount (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) + 3 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have ec := extractOutput_counts tr v xs work one U V F pk W
  have gt : toffoliCount (Gc c g O D H W) = 0 := by simp [Gc, toffoliCount]
  have gm : measurementCount (Gc c g O D H W) = 0 := by simp [Gc, measurementCount]
  have zo := zeroWith_counts_general
    (OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u) (if e then 3 else 5) 8
    (fun h => OutputOpt.otailL_counts tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  have zc := zeroWith_counts_general
    (fun h => (Gc c g O D H W ++ (extractOutput tr xs work one U V F pk W ++ Gc c g O D H W)) ++
      OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h)
    (toffoliCount (extractOutput tr xs work one U V F pk W) + (if e then 3 else 5)) 11
    (fun h => by
      have tc := OutputOpt.otailL_counts tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h
      simp only [toffoliCount_append, measurementCount_append, ec.2.1, gt, gm]
      exact ⟨by rw [tc.1]; omega, by rw [tc.2]⟩)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc zo
  have rt := remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold oclassifierF OutputOpt.oclassifier
  simp only [toffoliCount_append, measurementCount_append, rt, rm, zc.1, zc.2, zo.1, zo.2]
  have e9 := ec.1
  refine ⟨by omega, by omega⟩

/-- Keep the old output prefix records and align the unused tail after the measured cleanup. -/
def outMeasPad (L : ControlledPointLayout) (C : Point) (d : List Bool) : List Bool :=
  FlagEntry.pfx (measurementCount (OutputOpt.outStage L C)) d ++ d.drop (measurementCount (outNew L C))

open Classical in
theorem out_pad {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s0 : State) (hs : PointDialogBoundary layout R b (fun _ => false) s0.basis) (t : State)
    (htx : regValue layout.point.x t.basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (hty : regValue layout.point.y t.basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (htf : t.basis layout.point.finite = false)
    (htg : t.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (htr : ∀ q, q ∉ layout.point.x → q ∉ layout.point.y → q ≠ layout.point.finite →
      q ≠ layout.genericSelect → t.basis q = s0.basis q)
    (v : Bool) (hv : v = (dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R)))) :
    FlagEntry.Pad (outNew layout (.some hc)) (OutputOpt.outStage layout (.some hc))
      (put t (FlagEntry.pkW layout) v) t (outMeasPad layout (.some hc)) := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have tv : (triOf (.some hc)).Valid := triOf_valid hc
  have pv := Tri.pivots tv
  obtain ⟨fx6n, fx6x, fx10n, fx10x, parkP, parkY, p253, p254, p255⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ := out_flag_wires
  have mcC := (oclassifierF_counts (triOf (.some hc)) tv (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
    (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
    layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
    layout.point.finite (FlagEntry.pkW layout) hwl).2
  set pk := FlagEntry.pkW layout with hpk
  have pknX : pk ∉ layout.point.x := (w2 pk (by simp)).1
  have pknY : pk ∉ layout.point.y := fun h => pool_not_point pk w6 (List.mem_append_right _ h)
  have pkE := w5
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at pkE
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := pkE
  have pk0 : pk ∉ wires (predecL (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect
      layout.control (layout.point.x.getD (triOf (.some hc)).r1 0)
      (layout.point.x.getD (triOf (.some hc)).r2 0) (yLow layout) (parkWire layout)
      layout.doubleSelect layout.core.equalNegY) := by
    intro h
    have hm := Finset.mem_of_subset (predecL_support _ _ _ _ _ _ _ _ _ _) h
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hm
    have x1 : layout.point.x.getD (triOf (.some hc)).r1 0 ∈ layout.point.x := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have x2 : layout.point.x.getD (triOf (.some hc)).r2 0 ∈ layout.point.x := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    rcases hm with e | e | e | e | e | e | e | e
    · exact n4 e
    · exact n2 e
    · exact pknX (e ▸ x1)
    · exact pknX (e ▸ x2)
    · exact n1 e
    · exact n5 e
    · exact n6 e
    · exact n7 e
  have pk1 : pk ∉ wires (ocorners layout (.some hc)) := by
    intro h
    have hm := Finset.mem_of_subset (ocorners_support layout (.some hc)) h
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (e | e) | e | e | e | e
    · exact pknX e
    · exact pknY e
    · exact n5 e
    · exact n6 e
    · exact n4 e
    · exact n7 e
  have pk2 : pk ∉ wires (OutputOpt.oclassifier (triOf (.some hc)) (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
      (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
      layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
      (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)) := by
    intro h
    have hm := Finset.mem_of_subset (OutputOpt.oclassifier_support _ tv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl hwl) h
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with (e | e) | e
    · exact pknX e
    · exact (w2 pk (by simp)).2.1 e
    · rcases e with e | e | e | e | e | e | e | e | e | e
      · exact n1 e
      · exact n2 e
      · exact n3 e
      · exact n4 e
      · exact n5 e
      · exact n6 e
      · exact n7 e
      · exact n8 e
      · exact n9 e
      · exact n10 e
  have padRun (d : List Bool) :
      run (OutputOpt.outStage layout (.some hc)) (outMeasPad layout (.some hc) d) t =
        run (OutputOpt.outStage layout (.some hc)) d t := by
    unfold outMeasPad
    rw [← run_take, List.take_append_of_le_length (by rw [FlagEntry.pfx_length]),
      List.take_of_length_le (by rw [FlagEntry.pfx_length]), FlagEntry.run_pfx]
  constructor
  · intro d
    rw [padRun]
    obtain ⟨u, hu, ux, upool, uf, ufl, uG⟩ := out_mid hc b R s0 hs t d htx hty htf htg htr
    unfold outNew OutputOpt.outStage
    simp only [← hpk]
    rw [LocalWireModel.run_concat, LocalWireModel.run_concat, LocalWireModel.run_concat,
      LocalWireModel.run_concat, LocalWireModel.run_concat, LocalWireModel.run_concat,
      run_put _ _ _ _ _ pk0, run_put _ _ _ _ _ pk1, ← hu]
    have xbit : ∀ i, i < 256 → u.basis (layout.point.x.getD i 0) =
        (codeX (if b then R + .some hc else R)).testBit i := by
      intro i hi
      rw [← ux]; exact (LocalWireModel.reg_bit layout.point.x u.basis i (by rw [hxl]; exact hi)).symm
    have hx256 : codeX (if b then R + .some hc else R) < 2^256 := by
      rw [← ux, ← hxl]; exact regValue_lt _ _
    have same (q : Wire) (hq : q ≠ pk) : (put u pk v).basis q = u.basis q := by simp [put, writeBit, hq]
    have pkx := (w2 pk (by simp)).1
    have sameX : ∀ q ∈ layout.point.x, (put u pk v).basis q = u.basis q :=
      fun q hq => same q (fun e => pkx (e ▸ hq))
    have ne (q : Wire) (hq : q ∈ [yLow layout, layout.control, layout.point.finite, layout.genericSelect,
        parkWire layout, layout.doubleSelect, layout.core.equalNegY, layout.dialogPool.getD 253 0,
        layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0]) : q ≠ pk :=
      fun e => w5 (e ▸ hq)
    have oxe (K : Nat) := oX_congr (triOf (.some hc)) tv K layout.point.x hxl _ _ sameX
    have hfl' := ufl
    have vx : (v ^^ (dialogOrdinary b R (.some hc) &&
        decide ((triOf (.some hc)).A < codeX (if b then R + .some hc else R)))) = false := by
      rw [hv]
      by_cases hG : dialogOrdinary b R (.some hc) = true
      · have hb := ((dialogOrdinary_true b R _ hC).mp hG).1
        rw [hG, hb]; simp
      · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
        rw [hG']; simp
    have ge : ((put u pk v).basis layout.control ^^ (put u pk v).basis layout.genericSelect ^^
        (put u pk v).basis (parkWire layout) ^^ (put u pk v).basis layout.doubleSelect ^^
        (put u pk v).basis layout.core.equalNegY) = dialogOrdinary b R (.some hc) := by
      rw [same _ (ne _ (by simp)), same _ (ne _ (by simp)), same _ (ne _ (by simp)),
        same _ (ne _ (by simp)), same _ (ne _ (by simp))]
      exact uG.symm
    have pv0 : (put u pk v).basis pk = v := by simp [put, writeBit]
    have knownPre : (put u pk v).basis pk =
        (((put u pk v).basis layout.control ^^ (put u pk v).basis layout.genericSelect ^^
          (put u pk v).basis (parkWire layout) ^^ (put u pk v).basis layout.doubleSelect ^^
          (put u pk v).basis layout.core.equalNegY) &&
          decide ((triOf (.some hc)).A < codeX (if b then R + .some hc else R))) := by
      rw [ge, pv0]
      exact MeasuredFV.xorFalse_eq _ _ vx
    have run1 := fun mm => oclassifierF_run (triOf (.some hc)) tv (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
      (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
      layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
      (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
      (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
      layout.point.finite pk hxn hxl hwl hwn hdisj fx10n fx10x w1 w2 w3 w4 w5 (put u pk v)
      mm
      ⟨fun q hq => by
        have hqp : q ≠ pk := fun e => (w2 pk (by simp)).2.1 (e ▸ hq)
        rw [same q hqp]
        exact upool q (List.mem_of_mem_take hq) (fun e => (fx10x _ (by simp)).2 (e ▸ hq)),
        by rw [same _ (ne _ (by simp))]; exact uf,
        by rw [same _ (ne _ (by simp))]; exact upool _ p253 w10,
        by rw [same _ (ne _ (by simp))]; exact upool _ p254 w11,
        by rw [same _ (ne _ (by simp))]; exact upool _ p255 w12⟩
      (by
        rw [same _ (ne _ (by simp)), same _ (ne _ (by simp)), same _ (ne _ (by simp)),
          same _ (ne _ (by simp)), same _ (ne _ (by simp)), same _ (ne _ (by simp)), oxe, oxe, oxe]
        exact ufl)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · rw [same _ (ne _ (by simp))]; exact upool _ p253 w10
        · rw [same _ (ne _ (by simp))]; exact upool _ p254 w11
        · rw [same _ (ne _ (by simp))]; exact upool _ p255 w12
        · rw [same _ (ne _ (by simp))]; exact uf)
      (by
        rw [same _ (Ne.symm (w2 pk (by simp)).2.2)]
        exact upool _ w7 w9)
      _ hx256
      (fun i hi => by
        rw [sameX _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)]
        exact xbit i hi)
      knownPre
    have upk : u.basis pk = false := upool pk w6 w8
    have clr : ∀ (o : State), o.basis pk = false → put (put o pk v) pk false = o := by
      intro o ho
      apply State.extensionality
      · rfl
      funext q
      by_cases e : q = pk
      · subst e; simp [put, writeBit, ho]
      · simp [put, writeBit, e]
    have run2 : ∀ mm, run (oclassifierF (triOf (.some hc)) (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
        (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
        layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
        (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
        (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
        layout.point.finite pk) mm (put u pk v) =
        run (OutputOpt.oclassifier (triOf (.some hc)) (yBit (.some hc)) (yBit ((.some hc : Point) + .some hc))
          (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
          layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
          (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)) mm u := by
      intro mm
      rw [run1 mm, ge, pv0, vx, run_put _ _ _ _ _ pk2]
      exact clr _ ((run_preserves_outside _ _ u pk pk2).trans upk)
    rw [run2]
    simp only [measurementCount_append, mcC]
    simp only [run_no_measure _ (FiniteFlagInterval.zrep_counts layout).2]
  · intro d
    unfold outMeasPad
    rw [List.drop_append_of_le_length (by rw [FlagEntry.pfx_length]),
      List.drop_of_length_le (by rw [FlagEntry.pfx_length])]
    rfl

end ECDSAAdd.Entrant.OutFlag
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FlagTop2
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out FlagTop FlagExit OutFlag ParityEven ParityUniform

attribute [local irreducible] layout

def finiteN (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  stageNew L C (pkW L) ++ renameProgram (rho L) (genericN L cx cy) ++ outNew L C

def wrapperN (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteN L C cx cy)

theorem pkN_wires (cx cy : Fp) : pkW layout ∈ wires (genericN layout cx cy) := by
  have h : pkW layout ∈ wires (entryXNew layout (pkW layout) (-cx)) := by
    unfold entryXNew
    split_ifs
    · rw [wires_append]
      exact Finset.mem_union_left _ (by simp [swp, wires, Instr.wires])
    · rw [wires_append, wires_append]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simp [swp, wires, Instr.wires]))
  unfold genericN
  simp only [wires_append, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr h))

open Classical in
/-- The value of the parked wrap flag at the end of the generic block. -/
noncomputable def vB {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) : Bool :=
  dialogOrdinary b R (.some hc) &&
    decide ((triOf (.some hc)).A < codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))

open Classical in
theorem blk_values {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (t1 : State) (m2 : regValue layout.point.x t1.basis = codeX R)
    (t1y : regValue layout.point.y t1.basis = pointY R)
    (m3 : t1.basis layout.point.finite = false)
    (m4 : t1.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (hE : t1.basis layout.core.equalNegY = false) (hD : t1.basis layout.doubleSelect = false)
    (hclean : regValue layout.dialogPool t1.basis = 0) (mm : List Bool) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
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
theorem finite_padN {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    ∃ pad, Pad (finiteN layout (.some hc) cx cy) (finiteProgramOpt layout (.some hc) cx cy) s s pad := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hgen : pkW layout ≠ layout.core.generic :=
    pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  have hp := (point_holds _ _ _).mp hs.point
  have gsx := gsel_off
  have pre : ∀ (t1 : State), (∀ q, q ∉ layout.point.x → q ≠ layout.point.finite → q ≠ layout.genericSelect →
      t1.basis q = s.basis q) →
      regValue layout.point.y t1.basis = pointY R ∧ t1.basis layout.core.equalNegY = false ∧
      t1.basis layout.doubleSelect = false ∧ regValue layout.dialogPool t1.basis = 0 := by
    intro t1 m5
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hp.2.2]; apply regValue_congr; intro q hq
      exact m5 q (y_not_x layout layout_nodup q hq)
        (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
    · obtain ⟨a, b', c, d'⟩ := out_off layout.core.equalNegY (by simp)
      rw [m5 _ a c d']; exact hs.flags _ (by simp [flags_list])
    · obtain ⟨a, b', c, d'⟩ := out_off layout.doubleSelect (by simp)
      rw [m5 _ a c d']; exact hs.flags _ (by simp [flags_list])
    · apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
      rw [m5 q (fun h => pool_not_point q hq (List.mem_append_left _ h)) f1 g1]
      exact (regValue_zero _ _).mp hs.clean q hq
  have key : ∀ d, PadP (renameProgram (rho layout) (genericN layout cx cy))
      (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (genBlockOpt layout cx cy))))
      (run (stageNew layout (.some hc) (pkW layout)) d s) (run (stage layout (.some hc)) d s)
      (padG layout cx cy) (pkW layout) (vB hc b R) := by
    intro d
    obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s d hs
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := pk_stage
    rw [stageNew_run layout layout_widths layout_nodup hc b R s d hs (pkW layout) p1 p2 p3 p4 p5 p6 p7 p8]
    generalize ht1 : run (stage layout (.some hc)) d s = t1 at m1 m2 m3 m4 m5 ⊢
    obtain ⟨t1y, hE, hD, hclean⟩ := pre t1 m5
    rw [m4]
    unfold genBlockOpt
    rw [ren_eq]
    have wrap : ∀ (X Y : Fp), X.val = codeX R → Y.val = pointY R →
        (PointDialogValues layout X Y (dialogOrdinary b R (.some hc))
            (pullState (rho layout) t1).basis (pullState (rho layout) t1).basis →
          PadP (genericN layout cx cy) (ParityStageBothInverse23.genericAll layout cx cy)
            (put (pullState (rho layout) t1) (pkW layout)
              (if dialogOrdinary b R (.some hc) then
                decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
            (pullState (rho layout) t1) (padG layout cx cy) (pkW layout) (vB hc b R)) →
        PadP (renameProgram (rho layout) (genericN layout cx cy))
          (renameProgram (rho layout) (ParityStageBothInverse23.genericAll layout cx cy))
          (put t1 (pkW layout) (dialogOrdinary b R (.some hc) &&
            decide ((triOf (.some hc)).A < codeX R))) t1 (padG layout cx cy) (pkW layout) (vB hc b R) := by
      intro X Y hXv hYv h
      have pvv := pulled_values t1 X Y (dialogOrdinary b R (.some hc)) (m2.trans hXv.symm)
        (t1y.trans hYv.symm) m3 m4 hE hD hclean
      rw [flag_eq hc b R X hXv]
      apply PadP.rename (rho layout) rho_injective (pkW layout) rho_pk _ _ (pkN_wires cx cy)
      exact h ⟨pvv.1, pvv.2.1, pvv.2.2.1, pvv.2.2.2, fun _ _ => rfl⟩
    by_cases hG : dialogOrdinary b R (.some hc) = true
    · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
      cases R with
      | zero => exact absurd rfl h0
      | @some x y hr =>
        have den := dialog_denominators_ne_zero hr hc h1 h2 h3
        apply wrap x y rfl rfl
        intro hv
        have ve : vB hc b (.some hr) = decide (cx.val < (genericX x y cx cy).val) := by
          unfold vB
          rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1, Bool.true_and]
          rfl
        rw [ve]
        rw [hG] at hv
        exact generic_padp_true layout layout_widths layout_nodup x y cx cy _ _ hv
          (by rw [hv.generic, hG]) den.1 den.2 hgen
    · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
      have ve : vB hc b R = false := by unfold vB; rw [hG']; rfl
      cases R with
      | zero =>
        apply wrap (FiniteFlagInterval.sentinel : Fp) 0 FiniteFlagInterval.sentinel_val rfl
        intro hv
        rw [ve]
        rw [hG'] at hv
        exact generic_padp_false layout layout_widths layout_nodup _ 0 cx cy _ _ hv
          (by rw [hv.generic, hG']) FiniteFlagInterval.sentinel_ne_zero hgen
      | @some x y hr =>
        apply wrap x y rfl rfl
        intro hv
        rw [ve]
        rw [hG'] at hv
        exact generic_padp_false layout layout_widths layout_nodup x y cx cy _ _ hv
          (by rw [hv.generic, hG']) (curve_x_ne_zero hr) hgen
  have h1 := PadP.prefixMeas _ _ _ _ s s _ _ _ key
  unfold finiteN finiteProgramOpt
  refine ⟨_, Pad.ofP (pad2 := outMeasPad layout (.some hc)) (B' := outNew layout (.some hc)) (B := OutputOpt.outStage layout (.some hc))
    h1 (fun d => ?_)⟩
  rw [run_append]
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s
    (List.take (measurementCount (stage layout (.some hc))) _) hs
  generalize run (stage layout (.some hc)) (List.take (measurementCount (stage layout (.some hc))) _) s = t1
    at m1 m2 m3 m4 m5 ⊢
  obtain ⟨t1y, hE, hD, hclean⟩ := pre t1 m5
  obtain ⟨k1, k2, k3, k4⟩ := blk_values hc b R t1 m2 t1y m3 m4 hE hD hclean
    (List.drop (measurementCount (stage layout (.some hc))) _)
  generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
    (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) _) t1 = t2
    at k1 k2 k3 k4 ⊢
  have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
  have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
    simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
  exact out_pad hc b R s hs t2 k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
    (fun q hx hy hf hg => by
      rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    _ rfl

open Classical in
theorem finite_run_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteN layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteN layout (.some hc) cx cy) m s).basis := by
  obtain ⟨pad, h⟩ := finite_padN hc b R s hs
  rw [h.run_eq m]
  exact finite_run hc b R s (pad m) hs

open Classical in
theorem wrapper_spec_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperN layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run_N hc b R s m hs
  unfold wrapperN
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h

end ECDSAAdd.Entrant.FlagTop2
end

end

section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OutFlag
open Arithmetic Challenge RecordedQuantum MeasuredCodec5 Baselines InputSentinel Secp256k1 ControlledPointLayout
  ZeroFill OutputOpt ParityEven

theorem zeroWith_pre_physical (T : Wire → Program) (E : Program) (hE : GatePhysical E) :
    ∀ (c : Wire) (bs : List ZeroBit), GatePhysical (zeroWith T c bs) →
      GatePhysical (zeroWith (fun h => E ++ T h) c bs) := by
  intro c bs
  induction bs generalizing c with
  | nil =>
    intro h
    simp only [zeroWith, gatePhysical_append] at h ⊢
    exact ⟨hE, h⟩
  | cons b bs ih =>
    intro h
    simp only [zeroWith, gatePhysical_append] at h ⊢
    exact ⟨⟨h.1.1, ih b.work h.1.2⟩, h.2⟩

theorem zeroWith_pre_wires (T : Wire → Program) (E : Program) :
    ∀ (c : Wire) (bs : List ZeroBit),
      wires (zeroWith (fun h => E ++ T h) c bs) ⊆ wires (zeroWith T c bs) ∪ wires E := by
  intro c bs
  induction bs generalizing c with
  | nil =>
    simp only [zeroWith, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    tauto
  | cons b bs ih =>
    simp only [zeroWith, wires_append]
    intro q hq
    have i := @ih b.work q
    simp only [Finset.mem_union] at hq i ⊢
    tauto

theorem Gc_physical (c g O D H W : Wire) (h1 : c ≠ W) (h2 : g ≠ W) (h3 : O ≠ W) (h4 : D ≠ W) (h5 : H ≠ W) :
    GatePhysical (Gc c g O D H W) := by
  simp [Gc, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, h1, h2, h3, h4, h5]

theorem oclassifierF_physical (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) (hlen : xs.length = 256)
    (hU : U ∉ xs ∧ U ∉ work ∧ U ≠ one) (hV : V ∉ xs ∧ V ∉ work ∧ V ≠ one)
    (hF : F ∉ xs ∧ F ∉ work ∧ F ≠ one) (UV : U ≠ V) (VF : V ≠ F) (Fp : F ≠ pk) (gp : W ≠ pk)
    (h1 : c ≠ W) (h2 : g ≠ W) (h3 : O ≠ W) (h4 : D ≠ W) (h5 : H ≠ W)
    (old : GatePhysical (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u)) :
    GatePhysical (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) := by
  have hE := extractOutput_physical tr v xs work one U V F pk W hlen hU hV hF UV VF Fp gp
  have hG := Gc_physical c g O D H W h1 h2 h3 h4 h5
  have hE3 : GatePhysical (Gc c g O D H W ++ (extractOutput tr xs work one U V F pk W ++ Gc c g O D H W)) := by
    simp only [gatePhysical_append]
    exact ⟨hG, hE, hG⟩
  unfold OutputOpt.oclassifier at old
  simp only [gatePhysical_append] at old
  unfold oclassifierF
  simp only [gatePhysical_append]
  exact ⟨old.1, old.2.1, zeroWith_pre_physical _ _ hE3 _ _ old.2.2.1, old.2.2.2⟩

theorem oclassifierF_wires (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) (hlen : xs.length = 256) (Wf : Finset Wire)
    (hc : wires (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ⊆ Wf)
    (hx : ∀ q ∈ xs, q ∈ Wf) (hw : ∀ q ∈ work, q ∈ Wf)
    (h1 : one ∈ Wf) (h2 : U ∈ Wf) (h3 : V ∈ Wf) (h4 : F ∈ Wf) (h5 : pk ∈ Wf) (h6 : W ∈ Wf)
    (m1 : c ∈ Wf) (m2 : g ∈ Wf) (m3 : O ∈ Wf) (m4 : D ∈ Wf) (m5 : H ∈ Wf) :
    wires (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) ⊆ Wf := by
  have E := extractOutput_sub tr v xs work one U V F pk W hlen Wf hx hw h1 h2 h3 h4 h5 h6
  have G : wires (Gc c g O D H W) ⊆ Wf := by
    simp [Gc, wires, Instr.wires, Finset.insert_subset_iff, m1, m2, m3, m4, m5, h6]
  have E3 : wires (Gc c g O D H W ++ (extractOutput tr xs work one U V F pk W ++ Gc c g O D H W)) ⊆ Wf := by
    simp only [wires_append, Finset.union_subset_iff]
    exact ⟨G, E, G⟩
  unfold OutputOpt.oclassifier at hc
  simp only [wires_append, Finset.union_subset_iff] at hc
  unfold oclassifierF
  simp only [wires_append, Finset.union_subset_iff]
  exact ⟨hc.1, hc.2.1, (zeroWith_pre_wires _ _ _ _).trans (Finset.union_subset hc.2.2.1 E3), hc.2.2.2⟩

theorem oclassifierF_slots (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u W one U V F pk : Wire) :
    Challenge.gateSlots (oclassifierF tr yc y2c e xs work y0 c f g O D H t1 t2 u W one U V F pk) ≤
      Challenge.gateSlots (OutputOpt.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) + 1048 := by
  have ec := extractOutput_counts tr v xs work one U V F pk W
  have gs : Challenge.gateSlots (Gc c g O D H W) = 5 := by
    simp [Gc, Challenge.gateSlots, Challenge.instructionSlots]
  have zo := InputSentinel.zeroWith_slots
    (OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
    (Challenge.gateSlots (OutputOpt.otail tr yc y2c e))
    (fun h => OutputOpt.otailL_slots tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  have zc := InputSentinel.zeroWith_slots
    (fun h => (Gc c g O D H W ++ (extractOutput tr xs work one U V F pk W ++ Gc c g O D H W)) ++
      OutputOpt.otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h)
    (5 + (Challenge.gateSlots (extractOutput tr xs work one U V F pk W) + 5) +
      Challenge.gateSlots (OutputOpt.otail tr yc y2c e))
    (fun h => by
      simp only [Challenge.gateSlots_append, gs]
      rw [OutputOpt.otailL_slots])
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  have e3 := ec.2.2
  unfold oclassifierF OutputOpt.oclassifier
  simp only [Challenge.gateSlots_append, zc, zo]
  omega

theorem predec_mem (tr : Tri) (yc : Bool) (i : Nat) (hi : i = 0 ∨ i = 1 ∨ i = 5 ∨ i = 6 ∨ i = 7) :
    i ∈ wires (predecT tr yc) := by
  unfold predecT
  split_ifs <;>
  · generalize tr.B.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.S.testBit tr.r1 = a'; generalize tr.B.testBit tr.r2 = b'
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    cases a <;> cases b <;> cases a' <;> cases b' <;> cases yc <;> decide

theorem predecL_mem (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire) :
    g ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) ∧ c ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) ∧
    O ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) ∧ D ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) ∧
    H ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) := by
  have key : ∀ i, (i = 0 ∨ i = 1 ∨ i = 5 ∨ i = 6 ∨ i = 7) →
      ([g, c, xr1, xr2, y0, O, D, H] : List Wire).getD i 0 ∈ wires (predecL tr yc g c xr1 xr2 y0 O D H) := by
    intro i hi
    unfold predecL
    rw [renameProgram_support]
    refine Finset.mem_image.mpr ⟨i, predec_mem tr yc i hi, ?_⟩
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [LocalWireModel.label]
  exact ⟨key 0 (by simp), key 1 (by simp), key 5 (by simp), key 6 (by simp), key 7 (by simp)⟩

theorem outNew_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (outNew layout (.some hc)) ≤ toffoliCount (OutputOpt.outStage layout (.some hc)) + 2 ∧
    measurementCount (outNew layout (.some hc)) = measurementCount (OutputOpt.outStage layout (.some hc)) + 3 ∧
    Challenge.gateSlots (outNew layout (.some hc)) ≤
      Challenge.gateSlots (OutputOpt.outStage layout (.some hc)) + 1048 := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  have c := oclassifierF_counts (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc : Point) + .some hc)) (exceptionBit (.some hc)) layout.point.x
    (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
    (parkWire layout) layout.doubleSelect layout.core.equalNegY (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
    layout.point.finite (FlagEntry.pkW layout) hwl
  have s := oclassifierF_slots (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc : Point) + .some hc)) (exceptionBit (.some hc)) layout.point.x
    (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
    (parkWire layout) layout.doubleSelect layout.core.equalNegY (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) (wW layout)
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
    layout.point.finite (FlagEntry.pkW layout)
  unfold outNew OutputOpt.outStage
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
  omega

theorem outNew_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (outNew layout (.some hc)) := by
  have old := OutputOpt.outStage_physical hc
  unfold OutputOpt.outStage at old
  simp only [gatePhysical_append] at old
  obtain ⟨⟨⟨A, B⟩, D⟩, E⟩ := old
  obtain ⟨hnd, hmem, -, ⟨c1, c2, c3, c4, c5⟩, -⟩ := out_flag_wires
  obtain ⟨-, hxl, -⟩ := stage_layout layout layout_widths layout_nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true, and_self] at hnd
  obtain ⟨⟨a12, a13, a14, -⟩, ⟨a23, -, -⟩, ⟨a34, -⟩, a45⟩ := hnd
  unfold outNew
  simp only [gatePhysical_append]
  refine ⟨⟨⟨A, B⟩, ?_⟩, E⟩
  exact oclassifierF_physical _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl
    ⟨(hmem _ (by simp)).1, (hmem _ (by simp)).2.1, Ne.symm a12⟩
    ⟨(hmem _ (by simp)).1, (hmem _ (by simp)).2.1, Ne.symm a13⟩
    ⟨(hmem _ (by simp)).1, (hmem _ (by simp)).2.1, Ne.symm a14⟩ a23 a34 a45
    (Ne.symm (hmem _ (by simp)).2.2) c1 c2 c3 c4 c5 D

end ECDSAAdd.Entrant.OutFlag
end

section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FlagTop2
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out FlagTop FlagExit OutFlag ZeroFill ParityEven
  ParityUniform E1Merge NativeFirstDirect MappedCompressed ParityXEntry

attribute [local irreducible] layout

theorem wW_eq (L : ControlledPointLayout) : wW L = E1QubitPlacement.pmapR L (base 721) := by
  unfold E1QubitPlacement.pmapR E1QubitPlacement.pmap
  rw [E1QubitPlacement.rho_base, E1QubitPlacement.sig_base]
  rfl

theorem tailX_721 (k : Nat) : base 721 ∈ wires (tailX base (base 2400) k) := by
  simp only [tailX, prodPart, wires_append, Finset.mem_union]
  simp [wires, Instr.wires]

theorem evenTail_721 (k : Nat) : base 721 ∈ wires (evenTail k) := by
  simp only [evenTail, wires_append, Finset.mem_union]
  simp [wires, Instr.wires]

theorem entryX_W (L : ControlledPointLayout) (k : Fp) : wW L ∈ wires (entryXAll L k) := by
  rw [wW_eq L]
  unfold entryXAll
  rw [renameProgram_support]
  apply Finset.mem_image_of_mem
  unfold mergedAll
  split_ifs with he
  · unfold mergedOdd
    rw [if_pos he, wires_append]
    exact Finset.mem_union_right _ (tailX_721 k.val)
  · unfold mergedEven
    rw [wires_append]
    exact Finset.mem_union_right _ (evenTail_721 k.val)

theorem generic_W (cx cy : Fp) : wW layout ∈ wires (ParityStageBothInverse23.genericAll layout cx cy) := by
  have h := entryX_W layout (-cx)
  simp only [ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll, wires_append,
    Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr h))

theorem W_pool : wW layout ∈ layout.dialogPool :=
  Square5Placement.pool_member layout layout_widths 723 (by omega)

theorem W_ne_pool (i : Nat) (hi : i < 2613) (hne : i ≠ 723) : wW layout ≠ layout.core.poolWire i :=
  fun e => hne (pool_inj layout layout_widths layout_nodup i 723 hi (by omega) e.symm)

theorem W_flag (b : Wire) (hb : b ∈ layout.inPlaceFlags) : wW layout ≠ b :=
  fun e => pool_not_flag _ W_pool (e ▸ hb)

theorem rho_W : rho layout (wW layout) = wW layout := by
  apply rho_fix
  · exact (out_pool_off _ W_pool).1
  · exact W_ne_pool 1400 (by omega) (by omega)
  · exact W_ne_pool 684 (by omega) (by omega)
  · exact W_ne_pool 717 (by omega) (by omega)
  · exact W_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact W_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact W_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact W_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  · exact W_ne_pool 1540 (by omega) (by omega)

theorem genericN_wires (L : ControlledPointLayout) (cx cy : Fp) :
    wires (genericN L cx cy) ⊆ wires (genericNew L cx cy) := by
  simp only [genericN, genericNew, secondStageN, ParityStageBothInverse23.secondStageAll, wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
      (ParityXExitInverse23Kernel.restXXN_sub L _)) (Finset.Subset.refl _))

theorem genericN_counts (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (genericN L cx cy) + 254 = toffoliCount (genericNew L cx cy) ∧
    measurementCount (genericN L cx cy) ≤ measurementCount (genericNew L cx cy) ∧
    Challenge.gateSlots (genericN L cx cy) ≤ Challenge.gateSlots (genericNew L cx cy) + 2 := by
  have r := ParityXExitInverse23Kernel.restXXN_counts L cx.val
  simp only [genericN, genericNew, secondStageN, ParityStageBothInverse23.secondStageAll,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
  omega

theorem genericN_physical (cx cy : Fp) : GatePhysical (genericN layout cx cy) := by
  have old : GatePhysical (ParityStageBothInverse23.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0 := ParityStageBothInverse23.generic_physical layout layout_widths layout_nodup cx cy old
  simp only [ParityStageBothInverse23.genericAll, ParityStageBothInverse23.entryStageAll,
    ParityStageBothInverse23.secondStageAll, gatePhysical_append] at p0
  simp only [genericN, secondStageN, gatePhysical_append]
  exact ⟨⟨⟨p0.1.1.1, entryXNew_physical layout layout_widths layout_nodup _ _
      (pk_ne_flag layout layout_widths layout_nodup)⟩, p0.1.2⟩,
    ⟨p0.2.1.1, ParityXExitInverse23Kernel.restXXN_physical layout layout_widths layout_nodup _⟩, p0.2.2⟩

theorem outNew_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (outNew layout (.some hc)) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
  have mem := stage_wires_mem hc
  have hstage : wires (stage layout (.some hc)) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inl (Or.inl hq))
  have hOut : wires (OutputOpt.outStage layout (.some hc)) ⊆
      ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    intro q hq
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    exact Or.inr (Or.inr hq)
  have pkIn : pkW layout ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    refine Or.inr (Or.inl (Or.inr ?_))
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_, genericNew_wires layout cx cy (pk_wires cx cy), rho_pk⟩
  have wIn : wW layout ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
    rw [finiteOpt_wires hc]
    simp only [Finset.mem_union]
    refine Or.inr (Or.inl (Or.inr ?_))
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_, generic_W cx cy, rho_W⟩
  have mx : ∀ q ∈ layout.point.x, q ∈ ioSet := by
    intro q hq
    simp [ioSet, PointAddLayout.pointWires, hq]
  have mf : layout.point.finite ∈ ioSet := by simp [ioSet, PointAddLayout.pointWires]
  have tk : ∀ q ∈ layout.dialogPool.take 253, q ∈ layout.dialogPool.take 256 := by
    intro q hq
    have hpl := dialogPool_length layout layout_widths
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    rw [← e]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  have pool256 : ∀ q ∈ layout.dialogPool.take 256,
      q ∈ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) :=
    fun q hq => hstage (mem.1 q hq)
  have hO := hOut
  unfold OutputOpt.outStage at hO
  simp only [wires_append, Finset.union_subset_iff] at hO
  obtain ⟨⟨⟨hA, hB⟩, hD⟩, hE⟩ := hO
  obtain ⟨n1, n2, n3, n4, n5⟩ := predecL_mem (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect
    layout.control (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0)
    (yLow layout) (parkWire layout) layout.doubleSelect layout.core.equalNegY
  unfold outNew
  simp only [wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨hA, hB⟩, ?_⟩, hE⟩
  exact oclassifierF_wires _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    layout_widths.inputX _ hD
    (fun q hq => Finset.mem_union_left _ (mx q hq)) (fun q hq => pool256 q (tk q hq))
    (pool256 _ (pool_take_mem 253 (by omega))) (pool256 _ (pool_take_mem 254 (by omega)))
    (pool256 _ (pool_take_mem 255 (by omega))) (Finset.mem_union_left _ mf) pkIn wIn
    (hA n2) (hA n1) (hA n3) (hA n4) (hA n5)

theorem finiteN_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteN layout (.some hc) cx cy) ⊆ ioSet ∪ wires (finiteProgramOpt layout (.some hc) cx cy) := by
  have s := stageNew_wires (cx := cx) (cy := cy) hc
  have o := outNew_wires (cx := cx) (cy := cy) hc
  unfold finiteN
  rw [wires_append, wires_append]
  refine Finset.union_subset (Finset.union_subset s ?_) o
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  rw [finiteOpt_wires hc]
  simp only [Finset.mem_union]
  refine Or.inr (Or.inl (Or.inr ?_))
  rw [renameProgram_support]
  exact Finset.mem_image_of_mem _ (genericNew_wires layout cx cy (genericN_wires layout cx cy ha))

theorem wrapperN_wires {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperN layout (.some hc) cx cy) ⊆ ioSet ∪ wires (wrapperOpt layout (.some hc) cx cy) := by
  have k := finiteN_wires (cx := cx) (cy := cy) hc
  have hw := layout_widths
  have fixIO : ∀ q ∈ ioSet, Wrapper5.U layout q = q := by
    intro q hq
    have hq' := List.mem_toFinset.mp hq
    have np := io_not_pool q hq'
    have n1 : q ≠ layout.core.poolWire 684 := by
      intro e; apply np; rw [e]; exact Square5Placement.pool_member layout hw 684 (by omega)
    have n2 : q ≠ layout.core.poolWire 717 := by
      intro e; apply np; rw [e]; exact Square5Placement.pool_member layout hw 717 (by omega)
    rw [U_apply, if_neg n1, if_neg n2]
  unfold wrapperN wrapperOpt
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (k ha) with h | h
  · rw [fixIO a h]; exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

theorem support_used_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperN layout (.some hc) cx cy) ⊆ layout.dialogUsedWires.toFinset := by
  refine (wrapperN_wires hc).trans (Finset.union_subset ?_ (support_used hc))
  intro q hq
  apply List.mem_toFinset.mpr
  unfold ControlledPointLayout.dialogUsedWires
  simp only [List.mem_append]
  have := List.mem_toFinset.mp hq
  simp only [List.mem_append] at this
  tauto

theorem wrapper_physical_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperN layout (.some hc) cx cy) := by
  unfold wrapperN
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteN, gatePhysical_append]
  exact ⟨⟨stageNew_physical hc, gatePhysical_rename _ rho_injective _ (genericN_physical cx cy)⟩,
    outNew_physical hc⟩

theorem wrapperN_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperN layout (.some hc) cx cy) + 504 ≤
      toffoliCount (wrapperOpt layout (.some hc) cx cy) ∧
    measurementCount (wrapperN layout (.some hc) cx cy) ≤
      measurementCount (wrapperOpt layout (.some hc) cx cy) + 5 ∧
    Challenge.gateSlots (wrapperN layout (.some hc) cx cy) ≤
      Challenge.gateSlots (wrapperOpt layout (.some hc) cx cy) + 5708 := by
  have gN := genericN_counts layout cx cy
  have g := genericNew_counts layout cx cy
  have s := stageNew_counts hc (pkW layout)
  have o := stage_counts hc
  have u := outNew_counts hc
  simp only [wrapperN, wrapperOpt, finiteN, finiteProgramOpt, genBlockOpt,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append,
    (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, rename_gateSlots]
  omega

open Classical in
theorem full_spec_N {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperN layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec_N hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used_N hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programB (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperN layout C cx cy

def entryB : Challenge.Entry := fun C=>normalizeProgram (programB C)
def boundsB : Challenge.Bounds := ⟨2149749,1498375,1587,50256956⟩

theorem program_correct_B (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programB C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programB,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec_N hc b R) (support_used_N hc)

theorem program_toffoli_B (C : Point) : toffoliCount (programB C)≤2149749 := by
  cases C with
  | zero=>simp [programB,toffoliCount]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_toffoli (.some hc)
    have delta:=(wrapperN_metrics hc).1
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤_ at old
    change toffoliCount (wrapperN layout (.some hc) cx cy)≤2149749
    omega

theorem program_measurements_B (C : Point) : measurementCount (programB C)≤1498375 := by
  cases C with
  | zero=>simp [programB,measurementCount]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_measurements (.some hc)
    have delta:=(wrapperN_metrics hc).2.1
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperN layout (.some hc) cx cy)≤1498375
    omega

theorem program_qubits_B (C : Point) : qubits (programB C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_qubits (.some hc)
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperN layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact Finset.mem_union_left _ h
    · rcases Finset.mem_union.mp (wrapperN_wires hc h) with e | e
      · exact Finset.mem_union_left _ (io_mem q (List.mem_toFinset.mp e))
      · exact Finset.mem_union_right _ e

theorem program_physical_B (C : Point) : GatePhysical (programB C) := by
  cases C with
  | zero=>simp [programB,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical_N hc

theorem program_slots_B (C : Point) : Challenge.gateSlots (programB C)≤50256956 := by
  cases C with
  | zero=>simp [programB]
  | @some cx cy hc=>
    have old:=ParityFinalBothInverse23Out.program_slots (.some hc)
    have delta:=(wrapperN_metrics hc).2.2
    change Challenge.gateSlots (wrapperOpt layout (.some hc) cx cy)≤50251248 at old
    change Challenge.gateSlots (wrapperN layout (.some hc) cx cy)≤50256956
    omega

theorem certificateB : Challenge.Certificate entryB boundsB where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct_B C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical_B C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli_B C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programB C))≤1498375
    rw [normalize_measurements];exact program_measurements_B C
  qubits_le C:=by
    change qubits (normalizeProgram (programB C))≤1587
    rw [normalize_qubits];exact program_qubits_B C
  gateSlots_le C:=by
    change Challenge.gateSlots (normalizeProgram (programB C))≤50256956
    rw [normalize_slots];exact program_slots_B C

end ECDSAAdd.Entrant.FlagTop2
end

end

namespace ECDSAAdd.Entrant
def program := FlagTop2.programB
def entry := FlagTop2.entryB
def bounds := FlagTop2.boundsB
theorem certificate : Challenge.Certificate entry bounds := FlagTop2.certificateB
end ECDSAAdd.Entrant
