import ECDSAAdd.Submission.Entrant.ParityKernel
import ECDSAAdd.Submission.Entrant.E1Merge

set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

namespace ECDSAAdd.Entrant.E1Generic
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk

/-! ### Placement of the merged first tick -/

/-- The three integer-host relabelings that the stage kernels apply to their first phase. -/
def sig (q : Wire) : Wire := Q7IntegerHost.swap (Q6IntegerHost.swap (Q5Global718.swap q))
def pmap (L : ControlledPointLayout) (q : Wire) : Wire := wireFn2 L (sig q)

def sw (i : Nat) : Nat :=
  if i=1026 then 718 else if i=718 then 1026 else if i=1541 then 719 else if i=719 then 1541
  else if i=1542 then 720 else if i=720 then 1542 else i

theorem sig_base (i : Nat) : sig (base i)=base (sw i) := by
  unfold sig sw
  simp only [Q7IntegerHost.swap,Q6IntegerHost.swap,Q5Global718.swap,Equiv.swap_apply_def,base]
  by_cases h1 : i=1026 <;> by_cases h2 : i=718 <;> by_cases h3 : i=1541 <;> by_cases h4 : i=719 <;>
    by_cases h5 : i=1542 <;> by_cases h6 : i=720 <;> simp_all <;> omega

theorem sig_injective : Function.Injective sig := by
  intro a b h
  unfold sig at h
  exact Q5Global718.swap.injective (Q6IntegerHost.swap.injective (Q7IntegerHost.swap.injective h))

/-- The label set of the merged circuit. -/
def S : Finset Wire := (E1Merge.mSites base (base 2400)).toFinset

theorem S_cases (q : Wire) (hq : q∈S) : ∃ i, q=base i ∧
    (i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) := by
  simp only [S,E1Merge.mSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false] at hq
  rcases hq with ((h|h)|h)|h|h|h
  all_goals first
    | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
       simp only [List.mem_range'_1] at hi
       exact ⟨i,rfl,by omega⟩)
    | exact ⟨_,h,by omega⟩

theorem sw_slot (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 723 ∨ i = 2400) :
    base (sw i)∈slots.toFinset := by
  apply slot_mem
  · unfold live sw; split_ifs <;> omega
  · unfold CompressedAllocation.omitted sw; split_ifs <;> omega

theorem sw_logical (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 723 ∨ i = 2400) :
    base (sw i)∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨sw i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  unfold sw; split_ifs <;> omega

/-! The 1591-qubit kernels host the first tick's work label 1797 on label 511
(`FrontierEntry1591Native.forward`). The merged circuit additionally uses label 511 as its
last comparison carry, which is moved to the clean pool label 723. -/
def rho (q : Wire) : Wire := Equiv.swap (base 1797) (base 511) (Equiv.swap (base 511) (base 723) q)
def rhoN (i : Nat) : Nat := if i=1797 then 511 else if i=511 then 723 else if i=723 then 1797 else i

theorem rho_base (i : Nat) : rho (base i)=base (rhoN i) := by
  unfold rho rhoN
  simp only [Equiv.swap_apply_def,base]
  by_cases h1 : i=1797 <;> by_cases h2 : i=511 <;> by_cases h3 : i=723 <;> simp_all <;> omega

theorem rho_injective : Function.Injective rho := by
  intro a b h
  unfold rho at h
  exact (Equiv.swap (base 511) (base 723)).injective ((Equiv.swap (base 1797) (base 511)).injective h)

theorem rhoN_range (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) :
    rhoN i < 515 ∨ (770 ≤ rhoN i ∧ rhoN i < 1285) ∨ (1540 ≤ rhoN i ∧ rhoN i < 1798) ∨ rhoN i = 721 ∨
      rhoN i = 722 ∨ rhoN i = 723 ∨ rhoN i = 2400 := by
  unfold rhoN; split_ifs <;> omega

/-- Placement of the merged circuit: transport, then the three integer-host relabelings. -/
def pmapR (L : ControlledPointLayout) (q : Wire) : Wire := pmap L (rho q)

section Place
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pmap_inj : ∀a∈S,∀b∈S,pmapR L a=pmapR L b → a=b := by
  intro a ha b hb e
  obtain ⟨i,rfl,hi⟩ := S_cases a ha
  obtain ⟨j,rfl,hj⟩ := S_cases b hb
  have pl := placement2 L hw hn
  unfold pmapR pmap at e
  rw [rho_base,rho_base,sig_base,sig_base] at e
  have := pl.injectiveOnSlots _ (sw_slot _ (rhoN_range i hi)) _ (sw_slot _ (rhoN_range j hj)) e
  rw [←sig_base,←sig_base] at this
  have := sig_injective this
  rw [←rho_base,←rho_base] at this
  exact rho_injective this

theorem pmap_x : (wireBlock base 770 256).map (pmapR L)=L.point.x := by
  have pl := placement2 L hw hn
  rw [←pl.divisorMap]
  apply List.map_congr_left
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  unfold pmapR pmap; rw [rho_base,sig_base]
  congr 2; unfold sw rhoN; split_ifs <;> omega

theorem pmap_g : pmapR L (base 2400)=L.core.generic := by
  have pl := placement2 L hw hn
  unfold pmapR pmap; rw [rho_base,sig_base]
  have : sw (rhoN 2400)=2400 := by unfold sw rhoN; simp
  rw [this]; exact pl.controlMap

theorem pmap_pool (q : Wire) (hq : q∈S) (hx : q∉wireBlock base 770 256) (hg : q≠base 2400) :
    pmapR L q∈L.dialogPool := by
  obtain ⟨i,rfl,hi⟩ := S_cases q hq
  have pl := placement2 L hw hn
  unfold pmapR pmap; rw [rho_base,sig_base]
  have hx' : ¬(770 ≤ i ∧ i < 1026) := by
    intro h; apply hx; exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have hg' : i≠2400 := fun e => hg (by rw [e])
  apply pl.sharedWork
  · simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨sw (rhoN i),by unfold sw rhoN; split_ifs <;> omega,rfl⟩
  · exact sw_slot _ (rhoN_range i hi)
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    unfold sw rhoN at this; split_ifs at this <;> omega
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    unfold sw rhoN at this; split_ifs at this <;> omega

end Place


def tickF (L : ControlledPointLayout) : Program := renameProgram (pmapR L) (NativeFirstDirect.forward base)
def entryM (L : ControlledPointLayout) (k : Fp) : Program :=
  renameProgram (pmapR L) (E1Merge.merged base (base 2400) k.val)

theorem regValue_pull (f : Wire → Wire) (r : List Wire) (s : BasisState) :
    regValue r (fun q => s (f q))=regValue (r.map f) s := by
  induction r with
  | nil => rfl
  | cons a rs ih =>
    change (if s (f a) then 1 else 0)+2*regValue rs (fun q => s (f q))=
      (if s (f a) then 1 else 0)+2*regValue (rs.map f) s
    rw [ih]

theorem g2400 : base 2400∉skywalkPoolWires base := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hi
  have := base_injective e; omega

theorem merged_S (k : Nat) : wires (E1Merge.merged base (base 2400) k)⊆S :=
  E1Merge.merged_support base (base 2400) k

theorem prefix_S : (NativeFirstDirect.prefixSites base).toFinset⊆S := by
  intro q h
  rw [List.mem_toFinset] at h
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at h
  simp only [S,List.mem_toFinset]
  rcases h with ((h|h)|h)|h|h
  · exact E1Merge.blk_mSites base (base 2400) 0 257 (by omega) q h
  · exact E1Merge.blk_mSites base (base 2400) 770 258 (by omega) q h
  · exact E1Merge.blk_mSites base (base 2400) 1540 256 (by omega) q h
  · rw [h]; exact E1Merge.in_mSites base (base 2400) 1028 (by omega)
  · rw [h]; exact E1Merge.in_mSites base (base 2400) 1797 (by omega)

theorem forward_S : wires (NativeFirstDirect.forward base)⊆S :=
  Finset.Subset.trans (NativeFirstDirect.prefix_support base).1 prefix_S

section Entry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

/-- Physical form: the merged entry equals the compare-first constant addition followed by the
renamed direct first tick, on every pair of measurement records. -/
theorem entry_eq (k : Fp) (s : State) (X : Nat) (hX : X<p) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hg : s.basis L.core.generic=G)
    (hc : regValue L.dialogPool s.basis=0) (m1 m2 : List Bool) :
    run (entryM L k) m1 s=run (fastConstAdd L L.point.x k++tickF L) m2 s := by
  have inj := pmap_inj L hw hn
  have pool := pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := pmapR L
  let t : State := pullState F s
  have clean (q : Wire) (hq : q∈S) (h1 : q∉wireBlock base 770 256) (h2 : q≠base 2400) :
      t.basis q=false := hzero _ (pool q hq h1 h2)
  have inS (i : Nat) (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      base i∈S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i hi)
  have notx (i : Nat) (hi : ¬ (770 ≤ i ∧ i < 1026)) : base i∉wireBlock base 770 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have ne2400 (i : Nat) (hi : i≠2400) : base i≠base 2400 := fun e => hi (base_injective e)
  have cl (i : Nat) (hi : i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      t.basis (base i)=false :=
    clean _ (inS i (by omega)) (notx i (by omega)) (ne2400 i (by omega))
  have blkz (a n : Nat) (h : a + n ≤ 515 ∨ (1026 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
      regValue (wireBlock base a n) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (by omega)
  have xval : regValue (wireBlock base 770 256) t.basis=X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (F q))=X
    rw [regValue_pull,pmap_x L hw hn,hx]
  have tk0 : regValue (E1Merge.kR base) t.basis=X := by
    rw [E1Merge.kR_x base base_pool_nodup,show E1Merge.xR base=wireBlock base 770 256 from rfl,xval,
      blkz 1026 2 (by omega)]
    simp
  have tg : t.basis (base 2400)=G := by
    change s.basis (pmapR L (base 2400))=G
    rw [pmap_g L hw hn,hg]
  -- old side
  have fca := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s
    (m2.take (measurementCount (fastConstAdd L L.point.x k))) hg hx hc
  generalize hs1 : run (fastConstAdd L L.point.x k) (m2.take (measurementCount (fastConstAdd L L.point.x k))) s=s1 at fca
  obtain ⟨p1,x1,o1⟩ := fca
  let u : State := ⟨t.phase,fun q => if q∈E1Merge.kR base then s1.basis (F q) else t.basis q⟩
  have hu2 : ∀q,q∉E1Merge.kR base → u.basis q=t.basis q := by
    intro q hq; simp [u,hq]
  have xS : ∀q∈L.point.x,∃a∈S,F a=q ∧ a∈wireBlock base 770 256 := by
    intro q hq
    rw [←pmap_x L hw hn] at hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    refine ⟨a,?_,rfl,ha⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact inS i (by omega)
  have hu3 : regValue (E1Merge.kR base) u.basis=(X+(if t.basis (base 2400) then k.val else 0))%p := by
    rw [tg,E1Merge.kR_x base base_pool_nodup]
    have e1 : regValue (E1Merge.xR base) u.basis=regValue L.point.x s1.basis := by
      rw [←pmap_x L hw hn,←regValue_pull]
      apply regValue_congr
      intro q hq
      have : q∈E1Merge.kR base := E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) q hq
      simp only [u,this,if_true]
      rfl
    have e2 : regValue (wireBlock base 1026 2) u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      have kq : base i∈E1Merge.kR base := E1Merge.blk_sub base 1026 2 770 258 (by omega) (by omega) _ hq
      have outx : F (base i)∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha (base i) (inS i (by omega)) ea
        subst this
        exact notx i (by omega) ax
      simp only [u,kq,if_true]
      rw [o1 _ outx]
      exact cl i (by omega)
    rw [e1,e2,x1]; simp
  have t1 := (regValue_zero _ _).mp (blkz 0 258 (by omega))
  have eqL := E1Merge.merged_eq_forward base (base 2400) base_pool_nodup g2400 k.val k.isLt X hX t u m1
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) tk0 (blkz 0 258 (by omega))
    (blkz 1029 256 (by omega)) (cl 1028 (by omega)) (cl 514 (by omega)) (cl 721 (by omega)) (cl 722 (by omega))
    (fun i h1 h2 => cl i (by omega)) (cl 513 (by omega))
    (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact cl i (by omega)) (cl 1797 (by omega)) rfl hu2 hu3
  -- transport both sides
  have hS : ∀q∈S,t.basis q=s.basis (F q) := fun q _ => rfl
  have newSide := run_rename_pool F S inj _ (merged_S k.val) m1 t s rfl hS
  have uS : ∀q∈S,u.basis q=s1.basis (F q) := by
    intro q hq
    by_cases kq : q∈E1Merge.kR base
    · simp [u,kq]
    · simp only [u,kq,if_false]
      change s.basis (F q)=s1.basis (F q)
      have outx : F q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha q hq ea
        subst this
        exact kq (E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) _ ax)
      rw [o1 _ outx]
  have oldSide := run_rename_pool F S inj _ forward_S
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) u s1 (by simp [u,t,pullState,p1]) uS
  have rhs : run (fastConstAdd L L.point.x k++tickF L) m2 s=
      run (tickF L) (m2.drop (measurementCount (fastConstAdd L L.point.x k))) s1 := by
    rw [run_append,hs1]
  rw [rhs]
  apply State.extensionality
  · rw [entryM,newSide.1,eqL,tickF,oldSide.1]
  · funext q
    by_cases im : q∈S.image F
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp im
      rw [entryM,newSide.2 a ha,eqL,tickF,oldSide.2 a ha]
    · rw [entryM,run_rename_pool_outside F S _ (merged_S k.val) m1 s q im,tickF,
        run_rename_pool_outside F S _ forward_S _ s1 q im]
      have outx : q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,_⟩ := xS _ hm
        exact im (Finset.mem_image.mpr ⟨a,ha,ea⟩)
      rw [o1 q outx]

end Entry


/-! ### Splitting the stage kernels at the first tick -/

theorem rp_append (f : Wire → Wire) (a b : Program) :
    renameProgram f (a++b)=renameProgram f a++renameProgram f b := List.map_append

def entryRest (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L) (FrontierEntry1591Native.hosted (NewStackOB5.stackForwardT++skywalkArithmeticClear base)++
    (FrontierEntry1591Field.entry++FrontierEntry1591Native.hosted FrontierEntry1591Kernel.lastPhase))

def exitRest (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L) (FrontierEntry1591Native.hosted (NewStackOB5.stackForwardT++skywalkArithmeticClear base)++
    (FrontierEntry1591Field.exit++FrontierEntry1591Native.hosted FrontierEntry1591Kernel.lastPhase))

/-- Congruence of renamings through a support bound (keeps concrete programs opaque). -/
theorem congr_sub (f g : Wire → Wire) (P : Program) (T : Finset Wire) (hP : wires P ⊆ T)
    (h : ∀ q ∈ T, f q = g q) : renameProgram f P = renameProgram g P :=
  renameProgram_congr_support f g P (fun q hq => h q (hP hq))

/-- On the support of the direct tick the work-wire transport of the 1591-qubit kernels agrees
with `rho`. -/
theorem forward_rho : FrontierEntry1591Native.forward base=renameProgram rho (NativeFirstDirect.forward base) := by
  unfold FrontierEntry1591Native.forward FrontierEntry1591Native.Transport.program
  apply congr_sub _ _ _ _ (NativeFirstDirect.prefix_support base).1
  intro q h
  rw [List.mem_toFinset] at h
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at h
  have e : ∃ i, q=base i ∧ (i < 257 ∨ (770 ≤ i ∧ i < 1028) ∨ (1540 ≤ i ∧ i < 1796) ∨ i = 1028 ∨ i = 1797) := by
    rcases h with ((h|h)|h)|h|h
    all_goals first
      | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
         simp only [List.mem_range'_1] at hi
         exact ⟨i,rfl,by omega⟩)
      | exact ⟨_,h,by omega⟩
  obtain ⟨i,rfl,hi⟩ := e
  have b1 : base i≠base 511 := fun h => by have := base_injective h; omega
  have b2 : base i≠base 723 := fun h => by have := base_injective h; omega
  unfold rho
  rw [Equiv.swap_apply_of_ne_of_ne b1 b2]

/-- The kernels' hosted first tick is exactly `tickF`. -/
theorem tick_eq (L : ControlledPointLayout) :
    renameProgram (wireFn2 L) (FrontierEntry1591Native.hosted (FrontierEntry1591Native.forward base))=tickF L := by
  rw [forward_rho,FrontierEntry1591Native.hosted,tickF]
  simp only [renameProgram_comp]
  rfl

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry FrontierEntry1591Kernel.entryKernel L=tickF L++entryRest L := by
  rw [← tick_eq]
  simp only [FrontierEntry1591Callers.entry,FrontierEntry1591Kernel.entryKernel,FrontierEntry1591Native.relocated,
    FrontierEntry1591Kernel.firstPhase,FrontierEntry1591Native.hosted_append,entryRest,rp_append,List.append_assoc]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit FrontierEntry1591Kernel.exitKernel L=tickF L++exitRest L := by
  rw [← tick_eq]
  simp only [FrontierEntry1591Callers.exit,FrontierEntry1591Kernel.exitKernel,FrontierEntry1591Native.relocated,
    FrontierEntry1591Kernel.firstPhase,FrontierEntry1591Native.hosted_append,exitRest,rp_append,List.append_assoc]

/-- Replace a prefix whose final state agrees with an old prefix on every record. -/
theorem tri_transfer {P Q : BasisState → Prop} {A B R : Program}
    (h : ∀s : State,P s.basis → ∀ m1 m2 : List Bool,run A m1 s=run B m2 s)
    (t : Triple P (B++R) Q) : Triple P (A++R) Q := by
  intro s m hs
  have := t s (List.replicate (measurementCount B) false++m.drop (measurementCount A)) hs
  rw [run_append] at this ⊢
  have e1 : (List.replicate (measurementCount B) false++m.drop (measurementCount A)).take
      (measurementCount B)=List.replicate (measurementCount B) false := by simp
  have e2 : (List.replicate (measurementCount B) false++m.drop (measurementCount A)).drop
      (measurementCount B)=m.drop (measurementCount A) := by simp
  rw [e1,e2] at this
  rw [h s hs (m.take (measurementCount A)) (List.replicate (measurementCount B) false)]
  exact this

section Entry1
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem lay (q : Wire) :
    (q∈L.point.x → q∉L.point.y) ∧ (q∈L.dialogPool → q∉L.point.x ∧ q∉L.point.y) ∧
    (q=L.core.generic → q∉L.point.x ∧ q∉L.point.y) := by
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  refine ⟨fun hx hy => ?_,fun hp => ⟨fun hx => ?_,fun hy => ?_⟩,fun hg => ⟨fun hx => ?_,fun hy => ?_⟩⟩
  all_goals
    first
    | (have h1 := List.count_pos_iff.mpr hx; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (have h1 := List.count_pos_iff.mpr hp; have h2 := List.count_pos_iff.mpr hx
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (have h1 := List.count_pos_iff.mpr hp; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (subst hg; have h2 := List.count_pos_iff.mpr hx
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
       omega)
    | (subst hg; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
       omega)


/-- The y-side fused offset commutes with the x-side constant addition, so the merged x entry
can run after it. -/
theorem entry1_eq (k ky : Fp) (s : State) (X : Nat) (hX : X<p) (Y : Fp) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (hg : s.basis L.core.generic=G) (hc : regValue L.dialogPool s.basis=0) (m1 m2 : List Bool) :
    run (EntryFuse.fusedY L ky++entryM L k) m1 s=
      run (fastConstAdd L L.point.x k++EntryFuse.fusedY L ky++tickF L) m2 s := by
  have xy (q : Wire) (h : q∈L.point.x) : q∉L.point.y := (lay L hw hn q).1 h
  have px (q : Wire) (h : q∈L.dialogPool) : q∉L.point.x := ((lay L hw hn q).2.1 h).1
  have py (q : Wire) (h : q∈L.dialogPool) : q∉L.point.y := ((lay L hw hn q).2.1 h).2
  have gx : L.core.generic∉L.point.x := ((lay L hw hn _).2.2 rfl).1
  have gy : L.core.generic∉L.point.y := ((lay L hw hn _).2.2 rfl).2
  -- left: fusedY then merged entry
  have fy := EntryFuse.fusedY_correct L hw hn Y ky s (m1.take (measurementCount (EntryFuse.fusedY L ky))) hy hc
  generalize hsy : run (EntryFuse.fusedY L ky) (m1.take (measurementCount (EntryFuse.fusedY L ky))) s=sy at fy
  obtain ⟨py1,py2,py3⟩ := fy
  have syx : regValue L.point.x sy.basis=X := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (xy q hq)),hx]
  have syg : sy.basis L.core.generic=G := (py3 _ gy).trans hg
  have syc : regValue L.dialogPool sy.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (py q hq)),hc]
  -- commutation of the two constant steps
  have comm (r0 r1 r2 : List Bool) : run (fastConstAdd L L.point.x k) r0 sy=
      run (EntryFuse.fusedY L ky) r2 (run (fastConstAdd L L.point.x k) r1 s) := by
    have fa := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX sy r0 syg syx syc
    have fc := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s r1 hg hx hc
    generalize ha : run (fastConstAdd L L.point.x k) r0 sy=a at fa
    generalize hcc : run (fastConstAdd L L.point.x k) r1 s=c at fc
    obtain ⟨a1,a2,a3⟩ := fa
    obtain ⟨c1,c2,c3⟩ := fc
    have cy : regValue L.point.y c.basis=Y.val := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (fun h => xy q h hq)),hy]
    have cc : regValue L.dialogPool c.basis=0 := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (px q hq)),hc]
    have fb := EntryFuse.fusedY_correct L hw hn Y ky c r2 cy cc
    generalize hb : run (EntryFuse.fusedY L ky) r2 c=b at fb
    obtain ⟨b1,b2,b3⟩ := fb
    have cg : c.basis L.core.generic=s.basis L.core.generic := c3 _ gx
    apply State.extensionality
    · rw [a1,b1,c1,py1]
    · funext q
      by_cases qx : q∈L.point.x
      · have e : regValue L.point.x a.basis=regValue L.point.x b.basis := by
          rw [a2,regValue_congr _ _ c.basis (fun q hq => b3 q (xy q hq)),c2]
        exact (regValue_eq_iff _ _ _).mp e q qx
      by_cases qy : q∈L.point.y
      · have e : regValue L.point.y a.basis=regValue L.point.y b.basis := by
          rw [regValue_congr _ _ sy.basis (fun q hq => a3 q (fun h => xy q h hq)),py2,b2,cg]
        exact (regValue_eq_iff _ _ _).mp e q qy
      rw [a3 q qx,b3 q qy,c3 q qx,py3 q qy]
  -- assemble
  let nA := measurementCount (fastConstAdd L L.point.x k)
  let nY := measurementCount (EntryFuse.fusedY L ky)
  let M := List.replicate nA false++m2.drop (nA+nY)
  have lhs : run (EntryFuse.fusedY L ky++entryM L k) m1 s=
      run (tickF L) (m2.drop (nA+nY)) (run (fastConstAdd L L.point.x k) (List.replicate nA false) sy) := by
    rw [run_append,hsy,entry_eq L hw hn k sy X hX G syx syg syc _ M,run_append]
    have t1 : M.take nA=List.replicate nA false := List.take_left' (by simp)
    have t2 : M.drop nA=m2.drop (nA+nY) := List.drop_left' (by simp)
    rw [t1,t2]
  have rhs : run (fastConstAdd L L.point.x k++EntryFuse.fusedY L ky++tickF L) m2 s=
      run (tickF L) (m2.drop (nA+nY)) (run (EntryFuse.fusedY L ky) ((m2.take (nA+nY)).drop nA)
        (run (fastConstAdd L L.point.x k) ((m2.take (nA+nY)).take nA) s)) := by
    rw [run_append,run_append,measurementCount_append]
  rw [lhs,rhs,comm]

end Entry1


/-! ### The generic body with both constant additions absorbed into the first ticks -/

section Generic
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  EntryFuse.fusedY L (-cy)++entryM L (-cx)++entryRest L++PrefixFrontierSquare1591.program L++
  entryM L (3*cx-(OwnDiagAll12Square.sqOff : Nat))++exitRest L++exitY L cy++fastConstNeg L cx

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
  (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
  (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
    (mixedTranscriptTape base))
include hw hn logicalND hlo logicalAway logicalReplay
attribute [local irreducible] run fastConstAdd fastConstNeg exitY

theorem prefix1 (X Y cx cy : Fp) (G : Bool) (origin : BasisState) (hX : X+(if G then -cx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin)
      (EntryFuse.fusedY L (-cy)++entryM L (-cx)++entryRest L)
      (PointDialogValues L (X+(if G then -cx else 0))
        ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) G origin) := by
  have h1 := fastStep_addX L hw hn X Y G origin (-cx)
  have h2 := FrontierEntry1591Callers.division_step FrontierEntry1591Kernel.entryKernel
    FrontierEntry1591Kernel.entry_support FrontierEntry1591Kernel.entry_correct L hw hn logicalND hlo
    logicalAway logicalReplay (X+(if G then -cx else 0)) Y (-cy) G origin hX
  have h12 := h1.seq h2
  rw [FrontierEntry1591Callers.division,entry_split,
    show fastConstAdd L L.point.x (-cx)++(EntryFuse.fusedY L (-cy)++(tickF L++entryRest L))=
      (fastConstAdd L L.point.x (-cx)++EntryFuse.fusedY L (-cy)++tickF L)++entryRest L by
      simp only [List.append_assoc]] at h12
  exact tri_transfer (fun s hs m1 m2 => entry1_eq L hw hn (-cx) (-cy) s X.val X.isLt Y G
    hs.x hs.y hs.generic hs.clean m1 m2) h12

theorem suffix2 (X Y k cy : Fp) (G : Bool) (origin : BasisState) (hX : X+(if G then k else 0)≠0) :
    Triple (PointDialogValues L X Y G origin)
      (entryM L k++(exitRest L++exitY L cy))
      (PointDialogValues L (X+(if G then k else 0))
        (Y*(X+(if G then k else 0))-(if G then cy else 0)) G origin) := by
  have h4 := fastStep_addX L hw hn X Y G origin k
  have h5 := fusedMultiply_step L hw hn (FrontierEntry1591Callers.exit FrontierEntry1591Kernel.exitKernel L)
    (FrontierEntry1591Callers.exit_correct FrontierEntry1591Kernel.exitKernel FrontierEntry1591Kernel.exit_support
      FrontierEntry1591Kernel.exit_correct L hw hn) (X+(if G then k else 0)) Y cy G origin hX
  have h45 := h4.seq h5
  rw [fusedMultiply,exit_split,
    show fastConstAdd L L.point.x k++(tickF L++exitRest L++exitY L cy)=
      (fastConstAdd L L.point.x k++tickF L)++(exitRest L++exitY L cy) by
      simp only [List.append_assoc]] at h45
  exact tri_transfer (fun s hs m1 m2 => entry_eq L hw hn k s X.val X.isLt G hs.x hs.generic hs.clean m1 m2) h45

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h12 := prefix1 L hw hn logicalND hlo logicalAway logicalReplay X Y cx cy true origin
    (by simp only [if_true,←sub_eq_add_neg]; exact sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,←sub_eq_add_neg,ha] at h12
  have h3 := FrontierEntry1591Point.square_step L hw hn (X-cx) a true origin
  simp only [if_true] at h3
  have hd4 : ((X-cx)-a*a+(OwnDiagAll12Square.sqOff : Nat))+(3*cx-(OwnDiagAll12Square.sqOff : Nat))=d := by
    have e := hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [← e]; ring
  have h45 := suffix2 L hw hn logicalND hlo logicalAway logicalReplay ((X-cx)-a*a+(OwnDiagAll12Square.sqOff : Nat)) a
    (3*cx-(OwnDiagAll12Square.sqOff : Nat)) cy true origin (by simp only [if_true]; rw [hd4]; exact hd)
  simp only [if_true] at h45
  rw [hd4] at h45
  have h6 := fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at h6
  rw [show cx-d=genericX X Y cx cy by dsimp [d]; ring] at h6
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h45 h6
  have h := ((h12.seq h3).seq h45).seq h6
  simpa only [generic,List.append_assoc] using h

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have h12 := prefix1 L hw hn logicalND hlo logicalAway logicalReplay X Y cx cy false origin
    (by simpa using hX)
  have h3 := FrontierEntry1591Point.square_step L hw hn X (Y/X) false origin
  have h45 := suffix2 L hw hn logicalND hlo logicalAway logicalReplay X (Y/X) (3*cx-(OwnDiagAll12Square.sqOff : Nat)) cy
    false origin (by simpa using hX)
  have h6 := fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y := div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,if_true,Nat.cast_zero,add_zero,sub_zero] at h12 h3 h45 h6
  rw [back] at h45
  have h := ((h12.seq h3).seq h45).seq h6
  simpa only [generic,List.append_assoc] using h

end Generic


/-! ### Resources -/

section Res

attribute [local irreducible] wires E1Merge.merged NativeFirstDirect.forward

/-- The logical program under the three integer-host relabelings. -/
def sigP (P : Program) : Program :=
  renameProgram Q7IntegerHost.swap (renameProgram Q6IntegerHost.swap (renameProgram Q5Global718.swap P))

/-- The merged circuit after the work-wire transport. -/
def rhoP (P : Program) : Program := renameProgram rho P

theorem entryM_eq (L : ControlledPointLayout) (k : Fp) :
    entryM L k=renameProgram (wireFn2 L) (sigP (rhoP (E1Merge.merged base (base 2400) k.val))) := by
  simp only [entryM,sigP,rhoP,renameProgram_comp]
  rfl

theorem sigP_wires (P : Program) (q : Wire) (hq : q∈wires (sigP P)) : ∃a∈wires P,q=sig a := by
  simp only [sigP,renameProgram_support,Finset.mem_image] at hq
  obtain ⟨b,⟨c,⟨a,ha,rfl⟩,rfl⟩,rfl⟩ := hq
  exact ⟨a,ha,rfl⟩

theorem rhoP_wires (P : Program) (q : Wire) (hq : q∈wires (rhoP P)) : ∃a∈wires P,q=rho a := by
  simp only [rhoP,renameProgram_support,Finset.mem_image] at hq
  obtain ⟨a,ha,rfl⟩ := hq
  exact ⟨a,ha,rfl⟩

/-- Every label of the placed merged circuit, before the layout map. -/
theorem merged_labels (k : Nat) (q : Wire)
    (hq : q∈wires (sigP (rhoP (E1Merge.merged base (base 2400) k)))) :
    ∃ j, q=base (sw (rhoN j)) ∧
      (j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j = 721 ∨ j = 722 ∨ j = 2400) := by
  obtain ⟨a,ha,e⟩ := sigP_wires _ q hq
  obtain ⟨b,hb,e2⟩ := rhoP_wires _ a ha
  obtain ⟨j,ej,hj⟩ := S_cases b (Finset.mem_of_subset (merged_S k) hb)
  refine ⟨j,?_,hj⟩
  rw [e,e2,ej,rho_base,sig_base]

theorem logicalM (k : Nat) :
    wires (sigP (rhoP (E1Merge.merged base (base 2400) k)))⊆OB5Support.logicalSites := by
  intro q hq
  obtain ⟨j,rfl,hj⟩ := merged_labels k q hq
  exact sw_logical _ (rhoN_range j hj)

theorem entryM_counts (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (entryM L k)=1026 ∧ measurementCount (entryM L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1Merge.merged base (base 2400) k.val)
  have c := E1Merge.merged_counts base (base 2400) k.val
  rw [entryM,r.1,r.2]; exact c

theorem tickF_counts (L : ControlledPointLayout) :
    toffoliCount (tickF L)=508 ∧ measurementCount (tickF L)=508 := by
  have r := renameProgram_counts (pmapR L) (NativeFirstDirect.forward base)
  have c := NativeFirstDirect.forward_counts base
  rw [tickF,r.1,r.2]; exact c

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw

theorem entryM_sites (k : Fp) : wires (entryM L k)⊆(OB5Support.sites L).toFinset := by
  rw [entryM_eq]
  exact OB5Support.placed_support_logical L hw _ (logicalM k.val)

include hn

theorem placed_avoid (P : Program) (hp : wires P⊆OB5Support.logicalSites) (i kk : Nat)
    (hi : base i∈OB5Support.logicalSites) (hm : wireFn2 L (base i)=L.core.poolWire kk)
    (free : base i∉wires P) : L.core.poolWire kk∉wires (renameProgram (wireFn2 L) P) := by
  rw [renameProgram_support]
  intro h
  obtain ⟨old,used,eq⟩ := Finset.mem_image.mp h
  have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
  have back := (placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (hp used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
  exact free (back ▸ used)

theorem sw_avoid (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j = 721 ∨ j = 722 ∨ j = 2400) :
    sw (rhoN j)∉FrontierEntry1591Callers.logicalOmissions := by
  simp only [FrontierEntry1591Callers.logicalOmissions,List.mem_cons,List.not_mem_nil,or_false]
  unfold sw rhoN; split_ifs <;> omega

theorem merged_omits (k : Fp) (i : Nat) (hi : i∈FrontierEntry1591Callers.logicalOmissions) :
    base i∉wires (sigP (rhoP (E1Merge.merged base (base 2400) k.val))) := by
  intro h
  obtain ⟨j,e,hj⟩ := merged_labels k.val (base i) h
  have := base_injective e
  exact sw_avoid L hw hn j hj (this ▸ hi)

theorem entryM_free (k : Fp) (kk : Nat) (hk : kk∈Q1591Resources.genericOmissions) :
    L.core.poolWire kk∉wires (entryM L k) := by
  rw [entryM_eq]
  exact FrontierEntry1591Callers.placed_omissions _ (logicalM k.val) (merged_omits L hw hn k) L hw hn kk hk

theorem entryM_physical (k : Fp) : GatePhysical (entryM L k) := by
  rw [entryM]
  exact gatePhysical_rename_support (pmapR L) (E1Merge.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (Finset.mem_of_subset (merged_S k.val) ha) b
      (Finset.mem_of_subset (merged_S k.val) hb) e)
    (E1Merge.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

end Res

end ECDSAAdd.Entrant.E1Generic




