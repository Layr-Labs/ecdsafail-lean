import ECDSAAdd.Submission.Entrant.MainPart04

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.E1QubitPlacement =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Prefix1590Point
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierEntry1591Native
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1Merge

/-! Research source. Complete proof bodies, adapted from the pinned accepted
E1 placement proof to a different bijection. No sorry/axiom/certificate.
Not elaborated or replayed in this environment. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1QubitPlacement
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk

/-! Complete zero-cost placement for E1 on the old Q1588 rolling route.
The global bijection first moves three E1-only scratch locations:
  compare carry511 ->725, product721 ->723, product722 ->724.
It then hosts native cin1797 at511 and applies the three rolling phase hosts.
No two live values are aliased. All added destinations are already-counted
ordinary field carry sites. This file has NOT been Lean-checked here. -/

def nativeSwap : Equiv.Perm Wire := Equiv.swap (base 1797) (base 511)
def phaseHost : Equiv.Perm Wire :=
  (Equiv.swap (base 1026) (base 721)).trans
    ((Equiv.swap (base 1541) (base 722)).trans
      (Equiv.swap (base 1542) (base 720)))
def sig (q : Wire) : Wire := phaseHost (nativeSwap q)
def pmap (L : ControlledPointLayout) (q : Wire) : Wire := wireFn2 L (sig q)

def sw (i : Nat) : Nat :=
  if i=1797 then 511 else if i=511 then 1797 else
  if i=1026 then 721 else if i=721 then 1026 else
  if i=1541 then 722 else if i=722 then 1541 else
  if i=1542 then 720 else if i=720 then 1542 else i

theorem swap_base (a b i : Nat) :
    Equiv.swap (base a) (base b) (base i)=base (if i=a then b else if i=b then a else i) := by
  rw [Equiv.swap_apply_def]
  by_cases h1 : i=a
  · subst h1; simp
  · have n1 : base i≠base a := fun e => h1 (base_injective e)
    by_cases h2 : i=b
    · subst h2; simp [n1,h1]
    · have n2 : base i≠base b := fun e => h2 (base_injective e)
      simp [n1,n2,h1,h2]

theorem sig_base (i : Nat) : sig (base i)=base (sw i) := by
  unfold sig phaseHost nativeSwap
  simp only [Equiv.trans_apply,swap_base]
  congr 1
  unfold sw
  split_ifs <;> omega

theorem sig_injective : Function.Injective sig :=
  phaseHost.injective.comp nativeSwap.injective

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

/-- Label range of the merged circuit after the scratch relocation `rho`. -/
abbrev Rng (i : Nat) : Prop :=
  (i < 515 ∧ i ≠ 511) ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 723 ∨ i = 724 ∨ i = 725 ∨ i = 2400

theorem sw_slot (i : Nat) (hi : Rng i) : base (sw i)∈slots.toFinset := by
  apply slot_mem
  · unfold live sw; split_ifs <;> omega
  · unfold CompressedAllocation.omitted sw; split_ifs <;> omega

theorem sw_logical (i : Nat) (hi : Rng i) : base (sw i)∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨sw i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  unfold sw; split_ifs <;> omega

/-- Three disjoint E1 scratch relocations. The direct tick omits all six ports. -/
def rho : Equiv.Perm Wire :=
  (Equiv.swap (base 511) (base 725)).trans
    ((Equiv.swap (base 721) (base 723)).trans (Equiv.swap (base 722) (base 724)))
def rhoN (i : Nat) : Nat :=
  if i=511 then 725 else if i=725 then 511 else
  if i=721 then 723 else if i=723 then 721 else
  if i=722 then 724 else if i=724 then 722 else i

theorem rho_base (i : Nat) : rho (base i)=base (rhoN i) := by
  unfold rho rhoN
  simp only [Equiv.trans_apply,swap_base]
  congr 1
  split_ifs <;> omega

theorem rho_injective : Function.Injective rho := rho.injective

theorem rhoN_range (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) :
    Rng (rhoN i) := by
  unfold Rng rhoN; split_ifs <;> omega

/-- Placement of the merged circuit: relocation, the four relabelings, the layout map. -/
def pmapR (L : ControlledPointLayout) (q : Wire) : Wire := pmap L (rho q)


theorem sig_rho_x (i : Nat) (hi : 770≤ i ∧ i<1026) :
    sig (rho (base i))=base i := by
  have hr : rhoN i=i := by unfold rhoN;split_ifs <;> omega
  have hs : sw i=i := by unfold sw;split_ifs <;> omega
  rw [rho_base,hr,sig_base,hs]

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
  change wireFn2 L (sig (rho (base i)))=wireFn2 L (base i)
  rw [sig_rho_x i (by omega)]

theorem pmap_g : pmapR L (base 2400)=L.core.generic := by
  have pl := placement2 L hw hn
  unfold pmapR pmap; rw [rho_base,sig_base]
  have : sw (rhoN 2400)=2400 := by unfold sw rhoN; simp
  rw [this]; exact pl.controlMap

theorem pmap_pool (q : Wire) (hq : q∈S) (hx : q∉wireBlock base 770 256) (hg : q≠base 2400) :
    pmapR L q∈L.dialogPool := by
  obtain ⟨i,rfl,hi⟩ := S_cases q hq
  have pl := placement2 L hw hn
  let j:=sw (rhoN i)
  have indexEq : sig (rho (base i))=base j := by rw [rho_base,sig_base]
  have injective:=sig_injective.comp rho_injective
  have fixedG : sig (rho (base 2400))=base 2400 := by decide +kernel
  have jRange : j<1798 ∨ j=2400 := by
    have range:=rhoN_range i hi
    dsimp [j]
    generalize rhoN i=v at range ⊢
    unfold Rng at range
    unfold sw
    split_ifs <;> omega
  have jNotG : j≠2400 := by
    intro e
    apply hg
    exact injective (indexEq.trans ((congrArg base e).trans fixedG.symm))
  have jlt : j<1798 := by omega
  have jNotX : ¬(770≤ j ∧ j<1026) := by
    intro bounds
    have equal:=injective (indexEq.trans (sig_rho_x j bounds).symm)
    have same:=base_injective equal
    apply hx
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1];omega,rfl⟩
  change wireFn2 L (sig (rho (base i)))∈L.dialogPool
  rw [indexEq]
  apply pl.sharedWork
  · exact List.mem_map.mpr ⟨j,by simp only [skywalkSharedWires,List.mem_range'_1];omega,rfl⟩
  · exact sw_slot _ (rhoN_range i hi)
  · intro h
    obtain ⟨v,hv,e⟩:=List.mem_map.mp h
    have same:=base_injective e
    simp only [List.mem_range'_1] at hv
    exact jNotX (by omega)
  · intro h
    obtain ⟨v,hv,e⟩:=List.mem_map.mp h
    have same:=base_injective e
    simp only [List.mem_range'_1] at hv
    omega

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

-- Keep the inherited width argument for existing callers.
set_option linter.unusedSectionVars false in
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

/-! Resource and support facts are independent of the point-level caller. -/
section Resources
open Challenge
attribute [local irreducible] wires

def logicalEntry (k : Nat) : Program :=
  renameProgram sig (renameProgram rho (E1Merge.merged base (base 2400) k))

theorem entryM_eq (L : ControlledPointLayout) (k : Fp) :
    entryM L k=renameProgram (wireFn2 L) (logicalEntry k.val) := by
  simp only [entryM,logicalEntry,renameProgram_comp]
  rfl

private theorem renamed_twice_labels (f h : Wire→Wire) (P : Program) (U : Finset Wire)
    (sub : wires P⊆U) (q : Wire) (hq : q∈wires (renameProgram f (renameProgram h P))) :
    ∃b∈U,q=f (h b) := by
  rw [renameProgram_support,renameProgram_support] at hq
  obtain ⟨a,ha,ea⟩:=Finset.mem_image.mp hq
  obtain ⟨b,hb,eb⟩:=Finset.mem_image.mp ha
  refine ⟨b,sub hb,?_⟩
  rw [←ea,←eb]


theorem merged_labels (k : Nat) (q : Wire) (hq : q∈wires (logicalEntry k)) :
    ∃ j, q=base (sw (rhoN j)) ∧
      (j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
        j=721 ∨ j=722 ∨ j=2400) := by
  obtain ⟨b,hb,eq⟩:=renamed_twice_labels sig rho
    (E1Merge.merged base (base 2400) k) S (merged_S k) q hq
  obtain ⟨j,rfl,hj⟩:=S_cases b hb
  refine ⟨j,?_,hj⟩
  rw [eq,rho_base,sig_base]

theorem logicalM (k : Nat) : wires (logicalEntry k)⊆OB5Support.logicalSites := by
  intro q hq
  obtain ⟨j,rfl,hj⟩ := merged_labels k q hq
  exact sw_logical _ (rhoN_range j hj)

theorem sw_avoid (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
      j=721 ∨ j=722 ∨ j=2400) :
    sw (rhoN j)∉[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  have range:=rhoN_range j hj
  generalize rhoN j=i at range ⊢
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  unfold Rng at range
  unfold sw
  split_ifs <;> omega

theorem merged_omits (k i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (logicalEntry k) := by
  intro h
  obtain ⟨j,e,hj⟩ := merged_labels k (base i) h
  have eq := base_injective e
  exact sw_avoid j hj (eq ▸ hi)

theorem entryM_counts (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (entryM L k)=1025 ∧ measurementCount (entryM L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1Merge.merged base (base 2400) k.val)
  have c := E1Merge.merged_counts base (base 2400) k.val
  rw [entryM,r.1,r.2]; exact c

theorem tickF_counts (L : ControlledPointLayout) :
    toffoliCount (tickF L)=508 ∧ measurementCount (tickF L)=508 := by
  have r := renameProgram_counts (pmapR L) (NativeFirstDirect.forward base)
  have c := NativeFirstDirect.forward_counts base
  rw [tickF,r.1,r.2]; exact c

theorem entryM_slots (L : ControlledPointLayout) (k : Fp) :
    gateSlots (entryM L k)≤25000 := by
  simpa only [entryM,Baselines.rename_gateSlots] using
    E1Merge.merged_slots base (base 2400) k.val

theorem entryM_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryM L k)⊆(OB5Support.sites L).toFinset := by
  rw [entryM_eq]
  exact OB5Support.placed_support_logical L hw _ (logicalM k.val)

theorem entryM_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (entryM L k) := by
  rw [entryM]
  exact gatePhysical_rename_support (pmapR L) (E1Merge.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (merged_S k.val ha) b (merged_S k.val hb) e)
    (E1Merge.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

theorem prefix_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryM L k)+249=
      toffoliCount (fastConstAdd L L.point.x k++tickF L) ∧
    measurementCount (entryM L k)+248=
      measurementCount (fastConstAdd L L.point.x k++tickF L) := by
  have a := fastConstAdd_counts L hw L.point.x (Or.inl rfl) k
  have e := entryM_counts L k
  have t := tickF_counts L
  simp only [toffoliCount_append,measurementCount_append]
  constructor <;> omega

end Resources

/-- All pre-relocated ports are absent from the actual direct first tick. -/
theorem rho_fix (f : Wire → Wire) :
    renameProgram (fun q => f (rho q)) (NativeFirstDirect.forward base)=
      renameProgram f (NativeFirstDirect.forward base) := by
  have fix (P : Program) (support : wires P⊆(NativeFirstDirect.prefixSites base).toFinset) :
      renameProgram (fun q => f (rho q)) P=renameProgram f P := by
    apply renameProgram_congr_support
    intro q hq
    have h := support hq
    rw [List.mem_toFinset] at h
    simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at h
    have e : ∃ i, q=base i ∧
        (i<257 ∨ (770≤ i ∧ i<1028) ∨ (1540≤ i ∧ i<1796) ∨ i=1028 ∨ i=1797) := by
      rcases h with ((h|h)|h)|h|h
      all_goals first
        | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
           simp only [List.mem_range'_1] at hi
           exact ⟨i,rfl,by omega⟩)
        | exact ⟨_,h,by omega⟩
    obtain ⟨i,rfl,hi⟩ := e
    rw [rho_base]
    have fixed : rhoN i=i := by unfold rhoN; split_ifs <;> omega
    rw [fixed]
  exact fix (NativeFirstDirect.forward base) (NativeFirstDirect.prefix_support base).1

/-- The new merged entry has exactly the old rolling native tick boundary. -/
theorem tick_eq (L : ControlledPointLayout) :
    renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base))=tickF L := by
  rw [tickF,show pmapR L=fun q => pmap L (rho q) from rfl,rho_fix]
  simp only [FrontierEntry1591Native.forward,FrontierEntry1591Native.Transport.program,
    renameProgram_comp]
  rfl

end ECDSAAdd.Entrant.E1QubitPlacement
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1Reflected =====
section
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectValues
-- consolidated import: import ECDSAAdd.Arithmetic.Compare
-- consolidated import: import ECDSAAdd.Arithmetic.ComparePhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MaskedConstant
-- consolidated import: import ECDSAAdd.Arithmetic.MappedSources
-- consolidated import: import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.Copy
-- consolidated import: import ECDSAAdd.Arithmetic.Rotate
-- consolidated import: import ECDSAAdd.Arithmetic.Reduction
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredGateSupport
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
-- consolidated import: import ECDSAAdd.Baselines.SlotAlgebra
-- consolidated import: import ECDSAAdd.Baselines.SlotMapped
-- consolidated import: import ECDSAAdd.Baselines.SlotNativeFirst

set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Research adaptation of pinned accepted E1Merge. Reflects canonical input
unconditionally, then performs its controlled constant addition and first tick.
Full proof bodies are supplied; this module has NOT been Lean-checked here.
Input/output contract remains full State and every measurement record. -/
namespace ECDSAAdd.Entrant.E1Reflected
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum

/-! ### Arithmetic of the merged first tick -/

theorem p_val : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [ECDSAAdd.p]

/-- bit 0 of the selected constant `g·k − f·p`. -/
def ksel0 (k : Nat) (G f : Bool) : Bool := (G && decide (k%2=1)) ^^ f
/-- low bit of the input implied by `(g,f,par)`. -/
def x0 (k : Nat) (G f par : Bool) : Bool := par ^^ ksel0 k G f

/-- Constant added to the complemented 258-bit `x>>1` bank to obtain the direct first-tick `K` word. -/
def tk (k : Nat) (G f par : Bool) : Nat :=
  if f then
    if G then (kConstant false par+1+(k-1-(x0 k G f par).toNat-par.toNat)/2)%2^258
    else 0
  else (kConstant false par+1+
    (p-1-(x0 k G f par).toNat+(if G then k else 0)-par.toNat)/2)%2^258

def delta (par : Bool) : Nat := if par then p else 2^257-p

def thr (k : Nat) (G par : Bool) : Nat := if G then (if par then (k+p+1)/2 else (k+1)/2) else 0

theorem hC_val : hConstant = 57896044618658097711785492504343953926634992332820282019728792003954417335832 := by
  norm_num [hConstant, ECDSAAdd.p]
theorem kC_val (par : Bool) : kConstant false par =
    if par then 405272312330606683982498447530407677486444946329741974138101544027698101223913
    else 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  cases par <;> norm_num [kConstant, ECDSAAdd.p]


theorem arith (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let f := decide (X<(if G then k else 0))
    let dx := (p-1-X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    decide (X%2=1)=x0 k G f par ∧
    (2^258-1-X/2+tk k G f par)%2^258=K ∧
    H=dx/2+(if par then hConstant else 0) ∧
    f=decide (H<thr k G par) ∧
    tk k G f par<2^258 := by
  intro f dx par K H
  rw [p_val] at hk hX
  simp only [f,dx,par,K,H,tk,delta,thr,x0,ksel0,kC_val,hC_val,p_val,Nat.reducePow]
  clear H K par dx f
  cases G
  · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+0)%115792089237316195423570985008687907853269984665640564039457584007908834671663=115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X :=
      Nat.mod_eq_of_lt (by omega)
    simp only [if_false,Bool.false_eq_true,Nat.not_lt_zero,decide_false,
      e1,Bool.false_and,Bool.false_xor,Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X) with h|h <;>
      simp only [h,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
  · simp only [if_true,Bool.true_and]
    by_cases hf : X<k
    · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=k-1-X := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
        omega
      have e2 : decide (X<k)=true := by simp [hf]
      simp only [e1,e2,Bool.xor_true]
      rcases Nat.mod_two_eq_zero_or_one (k-1-X) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
    · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k := Nat.mod_eq_of_lt (by omega)
      have e2 : decide (X<k)=false := by simp [hf]
      simp only [e1,e2,Bool.xor_false]
      rcases Nat.mod_two_eq_zero_or_one (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩

/-! ### Circuit -/

def cmpC : Nat := 2^256-p

def srcR (w : Nat → Wire) : List Wire := wireBlock w 0 256
def xR (w : Nat → Wire) : List Wire := wireBlock w 770 256
def cR (w : Nat → Wire) : List Wire := wireBlock w 256 256
def hR (w : Nat → Wire) : List Wire := wireBlock w 0 258
def kR (w : Nat → Wire) : List Wire := wireBlock w 770 258
def tR (w : Nat → Wire) : List Wire := wireBlock w 1029 256
def hpR (w : Nat → Wire) : List Wire := wireBlock w 1 257
def aC (w : Nat → Wire) : List Wire := wireBlock w 1540 257
def hC2 (w : Nat → Wire) : List Wire := wireBlock w 1540 256
def hp8 (w : Nat → Wire) : List Wire := wireBlock w 1 256
def hC3 (w : Nat → Wire) : List Wire := wireBlock w 1540 255

def comparePart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (srcR w) k++
  compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514)++
  maskedConstant g (srcR w) k

def parGates (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]++
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]

def prodPart (w : Nat → Wire) (g : Wire) : Program :=
  [.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)]

def c1 (k : Nat) : Nat := tk k false false false
def cg (k : Nat) : Nat := tk k true false false ^^^ tk k false false false
def cf (k : Nat) : Nat := tk k true true false ^^^ tk k true false false
def cp (k : Nat) : Nat := tk k false false true ^^^ tk k false false false
def cgp (k : Nat) : Nat :=
  tk k true false true ^^^ tk k true false false ^^^ tk k false false true ^^^ tk k false false false
def cfp (k : Nat) : Nat :=
  tk k true true true ^^^ tk k true true false ^^^ tk k true false true ^^^ tk k true false false

def loadK (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1 k)++maskedConstant g (hR w) (cg k)++maskedConstant (w 514) (hR w) (cf k)++
  maskedConstant (w 1028) (hR w) (cp k)++maskedConstant (w 721) (hR w) (cgp k)++
  maskedConstant (w 722) (hR w) (cfp k)

def kAddM (w : Nat → Wire) : Program := mappedAdd (mappedRead (hR w) false) (kR w) (aC w) (w 1797)

def dBits (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := (2^257-p).testBit j
  let b := p.testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def hAddM (w : Nat → Wire) : Program := mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)

/-- `hAddM` with its first carry trimmed. The first mapped bit is the literal `1`
(`2^257-p` and `p` are both odd) and the carry-in `w 1797` is clean, so the first
majority's Toffoli `CCX (w 1) (w 1797) (w 1540)` never fires; it is dropped. -/
def hPost (w : Nat → Wire) : Program :=
  mappedAdd (dBits w).tail (hpR w).tail (hC2 w).tail (w 1540) ++
    mappedEraseCarry {wire:=none,flip:=true} (w 1) (w 1797) (w 1540) ++
    mappedSum {wire:=none,flip:=true} (w 1) (w 1797)

def hAddT (w : Nat → Wire) : Program := [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ hPost w


def thrA (k : Nat) : Nat := (k+1)/2
def thrB (k : Nat) : Nat := (k+1)/2 ^^^ (k+p+1)/2

def loadT (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrA k)++maskedConstant (w 721) (tR w) (thrB k)

/-- Unconditional canonical reflection followed by controlled constant addition, merged into the direct first tick. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w)++notRegister (kR w))++prodPart w g++loadK w g k++kAddM w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-! ### Layout facts -/

section Layout
variable (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
include hn

theorem mem_blk (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) :
    w i ∈ wireBlock w a n ↔ a ≤ i ∧ i < a + n := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := skywalkPool_index_inj w hn i j hi (by omega) he.symm
    omega
  · intro h
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem w_ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
  index_ne w hn i j hi hj h

omit hn in
theorem blk_sub (a n b m : Nat) (h1 : b≤a) (h2 : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem blk_nd (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := block_nodup w hn a n ha

theorem blk_dis (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798) (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := block_disjoint w hn a n b m ha hb sep

theorem g_out (g : Wire) (hg : g∉skywalkPoolWires w) (a n : Nat) (ha : a+n≤1798) : g∉wireBlock w a n :=
  fun h => hg (blk_sub w a n 0 1798 (by omega) (by omega) g h)

theorem g_ne (g : Wire) (hg : g∉skywalkPoolWires w) (i : Nat) (hi : i<1798) : g≠w i := by
  intro e; apply hg; rw [e]
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

end Layout


/-! ### Frame -/

def mutL (w : Nat → Wire) : List Wire := hR w++kR w++tR w++[w 1028,w 514,w 721,w 722]

def MF (w : Nat → Wire) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState) : Prop :=
  regValue (hR w) s=H ∧ regValue (kR w) s=X ∧ regValue (tR w) s=T ∧
  s (w 1028)=par ∧ s (w 514)=f ∧ s (w 721)=gp ∧ s (w 722)=fp ∧ ∀q,q∉mutL w → s q=b0 q

theorem keep (R : List Wire) (s t : BasisState) (hf : ∀q,q∉R → t q=s q) (C : List Wire)
    (hC : ∀q∈C,q∉R) : regValue C t=regValue C s :=
  regValue_congr C t s (fun q hq => hf q (hC q hq))

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem hR_nd : (hR w).Nodup := blk_nd w hn 0 258 (by omega)
theorem kR_nd : (kR w).Nodup := blk_nd w hn 770 258 (by omega)
theorem tR_nd : (tR w).Nodup := blk_nd w hn 1029 256 (by omega)

theorem hR_kR : ∀q∈kR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 770 258 (by omega) (by omega) (by omega)) h hq
theorem hR_tR : ∀q∈tR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem kR_hR : ∀q∈hR w,q∉kR w := fun q hq h => hR_kR w hn q h hq
theorem kR_tR : ∀q∈tR w,q∉kR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 770 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem tR_hR : ∀q∈hR w,q∉tR w := fun q hq h => hR_tR w hn q h hq
theorem tR_kR : ∀q∈kR w,q∉tR w := fun q hq h => kR_tR w hn q h hq

theorem nb (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n :=
  block_not_mem w hn i a n hi ha sep

theorem out_of_mut (R : List Wire) (hR' : ∀q∈R,q∈mutL w) (q : Wire) (hq : q∉mutL w) : q∉R :=
  fun h => hq (hR' q h)

theorem hR_mut : ∀q∈hR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem kR_mut : ∀q∈kR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem tR_mut : ∀q∈tR w,q∈mutL w := fun q hq => by simp [mutL,hq]

/-- An operation that changes only the `H` block. -/
theorem stepH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉hR w → t.basis q=s.basis q) (H' : Nat)
    (hv : regValue (hR w) t.basis=H') : MF w b0 H' X T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨hv,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (hR_kR w hn)]; exact h2
  · rw [keep _ _ _ hf _ (hR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 0 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 0 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 0 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 0 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (hR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the `K` block. -/
theorem stepK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉kR w → t.basis q=s.basis q) (X' : Nat)
    (hv : regValue (kR w) t.basis=X') : MF w b0 H X' T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,hv,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (kR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (kR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 770 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 770 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 770 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (kR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the threshold block. -/
theorem stepT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉tR w → t.basis q=s.basis q) (T' : Nat)
    (hv : regValue (tR w) t.basis=T') : MF w b0 H X T' par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (tR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (tR_kR w hn)]; exact h2
  · rw [hf _ (nb w hn 1028 1029 256 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 1029 256 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 1029 256 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 1029 256 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (tR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes one scalar wire `w j` of the frame. -/
theorem stepBit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State) (j : Nat)
    (hj : j=1028 ∨ j=514 ∨ j=721 ∨ j=722)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q≠w j → t.basis q=s.basis q) :
    MF w b0 H X T (if j=1028 then t.basis (w j) else par) (if j=514 then t.basis (w j) else f)
      (if j=721 then t.basis (w j) else gp) (if j=722 then t.basis (w j) else fp) t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have hjr : j<1798 := by omega
  have nh : w j∉hR w := nb w hn j 0 258 hjr (by omega) (by omega)
  have nk : w j∉kR w := nb w hn j 770 258 hjr (by omega) (by omega)
  have nt : w j∉tR w := nb w hn j 1029 256 hjr (by omega) (by omega)
  have ne (i : Nat) (hi : i<1798) (hij : i≠j) : w i≠w j := w_ne w hn i j hi hjr hij
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nh (e ▸ hq)))]; exact h1
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nk (e ▸ hq)))]; exact h2
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nt (e ▸ hq)))]; exact h3
  · by_cases e : j=1028
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 1028 (by omega) (Ne.symm e))]; exact h4
  · by_cases e : j=514
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 514 (by omega) (Ne.symm e))]; exact h5
  · by_cases e : j=721
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 721 (by omega) (Ne.symm e))]; exact h6
  · by_cases e : j=722
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 722 (by omega) (Ne.symm e))]; exact h7
  · intro q hq
    have : q≠w j := by
      intro e; apply hq; rw [e]
      rcases hj with rfl|rfl|rfl|rfl <;> simp [mutL]
    rw [hf q this]; exact h8 q hq

end Steps


/-! ### Concrete steps -/

theorem run_cx (a b : Wire) (m : List Bool) (s : State) :
    run [.CX a b] m s=⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis a)⟩ := rfl
theorem run_ccx (a b c : Wire) (m : List Bool) (s : State) :
    run [.CCX a b c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ (s.basis a && s.basis b))⟩ := rfl
theorem run_x (a : Wire) (m : List Bool) (s : State) :
    run [.X a] m s=⟨s.phase,writeBit s.basis a (!s.basis a)⟩ := rfl

theorem run_meas_and (t a b : Wire) (m : List Bool) (s : State) (ha : a≠t) (hb : b≠t)
    (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases m.headD false <;> simp [correct,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,ht]

section Concrete
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem kR_split (s : BasisState) :
    regValue (kR w) s=(s (w 770)).toNat+2*regValue (wireBlock w 771 257) s := by
  have e : kR w=w 770::wireBlock w 771 257 := by
    simp [kR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 770) <;> simp [regValue,h]

theorem hR_split (s : BasisState) :
    regValue (hR w) s=(s (w 0)).toNat+2*regValue (hpR w) s := by
  have e : hR w=w 0::hpR w := by
    simp [hR,hpR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 0) <;> simp [regValue,h]

theorem hR_src (s : BasisState) :
    regValue (hR w) s=regValue (srcR w) s+2^256*regValue (wireBlock w 256 2) s := by
  have e : hR w=srcR w++wireBlock w 256 2 := by
    rw [hR,srcR,wireBlock_append]
  rw [e,regValue_append,srcR,wireBlock_length]

theorem kR_x (s : BasisState) :
    regValue (kR w) s=regValue (xR w) s+2^256*regValue (wireBlock w 1026 2) s := by
  have e : kR w=xR w++wireBlock w 1026 2 := by
    rw [kR,xR,wireBlock_append]
  rw [e,regValue_append,xR,wireBlock_length]

theorem kR_low (s : BasisState) :
    regValue (kR w) s=regValue (wireBlock w 770 257) s+2^257*regValue (wireBlock w 1027 1) s := by
  have e : kR w=wireBlock w 770 257++wireBlock w 1027 1 := by
    rw [kR,wireBlock_append]
  rw [e,regValue_append,wireBlock_length]

/-- A CX targeting the parity wire. -/
theorem stepParCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 1028) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 1028)] (MF w b0 H X T (par ^^ cv) f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 1028)
    (s.basis (w 1028) ^^ s.basis c)⟩ 1028 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.1,hcv s.basis h] using this

/-- A CX targeting bit 0 of the K block. -/
theorem stepLowCX (b0 : BasisState) (H Y T : Nat) (b par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 770) (hcv : ∀s : BasisState,MF w b0 H (2*Y+b.toNat) T par f gp fp s → s c=cv) :
    Triple (MF w b0 H (2*Y+b.toNat) T par f gp fp) [.CX c (w 770)]
      (MF w b0 H (2*Y+(b ^^ cv).toNat) T par f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have m770 : w 770∈kR w := (mem_blk w hn 770 770 258 (by omega) (by omega)).mpr (by omega)
  have rest : ∀q∈wireBlock w 771 257,q≠w 770 := fun q hq e =>
    nb w hn 770 771 257 (by omega) (by omega) (by omega) (e ▸ hq)
  apply stepK w hn b0 H _ T par f gp fp s _ h
  · intro q hq; have : q≠w 770 := fun e => hq (e ▸ m770)
    simp [writeBit,Function.update_of_ne this]
  · have sp := kR_split w hn s.basis
    have sp2 := kR_split w hn (writeBit s.basis (w 770) (s.basis (w 770) ^^ s.basis c))
    rw [h.2.1] at sp
    rw [sp2,regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,Function.update_of_ne (rest q hq)])]
    rw [hcv s.basis h]
    simp only [writeBit,Function.update_self]
    cases hb : s.basis (w 770) <;> cases b <;> cases cv <;> simp [hb] at sp ⊢ <;> omega

end Concrete


section Concrete2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepXorH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (xorConstant (hR w) v) (MF w b0 (H^^^v) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := xorConstant_correct (hR w) (hR_nd w hn) v (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1])⟩

theorem stepMaskH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉hR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (hR w) v)
      (MF w b0 (H^^^(if cv then v else 0)) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (hR w) v (hR_nd w hn) hc
    (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1,hcv s.basis h])⟩

theorem stepMaskT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉tR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^256) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (tR w) v)
      (MF w b0 H X (T^^^(if cv then v else 0)) par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (tR w) v (tR_nd w hn) hc
    (by simpa [tR,wireBlock_length] using hv) s m
  exact ⟨hp,stepT w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.2.2.1,hcv s.basis h])⟩

theorem stepCCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (a b : Wire) (j : Nat)
    (hj : j=721 ∨ j=722) (av bv : Bool) (ha : a≠w j) (hb : b≠w j)
    (hav : ∀s : BasisState,MF w b0 H X T par f gp fp s → s a=av)
    (hbv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s b=bv) :
    Triple (MF w b0 H X T par f gp fp) [.CCX a b (w j)]
      (MF w b0 H X T par f (if j=721 then gp ^^ (av && bv) else gp)
        (if j=722 then fp ^^ (av && bv) else fp)) := by
  intro s m h
  rw [run_ccx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w j)
    (s.basis (w j) ^^ (s.basis a && s.basis b))⟩ j (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  rcases hj with rfl|rfl
  · simpa [writeBit,h.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this
  · simpa [writeBit,h.2.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this

theorem stepKAdd (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 H X T par f gp fp) (kAddM w) (MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m h
  have caway : ∀q∈aC w,q∉mutL w := by
    intro q hq hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
    · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
    all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm
  have m1797 : w 1797∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have nd : (w 1797::(kR w++aC w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),
      blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
  have src : ∀q∈mappedWires (mappedRead (hR w) false),q∉w 1797::(kR w++aC w) := by
    rw [mappedRead_wires]
    intro q hq hm
    simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with e|e|e
    · exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq)
    · exact hR_kR w hn q e hq
    · exact List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq e
  have cl : ∀q∈aC w,s.basis q=false := fun q hq => (h.2.2.2.2.2.2.2 q (caway q hq)).trans (hc q hq)
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (mappedRead (hR w) false) (kR w) (aC w) (w 1797) nd src
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length]) s m cl
  refine ⟨hp,stepK w hn b0 H X T par f gp fp s _ h he _ ?_⟩
  rw [hval,mappedRead_value,h.1,h.2.1,(h.2.2.2.2.2.2.2 _ m1797).trans hcin]
  simp [kR,wireBlock_length]

end Concrete2


def CF (w : Nat → Wire) (b0 : BasisState) (S : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue (srcR w) s=S ∧ s (w 514)=F ∧ ∀q,q∉srcR w → q≠w 514 → s q=b0 q

section Compare
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem src_nd : (srcR w).Nodup := blk_nd w hn 0 256 (by omega)
theorem w514_src : w 514∉srcR w := nb w hn 514 0 256 (by omega) (by omega) (by omega)

theorem cfMask (b0 : BasisState) (S : Nat) (F : Bool) (c : Wire) (hc : c∉srcR w) (hc' : c≠w 514)
    (v : Nat) (hv : v<2^256) :
    Triple (CF w b0 S F) (maskedConstant c (srcR w) v) (CF w b0 (S^^^(if b0 c then v else 0)) F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (srcR w) v (src_nd w hn) hc
    (by simpa [srcR,wireBlock_length] using hv) s m
  refine ⟨hp,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2 c hc hc']
  · rw [he _ (w514_src w hn)]; exact h.2.1
  · intro q h1 h2; rw [he q h1]; exact h.2.2 q h1 h2

theorem cfNot (b0 : BasisState) (S : Nat) (F : Bool) :
    Triple (CF w b0 S F) (notRegister (srcR w)) (CF w b0 (2^256-1-S) F) := by
  intro s m h
  rw [notRegister_correct (srcR w) (src_nd w hn)]
  refine ⟨rfl,?_,?_,?_⟩
  · change regValue (srcR w) (fun q => if q∈srcR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (srcR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.1]
    simp [srcR,wireBlock_length]
  · change (if w 514∈srcR w then !s.basis (w 514) else s.basis (w 514))=_
    simp [w514_src w hn,h.2.1]
  · intro q h1 h2
    change (if q∈srcR w then !s.basis q else s.basis q)=_
    simp [h1,h.2.2 q h1 h2]

theorem cfCmp (b0 : BasisState) (S : Nat) (F : Bool) (X : Nat) (hx : regValue (xR w) b0=X)
    (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false) :
    Triple (CF w b0 S F) (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))
      (CF w b0 S (F ^^ decide (X<S))) := by
  intro s m h
  have xs : ∀q∈xR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)) h' hq
  have x514 : ∀q∈xR w,q≠w 514 := fun q hq e => nb w hn 514 770 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have cs : ∀q∈cR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)) h' hq
  have c514 : ∀q∈cR w,q≠w 514 := fun q hq e => nb w hn 514 256 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have n513 : w 513∉srcR w := nb w hn 513 0 256 (by omega) (by omega) (by omega)
  have e513 : w 513≠w 514 := w_ne w hn 513 514 (by omega) (by omega) (by omega)
  have nd : (w 514::w 513::(xR w++srcR w++cR w)).Nodup := by
    have a1 := blk_dis w hn 770 256 0 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
    have l1 : (xR w++srcR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 770 256 (by omega),src_nd w hn,a1⟩
    have l2 : (xR w++srcR w++cR w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨e513.symm,⟨nb w hn 514 770 256 (by omega) (by omega) (by omega),w514_src w hn⟩,
        nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 513 770 256 (by omega) (by omega) (by omega),n513⟩,
        nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (xR w) (srcR w) (cR w) (w 513) (w 514) nd (by simp)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,srcR,xR,wireBlock_length]) s m
    ((h.2.2 _ n513 e513).trans hcin) (fun q hq => (h.2.2 q (cs q hq) (c514 q hq)).trans (hc q hq))
  refine ⟨hp,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => he q (fun e => w514_src w hn (e ▸ hq)))]; exact h.1
  · rw [hv,h.2.1,h.1,regValue_congr _ _ b0 (fun q hq => h.2.2 q (xs q hq) (x514 q hq)),hx]
    simp [controlValue]
  · intro q h1 h2; rw [he q h2]; exact h.2.2 q h1 h2

theorem cfCompare (b0 : BasisState) (F : Bool) (k X : Nat) (hk : k<2^256)
    (hx : regValue (xR w) b0=X) (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) :
    Triple (CF w b0 0 F) (comparePart w g k)
      (CF w b0 0 (F ^^ decide (X<(if b0 g then k else 0)))) := by
  have t := ((cfMask w hn b0 0 F g gs g514 k hk).seq
    (cfCmp w hn b0 _ F X hx hc hcin)).seq
    (cfMask w hn b0 _ _ g gs g514 k hk)
  simpa only [comparePart,Nat.zero_xor,Nat.xor_self] using t

end Compare


def dScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0

theorem dScalar_value (par : Bool) : dScalar par=delta par := by
  cases par <;> decide

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem d_list_value (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (2^257-p).testBit j
      let b := p.testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem dBits_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBits w) s=delta (s (w 1028)) := by
  rw [dBits,d_list_value]
  exact dScalar_value (s (w 1028))

theorem dBits_length (w : Nat → Wire) : (dBits w).length=257 := by simp [dBits]

theorem dBits_cons (w : Nat → Wire) :
    ∃ b' bs, dBits w = {wire:=none,flip:=true} :: b' :: bs := by
  have e : List.range 257 = 0 :: 1 :: List.range' 2 255 := by
    rw [List.range_eq_range']; rfl
  have t1 : (2^257-p).testBit 0 = true := by rw [p_val]; decide
  have t2 : p.testBit 0 = true := by rw [p_val]; decide
  rw [dBits, e, List.map_cons, List.map_cons]
  simp only [t1, t2, ite_true]
  exact ⟨_, _, rfl⟩

theorem hpR_cons (w : Nat → Wire) : ∃ y' ys, hpR w = w 1 :: y' :: ys :=
  ⟨w 2, (List.range' 3 255).map w, by
    rw [hpR, wireBlock, show (257:Nat) = 255+1+1 from rfl, List.range'_succ, List.range'_succ]; rfl⟩

theorem hC2_cons (w : Nat → Wire) : ∃ cs, hC2 w = w 1540 :: cs :=
  ⟨(List.range' 1541 255).map w, by
    rw [hC2, wireBlock, show (256:Nat) = 255+1 from rfl, List.range'_succ]; rfl⟩

theorem hAddM_split (w : Nat → Wire) :
    hAddM w = [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ [.CCX (w 1) (w 1797) (w 1540)] ++ hPost w := by
  obtain ⟨b', bs, hD⟩ := dBits_cons w
  obtain ⟨y', ys, hY⟩ := hpR_cons w
  obtain ⟨cs, hC⟩ := hC2_cons w
  simp only [hAddM, hPost, hD, hY, hC, List.tail_cons, mappedAdd, mappedMajority, List.append_assoc,
    List.cons_append, List.nil_append, if_true]

/-- Dropping a Toffoli whose second control is false after a measurement-free prefix. -/
theorem run_drop_ccx (P Q : Program) (a b t : Wire) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hb : (run P [] s).basis b = false) :
    run (P ++ [.CCX a b t] ++ Q) m s = run (P ++ Q) m s := by
  rw [List.append_assoc, run_append, run_append P Q, hP]
  simp only [List.take_zero, List.drop_zero, List.cons_append, List.nil_append, run, hb,
    Bool.and_false, Bool.xor_false, writeBit, Function.update_eq_self]

theorem hAddT_run (w : Nat → Wire) (h17 : w 1797 ≠ w 1540) (m : List Bool) (s : State)
    (hc : s.basis (w 1797) = false) : run (hAddT w) m s = run (hAddM w) m s := by
  rw [hAddM_split, hAddT, run_drop_ccx]
  · rfl
  · simp only [run, writeBit, Function.update_of_ne h17, hc]

theorem hAddT_counts (w : Nat → Wire) :
    toffoliCount (hAddT w) + 1 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT w) = measurementCount (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [toffoliCount_append, measurementCount_append]
  constructor
  · simp [toffoliCount]; omega
  · simp [measurementCount]

theorem hAddT_wires (w : Nat → Wire) : wires (hAddT w) ⊆ wires (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.subset_union_left) (Finset.Subset.refl _)

theorem hAddT_physical (w : Nat → Wire) (h : GatePhysical (hAddM w)) : GatePhysical (hAddT w) := by
  rw [hAddM_split] at h
  rw [hAddT]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem hAddT_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT w) + 1 = Challenge.gateSlots (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [Challenge.gateSlots_append]
  simp [Challenge.gateSlots, Challenge.instructionSlots]
  omega


theorem dBits_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBits w)) : q=w 1028 := by
  simp only [dBits,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all

section Rest
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCompareMF (b0 : BasisState) (k X : Nat) (hk : k<2^256) (hX : X<2^256)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) (gm : g∉mutL w) :
    Triple (MF w b0 0 X 0 false false false false) (comparePart w g k)
      (MF w b0 0 X 0 false (decide (X<(if b0 g then k else 0))) false false) := by
  intro s m h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have sp := hR_src w hn s.basis
  have kx := kR_x w hn s.basis
  have xl := regValue_lt (xR w) s.basis
  have sl := regValue_lt (srcR w) s.basis
  simp only [xR,srcR,wireBlock_length] at xl sl
  rw [h1] at sp; rw [h2] at kx
  have hx : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    omega
  have src0 : regValue (srcR w) s.basis=0 := by omega
  have top0 : regValue (wireBlock w 256 2) s.basis=0 := by
    by_contra hne; have : 1≤regValue (wireBlock w 256 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
    have : 2^256≤2^256*regValue (wireBlock w 256 2) s.basis := Nat.le_mul_of_pos_right _ this
    omega
  have hzero := (regValue_zero _ _).mp h1
  have cc : ∀q∈cR w,s.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    by_cases hi2 : i<258
    · exact hzero _ ((mem_blk w hn i 0 258 (by omega) (by omega)).mpr (by omega))
    · rw [h8 _ ?_]; exact hc i (by omega) (by omega)
      simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨⟨⟨nb w hn i 0 258 (by omega) (by omega) (by omega),nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
        nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
        exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have m513 : w 513∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 513 0 258 (by omega) (by omega) (by omega),nb w hn 513 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 513 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have cfr := cfCompare w g hn s.basis false k X hk hx cc ((h8 _ m513).trans hcin) gs g514 s m
    ⟨src0,h5,fun _ _ _ => rfl⟩
  obtain ⟨tp,c1',c2',c3'⟩ := cfr
  refine ⟨tp,?_⟩
  simp only [Bool.false_xor] at c2'
  have gv : s.basis g=b0 g := h8 g gm
  rw [gv] at c2'
  have same : ∀q,q∉srcR w → q≠w 514 → (run (comparePart w g k) m s).basis q=s.basis q := c3'
  have srcm : ∀q∈srcR w,q∈mutL w := fun q hq => hR_mut w hn q (blk_sub w 0 256 0 258 (by omega) (by omega) q hq)
  have m514 : w 514∈mutL w := by simp [mutL]
  refine ⟨?_,?_,?_,?_,c2',?_,?_,?_⟩
  · rw [hR_src w hn,c1',regValue_congr _ _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 256 2 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 256 2 (by omega) (by omega) (by omega) (e ▸ hq))),top0]; simp
  · rw [regValue_congr (kR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 770 258 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 770 258 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h2
  · rw [regValue_congr (tR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 1029 256 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 1029 256 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h3
  · rw [same _ (nb w hn 1028 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h4
  · rw [same _ (nb w hn 721 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h6
  · rw [same _ (nb w hn 722 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h7
  · intro q hq
    rw [same q (fun h' => hq (srcm q h')) (fun e => hq (e ▸ m514))]; exact h8 q hq

theorem stepMeasFp (b0 : BasisState) (H X T : Nat) (par f gp : Bool) :
    Triple (MF w b0 H X T par f gp (f && par)) [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]
      (MF w b0 H X T par f gp false) := by
  intro s m h
  rw [run_meas_and (w 722) (w 514) (w 1028) m s (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.1])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp (f && par) s ⟨s.phase,writeBit s.basis (w 722) false⟩ 722
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepMeasGp (b0 : BasisState) (H X T : Nat) (par f fp : Bool) (gm : g∉mutL w)
    (g515 : g≠w 721) :
    Triple (MF w b0 H X T par f (b0 g && par) fp) [.measureX (w 721) [] [.CZ g (w 1028)]]
      (MF w b0 H X T par f false fp) := by
  intro s m h
  rw [run_meas_and (w 721) g (w 1028) m s g515
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2 g gm])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f (b0 g && par) fp s ⟨s.phase,writeBit s.basis (w 721) false⟩ 721
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepCopy (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 0 X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have e0 : regValue (hpR w) s.basis=0 := by omega
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    rw [e0,b0',Nat.zero_xor]
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [this]; simp

end Rest


section Rest2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem aC_out : ∀q∈aC w,q∉mutL w := by
  intro q hq hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
  · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
  all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm

theorem w1797_out : w 1797∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
    nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
    exact w_ne w hn _ _ (by omega) (by omega) (by omega)

theorem stepHAdd (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddM w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  rw [hAddM]
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBits w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBits_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (dBits w) (hpR w) (hC2 w) (w 1797) nd srcw
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length]) s m cl
  refine ⟨hp,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)) m s).basis
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=Y := by rw [b0'] at sp; simp at sp; omega
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,dBits_value,e0,
      h.2.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin]
    simp [hpR,wireBlock_length]

theorem stepHAddT (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddT w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  rw [hAddT_run w (w_ne w hn 1797 1540 (by omega) (by omega) (by omega)) m s c17]
  exact stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s m h

theorem stepW0 (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,b0',h.2.2.2.1]
    rw [b0'] at sp
    simp [writeBit] at sp ⊢
    omega

theorem stepErase (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : H<2^257) (hf : f=decide (H/2<T)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC3 w)).Nodup := by
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H/2 := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      cases hb : s.basis (w 0) <;> simp [hb] at sp <;> omega
    cases hb : s.basis (w 0) <;> simp [hb] at sp <;> simp only [hp8] at * <;> omega
  have r := eraseLtChain_correct (hp8 w) (tR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hpv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

end Rest2


section Compose
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem g_mut (hg : g∉skywalkPoolWires w) : g∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨g_out w hn g hg 0 258 (by omega),g_out w hn g hg 770 258 (by omega)⟩,g_out w hn g hg 1029 256 (by omega)⟩,
    g_ne w hn g hg 1028 (by omega),g_ne w hn g hg 514 (by omega),g_ne w hn g hg 721 (by omega),g_ne w hn g hg 722 (by omega)⟩

theorem low_bit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState)
    (h : MF w b0 H X T par f gp fp s) : s (w 770)=decide (X%2=1) := by
  have sp := kR_split w hn s
  rw [h.2.1] at sp
  cases hb : s (w 770) <;> simp [hb] at sp ⊢ <;> omega

omit hn in
theorem xor_clear (a b c : Bool) : (((a ^^ (((false ^^ a) ^^ b) ^^ c)) ^^ b) ^^ c)=false := by
  cases a <;> cases b <;> cases c <;> rfl
omit hn in
theorem xor_clear2 (a c : Bool) : ((a ^^ ((false ^^ a) ^^ c)) ^^ c)=false := by
  cases a <;> cases c <;> rfl

theorem stepPar (b0 : BasisState) (k X : Nat) (f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 X 0 false f false false) (parGates w g k)
      (MF w b0 0 (2*(X/2)) 0 (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f) f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have xs : X=2*(X/2)+(decide (X%2=1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;> simp [hx] <;> omega
  apply Triple.conseq (fun s h => by rw [xs] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parGates,if_pos hk,if_pos hk]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 _ _ f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear] at h
    simpa [hk] using h
  · rw [parGates,if_neg hk,if_neg hk]
    try simp only [List.nil_append]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear2] at h
    simpa [hk] using h

theorem stepRot (b0 : BasisState) (X : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 (2*(X/2)) 0 par f gp fp) (rotateRight (kR w)) (MF w b0 0 (X/2) 0 par f gp fp) := by
  intro s m h
  have r := rotateRight_spec (kR w) (kR_nd w hn) (2*(X/2)) (by omega) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 0 _ 0 par f gp fp s _ h fr.2.1 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  rw [this]; omega

end Compose


/-- Complement the entire 258-bit K bank after shifting the original input. -/
theorem stepNotK (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 H X T par f gp fp) (notRegister (kR w))
      (MF w b0 H (2^258-1-X) T par f gp fp) := by
  intro s m hs
  rw [notRegister_correct (kR w) (kR_nd w hn)]
  refine ⟨rfl,?_⟩
  apply stepK w hn b0 H X T par f gp fp s _ hs
  · intro q hq
    change (if q∈kR w then !s.basis q else s.basis q)=s.basis q
    simp only [if_neg hq]
  · change regValue (kR w) (fun q => if q∈kR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (kR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,hs.2.1]
    simp [kR,wireBlock_length]

theorem kC_lt (par : Bool) : kConstant false par<2^258 := by
  cases par <;> norm_num [kConstant,ECDSAAdd.p]

theorem tk_lt (k : Nat) (G f par : Bool) : tk k G f par<2^258 := by
  unfold tk
  split_ifs <;> first | exact Nat.mod_lt _ (by norm_num) | norm_num

theorem xlt (a b : Nat) (ha : a<2^258) (hb : b<2^258) : a^^^b<2^258 := Nat.xor_lt_two_pow ha hb

theorem c1_lt (k : Nat) : c1 k<2^258 := tk_lt k _ _ _
theorem cg_lt (k : Nat) : cg k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cf_lt (k : Nat) : cf k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cp_lt (k : Nat) : cp k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cgp_lt (k : Nat) : cgp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)
theorem cfp_lt (k : Nat) : cfp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)

def lkv (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1 k ^^^ (if G then cg k else 0) ^^^ (if f then cf k else 0) ^^^ (if par then cp k else 0) ^^^
    (if gp then cgp k else 0) ^^^ (if fp then cfp k else 0)

theorem lkv_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkv k G f par (G && par) (f && par)=tk k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkv,c1,cg,cf,cp,cgp,cfp,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltv (k : Nat) (G gp : Bool) : Nat := (if G then thrA k else 0) ^^^ (if gp then thrB k else 0)

theorem ltv_eq (k : Nat) (G par : Bool) : ltv k G (G && par)=thr k G par := by
  cases G <;> cases par <;> simp [ltv,thr,thrA,thrB,Nat.xor_assoc,Nat.xor_self]

section Compose2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepLoadK (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadK w g k)
      (MF w b0 (H^^^lkv k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1 k) (c1_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cg k) (cg_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cf k) (cf_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cp k) (cp_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgp k) (cgp_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfp k) (cfp_lt k))))))
  unfold loadK
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1 k^^^(if b0 g then cg k else 0)^^^(if f then cf k else 0)^^^(if par then cp k else 0)^^^
      (if gp then cgp k else 0)^^^(if fp then cfp k else 0)=H^^^lkv k (b0 g) f par gp fp := by
    simp only [lkv,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadT (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadT w g k)
      (MF w b0 H X (T^^^ltv k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrA k<2^256 := by unfold thrA; omega
  have lb : thrB k<2^256 := Nat.xor_lt_two_pow la (by rw [p_val]; omega)
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrB k) lb)
  unfold loadT
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltv,Nat.xor_assoc] using h

end Compose2


section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (X<(if G then k else 0))
    let dx := (p-1-X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=x0 k G f par at a1
  change (2^258-1-X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=x0 k G f par := a1
    rw [e]; unfold x0 ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (X<(if b0 g then k else 0))=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by rw [p_val] at hk; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s3n := stepNotK w hn b0 0 (X/2) 0 par f false false
  have s4a := stepCCX w hn b0 0 (2^258-1-X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (2^258-1-X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (2^258-1-X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have s6 := stepKAdd w hn b0 (tk k G f par) (2^258-1-X/2) 0 par f (G && par) (f && par) hac h1797
  rw [show (tk k G f par+(2^258-1-X/2))%2^258=K by rw [Nat.add_comm]; exact a2] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by norm_num)) hac h1797
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;> simp [hC_val] <;> omega
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp <;> omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq ((s3.seq s3n).seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main


section Final
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- The reflected-input merged circuit leaves exactly the direct-first-tick state for
`(p-1-X+g*k) mod p`, on every measurement record. -/
theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(p-1-X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (p-1-X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
  generalize hpar : decide (dx%2=1)=par at tri a1 a2 a3 a4 a5
  generalize hK : (dx/2+kConstant false par)%2^258=K at tri a1 a2 a3 a4 a5
  generalize hH : (K%2^257+delta par)%2^257=H at tri a1 a2 a3 a4 a5
  obtain ⟨lp,l1,l2,l3,l4,l5,l6,l7,l8⟩ := tri
  have dxlt : dx<p := by rw [←hdx]; exact Nat.mod_lt _ (by rw [p_val]; norm_num)
  have kh : ∀q∈hR w,q∉kR w := kR_hR w hn
  have kt : ∀q∈tR w,q∉kR w := kR_tR w hn
  have hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 dx u.basis := by
    constructor
    · change regValue (wireBlock w 0 258) u.basis=0
      rw [show wireBlock w 0 258=hR w from rfl,regValue_congr _ _ t.basis (fun q hq => hu2 q (kh q hq)),th0]
    · change regValue (wireBlock w 770 258) u.basis=dx
      exact hu3
    · change regValue (wireBlock w 1540 257) u.basis=0
      apply (regValue_zero _ _).mpr
      intro q hq
      rw [hu2 q (fun h' => List.disjoint_left.mp (blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)) h' hq)]
      exact hac q hq
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
    · change u.basis (w 1028)=false
      rw [hu2 _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact t1028
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn dx dxlt u m' hin
  have e770 : u.basis (w 770)=par := by
    have sp := kR_split w hn u.basis
    rw [hu3] at sp
    rw [←hpar]
    cases hb : u.basis (w 770) <;> simp [hb] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  rw [hK] at zk
  have hv : 2*(dx/2+(if par then hConstant else 0))+(!par).toNat=2*H+(!par).toNat := by rw [a3]
  rw [hv] at zh
  apply State.extensionality
  · rw [lp,zp,hu]
  · funext q
    by_cases qh : q∈hR w
    · exact (regValue_eq_iff (hR w) _ _).mp (l1.trans zh.symm) q qh
    by_cases qk : q∈kR w
    · exact (regValue_eq_iff (kR w) _ _).mp (l2.trans zk.symm) q qk
    by_cases q1 : q=w 1028
    · rw [q1,l4,z1028]
    have nmut : q∉NativeFirstDirect.mutable w := by
      simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
      exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),qk⟩,q1⟩
    rw [zrest q nmut,hu2 q qk]
    by_cases qt : q∈tR w
    · rw [(regValue_zero _ _).mp l3 q qt,(regValue_zero _ _).mp tt0 q qt]
    by_cases q4 : q=w 514
    · rw [q4,l5,t514]
    by_cases q5 : q=w 721
    · rw [q5,l6,t515]
    by_cases q6 : q=w 722
    · rw [q6,l7,t516]
    apply l8
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,qk⟩,qt⟩,q1,q4,q5,q6⟩

end Final


/-! ### Resources -/

def mSites (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 515++wireBlock w 770 515++wireBlock w 1540 258++[w 721,w 722,g]

theorem in_mSites (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) : w i∈mSites w g := by
  simp only [mSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hi with h|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩))
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))

theorem blk_mSites (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 515 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀q∈wireBlock w a n,q∈mSites w g := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_mSites w g i (by omega)

theorem g_mSites (w : Nat → Wire) (g : Wire) : g∈mSites w g := by simp [mSites]

theorem dBits_wires_sub (w : Nat → Wire) : ∀q∈mappedWires (dBits w),q=w 1028 := dBits_wire w

theorem lsub (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀q∈l,q∈mSites w g) :
    l.toFinset⊆(mSites w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀q∈i.wires,q∈mSites w g) :
    wires [i]⊆(mSites w g).toFinset := by
  intro q hq
  simp only [wires,Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

theorem merged_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (xR w) (srcR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,srcR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 770 256 (by omega) q hq
    · exact B 0 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨mskS _,cmp⟩,mskS _⟩
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mSites w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hNot : wires (notRegister (kR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]
    exact lsub w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mSites w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mSites w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hK : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mSites w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mSites w g).toFinset := (hAddT_wires w).trans hH
  simp only [merged,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC,⟨hP,hR'⟩,hNot⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩


theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1025 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (kR w)
  have c1' := compareLt_counts none (xR w) (srcR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,srcR,xR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have h1 := mappedAdd_counts (dBits w) (hpR w) (hC2 w) (w 1797)
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pg : toffoliCount (parGates w g k)=0 ∧ measurementCount (parGates w g k)=0 := by
    unfold parGates; split_ifs <;> simp [toffoliCount,measurementCount]
  have lx : (srcR w).length=256 := by simp [srcR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=255 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,comparePart,prodPart,loadK,kAddM,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,k1.1,k1.2,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_physical (k : Nat) : GatePhysical (merged w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have mp (c : Wire) (c' : Wire) : GatePhysical [.measureX c [] [.CZ c' c]] ∧
      GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by
    simp [GatePhysical,PhysicalInstr]
  have gS : g∉srcR w := g_out w hn g hg 0 256 (by omega)
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 770 256 0 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (xR w++srcR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 770 256 (by omega),src_nd w hn,a1⟩
      have l2 : (xR w++srcR w++cR w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 770 256 (by omega) (by omega) (by omega),
          nb w hn 514 0 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 770 256 (by omega) (by omega) (by omega),nb w hn 513 0 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
  have kP : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have hP : GatePhysical (hAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBits w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBits_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have eP : GatePhysical (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parGates w g k) := by
    unfold parGates
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).1
  have prodP : GatePhysical (prodPart w g) := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,gatePhysical_append]
    exact ⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h1286 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h1287 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t1286 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadK w g k) := by
    simp only [loadK,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h1286⟩,maskedConstant_physical _ _ _ h1287⟩
  have ltP : GatePhysical (loadT w g k) := by
    simp only [loadT,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t1286⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have cP : GatePhysical (comparePart w g k) := by
    simp only [comparePart,gatePhysical_append]
    exact ⟨⟨maskedConstant_physical _ _ _ gS,cmpP⟩,maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hP
  simp only [merged,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cP,⟨parP,rotP⟩,notRegister_physical _⟩,prodP⟩,lkP⟩,kP⟩,lkP⟩,m1⟩,cpP⟩,hPT⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩

end Phys

theorem gs1 (i : Instr) : Challenge.gateSlots [i]=Challenge.instructionSlots i := by
  simp [Challenge.gateSlots]

theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (xR w) (srcR w) (cR w) (w 513) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).1
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.mappedAdd_gateSlots_le (dBits w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
  have pg : Challenge.gateSlots (parGates w g k)≤6 := by
    unfold parGates; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have pr : Challenge.gateSlots (prodPart w g)=2 := by simp [prodPart,Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q2 : Challenge.gateSlots [.measureX (w 721) [] [.CZ g (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadK w g k)≤6*258 := by
    simp only [loadK,Challenge.gateSlots_append]
    have := x1 (hR w) (c1 k); have := m1 g (hR w) (cg k); have := m1 (w 514) (hR w) (cf k)
    have := m1 (w 1028) (hR w) (cp k); have := m1 (w 721) (hR w) (cgp k); have := m1 (w 722) (hR w) (cfp k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadT w g k)≤2*256 := by
    simp only [loadT,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrA k); have := m1 (w 721) (tR w) (thrB k)
    simp only [tR,wireBlock_length] at *
    omega
  have cP : Challenge.gateSlots (comparePart w g k)≤2*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) k
    simp only [srcR,xR,wireBlock_length] at *
    omega
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  rw [dBits_length] at h1
  rw [lh] at e1
  have nk : Challenge.gateSlots (notRegister (kR w))=258 := by
    simp [Baselines.notRegister_gateSlots,kR,wireBlock_length]
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,Challenge.gateSlots_append,pr,w0,q1,q2,cp,kAddM,nk]
  omega

end ECDSAAdd.Entrant.E1Reflected

end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1ReflectedPlacement =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1QubitPlacement
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1Reflected

/-! Full all-record physical transfer for the reflected-input merged entry.
Research source, NOT elaborated here. The r-state relation is the internal
boundary supplied by the removed square output reflection, not a new external
point-addition premise. All clean scratch values are derived from dialogPool0.
-/
namespace ECDSAAdd.Entrant.E1ReflectedPlacement
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement

def entryR (L : ControlledPointLayout) (k : Fp) : Program :=
  renameProgram (pmapR L) (E1Reflected.merged base (base 2400) k.val)

theorem mergedR_S (k : Nat) : wires (E1Reflected.merged base (base 2400) k)⊆S :=
  E1Reflected.merged_support base (base 2400) k

section Entry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryR_eq (k : Fp) (s r : State) (X : Nat) (hX : X<p) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hg : s.basis L.core.generic=G)
    (hc : regValue L.dialogPool s.basis=0)
    (rphase : r.phase=s.phase)
    (rx : regValue L.point.x r.basis=p-1-X)
    (rout : ∀q,q∉L.point.x → r.basis q=s.basis q) (m1 m2 : List Bool) :
    run (entryR L k) m1 s=run (fastConstAdd L L.point.x k++E1QubitPlacement.tickF L) m2 r := by
  have inj := pmap_inj L hw hn
  have pool := pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := pmapR L
  let t : State := pullState F s
  have clean (q : Wire) (hq : q∈S) (h1 : q∉wireBlock base 770 256) (h2 : q≠base 2400) :
      t.basis q=false := hzero _ (pool q hq h1 h2)
  have inS (i : Nat) (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      base i∈S := List.mem_toFinset.mpr (E1Reflected.in_mSites base (base 2400) i hi)
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
  have tk0 : regValue (E1Reflected.kR base) t.basis=X := by
    rw [E1Reflected.kR_x base base_pool_nodup,show E1Reflected.xR base=wireBlock base 770 256 from rfl,xval,
      blkz 1026 2 (by omega)]
    simp
  have tg : t.basis (base 2400)=G := by
    change s.basis (pmapR L (base 2400))=G
    rw [pmap_g L hw hn,hg]
  -- The reflected comparison state differs only on x; no new scratch premise.
  have gx : L.core.generic∉L.point.x := ((E1QubitPlacement.lay L hw hn _).2.2 rfl).1
  have px (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    ((E1QubitPlacement.lay L hw hn q).2.1 hq).1
  have rg : r.basis L.core.generic=G := (rout _ gx).trans hg
  have rc : regValue L.dialogPool r.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => rout q (px q hq)),hc]
  have xrlt : p-1-X<p := by
    rw [E1Reflected.p_val] at hX ⊢
    omega
  have fca := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k (p-1-X) G xrlt r
    (m2.take (measurementCount (fastConstAdd L L.point.x k))) rg rx rc
  generalize hs1 : run (fastConstAdd L L.point.x k) (m2.take (measurementCount (fastConstAdd L L.point.x k))) r=s1 at fca
  obtain ⟨p1r,x1,o1r⟩ := fca
  have p1 : s1.phase=s.phase := p1r.trans rphase
  have o1 (q : Wire) (hq : q∉L.point.x) : s1.basis q=s.basis q := (o1r q hq).trans (rout q hq)
  let u : State := ⟨t.phase,fun q => if q∈E1Reflected.kR base then s1.basis (F q) else t.basis q⟩
  have hu2 : ∀q,q∉E1Reflected.kR base → u.basis q=t.basis q := by
    intro q hq; simp [u,hq]
  have xS : ∀q∈L.point.x,∃a∈S,F a=q ∧ a∈wireBlock base 770 256 := by
    intro q hq
    rw [←pmap_x L hw hn] at hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    refine ⟨a,?_,rfl,ha⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact inS i (by omega)
  have hu3 : regValue (E1Reflected.kR base) u.basis=(p-1-X+(if t.basis (base 2400) then k.val else 0))%p := by
    rw [tg,E1Reflected.kR_x base base_pool_nodup]
    have e1 : regValue (E1Reflected.xR base) u.basis=regValue L.point.x s1.basis := by
      rw [←pmap_x L hw hn,←regValue_pull]
      apply regValue_congr
      intro q hq
      have : q∈E1Reflected.kR base := E1Reflected.blk_sub base 770 256 770 258 (by omega) (by omega) q hq
      simp only [u,this,if_true]
      rfl
    have e2 : regValue (wireBlock base 1026 2) u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      have kq : base i∈E1Reflected.kR base := E1Reflected.blk_sub base 1026 2 770 258 (by omega) (by omega) _ hq
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
  have eqL := E1Reflected.merged_eq_forward base (base 2400) base_pool_nodup g2400 k.val k.isLt X hX t u m1
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) tk0 (blkz 0 258 (by omega))
    (blkz 1029 256 (by omega)) (cl 1028 (by omega)) (cl 514 (by omega)) (cl 721 (by omega)) (cl 722 (by omega))
    (fun i h1 h2 => cl i (by omega)) (cl 513 (by omega))
    (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact cl i (by omega)) (cl 1797 (by omega)) rfl hu2 hu3
  -- transport both sides
  have hS : ∀q∈S,t.basis q=s.basis (F q) := fun q _ => rfl
  have newSide := run_rename_pool F S inj _ (mergedR_S k.val) m1 t s rfl hS
  have uS : ∀q∈S,u.basis q=s1.basis (F q) := by
    intro q hq
    by_cases kq : q∈E1Reflected.kR base
    · simp [u,kq]
    · simp only [u,kq,if_false]
      change s.basis (F q)=s1.basis (F q)
      have outx : F q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha q hq ea
        subst this
        exact kq (E1Reflected.blk_sub base 770 256 770 258 (by omega) (by omega) _ ax)
      rw [o1 _ outx]
  have oldSide := run_rename_pool F S inj _ forward_S
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) u s1 (by simp [u,t,pullState,p1]) uS
  have rhs : run (fastConstAdd L L.point.x k++E1QubitPlacement.tickF L) m2 r=
      run (E1QubitPlacement.tickF L) (m2.drop (measurementCount (fastConstAdd L L.point.x k))) s1 := by
    rw [run_append,hs1]
  rw [rhs]
  apply State.extensionality
  · rw [entryR,newSide.1,eqL,E1QubitPlacement.tickF,oldSide.1]
  · funext q
    by_cases im : q∈S.image F
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp im
      rw [entryR,newSide.2 a ha,eqL,E1QubitPlacement.tickF,oldSide.2 a ha]
    · rw [entryR,run_rename_pool_outside F S _ (mergedR_S k.val) m1 s q im,E1QubitPlacement.tickF,
        run_rename_pool_outside F S _ forward_S _ s1 q im]
      have outx : q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,_⟩ := xS _ hm
        exact im (Finset.mem_image.mpr ⟨a,ha,ea⟩)
      rw [o1 q outx]

end Entry

open Challenge
attribute [local irreducible] wires

theorem entryR_counts (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (entryR L k)=1025 ∧ measurementCount (entryR L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1Reflected.merged base (base 2400) k.val)
  have c := E1Reflected.merged_counts base (base 2400) k.val
  rw [entryR,r.1,r.2]; exact c

theorem entryR_slots (L : ControlledPointLayout) (k : Fp) : gateSlots (entryR L k)≤25000 := by
  simpa only [entryR,Baselines.rename_gateSlots] using
    E1Reflected.merged_slots base (base 2400) k.val

theorem entryR_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (entryR L k) := by
  rw [entryR]
  exact gatePhysical_rename_support (pmapR L) (E1Reflected.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (mergedR_S k.val ha) b (mergedR_S k.val hb) e)
    (E1Reflected.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

theorem entryR_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryR L k)⊆(OB5Support.sites L).toFinset := by
  have hlog : wires (renameProgram sig (renameProgram rho
      (E1Reflected.merged base (base 2400) k.val)))⊆OB5Support.logicalSites := by
    intro q hq
    simp only [renameProgram_support,Finset.mem_image] at hq
    obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩ := hq
    obtain ⟨j,rfl,hj⟩ := S_cases b (mergedR_S k.val hb)
    rw [rho_base,sig_base]
    exact sw_logical _ (rhoN_range j hj)
  have h := OB5Support.placed_support_logical L hw _ hlog
  simpa only [entryR,renameProgram_comp,pmapR,pmap,Function.comp_def] using h

/-- Both the ordinary and reflected E1 programs have the same support envelope. -/
theorem logicalR_omits (k i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (renameProgram sig (renameProgram rho
      (E1Reflected.merged base (base 2400) k))) := by
  intro h
  simp only [renameProgram_support,Finset.mem_image] at h
  obtain ⟨a,⟨b,hb,rfl⟩,eq⟩ := h
  obtain ⟨j,rfl,hj⟩ := S_cases b (mergedR_S k hb)
  rw [rho_base,sig_base] at eq
  have e := base_injective eq
  exact sw_avoid j hj (e.symm ▸ hi)

end ECDSAAdd.Entrant.E1ReflectedPlacement
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Entry =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588BFFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Square
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1ReflectedPlacement

/-! Both merged entries retain the complete rolling inverse phases. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires

def tailP (a : Bool) : Program := Rolling1588.stackForward a++skywalkArithmeticClear base

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (tailP true)++
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (tailP false)++
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))

def entryStage (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky++E1QubitPlacement.entryM L kx++restE L

def squareEntry (L : ControlledPointLayout) (k : Fp) : Program :=
  ReflectionE1Square.program L++E1ReflectedPlacement.entryR L k

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  squareEntry L k++restX L++exitY L cy

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry Rolling1588.entryKernel L=E1QubitPlacement.tickF L++restE L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,Rolling1588.entryKernel,Rolling1588.firstPhase,restE,tailP,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit Rolling1588.exitKernel L=E1QubitPlacement.tickF L++restX L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,Rolling1588.exitKernel,Rolling1588.firstPhase,restX,tailP,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryStage_step (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStage L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  have add:=fastStep_addX L hw hn X Y G origin kx
  have divide:=division_step Rolling1588.entryKernel Rolling1588.entryKernel_support
    Rolling1588.entry_correct L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior:=add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky++E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx++fusedY L ky++E1QubitPlacement.tickF L)
    (R:=restE L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryStage,division,entry_split,List.append_assoc] using prior

/-- The deleted reflection and changed entry use independent record lists.
The equality ends before the common suffix, so no suffix tape equality is assumed. -/
theorem squareEntry_eq (k : Fp) (X Y : Fp) (G : Bool) (origin : BasisState)
    (s : State) (m1 m2 : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) m1 s=
      run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++
        E1QubitPlacement.tickF L) m2 s := by
  let n1:=measurementCount (ReflectionE1Square.program L)
  let n2:=measurementCount (SquareCarryLoan719BF.program L)
  obtain ⟨a,ha⟩ : ∃a : State,run (ReflectionE1Square.program L) (m1.take n1) s=a := ⟨_,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : State,run (SquareCarryLoan719BF.program L) (m2.take n2) s=r := ⟨_,rfl⟩
  have fresh:=ReflectionE1Square.boundary L hw hn X Y G origin s (m1.take n1) v
  have prior:=SquareCarryLoan719BF.step L hw hn X Y G origin s (m2.take n2) v
  rw [ha] at fresh
  rw [hr] at prior
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  let R:=p-1-Z.val
  have ppos : 0<p := by norm_num [p]
  have rp : R<p := by
    change p-1-Z.val<p
    omega
  have ax : regValue L.point.x a.basis=R:=fresh.2.1
  have ag : a.basis L.core.generic=G :=
    (fresh.2.2 _ (((E1QubitPlacement.lay L hw hn _).2.2 rfl).1)).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ s.basis
      (fun q hq=>fresh.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).1)),v.clean]
  have involution (n : Nat) (bound : n<p) : n=p-1-(p-1-n) := by omega
  have rx : regValue L.point.x r.basis=p-1-R := by
    have value : regValue L.point.x r.basis=Z.val:=prior.2.x
    exact value.trans (involution Z.val Z.isLt)
  have outside (q : Wire) (hq : q∉L.point.x) : r.basis q=a.basis q := by
    have oldFrame : r.basis q=s.basis q := by
      by_cases hy : q∈L.point.y
      · exact (regValue_eq_iff _ _ _).mp (prior.2.y.trans v.y.symm) q hy
      · have away : q∉L.point.x++L.point.y:=by simp only [List.mem_append,not_or];exact ⟨hq,hy⟩
        exact (prior.2.rest q away).trans (v.rest q away).symm
    exact oldFrame.trans (fresh.2.2 q hq).symm
  have eq:=E1ReflectedPlacement.entryR_eq L hw hn k a r R rp G ax ag ac
    (prior.1.trans fresh.1.symm) rx outside (m1.drop n1) (m2.drop n2)
  simpa only [squareEntry,run_append,n1,n2,ha,hr,List.append_assoc] using eq

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=fusedMultiply_step L hw hn (FrontierEntry1591Callers.exit Rolling1588.exitKernel L)
    (exit_correct Rolling1588.exitKernel Rolling1588.exitKernel_support Rolling1588.exit_correct L hw hn)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=restX L++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [secondStage,fusedMultiply,exit_split,List.append_assoc,Z] using prior

end Correct
end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Generic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Entry

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5
  EntryFuse EntryFuseFinite ExitFusionResearch
attribute [local irreducible] run wires

def correction (cx : Fp) : Fp := 3*cx-(SquareCarryLoan719BF.K:Nat)

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage L (-cx) (-cy)++secondStage L (correction cx) cy++fastConstNeg L cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold correction
    ring
  have second:=secondStage_step L hw hn (X-cx) a (correction cx) cy true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  have finish:=fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at finish
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at finish
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at second finish
  exact (first.seq second).seq finish

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStage_step L hw hn X (Y/X) (correction cx) cy false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have finish:=fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second finish
  rw [back] at second
  exact (first.seq second).seq finish


theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Correct
end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Resources =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Generic

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] wires toffoliCount measurementCount gateSlots

abbrev baselineGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ControlLoan1589BFFinal.Offset.generic L (division Rolling1588.entryKernel L)
    (SquareCarryLoan719BF.program L) (FrontierEntry1591Callers.exit Rolling1588.exitKernel L) cx cy

private theorem envelopes_of_shapes (A0 Y T E S R A1 X EY N M RF New Old : Program)
    (newShape : New=(Y++M++E)++(S++RF++X++EY)++N)
    (oldShape : Old=A0++(Y++(T++E))++(S++R)++A1++(T++X)++EY++N) :
    New⊆Old++M++RF ∧ wires New⊆wires Old∪wires M∪wires RF := by
  rw [newShape,oldShape]
  constructor
  · intro i hi
    simp only [List.mem_append] at hi ⊢
    tauto
  · intro q hq
    simp only [wires_append,Finset.mem_union] at hq ⊢
    tauto

private theorem envelopes (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy⊆baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx) ∧
    wires (generic L cx cy)⊆wires (baselineGeneric L cx cy)∪
      wires (E1QubitPlacement.entryM L (-cx))∪
        wires (E1ReflectedPlacement.entryR L (correction cx)) := by
  apply envelopes_of_shapes
    (fastConstAdd L L.point.x (-cx)) (fusedY L (-cy)) (E1QubitPlacement.tickF L)
    (restE L) (ReflectionE1Square.program L) (ReflectionE1Square.reflectedTail L)
    (fastConstAdd L L.point.x (3*cx-(ControlLoan1589BFFinal.Offset.K:Nat)))
    (restX L) (exitY L cy) (fastConstNeg L cx) (E1QubitPlacement.entryM L (-cx))
    (E1ReflectedPlacement.entryR L (correction cx))
  · rfl
  · simp only [baselineGeneric,ControlLoan1589BFFinal.Offset.generic,division,
      entry_split,exit_split,ReflectionE1Square.program_split]

theorem instructions_subset (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy⊆baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx) :=
  (envelopes L cx cy).1

theorem support_envelope (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (baselineGeneric L cx cy)∪
      wires (E1QubitPlacement.entryM L (-cx))∪
        wires (E1ReflectedPlacement.entryR L (correction cx)) :=
  (envelopes L cx cy).2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (support_envelope L cx cy).trans (Finset.union_subset
    (Finset.union_subset (Rolling1588BFFinal.generic_support L hw hn cx cy)
      (E1QubitPlacement.entryM_sites L hw (-cx)))
    (E1ReflectedPlacement.entryR_sites L hw (correction cx)))

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old:=ControlLoan1589BFFinal.Offset.generic_physical L hw hn
    (division Rolling1588.entryKernel L) (SquareCarryLoan719BF.program L)
    (FrontierEntry1591Callers.exit Rolling1588.exitKernel L)
    (division_physical Rolling1588.entryKernel Rolling1588.entryKernel_support
      Rolling1588.entryKernel_physical L hw hn)
    (SquareCarryLoan719BF.physical L hw hn)
    (placed_physical Rolling1588.exitKernel Rolling1588.exitKernel_support
      Rolling1588.exitKernel_physical L hw hn) cx cy
  have full : GatePhysical (baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx)) := by
    rw [gatePhysical_append,gatePhysical_append]
    exact ⟨⟨old,E1QubitPlacement.entryM_physical L hw hn (-cx)⟩,
      E1ReflectedPlacement.entryR_physical L hw hn (correction cx)⟩
  intro i hi
  exact full i (instructions_subset L cx cy hi)

private def logicalTarget (i : Nat) : Nat :=
  if i=1800 then 2312 else if i=770 then 1026 else if i=1285 then 1541 else
    if i=1286 then 1542 else if i=769 then 1797 else i

private theorem target_facts (L : ControlledPointLayout) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    wireFn2 L (base (logicalTarget i))=L.core.poolWire i ∧
    base (logicalTarget i)∈OB5Support.logicalSites ∧
    logicalTarget i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨rfl,?_,by decide⟩
  all_goals
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    simp only [logicalTarget,OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    norm_num

private theorem placed_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (support : wires P⊆OB5Support.logicalSites) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719])
    (free : base (logicalTarget i)∉wires P) :
    L.core.poolWire i∉wires (renameProgram (wireFn2 L) P) := by
  obtain ⟨map,logical,_⟩:=target_facts L i hi
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩:=Finset.mem_image.mp used
  have same : wireFn2 L q=wireFn2 L (base (logicalTarget i)):=eq.trans map.symm
  have back:=(placement2 L hw hn).injectiveOnSlots q
    (ArithmeticOB5.logical_sub_old (support hq)) (base (logicalTarget i))
    (ArithmeticOB5.logical_sub_old logical) same
  exact free (back ▸ hq)

private theorem entry_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (E1QubitPlacement.entryM L k) := by
  rw [E1QubitPlacement.entryM_eq]
  exact placed_free L hw hn _ (E1QubitPlacement.logicalM k.val) i hi
    (E1QubitPlacement.merged_omits k.val _ (target_facts L i hi).2.2)

private theorem reflected_logical (k : Nat) :
    wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k)))⊆OB5Support.logicalSites := by
  intro q hq
  simp only [renameProgram_support,Finset.mem_image] at hq
  obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩:=hq
  obtain ⟨j,rfl,hj⟩:=E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k hb)
  rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range j hj)

private theorem reflected_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (E1ReflectedPlacement.entryR L k) := by
  have h:=placed_free L hw hn _ (reflected_logical k.val) i hi
    (E1ReflectedPlacement.logicalR_omits k.val _ (target_facts L i hi).2.2)
  simpa only [E1ReflectedPlacement.entryR,renameProgram_comp,E1QubitPlacement.pmapR,
    E1QubitPlacement.pmap,Function.comp_def] using h

private theorem kernel_free (entrySide : Bool) (i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (if entrySide then Rolling1588.entryKernel else Rolling1588.exitKernel) := by
  by_cases a : i=768
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_768_free
    · exact Rolling1588.entryKernel_768_free
  by_cases b : i=718
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_718_free
    · exact Rolling1588.entryKernel_718_free
  by_cases c : i=719
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_719_free
    · exact Rolling1588.entryKernel_719_free
  have old : i∈logicalOmissions := by
    simp only [logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  cases entrySide
  · exact Rolling1588.exitKernel_free i old
  · exact Rolling1588.entryKernel_free i old

theorem baseline_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (baselineGeneric L cx cy) := by
  have bounds : 515≤ i ∧ i<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega
  have en:=placed_free L hw hn _ Rolling1588.entryKernel_support i hi
    (kernel_free true _ (target_facts L i hi).2.2)
  have ex:=placed_free L hw hn _ Rolling1588.exitKernel_support i hi
    (kernel_free false _ (target_facts L i hi).2.2)
  have sq : L.core.poolWire i∉wires (SquareCarryLoan719BF.program L) := by
    by_cases h : i=719
    · subst i;exact SquareCarryLoan719BF.retired_free719 L hw hn
    · apply SquareCarryLoan719BF.square_free L hw hn i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;tauto
  apply ControlLoan1589BFFinal.Offset.generic_free L hw hn
    (division Rolling1588.entryKernel L) (SquareCarryLoan719BF.program L)
    (FrontierEntry1591Callers.exit Rolling1588.exitKernel L) i bounds _ sq ex cx cy
  intro k
  have constant:=ExitGenericQ5.constant_ports_avoid_large L hw hn i bounds L.point.y (Or.inr rfl)
  simp only [division,FrontierEntry1591Callers.entry,wires_append,Finset.mem_union,not_or]
  exact ⟨fun used=>constant (fusedY_support L hw k used),en⟩

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) := by
  intro used
  have member:=support_envelope L cx cy used
  simp only [Finset.mem_union] at member
  rcases member with (old|ordinary)|reflected
  · exact baseline_free L hw hn cx cy i hi old
  · exact entry_free L hw hn (-cx) i hi ordinary
  · exact reflected_free L hw hn (correction cx) i hi reflected

theorem generic_counts_delta (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (generic L cx cy)+753=toffoliCount (baselineGeneric L cx cy) ∧
    measurementCount (generic L cx cy)+751=measurementCount (baselineGeneric L cx cy) := by
  have first:=E1QubitPlacement.prefix_counts L hw (-cx)
  have second:=E1QubitPlacement.prefix_counts L hw (correction cx)
  have ordinary:=E1QubitPlacement.entryM_counts L (correction cx)
  have reflected:=E1ReflectedPlacement.entryR_counts L (correction cx)
  have square:=ReflectionE1Square.counts_delta L hw
  simp only [generic,entryStage,secondStage,squareEntry,baselineGeneric,
    ControlLoan1589BFFinal.Offset.generic,division,entry_split,exit_split,
    toffoliCount_append,measurementCount_append,correction,SquareCarryLoan719BF.K,
    ControlLoan1589BFFinal.Offset.K,ControlLoan1589BFSquare.K] at first second ordinary reflected square ⊢
  constructor <;> omega

theorem generic_slots_delta (L : ControlledPointLayout) (cx cy : Fp) :
    gateSlots (generic L cx cy)≤ gateSlots (baselineGeneric L cx cy)+50000 := by
  have first:=E1QubitPlacement.entryM_slots L (-cx)
  have second:=E1ReflectedPlacement.entryR_slots L (correction cx)
  simp only [generic,entryStage,secondStage,squareEntry,baselineGeneric,
    ControlLoan1589BFFinal.Offset.generic,division,entry_split,exit_split,
    ReflectionE1Square.program_split,gateSlots_append]
  omega

private theorem baseline_gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    Rolling1588BFFinal.gen L cx cy=GenericQ5Geometry.wrapG L (baselineGeneric L cx cy) := by
  simp only [Rolling1588BFFinal.gen,ControlLoan1589BFFinal.Offset.gen_shape,baselineGeneric]

private theorem wrap_counts_delta (L : ControlledPointLayout) (A B : Program)
    (h : toffoliCount A+753=toffoliCount B ∧ measurementCount A+751=measurementCount B) :
    toffoliCount (GenericQ5Geometry.wrapG L A)+753=toffoliCount (GenericQ5Geometry.wrapG L B) ∧
    measurementCount (GenericQ5Geometry.wrapG L A)+751=measurementCount (GenericQ5Geometry.wrapG L B) := by
  simp only [GenericQ5Geometry.wrapG,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem gen_counts_delta (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+753=toffoliCount (Rolling1588BFFinal.gen L cx cy) ∧
    measurementCount (gen L cx cy)+751=measurementCount (Rolling1588BFFinal.gen L cx cy) := by
  rw [gen_shape,baseline_gen_shape]
  exact wrap_counts_delta L _ _ (generic_counts_delta L hw cx cy)

theorem gen_slots_delta (L : ControlledPointLayout) (cx cy : Fp) :
    gateSlots (gen L cx cy)≤ gateSlots (Rolling1588BFFinal.gen L cx cy)+50000 := by
  have d:=generic_slots_delta L cx cy
  rw [gen_shape,baseline_gen_shape]
  simp only [GenericQ5Geometry.wrapG,gateSlots_append,rename_gateSlots]
  omega

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_counts_delta (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (A B : Program) (h : toffoliCount A+753=toffoliCount B ∧ measurementCount A+751=measurementCount B) :
    toffoliCount (Edges.wrapper L C cy A)+753=toffoliCount (Edges.wrapper L C cy B) ∧
    measurementCount (Edges.wrapper L C cy A)+751=measurementCount (Edges.wrapper L C cy B) := by
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2151696 := by
  have diff:=(wrapper_counts_delta layout (.some hc) cy _ _
    (gen_counts_delta layout layout_widths cx cy)).1
  have old:=Rolling1588BFFinal.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499214 := by
  have diff:=(wrapper_counts_delta layout (.some hc) cy _ _
    (gen_counts_delta layout layout_widths cx cy)).2
  have old:=Rolling1588BFFinal.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50189199+Rolling1588.slotGrowth := by
  have diff:=gen_slots_delta layout cx cy
  have old:=Rolling1588BFFinal.wrapper_slots C cx cy
  have lift : gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤
      gateSlots (Edges.wrapper layout C cy (Rolling1588BFFinal.gen layout cx cy))+50000 := by
    simp only [Edges.wrapper,Edges.finiteProgram,gateSlots_append,rename_gateSlots]
    omega
  omega

end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Final =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Resources

/-! Current Q1588 BF point with both E1 entries and one deleted reflection. -/
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151696,1499214,1588,50189199+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151696 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1499214 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50189199+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499214
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50189199+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- Selected checked E1+TickGap branch follows; merged entries, reflected square and inverse phases are preserved.

-- ===== ECDSAAdd.Submission.Entrant.TickGap1591Arithmetic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.OneFlag

/-! TickGap arithmetic from public frontier8764679c, MainPre.lean.
The copied proof bodies and circuit definitions are unchanged.
The new-codec forward and phase transports are separate modules. -/

section
-- ===== TickGapBudget =====
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TickGap

theorem scaled_budget (p x i : Nat) (hx : x  ≤  p) :
    ∃ j k : Nat, j+k=i  ∧
      (SkywalkNat.step^[i] (SkywalkNat.init x p)).u * 2^j  ≤  p  ∧
      (SkywalkNat.step^[i] (SkywalkNat.init x p)).v * 2^k  ≤  p := by
  induction i with
  | zero => exact ⟨0,0,rfl,by simpa [SkywalkNat.init] using hx,by simp [SkywalkNat.init]⟩
  | succ i ih =>
    obtain ⟨j,k,hjk,hu,hv⟩ := ih
    rw [Function.iterate_succ_apply']
    generalize SkywalkNat.step^[i] (SkywalkNat.init x p)=z at hu hv ⊢
    by_cases hz : z.u=0
    · refine ⟨j+1,k,by omega,?_,?_⟩
      · simp [SkywalkNat.step,hz]
      · simpa [SkywalkNat.step,hz] using hv
    · by_cases he : z.u%2=0
      · refine ⟨j+1,k,by omega,?_,?_⟩
        · simp only [SkywalkNat.step,if_neg hz,if_pos he,pow_succ]
          have hhalf : z.u/2*2 ≤ z.u := by omega
          nlinarith [Nat.mul_le_mul_right (2^j) hhalf]
        · simpa [SkywalkNat.step,hz,he] using hv
      · by_cases hle : z.v ≤ z.u
        · refine ⟨j+1,k,by omega,?_,?_⟩
          · simp only [SkywalkNat.step,if_neg hz,if_neg he,if_pos hle,pow_succ]
            have hhalf : (z.u-z.v)/2*2 ≤ z.u := by omega
            nlinarith [Nat.mul_le_mul_right (2^j) hhalf]
          · simpa [SkywalkNat.step,hz,he,hle] using hv
        · refine ⟨k+1,j,by omega,?_,?_⟩
          · simp only [SkywalkNat.step,if_neg hz,if_neg he,if_neg hle,pow_succ]
            have hhalf : (z.v-z.u)/2*2 ≤ z.v := by omega
            nlinarith [Nat.mul_le_mul_right (2^k) hhalf]
          · simpa [SkywalkNat.step,hz,he,hle] using hu

private theorem two_pow_sum (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2^a+2^b ≤ 2^(a+b-1) := by
  obtain ⟨c,rfl⟩ : ∃ c, a=c+2 := ⟨a-2,by omega⟩
  obtain ⟨d,rfl⟩ : ∃ d, b=d+2 := ⟨b-2,by omega⟩
  have he : c+2+(d+2)-1=c+d+3 := by omega
  rw [he, pow_add, pow_add, pow_add]
  norm_num
  rw [pow_add]
  have hc : 1 ≤ 2^c := Nat.one_le_two_pow
  have hd : 1 ≤ 2^d := Nat.one_le_two_pow
  nlinarith [Nat.mul_le_mul hc hd]

private theorem scaled_lt (u p j : Nat) (hp : p < 2^256) (hu : u*2^j ≤ p) (hj : j ≤ 256) :
    u < 2^(256-j) := by
  have he : 2^(256-j)*2^j=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
  by_contra h
  have hle := Nat.mul_le_mul_right (2^j) (Nat.le_of_not_gt h)
  omega

/-- A strict fixed-modulus sum cap across the late 32-stage band. -/
theorem strict_sum_band (x p i : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p)
    (cop : x.Coprime p) (hi : 256 ≤ i  ∧  i ≤ 287) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v < 2^(511-i) := by
  dsimp only
  obtain ⟨j,k,hjk,hu,hv⟩ := scaled_budget p x i (Nat.le_of_lt hx)
  have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  change z.u*2^j ≤ p at hu
  change z.v*2^k ≤ p at hv
  change 0 < z.v  ∧  z.v%2=1  ∧  z.u.gcd z.v=x.gcd p at valid
  change z.u+z.v < _
  by_cases hz : z.u=0
  · have hv1 : z.v=1 := by
      have hg := valid.2.2.trans cop
      rw [hz,Nat.gcd_zero_left] at hg
      exact hg
    have hi' : 1 ≤ 511-i := by omega
    have pow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) hi'
    simp only [pow_one] at pow
    omega
  have hu0 : 1 ≤ z.u := by omega
  have hv0 : 1 ≤ z.v := by omega
  have hj : j ≤ 255 := by
    by_contra h
    have hpw := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) (show 256 ≤ j by omega)
    nlinarith
  have hk : k ≤ 255 := by
    by_contra h
    have hpw := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) (show 256 ≤ k by omega)
    nlinarith
  have ju := scaled_lt z.u p j hp hu (by omega)
  have kv := scaled_lt z.v p k hp hv (by omega)
  by_cases hje : j=255
  · have ue : z.u=1 := by simp only [hje] at ju; norm_num at ju; omega
    have kk : k=i-255 := by omega
    have kp : k ≤ 32 := by omega
    have kp32 := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) kp
    have ep : 2^(256-k)*2^k=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
    have ek : 511-i=256-k := by omega
    rw [ue,ek]
    by_contra h
    have hbig : 2^(256-k) ≤ z.v+1 := by omega
    have mul := Nat.mul_le_mul_right (2^k) hbig
    nlinarith
  · by_cases hke : k=255
    · have ve : z.v=1 := by simp only [hke] at kv; norm_num at kv; omega
      have jj : j=i-255 := by omega
      have jp : j ≤ 32 := by omega
      have jp32 := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) jp
      have ep : 2^(256-j)*2^j=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
      have ek : 511-i=256-j := by omega
      rw [ve,ek]
      by_contra h
      have hbig : 2^(256-j) ≤ z.u+1 := by omega
      have mul := Nat.mul_le_mul_right (2^j) hbig
      nlinarith
    · have a : 2 ≤ 256-j := by omega
      have b : 2 ≤ 256-k := by omega
      have bound := two_pow_sum (256-j) (256-k) a b
      have e : (256-j)+(256-k)-1=511-i := by omega
      rw [e] at bound
      omega
end ECDSAAdd.Entrant.TickGap

end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def signedAddTop (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ TopCarry.addInPlaceTop x y carry q ++ signComplement q x

def Shape (n V : Nat) : Prop := V < 2^n ∨ 3*2^n ≤ V

theorem shape_complement (n V : Nat) (hv : V < 2^(n+2)) (h : Shape n V) :
    Shape n (2^(n+2)-1-V) := by
  have pow : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  unfold Shape at *
  omega

theorem shape_of_signed (n V : Nat) (hv : V < 2^(n+2))
    (lo : -((2^n:Nat):Int) ≤ signedDecode (n+2) V)
    (hi : signedDecode (n+2) V < ((2^n:Nat):Int)) : Shape n V := by
  have p2 : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1) = 2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold signedDecode at lo hi
  split_ifs at lo hi <;> unfold Shape <;> omega

theorem signedAddTop_eq (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (clean : ∀ w ∈ cs, s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Shape n (regValue y (run (signedAdd q x y cs) [] s).basis)) :
    run (signedAddTop q x y cs) m s=run (signedAdd q x y cs) m s := by
  have hxnd : x.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).1
  have qx : q∉x := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : List.Disjoint x (y++cs) := by
    have h : (x++(y++cs)).Nodup := by simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
    exact (List.nodup_append'.mp h).2.2
  have zx := (signComplement_counts q x).2
  let u := run (signComplement q x) [] s
  have fan := signComplement_correct q x hxnd qx s []
  have ux : Shape n (regValue x u.basis) := by
    change Shape n (regValue x (run (signComplement q x) [] s).basis)
    rw [fan.2.2]
    cases hs : s.basis q
    · exact source
    · simpa only [hx,if_true] using shape_complement n _ (by simpa [hx] using regValue_lt x s.basis) source
  have clean' : ∀ w ∈ cs, u.basis w=false := by
    intro w hw
    exact (fan.2.1 w (fun h => List.disjoint_left.mp dis h (List.mem_append_right _ hw))).trans (clean w hw)
  have out (r : List Bool) :
      regValue y (run (signComplement q x) r (run (addInPlace x y cs q) r u)).basis =
      regValue y (run (addInPlace x y cs q) r u).basis := by
    have h := signComplement_correct q x hxnd qx (run (addInPlace x y cs q) r u) r
    apply regValue_congr
    intro w hw
    exact h.2.1 w (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw))
  have old : regValue y (run (signedAdd q x y cs) [] s).basis =
      regValue y (run (addInPlace x y cs q) [] u).basis := by
    simp only [signedAdd,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have add := addInPlace_correct x y cs q hn (hx.trans hy.symm) hc u [] clean'
  have us : Shape n ((regValue x u.basis+regValue y u.basis+(u.basis q).toNat)%2^(n+2)) := by
    rw [old,add.2.2,hy] at sum
    exact sum
  have eq (r : List Bool) := TopCarry.addInPlaceTop_eq n x y cs q hy (hx.trans hy.symm)
    hc hn u r clean' ux us
  simp only [signedAddTop,signedAdd,List.append_assoc]
  rw [TopCarry.run_zero_head _ _ m s zx,TopCarry.run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq]
  have mc := TopCarry.addInPlaceTop_counts n x y cs q hy (hx.trans hy.symm) hc
  have mo := addInPlace_counts x y cs q (hx.trans hy.symm) hc
  rw [mc.2,mo.2,hy]
  rfl
end ECDSAAdd.Entrant.TickGap
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def recordTop (sx sy q : Wire) (x y cs : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAddTop q x y cs ++ skywalkSignToggle sx sy q

theorem signedAddTop_counts (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length) :
    toffoliCount (signedAddTop q x y cs)=n ∧ measurementCount (signedAddTop q x y cs)=n+1 := by
  have h := TopCarry.addInPlaceTop_counts n x y cs q hy (hx.trans hy.symm) hc
  simp only [signedAddTop,toffoliCount_append,measurementCount_append,
    (signComplement_counts q x).1,(signComplement_counts q x).2,h.1,h.2]
  exact ⟨by omega,by omega⟩

theorem toggle_frame (sx sy q : Wire) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (w : Wire) (hw : w≠q) :
    (run (skywalkSignToggle sx sy q) m s).basis w=s.basis w := by
  rw [skywalkSignToggle_correct sx sy q hqx hqy]
  simp [writeBit,hw]

theorem recordTop_eq (n : Nat) (sx sy q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (clean : ∀w∈cs,s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Shape n (regValue y (run (signedRecord sx sy q x y cs) [] s).basis)) :
    run (recordTop sx sy q x y cs) m s=run (signedRecord sx sy q x y cs) m s := by
  have qrest := (List.nodup_cons.mp hn).1
  have away (w : Wire) (hw : w∈x++y++cs) : w≠q := by
    intro he; subst w; exact qrest hw
  let u := run (skywalkSignToggle sx sy q) [] s
  have ut (w : Wire) (hw : w≠q) : u.basis w=s.basis w := toggle_frame sx sy q hqx hqy s [] w hw
  have ux : regValue x u.basis=regValue x s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  have uc : ∀w∈cs,u.basis w=false := by
    intro w hw
    exact (ut w (away w (by simp [hw]))).trans (clean w hw)
  have zx := (skywalkSignToggle_counts sx sy q).2
  have out (r : List Bool) :
      regValue y (run (skywalkSignToggle sx sy q) r (run (signedAdd q x y cs) r u)).basis =
      regValue y (run (signedAdd q x y cs) r u).basis :=
    regValue_congr _ _ _ (fun w hw => toggle_frame sx sy q hqx hqy _ r w (away w (by simp [hw])))
  have old : regValue y (run (signedRecord sx sy q x y cs) [] s).basis =
      regValue y (run (signedAdd q x y cs) [] u).basis := by
    simp only [signedRecord,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  rw [old] at sum
  have eq (r : List Bool) := signedAddTop_eq n q x y cs hx hy hc hn u r uc (ux ▸ source) sum
  have mc := (signedAddTop_counts n q x y cs hx hy hc).2
  have mo := (signedWord_counts q x y cs (hx.trans hy.symm) hc).2.1
  simp only [recordTop,signedRecord,List.append_assoc]
  rw [TopCarry.run_zero_head _ _ m s zx,TopCarry.run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq,mc,mo,hy]
  rfl
end ECDSAAdd.Entrant.TickGap
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def narrowTop (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  recordTop L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

theorem record_source (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0) :
    regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) m s).basis = regValue L.xp s.basis := by
  have h := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
    (signedRegValue L.xp s.basis) (signedRegValue L.yp s.basis) s m ⟨hq,rfl,rfl,clean⟩
  have eq := (signedRegValue_eq_iff L.xp _ _).mp h.2.2.1
  exact regValue_congr _ _ _ eq

theorem narrowTop_eq (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0)
    (source : Shape n (regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis))
    (sum : Shape n (regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis)) :
    run (narrowTop L (n+2)) m s=run (narrowSignedRecord L (n+2)) m s := by
  have views := L.views (n+2) hw
  have clean' : ∀w∈L.carryLow,s.basis w=false := (regValue_zero _ _).mp clean
  have qx : L.sx≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have fan (r : List Wire) (hr : ∀w∈r,w∉L.yhigh) (v : State) (record : List Bool) :
      regValue r (run (signComplement L.q L.yhigh) record v).basis=regValue r v.basis := by
    have f := signComplement_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) v record
    exact regValue_congr _ _ _ (fun w hw => f.2.1 w (hr w hw))
  have xaway : ∀w∈L.xp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp only [NarrowSignedRecordLayout.x,List.mem_append] at *; tauto)
  have yaway : ∀w∈L.yp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp [hw'])
  have outx : regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.xp xaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  have outy : regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.yp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.yp yaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  rw [outx,record_source L (n+2) hw hn s [] hq clean] at source
  rw [outy] at sum
  have eq (r : List Bool) := recordTop_eq n L.sx L.sy L.q L.xp L.yp L.carryLow
    hw.x hw.y (hw.carry.trans hw.y.symm) (L.short_nodup hn) qx qy s r clean' source sum
  have mc := signedAddTop_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have rz := (skywalkSignToggle_counts L.sx L.sy L.q).2
  have old := (signedWord_counts L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)).2.1
  have counts : measurementCount (recordTop L.sx L.sy L.q L.xp L.yp L.carryLow)=
      measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) := by
    simp only [recordTop,signedRecord,measurementCount_append,rz,mc.2,old,hw.y]
    omega
  simp only [narrowTop,narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
  rw [run_append,run_append,run_take,run_take,eq,counts]
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic Baselines Challenge RecordedQuantum

theorem signedAddTop_support (q : Wire) (x y cs : List Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (signedAddTop q x y cs) ⊆ wires (signedAdd q x y cs) := by
  rw [(signedWord_wires q x y cs hx hc).1]
  have fan : wires (signComplement q x) ⊆ (q::(x++y++cs)).toFinset := by
    intro w hw
    have h := signComplement_wires_subset q x hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  simp only [signedAddTop,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fan,TopCarry.addInPlaceTop_wires x y cs q⟩,fan⟩

theorem narrowTop_counts (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    toffoliCount (narrowTop L (n+2))+1=toffoliCount (narrowSignedRecord L (n+2)) ∧
      measurementCount (narrowTop L (n+2))=measurementCount (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have h := signedAddTop_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have old := narrowSignedRecord_counts L (n+2) hw
  have z := skywalkSignToggle_counts L.sx L.sy L.q
  have f := signComplement_counts L.q L.yhigh
  simp only [narrowTop,recordTop,v.1,v.2.1,v.2.2.1,v.2.2.2,
    toffoliCount_append,measurementCount_append,z.1,z.2,h.1,h.2,f.1,f.2,old.1,old.2.1]
  exact ⟨by omega,by omega⟩

theorem narrowTop_support (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    wires (narrowTop L (n+2)) ⊆ wires (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have sub := signedAddTop_support L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [narrowTop,narrowSignedRecord,recordTop,signedRecord,v.1,v.2.1,v.2.2.1,v.2.2.2,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub)
    (Finset.Subset.refl _)) (Finset.Subset.refl _)

theorem signedAddTop_physical (q : Wire) (x y cs : List Wire) (hn : (q::(x++y++cs)).Nodup) :
    GatePhysical (signedAddTop q x y cs) := by
  have qx : q∉x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x qx
  have top := TopCarry.addInPlaceTop_physical x y cs q hn
  simp only [signedAddTop,gatePhysical_append]
  exact ⟨⟨fan,top⟩,fan⟩

theorem narrowTop_physical (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) : GatePhysical (narrowTop L (n+2)) := by
  have v := L.views (n+2) hw
  have nd := L.short_nodup hn
  have qx : L.sx≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,qx,qy]
  have top := signedAddTop_physical L.q L.xp L.yp L.carryLow nd
  have fan := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowTop,recordTop,v.1,v.2.1,v.2.2.1,v.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨toggle,top⟩,toggle⟩,fan⟩

theorem top_slots_le_old (x y cs : List Wire) (c : Wire) :
    gateSlots (TopCarry.addInPlaceTop x y cs c) ≤ gateSlots (addInPlace x y cs c) := by
  induction x generalizing y cs c with
  | nil => simp [TopCarry.addInPlaceTop,addInPlace]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [TopCarry.addInPlaceTop,addInPlace]
      | cons b bs => cases bs <;> simp [TopCarry.addInPlaceTop,addInPlace]
    | cons a' as =>
      cases y with
      | nil => simp [TopCarry.addInPlaceTop,addInPlace]
      | cons b bs =>
        cases bs with
        | nil => simp [TopCarry.addInPlaceTop,addInPlace]
        | cons b' bs =>
          cases cs with
          | nil => simp [TopCarry.addInPlaceTop,addInPlace]
          | cons d ds =>
            have h := ih (b'::bs) ds d
            simp only [TopCarry.addInPlaceTop,addInPlace,gateSlots_append] at h ⊢
            split_ifs <;> simp only [majority_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots] at h ⊢ <;> omega

theorem narrowTop_slots (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (narrowTop L (n+2)) ≤ gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := top_slots_le_old L.xp L.yp L.carryLow L.q
  simp only [narrowTop,narrowSignedRecord,recordTop,signedRecord,signedAddTop,signedAdd,
    v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

/-- The two post-tick signed values fit below the strict late-stage cap. -/
theorem band_step_values (x p i : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p)
    (hi : 255 ≤ i  ∧  i ≤ 286) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int));
    let n := W.compactSkywalkTickPostWidth i-2;
    -((2^n:Nat):Int)  ≤  (SkywalkRails.step r).h  ∧  (SkywalkRails.step r).h  <  ((2^n:Nat):Int)  ∧
    -((2^n:Nat):Int)  ≤  (SkywalkRails.step r).k  ∧  (SkywalkRails.step r).k  <  ((2^n:Nat):Int) := by
  dsimp only
  have nw : W.compactSkywalkTickPostWidth i-2=510-i := by
    unfold W.compactSkywalkTickPostWidth W.narrowSkywalkWidth
    omega
  rw [nw]
  have cap := strict_sum_band x p (i+1) hp0 hpo hp gap hx cop (by omega)
  obtain ⟨G,S,enc⟩ := SkywalkTrace.iter_encoded (i+1) false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at enc
  rw [Function.iterate_succ_apply'] at enc
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  let z := SkywalkNat.step^[i+1] (SkywalkNat.init x p)
  change SkywalkTrace.next r=SkywalkRails.encode G S (z.u:Int) (z.v:Int) at enc
  change z.u+z.v < 2^(511-(i+1)) at cap
  have exp : 511-(i+1)=510-i := by omega
  rw [exp] at cap
  have abs := SkywalkRails.encode_abs_sum_bound G S z.u z.v (z.u+z.v) (Nat.le_refl _)
  rw [←enc] at abs
  change |(SkywalkRails.step r).h|  ≤  ((z.u+z.v:Nat):Int)  ∧
    |(SkywalkRails.step r).k|  ≤  ((z.u+z.v:Nat):Int) at abs
  have cap' : ((z.u+z.v:Nat):Int) < ((2^(510-i):Nat):Int) := by exact_mod_cast cap
  have ah := abs_le.mp abs.1
  have ak := abs_le.mp abs.2
  dsimp only [r] at ah ak
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem repaired_output_shape (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p)
    (hi : 255 ≤ i  ∧  i ≤ 286) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let L := W.compactSkywalkTickLayout w i;
    let n := W.compactSkywalkTickPostWidth i;
    Shape (n-2) (regValue (L.half.take n) (run (W.repairedTick w i) m s).basis)  ∧
      Shape (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis) := by
  dsimp only
  have hgap : p+2^32 ≤ 2^256 := Nat.le_of_lt gap
  rw [W.repairedTick_eq w hn x p i hp0 hx0 hpo hp hgap hx cop (by omega) s m hs]
  have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx cop (by omega) s hs
  have fit := W.narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp hgap hx cop (by omega)
  have out := W.compactSkywalkTickOutput_spec w i (by omega) hn _ _ _ fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s [] input
  have bounds := band_step_values x p i hp0 hpo hp gap hx cop hi
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have ns : n-2+2=n := by
    have width := W.compactSkywalkTick_width_bounds i (by omega)
    dsimp only [n]
    omega
  have lenA : n ≤ L.half.length := by
    rw [W.compactSkywalkTick_half w i (by omega),wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i (by omega)).2.2.1
  have lenB : n ≤ L.b.length := by
    rw [W.compactSkywalkTick_b w i (by omega),wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i (by omega)).2.2.1
  have aview : (W.compactSkywalkTickARelease w i).retained=L.half.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenA
  have bview : (W.compactSkywalkTickBRelease w i).retained=L.b.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenB
  have a := out.2.1
  have b := out.2.2.1
  rw [aview] at a
  rw [bview] at b
  have lenA' : (L.half.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenA]
  have lenB' : (L.b.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenB]
  unfold signedRegValue at a b
  rw [lenA'] at a
  rw [lenB'] at b
  change Shape (n-2) (regValue (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis) ∧
    Shape (n-2) (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
  constructor
  · apply shape_of_signed (n-2) _ (by simpa [ns,lenA'] using regValue_lt (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis)
    · rw [ns,a]; exact bounds.1
    · rw [ns,a]; exact bounds.2.1
  · apply shape_of_signed (n-2) _ (by simpa [ns,lenB'] using regValue_lt (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
    · rw [ns,b]; exact bounds.2.2.1
    · rw [ns,b]; exact bounds.2.2.2
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def head (w : Nat → Wire) (i : Nat) : Program :=
  let L := W.compactSkywalkTickLayout w i
  (if i=224 ∨ (255 ≤ i  ∧  i ≤ 509) then W.repairedRoute L
    else skywalkRoute L.a0 L.b0 L.ah L.bh) ++ skywalkSignedHalf L.aSign L.ext

def tail (w : Nat → Wire) (i : Nat) : Program :=
  [.CX (W.compactSkywalkTickLayout w i).previous (W.compactSkywalkTickLayout w i).a0] ++
    W.compactSkywalkTickCleanup w i

def tick (w : Nat → Wire) (i : Nat) : Program :=
  if 255 ≤ i  ∧  i ≤ 286 then
    head w i ++ narrowTop (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
      (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i
  else W.repairedTick w i

theorem old_split (w : Nat → Wire) (i : Nat) (band : 255 ≤ i  ∧  i ≤ 286) :
    W.repairedTick w i = head w i ++
      narrowSignedRecord (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
        (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i := by
  have nf : ¬ W.fwdTrim i := by unfold W.fwdTrim; omega
  simp only [W.repairedTick,if_neg nf,W.repairedTick0,head,tail,W.compactSkywalkTick,narrowSkywalkTick]
  split_ifs  <;> simp only [List.append_assoc]

theorem repairedRoute_small_support (L : SkywalkIntegerLayout) (hv : L.Valid) (hpos : 0 < L.bMid.length) :
    wires (W.repairedRoute L) ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
  have lo := swapRegisters_wires L.a0 L.aMid L.bMid hv.mids
  have tm : L.bMid.getD (L.bMid.length-1) 0∈L.bMid := W.repair_member_getD _ _ (by omega)
  have ls : wires (swapRegisters L.a0 L.aMid L.bMid) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    have h := lo hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh] at h ⊢
    tauto
  have ss : wires (W.signRepair L.aSign L.bSign L.previous (L.bMid.getD (L.bMid.length-1) 0)) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [W.signRepair,wires,Instr.wires,correctionWires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
      List.not_mem_nil,or_false]
    have ht : q=L.bMid.getD (L.bMid.length-1) 0 → q∈L.bMid := fun he => he ▸ tm
    tauto
  have cx : wires [.CX L.a0 L.b0] ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [W.repairedRoute,W.repairedSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨ls,ss⟩,cx⟩

theorem head_aux (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).history::(W.compactSkywalkTickLayout w i).carry) :
    (run (head w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have hpos : 0 < L.bMid.length := by
    change 0 < (wireBlock w 771 (W.compactSkywalkTickPreWidth i-2)).length
    rw [wireBlock_length]
    have width := W.compactSkywalkTick_width_bounds i hi
    omega
  have dis : List.Disjoint (L.history::L.carry) (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)) := by
    have nd : ((L.history::L.carry)++(L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh))).Nodup := by
      apply List.nodup_iff_count.mpr
      intro a
      have h := List.nodup_iff_count.mp hv.nodup a
      simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at h ⊢
      omega
    exact (List.nodup_append'.mp nd).2.2
  have qaway : q∉L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh) := List.disjoint_left.mp dis hq
  have sup : wires (head w i) ⊆ (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    have inc : (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [List.mem_toFinset,List.mem_cons] at ha ⊢
      tauto
    have repair := (repairedRoute_small_support L hv hpos).trans inc
    have full : wires (skywalkRoute L.a0 L.b0 L.ah L.bh) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    have half : wires (skywalkSignedHalf L.aSign L.ext) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [skywalkSignedHalf,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,or_false] at ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,List.mem_singleton]
      tauto
    simp only [head,wires_append,Finset.union_subset_iff]
    split_ifs  <;> exact ⟨by assumption,half⟩
  exact run_preserves_outside _ _ _ _ (fun h => qaway (List.mem_toFinset.mp (sup h)))

theorem tail_prefix (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).half.take (W.compactSkywalkTickPostWidth i) ++
      (W.compactSkywalkTickLayout w i).b.take (W.compactSkywalkTickPostWidth i)) :
    (run (tail w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have words := W.compactSkywalkTick_words_disjoint w i hi hn
  have nd := (List.nodup_cons.mp (L.record_nodup hv)).2
  have wa : L.half.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).1
  have wb : L.b.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  have adot : List.Disjoint (L.half.take n) (L.half.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wa
  have bdot : List.Disjoint (L.b.take n) (L.b.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wb
  have apart : q∉L.half.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact List.disjoint_left.mp adot hqa
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_drop h) (List.mem_of_mem_take hqb)
  have bpart : q∉L.b.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_take hqa) (List.mem_of_mem_drop h)
    · exact List.disjoint_left.mp bdot hqb
  have q0 : q≠L.a0 := by
    have qm : q∈L.half++L.b := by
      rcases List.mem_append.mp hq with hqa|hqb
      · exact List.mem_append_left _ (List.mem_of_mem_take hqa)
      · exact List.mem_append_right _ (List.mem_of_mem_take hqb)
    intro he
    subst q
    have h := List.nodup_iff_count.mp hv.nodup L.a0
    have hq' := List.count_pos_iff.mpr qm
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,List.count_nil,List.count_cons,List.count_append,
      List.count_singleton] at h hq'
    simp only [beq_self_eq_true,if_true] at h
    omega
  have valid := W.compactSkywalkTick_release_valid w i hi hn
  have af (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickARelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.1 v r).2.1 q apart
  have bf (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickBRelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.2 v r).2.1 q bpart
  simp only [tail,W.compactSkywalkTickCleanup,run_append,run_take]
  rw [bf,af]
  change Function.update s.basis L.a0 (s.basis L.a0 ^^ s.basis L.previous) q = s.basis q
  exact Function.update_of_ne q0 _ _
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

theorem tick_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p) (hi : i < 512)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (tick w i) m s=run (W.repairedTick w i) m s := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    let P := head w i
    let Q := narrowSignedRecord R n
    let E := tail w i
    let u := run P (m.take (measurementCount P)) s
    let v := run Q (m.drop (measurementCount P)) u
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have width := W.compactSkywalkTick_width_bounds i hi
    have npos : 2 ≤ n := width.2.1
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have nd : R.wires.Nodup := narrowSkywalkRecord_nodup L hv n (by omega) nlen
    have n2 : n-2+2=n := by omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have whole : run (W.repairedTick w i) m s=
        run E ((m.drop (measurementCount P)).drop (measurementCount Q)) v := by
      rw [old_split _ _ band,List.append_assoc,run_append,run_take,run_append,run_take]
      simp only [P,Q,E,u,v,run_take]
      rfl
    have sizes := repaired_output_shape w hn x p i hp0 hx0 hpo hp gap hx cop band s m hs
    have keep (r : List Wire) (hr : r⊆L.half.take n++L.b.take n) :
        regValue r (run (W.repairedTick w i) m s).basis=regValue r v.basis := by
      rw [whole]
      apply regValue_congr
      intro q hq
      exact tail_prefix w i hi hn v _ q (hr hq)
    have shapeX : Shape (n-2) (regValue (L.half.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_left _ hq)]
      exact sizes.1
    have shapeY : Shape (n-2) (regValue (L.b.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_right _ hq)]
      exact sizes.2
    have record0 : (run Q [] u).basis=v.basis := run_basis_records Q u u [] (m.drop (measurementCount P)) rfl
    have orig := narrowSkywalkRecord_views L hv n (by omega) nlen
    have views := R.views n hw
    have xx : R.xp=L.half.take n := by rw [←views.1]; rw [orig.1]
    have yy : R.yp=L.b.take n := by rw [←views.2.1]; rw [orig.2.1]
    have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp (Nat.le_of_lt gap) hx cop hi s hs
    have uq : u.basis R.q=false := by
      apply (head_aux w i hi hn s _ L.history (List.mem_cons_self)).trans
      exact input.2.2.2.2.1
    have clean : regValue R.carryLow u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have qm : q∈L.carry := List.mem_of_mem_take hq
      apply (head_aux w i hi hn s _ q (List.mem_cons_of_mem _ qm)).trans
      exact (regValue_zero _ _).mp input.2.2.2.2.2 q qm
    have eq (r : List Bool) : run (narrowTop R n) r u=run Q r u := by
      have a : Shape (n-2) (regValue R.xp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,xx,record0]
        exact shapeX
      have b : Shape (n-2) (regValue R.yp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,yy,record0]
        exact shapeY
      simpa only [n2] using narrowTop_eq (n-2) R hw' nd u r uq clean a b
    have counts : measurementCount (narrowTop R n)=measurementCount Q := by
      simpa only [n2] using (narrowTop_counts (n-2) R hw').2
    simp only [tick,if_pos band]
    rw [old_split _ _ band]
    change run ((P++narrowTop R n)++E) m s=run ((P++Q)++E) m s
    conv_lhs => rw [List.append_assoc,run_append P (narrowTop R n++E)]
    conv_rhs => rw [List.append_assoc,run_append P (Q++E)]
    change run (narrowTop R n++E) (m.drop (measurementCount P)) u = run (Q++E) (m.drop (measurementCount P)) u
    rw [run_append (narrowTop R n) E,run_append Q E]
    rw [run_take (narrowTop R n),run_take Q,eq,counts]
  · simp only [tick,if_neg band]

def due (i : Nat) : Nat := if 255 ≤ i  ∧  i ≤ 286 then 1 else 0

theorem tick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (tick w i)+due i=toffoliCount (W.repairedTick w i)  ∧
    measurementCount (tick w i)=measurementCount (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_counts (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,due,if_pos band,toffoliCount_append,measurementCount_append]
    exact ⟨by omega,by omega⟩
  · simp only [tick,if_neg band,due,if_neg band,Nat.add_zero,and_self]

theorem tick_support (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    wires (tick w i) ⊆ wires (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_support (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)
  · simp only [tick,if_neg band]
    exact Finset.Subset.refl _

theorem tick_slots (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    Challenge.gateSlots (tick w i)  ≤  Challenge.gateSlots (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_slots (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,Challenge.gateSlots_append]
    omega
  · simp only [tick,if_neg band]
    exact Nat.le_refl _

theorem tick_physical (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (tick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_physical (n-2) R hw' (narrowSkywalkRecord_nodup L hv n (by omega) nlen)
    simp only [n2] at h
    dsimp only [R,n,L] at h
    have old := W.repairedTick_physical w i hi hn
    rw [old_split _ _ band] at old
    simp only [tick,if_pos band,gatePhysical_append] at old ⊢
    exact ⟨⟨old.1.1,h⟩,old.2⟩
  · simpa only [tick,if_neg band] using W.repairedTick_physical w i hi hn
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic MappedCompressed Secp256k1 History5 OB5

theorem tick_eq5 (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  have dis := Stack5.prefix_disjoint_layout base base_pool_nodup i i (Nat.le_refl i) hi
  have read : ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q (fun he => Finset.disjoint_left.mp dis he hq)
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (tick_support base i hi base_pool_nodup).trans old
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 < 2^256 := by norm_num [p]
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (tick_eq base base_pool_nodup x p i hp0 hx0 hpo hp gap hx cop hi raw m hraw)

end ECDSAAdd.Entrant.TickGap
end
end -- original module boundary


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end
