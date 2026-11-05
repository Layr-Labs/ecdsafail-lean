import ECDSAAdd.Submission.Entrant.MainPart04
import ECDSAAdd.Submission.Entrant.ForwardCarryAffine

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
  renameProgram (pmapR L) (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val)

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

theorem merged_S (k : Nat) : wires (E1AffineEndpoints52Research.Forward.merged base (base 2400) k)⊆S :=
  E1AffineEndpoints52Research.Forward.merged_support base (base 2400) k

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
  have eqL := E1AffineEndpoints52Research.Forward.merged_eq_forward base (base 2400) base_pool_nodup g2400 k.val k.isLt X hX t u m1
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
  renameProgram sig (renameProgram rho (E1AffineEndpoints52Research.Forward.merged base (base 2400) k))

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
    (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) S (merged_S k) q hq
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
    toffoliCount (entryM L k)=1022 ∧ measurementCount (entryM L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val)
  have c := E1AffineEndpoints52Research.Forward.merged_counts base (base 2400) k.val
  rw [entryM,r.1,r.2]; exact c

theorem tickF_counts (L : ControlledPointLayout) :
    toffoliCount (tickF L)=508 ∧ measurementCount (tickF L)=508 := by
  have r := renameProgram_counts (pmapR L) (NativeFirstDirect.forward base)
  have c := NativeFirstDirect.forward_counts base
  rw [tickF,r.1,r.2]; exact c

theorem entryM_slots (L : ControlledPointLayout) (k : Fp) :
    gateSlots (entryM L k)≤25000 := by
  simpa only [entryM,Baselines.rename_gateSlots] using
    E1AffineEndpoints52Research.Forward.merged_slots base (base 2400) k.val

theorem entryM_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryM L k)⊆(OB5Support.sites L).toFinset := by
  rw [entryM_eq]
  exact OB5Support.placed_support_logical L hw _ (logicalM k.val)

theorem entryM_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (entryM L k) := by
  rw [entryM]
  exact gatePhysical_rename_support (pmapR L) (E1AffineEndpoints52Research.Forward.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (merged_S k.val ha) b (merged_S k.val hb) e)
    (E1AffineEndpoints52Research.Forward.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

theorem prefix_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryM L k)+252=
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

def hAddT1 (w : Nat → Wire) : Program := [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ hPost w

/-- `hAddT1` with its last carry trimmed as well (see `MappedTopZero`). -/
def hAddT (w : Nat → Wire) : Program := MappedTopZero.topT (dBits w) w (w 1028)


def thrA (k : Nat) : Nat := (k+1)/2
def thrB (k : Nat) : Nat := (k+1)/2 ^^^ (k+p+1)/2

def loadT (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrA k)++maskedConstant (w 721) (tR w) (thrB k)

/-- Unconditional canonical reflection followed by controlled constant addition, merged into the direct first tick. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w)++notRegister (kR w))++prodPart w g++loadK w g k++E1WholeKAdd52Research.flagKAdd52 w++loadK w g k++
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

/-- Literal identity for this reflected namespace, without changing the generic adder. -/
theorem kAdd_literal (w : Nat → Wire) : E1Reflected.kAddM w = KAddCallerBridgeResearch.literalKAdd w := rfl

/-- Carry cleanliness from the actual reflected MF frame and carry-bank premise. -/
theorem carry_clean (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Reflected.aC w,b0 q=false) (s : BasisState)
    (hs : E1Reflected.MF w b0 H X T par f gp fp s) : s (w 1796)=false := by
  have away : w 1796∉E1Reflected.mutL w := by
    simp only [E1Reflected.mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨E1Reflected.nb w hn 1796 0 258 (by omega) (by omega) (by omega),
      E1Reflected.nb w hn 1796 770 258 (by omega) (by omega) (by omega)⟩,
      E1Reflected.nb w hn 1796 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact E1Reflected.w_ne w hn _ _ (by omega) (by omega) (by omega)
  have member : w 1796∈E1Reflected.aC w := by
    apply List.mem_map.mpr
    refine ⟨1796,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  exact (hs.2.2.2.2.2.2.2 _ away).trans (hc _ member)

/-- Known-output flag replacement for the actual reflected MF. -/
theorem stepKAddFlag (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Reflected.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (D : Nat) (hD : D<ECDSAAdd.p) (hp : par=decide (D%2=1))
    (hWord : (H+X)%2^258=E1CallerValueFactsResearch.Kword D par) :
    Triple (E1Reflected.MF w b0 H X T par f gp fp) (KAddCallerBridgeResearch.flagKAdd w)
      (E1Reflected.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Reflected.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (KAddCallerBridgeResearch.literalKAdd w) [] s).basis =
      E1CallerValueFactsResearch.Kword D par := oldEmpty.2.2.1.trans hWord
  have clean := carry_clean w hn b0 H X T par f gp fp hc s.basis hs
  have equal := KAddCallerBridgeResearch.forward_run_eq_pool w hn s m clean D hD par hp hs.2.2.2.1 postWord
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Reflected.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mp (old s m hs)

/-! Checked reflected own-MF52 proof body, inlined to avoid a MainPart05 import cycle. -/
namespace Tail52
open Arithmetic RecordedQuantum KAddCallerBridgeResearch
open E1CallerValueFactsResearch E1WholeKAdd52Research

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.regValue

private theorem carry_clean_at52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Reflected.aC w,b0 q=false) (s : BasisState)
    (hs : E1Reflected.MF w b0 H X T par f gp fp s)
    (i : Nat) (hi : 1794 ≤ i ∧ i < 1797) : s (w i)=false := by
  have away : w i∉E1Reflected.mutL w := by
    simp only [E1Reflected.mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨E1Reflected.nb w hn i 0 258 (by omega) (by omega) (by omega),
      E1Reflected.nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
      E1Reflected.nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact E1Reflected.w_ne w hn _ _ (by omega) (by omega) (by omega)
  have member : w i∈E1Reflected.aC w := by
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  exact (hs.2.2.2.2.2.2.2 _ away).trans (hc _ member)

/-- The real reflected MF exterior frame supplies all three clean tail carries. -/
theorem highCarryClean_from_MF52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Reflected.aC w,b0 q=false) (s : BasisState)
    (hs : E1Reflected.MF w b0 H X T par f gp fp s) : highCarryClean52 w s := by
  change s (w 1794)=false ∧ s (w 1795)=false ∧ s (w 1796)=false
  exact ⟨carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1794 ⟨by decide,by decide⟩,
    carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1795 ⟨by decide,by decide⟩,
    carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1796 ⟨by decide,by decide⟩⟩

/-- Reflected flag replacement from its OWN old stepKAdd and actual MF.
H/X remain the caller's physical register values; hWord and parity stay explicit. -/
theorem stepKAddFlag52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Reflected.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (D : Nat) (hD : D<ECDSAAdd.p) (hp : par=decide (D%2=1))
    (hWord : (H+X)%2^258=Kword D par) :
    Triple (E1Reflected.MF w b0 H X T par f gp fp) (flagKAdd52 w)
      (E1Reflected.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Reflected.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [E1Reflected.kAdd_literal] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Kword D par :=
    oldEmpty.2.2.1.trans hWord
  have clean := highCarryClean_from_MF52 w hn b0 H X T par f gp fp hc s.basis hs
  have outputs := ActualMF52Research.forward_outputs_from_postWord52 w s D hD par hp postWord
  have equal := flag_run_eq52 w hn s m clean par hs.2.2.2.1 outputs
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Reflected.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mpr (old s m hs)

end Tail52

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

theorem hAddT1_run (w : Nat → Wire) (h17 : w 1797 ≠ w 1540) (m : List Bool) (s : State)
    (hc : s.basis (w 1797) = false) : run (hAddT1 w) m s = run (hAddM w) m s := by
  rw [hAddM_split, hAddT1, run_drop_ccx]
  · rfl
  · simp only [run, writeBit, Function.update_of_ne h17, hc]

theorem hAddT1_counts (w : Nat → Wire) :
    toffoliCount (hAddT1 w) + 1 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT1 w) = measurementCount (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [toffoliCount_append, measurementCount_append]
  constructor
  · simp [toffoliCount]; omega
  · simp [measurementCount]

theorem hAddT1_wires (w : Nat → Wire) : wires (hAddT1 w) ⊆ wires (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.subset_union_left) (Finset.Subset.refl _)

theorem hAddT1_physical (w : Nat → Wire) (h : GatePhysical (hAddM w)) : GatePhysical (hAddT1 w) := by
  rw [hAddM_split] at h
  rw [hAddT1]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem hAddT1_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT1 w) + 1 = Challenge.gateSlots (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [Challenge.gateSlots_append]
  simp [Challenge.gateSlots, Challenge.instructionSlots]
  omega


theorem dBits_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBits w)) : q=w 1028 := by
  simp only [dBits,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all


/-! ### Last-carry trim of `hAddT1`: the output `H < p < 2^256`, so its top bit is zero -/

theorem hAddT1_eq (w : Nat → Wire) : hAddT1 w = MappedTopZero.oldT (dBits w) w := rfl

theorem hAddT_eq (w : Nat → Wire) : hAddT w = MappedTopZero.topT (dBits w) w (w 1028) := rfl

theorem dBits_drop (w : Nat → Wire) :
    (dBits w).drop 255 = [MappedTopZero.lowBit (w 1028), MappedTopZero.highBit (w 1028)] := by
  have e : (List.range 257).drop 255 = [255,256] := by decide
  have t1 : (2^257-p).testBit 255 = false := by rw [p_val]; decide
  have t2 : p.testBit 255 = true := by rw [p_val]; decide
  have t3 : (2^257-p).testBit 256 = true := by rw [p_val]; decide
  have t4 : p.testBit 256 = false := by rw [p_val]; decide
  rw [dBits, ← List.map_drop, e]
  simp only [List.map_cons, List.map_nil, t1, t2, t3, t4, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, MappedTopZero.lowBit, MappedTopZero.highBit]

theorem hAddT_counts (w : Nat → Wire) :
    toffoliCount (hAddT w) + 2 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT w) = measurementCount (hAddM w) := by
  have a := hAddT1_counts w
  have b : toffoliCount (hAddT w)+1=toffoliCount (hAddT1 w) ∧
      measurementCount (hAddT w)=measurementCount (hAddT1 w) ∧
      Challenge.gateSlots (hAddT w)+7=Challenge.gateSlots (hAddT1 w) :=
    MappedTopZero.topT_counts (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
  exact ⟨by omega, by omega⟩

section HTopWires
-- Keep elaboration from expanding the whole 257-bit adder's wire set.
attribute [local irreducible] ECDSAAdd.wires

theorem hAddT_wires (w : Nat → Wire) : wires (hAddT w) ⊆ wires (hAddM w) := by
  have b : wires (hAddT w) ⊆ wires (hAddT1 w) :=
    MappedTopZero.topT_wires (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
  exact Finset.Subset.trans b (hAddT1_wires w)

end HTopWires

theorem hAddT_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (h : GatePhysical (hAddM w)) : GatePhysical (hAddT w) := by
  have nd : [w 1028,w 256,w 1794,w 257].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨w_ne w hn _ _ (by omega) (by omega) (by omega),w_ne w hn _ _ (by omega) (by omega) (by omega),
      w_ne w hn _ _ (by omega) (by omega) (by omega)⟩,
      ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),w_ne w hn _ _ (by omega) (by omega) (by omega)⟩,
      w_ne w hn _ _ (by omega) (by omega) (by omega)⟩
  have b : GatePhysical (hAddT1 w) → GatePhysical (hAddT w) :=
    MappedTopZero.topT_physical (dBits w) w (w 1028) (dBits_length w) (dBits_drop w) nd
  exact b (hAddT1_physical w h)

theorem hAddT_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT w) + 8 = Challenge.gateSlots (hAddM w) := by
  have a := hAddT1_slots w
  have b : Challenge.gateSlots (hAddT w)+7=Challenge.gateSlots (hAddT1 w) :=
    (MappedTopZero.topT_counts (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)).2.2
  omega

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
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : (delta par+Y)%2^257<2^256) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddT w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  have h17 : w 1797 ≠ w 1540 := w_ne w hn 1797 1540 (by omega) (by omega) (by omega)
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  have m95 : w 1795∈aC w := (mem_blk w hn 1795 1540 257 (by omega) (by omega)).mpr (by omega)
  have c95 : s.basis (w 1795)=false := (h.2.2.2.2.2.2.2 _ (aC_out w hn _ m95)).trans (hc _ m95)
  have post := (stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s [] h).2
  have top : (run (MappedTopZero.oldT (dBits w) w) [] s).basis (w 257)=false := by
    rw [← hAddT1_eq, hAddT1_run w h17 [] s c17]
    have bit := regValue_bit (hR w) 257 0 (run (hAddM w) [] s).basis (by simp [hR,wireBlock_length])
    have port : (hR w).getD 257 0=w 257 := rfl
    rw [port,post.1] at bit
    have lt : 2*((delta par+Y)%2^257)<2^257 := by
      rw [show (2:Nat)^257=2*2^256 by norm_num]; omega
    rw [Nat.div_eq_of_lt lt] at bit
    cases hb : (run (hAddM w) [] s).basis (w 257) <;> simp_all
  have inj : ∀ i j,i<1798 → j<1798 → w i=w j → i=j :=
    fun i j hi hj e => skywalkPool_index_inj w hn i j hi hj e
  have eq := MappedTopZero.topT_run (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
    (fun q hq => dBits_wire w q hq) inj rfl s m c95 top
  rw [hAddT_eq,eq,← hAddT1_eq,hAddT1_run w h17 m s c17]
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
  have hdx : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
  have hK : (tk k G f par+(2^258-1-X/2))%2^258=K := by
    rw [Nat.add_comm]
    exact a2
  have hWord : (tk k G f par+(2^258-1-X/2))%2^258=
      E1CallerValueFactsResearch.Kword dx par := by
    simpa only [K,E1CallerValueFactsResearch.Kword] using hK
  have s6 := Tail52.stepKAddFlag52 w hn b0 (tk k G f par) (2^258-1-X/2) 0 par f
    (G && par) (f && par) hac h1797 dx hdx rfl hWord
  rw [hK] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;> simp [hC_val] <;> omega
  have hH10 : (delta par+K%2^257)%2^257<2^256 := by
    rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]]
    have h2 := hHlt
    have h3 := Bool.toNat_le (!par)
    rw [show (2:Nat)^257=2*2^256 by norm_num] at h2
    omega
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by norm_num)) hac h1797 hH10
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
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
  have hKOld : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (E1WholeKAdd52Research.flagKAdd52 w)⊆(mSites w g).toFinset := by
    have sub := E1ResourceBridge52Research.flag_support52 w
    rw [← kAdd_literal w] at sub
    apply sub.trans
    refine Finset.union_subset hKOld ?_
    exact Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr (I 1028 (by omega)))
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
    toffoliCount (merged w g k)=1022 ∧ measurementCount (merged w g k)=1027 := by
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
  have kc := E1WholeKAdd52Research.flag_counts52 w
  have kT : toffoliCount (E1WholeKAdd52Research.flagKAdd52 w)=255 := by
    have oldT := k1.1
    change toffoliCount (KAddCallerBridgeResearch.literalKAdd w)=257 at oldT
    omega
  have kM : measurementCount (E1WholeKAdd52Research.flagKAdd52 w)=257 := by
    have oldM := k1.2
    change measurementCount (KAddCallerBridgeResearch.literalKAdd w)=257 at oldM
    omega
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=254 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,comparePart,prodPart,loadK,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,kT,kM,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
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
  have kOldP : GatePhysical (kAddM w) := by
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
  have kP : GatePhysical (E1WholeKAdd52Research.flagKAdd52 w) := by
    apply E1ResourceBridge52Research.flag_gatePhysical_pool52 w hn
    simpa only [← kAdd_literal w] using kOldP
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
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hn hP
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
  have kOld : Challenge.gateSlots (KAddCallerBridgeResearch.literalKAdd w)≤17*258 := k1
  have kNew : Challenge.gateSlots (E1WholeKAdd52Research.flagKAdd52 w)+2≤17*258 := by
    rw [(E1WholeKAdd52Research.flag_counts52 w).2.2]
    exact kOld
  rw [dBits_length] at h1
  rw [lh] at e1
  have nk : Challenge.gateSlots (notRegister (kR w))=258 := by
    simp [Baselines.notRegister_gateSlots,kR,wireBlock_length]
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,Challenge.gateSlots_append,pr,w0,q1,q2,cp,nk]
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
    toffoliCount (entryR L k)=1022 ∧ measurementCount (entryR L k)=1027 := by
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
    toffoliCount (generic L cx cy)+759=toffoliCount (baselineGeneric L cx cy) ∧
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
    (h : toffoliCount A+759=toffoliCount B ∧ measurementCount A+751=measurementCount B) :
    toffoliCount (GenericQ5Geometry.wrapG L A)+759=toffoliCount (GenericQ5Geometry.wrapG L B) ∧
    measurementCount (GenericQ5Geometry.wrapG L A)+751=measurementCount (GenericQ5Geometry.wrapG L B) := by
  simp only [GenericQ5Geometry.wrapG,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem gen_counts_delta (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+759=toffoliCount (Rolling1588BFFinal.gen L cx cy) ∧
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
    (A B : Program) (h : toffoliCount A+759=toffoliCount B ∧ measurementCount A+751=measurementCount B) :
    toffoliCount (Edges.wrapper L C cy A)+759=toffoliCount (Edges.wrapper L C cy B) ∧
    measurementCount (Edges.wrapper L C cy A)+751=measurementCount (Edges.wrapper L C cy B) := by
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2151690 := by
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
def bounds : Challenge.Bounds := ⟨2151690,1499214,1588,50189199+Rolling1588.slotGrowth⟩

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

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151690 := by
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


set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== IntegerTickRanges (ArthurOstapenko baaabf50, ported) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TickRanges

def H : Nat := 2^255

theorem classify (x p i : Nat) (hx0 : 0<x) (hx : x<p) (hpodd : p%2=1)
    (hp : p<2^256) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v < H   ∨
    (z.v=p   ∧   z.u*2^i=x)   ∨
    (∃ t r : Nat, t+r=i   ∧   1  ≤  r   ∧   z.v*2^t=x   ∧   z.u*2^r+z.v=p   ∧   z.u+z.v<p) := by
  induction i with
  | zero =>
    exact Or.inr (Or.inl ⟨rfl,by simp [SkywalkNat.init]⟩)
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    generalize heq : SkywalkNat.step^[i] (SkywalkNat.init x p)=z at ih ⊢
    rcases ih with hs | hno | hone
    · exact Or.inl ((SkywalkNat.step_sum_nonincrease z).trans_lt hs)
    · obtain ⟨hv,hu⟩ := hno
      have hz : z.u  ≠  0 := by intro h; simp [h] at hu; omega
      have hul : z.u<p := by
        have hi : 1  ≤  2^i := Nat.one_le_two_pow
        nlinarith
      by_cases he : z.u%2=0
      · right; left
        refine ⟨by simp [SkywalkNat.step,hz,he,hv],?_⟩
        simp only [SkywalkNat.step,if_neg hz,if_pos he,pow_succ]
        have hh : z.u/2*2=z.u := by omega
        calc
          _ = (z.u/2*2)*2^i := by ring
          _ = x := by rw [hh,hu]
      · right; right
        have hodd : z.u%2=1 := by omega
        have hdiff : (p-z.u)/2*2=p-z.u := by omega
        refine ⟨i,1,by omega,by omega,?_,?_,?_⟩
        all_goals simp only [SkywalkNat.step,if_neg hz,if_neg he,hv,
          if_neg (show   ¬  p  ≤  z.u by omega)]
        · exact hu
        · norm_num; omega
        · omega
    · obtain ⟨t,r,htr,hr,hv,hu,hs⟩ := hone
      have vz : z.v  ≤  x := by
        have ht : 1  ≤  2^t := Nat.one_le_two_pow
        nlinarith
      have hz : z.u  ≠  0 := by intro h; simp [h] at hu; omega
      have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) (show 0<p from by omega) hpodd
      rw [heq] at valid
      have vo : z.v%2=1 := valid.2.1
      by_cases he : z.u%2=0
      · right; right
        refine ⟨t,r+1,by omega,by omega,?_,?_,?_⟩
        all_goals simp only [SkywalkNat.step,if_neg hz,if_pos he]
        · exact hv
        · rw [pow_succ]
          have hh : z.u/2*2=z.u := by omega
          calc
            _ = (z.u/2*2)*2^r+z.v := by ring
            _ = p := by rw [hh,hu]
        · omega
      · left
        unfold SkywalkNat.step
        rw [if_neg hz,if_neg he]
        have hpH : p<2*H := by simpa [H,pow_succ] using hp
        split_ifs <;> dsimp only <;> omega

theorem early_gap (x i : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hi : 225  ≤  i   ∧   i  ≤  254) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)
    z.u+z.v < H   ∨   H  ≤  z.v := by
  have hp : ECDSAAdd.p<2^256 := by norm_num [ECDSAAdd.p]
  have hpodd : ECDSAAdd.p%2=1 := by norm_num [ECDSAAdd.p]
  have hpe : ECDSAAdd.p+(2^32+977)=2*H := by norm_num [ECDSAAdd.p,H]
  obtain hs | hno | hone := classify x ECDSAAdd.p i hx0 hx hpodd hp
  · exact Or.inl hs
  · exact Or.inr (by rw [hno.1]; norm_num [ECDSAAdd.p,H])
  · obtain ⟨t,r,htr,hr,hv,hu,_⟩ := hone
    by_cases ht : 2  ≤  t
    · by_cases hr2 : 2  ≤  r
      · left
        have tp : 4  ≤  2^t := by simpa using Nat.pow_le_pow_right (by decide : 1  ≤  (2:Nat)) ht
        have rp : 4  ≤  2^r := by simpa using Nat.pow_le_pow_right (by decide : 1  ≤  (2:Nat)) hr2
        have hsmall : 4*((SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).u+
            (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v)<2*ECDSAAdd.p := by nlinarith
        nlinarith
      · have re : r=1 := by omega
        have tt : 224  ≤  t := by omega
        have tp : 2^224  ≤  2^t := Nat.pow_le_pow_right (by decide) tt
        left
        rw [re] at hu
        norm_num at hu
        have vle : (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v<2^32 := by
          by_contra hh
          have vv : 2^32  ≤  (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v := by omega
          have mul := Nat.mul_le_mul vv tp
          norm_num at mul
          nlinarith
        nlinarith
    · have rr : 224  ≤  r := by omega
      have rle : r  ≤  254 := by omega
      have rp : 2^224  ≤  2^r := Nat.pow_le_pow_right (by decide) rr
      have rpbig : 2^32+977<2^r := by
        calc
          2^32+977 < 2^224 := by norm_num
          _   ≤   2^r := rp
      have ep : 2^(256-r)*2^r=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
      have exp : 256-r  ≤  32 := by omega
      have sm : 2^(256-r)  ≤  2^32 := Nat.pow_le_pow_right (by decide) exp
      let z := SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)
      change z.v*2^t=x at hv
      change z.u*2^r+z.v=ECDSAAdd.p at hu
      change z.u+z.v<H   ∨   H  ≤  z.v
      have ucap : z.u<2^32 := by
        have ub : z.u<2^(256-r) := by
          by_contra h
          have mm := Nat.mul_le_mul_right (2^r) (Nat.le_of_not_gt h)
          nlinarith
        omega
      by_cases vb : H  ≤  z.v
      · exact Or.inr vb
      · left
        by_contra ns
        have vl : z.v<H := by omega
        have vt : H<z.v+(2^32+977) := by omega
        have hm : 2^(255-r)*2^r=H := by
          rw [←pow_add]
          change 2^(255-r+r)=(2:Nat)^255
          congr 1
          omega
        have um : z.u<2^(255-r) := by
          by_contra hh
          have mm := Nat.mul_le_mul_right (2^r) (Nat.le_of_not_gt hh)
          nlinarith
        have mm := Nat.mul_le_mul_right (2^r) (show z.u+1  ≤  2^(255-r) by omega)
        nlinarith
end ECDSAAdd.Entrant.TickRanges
namespace ECDSAAdd.Entrant.TickRanges

def Outside (v : Int) : Prop := v< -(H:Int)  ∨  (H:Int) ≤ v

theorem encode_boundary (g s : Bool) (u v : Int) (hu : 0 ≤ u) (hv : 0<v)
    (hvo : v%2=1) (hb : u+v<2*(H:Int)) (gap : u+v<(H:Int)  ∨  (H:Int) ≤ v) :
    let r := SkywalkRails.encode g s u v
    let eo := SkywalkRails.route r.a r.b;
    - (H:Int)  ≤  (SkywalkRails.step r).h  ∧  (SkywalkRails.step r).h<(H:Int)  ∧
      (Outside eo.2 ↔ Outside (SkywalkRails.step r).k) := by
  have hp : 0<(H:Int) := by norm_num [H]
  have ucap : u<(H:Int) := by omega
  by_cases he : u%2=0
  · have step := SkywalkRails.step_encode_even g s u v hu hv hvo he
    have hl : (u+v)%2 ≠ 0 := by omega
    have hn : (-u)%2=0 := by omega
    have hneg : (-u)/2= -(u/2) := by omega
    cases g <;> cases s <;>
      simp only [SkywalkRails.encode,SkywalkRails.route,SkywalkRails.odd,
        SkywalkRails.signed,Bool.false_eq_true,if_false,if_true,hl,hn,he,
        ne_eq,not_false_eq_true,not_true_eq_false,decide_true,decide_false] at step ⊢ <;>
      rw [step] <;> dsimp only <;> unfold Outside <;> omega
  · have step := SkywalkRails.step_encode_odd g s u v hu hv hvo he
    have hl : (u+v)%2=0 := by omega
    have hn : (-u)%2 ≠ 0 := by omega
    cases g <;> cases s <;>
      simp only [SkywalkRails.encode,SkywalkRails.route,SkywalkRails.odd,
        SkywalkRails.signed,Bool.false_eq_true,if_false,if_true,hl,hn,he,
        ne_eq,not_false_eq_true,not_true_eq_false,decide_true,decide_false] at step ⊢ <;>
      rw [step] <;> dsimp only <;> unfold Outside <;> omega
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
theorem run_mid_congr (M X X' E : Program) (m : List Bool) (s : State)
    (hM : measurementCount M = 0) (hc : measurementCount X = measurementCount X')
    (h : ∀ r, run X r (run M [] s) = run X' r (run M [] s)) :
    run (M ++ X ++ E) m s = run (M ++ X' ++ E) m s := by
  rw [List.append_assoc, List.append_assoc, run_append M (X ++ E), run_append M (X' ++ E), hM,
    List.take_zero, List.drop_zero, run_append X E, run_append X' E, hc, h]

theorem run_zero_head (M R : Program) (m : List Bool) (s : State) (hM : measurementCount M = 0) :
    run (M ++ R) m s = run R m (run M [] s) := by
  rw [run_append, hM, List.take_zero, List.drop_zero]

theorem run_congr_head (X X' E : Program) (m : List Bool) (v : State)
    (hc : measurementCount X = measurementCount X') (h : ∀ r, run X r v = run X' r v) :
    run (X ++ E) m v = run (X' ++ E) m v := by
  rw [run_append, run_append X' E, hc, h]

theorem run_head_congr (P P' E : Program) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hP' : measurementCount P' = 0)
    (h : run P [] s = run P' [] s) :
    run (P ++ E) m s = run (P' ++ E) m s := by
  rw [run_append P E, run_append P' E, hP, hP', List.take_zero, List.drop_zero, h]

def addCopy : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      (if as = [] then [.CX cin c] else majority a b cin c) ++
        addCopy (a' :: as) (b' :: bs) cs c ++ eraseCarry a b cin c ++ [.CX a b, .CX cin b]
  | [a], [b], _, cin => [.CX a b, .CX cin b]
  | _, _, _, _ => []

theorem shape_two {x y carry : List Wire} (hy : y.length = 0 + 2) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) :
    ∃ a a' b b' c, x = [a, a'] ∧ y = [b, b'] ∧ carry = [c] := by
  rcases y with _ | ⟨b, _ | ⟨b', _ | ⟨b'', ys⟩⟩⟩ <;> simp at hy
  rcases x with _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs⟩⟩⟩ <;> simp at hx
  rcases carry with _ | ⟨c, _ | ⟨c', cs⟩⟩ <;> simp at hc
  exact ⟨a, a', b, b', c, rfl, rfl, rfl⟩

theorem shape_succ {n : Nat} {x y carry : List Wire} (hy : y.length = n + 1 + 2)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    ∃ a a' a'' as b b' b'' bs c cs, x = a :: a' :: a'' :: as ∧ y = b :: b' :: b'' :: bs ∧
      carry = c :: cs := by
  rcases y with _ | ⟨b, _ | ⟨b', _ | ⟨b'', ys⟩⟩⟩ <;> simp at hy
  rcases x with _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs⟩⟩⟩ <;> simp at hx
  rcases carry with _ | ⟨c, cs⟩ <;> simp at hc
  exact ⟨a, a', a'', xs, b, b', b'', ys, c, cs, rfl, rfl, rfl⟩

theorem regValue_nil' (st : BasisState) : regValue [] st = 0 := rfl

theorem addCopy_counts : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    toffoliCount (addCopy x y carry cin) = n ∧
    measurementCount (addCopy x y carry cin) = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    simp [addCopy, eraseCarry, toffoliCount, measurementCount]
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addCopy, List.cons_ne_nil, if_false, toffoliCount_append,
        measurementCount_append, h.1, h.2, majority, eraseCarry, toffoliCount, measurementCount]
    omega

theorem regValue_cons' (a : Wire) (r : List Wire) (st : BasisState) :
    regValue (a :: r) st = (st a).toNat + 2 * regValue r st := by
  cases h : st a <;> simp [regValue, h]

theorem copy_affine (A A' B B' C : Bool)
    (hX : A.toNat + 2*A'.toNat < 1 ∨ 3 ≤ A.toNat + 2*A'.toNat)
    (hS : (1 ≤ B.toNat+2*B'.toNat ∧ B.toNat+2*B'.toNat < 3) ↔
      (1 ≤ (A.toNat+2*A'.toNat+(B.toNat+2*B'.toNat)+C.toNat)%4 ∧
      (A.toNat+2*A'.toNat+(B.toNat+2*B'.toNat)+C.toNat)%4 < 3)) :
    carryBit A B C = C := by
  revert hX hS
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> decide
theorem addCopy_eq : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    (cin :: (x ++ y ++ carry)).Nodup → ∀ (s : State) (m : List Bool),
    (∀ w ∈ carry, s.basis w = false) →
    (regValue x s.basis < 2^n ∨ 3 * 2^n ≤ regValue x s.basis) →
    ((2^n ≤ regValue y s.basis ∧ regValue y s.basis < 3*2^n) ↔
      (2^n ≤ (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^(n+2) ∧
        (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^(n+2) < 3*2^n)) →
    run (addCopy x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc hnd s m hclean hX hS
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hbc : b ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hb'c : b' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hcc : cin ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hzero : s.basis c = false := hclean c (by simp)
    have hK : carryBit (s.basis a) (s.basis b) (s.basis cin) =
        (s.basis cin) := by
      apply copy_affine _ (s.basis a') _ _ _
      · simpa [regValue_cons', regValue_nil'] using hX
      · simpa [regValue_cons', regValue_nil'] using hS
    have hm1 : measurementCount ([.CX cin c] : Program) = 0 := rfl
    have hm2 : measurementCount (majority a b cin c) = 0 := rfl
    have hmid : run ([.CX cin c] : Program) [] s = run (majority a b cin c) [] s := by
      rw [majority_correct _ _ _ _ h4]
      simp only [run]
      apply State.extensionality
      · rfl
      · funext w
        simp only [writeBit, Function.update]
        by_cases hwc : w = c
        · subst hwc
          simp [hbc, hb'c, hcc, hzero, hK]
        · simp [hwc]
    simp only [addCopy, addInPlace, if_pos (rfl : ([] : List Wire) = []), List.append_assoc]
    exact run_head_congr _ _ _ m s hm1 hm2 hmid
  | succ n ih =>
    intro x y carry cin hy hx hc hnd s m hclean hX hS
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append] at this ⊢; omega
    have hcx : c ∉ a' :: a'' :: as := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hcy : c ∉ b' :: b'' :: bs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hccs : c ∉ cs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hzero : s.basis c = false := hclean c (by simp)
    let A := s.basis a
    let B := s.basis b
    let C := s.basis cin
    let s1 : State := ⟨s.phase, writeBit s.basis c (carryBit A B C)⟩
    have hfirst (record : List Bool) : run (majority a b cin c) record s = s1 := by
      rw [majority_correct _ _ _ _ h4]; simp [s1, hzero, A, B, C]
    have hs1 (w : Wire) (hw : w ≠ c) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
    have hclean' : ∀ d ∈ cs, s1.basis d = false := by
      intro d hd; rw [hs1 d (fun h => hccs (h ▸ hd))]; exact hclean d (by simp [hd])
    have hxs : regValue (a' :: a'' :: as) s1.basis = regValue (a' :: a'' :: as) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcx (h ▸ hw)))
    have hys : regValue (b' :: b'' :: bs) s1.basis = regValue (b' :: b'' :: bs) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcy (h ▸ hw)))
    have hc1 : s1.basis c = carryBit A B C := by simp [s1, writeBit]
    have hp1 : 2^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    have hp3 : 2^(n+1+2) = 2 * 2^(n+2) := by rw [show n+1+2 = (n+2)+1 by omega, pow_succ]; ring
    rw [regValue_cons' a, regValue_cons' b] at hS
    rw [regValue_cons' a] at hX
    have step := sum_value_step A B C (regValue (a' :: a'' :: as) s.basis)
      (regValue (b' :: b'' :: bs) s.basis) (n+2)
    have hsb : (sumBit A B C).toNat ≤ 1 := by cases sumBit A B C <;> decide
    have hA : (s.basis a).toNat ≤ 1 := by cases s.basis a <;> decide
    have hX' : regValue (a' :: a'' :: as) s1.basis < 2^n ∨
        3 * 2^n ≤ regValue (a' :: a'' :: as) s1.basis := by
      rw [hxs]; omega
    have hB : (s.basis b).toNat ≤ 1 := by cases s.basis b <;> decide
    have hS' :
        (2^n ≤ regValue (b' :: b'' :: bs) s1.basis ∧
          regValue (b' :: b'' :: bs) s1.basis < 3*2^n) ↔
        (2^n ≤ (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2) ∧
          (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2) < 3*2^n) := by
      rw [hxs,hys,hc1]
      change (sumBit A B C).toNat + 2 * ((regValue (a' :: a'' :: as) s.basis +
        regValue (b' :: b'' :: bs) s.basis + (carryBit A B C).toNat) % 2^(n+2)) =
        ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
          (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+2+1) at step
      rw [show n+2+1 = n+1+2 by omega] at step
      generalize (regValue (a' :: a'' :: as) s.basis + regValue (b' :: b'' :: bs) s.basis +
        (carryBit A B C).toNat) % 2^(n+2) = S' at step ⊢
      generalize ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
        (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+1+2) = S at step hS
      omega
    have hmc : measurementCount (addCopy (a' :: a'' :: as) (b' :: b'' :: bs) cs c) =
        measurementCount (addInPlace (a' :: a'' :: as) (b' :: b'' :: bs) cs c) := by
      rw [(addCopy_counts n _ _ _ c (by simpa using hy) (by simpa using hx)
          (by simpa using hc)).2,
        (addInPlace_counts _ _ _ c (by simpa using hx) (by simpa using hc)).2]
      simp only [List.length_cons] at hy ⊢
      omega
    have hm0 : measurementCount (majority a b cin c) = 0 := rfl
    simp only [addCopy, addInPlace, List.cons_ne_nil, if_false]
    rw [List.append_assoc (majority a b cin c ++ _), List.append_assoc (majority a b cin c ++ _)]
    apply run_mid_congr _ _ _ _ m s hm0 hmc
    intro record
    rw [hfirst]
    exact ih _ _ _ c (by simpa using hy) (by simpa using hx) (by simpa using hc) hnd' s1 record
      hclean' hX' hS'

end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
def signedAddCopy (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ addCopy x y carry q ++ signComplement q x

def Shape (n V : Nat) : Prop := V < 2^n ∨ 3*2^n ≤ V
def Band (n V : Nat) : Prop := 2^n ≤ V ∧ V<3*2^n

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

theorem signedAddCopy_eq (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (clean : ∀ w ∈ cs, s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Band n (regValue y s.basis) ↔ Band n (regValue y (run (signedAdd q x y cs) [] s).basis)) :
    run (signedAddCopy q x y cs) m s=run (signedAdd q x y cs) m s := by
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
    rw [run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have add := addInPlace_correct x y cs q hn (hx.trans hy.symm) hc u [] clean'
  have uy : regValue y u.basis=regValue y s.basis := by
    exact regValue_congr _ _ _ (fun w hw => fan.2.1 w
      (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw)))
  have us : Band n (regValue y u.basis) ↔
      Band n ((regValue x u.basis+regValue y u.basis+(u.basis q).toNat)%2^(n+2)) := by
    rw [←uy,old,add.2.2,hy] at sum
    exact sum
  have eq (r : List Bool) := addCopy_eq n x y cs q hy (hx.trans hy.symm)
    hc hn u r clean' ux us
  simp only [signedAddCopy,signedAdd,List.append_assoc]
  rw [run_zero_head _ _ m s zx,run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq]
  have mc := addCopy_counts n x y cs q hy (hx.trans hy.symm) hc
  have mo := addInPlace_counts x y cs q (hx.trans hy.symm) hc
  rw [mc.2,mo.2,hy]
  rfl
def recordCopy (sx sy q : Wire) (x y cs : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAddCopy q x y cs ++ skywalkSignToggle sx sy q

theorem signedAddCopy_counts (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length) :
    toffoliCount (signedAddCopy q x y cs)=n ∧ measurementCount (signedAddCopy q x y cs)=n+1 := by
  have h := addCopy_counts n x y cs q hy (hx.trans hy.symm) hc
  simp only [signedAddCopy,toffoliCount_append,measurementCount_append,
    (signComplement_counts q x).1,(signComplement_counts q x).2,h.1,h.2]
  exact ⟨by omega,by omega⟩

theorem toggle_frame (sx sy q : Wire) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (w : Wire) (hw : w≠q) :
    (run (skywalkSignToggle sx sy q) m s).basis w=s.basis w := by
  rw [skywalkSignToggle_correct sx sy q hqx hqy]
  simp [writeBit,hw]

theorem recordCopy_eq (n : Nat) (sx sy q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (clean : ∀w∈cs,s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Band n (regValue y s.basis) ↔ Band n (regValue y (run (signedRecord sx sy q x y cs) [] s).basis)) :
    run (recordCopy sx sy q x y cs) m s=run (signedRecord sx sy q x y cs) m s := by
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
    rw [run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have uy : regValue y u.basis=regValue y s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  rw [←uy,old] at sum
  have eq (r : List Bool) := signedAddCopy_eq n q x y cs hx hy hc hn u r uc (ux ▸ source) sum
  have mc := (signedAddCopy_counts n q x y cs hx hy hc).2
  have mo := (signedWord_counts q x y cs (hx.trans hy.symm) hc).2.1
  simp only [recordCopy,signedRecord,List.append_assoc]
  rw [run_zero_head _ _ m s zx,run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq,mc,mo,hy]
  rfl
def narrowCopy (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  recordCopy L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

theorem record_source (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0) :
    regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) m s).basis = regValue L.xp s.basis := by
  have h := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
    (signedRegValue L.xp s.basis) (signedRegValue L.yp s.basis) s m ⟨hq,rfl,rfl,clean⟩
  have eq := (signedRegValue_eq_iff L.xp _ _).mp h.2.2.1
  exact regValue_congr _ _ _ eq

theorem narrowCopy_eq (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0)
    (source : Shape n (regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis))
    (sum : Band n (regValue L.yp s.basis) ↔ Band n (regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis)) :
    run (narrowCopy L (n+2)) m s=run (narrowSignedRecord L (n+2)) m s := by
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
  have eq (r : List Bool) := recordCopy_eq n L.sx L.sy L.q L.xp L.yp L.carryLow
    hw.x hw.y (hw.carry.trans hw.y.symm) (L.short_nodup hn) qx qy s r clean' source sum
  have mc := signedAddCopy_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have rz := (skywalkSignToggle_counts L.sx L.sy L.q).2
  have old := (signedWord_counts L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)).2.1
  have counts : measurementCount (recordCopy L.sx L.sy L.q L.xp L.yp L.carryLow)=
      measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) := by
    simp only [recordCopy,signedRecord,measurementCount_append,rz,mc.2,old,hw.y]
    omega
  simp only [narrowCopy,narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
  rw [run_append,run_append,run_take,run_take,eq,counts]
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic Baselines Challenge RecordedQuantum
theorem addCopy_wires (x y carry : List Wire) (cin : Wire) :
    wires (addCopy x y carry cin) ⊆ (cin :: (x ++ y ++ carry)).toFinset := by
  induction x generalizing y carry cin with
  | nil => simp [addCopy, wires]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [addCopy, wires]
      | cons b bs =>
        cases bs with
        | nil =>
          intro w hw
          simp only [addCopy, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.notMem_empty, or_false] at hw
          simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
          tauto
        | cons b' bs => simp [addCopy, wires]
    | cons a' as =>
      cases y with
      | nil => simp [addCopy, wires]
      | cons b bs =>
        cases bs with
        | nil => simp [addCopy, wires]
        | cons b' bs =>
          cases carry with
          | nil => simp [addCopy, wires]
          | cons c cs =>
            have hr := ih (b' :: bs) cs c
            have hm : wires (majority a b cin c) = {a, b, cin, c} := by
              ext w; simp [majority, wires, Instr.wires]; tauto
            have he := eraseCarry_wires a b cin c
            intro w hw
            simp only [addCopy, wires_append, Finset.mem_union, he] at hw
            simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
            rcases hw with ((h | h) | h) | h
            · split_ifs at h
              · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
                  Finset.mem_singleton, Finset.notMem_empty, or_false] at h
                tauto
              · rw [hm] at h
                simp only [Finset.mem_insert, Finset.mem_singleton] at h
                tauto
            · have := hr h
              simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at this
              tauto
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h
              tauto
            · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
                Finset.mem_singleton, Finset.notMem_empty, or_false] at h
              tauto

theorem addCopy_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: x ++ y ++ carry).Nodup) : GatePhysical (addCopy x y carry cin) := by
  induction x generalizing y carry cin with
  | nil => simp [addCopy, GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases y with
      | nil => simp [addCopy, GatePhysical]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [addCopy, GatePhysical]
        | nil =>
          have hab : a ≠ b := by
            intro e; subst b
            have h := List.nodup_iff_count.mp hn a
            simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h
            omega
          have hcb : cin ≠ b := by
            intro e; subst cin
            have h := List.nodup_iff_count.mp hn b
            simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h
            omega
          simp [addCopy, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hab, hcb]
    | cons a' xs =>
      cases y with
      | nil => simp [addCopy, GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [addCopy, GatePhysical]
        | cons b' ys =>
          cases carry with
          | nil => simp [addCopy, GatePhysical]
          | cons k ks =>
            have hs : [a,b,cin,k,b'].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons, List.count_append, List.count_nil] at h ⊢; omega
            have ht : (k :: (a'::xs) ++ (b'::ys) ++ ks).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons, List.count_append] at h ⊢; omega
            have hs4 : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hs q
              simp only [List.count_cons, List.count_nil] at h ⊢; omega
            have htail := ih (b'::ys) ks k ht
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
              not_or, not_false_eq_true, and_true] at hs
            rw [addCopy]
            simp only [gatePhysical_append]
            refine ⟨⟨⟨?_, htail⟩, eraseCarry_physical _ _ _ _⟩, ?_⟩
            · split_ifs
              · simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hs.2.1.2.1, hs.2.2.1.1,
                  Ne.symm hs.2.2.2]
              · exact majority_physical _ _ _ _ hs4
            · have hcb : cin ≠ b := Ne.symm hs.2.1.1
              simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hs.1.1, hcb]

theorem signedAddCopy_support (q : Wire) (x y cs : List Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (signedAddCopy q x y cs) ⊆ wires (signedAdd q x y cs) := by
  rw [(signedWord_wires q x y cs hx hc).1]
  have fan : wires (signComplement q x) ⊆ (q::(x++y++cs)).toFinset := by
    intro w hw
    have h := signComplement_wires_subset q x hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  simp only [signedAddCopy,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fan,addCopy_wires x y cs q⟩,fan⟩

theorem narrowCopy_counts (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    toffoliCount (narrowCopy L (n+2))+1=toffoliCount (narrowSignedRecord L (n+2)) ∧
      measurementCount (narrowCopy L (n+2))=measurementCount (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have h := signedAddCopy_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have old := narrowSignedRecord_counts L (n+2) hw
  have z := skywalkSignToggle_counts L.sx L.sy L.q
  have f := signComplement_counts L.q L.yhigh
  simp only [narrowCopy,recordCopy,v.1,v.2.1,v.2.2.1,v.2.2.2,
    toffoliCount_append,measurementCount_append,z.1,z.2,h.1,h.2,f.1,f.2,old.1,old.2.1]
  exact ⟨by omega,by omega⟩

theorem narrowCopy_support (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    wires (narrowCopy L (n+2)) ⊆ wires (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have sub := signedAddCopy_support L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [narrowCopy,narrowSignedRecord,recordCopy,signedRecord,v.1,v.2.1,v.2.2.1,v.2.2.2,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub)
    (Finset.Subset.refl _)) (Finset.Subset.refl _)

theorem signedAddCopy_physical (q : Wire) (x y cs : List Wire) (hn : (q::(x++y++cs)).Nodup) :
    GatePhysical (signedAddCopy q x y cs) := by
  have qx : q∉x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x qx
  have top := addCopy_physical x y cs q hn
  simp only [signedAddCopy,gatePhysical_append]
  exact ⟨⟨fan,top⟩,fan⟩

theorem narrowCopy_physical (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) : GatePhysical (narrowCopy L (n+2)) := by
  have v := L.views (n+2) hw
  have nd := L.short_nodup hn
  have qx : L.sx≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,qx,qy]
  have top := signedAddCopy_physical L.q L.xp L.yp L.carryLow nd
  have fan := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowCopy,recordCopy,v.1,v.2.1,v.2.2.1,v.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨toggle,top⟩,toggle⟩,fan⟩

theorem top_slots_le_old (x y cs : List Wire) (c : Wire) :
    gateSlots (addCopy x y cs c) ≤ gateSlots (addInPlace x y cs c) := by
  induction x generalizing y cs c with
  | nil => simp [addCopy,addInPlace]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [addCopy,addInPlace]
      | cons b bs => cases bs <;> simp [addCopy,addInPlace]
    | cons a' as =>
      cases y with
      | nil => simp [addCopy,addInPlace]
      | cons b bs =>
        cases bs with
        | nil => simp [addCopy,addInPlace]
        | cons b' bs =>
          cases cs with
          | nil => simp [addCopy,addInPlace]
          | cons d ds =>
            have h := ih (b'::bs) ds d
            simp only [addCopy,addInPlace,gateSlots_append] at h ⊢
            split_ifs <;> simp only [majority_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots] at h ⊢ <;> omega

theorem narrowCopy_slots (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (narrowCopy L (n+2)) ≤ gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := top_slots_le_old L.xp L.yp L.carryLow L.q
  simp only [narrowCopy,narrowSignedRecord,recordCopy,signedRecord,signedAddCopy,signedAdd,
    v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
end ECDSAAdd.Entrant.TickRanges
end

section
set_option exponentiation.threshold 512
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
def head (w : Nat → Wire) (i : Nat) : Program :=
  let L := W.compactSkywalkTickLayout w i
  (if i=224 ∨ (255 ≤ i  ∧  i ≤ 509) then W.repairedRoute L
    else skywalkRoute L.a0 L.b0 L.ah L.bh) ++ skywalkSignedHalf L.aSign L.ext

def tail (w : Nat → Wire) (i : Nat) : Program :=
  [.CX (W.compactSkywalkTickLayout w i).previous (W.compactSkywalkTickLayout w i).a0] ++
    W.compactSkywalkTickCleanup w i

def tick (w : Nat → Wire) (i : Nat) : Program :=
  if 225 ≤ i ∧ i ≤ 254 then
    head w i ++ narrowCopy (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
      (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i
  else TickGap.tick w i

theorem old_split (w : Nat → Wire) (i : Nat) (band : 225 ≤ i  ∧  i ≤ 254) :
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
theorem route_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.ext::L.carry) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis q=s.basis q := by
  have hn : ((L.previous::L.history::L.ext::L.carry)++
      (L.a0::L.b0::(L.ah++L.bh))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  apply run_preserves_outside
  intro hm
  have hh := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) hm
  exact List.disjoint_left.mp hd hq (List.mem_toFinset.mp hh)

theorem route_int_values (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (hp : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (hext : s.basis L.ext=false) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).phase=s.phase ∧
    signedRegValue (L.ext::L.ah) (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).1 ∧
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).2 ∧
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis L.a0=SkywalkRails.odd A := by
  have hna : L.ah≠[] := by simp [SkywalkIntegerLayout.ah]
  have hnb : L.bh≠[] := by simp [SkywalkIntegerLayout.bh]
  have hA := ha.symm.trans (signedRegValue_cons L.a0 L.ah s.basis hna)
  have hB := hb.symm.trans (signedRegValue_cons L.b0 L.bh s.basis hnb)
  have hpar : s.basis L.b0=(!s.basis L.a0) := by
    cases hca : s.basis L.a0 with
    | false =>
      cases hcb : s.basis L.b0 with
      | false =>
        simp [hca,hcb] at hA hB
        omega
      | true => rfl
    | true =>
      cases hcb : s.basis L.b0 with
      | false => rfl
      | true =>
        simp [hca,hcb] at hA hB
        omega
  have hctrl : s.basis L.a0=SkywalkRails.odd A := by
    cases hc : s.basis L.a0 with
    | false =>
      have he : A%2=0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
    | true =>
      have he : A%2≠0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  obtain ⟨hf,_,hctl,hlo,hrawA,hrawB⟩ := skywalkRoute_correct L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv) s m hpar
  have he0 : t.basis L.ext=false :=
    (route_aux_frame L hv s m L.ext (by simp)).trans hext
  have hsa : signedRegValue L.ah t.basis=
      if s.basis L.a0 then signedRegValue L.bh s.basis else signedRegValue L.ah s.basis := by
    have hh := congrArg (signedDecode L.ah.length) hrawA
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  have hsb : signedRegValue L.bh t.basis=
      if s.basis L.a0 then signedRegValue L.ah s.basis else signedRegValue L.bh s.basis := by
    have hh := congrArg (signedDecode L.bh.length) hrawB
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  refine ⟨hf,?_,?_,hctl.trans hctrl⟩
  · rw [signedRegValue_cons L.ext L.ah t.basis hna,he0,hsa]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

  · change signedRegValue (L.b0::L.bh) t.basis=_
    rw [signedRegValue_cons L.b0 L.bh t.basis hnb,hlo,hsb]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega


theorem head_odd_value (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (par : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (he : s.basis L.ext=false) :
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh ++
      skywalkSignedHalf L.aSign L.ext) m s).basis=(SkywalkRails.route A B).2 := by
  have route := (route_int_values L hv A B par s [] ha hb he).2.2.1
  have zero := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh (L.high_lengths hv) (L.route_nodup hv)).2
  rw [run_append,zero,List.take_zero,List.drop_zero]
  have extaway (q : Wire) (hq : q∈L.b) : q≠L.ext := by
    intro hh
    subst q
    have cnt := List.nodup_iff_count.mp hv.nodup L.ext
    have mem := List.count_pos_iff.mpr hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.b,List.count_cons,List.count_append,
      List.count_nil,List.count_singleton,beq_self_eq_true,if_true] at cnt mem
    omega
  apply Eq.trans (show signedRegValue L.b _=signedRegValue L.b
      (run (skywalkRoute L.a0 L.b0 L.ah L.bh) [] s).basis from ?_) route
  unfold signedRegValue
  congr 1
  exact regValue_congr _ _ _ (fun q hq =>
    (skywalkSignedHalf_frame L.aSign L.ext _ m).2 q (extaway q hq))

theorem band_signed (n V : Nat) (hv : V<2^(n+2)) :
    Band n V ↔ signedDecode (n+2) V< -((2^n:Nat):Int) ∨
      ((2^n:Nat):Int)≤signedDecode (n+2) V := by
  have p2 : 2^(n+2)=4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1)=2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold Band signedDecode
  split_ifs <;> omega

theorem repaired_output_info (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0<x) (hx : x<p) (cop : x.Coprime p)
    (band : 225 ≤ i ∧ i ≤ 254) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    Shape (n-2) (regValue (L.half.take n) (run (W.repairedTick w i) m s).basis) ∧
      (Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
        Band (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis)) := by
  dsimp only
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have hi : i<512 := by omega
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  have cap := W.iter_sum_late x p i hx0 hpo hp gap hx (by omega)
  have early := early_gap x i hx0 hx band
  obtain ⟨G,S,enc⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at enc
  change r=SkywalkRails.encode G S (z.u:Int) (z.v:Int) at enc
  have u0 : 0 ≤ (z.u:Int) := by omega
  have v0 : 0 < (z.v:Int) := by exact_mod_cast valid.1
  have vo : (z.v:Int)%2=1 := by exact_mod_cast valid.2.1
  have cp : (z.u:Int)+(z.v:Int)<2*(H:Int) := by
    change z.u+z.v<2^256 at cap
    have : 2^256=2*H := by norm_num [H]
    exact_mod_cast (this ▸ cap)
  have eg : (z.u:Int)+(z.v:Int)<(H:Int) ∨ (H:Int) ≤ (z.v:Int) := by
    change z.u+z.v<H ∨ H≤z.v at early
    exact_mod_cast early
  have bounds := encode_boundary G S (z.u:Int) (z.v:Int) u0 v0 vo cp eg
  rw [←enc] at bounds
  have par : (r.a+r.b)%2=1 := by rw [enc]; exact SkywalkRails.encode_odd_sum G S _ _ vo
  have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp gap hx cop hi s hs
  have fit := W.narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp gap hx cop hi
  have out := W.compactSkywalkTickOutput_spec w i hi hn _ _ _ fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s [] input
  have nw : n=257 := by unfold n W.compactSkywalkTickPostWidth W.narrowSkywalkWidth; omega
  have lenA : n ≤ L.half.length := by
    rw [W.compactSkywalkTick_half w i hi,wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i hi).2.2.1
  have lenB : L.b.length=n := by
    rw [W.compactSkywalkTick_b w i hi,wireBlock_length]
    unfold n W.compactSkywalkTickPostWidth W.compactSkywalkTickPreWidth
      W.narrowSkywalkRouteWidth W.narrowSkywalkWidth
    omega
  have av : (W.compactSkywalkTickARelease w i).retained=L.half.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenA
  have bv : (W.compactSkywalkTickBRelease w i).retained=L.b.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) (by change n ≤ L.b.length; omega)
  have a := out.2.1
  have b := out.2.2.1
  rw [av] at a
  rw [bv] at b
  have lenA' : (L.half.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenA]
  have lenB' : (L.b.take n).length=n := by simp [List.length_take,lenB]
  have old : run (W.repairedTick w i) m s=run (W.compactSkywalkTick w i) [] s :=
    W.repairedTick_eq w hn x p i hp0 hx0 hpo hp gap hx cop hi s m hs
  have valO : signedRegValue (L.b.take n) (run (head w i) m s).basis=
      (SkywalkRails.route r.a r.b).2 := by
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have he : ¬(i=224 ∨ (255 ≤ i ∧ i ≤ 509)) := by omega
    change signedRegValue _ (run _ m s).basis=_
    rw [head,if_neg he,List.take_of_length_le (by omega : L.b.length≤n)]
    exact head_odd_value L hv r.a r.b par s m input.1 input.2.1 input.2.2.2.1
  have rawShape : Shape (n-2) (regValue (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis) := by
    unfold signedRegValue at a
    rw [lenA'] at a
    rw [nw] at a ⊢
    apply shape_of_signed 255 _ (by have h := regValue_lt (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis; rw [lenA',nw] at h; exact h)
    · rw [a]; exact bounds.1
    · rw [a]; exact bounds.2.1
  refine ⟨old ▸ rawShape,?_⟩
  rw [old]
  have oy : Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
      Outside (SkywalkRails.route r.a r.b).2 := by
    have hh := band_signed 255 (regValue (L.b.take n) (run (head w i) m s).basis)
      (by have h := regValue_lt (L.b.take n) (run (head w i) m s).basis; rw [lenB',nw] at h; simpa only [nw] using h)
    unfold signedRegValue at valO
    rw [lenB',nw] at valO
    simpa only [nw,Nat.reduceSub,valO,Outside,H] using hh
  have ky : Band (n-2) (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis) ↔
      Outside (SkywalkRails.step r).k := by
    have hh := band_signed 255 (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
      (by have h := regValue_lt (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis; rw [lenB',nw] at h; simpa only [nw] using h)
    unfold signedRegValue at b
    rw [lenB',nw] at b
    simpa only [nw,Nat.reduceSub,b,Outside,H] using hh
  exact oy.trans (bounds.2.2.trans ky.symm)
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
theorem tick_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0 < x) (hx : x < p) (cop : x.Coprime p) (hi : i < 512)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (tick w i) m s=run (W.repairedTick w i) m s := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  by_cases band : 225 ≤ i ∧ i ≤ 254
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
    have sizes := repaired_output_info w hn x i hx0 hx cop band s m hs
    have keep (r : List Wire) (hr : r⊆L.half.take n++L.b.take n) :
        regValue r (run (W.repairedTick w i) m s).basis=regValue r v.basis := by
      rw [whole]
      apply regValue_congr
      intro q hq
      exact tail_prefix w i hi hn v _ q (hr hq)
    have shapeX : Shape (n-2) (regValue (L.half.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_left _ hq)]
      exact sizes.1
    have bandY : Band (n-2) (regValue (L.b.take n) u.basis) ↔
        Band (n-2) (regValue (L.b.take n) v.basis) := by
      have yu : run (head w i) m s=u := by dsimp only [u,P]; rw [run_take]
      have yv := keep (L.b.take n) (by intro q hq; exact List.mem_append_right _ hq)
      have sy : Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
          Band (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis) := sizes.2
      rw [yu,yv] at sy
      exact sy
    have record0 : (run Q [] u).basis=v.basis := run_basis_records Q u u [] (m.drop (measurementCount P)) rfl
    have orig := narrowSkywalkRecord_views L hv n (by omega) nlen
    have views := R.views n hw
    have xx : R.xp=L.half.take n := by rw [←views.1]; rw [orig.1]
    have yy : R.yp=L.b.take n := by rw [←views.2.1]; rw [orig.2.1]
    have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp gap hx cop hi s hs
    have uq : u.basis R.q=false := by
      apply (head_aux w i hi hn s _ L.history (List.mem_cons_self)).trans
      exact input.2.2.2.2.1
    have clean : regValue R.carryLow u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have qm : q∈L.carry := List.mem_of_mem_take hq
      apply (head_aux w i hi hn s _ q (List.mem_cons_of_mem _ qm)).trans
      exact (regValue_zero _ _).mp input.2.2.2.2.2 q qm
    have eq (r : List Bool) : run (narrowCopy R n) r u=run Q r u := by
      have a : Shape (n-2) (regValue R.xp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,xx,record0]
        exact shapeX
      have b : Band (n-2) (regValue R.yp u.basis) ↔
          Band (n-2) (regValue R.yp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,yy,record0]
        exact bandY
      simpa only [n2] using narrowCopy_eq (n-2) R hw' nd u r uq clean a b
    have counts : measurementCount (narrowCopy R n)=measurementCount Q := by
      simpa only [n2] using (narrowCopy_counts (n-2) R hw').2
    simp only [tick,if_pos band]
    rw [old_split _ _ band]
    change run ((P++narrowCopy R n)++E) m s=run ((P++Q)++E) m s
    conv_lhs => rw [List.append_assoc,run_append P (narrowCopy R n++E)]
    conv_rhs => rw [List.append_assoc,run_append P (Q++E)]
    change run (narrowCopy R n++E) (m.drop (measurementCount P)) u = run (Q++E) (m.drop (measurementCount P)) u
    rw [run_append (narrowCopy R n) E,run_append Q E]
    rw [run_take (narrowCopy R n),run_take Q,eq,counts]
  · simpa only [tick,if_neg band] using
      TickGap.tick_eq w hn x p i hp0 hx0 hpo hp (by norm_num [p]) hx cop hi s m hs

def due (i : Nat) : Nat := if 225 ≤ i ∧ i ≤ 254 then 1 else TickGap.due i

theorem tick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (tick w i)+due i=toffoliCount (W.repairedTick w i)  ∧
    measurementCount (tick w i)=measurementCount (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_counts (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,due,if_pos band,toffoliCount_append,measurementCount_append]
    exact ⟨by omega,by omega⟩
  · simpa only [tick,if_neg band,due,if_neg band] using TickGap.tick_counts w i hi hn

theorem tick_support (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    wires (tick w i) ⊆ wires (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_support (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)
  · simpa only [tick,if_neg band] using TickGap.tick_support w i hi hn

theorem tick_slots (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    Challenge.gateSlots (tick w i)  ≤  Challenge.gateSlots (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_slots (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,Challenge.gateSlots_append]
    omega
  · simpa only [tick,if_neg band] using TickGap.tick_slots w i hi hn

theorem tick_physical (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (tick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_physical (n-2) R hw' (narrowSkywalkRecord_nodup L hv n (by omega) nlen)
    simp only [n2] at h
    dsimp only [R,n,L] at h
    have old := W.repairedTick_physical w i hi hn
    rw [old_split _ _ band] at old
    simp only [tick,if_pos band,gatePhysical_append] at old ⊢
    exact ⟨⟨old.1.1,h⟩,old.2⟩
  · simpa only [tick,if_neg band] using TickGap.tick_physical w i hi hn
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
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
    (tick_eq base base_pool_nodup x i hx0 hx cop hi raw m hraw)

theorem block_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i++FirstNonzeroCodec.pack8first base i) m s=run (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) m s := by
  rw [run_append (tick base i),run_append (W.repairedTick base i),run_take (tick base i),run_take (W.repairedTick base i)]
  rw [tick_eq5 x hx0 hx i hi s m hs,(tick_counts base i hi base_pool_nodup).2]

def forward (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)++forward (i+1) n

/-- The replacement forward prefix has exactly the existing logical trajectory. -/
theorem forward_gen (x : Nat) (hx0 : 0 < x) (hx : x < p) (n : Nat) :
    ∀ i, 1 ≤ i → i+n ≤ 512 → ∀(s : State)(m : List Bool),
    W.CompressedCompactStage5 base x p i s.basis →
    run (forward i n) m (pullState (sig (i-1)) s)=
      pullState (sig (i+n-1)) (run (Stack5.forward5 base i n) m s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  induction n with
  | zero => intro i _ _ s m _; simp only [forward,Stack5.forward5,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 hb s m hs
    have hi : i ≤ 511 := by omega
    have z := StackOB5.stage_zero x i (by omega) s.basis hs
    rw [pull_step i hi s z.1 z.2]
    have cnt : measurementCount (renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i))=
        measurementCount (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) := by
      rw [(renameProgram_counts (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)).2]
      simp only [measurementCount_append,(tick_counts base i (by omega) base_pool_nodup).2]
    rw [forward,Stack5.forward5,run_append _ (forward (i+1) n),run_append _ (Stack5.forward5 base (i+1) n),cnt,StackOB5.forward_step_records,OB5.run_rename i hi]
    rw [block_eq x hx0 hx i (by omega) s _ hs]
    rw [StackOB5.forward_step_eq base base_pool_nodup x p i hp0 hx0 hpo hp hpGap hx cop _ _ hs]
    have next := (Stack5.step_spec base base_pool_nodup StackOB5.historyAbove x p i hp0 hx0 hpo hp hpGap hx
      cop (by omega) s (m.take (measurementCount (W.repairedTick base i++History5.packAfter base i))) hs).2
    have step := ih (i+1) (by omega) (by omega) _ (m.drop (measurementCount (W.repairedTick base i++History5.packAfter base i))) next
    rw [show i+1-1=i by omega] at step
    rw [step,show i+1+n-1=i+(n+1)-1 by omega]

theorem forward_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (i n : Nat) (h1 : 1 ≤ i) (hi : i+n ≤ 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (forward i n) m (pullState (sig (i-1)) s)=run (StackOB5.forward i n) m (pullState (sig (i-1)) s) := by
  rw [forward_gen x hx0 hx n i h1 hi s m hs,StackOB5.forward_gen x hx0 hx n i h1 hi s m hs]

def count (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => due i+count (i+1) n

theorem forward_metrics (i n : Nat) (hi : i+n ≤ 512) :
    toffoliCount (forward i n)+count i n=toffoliCount (StackOB5.forward i n)  ∧
    measurementCount (forward i n)=measurementCount (StackOB5.forward i n)  ∧
    Challenge.gateSlots (forward i n) ≤ Challenge.gateSlots (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward,count]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have stepCounts := tick_counts base i (by omega) base_pool_nodup
    have slots := tick_slots base i (by omega) base_pool_nodup
    have a := renameProgram_counts (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)
    have b := renameProgram_counts (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    have c := Baselines.rename_gateSlots (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)
    have d := Baselines.rename_gateSlots (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    simp only [forward,StackOB5.forward,count,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at a b c d ⊢
    exact ⟨by omega,by omega,by omega⟩

theorem forward_support (i n : Nat) (hi : i+n ≤ 512) : wires (forward i n)⊆wires (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward]
  | succ n ih =>
    have fresh := tick_support base i (by omega) base_pool_nodup
    have block : wires (tick base i++FirstNonzeroCodec.pack8first base i) ⊆ wires (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) := by
      simp only [wires_append]
      exact Finset.union_subset_union fresh (Finset.Subset.refl _)
    have ren : wires (renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)) ⊆
        wires (renameProgram (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)) := by
      rw [renameProgram_support,renameProgram_support]
      exact Finset.image_mono (sig i) block
    simp only [forward,StackOB5.forward,wires_append]
    exact Finset.union_subset_union ren (ih (i+1) (by omega))

theorem forward_physical (i n : Nat) (hi : i+n ≤ 512) : GatePhysical (forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have stepPhysical := tick_physical base i (by omega) base_pool_nodup
    have codec := (FirstNonzeroCodec.packet_physical base base_pool_nodup i (by omega)).1
    have ren := gatePhysical_rename (sig i) (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr ⟨stepPhysical,codec⟩)
    simp only [forward,gatePhysical_append]
    exact ⟨ren,ih (i+1) (by omega)⟩

theorem count_508 : count 1 508=62 := by decide +kernel
end ECDSAAdd.Entrant.TickRanges
end

namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 History5

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- Return the final basis integer when both measurement outcomes preserve phase at every step. -/
def phaseClean508 : Program → Nat → Option Nat
  | [], b => some b
  | .X t :: p, b => phaseClean508 p (b ^^^ 2^t)
  | .CX c t :: p, b => phaseClean508 p (flipN_t8 b t (b.testBit c))
  | .CCX a c t :: p, b => phaseClean508 p (flipN_t8 b t (b.testBit a && b.testBit c))
  | .measureX t c₀ c₁ :: p, b =>
    let d := flipN_t8 b t (b.testBit t)
    if corrP_t8 c₀ false d = false ∧ corrP_t8 c₁ (b.testBit t) d = false then
      phaseClean508 p d
    else none

theorem phaseClean508_sound (p : Program) (b v : Nat) (h : phaseClean508 p b = some v) (m : List Bool) :
    runN_t8 p m (false,b) = (false,v) := by
  induction p generalizing b m with
  | nil =>
    simp [phaseClean508] at h
    simp [runN_t8,h]
  | cons g p ih =>
    cases g with
    | X t => exact ih _ h m
    | CX c t => exact ih _ h m
    | CCX a c t => exact ih _ h m
    | measureX t c₀ c₁ =>
      simp only [phaseClean508] at h
      split at h
      · rename_i clean
        obtain ⟨h0,h1⟩ := clean
        have suffix :=  ih _ h m.tail
        cases m with
        | nil => simpa [runN_t8,List.headD,h0,h1] using suffix
        | cons z ms => cases z <;> simpa [runN_t8,List.headD,h0,h1] using suffix
      · contradiction

def agree508 (p q : Program) (b : Nat) : Bool :=
  match phaseClean508 q b with
  | none => false
  | some v => decide (phaseClean508 p b = some v)

theorem agree508_sound (p q : Program) (b : Nat) (h : agree508 p q b = true) (m : List Bool) :
    runN_t8 p m (false,b) = runN_t8 q m (false,b) := by
  cases hq : phaseClean508 q b with
  | none => simp [agree508,hq] at h
  | some v =>
    have hp : phaseClean508 p b = some v := by simpa [agree508,hq] using h
    rw [phaseClean508_sound p b v hp, phaseClean508_sound q b v hq]

def forward6 : Program :=
  [.CX 525 790,
   .CX 789 790,
   .CX 527 528,
   .CX 787 528,
   .CCX 790 528 786,
   .CX 525 788,
   .CX 526 788,
   .CX 787 788,
   .CCX 788 524 1556,
   .CX 790 787,
   .CCX 787 786 1553,
   .CX 524 527,
   .CX 786 527,
   .CX 789 527,
   .CX 790 787,
   .CX 1553 787,
   .CCX 527 787 1554,
   .CX 525 526,
   .CX 1554 526,
   .CX 1556 526,
   .CX 523 1554,
   .CX 524 1554,
   .CX 525 1554,
   .CX 527 1554,
   .CX 1553 1554,
   .CCX 526 1554 529,
   .CX 523 1553,
   .CX 525 1553,
   .CX 786 1553,
   .CX 788 1553,
   .CCX 1553 526 1552,
   .CX 523 524,
   .CX 525 787,
   .CX 525 790,
   .CX 1554 1557,
   .CX 1552 1558,
   .CX 524 525,
   .CX 787 525,
   .CX 523 1553,
   .CX 524 1553,
   .CX 527 1553,
   .CX 786 1553,
   .CX 1552 1553,
   .CX 1554 1553,
   .CX 523 1554,
   .CX 524 1554,
   .CX 527 1554,
   .CX 529 1554,
   .CX 786 1554,
   .CX 1552 1554,
   .CX 523 1552,
   .CX 528 1552,
   .CX 786 1552,
   .CX 787 1552,
   .CX 788 1552,
   .CX 790 1552,
   .CX 1554 1552,
   .CX 1557 1552,
   .CX 524 528,
   .CX 527 528,
   .CX 529 528,
   .CX 787 528,
   .CX 788 528,
   .CX 790 528,
   .CX 1552 528,
   .X 527,
   .CX 523 527,
   .CX 524 527,
   .CX 525 527,
   .CX 526 527,
   .CX 529 527,
   .CX 786 527,
   .CX 1554 527,
   .CX 1557 527,
   .CX 1558 527,
   .CX 525 526,
   .measureX 787 [] [.Z 1552, .Z 523, .Z 529, .Z 1556, .Z 789, .CZ 1554 524, .CZ 1554 523, .CZ 1554 529, .CZ 1554 789, .CZ 1554 790, .CZ 1554 786, .CZ 1553 523, .CZ 1553 529, .CZ 1553 788, .CZ 1553 789, .CZ 527 789, .CZ 1552 789, .CZ 525 1556, .CZ 525 789, .CZ 524 523, .CZ 524 1556, .CZ 524 789, .CZ 523 529],
   .X 786,
   .measureX 786 [] [.Z 1553, .Z 1552, .Z 525, .Z 523, .Z 529, .Z 1558, .Z 788, .CZ 1554 524, .CZ 1553 524, .CZ 527 1552],
   .measureX 790 [] [.CZ 523 789],
   .measureX 789 [] [.Z 1554, .Z 1553, .Z 1552, .CZ 1554 523, .CZ 523 529, .CZ 523 1558, .CZ 523 1557],
   .measureX 1557 [] [.Z 527, .Z 1552, .CZ 1554 524, .CZ 527 524, .CZ 527 529, .CZ 527 788, .CZ 524 529],
   .measureX 1556 [] [.CZ 523 788, .CZ 524 788],
   .measureX 788 [] [.Z 1553, .Z 525, .Z 1558, .CZ 1554 524, .CZ 525 524, .CZ 524 529, .CZ 524 1558],
   .measureX 1558 [] [.Z 1553, .Z 529, .CZ 1554 525, .CZ 1553 527],
   .measureX 529 [] [.Z 1552, .CZ 1554 525, .CZ 527 1552, .CZ 1552 525],
   .CX 526 786]

theorem forward6_counts :
    toffoliCount forward6 = 6 ∧ measurementCount forward6 = 9 := by decide +kernel

theorem forward6_wires : wires forward6 ⊆ sitesT8.toFinset := by decide +kernel

theorem forward6_physical : GatePhysical forward6 := by
  simp (config := {maxSteps := 4000000}) [forward6,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]

abbrev previousForward508 : Program := tick508ExF ++ tickMF

def forward6_pair (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    agree508 forward6 previousForward508 (encN_t8 (pre508 g s uv.1 uv.2) sitesT8)

theorem forward6_table : pairs508.all forward6_pair = true := by decide +kernel

theorem forward6_forced (g s : Bool) (uv : Nat × Nat) (member : uv ∈ pairs508) (m : List Bool) :
    run forward6 m ⟨false,pre508 g s uv.1 uv.2⟩ = run previousForward508 m ⟨false,pre508 g s uv.1 uv.2⟩ := by
  have table := forward6_table
  simp only [List.all_eq_true] at table
  have row := table uv member
  simp only [forward6_pair,List.all_eq_true] at row
  have h := row g (by cases g <;> simp) s (by cases s <;> simp)
  have eqr := agree508_sound _ _ _ h m
  rw [tb_enc_t8 (pre508 g s uv.1 uv.2) sitesT8 (pre508_supp g s uv.1 uv.2)]
  simp only [run_sim_t8,eqr]

theorem forward6_resources :
    toffoliCount forward6 + 2 = toffoliCount previousForward508 ∧
    measurementCount forward6 = measurementCount previousForward508 ∧
    Challenge.gateSlots forward6 ≤ Challenge.gateSlots previousForward508 := by decide +kernel

theorem forward6_on_site (g s : Bool) (uv : Nat × Nat) (h : uv ∈ pairs508)
    (st : State) (bits : ∀ q ∈ sitesT8, st.basis q = pre508 g s uv.1 uv.2 q) (m : List Bool) :
    run forward6 m st = run previousForward508 m st := by
  apply forced_eqN forward6 previousForward508 sitesT8 (pre508 g s uv.1 uv.2) 9
    (recsUpTo 9) (take_recsUpTo 9) forward6_wires (by decide +kernel)
    (by decide +kernel) (by decide +kernel) _ st bits m
  intro r _
  rw [forward6_forced g s uv h r]
  exact ⟨rfl, fun _ _ => rfl⟩

end ECDSAAdd.Entrant

namespace ECDSAAdd.Entrant.ForwardSixPlacement
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 History5 OB5
open Rolling1588.Integer
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem at_stage (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (hs : Stage base isA x p 508 a.basis) (r : List Bool) :
    run forward6 r a = run (tick508ExF ++ tickMF) r a := by
  obtain ⟨g,s,uv,huv,bits⟩ := stage508_bitsT_new isA x hx0 hx a hs
  exact forward6_on_site g s uv huv a bits r

theorem place (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 508 a.basis) (r : List Bool) :
    run (renameProgram (sig 510) forward6) r (pullState (sig 507) a) =
    run (renameProgram (sig 508) tick508ExF ++ renameProgram (sig 510) tickMF)
      r (pullState (sig 507) a) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have z8 := stage_zero_gen isA x 508 508 (by omega) (by omega) a.basis stage
  have z9 := stage_zero_gen isA x 508 509 (by omega) (by omega) a.basis stage
  have z10 := stage_zero_gen isA x 508 510 (by omega) (by omega) a.basis stage
  have m8 : pullState (sig 507) a = pullState (sig 508) a := OB5.pull_step 508 (by omega) a z8.1 z8.2
  have m9 : pullState (sig 508) a = pullState (sig 509) a := OB5.pull_step 509 (by omega) a z9.1 z9.2
  have m10 : pullState (sig 509) a = pullState (sig 510) a := OB5.pull_step 510 (by omega) a z10.1 z10.2
  let b := run tick508ExF (r.take (measurementCount tick508ExF)) a
  have s9 : Stage base isA x p 509 b.basis := by
    have step := (Rolling1588.Integer.step_spec base isA base_pool_nodup StackOB5.historyAbove x p 508
      hp0 hx0 hpo hp gap hx cop (by omega) a (r.take (measurementCount tick508ExF)) stage).2
    simpa only [pack508 isA, List.append_nil, tick508ExF_explicit, b] using step
  have b9 := stage_zero_gen isA x 509 509 (by omega) (by omega) b.basis s9
  have b10 := stage_zero_gen isA x 509 510 (by omega) (by omega) b.basis s9
  have align : pullState (sig 508) b = pullState (sig 510) b :=
    (OB5.pull_step 509 (by omega) b b9.1 b9.2).trans (OB5.pull_step 510 (by omega) b b10.1 b10.2)
  rw [m8, run_append, (renameProgram_counts _ _).2, OB5.run_rename 508 (by omega)]
  change run (renameProgram (sig 510) forward6) r (pullState (sig 508) a) =
    run (renameProgram (sig 510) tickMF) (r.drop (measurementCount tick508ExF)) (pullState (sig 508) b)
  rw [align, m9, m10, OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
    at_stage isA x hx0 hx a stage, run_append]

end ECDSAAdd.Entrant.ForwardSixPlacement

namespace ECDSAAdd.Entrant.ForwardSixPlacement
open Arithmetic MappedCompressed Secp256k1 History5 OB5
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward

def prior : Program := renameProgram (sig 508) tick508ExF ++ renameProgram (sig 510) tickMF
def merged : Program := renameProgram (sig 510) forward6
def after (isA : Bool) : Program :=
  renameProgram (sig 510) (Rolling1588.packAtTick isA 510) ++ renameProgram (sig 511) tickF

theorem prior_resources : toffoliCount merged+2=toffoliCount prior ∧
    measurementCount merged=measurementCount prior ∧ Challenge.gateSlots merged ≤ Challenge.gateSlots prior := by
  have h := forward6_resources
  simpa only [merged, prior, previousForward508, toffoliCount_append, measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots] using h

theorem prior_support : wires merged ⊆ wires prior := by decide +kernel

theorem previous_shape (isA : Bool) :
    Rolling1588.stackForward isA = Rolling1588.forward isA 1 507 ++ (prior ++ after isA) := by
  have snoc := Rolling1588.Integer.forward_snoc isA 1 507
  have pack : Rolling1588.Integer.packFirst base isA 508=[] := by
    simp only [Rolling1588.Integer.packFirst,show ¬(508:Nat)=5 from by decide,if_false,
      Rolling1588.Integer.pack508 isA]
  rw [show (1:Nat)+507=508 by rfl,pack,List.append_nil,Rolling1588.Integer.forward_eq_packets,
    Rolling1588.Integer.forward_eq_packets,tick508ExF_explicit] at snoc
  rw [Rolling1588.stackForward,snoc]
  simp only [prior,after,renameProgram,List.map_append,List.append_assoc]

theorem prior_at_prefix (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis)
    (u r : List Bool) :
    run merged r (run (Rolling1588.forward isA 1 507) u s) =
    run prior r (run (Rolling1588.forward isA 1 507) u s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have init := Rolling1588.Integer.stage_one base isA x p s first
  have st := ((Rolling1588.Integer.regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p
    1 507 hp0 hx0 hpo hp gap hx cop (by omega)) s u init).2
  have start : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  have pre := Rolling1588.Integer.forward_gen isA x hx0 hx 507 1 (by omega) (by omega) s u init
  rw [start,Rolling1588.Integer.forward_eq_packets] at pre
  rw [pre]
  exact place isA x hx0 hx _ st r

theorem replace_at_prefix (P Q R : Program) (s : State) (m : List Bool)
    (counts : measurementCount P=measurementCount Q)
    (prefixSame : ∀ u, run P u s=run Q u s)
    (same : ∀ u v, run merged v (run Q u s)=run prior v (run Q u s)) :
    run (P ++ (merged ++ R)) m s = run (Q ++ (prior ++ R)) m s := by
  simp only [run_append P,run_append Q,run_append merged,run_append prior,counts,prior_resources.2.1]
  rw [prefixSame,same]

end ECDSAAdd.Entrant.ForwardSixPlacement

namespace ECDSAAdd.Entrant.MorningFour
open Arithmetic MappedCompressed Secp256k1 History5
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 2048

def tick507 : Program :=
  [.CX 787 524,
   .CX 788 525,
   .CX 789 526,
   .CX 790 527,
   .CCX 523 524 787,
   .CCX 523 525 788,
   .CCX 523 526 789,
   .CCX 523 527 790,
   .CX 787 524,
   .CX 788 525,
   .CX 789 526,
   .CX 790 527,
   .CX 528 791,
   .measureX 528 [] [.CZ 522 791],
   .CX 791 528,
   .CX 528 791,
   .CX 790 791,
   .CX 790 528,
   .CX 523 786,
   .CX 528 529,
   .X 1551,
   .CX 528 1551,
   .CX 790 1551,
   .CX 1551 524,
   .CX 1551 525,
   .CX 1551 526,
   .CX 1551 527,
   .CX 1551 528,
   .CX 524 786,
   .CX 524 1551,
   .CCX 786 1551 1556,
   .CX 524 1556,
   .CX 524 1551,
   .CX 524 786,
   .CX 525 787,
   .CX 525 1556,
   .CCX 787 1556 1557,
   .CX 525 1557,
   .CX 525 1556,
   .CX 525 787,
   .CX 526 788,
   .CX 526 1557,
   .CCX 788 1557 1558,
   .CX 526 1558,
   .CX 526 1557,
   .CX 526 788,
   .CX 527 789,
   .CX 527 1558,
   .CCX 789 1558 1559,
   .CX 527 1559,
   .CX 527 1558,
   .CX 527 789,
   .CX 528 790,
   .CX 1559 790,
   .measureX 1559 [] [.CZ 527 789, .CZ 527 1558, .CZ 789 1558],
   .CX 527 789,
   .CX 1558 789,
   .measureX 1558 [] [.CZ 526 788, .CZ 526 1557, .CZ 788 1557],
   .CX 526 788,
   .CX 1557 788,
   .measureX 1557 [] [.CZ 525 787, .CZ 525 1556, .CZ 787 1556],
   .CX 525 787,
   .CX 1556 787,
   .measureX 1556 [] [.CZ 524 786, .CZ 524 1551, .CZ 786 1551],
   .CX 524 786,
   .CX 1551 786,
   .CX 1551 524,
   .CX 1551 525,
   .CX 1551 526,
   .CX 1551 527,
   .CX 1551 528,
   .X 1551,
   .CX 528 1551,
   .CX 790 1551,
   .CX 1551 791,
   .CX 522 523,
   .CX 528 529,
   .CX 790 791]

abbrev incumbent6 : Program := ECDSAAdd.Entrant.forward6

def forward13 : Program :=
  [.CX 787 524,
   .CX 788 525,
   .CX 789 526,
   .CCX 523 524 787,
   .CCX 523 525 788,
   .CCX 523 526 789,
   .CX 787 524,
   .CX 788 525,
   .CX 789 526,
   .CX 528 791,
   .measureX 528 [] [.CZ 522 791],
   .CX 791 528,
   .CX 528 791,
   .CX 790 791,
   .CX 790 528,
   .CX 523 786,
   .CX 528 529,
   .X 1551,
   .CX 528 1551,
   .CX 790 1551,
   .CX 1551 524,
   .CX 1551 525,
   .CX 1551 526,
   .CX 1551 527,
   .CX 1551 528,
   .CX 524 786,
   .CX 524 1551,
   .CCX 786 1551 1556,
   .CX 524 1556,
   .CX 524 1551,
   .CX 524 786,
   .CX 525 787,
   .CX 525 1556,
   .CCX 787 1556 1557,
   .CX 525 1557,
   .CX 525 1556,
   .CX 525 787,
   .CX 526 788,
   .CX 526 1557,
   .CCX 788 1557 1558,
   .CX 526 1558,
   .CX 526 1557,
   .CX 526 788,
   .CX 527 789,
   .CX 527 1558,
   .CX 523 522,
   .CX 1558 789,
   .CCX 522 789 1554,
   .CX 1558 789,
   .CX 523 522,
   .X 1554,
   .CX 522 1554,
   .CX 523 1554,
   .CX 789 1554,
   .CX 1558 1554,
   .CX 527 1554,
   .CX 527 1558,
   .CX 528 790,
   .CX 1554 790,
   .X 1554,
   .measureX 1554 [] [.CZ 786 790],
   .CX 1558 789,
   .measureX 1558 [] [.CZ 526 788, .CZ 526 1557, .CZ 788 1557],
   .CX 526 788,
   .CX 1557 788,
   .measureX 1557 [] [.CZ 525 787, .CZ 525 1556, .CZ 787 1556],
   .CX 525 787,
   .CX 1556 787,
   .measureX 1556 [] [.CZ 524 786, .CZ 524 1551, .CZ 786 1551],
   .CX 524 786,
   .CX 1551 786,
   .CX 1551 524,
   .CX 1551 525,
   .CX 1551 526,
   .CX 1551 527,
   .CX 1551 528,
   .X 1551,
   .CX 528 1551,
   .CX 790 1551,
   .CX 1551 791,
   .CX 522 523,
   .CX 528 529,
   .CX 790 791,
   .CX 525 790,
   .CX 789 790,
   .CX 527 528,
   .CX 787 528,
   .CCX 790 528 786,
   .CX 525 788,
   .CX 526 788,
   .CX 787 788,
   .CCX 788 524 1556,
   .CX 790 787,
   .CCX 787 786 1553,
   .CX 524 527,
   .CX 786 527,
   .CX 789 527,
   .CX 790 787,
   .CX 1553 787,
   .CCX 527 787 1554,
   .CX 525 526,
   .CX 1554 526,
   .CX 1556 526,
   .CX 523 1554,
   .CX 524 1554,
   .CX 525 1554,
   .CX 527 1554,
   .CX 1553 1554,
   .CCX 526 1554 529,
   .CX 523 1553,
   .CX 525 1553,
   .CX 786 1553,
   .CX 788 1553,
   .CCX 1553 526 1552,
   .CX 523 524,
   .CX 525 787,
   .CX 525 790,
   .CX 1554 1557,
   .CX 1552 1558,
   .CX 524 525,
   .CX 787 525,
   .CX 523 1553,
   .CX 524 1553,
   .CX 527 1553,
   .CX 786 1553,
   .CX 1552 1553,
   .CX 1554 1553,
   .CX 523 1554,
   .CX 524 1554,
   .CX 527 1554,
   .CX 529 1554,
   .CX 786 1554,
   .CX 1552 1554,
   .CX 523 1552,
   .CX 528 1552,
   .CX 786 1552,
   .CX 787 1552,
   .CX 788 1552,
   .CX 790 1552,
   .CX 1554 1552,
   .CX 1557 1552,
   .CX 524 528,
   .CX 527 528,
   .CX 529 528,
   .CX 787 528,
   .CX 788 528,
   .CX 790 528,
   .CX 1552 528,
   .X 527,
   .CX 523 527,
   .CX 524 527,
   .CX 525 527,
   .CX 526 527,
   .CX 529 527,
   .CX 786 527,
   .CX 1554 527,
   .CX 1557 527,
   .CX 1558 527,
   .CX 525 526,
   .measureX 789 [] [.Z 790, .Z 1552, .Z 1553, .Z 1554, .CZ 522 529, .CZ 522 790, .CZ 522 1551, .CZ 522 1554, .CZ 522 1557, .CZ 522 1558],
   .measureX 790 [] [.CZ 523 529, .CZ 523 1552, .CZ 523 1553, .CZ 523 1557, .CZ 523 1558],
   .measureX 1556 [] [.CZ 523 788, .CZ 524 788],
   .measureX 787 [] [.Z 523, .Z 524, .CZ 523 525, .CZ 523 529, .CZ 523 786, .CZ 523 788, .CZ 523 1553, .CZ 523 1554, .CZ 524 525, .CZ 524 786],
   .measureX 1557 [] [.Z 527, .Z 1552, .CZ 1554 524, .CZ 527 524, .CZ 527 529, .CZ 527 788, .CZ 524 529],
   .measureX 788 [] [.Z 1553, .Z 525, .Z 1558, .CZ 1554 524, .CZ 525 524, .CZ 524 529, .CZ 524 1558],
   .X 786,
   .measureX 786 [] [.Z 523, .CZ 524 525, .CZ 524 529, .CZ 524 1553, .CZ 524 1558, .CZ 525 1552, .CZ 525 1554],
   .measureX 529 [] [.Z 1552, .CZ 1554 525, .CZ 527 1552, .CZ 1552 525],
   .measureX 1558 [] [.CZ 525 1552, .CZ 526 1552, .CZ 526 1553],
   .CX 526 786]

def prior : Program := tick507 ++ incumbent6

def sites : List Wire := [522, 523, 524, 525, 526, 527, 528, 529, 786, 787, 788, 789, 790, 791, 1551, 1552, 1553, 1554, 1556, 1557, 1558, 1559]

def pairs : List (Nat × Nat) := [(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1), (9, 1), (10, 1), (11, 1), (12, 1), (13, 1), (14, 1), (15, 1), (1, 3), (2, 3), (4, 3), (5, 3), (7, 3), (10, 3), (13, 3), (1, 5), (2, 5), (3, 5), (6, 5), (7, 5), (11, 5), (1, 7), (2, 7), (3, 7), (5, 7), (9, 7), (1, 9), (7, 9), (1, 11), (5, 11), (1, 13), (3, 13), (1, 15)]

def pre507 (g s : Bool) (u v : Nat) : BasisState := fun q =>
  if q = 522 then g
  else if q = 523 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 1 % 2 = 1)
  else if q = 524 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 2 % 2 = 1)
  else if q = 525 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 4 % 2 = 1)
  else if q = 526 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 8 % 2 = 1)
  else if q = 527 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a / 16 % 2 = 1)
  else if q = 528 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).a < 0)
  else if q = 786 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 1 % 2 = 1)
  else if q = 787 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 2 % 2 = 1)
  else if q = 788 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 4 % 2 = 1)
  else if q = 789 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 8 % 2 = 1)
  else if q = 790 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b / 16 % 2 = 1)
  else if q = 791 then decide ((SkywalkRails.encode g s (u : Int) (v : Int)).b < 0)
  else false

theorem explicit507 : W.repairedTick base 507 = tick507 := by decide +kernel

theorem resources : toffoliCount forward13 = 13 ∧ toffoliCount prior = 14 ∧
    measurementCount forward13 = 14 ∧ measurementCount prior = 14 ∧
    Challenge.gateSlots forward13 = 236 ∧ Challenge.gateSlots prior = 243 := by decide +kernel

theorem support : wires forward13 ⊆ sites.toFinset ∧ wires prior ⊆ sites.toFinset := by decide +kernel

theorem physical : GatePhysical forward13 := by
  simp (config := {maxSteps := 4000000}) [forward13,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]

theorem pre_supp (g s : Bool) (u v : Nat) : ∀ q, q ∉ sites → pre507 g s u v q = false := by
  intro q h
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  simp_all [pre507]

def checkPair (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    agree508 forward13 prior (encN_t8 (pre507 g s uv.1 uv.2) sites)
theorem table : pairs.all checkPair = true := by decide +kernel

theorem on_site (g s : Bool) (uv : Nat × Nat) (member : uv ∈ pairs) (st : State)
    (bits : ∀ q ∈ sites, st.basis q = pre507 g s uv.1 uv.2 q) (m : List Bool) :
    run forward13 m st = run prior m st := by
  have ht := table
  simp only [List.all_eq_true] at ht
  have row := ht uv member
  simp only [checkPair,List.all_eq_true] at row
  have h := row g (by cases g <;> simp) s (by cases s <;> simp)
  apply forced_eqN forward13 prior sites (pre507 g s uv.1 uv.2) 14
    (recsUpTo 14) (take_recsUpTo 14) support.1 support.2
    (by decide +kernel) (by decide +kernel) _ st bits m
  intro tape _
  have eqr := agree508_sound _ _ _ h tape
  have supp : ∀ q : Wire, pre507 g s uv.1 uv.2 q = true → q ∈ sites := by
    intro q hq
    by_contra hn
    rw [pre_supp g s uv.1 uv.2 q hn] at hq
    contradiction
  have same : run forward13 tape ⟨false,pre507 g s uv.1 uv.2⟩ =
      run prior tape ⟨false,pre507 g s uv.1 uv.2⟩ := by
    rw [tb_enc_t8 (pre507 g s uv.1 uv.2) sites supp]
    simp only [run_sim_t8,eqr]
  rw [same]
  exact ⟨rfl, fun _ _ => rfl⟩

end ECDSAAdd.Entrant.MorningFour

namespace ECDSAAdd.Entrant.MorningFour
open Arithmetic MappedCompressed Secp256k1 History5
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

theorem signed6_cases (a b c d e f : Wire) (s : BasisState) (v : Int)
    (h : signedRegValue [a,b,c,d,e,f] s = v) :
    s a = decide (v % 2 = 1) ∧ s b = decide (v / 2 % 2 = 1) ∧ s c = decide (v / 4 % 2 = 1) ∧
      s d = decide (v / 8 % 2 = 1) ∧ s e = decide (v / 16 % 2 = 1) ∧ s f = decide (v < 0) := by
  unfold signedRegValue signedDecode at h
  simp only [regValue,List.length] at h
  cases ha : s a <;> cases hb : s b <;> cases hc : s c <;> cases hd : s d <;> cases he : s e <;> cases hf : s f <;>
    simp [ha,hb,hc,hd,he,hf] at h <;> subst h <;> decide

theorem pairs_of (z : SkywalkNat.State) (hs : z.u+z.v≤16) (h0 : 0<z.v) (h1 : z.v%2=1)
    (hg : z.u.gcd z.v=1) (ht : (SkywalkNat.step^[4] z).u=0) : (z.u,z.v)∈pairs := by
  obtain ⟨u,v⟩ := z
  simp only at hs h0 h1 hg ht ⊢
  have hv : v=1 ∨ v=3 ∨ v=5 ∨ v=7 ∨ v=9 ∨ v=11 ∨ v=13 ∨ v=15 := by omega
  have hu : u ≤ 16-v := by omega
  clear hs h0 h1
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hu <;>
    interval_cases u <;> revert hg ht <;> decide

theorem retainedA507 : (W.compactSkywalkSignPoolA base 507).retained =
    [base 507,base 508,base 509,base 510,base 511,base 512] := by decide +kernel
theorem retainedB507 : (W.compactSkywalkSignPoolB base 507).retained =
    [base 770,base 771,base 772,base 773,base 774,base 775] := by decide +kernel
theorem releasedA507 : base 513 ∈ (W.compactSkywalkSignPoolA base 507).released := by decide +kernel

attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix

theorem raw507 (x : Nat) (hx0 : 0<x) (hx : x<p) (raw : State)
    (hraw : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 507 raw.basis) :
    ∃ g s : Bool, ∃ uv∈pairs, ∀ q∈sites, raw.basis q = pre507 g s uv.1 uv.2 q := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  have fields := (W.compactSkywalkStage_fields_iff base _ 507 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨readA, readB, prev, -, future, carry, -, cleanA, -⟩ := fields
  obtain ⟨G, S, encoded⟩ := SkywalkTrace.iter_encoded 507 false false (SkywalkNat.init x p) hp0 hpo
  have sum := W.iter_sum_width x p 507 hp0 hx0 hpo hp hx cop (by omega)
  have valid := SkywalkNat.iter_valid 507 (SkywalkNat.init x p) hp0 hpo
  have term := (SkywalkNat.terminates_511 p x hp0 hx0 hpo hp hx cop).1
  have split : SkywalkNat.step^[511] (SkywalkNat.init x p) =
      SkywalkNat.step^[4] (SkywalkNat.step^[507] (SkywalkNat.init x p)) := by
    rw [← Function.iterate_add_apply]
  rw [split] at term
  change (SkywalkNat.step^[507] (SkywalkNat.init x p)).u+
    (SkywalkNat.step^[507] (SkywalkNat.init x p)).v ≤ 2^(511-507) at sum
  change SkywalkTrace.next^[507] (SkywalkRails.encode false false (x : Int) (p : Int)) =
    SkywalkRails.encode G S ((SkywalkNat.step^[507] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[507] (SkywalkNat.init x p)).v : Int) at encoded
  generalize SkywalkNat.step^[507] (SkywalkNat.init x p) = z at encoded sum valid term
  have sixteen : (2:Nat)^(511-507) = 16 := by norm_num
  rw [sixteen] at sum
  have mem := pairs_of z sum valid.1 valid.2.1 (valid.2.2.trans cop) term
  rw [encoded, retainedA507] at readA
  rw [encoded, retainedB507] at readB
  rw [encoded] at prev
  have bA := signed6_cases _ _ _ _ _ _ raw.basis _ readA
  have bB := signed6_cases _ _ _ _ _ _ raw.basis _ readB
  have f7 := future 507 (le_refl _) (by omega)
  have f8 := future 508 (by omega) (by omega)
  have f9 := future 509 (by omega) (by omega)
  have f10 := future 510 (by omega) (by omega)
  have c1540 : raw.basis (base 1540) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1540, by simp, rfl⟩)
  have c1541 : raw.basis (base 1541) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1541, by simp, rfl⟩)
  have c1542 : raw.basis (base 1542) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1542, by simp, rfl⟩)
  have c1543 : raw.basis (base 1543) = false :=
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1543, by simp, rfl⟩)
  have c513 : raw.basis (base 513) = false := cleanA _ releasedA507
  have prev' : raw.basis (base 506) = G := by
    have h : skywalkPoolPreviousId 507 = 506 := rfl
    rw [h] at prev
    cases G <;> simpa [SkywalkRails.encode] using prev
  refine ⟨G,S,_,mem,?_⟩
  intro q hq
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prev'
  · simpa [pre507] using bA.1
  · exact bA.2.1
  · exact bA.2.2.1
  · exact bA.2.2.2.1
  · exact bA.2.2.2.2.1
  · exact bA.2.2.2.2.2
  · exact c513
  · simpa [pre507] using bB.1
  · exact bB.2.1
  · exact bB.2.2.1
  · exact bB.2.2.2.1
  · exact bB.2.2.2.2.1
  · exact bB.2.2.2.2.2
  · exact f7.2
  · exact f8.2
  · exact f9.2
  · exact f10.2
  · exact c1540
  · exact c1541
  · exact c1542
  · exact c1543

end ECDSAAdd.Entrant.MorningFour

namespace ECDSAAdd.Entrant.MorningPlacement
open Arithmetic MappedCompressed Secp256k1 History5 OB5 Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

def prior : Program := renameProgram (sig 507) MorningFour.tick507 ++ ForwardSixPlacement.prior
def merged : Program := renameProgram (sig 510) MorningFour.forward13

theorem prior_resources : toffoliCount merged+3=toffoliCount prior ∧
    measurementCount merged=measurementCount prior ∧ Challenge.gateSlots merged ≤ Challenge.gateSlots prior := by decide +kernel

theorem prior_support : wires merged ⊆ wires prior := by decide +kernel

theorem pack507 (isA : Bool) : Rolling1588.Integer.packAfter base isA 507=[] := by
  simp only [Rolling1588.Integer.packAfter, show History5.packDue 507=false from by decide,Bool.false_eq_true,if_false]

theorem first507 (isA : Bool) : packFirst base isA 507=[] := by
  simp only [packFirst,show ¬(507:Nat)=5 from by decide,if_false,pack507 isA]

attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward

theorem previous_shape (isA : Bool) :
    Rolling1588.stackForward isA = Rolling1588.forward isA 1 506 ++ (prior ++ ForwardSixPlacement.after isA) := by
  have snoc := Rolling1588.Integer.forward_snoc isA 1 506
  rw [show (1:Nat)+506=507 by rfl,first507,List.append_nil,Rolling1588.Integer.forward_eq_packets,
    Rolling1588.Integer.forward_eq_packets,MorningFour.explicit507] at snoc
  rw [ForwardSixPlacement.previous_shape,snoc]
  simp only [prior,List.append_assoc]

theorem layouts : ∀ q ∈ MorningFour.sites,
    q∈(W.compactSkywalkTickLayout base 507).wires.toFinset ∨
    q∈(W.compactSkywalkTickLayout base 508).wires.toFinset ∨
    q∈(W.compactSkywalkTickLayout base 509).wires.toFinset ∨
    q∈(W.compactSkywalkTickLayout base 510).wires.toFinset := by decide +kernel

theorem at_stage (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (hs : Stage base isA x p 507 a.basis) (r : List Bool) :
    run MorningFour.forward13 r a = run MorningFour.prior r a := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  obtain ⟨g,s,uv,mem,reads⟩ := MorningFour.raw507 x hx0 hx raw hraw
  apply MorningFour.on_site g s uv mem
  intro q hq
  rw [hbits,←reads q hq]
  apply run_preserves_outside
  rcases layouts q hq with h|h|h|h
  all_goals
    exact fun hh => Finset.disjoint_left.mp
      (prefix_disjoint_layout base isA base_pool_nodup 507 _ (by omega) (by omega)) hh h

theorem place (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 507 a.basis) (r : List Bool) :
    run merged r (pullState (sig 506) a) = run prior r (pullState (sig 506) a) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let k := measurementCount MorningFour.tick507
  let b := run MorningFour.tick507 (r.take k) a
  have s8 : Stage base isA x p 508 b.basis := by
    have next := (Rolling1588.Integer.step_spec base isA base_pool_nodup StackOB5.historyAbove x p 507
      hp0 hx0 hpo hp gap hx cop (by omega) a (r.take k) stage).2
    simpa only [pack507 isA,List.append_nil,MorningFour.explicit507,b] using next
  have p7 : pullState (sig 506) a = pullState (sig 507) a :=
    OB5.pull_step 507 (by omega) a (stage_zero_gen isA x 507 507 (by omega) (by omega) a.basis stage).1
      (stage_zero_gen isA x 507 507 (by omega) (by omega) a.basis stage).2
  have align (v : State) (i : Nat) (hi : i ≤ 508) (h : Stage base isA x p i v.basis) :
      pullState (sig 507) v = pullState (sig 510) v := by
    have z8 := stage_zero_gen isA x i 508 hi (by omega) v.basis h
    have z9 := stage_zero_gen isA x i 509 (by omega) (by omega) v.basis h
    have z10 := stage_zero_gen isA x i 510 (by omega) (by omega) v.basis h
    exact (OB5.pull_step 508 (by omega) v z8.1 z8.2).trans
      ((OB5.pull_step 509 (by omega) v z9.1 z9.2).trans (OB5.pull_step 510 (by omega) v z10.1 z10.2))
  rw [p7,prior,run_append,(renameProgram_counts _ _).2,OB5.run_rename 507 (by omega)]
  change run merged r (pullState (sig 507) a) =
    run ForwardSixPlacement.prior (r.drop k) (pullState (sig 507) b)
  rw [ForwardSixPlacement.prior,←ForwardSixPlacement.place isA x hx0 hx b s8,align b 508 (by omega) s8,
    align a 507 (by omega) stage,merged,OB5.run_rename 510 (by omega),
    OB5.run_rename 510 (by omega),at_stage isA x hx0 hx a stage,MorningFour.prior,run_append]

theorem prior_at_prefix (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis)
    (u r : List Bool) :
    run merged r (run (Rolling1588.forward isA 1 506) u s) =
    run prior r (run (Rolling1588.forward isA 1 506) u s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have init := Rolling1588.Integer.stage_one base isA x p s first
  have st := ((Rolling1588.Integer.regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p
    1 506 hp0 hx0 hpo hp gap hx cop (by omega)) s u init).2
  have start : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  have pre := Rolling1588.Integer.forward_gen isA x hx0 hx 506 1 (by omega) (by omega) s u init
  rw [start,Rolling1588.Integer.forward_eq_packets] at pre
  rw [pre]
  exact place isA x hx0 hx _ st r

theorem replace_at_prefix (P Q R : Program) (s : State) (m : List Bool)
    (counts : measurementCount P=measurementCount Q)
    (prefixSame : ∀ u, run P u s=run Q u s)
    (same : ∀ u v, run merged v (run Q u s)=run prior v (run Q u s)) :
    run (P ++ (merged ++ R)) m s = run (Q ++ (prior ++ R)) m s := by
  simp only [run_append P,run_append Q,run_append merged,run_append prior,counts,prior_resources.2.1]
  rw [prefixSame,same]

end ECDSAAdd.Entrant.MorningPlacement

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.TickGap1591Arithmetic
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Integer

/-! Forward TickGap on the checked A/B integer stage. The packet programs,
the three terminal ticks, and the complete reverse walk stay unchanged. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed Secp256k1 OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

theorem tick_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (TickRanges.tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,oldStage,read⟩ := Rolling1588.Integer.old_stage_local
    base isA base_pool_nodup x p i hi s stage
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (TickRanges.tick_support base i hi base_pool_nodup).trans old
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (TickRanges.tick_eq5 x hx0 hx i hi raw m oldStage)

theorem block_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i) m s=
      run (W.repairedTick base i++Rolling1588.Integer.packFirst base isA i) m s := by
  rw [run_append (TickRanges.tick base i),run_append (W.repairedTick base i),
    run_take (TickRanges.tick base i),run_take (W.repairedTick base i),
    tick_run_eq isA x hx0 hx i hi s m stage,
    (TickRanges.tick_counts base i hi base_pool_nodup).2]

def forward (isA : Bool) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i)
      (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)++
        forward isA (i+1) n

def count (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => TickRanges.due i+count (i+1) n

def stackForward (isA : Bool) : Program :=
  forward isA 1 506 ++ (MorningPlacement.merged ++ ForwardSixPlacement.after isA)

attribute [local irreducible] forward stackForward Rolling1588.forward
  Rolling1588.Integer.forward Rolling1588.stackForward

theorem forward_gen (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (n : Nat) :
    ∀i,1 ≤ i → i+n ≤ 512 → ∀(s : State)(m : List Bool),
      Rolling1588.Integer.Stage base isA x p i s.basis →
      run (forward isA i n) m (pullState (sig (i-1)) s)=
        pullState (sig (i+n-1)) (run (Rolling1588.Integer.regularForward base isA i n) m s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  induction n with
  | zero =>
    intro i _ _ s m _
    simp only [forward,Rolling1588.Integer.regularForward,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 bound s m stage
    have hi : i ≤ 511 := by omega
    have zero := Rolling1588.Integer.stage_zero isA x i (by omega) s.basis stage
    rw [pull_step i hi s zero.1 zero.2]
    have mapped := (renameProgram_counts (sig i)
      (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)).2
    have records :
        measurementCount (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)=
          measurementCount (W.repairedTick base i++Rolling1588.Integer.packAfter base isA i) := by
      rw [measurementCount_append,measurementCount_append,
        (TickRanges.tick_counts base i (by omega) base_pool_nodup).2,
        Rolling1588.Integer.packFirst_records]
    rw [forward,Rolling1588.Integer.regularForward,run_append,run_append,mapped,records,
      OB5.run_rename i hi,block_run_eq isA x hx0 hx i (by omega) s _ stage,
      Rolling1588.Integer.forward_step_eq base isA base_pool_nodup x p i
        hp0 hx0 hpo hp gap hx cop _ _ stage]
    have next := (Rolling1588.Integer.step_spec base isA base_pool_nodup
      StackOB5.historyAbove x p i hp0 hx0 hpo hp gap hx cop (by omega) s
        (m.take (measurementCount (W.repairedTick base i++
          Rolling1588.Integer.packAfter base isA i))) stage).2
    have rest := ih (i+1) (by omega) (by omega) _
      (m.drop (measurementCount (W.repairedTick base i++
        Rolling1588.Integer.packAfter base isA i))) next
    rw [show i+1-1=i by omega,show i+1+n-1=i+(n+1)-1 by omega] at rest
    exact rest

theorem forward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i n : Nat) (h1 : 1 ≤ i) (bound : i+n ≤ 512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (forward isA i n) m (pullState (sig (i-1)) s)=
      run (Rolling1588.forward isA i n) m (pullState (sig (i-1)) s) := by
  rw [←Rolling1588.Integer.forward_eq_packets]
  rw [forward_gen isA x hx0 hx n i h1 bound s m stage,
    Rolling1588.Integer.forward_gen isA x hx0 hx n i h1 bound s m stage]

theorem forward_first_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (n : Nat) (bound : 1+n ≤ 512) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (forward isA 1 n) m s=run (Rolling1588.forward isA 1 n) m s := by
  have same := forward_run_eq isA x hx0 hx 1 n (Nat.le_refl 1) bound s m
    (Rolling1588.Integer.stage_one base isA x p s first)
  have start : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  rwa [start] at same

private theorem forward_integer_metrics (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    toffoliCount (forward isA i n)+count i n=
        toffoliCount (Rolling1588.Integer.forward isA i n) ∧
      measurementCount (forward isA i n)=measurementCount (Rolling1588.Integer.forward isA i n) ∧
      Challenge.gateSlots (forward isA i n) ≤
        Challenge.gateSlots (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero =>
    simp [forward,Rolling1588.Integer.forward,count,toffoliCount,measurementCount,Challenge.gateSlots]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have step := TickRanges.tick_counts base i (by omega) base_pool_nodup
    have slots := TickRanges.tick_slots base i (by omega) base_pool_nodup
    simp only [forward,Rolling1588.Integer.forward,count,toffoliCount_append,
      measurementCount_append,Challenge.gateSlots_append,
      (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
      Baselines.rename_gateSlots]
    exact ⟨by omega,by omega,by omega⟩

theorem forward_metrics (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    toffoliCount (forward isA i n)+count i n=toffoliCount (Rolling1588.forward isA i n) ∧
      measurementCount (forward isA i n)=measurementCount (Rolling1588.forward isA i n) ∧
      Challenge.gateSlots (forward isA i n) ≤ Challenge.gateSlots (Rolling1588.forward isA i n) := by
  simpa only [Rolling1588.Integer.forward_eq_packets] using
    forward_integer_metrics isA i n bound

theorem count_508 : count 1 508=62 := by decide +kernel

theorem stackForward_metrics (isA : Bool) :
    toffoliCount (stackForward isA)+65=toffoliCount (Rolling1588.stackForward isA) ∧
      measurementCount (stackForward isA)=measurementCount (Rolling1588.stackForward isA) ∧
      Challenge.gateSlots (stackForward isA) ≤ Challenge.gateSlots (Rolling1588.stackForward isA) := by
  have head := forward_metrics isA 1 506 (by omega)
  have c : count 1 506=62 := by decide +kernel
  rw [c] at head
  have tail := MorningPlacement.prior_resources
  rw [stackForward,MorningPlacement.previous_shape]
  simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem forward_integer_support (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    wires (forward isA i n)⊆wires (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,Rolling1588.Integer.forward,wires]
  | succ n ih =>
    have block : wires (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)⊆
        wires (W.repairedTick base i++Rolling1588.Integer.packFirst base isA i) := by
      rw [wires_append,wires_append]
      exact Finset.union_subset_union
        (TickRanges.tick_support base i (by omega) base_pool_nodup) (Finset.Subset.refl _)
    have placed := Finset.image_mono (sig i) block
    rw [←renameProgram_support,←renameProgram_support] at placed
    simp only [forward,Rolling1588.Integer.forward,wires_append]
    exact Finset.union_subset_union placed (ih (i+1) (by omega))

theorem forward_support (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    wires (forward isA i n)⊆wires (Rolling1588.forward isA i n) := by
  simpa only [Rolling1588.Integer.forward_eq_packets] using
    forward_integer_support isA i n bound

theorem stackForward_support (isA : Bool) :
    wires (stackForward isA)⊆wires (Rolling1588.stackForward isA) := by
  rw [stackForward,MorningPlacement.previous_shape]
  simp only [wires_append]
  exact Finset.union_subset_union (forward_support isA 1 506 (by omega))
    (Finset.union_subset_union MorningPlacement.prior_support (Finset.Subset.refl _))

private theorem append_run_eq (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem stackForward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=run (Rolling1588.stackForward isA) m s := by
  rw [stackForward,MorningPlacement.previous_shape]
  exact MorningPlacement.replace_at_prefix _ _ _ s m
    (forward_metrics isA 1 506 (by omega)).2.1
    (fun r => forward_first_run_eq isA x hx0 hx 506 (by omega) s r first)
    (MorningPlacement.prior_at_prefix isA x hx0 hx s first)

theorem stackForward_boundary (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=pullState (sig 511)
      (run (Rolling1588.allEncode base isA 102) []
        (run (W.compactSkywalkForward base 1 511) [] s)) := by
  rw [stackForward_run_eq isA x hx0 hx s m first]
  exact Rolling1588.stackForward_boundary isA hn hlo x hx0 hx s m first

theorem stack_roundtrip (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (Rolling1588.stackReverse isA) mD (run (stackForward isA) mE s)=s := by
  rw [stackForward_run_eq isA x hx0 hx s mE first]
  exact Rolling1588.stack_roundtrip isA hn hlo x hx0 hx s mE mD first

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Native
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Kernel
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588KernelResources

/-! The new forward phase has the exact old A/B State boundary. All native,
field, inverse, host, and caller interfaces are retained. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Challenge Baselines
  FrontierEntry1591Callers OB5
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  forward stackForward Rolling1588.forward Rolling1588.stackForward Rolling1588.stackReverse
  FrontierEntry1591Native.forward FrontierEntry1591Native.inverse
  Rolling1588.firstPhase Rolling1588.lastPhase

def tailPhase (isA : Bool) : Program := stackForward isA++skywalkArithmeticClear base

def firstPhase (isA : Bool) : Program := FrontierEntry1591Native.forward base++tailPhase isA

def oldKernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def kernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def entryKernel : Program := kernel true false Rolling1588.entryFieldHosted
def exitKernel : Program := kernel false true Rolling1588.exitFieldHosted

attribute [local irreducible] tailPhase firstPhase oldKernel kernel entryKernel exitKernel
  Rolling1588.entryKernel Rolling1588.exitKernel

private theorem first_run_eq_of_stack (N F F0 C : Program) (s : State) (m : List Bool)
    (records : measurementCount F=measurementCount F0)
    (same : ∀mn mf,run F mf (run N mn s)=run F0 mf (run N mn s)) :
    run (N++(F++C)) m s=run (N++(F0++C)) m s := by
  simp only [run_append,records]
  rw [same]

theorem first_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=run (Rolling1588.firstPhase isA) m s := by
  have same (mn mf : List Bool) :
      run (stackForward isA) mf (run (FrontierEntry1591Native.forward base) mn s)=
        run (Rolling1588.stackForward isA) mf
          (run (FrontierEntry1591Native.forward base) mn s) :=
    stackForward_run_eq isA x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [firstPhase,tailPhase,Rolling1588.firstPhase,List.append_assoc] using
    first_run_eq_of_stack (FrontierEntry1591Native.forward base) (stackForward isA)
      (Rolling1588.stackForward isA) (skywalkArithmeticClear base) s m
      (stackForward_metrics isA).2.1 same

private theorem state_fact_of_eq (P : State→Prop) (a b : State)
    (same : a=b) (fact : P b) : P a := by
  cases same
  exact fact

theorem first_clean (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    ∀q∈FrontierEntry1591Native.workSites,(run (firstPhase isA) m s).basis q=false := by
  exact state_fact_of_eq
    (fun t=>∀q∈FrontierEntry1591Native.workSites,t.basis q=false)
    (run (firstPhase isA) m s) (run (Rolling1588Lifetime.firstPhase isA) m s)
    (first_run_eq isA hn x y hx0 hx s m input)
    (Rolling1588Lifetime.first_clean isA hn hlo x y hx0 hx s m input)

theorem first_phase (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    (run (firstPhase isA) m s).phase=s.phase := by
  exact state_fact_of_eq (fun t=>t.phase=s.phase)
    (run (firstPhase isA) m s) (run (Rolling1588Lifetime.firstPhase isA) m s)
    (first_run_eq isA hn x y hx0 hx s m input)
    (Rolling1588Lifetime.first_phase isA hn hlo x y hx0 hx s m input)

theorem first_boundary (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=pullState (sig 511)
      (run (Rolling1588.allEncode base isA 102) []
        (run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) []
          (run (FrontierEntry1591Native.forward base)
            (m.take (measurementCount (FrontierEntry1591Native.forward base))) s)))) := by
  rw [first_run_eq isA hn x y hx0 hx s m input]
  exact Rolling1588Lifetime.first_boundary isA hn hlo x y hx0 hx s m input

theorem phases_roundtrip (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mE mD : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (Rolling1588.lastPhase isA) mD (run (firstPhase isA) mE s)=s := by
  rw [first_run_eq isA hn x y hx0 hx s mE input]
  exact Rolling1588Lifetime.phases_roundtrip isA hn hlo x y hx0 hx s mE mD input

theorem first_metrics (isA : Bool) :
    toffoliCount (firstPhase isA)+65=toffoliCount (Rolling1588.firstPhase isA) ∧
      measurementCount (firstPhase isA)=measurementCount (Rolling1588.firstPhase isA) ∧
      gateSlots (firstPhase isA) ≤ gateSlots (Rolling1588.firstPhase isA) := by
  have stack := stackForward_metrics isA
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem first_support (isA : Bool) :
    wires (firstPhase isA)⊆wires (Rolling1588.firstPhase isA) := by
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,wires_append,Finset.union_assoc]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (stackForward_support isA) (Finset.Subset.refl _))

private theorem mapped_code_physical (isA : Bool) (f : Fin 10→Wire)
    (hf : Function.Injective f) :
    GatePhysical (renameProgram (MeasuredCodec5.label f) (Rolling1588.codeEncode isA)) := by
  have support : wires (Rolling1588.codeEncode isA)⊆Finset.range 10 := by
    simpa only [(Rolling1588.code_support isA).1] using
      (Finset.Subset.refl (Finset.range 10))
  exact gatePhysical_rename_support _ _
    (fun a ha b hb eq=>FirstNonzeroCodec.label_inj' f hf a (support ha) b (support hb) eq)
    (Rolling1588.code_physical isA).1

private theorem pack_physical (isA : Bool) (i : Nat) (hi : i<512) :
    GatePhysical (Rolling1588.packAtTick isA i) := by
  by_cases first : i=5
  · simp only [Rolling1588.packAtTick,if_pos first]
    exact (ParityCodec5New.first_mapped_physical _
      (History5.historyMap_injective base base_pool_nodup 0 (by decide))).1
  · simp only [Rolling1588.packAtTick,if_neg first]
    split
    · have due := History5.packDue_true i ‹History5.packDue i=true›
      exact mapped_code_physical isA _
        (History5.historyMap_injective base base_pool_nodup (i-5) (by omega))
    · simp [GatePhysical]

theorem forward_physical (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    GatePhysical (forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have pack : GatePhysical (Rolling1588.Integer.packFirst base isA i) := by
      rw [Rolling1588.Integer.packFirst_base]
      exact pack_physical isA i (by omega)
    rw [forward,gatePhysical_append]
    exact ⟨gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr
        ⟨TickRanges.tick_physical base i (by omega) base_pool_nodup,pack⟩),
      ih (i+1) (by omega)⟩

theorem stackForward_physical (isA : Bool) : GatePhysical (stackForward isA) := by
  have old := Rolling1588.stackForward_physical isA
  rw [MorningPlacement.previous_shape] at old
  simp only [gatePhysical_append] at old
  rw [stackForward]
  simp only [gatePhysical_append]
  exact ⟨forward_physical isA 1 506 (by omega),
    gatePhysical_rename _ (sig_injective 510 (by omega)) _ MorningFour.physical,old.2.2⟩

theorem first_physical (isA : Bool) : GatePhysical (firstPhase isA) := by
  have old := Rolling1588.firstPhase_physical isA
  simp only [Rolling1588.firstPhase,gatePhysical_append] at old
  simpa only [firstPhase,tailPhase,gatePhysical_append] using
    And.intro old.1.1 (And.intro (stackForward_physical isA) old.2)

private theorem mapped_run_eq (f : Equiv.Perm Wire) (P Q : Program)
    (s : State) (m : List Bool) (clean : pullState f s=s)
    (same : run P m s=run Q m s) :
    run (renameProgram f P) m s=run (renameProgram f Q) m s := by
  apply pullState_perm_injective f
  rw [run_rename _ f.injective,run_rename _ f.injective,clean]
  exact same

theorem first_hosted_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (renameProgram Rolling1588Lifetime.phaseHost (firstPhase isA)) m s=
      run (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase isA)) m s := by
  exact mapped_run_eq Rolling1588Lifetime.phaseHost _ _ s m
    (Rolling1588Lifetime.pull_phase_clean s
      (Rolling1588Lifetime.caller_phase_clean x y s input))
    (first_run_eq isA hn x y hx0 hx s m input)

private theorem append_run_eq_tickgap_phases (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernel_run_eq (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel a b F) m s=run (oldKernel a b F) m s := by
  have records :
      measurementCount (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))=
        measurementCount (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(first_metrics a).2.1]
  simpa only [kernel,oldKernel] using append_run_eq_tickgap_phases
    (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a))
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) s m records
    (fun r=>first_hosted_run_eq a hn x y hx0 hx s r input)

theorem kernel_metrics (a b : Bool) (F : Program) :
    toffoliCount (kernel a b F)+65=toffoliCount (oldKernel a b F) ∧
      measurementCount (kernel a b F)=measurementCount (oldKernel a b F) ∧
      gateSlots (kernel a b F) ≤ gateSlots (oldKernel a b F) := by
  have first := first_metrics a
  simp only [kernel,oldKernel,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

private theorem mapped_append_support (f : Wire→Wire) (P Q R : Program)
    (first : wires P⊆wires Q) :
    wires (renameProgram f P++R)⊆wires (renameProgram f Q++R) := by
  rw [wires_append,wires_append,renameProgram_support,renameProgram_support]
  exact Finset.union_subset_union
    (Finset.image_mono f first) (Finset.Subset.refl _)

theorem kernel_support (a b : Bool) (F : Program) :
    wires (kernel a b F)⊆wires (oldKernel a b F) := by
  simpa only [kernel,oldKernel] using
    mapped_append_support Rolling1588Lifetime.phaseHost
      (firstPhase a) (Rolling1588.firstPhase a)
      (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) (first_support a)

theorem kernel_physical (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel a b F) := by
  simpa only [kernel,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (first_physical a))
      (And.intro field
        (Rolling1588Lifetime.phase_physical _ (Rolling1588.lastPhase_physical b)))

theorem kernel_entry_correct (F : Program) (raw : EntryCorrect (oldKernel true false F)) :
    EntryCorrect (kernel true false F) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [kernel_run_eq true false F hn x _ hx0 hx t m actual]
  exact raw hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half

theorem kernel_exit_correct (F : Program) (raw : ExitCorrect (oldKernel false true F)) :
    ExitCorrect (kernel false true F) := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  rw [kernel_run_eq false true F hn x Y.val hx0 hx s m input]
  exact raw hn hlo ho hf x Y hx0 hx s m input hg hs

theorem entry_correct : EntryCorrect entryKernel := by
  have old : EntryCorrect (oldKernel true false Rolling1588.entryFieldHosted) := by
    simpa only [oldKernel,Rolling1588.entryKernel] using Rolling1588.entry_correct
  simpa only [entryKernel] using kernel_entry_correct Rolling1588.entryFieldHosted old

theorem exit_correct : ExitCorrect exitKernel := by
  have old : ExitCorrect (oldKernel false true Rolling1588.exitFieldHosted) := by
    simpa only [oldKernel,Rolling1588.exitKernel] using Rolling1588.exit_correct
  simpa only [exitKernel] using kernel_exit_correct Rolling1588.exitFieldHosted old

private theorem metrics_of_shapes (P Q A B : Program)
    (left : P=A) (right : Q=B)
    (metrics : toffoliCount A+65=toffoliCount B ∧
      measurementCount A=measurementCount B ∧ gateSlots A ≤ gateSlots B) :
    toffoliCount P+65=toffoliCount Q ∧
      measurementCount P=measurementCount Q ∧ gateSlots P ≤ gateSlots Q := by
  cases left
  cases right
  exact metrics

theorem entryKernel_metrics :
    toffoliCount entryKernel+65=toffoliCount Rolling1588.entryKernel ∧
      measurementCount entryKernel=measurementCount Rolling1588.entryKernel ∧
      gateSlots entryKernel ≤ gateSlots Rolling1588.entryKernel := by
  have left : entryKernel=kernel true false Rolling1588.entryFieldHosted := by
    unfold entryKernel
    rfl
  have right : Rolling1588.entryKernel=oldKernel true false Rolling1588.entryFieldHosted := by
    unfold Rolling1588.entryKernel oldKernel
    rfl
  exact metrics_of_shapes entryKernel Rolling1588.entryKernel
    (kernel true false Rolling1588.entryFieldHosted)
    (oldKernel true false Rolling1588.entryFieldHosted) left right
    (kernel_metrics true false Rolling1588.entryFieldHosted)

theorem exitKernel_metrics :
    toffoliCount exitKernel+65=toffoliCount Rolling1588.exitKernel ∧
      measurementCount exitKernel=measurementCount Rolling1588.exitKernel ∧
      gateSlots exitKernel ≤ gateSlots Rolling1588.exitKernel := by
  have left : exitKernel=kernel false true Rolling1588.exitFieldHosted := by
    unfold exitKernel
    rfl
  have right : Rolling1588.exitKernel=oldKernel false true Rolling1588.exitFieldHosted := by
    unfold Rolling1588.exitKernel oldKernel
    rfl
  exact metrics_of_shapes exitKernel Rolling1588.exitKernel
    (kernel false true Rolling1588.exitFieldHosted)
    (oldKernel false true Rolling1588.exitFieldHosted) left right
    (kernel_metrics false true Rolling1588.exitFieldHosted)

theorem entryKernel_support_subset : wires entryKernel⊆wires Rolling1588.entryKernel := by
  simpa only [entryKernel,oldKernel,Rolling1588.entryKernel] using
    kernel_support true false Rolling1588.entryFieldHosted

theorem exitKernel_support_subset : wires exitKernel⊆wires Rolling1588.exitKernel := by
  simpa only [exitKernel,oldKernel,Rolling1588.exitKernel] using
    kernel_support false true Rolling1588.exitFieldHosted

theorem entryKernel_support : wires entryKernel⊆OB5Support.logicalSites :=
  entryKernel_support_subset.trans Rolling1588.entryKernel_support

theorem exitKernel_support : wires exitKernel⊆OB5Support.logicalSites :=
  exitKernel_support_subset.trans Rolling1588.exitKernel_support

theorem entryKernel_physical : GatePhysical entryKernel := by
  simpa only [entryKernel] using
    kernel_physical true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exitKernel_physical : GatePhysical exitKernel := by
  simpa only [exitKernel] using
    kernel_physical false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

theorem entryKernel_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_free i hi (entryKernel_support_subset used)

theorem exitKernel_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_free i hi (exitKernel_support_subset used)

theorem entryKernel_768_free : base 768∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_768_free (entryKernel_support_subset used)
theorem exitKernel_768_free : base 768∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_768_free (exitKernel_support_subset used)
theorem entryKernel_718_free : base 718∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_718_free (entryKernel_support_subset used)
theorem exitKernel_718_free : base 718∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_718_free (exitKernel_support_subset used)
theorem entryKernel_719_free : base 719∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_719_free (entryKernel_support_subset used)
theorem exitKernel_719_free : base 719∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_719_free (exitKernel_support_subset used)
theorem entryKernel_760_free : base 760∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_760_free (entryKernel_support_subset used)
theorem exitKernel_760_free : base 760∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_760_free (exitKernel_support_subset used)

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGap =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Final
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases

/-! E1 entries and the reflected square are unchanged. Only the two
forward tails use the checked TickGap program. Both inverse phases stay. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)++
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))

def entryStage (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky++E1QubitPlacement.entryM L kx++restE L

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  ReflectionE1.squareEntry L k++restX L++exitY L cy

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L=
      E1QubitPlacement.tickF L++restE L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,Rolling1588TickGap.entryKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restE,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L=
      E1QubitPlacement.tickF L++restX L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,Rolling1588TickGap.exitKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restX,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

section CorrectStages
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
  have divide:=division_step Rolling1588TickGap.entryKernel Rolling1588TickGap.entryKernel_support
    Rolling1588TickGap.entry_correct L hw hn config.1 above config.2.1 config.2.2
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
  have multiply:=fusedMultiply_step L hw hn
    (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L)
    (exit_correct Rolling1588TickGap.exitKernel Rolling1588TickGap.exitKernel_support
      Rolling1588TickGap.exit_correct L hw hn)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=ReflectionE1.squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=restX L++exitY L cy)
  · intro s v m1 m2
    exact ReflectionE1.squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [secondStage,fusedMultiply,exit_split,List.append_assoc,Z] using prior

end CorrectStages

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage L (-cx) (-cy)++secondStage L (ReflectionE1.correction cx) cy++fastConstNeg L cx

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
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStage_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy true origin
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
  have second:=secondStage_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy false origin
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
attribute [local irreducible] restE restX entryStage secondStage generic mid gen
  ReflectionE1.restE ReflectionE1.restX ReflectionE1.tailP ReflectionE1.generic ReflectionE1.gen
  Rolling1588TickGap.tailPhase Rolling1588TickGap.stackForward Rolling1588.stackForward
  Rolling1588.firstPhase Rolling1588.lastPhase Rolling1588.entryFieldHosted Rolling1588.exitFieldHosted

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (n : Nat) (P Q : Program) : Prop :=
  toffoliCount P+n=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
    gateSlots P ≤ gateSlots Q ∧ wires P⊆wires Q

private theorem append_facts (P Q C : Program)
    (count : toffoliCount P+65=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
      gateSlots P ≤ gateSlots Q) (sub : wires P⊆wires Q) : Facts 65 (P++C) (Q++C) := by
  simp only [Facts,toffoliCount_append,measurementCount_append,gateSlots_append,wires_append]
  exact ⟨by omega,by omega,by omega,Finset.union_subset_union sub (Finset.Subset.refl _)⟩

private theorem tail_facts (a : Bool) :
    Facts 65 (Rolling1588TickGap.tailPhase a) (ReflectionE1.tailP a) := by
  apply relation_of_shapes (Facts 65) _ _
    (Rolling1588TickGap.stackForward a++skywalkArithmeticClear base)
    (Rolling1588.stackForward a++skywalkArithmeticClear base)
  · unfold Rolling1588TickGap.tailPhase
    rfl
  · unfold ReflectionE1.tailP
    rfl
  · exact append_facts _ _ _ (Rolling1588TickGap.stackForward_metrics a)
      (Rolling1588TickGap.stackForward_support a)

private def restContext (f g : Wire→Wire) (P R : Program) : Program :=
  renameProgram f (renameProgram g P++R)

private theorem rest_facts (f g : Wire→Wire) (P Q R : Program) (h : Facts 65 P Q) :
    Facts 65 (restContext f g P R) (restContext f g Q R) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (restContext f g P R)⊆wires (restContext f g Q R) := by
    simp only [restContext,renameProgram_support,wires_append]
    exact Finset.image_mono f
      (Finset.union_subset_union (Finset.image_mono g hw) (Finset.Subset.refl _))
  simp only [Facts,restContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem restE_facts (L : ControlledPointLayout) :
    Facts 65 (restE L) (ReflectionE1.restE L) := by
  apply relation_of_shapes (Facts 65) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
  · unfold restE restContext
    rfl
  · unfold ReflectionE1.restE restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts true)

private theorem restX_facts (L : ControlledPointLayout) :
    Facts 65 (restX L) (ReflectionE1.restX L) := by
  apply relation_of_shapes (Facts 65) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
  · unfold restX restContext
    rfl
  · unfold ReflectionE1.restX restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts false)

private def stagesContext (Y M E S X EY N : Program) : Program :=
  (Y++M++E)++(S++X++EY)++N

private theorem stages_facts (Y M E E0 S X X0 EY N : Program)
    (entry : Facts 65 E E0) (exit : Facts 65 X X0) :
    Facts 130 (stagesContext Y M E S X EY N) (stagesContext Y M E0 S X0 EY N) := by
  rcases entry with ⟨et,em,es,ew⟩
  rcases exit with ⟨xt,xm,xs,xw⟩
  have sub : wires (stagesContext Y M E S X EY N)⊆
      wires (stagesContext Y M E0 S X0 EY N) := by
    simp only [stagesContext,wires_append]
    exact Finset.union_subset_union
      (Finset.union_subset_union
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
          (Finset.Subset.refl _)) ew)
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) xw)
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,stagesContext,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold generic entryStage secondStage stagesContext
  rfl

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1.generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold ReflectionE1.generic ReflectionE1.entryStage ReflectionE1.secondStage stagesContext
  rfl

private theorem generic_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 130 (generic L cx cy) (ReflectionE1.generic L cx cy) := by
  exact relation_of_shapes (Facts 130) _ _ _ _
    (generic_shape L cx cy) (old_generic_shape L cx cy)
    (stages_facts (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx)
      (restE_facts L) (restX_facts L))

theorem generic_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1.generic L cx cy) :=
  (generic_facts L cx cy).2.2.2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_subset L cx cy).trans (ReflectionE1.generic_sites L hw hn cx cy)

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) :=
  fun used=>ReflectionE1.generic_free L hw hn cx cy i hi (generic_support_subset L cx cy used)

private theorem suffix_physical (P Q R : Program) (shape : P=Q++R)
    (physical : GatePhysical P) : GatePhysical R := by
  rw [shape,gatePhysical_append] at physical
  exact physical.2

private theorem restE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restE L) := by
  have physical := placed_physical Rolling1588TickGap.entryKernel
    Rolling1588TickGap.entryKernel_support Rolling1588TickGap.entryKernel_physical L hw hn
  have entryPhysical : GatePhysical (FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.entry;rfl) physical
  exact suffix_physical _ _ _ (entry_split L) entryPhysical

private theorem restX_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restX L) := by
  have physical := placed_physical Rolling1588TickGap.exitKernel
    Rolling1588TickGap.exitKernel_support Rolling1588TickGap.exitKernel_physical L hw hn
  have exitPhysical : GatePhysical (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.exit;rfl) physical
  exact suffix_physical _ _ _ (exit_split L) exitPhysical

private theorem stages_physical (Y M E E0 S X X0 EY N : Program)
    (old : GatePhysical (stagesContext Y M E0 S X0 EY N))
    (entry : GatePhysical E) (exit : GatePhysical X) :
    GatePhysical (stagesContext Y M E S X EY N) := by
  simp only [stagesContext,gatePhysical_append] at old ⊢
  exact And.intro
    (And.intro (And.intro old.1.1.1 entry)
      (And.intro (And.intro old.1.2.1.1 exit) old.1.2.2)) old.2

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old := fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1.generic_physical L hw hn cx cy)
  exact fact_of_shape GatePhysical _ _ (generic_shape L cx cy)
    (stages_physical (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) old
      (restE_physical L hw hn) (restX_physical L hw hn))

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program)
    (h : Facts 130 P Q) : Facts 130 (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (wrapContext Z C f P)⊆wires (wrapContext Z C f Q) := by
    simp only [wrapContext,wires_append,renameProgram_support]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union
          (Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono f hw))
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem gen_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 130 (gen L cx cy) (ReflectionE1.gen L cx cy) := by
  apply relation_of_shapes (Facts 130) _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1.gen ReflectionE1.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L cx cy)

theorem gen_metrics (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+130=toffoliCount (ReflectionE1.gen L cx cy) ∧
    measurementCount (gen L cx cy)=measurementCount (ReflectionE1.gen L cx cy) ∧
    gateSlots (gen L cx cy) ≤ gateSlots (ReflectionE1.gen L cx cy) :=
  ⟨(gen_facts L cx cy).1,(gen_facts L cx cy).2.1,(gen_facts L cx cy).2.2.1⟩

theorem gen_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (ReflectionE1.gen L cx cy) := (gen_facts L cx cy).2.2.2

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L cx cy).trans (ReflectionE1.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts 130 P Q) :
    toffoliCount (Edges.wrapper L C cy P)+130=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P) ≤ gateSlots (Edges.wrapper L C cy Q) := by
  rcases h with ⟨ht,hm,hs,_⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2151558 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).1
  have entryDelta := (ReflectionE1.gen_counts_delta layout layout_widths cx cy).1
  have baseline := Rolling1588BFFinal.wrapper_toffoli cx cy hc
  have entryWrapperDelta :
      toffoliCount (Edges.wrapper layout (.some hc) cy (ReflectionE1.gen layout cx cy))+759=
        toffoliCount (Edges.wrapper layout (.some hc) cy (Rolling1588BFFinal.gen layout cx cy)) := by
    simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
      (renameProgram_counts _ _).1]
    omega
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1499214 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).2.1
  have old:=ReflectionE1.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50189199+Rolling1588.slotGrowth := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout cx cy)).2.2
  have old:=ReflectionE1.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGap

/-! E1/reflected Q1588 point with the two checked TickGap forward tails. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151558,1499214,1588,50189199+Rolling1588.slotGrowth⟩

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

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2151558 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1499214 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50189199+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1499214
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50189199+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- Checked Low48 dependencies follow; the selected reflected prefix retains both checked TickGap tails.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Square

/-! Only the retained E1 square prefix changes. The reflected entry and all maps stay fixed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Low48Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

abbrev K : Nat := ControlLoan1589BFFold.K

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.branchCK L ext control++LowZero18Square.branchBF L ext control++
    LowZero18Square.branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore L)

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    LowZero18Square.raw L ext control=core L ext control++LowZero18Square.reflection L ext := rfl

theorem program_split (L : ControlledPointLayout) :
    LowZero18Square.program L=program L++ReflectionE1Square.reflectedTail L := by
  change SquareCarryLoan719BF.place L (LowZero18Square.raw L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)=
    SquareCarryLoan719BF.place L (core L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)++
    SquareCarryLoan719BF.place L (SquareCarryLoan719BF.reflection
      L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))
  rw [raw_split,ReflectionE1Square.place_append]
  rfl

theorem raw_core_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (core L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (core L ext control) records s).basis=
      SquareReduction.p-1-
        (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
          (if s.basis control then K else 0))%SquareReduction.p) ∧
    ∀q,q∉L.core.out → (run (core L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (LowZero18Square.branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := LowZero18Square.branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (LowZero18Square.branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := LowZero18Square.branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA<SquareReduction.p := ofCast_lt _ _
  have reflected : OA=SquareReduction.p-1-
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) := by
    change SquareReduction.p-1-OA=
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) at exactResult
    omega
  exact ⟨phase,value.trans reflected,frame⟩


open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCore_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p) ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have extOK:=OwnDiagAll12Square.kext_ok L hw hn
  have hext : ECDSAAdd.Entrant.ExtOK K L.core.generic (OwnDiagAll12Square.kext L) :=
    ⟨extOK.nodup,extOK.away,extOK.len⟩
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hext hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  refine ⟨fresh.1,?_,fresh.2.2⟩
  have hK : ((SquareCarryLoan719BF.K:Nat):Fp).val=SquareCarryLoan719BF.K :=
    ZMod.val_natCast_of_lt (by norm_num [SquareCarryLoan719BF.K,ControlLoan1589BFFold.K,p])
  rw [ZMod.val_add,sub_val]
  cases G
  · simpa using fresh.2.1
  · simpa [ZMod.val_mul,hK,K,SquareCarryLoan719BF.K] using fresh.2.1

private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.point.x (run (program L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program L) m s).basis q=s.basis q := by
  have result:=fastCore_boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (fastCore L) m s=out := ⟨_,rfl⟩
  rw [heq] at result
  have clean : regValue L.dialogPool out.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq)),v.clean]
  have eq:=ReflectionE1Square.place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 := by
  have result:=boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (program L) m s=out := ⟨_,rfl⟩
  rw [heq] at result ⊢
  exact (regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq))).trans v.clean

/-- This comparison is separate from the direct boundary proof. -/
theorem run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (mNew mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) mNew s=run (ReflectionE1Square.program L) mOld s := by
  obtain ⟨a,ha⟩ : ∃a : State,run (program L) mNew s=a := ⟨_,rfl⟩
  obtain ⟨b,hb⟩ : ∃b : State,run (ReflectionE1Square.program L) mOld s=b := ⟨_,rfl⟩
  have fresh:=boundary L hw hn X Y G origin s mNew v
  have prior:=ReflectionE1Square.boundary L hw hn X Y G origin s mOld v
  rw [ha] at fresh
  rw [hb] at prior
  rw [ha,hb]
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · funext q
    by_cases hx : q∈L.point.x
    · exact (regValue_eq_iff _ _ _).mp (fresh.2.1.trans prior.2.1.symm) q hx
    · exact (fresh.2.2 q hx).trans (prior.2.2 q hx).symm

private theorem window_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18Square.withLowK2 L ext control src dst body)+66+5*(if src.length=128 then 0 else 1)=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (LowZero18Square.withLowK2 L ext control src dst body)+24+4*(if src.length=128 then 0 else 1)=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have a:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  have b:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  constructor <;> omega

private theorem window_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (LowZero18Square.withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_support_subset L hw ext control src dst body h128 h129 hd he

private theorem window_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_slots_le L hw ext control src dst body h128 h129 hd he

private theorem core_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (core L ext control)+243=toffoliCount (ReflectionE1Square.core L ext control) ∧
    measurementCount (core L ext control)+85=measurementCount (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_counts L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_counts L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_counts L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  rw [if_neg (show ¬L.core.sum.length=128 by omega)] at c
  rw [if_pos high] at b
  rw [if_pos low] at a
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,toffoliCount_append,measurementCount_append]
  constructor <;> omega

private theorem core_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (core L ext control)⊆wires (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_support L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_support L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_support L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  have k3 := q3.trans k3
  have b := b3.trans b
  have a := a3.trans a
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact k3.trans c | exact c | exact b | exact a | exact Finset.Subset.refl _

private theorem core_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (core L ext control)≤Challenge.gateSlots (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_slots L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_slots L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_slots L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,Challenge.gateSlots_append]
  omega

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+243=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program L)+85=measurementCount (ReflectionE1Square.program L) := by
  have h:=core_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    (ReflectionE1Square.place_counts _ _).1,(ReflectionE1Square.place_counts _ _).2] using h

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=51761 ∧ measurementCount (program L)=52735 := by
  have a:=counts_diff L hw
  have b:=ReflectionE1Square.counts L hw
  constructor <;> omega

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (ReflectionE1Square.program L) := by
  unfold program ReflectionE1Square.program SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact core_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (ReflectionE1Square.support L hw hn)

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) :=
  fun used=>ReflectionE1Square.free L hw hn i hi (support_subset L hw used)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have full:=LowZero18Square.physical L hw hn
  rw [program_split,gatePhysical_append] at full
  exact full.1

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (ReflectionE1Square.program L) := by
  have h:=core_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    SquareCarryLoan719BF.place,Baselines.rename_gateSlots] using h

end ECDSAAdd.Entrant.ReflectionE1Low48Square
end -- original module boundary


-- ===== R2 (sqep component): square with retired poolWire 760 =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


/-! # Square -/

namespace ECDSAAdd.Entrant.R2SqEp760
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

/-! ## Square: definitions -/

/-- The retired square site: fold-pad bit 239 (= `ktmp[108]`, carry #239 of every reflected core
adder; physically `poolWire 760`). -/
def sqRet (L : CuccaroStreamedSquareWideLayout) : Wire := L.foldPad.getD 239 0
/-- Its body host: extension wire 130 (physically `poolWire 1363`). -/
def sqHost (ext : List Wire) : Wire := ext.getD 130 0
def sqSwap (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) : Equiv.Perm Wire :=
  Equiv.swap (sqRet L) (sqHost ext)
def bodySwap (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (B : Program) : Program :=
  renameProgram (sqSwap L ext) B

def branchCK760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.gPrep L++
    LowZero18Square.withLowK2 L ext control L.core.sum L.core.product
      (bodySwap L ext (OwnDiagAll12Square.bodyCKTq L control))++
    OwnDiagAll12Square.gClear L

def branchBF760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.high (L.core.product.take 256)
    (bodySwap L ext (ControlLoan1589BFFold.bBodyTq L control))

def branchAF760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.low (L.core.product.take 256)
    (bodySwap L ext (ControlLoan1589BFFold.aBodyTq L control))

def core760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK760 L ext control++branchBF760 L ext control++branchAF760 L ext control

def fastCore760 (L : ControlledPointLayout) : Program :=
  core760 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

/-- The new square: `ReflectionE1Low48Square.program` with the three body swaps. -/
def program760 (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore760 L)

/-! ## Square: positions of the two sites -/

section Sites
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
include hw

theorem foldPad_length : L.foldPad.length=254 := by
  simp [foldPad,hw.core.pad,hw.overflowPad]

omit hw in
theorem sqRet_ktmp : sqRet L=(LowZero18LowK.ktmp L).getD 108 0 := by
  simp only [sqRet,LowZero18LowK.ktmp,List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem sqRet_mem_ktmpTail : sqRet L∈(LowZero18LowK.ktmp L).drop 99 := by
  rw [sqRet_ktmp L]
  have len := LowZero18LowK.ktmp_length L hw
  rw [List.getD_eq_getElem _ _ (by omega)]
  have h : (LowZero18LowK.ktmp L)[108]'(by omega)=((LowZero18LowK.ktmp L).drop 99)[9]'(by simp; omega) := by
    simp
  rw [h]
  exact List.getElem_mem _

theorem sqRet_mem_overflow : sqRet L∈L.overflowPad := by
  have h : sqRet L=L.overflowPad.getD 111 0 := by
    simp only [sqRet,foldPad,List.getD_eq_getElem?_getD,List.getElem?_append_right
      (show L.core.pad.length≤239 by rw [hw.core.pad]; omega),hw.core.pad]
  rw [h,List.getD_eq_getElem _ _ (by rw [hw.overflowPad]; omega)]
  exact List.getElem_mem _

theorem sqRet_mem_wires : sqRet L∈L.wires := by
  simp only [CuccaroStreamedSquareWideLayout.wires,List.mem_append]
  exact Or.inr (sqRet_mem_overflow L hw)

end Sites

theorem sqHost_mem (ext : List Wire) (he : 300≤ext.length) : sqHost ext∈ext := by
  rw [sqHost,List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- `sqRet` is outside the core layout (it is an overflow-pad site). -/
theorem sqRet_not_core (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) : sqRet L∉L.core.wires := by
  have overflow := sqRet_mem_overflow L hw
  have dis := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
  exact fun used=>dis (sqRet L) used (sqRet L) overflow rfl

/-! ## Square: support facts -/

section Support
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)

/-- Everything a LowZero leaf kernel names, except the untouched tail of `ktmp`. -/
def kOuter : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++
    (LowZero18LowK.ktmp L).take 99)++ext

include hn hs hd hx hdx in
theorem ktail_away (q : Wire) (hq : q∈(LowZero18LowK.ktmp L).drop 99) :
    q∉kOuter L control ext src dst := by
  apply kdis (LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx) _ q hq
  intro w
  have e := congrArg (List.count w) (List.take_append_drop 99 (LowZero18LowK.ktmp L))
  rw [List.count_append] at e
  simp only [kOuter,LowZero18LowK.kbig2,List.count_append,List.count_cons] at e ⊢
  omega

private theorem mem_tk {l : List Wire} {n : Nat} {q : Wire} (h : q∈l.take n) : q∈l := List.mem_of_mem_take h
private theorem mem_dr {l : List Wire} {n : Nat} {q : Wire} (h : q∈l.drop n) : q∈l := List.mem_of_mem_drop h
private theorem mem_dt {l : List Wire} {a b : Nat} {q : Wire} (h : q∈(l.drop a).take b) : q∈l.take (a+b) := by
  have e : (l.drop a).take b=(l.take (a+b)).drop a := by rw [List.drop_take]; simp
  rw [e] at h
  exact List.mem_of_mem_drop h

private theorem mem_66 {l : List Wire} {q : Wire} (h : q∈l.take 66) : q∈l.take 99 := by
  have e : l.take 66=(l.take 99).take 66 := by rw [List.take_take]; rfl
  rw [e] at h
  exact List.mem_of_mem_take h

/-- Every wire of the leaf kernel's register inventory lies in `kOuter`. -/
theorem kall_outer (q : Wire) (h : q∈(LowZero18LowK.kg L ext src dst).all) :
    q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons]
  unfold LowZero18LowK.kg at h
  split_ifs at h
  all_goals
    simp only [LowZero18LowK.kgH,LowZero18LowK.kgS,KG.all,KG.X,KRegs.all,LowZero18LowK.oregs,
      LowZero18LowK.iregs,LowZero18LowK.jregsH,LowZero18LowK.jregsS,KRegs.lo,KRegs.dlo,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    repeat' (refine Or.elim h (fun h => ?_) (fun h => ?_))
    all_goals first
      | simp [h]
      | simp [mem_tk h]
      | simp [mem_dr h]
      | simp [mem_tk (mem_tk h)]
      | simp [mem_dr (mem_tk h)]
      | simp [mem_tk (mem_dr h)]
      | simp [mem_dr (mem_tk (mem_tk h))]
      | simp [mem_66 (mem_tk h)]
      | simp [mem_66 (mem_tk (mem_tk h))]
      | simp [mem_dt h]

include hw hn hs hd hx hdx in
theorem sqRet_not_outer : sqRet L∉kOuter L control ext src dst :=
  ktail_away L control hn ext src dst hs hd hx hdx _ (sqRet_mem_ktmpTail L hw)

include hw hn hs hd hx hdx in
theorem sqRet_ne_of_outer (q : Wire) (hq : q∈kOuter L control ext src dst) : sqRet L≠q :=
  fun e => sqRet_not_outer L hw control hn ext src dst hs hd hx hdx (e ▸ hq)

theorem ktmp_eq : OwnDiagLowK.ktmp L=LowZero18LowK.ktmp L := rfl

theorem tk99_outer (q : Wire) (h : q∈(LowZero18LowK.ktmp L).take 99) : q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons]; tauto

theorem ext_outer (q : Wire) (h : q∈ext) : q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append]; tauto

theorem cs_outer (q : Wire) (h : q∈control::(src++L.inputBank.take src.length)) :
    q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons] at h ⊢; tauto

include hw in
theorem target_outer : SquareCarryLoan719.target L∈kOuter L control ext src dst := by
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.target L∈(LowZero18LowK.ktmp L).take 99 := by
    change (LowZero18LowK.ktmp L).getD 67 0∈_
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : (LowZero18LowK.ktmp L)[67]'(by omega)=((LowZero18LowK.ktmp L).take 99)[67]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  exact tk99_outer L control ext src dst _ m

include hw in
theorem earlyHost_outer : SquareCarryLoan719.earlyHost L∈kOuter L control ext src dst := by
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.earlyHost L∈(LowZero18LowK.ktmp L).take 99 := by
    change (LowZero18LowK.ktmp L).getD 1 0∈_
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : (LowZero18LowK.ktmp L)[1]'(by omega)=((LowZero18LowK.ktmp L).take 99)[1]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  exact tk99_outer L control ext src dst _ m

include hw hn hs hd hx hdx in
theorem sqRet_masks :
    sqRet L∉wires (copyRegister (some control) src (L.inputBank.take src.length)) ∧
    sqRet L∉wires (eraseMask control src (L.inputBank.take src.length)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  constructor
  · intro used
    have h := List.mem_toFinset.mp (copyRegister_wires_subset (some control) src (L.inputBank.take src.length) used)
    exact ne _ (cs_outer L control ext src dst _ (by simpa only [Option.toList_some,List.singleton_append,
      List.cons_append,List.append_assoc] using h)) rfl
  · intro used
    have h := List.mem_toFinset.mp (eraseMask_wires_subset control src (L.inputBank.take src.length) used)
    exact ne _ (cs_outer L control ext src dst _ h) rfl

include hw hn hs hd hx hdx in
theorem sqRet_kernels (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) :
    sqRet L∉wires (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) ∧
    sqRet L∉wires (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have sup := LowZero18LowK.kg_support L hw ext src dst h128 hsmax hlen he
  have offAll : sqRet L∉((LowZero18LowK.kg L ext src dst).all.toFinset) := fun h =>
    ne _ (kall_outer L control ext src dst _ (List.mem_toFinset.mp h)) rfl
  have fix : SquareCarryLoan719.earlyPerm L (sqRet L)=sqRet L := by
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (ne _ (target_outer L hw control ext src dst))
      (ne _ (earlyHost_outer L hw control ext src dst))
  have mk : sqRet L∉wires (LowZero18KG.make (LowZero18LowK.kg L ext src dst)) := fun h => offAll (sup.1 h)
  have cl : sqRet L∉wires (LowZero18KG.clear (LowZero18LowK.kg L ext src dst)) := fun h => offAll (sup.2 h)
  let K := LowZero18LowK.kg L ext src dst
  let T := K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
  let C := K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c
  have o1 : LowZero18KG.make K=K.Q1++T := by simp only [LowZero18KG.make,T,List.append_assoc]
  have n1 : LowZero18Square.make L K=renameProgram (SquareCarryLoan719.earlyPerm L) K.Q1++T := by
    simp only [LowZero18Square.make,LowZero18KG.make,SquareCarryLoan719.patchKG,T,List.append_assoc]
  have o2 : LowZero18KG.clear K=C++K.Q1c := by simp only [LowZero18KG.clear,C,List.append_assoc]
  have n2 : LowZero18Square.clear L K=C++renameProgram (SquareCarryLoan719.earlyPerm L) K.Q1c := by
    simp only [LowZero18Square.clear,LowZero18KG.clear,SquareCarryLoan719.patchKG,C,List.append_assoc]
  rw [o1,wires_append,Finset.mem_union,not_or] at mk
  rw [o2,wires_append,Finset.mem_union,not_or] at cl
  constructor
  · change sqRet L∉wires (LowZero18Square.make L K)
    rw [n1,wires_append,Finset.mem_union,not_or]
    exact ⟨OwnPlusHost.rename_avoid _ _ _ fix mk.1,mk.2⟩
  · change sqRet L∉wires (LowZero18Square.clear L K)
    rw [n2,wires_append,Finset.mem_union,not_or]
    exact ⟨cl.1,OwnPlusHost.rename_avoid _ _ _ fix cl.2⟩

end Support

section Core
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)

include hw in
theorem g_core_support :
    wires (OwnDiagAll12Square.gPrep L)⊆L.core.wires.toFinset ∧
    wires (OwnDiagAll12Square.gClear L)⊆L.core.wires.toFinset := by
  let M : CuccaroStreamedSquareWideLayout := ⟨L.core,L.core.pad.take 126⟩
  have mhw : M.Widths := ⟨hw.core,by simp [M,hw.core.pad]⟩
  have sub : (L.core.cin::M.wires).toFinset⊆L.core.wires.toFinset := by
    intro q used
    have h := List.mem_toFinset.mp used
    rcases List.mem_cons.mp h with h|h
    · subst q
      simp [CuccaroStreamedSquareLayout.wires]
    · change q∈L.core.wires++L.core.pad.take 126 at h
      rcases List.mem_append.mp h with h|h
      · exact List.mem_toFinset.mpr h
      · have hp := List.mem_of_mem_take h
        simp [CuccaroStreamedSquareLayout.wires,hp]
  have support := OwnDiagAll12Square.gSum_support M mhw L.core.cin
  exact ⟨support.1.trans sub,support.2.trans sub⟩

end Core

section Free
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hext in
theorem sqHost_in : sqHost ext∈ext := sqHost_mem ext hext

include hw hdx hext in
theorem sqHost_ne_target : sqHost ext≠SquareCarryLoan719.target L := by
  intro e
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.target L∈LowZero18LowK.ktmp L := by
    change (LowZero18LowK.ktmp L).getD 67 0∈_
    exact DiagSq.getD_in _ 67 (by omega)
  have w : SquareCarryLoan719.target L∈control::L.wires :=
    List.mem_cons_of_mem _ (LowZero18LowK.ktmp_wires L _ m)
  exact hdx _ (sqHost_in ext hext) (e ▸ w)

include hx hext in
theorem sqHost_ne_ext0 : sqHost ext≠ext.getD 0 0 := by
  intro e
  rw [sqHost,List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  omega

include hw hx hdx hext in
theorem sqHost_fold_free (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqHost ext∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  apply OwnPlusHost.rename_avoid _ _ _
    (Equiv.swap_apply_of_ne_of_ne (sqHost_ne_target L hw control ext hdx hext) (sqHost_ne_ext0 ext hx hext))
  exact fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used))

include hw hn hx hdx hext in
theorem sqRet_body_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  apply OwnPlusHost.rename_avoid _ _ _
    (Equiv.swap_apply_of_ne_of_ne (ne _ (target_outer L hw control ext src dst))
      (ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))))
  exact swap_free _ _ _ (fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used)))

include hw hn hx hdx hext in
theorem withLowK2_760_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)) := by
  have m := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have k := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen hext
  have f := sqRet_body_free L hw control hn ext hx hdx hext src dst hs hd B hb
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨m.1,k.1⟩,m.2⟩,f⟩,m.1⟩,k.2⟩,m.2⟩

include hw hn hx hdx hext in
theorem core760_free : sqRet L∉wires (core760 L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have hl (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have hh (q : Wire) : L.core.high.count q≤L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := hh q
    simp only [List.count_append]
    omega
  have hs (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := hh q
    simp only [CuccaroStreamedSquareLayout.sum,List.count_append] at h ⊢
    omega
  have hp (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := withLowK2_760_free L hw control hn ext hx hdx hext L.core.low (L.core.product.take 256)
    hl hp (by omega) (by omega) (by simp [hw.core.product,low]) _ (ControlLoan1589BFFold.aBody_supportTq L hw nd control)
  have sb := withLowK2_760_free L hw control hn ext hx hdx hext L.core.high (L.core.product.take 256)
    hb hp (by omega) (by omega) (by simp [hw.core.product,high]) _ (ControlLoan1589BFFold.bBody_supportTq L hw nd control)
  have sc := withLowK2_760_free L hw control hn ext hx hdx hext L.core.sum L.core.product
    hs (fun _=>le_rfl) (by omega) (by omega) (by rw [hw.core.product,sum]) _
    (OwnDiagAll12Square.bodyCK_supportTq L hw nd control)
  have coreOff := sqRet_not_core L hw control hn
  have gs := g_core_support L hw
  have gp : sqRet L∉wires (OwnDiagAll12Square.gPrep L) := fun u => coreOff (List.mem_toFinset.mp (gs.1 u))
  have gc : sqRet L∉wires (OwnDiagAll12Square.gClear L) := fun u => coreOff (List.mem_toFinset.mp (gs.2 u))
  simp only [core760,branchCK760,branchBF760,branchAF760,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨gp,sc⟩,gc⟩,sb⟩,sa⟩

end Free

section Placed
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
private theorem pool_getD' (i : Nat) (hi : i<2613) : L.dialogPool.getD i 0=L.core.poolWire i := by
  have shape := pool_block L hw 2613 (le_refl _)
  rw [List.take_of_length_le (by rw [L.dialogPool_length hw])] at shape
  rw [shape,List.getD_eq_getElem _ _ (by simp [wireBlock];omega)]
  simp [wireBlock]

include hw in
theorem sqRet_pool760 : sqRet L.dialogStreamedSquareWide=L.core.poolWire 760 := by
  rw [sqRet_ktmp,← ktmp_eq,SquareCarryLoan719Inventory.ktmp_layout L hw,List.getD_eq_getElem _ _ (by
    simp only [List.length_take,List.length_drop,L.dialogPool_length hw]
    omega)]
  simp only [List.getElem_take,List.getElem_drop,Nat.reduceAdd]
  have bound : 760<L.dialogPool.length := by rw [L.dialogPool_length hw];omega
  have same := pool_getD' L hw 760 (by omega)
  rw [List.getD_eq_getElem L.dialogPool 0 bound] at same
  exact same

theorem sqHost_pool1363 : sqHost (OwnDiagAll12Square.kext L)=L.core.poolWire 1363 := by
  simp [sqHost,OwnDiagAll12Square.kext,wireBlock]

include hw hn in
private theorem pool_fix (k a b : Nat) (hk : k<2613) (ha : a<2613) (hb : b<2613) (na : k≠a) (nb : k≠b) :
    Equiv.swap (L.core.poolWire a) (L.core.poolWire b) (L.core.poolWire k)=L.core.poolWire k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq
    exact na (pool_inj L hw hn k a hk ha eq)
  · intro eq
    exact nb (pool_inj L hw hn k b hk hb eq)

include hw hn in
/-- Every placement map of the square fixes pool sites 760 and 1363. -/
theorem place_fix (k : Nat) (hk : k=760 ∨ k=1363) (P : Program) (free : L.core.poolWire k∉wires P) :
    L.core.poolWire k∉wires (SquareCarryLoan719BF.place L P) := by
  have kb : k<2613 := by omega
  have blockFix : Square5Placement.blockPerm L 202 (L.core.poolWire k)=L.core.poolWire k := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) k kb]
    rcases hk with rfl|rfl <;> rfl
  have p0 := OwnPlusHost.rename_avoid _ _ _ blockFix free
  have p1 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 766 1530 kb (by omega) (by omega) (by omega) (by omega)) p0
  have p2 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 765 1531 kb (by omega) (by omega) (by omega) (by omega)) p1
  have p3 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 767 1532 kb (by omega) (by omega) (by omega) (by omega)) p2
  have p4 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 770 1536 kb (by omega) (by omega) (by omega) (by omega)) p3
  have p5 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 1285 1537 kb (by omega) (by omega) (by omega) (by omega)) p4
  have p6 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 1286 1538 kb (by omega) (by omega) (by omega) (by omega)) p5
  have p7 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 769 1539 kb (by omega) (by omega) (by omega) (by omega)) p6
  have p8 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 768 775 kb (by omega) (by omega) (by omega) (by omega)) p7
  have p9 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 718 907 kb (by omega) (by omega) (by omega) (by omega)) p8
  simpa only [SquareCarryLoan719BF.place,OwnPlusSquare.swap,OwnGuardSquare.swap,
    OwnQ4Square.swap,OwnQ5Square.swap,OwnDiagAll12PlacedQ6.swap,OwnDiagAll12PlacedQ7.swap,
    PrefixFrontierSquare1591.swap,Prefix1590Square.swap,ControlLoan1589Square.swap] using p9

include hw hn in
/-- **R2 square deliverable**: the new square never touches physical pool site 760. -/
theorem square760_free : L.core.poolWire 760∉wires (program760 L) := by
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have core := core760_free L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic controlND (OwnDiagAll12Square.kext L) he.nodup he.away he.len
  rw [sqRet_pool760 L hw] at core
  exact place_fix L hw hn 760 (Or.inl rfl) _ core

end Placed

/-! ## Square: counts, slots, physicality, support -/

theorem gatePhysical_rename_iff (e : Equiv.Perm Wire) (P : Program) :
    GatePhysical (renameProgram e P)↔GatePhysical P := by
  constructor
  · intro h i hi
    have hh := h (renameInstr e i) (List.mem_map_of_mem hi)
    cases i <;> simp_all [renameInstr,RecordedQuantum.PhysicalInstr,ECDSAAdd.ProperGate,e.injective.eq_iff]
  · exact gatePhysical_rename e e.injective P

theorem place_physical_iff (L : ControlledPointLayout) (P : Program) :
    GatePhysical (SquareCarryLoan719BF.place L P)↔GatePhysical P := by
  simp only [SquareCarryLoan719BF.place,gatePhysical_rename_iff]

theorem fastCore760_shape (L : ControlledPointLayout) :
    ReflectionE1Low48Square.program L=SquareCarryLoan719BF.place L (ReflectionE1Low48Square.fastCore L) := rfl

theorem program760_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program760 L) := by
  have old := ReflectionE1Low48Square.physical L hw hn
  rw [fastCore760_shape,place_physical_iff] at old
  rw [program760,place_physical_iff]
  simp only [ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,
    gatePhysical_append,gatePhysical_rename_iff] at old
  simp only [fastCore760,core760,branchCK760,branchBF760,branchAF760,LowZero18Square.withLowK2,bodySwap,
    gatePhysical_append,gatePhysical_rename_iff]
  exact old

theorem program760_counts (L : ControlledPointLayout) :
    toffoliCount (program760 L)=toffoliCount (ReflectionE1Low48Square.program L) ∧
    measurementCount (program760 L)=measurementCount (ReflectionE1Low48Square.program L) := by
  rw [fastCore760_shape]
  simp only [program760,SquareCarryLoan719BF.place,fastCore760,core760,branchCK760,branchBF760,branchAF760,
    ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,bodySwap,
    toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    and_self]

theorem program760_slots (L : ControlledPointLayout) :
    Challenge.gateSlots (program760 L)=Challenge.gateSlots (ReflectionE1Low48Square.program L) := by
  rw [fastCore760_shape]
  simp only [program760,SquareCarryLoan719BF.place,fastCore760,core760,branchCK760,branchBF760,branchAF760,
    ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,bodySwap,
    Challenge.gateSlots_append,Baselines.rename_gateSlots]

theorem counts_diff760 (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program760 L)+243=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program760 L)+85=measurementCount (ReflectionE1Square.program L) := by
  rw [(program760_counts L).1,(program760_counts L).2]
  exact ReflectionE1Low48Square.counts_diff L hw

theorem slots_le760 (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program760 L)≤Challenge.gateSlots (ReflectionE1Square.program L) := by
  rw [program760_slots]; exact ReflectionE1Low48Square.slots_le L hw

theorem rename_ins (e : Equiv.Perm Wire) (h : Wire) (P Q : Program)
    (sub : wires P⊆insert h (wires Q)) (fix : e h=h) :
    wires (renameProgram e P)⊆insert h (wires (renameProgram e Q)) := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (sub hx) with e'|hx'
  · subst x; rw [fix]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx')

theorem swap_ins (a b : Wire) (P : Program) (hb : b∉wires P) :
    wires (renameProgram (Equiv.swap a b) P)⊆insert b (wires P) :=
  (swap_support a b P hb).trans (Finset.insert_subset_insert _ (Finset.erase_subset _ _))

section SupportNew
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hw hx hdx hext in
theorem withLowK2_ins (src dst : List Wire) (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    wires (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))⊆
      insert (sqHost ext) (wires (LowZero18Square.withLowK2 L ext control src dst B)) := by
  have bfree : sqHost ext∉wires B := fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used))
  have fix : SquareCarryLoan719.foldPerm L ext (sqHost ext)=sqHost ext := by
    rw [SquareCarryLoan719.foldPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (sqHost_ne_target L hw control ext hdx hext) (sqHost_ne_ext0 ext hx hext)
  have body := rename_ins _ _ _ _ (swap_ins (sqRet L) (sqHost ext) B bfree) fix
  intro q hq
  simp only [LowZero18Square.withLowK2,bodySwap,sqSwap,wires_append,Finset.mem_union,Finset.mem_insert] at hq ⊢
  rcases hq with ((((((h|h)|h)|h)|h)|h)|h)
  all_goals first
    | (rcases Finset.mem_insert.mp (body h) with e|e
       · exact Or.inl e
       · tauto)
    | tauto

include hw hn hx hdx hext in
theorem core760_ins : wires (core760 L ext control)⊆
    insert (sqHost ext) (wires (ReflectionE1Low48Square.core L ext control)) := by
  have nd := (List.nodup_cons.mp hn).2
  have a := withLowK2_ins L hw control ext hx hdx hext L.core.low (L.core.product.take 256) _
    (ControlLoan1589BFFold.aBody_supportTq L hw nd control)
  have b := withLowK2_ins L hw control ext hx hdx hext L.core.high (L.core.product.take 256) _
    (ControlLoan1589BFFold.bBody_supportTq L hw nd control)
  have c := withLowK2_ins L hw control ext hx hdx hext L.core.sum L.core.product _
    (OwnDiagAll12Square.bodyCK_supportTq L hw nd control)
  intro q hq
  simp only [core760,branchCK760,branchBF760,branchAF760,wires_append,Finset.mem_union] at hq
  simp only [ReflectionE1Low48Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,wires_append,Finset.mem_union,Finset.mem_insert]
  rcases hq with (((h|h)|h)|h)|h
  · tauto
  · rcases Finset.mem_insert.mp (c h) with e|e <;> tauto
  · tauto
  · rcases Finset.mem_insert.mp (b h) with e|e <;> tauto
  · rcases Finset.mem_insert.mp (a h) with e|e <;> tauto

end SupportNew

section SupportPlaced
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw hn in
theorem place_ins (P Q : Program) (sub : wires P⊆insert (L.core.poolWire 1363) (wires Q)) :
    wires (SquareCarryLoan719BF.place L P)⊆insert (L.core.poolWire 1363) (wires (SquareCarryLoan719BF.place L Q)) := by
  have kb : 1363<2613 := by omega
  have blockFix : Square5Placement.blockPerm L 202 (L.core.poolWire 1363)=L.core.poolWire 1363 := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) 1363 kb]; rfl
  have f (a b : Nat) (ha : a<2613) (hb : b<2613) (na : 1363≠a) (nb : 1363≠b) :=
    pool_fix L hw hn 1363 a b kb ha hb na nb
  simp only [SquareCarryLoan719BF.place]
  apply rename_ins _ _ _ _ _ (f 718 907 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 768 775 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 769 1539 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 1286 1538 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 1285 1537 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 770 1536 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 767 1532 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 765 1531 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 766 1530 (by omega) (by omega) (by omega) (by omega))
  exact rename_ins _ _ _ _ sub blockFix

include hw hn in
/-- New square support: the old square's support with site 760 replaced by site 1363. -/
theorem program760_support_subset :
    wires (program760 L)⊆insert (L.core.poolWire 1363)
      ((wires (ReflectionE1Low48Square.program L)).erase (L.core.poolWire 760)) := by
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have core := core760_ins L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic controlND (OwnDiagAll12Square.kext L) he.nodup he.away he.len
  rw [sqHost_pool1363 L] at core
  have placed := place_ins L hw hn _ _ core
  have free := square760_free L hw hn
  intro q hq
  rcases Finset.mem_insert.mp (placed hq) with e|e
  · exact e ▸ Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_erase.mpr ⟨fun h => free (h ▸ hq),e⟩

include hw hn in
theorem program760_support : wires (program760 L)⊆(OB5Support.sites L).toFinset := by
  have old := ReflectionE1Low48Square.support L hw hn
  intro q hq
  rcases Finset.mem_insert.mp (program760_support_subset L hw hn hq) with e|e
  · subst e
    simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1363,⟨by omega,by omega⟩,rfl⟩)))))
  · exact old (Finset.mem_of_mem_erase e)

include hw hn in
theorem program760_free_old (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program760 L) := by
  intro used
  rcases Finset.mem_insert.mp (program760_support_subset L hw hn used) with e|e
  · have ib : i<2613 := by simp at hi; omega
    have := pool_inj L hw hn i 1363 ib (by omega) e
    subst this; simp at hi
  · exact ReflectionE1Low48Square.free L hw hn i hi (Finset.mem_of_mem_erase e)

end SupportPlaced

/-! ## Square: the host is clean when the body starts -/

theorem top_bits_zero (r : List Wire) (st : BasisState) (k : Nat) (h : regValue r st<2^k)
    (q : Wire) (hq : q∈r.drop k) : st q=false := by
  by_cases hk : k≤r.length
  · have e := regValue_append (r.take k) (r.drop k) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left hk] at e
    have z : regValue (r.drop k) st=0 := by
      by_contra nz
      have : 2^k≤2^k*regValue (r.drop k) st := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero nz)
      omega
    exact (regValue_zero _ _).mp z q hq
  · rw [List.drop_eq_nil_of_le (by omega)] at hq
    simp at hq

theorem host_not_drop (ext : List Wire) (hx : ext.Nodup) (hext : 300≤ext.length) (k : Nat) (hk : 131≤k) :
    sqHost ext∉ext.drop k := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_drop,sqHost,List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  omega

theorem host_not_take (ext : List Wire) (hx : ext.Nodup) (hext : 300≤ext.length) :
    sqHost ext∉ext.take 130 := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_take,sqHost,List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  simp at hi
  omega

private theorem mem_drop_mono {l : List Wire} {a b : Nat} {q : Wire} (h : q∈l.drop b) (hab : a≤b) :
    q∈l.drop a := by
  have e : l.drop b=(l.drop a).drop (b-a) := by rw [List.drop_drop]; congr 1; omega
  rw [e] at h
  exact List.mem_of_mem_drop h

/-- After copy/make/erase the body host is zero: for 128-bit sources it is outside every kernel
register; for the 129-bit sum it is bit 130 of `T = 2·lo·hi < 2^130`. -/
theorem prefix_host_zero (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (s : State) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (r1 r2 r3 : List Bool) :
    (run (eraseMask control src (L.inputBank.take src.length)) r3
      (run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2
        (run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s))).basis (sqHost ext)=false := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have hostE := sqHost_in ext he
  -- erase does not touch the host
  have eraseOff : sqHost ext∉wires (eraseMask control src (L.inputBank.take src.length)) := by
    intro used
    have h := List.mem_toFinset.mp (eraseMask_wires_subset control src (L.inputBank.take src.length) used)
    rcases List.mem_cons.mp h with h|h
    · exact hdx _ hostE (by simp [h])
    · rcases List.mem_append.mp h with h|h
      · exact extSrc _ hostE h
      · exact extB _ hostE h
  rw [run_preserves_outside _ _ _ _ eraseOff]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := LowZero18Square.make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  rw [mkEq]
  rw [hKR] at mk
  by_cases h : src.length=128
  · -- the host lies in no kernel register
    have notT : sqHost ext∉(LowZero18LowK.oregs L ext src dst).T := by
      intro m
      have m' : sqHost ext∈(ext.take 132).take 130 := by
        simpa [LowZero18LowK.oregs,h] using m
      rw [List.take_take] at m'
      exact host_not_take ext hx he (by simpa using m')
    have notX : sqHost ext∉(LowZero18LowK.kg L ext src dst).X := by
      intro m
      rw [LowZero18LowK.kg,if_pos h] at m
      simp only [LowZero18LowK.kgH,KG.X,LowZero18LowK.iregs,LowZero18LowK.jregsH,List.mem_append,
        List.not_mem_nil,or_false] at m
      rcases m with ((m|m)|(m|m))
      · exact tmpE _ (List.mem_of_mem_drop (List.mem_of_mem_take m)) hostE
      · exact host_not_drop ext hx he 132 (by omega) (List.mem_of_mem_take m)
      · exact host_not_drop ext hx he 198 (by omega) (List.mem_of_mem_take (List.mem_of_mem_take m))
      · exact host_not_drop ext hx he 232 (by omega) (List.mem_of_mem_take m)
    have notD : sqHost ext∉(LowZero18LowK.oregs L ext src dst).dst := fun m =>
      (dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega) : ∀q∈ext,q∉dst) _ hostE m
    rw [mk.2.2.2.2.2.2.2 _ notD notT notX,u0s _ (extB _ hostE)]
    exact ext0 _ hostE
  · -- the host is bit 130 of T = 2·lo·hi < 2^130
    have h129 : src.length=129 := by omega
    have tv := mk.2.2.2.1
    have lo_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
    have hi_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
    have lol : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
      simp [LowZero18LowK.oregs,KRegs.lo,sizes.1,h129]
    have hil : (LowZero18LowK.oregs L ext src dst).hi.length=65 := by
      simp [LowZero18LowK.oregs,KRegs.hi,sizes.1,h129]
    rw [lol] at lo_lt
    rw [hil] at hi_lt
    have prod : 2*regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis*
        regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^130 := by
      have := Nat.mul_lt_mul'' lo_lt hi_lt
      have e : (2:Nat)^130=2*(2^64*2^65) := by norm_num
      rw [e,Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left this (by norm_num)
    rw [← tv] at prod
    apply top_bits_zero _ _ 130 prod
    have tl : (LowZero18LowK.oregs L ext src dst).T=ext.take 132 := by
      simp [LowZero18LowK.oregs,h129]
    rw [tl,sqHost,List.getD_eq_getElem _ _ (by omega)]
    have : ext[130]'(by omega)=((ext.take 132).drop 130)[0]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _

/-! ## Square: run equality -/

theorem mid_swap (Pre X Post : Program) (a b : Wire) (s : State) (m : List Bool)
    (ua : (run Pre (m.take (measurementCount Pre)) s).basis a=false)
    (ub : (run Pre (m.take (measurementCount Pre)) s).basis b=false)
    (bX : b∉wires X) (aPost : a∉wires Post)
    (fin : (run (Pre++X++Post) m s).basis a=false) :
    run (Pre++renameProgram (Equiv.swap a b) X++Post) m s=run (Pre++X++Post) m s := by
  have mc := (renameProgram_counts (Equiv.swap a b) X).2
  simp only [run_append,measurementCount_append,mc] at fin ⊢
  have e : List.take (measurementCount Pre) (List.take (measurementCount Pre+measurementCount X) m)=
      List.take (measurementCount Pre) m := by rw [List.take_take]; congr 1; omega
  simp only [e] at fin ⊢
  generalize run Pre (List.take (measurementCount Pre) m) s=u at ua ub fin ⊢
  rw [run_preserves_outside Post _ _ a aPost] at fin
  congr 1
  exact swap_run_eq a b X u _ ua ub fin ((run_preserves_outside X _ u b bX).trans ub)

theorem swaps_commute (a b c d : Wire) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (P : Program) :
    renameProgram (Equiv.swap c d) (renameProgram (Equiv.swap a b) P)=
      renameProgram (Equiv.swap a b) (renameProgram (Equiv.swap c d) P) := by
  rw [renameProgram_comp,renameProgram_comp]
  congr 1
  funext x
  simp only [Function.comp,Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem withLowK2_swap_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0)
    (fin : (run (LowZero18Square.withLowK2 L ext control src dst B) m s).basis (sqRet L)=false) :
    run (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)) m s=
      run (LowZero18Square.withLowK2 L ext control src dst B) m s := by
  have masks := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have kern := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen he
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have rt := ne _ (target_outer L hw control ext src dst)
  have r0 := ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))
  have ht := sqHost_ne_target L hw control ext hdx he
  have h0 := sqHost_ne_ext0 ext hx he
  have com : renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)=
      renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
    rw [SquareCarryLoan719.foldPerm_eq L hw,bodySwap,sqSwap]
    exact swaps_commute _ _ _ _ rt r0 ht h0 B
  let Pre := copyRegister (some control) src (L.inputBank.take src.length)++
    LowZero18Square.make L (LowZero18LowK.kg L ext src dst)++eraseMask control src (L.inputBank.take src.length)
  let Post := copyRegister (some control) src (L.inputBank.take src.length)++
    LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)++eraseMask control src (L.inputBank.take src.length)
  have s0 : LowZero18Square.withLowK2 L ext control src dst B=
      Pre++renameProgram (SquareCarryLoan719.foldPerm L ext) B++Post := by
    simp only [LowZero18Square.withLowK2,Pre,Post,List.append_assoc]
  have s1 : LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)=
      Pre++renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B)++Post := by
    rw [← com]
    simp only [LowZero18Square.withLowK2,Pre,Post,List.append_assoc]
  rw [s0] at fin
  rw [s1,s0]
  have retPre : sqRet L∉wires Pre := by
    simp only [Pre,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨masks.1,kern.1⟩,masks.2⟩
  have retPost : sqRet L∉wires Post := by
    simp only [Post,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨masks.1,kern.2⟩,masks.2⟩
  have retS : s.basis (sqRet L)=false := by
    apply (regValue_zero _ _).mp hc.pad
    exact DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega)
  apply mid_swap _ _ _ _ _ s m ((run_preserves_outside _ _ _ _ retPre).trans retS) _
    (sqHost_fold_free L hw control ext hx hdx he B hb) retPost fin
  simp only [Pre,run_append]
  exact prefix_host_zero L hw control hn src dst hs hd h128 hsmax hlen ext hx hdx he s hc hzero hz _ _ _

theorem run3 (A W C : Program) (s : State) (m : List Bool) :
    run (A++W++C) m s=run C (m.drop (measurementCount A+measurementCount W))
      (run W ((m.drop (measurementCount A)).take (measurementCount W)) (run A (m.take (measurementCount A)) s)) := by
  simp only [run_append,measurementCount_append]
  have e1 : List.take (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=
      List.take (measurementCount A) m := by rw [List.take_take]; congr 1; omega
  have e2 : List.drop (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=
      List.take (measurementCount W) (List.drop (measurementCount A) m) := by
    rw [List.drop_take]; congr 1; omega
  rw [e1,e2]

theorem withLowK2_swap_mc (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (B : Program) :
    measurementCount (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) := by
  simp only [LowZero18Square.withLowK2,bodySwap,measurementCount_append,(renameProgram_counts _ _).2]

section Branches
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire) (control : Wire)
  (hn : (control::L.wires).Nodup)

include hw in
theorem sqRet_not_out (hn' : L.wires.Nodup) : sqRet L∉L.core.out :=
  (L.pairAuxAway hn' (sqRet L) (by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega))))).2

include hw in
theorem sqRet_clean (st : BasisState) (hc : L.PairClean st) : st (sqRet L)=false :=
  (regValue_zero _ _).mp hc.pad _ (DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega))

include hw hn in
theorem branchBF760_run_eq (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchBF760 L ext control) records s=run (LowZero18Square.branchBF L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have old := (LowZero18Square.branchBF_correct L hw ext control hn B O hO s records hb ho hp0 hc he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  exact withLowK2_swap_run_eq L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len _
    (ControlLoan1589BFFold.bBody_supportTq L hw nd control) s records hc dstZero hz old

include hw hn in
theorem branchAF760_run_eq (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchAF760 L ext control) records s=run (LowZero18Square.branchAF L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have old := (LowZero18Square.branchAF_correct L hw ext control hn A O hO s records ha ho hp0 hc he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  exact withLowK2_swap_run_eq L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len _
    (ControlLoan1589BFFold.aBody_supportTq L hw nd control) s records hc dstZero hz old

end Branches

theorem branchCK760_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hsum : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchCK760 L ext control) records s=run (LowZero18Square.branchCK L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  let W := LowZero18Square.withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)
  let W' := LowZero18Square.withLowK2 L ext control L.core.sum L.core.product
    (bodySwap L ext (OwnDiagAll12Square.bodyCKTq L control))
  let mp := measurementCount (OwnDiagAll12Square.gPrep L)
  let u := run (OwnDiagAll12Square.gPrep L) (records.take mp) s
  have prep := OwnDiagAll12Square.gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hsum,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (OwnDiagAll12Square.sum_in L control q bad)))).trans hz
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have gOff : sqRet L∉wires (OwnDiagAll12Square.gClear L) := fun used =>
    sqRet_not_core L hw control hn (List.mem_toFinset.mp ((g_core_support L hw).2 used))
  have old := (LowZero18Square.branchCK_correct L hw ext control hn A B O hO s records ha hsum bound ho hp0 hc he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  have shapeOld : LowZero18Square.branchCK L ext control=OwnDiagAll12Square.gPrep L++W++OwnDiagAll12Square.gClear L := rfl
  have shapeNew : branchCK760 L ext control=OwnDiagAll12Square.gPrep L++W'++OwnDiagAll12Square.gClear L := rfl
  rw [shapeOld,run3,run_preserves_outside _ _ _ _ gOff] at old
  have mid := withLowK2_swap_run_eq L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len _
    (OwnDiagAll12Square.bodyCK_supportTq L hw nd control) u _ cleanU productU hzU old
  rw [shapeNew,shapeOld,run3,run3,withLowK2_swap_mc]
  exact congrArg _ mid

theorem core760_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (core760 L ext control) records s=run (ReflectionE1Low48Square.core L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have keepAll (t : State) (hf : ∀q,q∉L.core.out → t.basis q=s.basis q) :
      regValue L.core.low t.basis=A ∧ regValue L.core.high t.basis=B ∧
      regValue L.core.product t.basis=0 ∧ regValue ext t.basis=0 ∧ L.PairClean t.basis := by
    refine ⟨regValue_congr _ _ _ (fun q hq => hf q (lowAway q hq)),
      regValue_congr _ _ _ (fun q hq => hf q (highAway q hq)),
      (regValue_congr _ _ _ (fun q hq => hf q (List.disjoint_left.mp disProduct hq))).trans hp0,
      (regValue_congr _ _ _ (fun q hq => hf q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz,
      L.squareFrame_clean nd s.basis t.basis _ ⟨rfl,hf⟩ hc⟩
  let CK := LowZero18Square.branchCK L ext control
  let BF := LowZero18Square.branchBF L ext control
  let AF := LowZero18Square.branchAF L ext control
  have mcC : measurementCount (branchCK760 L ext control)=measurementCount CK := by
    simp only [branchCK760,CK,LowZero18Square.branchCK,measurementCount_append,withLowK2_swap_mc]
  have mcB : measurementCount (branchBF760 L ext control)=measurementCount BF := withLowK2_swap_mc _ _ _ _ _ _
  have e0 : core760 L ext control=branchCK760 L ext control++branchBF760 L ext control++branchAF760 L ext control := rfl
  have e1 : ReflectionE1Low48Square.core L ext control=CK++BF++AF := rfl
  rw [e0,e1,run3,run3,mcC,mcB]
  have eqC := branchCK760_run_eq L hw ext control hn A B O hO s (records.take (measurementCount CK)) rfl sumB
    sumBound ho hp0 hc he hz
  rw [eqC]
  have rC := LowZero18Square.branchCK_correct L hw ext control hn A B O hO s (records.take (measurementCount CK))
    rfl sumB sumBound ho hp0 hc he hz
  generalize run CK (records.take (measurementCount CK)) s=t1 at rC ⊢
  have k1 := keepAll t1 rC.2.2
  have hO1 : regValue L.core.out t1.basis<SquareReduction.p := by rw [rC.2.1]; exact ofCast_lt _ _
  have eqB := branchBF760_run_eq L hw ext control hn B _ hO1 t1
    ((records.drop (measurementCount CK)).take (measurementCount BF)) k1.2.1 rfl k1.2.2.1 k1.2.2.2.2 he k1.2.2.2.1
  rw [eqB]
  have rB := LowZero18Square.branchBF_correct L hw ext control hn B _ hO1 t1
    ((records.drop (measurementCount CK)).take (measurementCount BF)) k1.2.1 rfl k1.2.2.1 k1.2.2.2.2 he k1.2.2.2.1
  generalize run BF ((records.drop (measurementCount CK)).take (measurementCount BF)) t1=t2 at rB ⊢
  have k2 := keepAll t2 (fun q hq => (rB.2.2 q hq).trans (rC.2.2 q hq))
  have hO2 : regValue L.core.out t2.basis<SquareReduction.p := by rw [rB.2.1]; exact ofCast_lt _ _
  exact branchAF760_run_eq L hw ext control hn A _ hO2 t2 _ k2.1 rfl k2.2.2.1 k2.2.2.2.2 he k2.2.2.2.1

section Final
open Secp256k1 CompressedPointDialog

theorem fastCore760_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (hX : X<p)
    (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (fastCore760 L) m s=run (ReflectionE1Low48Square.fastCore L) m s := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have extOK:=OwnDiagAll12Square.kext_ok L hw hn
  have hext : ECDSAAdd.Entrant.ExtOK K L.core.generic (OwnDiagAll12Square.kext L) :=
    ⟨extOK.nodup,extOK.away,extOK.len⟩
  exact core760_run_eq K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hext hz

private theorem pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

/-- **R2 square deliverable**: same hypotheses as `ReflectionE1Low48Square.boundary`. -/
theorem program760_run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program760 L) m s=run (ReflectionE1Low48Square.program L) m s := by
  have core := fastCore760_run_eq L hw hn X.val Y.val X.isLt s m v.x v.y v.clean
  have result := ReflectionE1Low48Square.fastCore_boundary L hw hn X Y G origin s m v
  have clean : regValue L.dialogPool (run (ReflectionE1Low48Square.fastCore L) m s).basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x' L hn q hq)),v.clean]
  have eNew := ReflectionE1Square.place_run_eq L hw (fastCore760 L) s m v.clean (by rw [core]; exact clean)
  have eOld := ReflectionE1Square.place_run_eq L hw (ReflectionE1Low48Square.fastCore L) s m v.clean clean
  change run (program760 L) m s=run (fastCore760 L) m s at eNew
  change run (ReflectionE1Low48Square.program L) m s=run (ReflectionE1Low48Square.fastCore L) m s at eOld
  rw [eNew,eOld,core]

/-- The new square satisfies the old square's boundary verbatim. -/
theorem program760_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program760 L) m s).phase=s.phase ∧
    regValue L.point.x (run (program760 L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program760 L) m s).basis q=s.basis q := by
  rw [program760_run_eq L hw hn X Y G origin s m v]
  exact ReflectionE1Low48Square.boundary L hw hn X Y G origin s m v

end Final

end ECDSAAdd.Entrant.R2SqEp760

end -- R2 square

-- ===== Exit-side merged tick (ExitMerge) in the multiplication kernel =====
section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed
namespace ECDSAAdd.Entrant.InverseFour15
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
def sites15 : List Wire := MorningFour.sites ++ [530]
def candidate15 : Program := [
  .X 527,
  .CX 526 527,
  .CX 526 786,
  .X 1551,
  .CX 1552 1551,
  .CX 1553 1551,
  .CX 1554 1551,
  .CCX 522 1551 527,
  .CX 1554 1551,
  .CX 1553 1551,
  .CX 1552 1551,
  .X 1551,
  .CX 526 525,
  .X 526,
  .CX 525 526,
  .CX 1553 526,
  .CX 1554 526,
  .CCX 525 526 528,
  .CX 1554 526,
  .CX 1553 526,
  .CX 525 526,
  .X 526,
  .CX 526 525,
  .CX 525 524,
  .CX 526 524,
  .X 528,
  .CX 524 528,
  .CX 1552 528,
  .CX 1554 528,
  .CCX 524 528 529,
  .CX 1554 528,
  .CX 1552 528,
  .CX 524 528,
  .X 528,
  .CX 526 524,
  .CX 525 524,
  .CX 526 524,
  .CX 528 524,
  .CX 1552 524,
  .CX 1553 524,
  .CX 524 528,
  .CX 1552 528,
  .CX 1553 528,
  .CCX 524 528 786,
  .CX 1553 528,
  .CX 1552 528,
  .CX 524 528,
  .CX 1553 524,
  .CX 1552 524,
  .CX 528 524,
  .CX 526 524,
  .CX 526 523,
  .CX 523 524,
  .CX 526 524,
  .CX 786 524,
  .CX 1552 524,
  .CCX 523 524 787,
  .CX 1552 524,
  .CX 786 524,
  .CX 526 524,
  .CX 523 524,
  .CX 526 523,
  .CX 528 524,
  .CX 1553 524,
  .CX 1554 524,
  .CX 524 525,
  .CX 526 525,
  .CX 529 525,
  .CX 786 525,
  .CX 1553 525,
  .CX 1554 525,
  .CCX 524 525 788,
  .CX 1554 525,
  .CX 1553 525,
  .CX 786 525,
  .CX 529 525,
  .CX 526 525,
  .CX 524 525,
  .CX 1554 524,
  .CX 1553 524,
  .CX 528 524,
  .measureX 528 [] [.Z 523, .Z 524, .Z 526, .Z 529, .Z 786, .Z 787, .Z 788, .CZ 523 524, .CZ 523 526, .CZ 523 786, .CZ 523 1552, .CZ 524 529, .CZ 524 1553, .CZ 525 529, .CZ 525 786, .CZ 525 1554],
  .CX 525 524,
  .CX 788 524,
  .CCX 523 524 528,
  .CX 788 524,
  .CX 525 524,
  .X 523,
  .CX 524 523,
  .CX 525 523,
  .CX 528 523,
  .CX 788 523,
  .CX 1551 523,
  .CX 1552 523,
  .CX 1553 523,
  .CX 1554 523,
  .CCX 522 523 789,
  .CX 1554 523,
  .CX 1553 523,
  .CX 1552 523,
  .CX 1551 523,
  .CX 788 523,
  .CX 528 523,
  .CX 525 523,
  .CX 524 523,
  .X 523,
  .CX 524 523,
  .X 1551,
  .CX 1552 1551,
  .CX 1553 1551,
  .CX 1554 1551,
  .CCX 523 1551 790,
  .CX 1554 1551,
  .CX 1553 1551,
  .CX 1552 1551,
  .X 1551,
  .CX 524 523,
  .X 526,
  .CX 529 526,
  .CX 786 526,
  .CX 1551 526,
  .CX 1552 526,
  .CX 1553 526,
  .CX 525 523,
  .CCX 526 523 791,
  .CX 525 523,
  .CX 1553 526,
  .CX 1552 526,
  .CX 1551 526,
  .CX 786 526,
  .CX 529 526,
  .X 526,
  .CX 523 522,
  .X 526,
  .CX 529 526,
  .CX 786 526,
  .CX 790 526,
  .CX 1554 526,
  .CCX 522 526 1556,
  .CX 1554 526,
  .CX 790 526,
  .CX 786 526,
  .CX 529 526,
  .X 526,
  .CX 523 522,
  .CX 523 522,
  .CX 522 525,
  .CX 529 525,
  .CX 788 525,
  .CX 790 525,
  .CX 791 525,
  .CX 1551 525,
  .CX 1552 525,
  .CX 1554 525,
  .CCX 522 525 1557,
  .CX 1554 525,
  .CX 1552 525,
  .CX 1551 525,
  .CX 791 525,
  .CX 790 525,
  .CX 788 525,
  .CX 529 525,
  .CX 522 525,
  .CX 523 522,
  .CX 524 522,
  .CX 529 526,
  .CX 786 526,
  .CX 790 526,
  .CX 1551 526,
  .CX 1552 526,
  .CX 1553 526,
  .CCX 522 526 1558,
  .CX 1553 526,
  .CX 1552 526,
  .CX 1551 526,
  .CX 790 526,
  .CX 786 526,
  .CX 529 526,
  .CX 524 522,
  .X 525,
  .CX 526 525,
  .CX 786 525,
  .CX 788 525,
  .CX 1551 525,
  .CX 1552 525,
  .CX 527 523,
  .CX 528 523,
  .CX 787 523,
  .CX 788 523,
  .CX 791 523,
  .CX 1556 523,
  .CX 1558 523,
  .CCX 525 523 530,
  .CX 1558 523,
  .CX 1556 523,
  .CX 791 523,
  .CX 788 523,
  .CX 787 523,
  .CX 528 523,
  .CX 527 523,
  .CX 1552 525,
  .CX 1551 525,
  .CX 788 525,
  .CX 786 525,
  .CX 526 525,
  .X 525,
  .CX 1551 529,
  .CX 1551 787,
  .CX 1551 790,
  .CX 1551 1552,
  .CX 1551 530,
  .CX 523 522,
  .X 523,
  .CX 522 523,
  .CX 525 523,
  .CX 526 523,
  .CX 528 523,
  .CX 786 523,
  .CX 788 523,
  .CX 791 523,
  .CX 1552 523,
  .CX 1556 523,
  .CX 530 523,
  .CCX 522 523 1551,
  .CX 530 523,
  .CX 1556 523,
  .CX 1552 523,
  .CX 791 523,
  .CX 788 523,
  .CX 786 523,
  .CX 528 523,
  .CX 526 523,
  .CX 525 523,
  .CX 522 523,
  .X 523,
  .CX 523 522,
  .X 788,
  .X 787,
  .X 529,
  .CX 530 1553,
  .CX 530 1552,
  .CX 530 1551,
  .CX 530 790,
  .CX 530 788,
  .CX 530 787,
  .CX 530 529,
  .CX 530 528,
  .CX 1558 1553,
  .CX 1558 1552,
  .CX 1558 790,
  .CX 1558 788,
  .CX 1558 786,
  .CX 1558 525,
  .CX 530 1558,
  .CX 1558 530,
  .CX 530 1558,
  .CX 1557 530,
  .CX 1557 1552,
  .CX 1557 791,
  .CX 1557 789,
  .CX 1557 787,
  .CX 1557 786,
  .CX 1557 526,
  .CX 1557 525,
  .CX 1558 1557,
  .CX 1557 1558,
  .CX 1558 1557,
  .CX 1556 1558,
  .CX 1556 1554,
  .CX 1556 1553,
  .CX 1556 1552,
  .CX 1556 1551,
  .CX 1556 791,
  .CX 1556 789,
  .CX 1556 788,
  .CX 1556 787,
  .CX 1556 786,
  .CX 1556 525,
  .CX 1556 524,
  .CX 1554 1552,
  .CX 1554 786,
  .CX 1558 1554,
  .CX 1554 1558,
  .CX 1558 1554,
  .CX 1553 1552,
  .CX 1553 786,
  .CX 1553 529,
  .CX 530 1553,
  .CX 1553 530,
  .CX 530 1553,
  .CX 1552 530,
  .CX 1552 1557,
  .CX 1552 1554,
  .CX 1552 1551,
  .CX 1552 791,
  .CX 1552 790,
  .CX 1552 788,
  .CX 1552 787,
  .CX 1552 529,
  .CX 1552 528,
  .CX 1553 1552,
  .CX 1552 1553,
  .CX 1553 1552,
  .CX 1551 790,
  .CX 1551 787,
  .CX 1551 529,
  .CX 1556 1551,
  .CX 1551 1556,
  .CX 1556 1551,
  .CX 791 530,
  .CX 791 786,
  .CX 791 529,
  .CX 1554 791,
  .CX 791 1554,
  .CX 1554 791,
  .CX 790 1558,
  .CX 790 1552,
  .CX 790 529,
  .CX 1551 790,
  .CX 790 1551,
  .CX 1551 790,
  .CX 789 1553,
  .CX 789 1552,
  .CX 789 1551,
  .CX 789 786,
  .CX 789 528,
  .CX 789 526,
  .CX 791 789,
  .CX 789 791,
  .CX 791 789,
  .CX 788 1557,
  .CX 788 787,
  .CX 788 529,
  .CX 788 528,
  .CX 788 526,
  .CX 1553 788,
  .CX 788 1553,
  .CX 1553 788,
  .CX 787 1556,
  .CX 787 1554,
  .CX 787 1553,
  .CX 787 786,
  .CX 787 526,
  .CX 786 530,
  .CX 786 1556,
  .CX 786 526,
  .CX 1553 786,
  .CX 786 1553,
  .CX 1553 786,
  .CX 529 530,
  .CX 529 1556,
  .CX 529 1553,
  .CX 529 526,
  .CX 786 529,
  .CX 529 786,
  .CX 786 529,
  .CX 528 1558,
  .CX 528 1557,
  .CX 528 1554,
  .CX 528 1553,
  .CX 528 787,
  .CX 528 529,
  .CX 527 1553,
  .CX 527 1552,
  .CX 527 1551,
  .CX 527 791,
  .CX 527 789,
  .CX 528 527,
  .CX 527 528,
  .CX 528 527,
  .CX 526 530,
  .CX 526 1556,
  .CX 526 1553,
  .CX 526 786,
  .CX 529 526,
  .CX 526 529,
  .CX 529 526,
  .CX 525 530,
  .CX 525 1558,
  .CX 525 1556,
  .CX 525 527,
  .CX 525 526,
  .CX 524 1553,
  .CX 524 1552,
  .CX 524 1551,
  .CX 524 786,
  .CX 524 529,
  .CX 524 527,
  .CX 524 526,
  .CX 524 525,
  .CX 523 530,
  .CX 523 791,
  .CX 523 529,
  .CX 523 527,
  .CX 523 524,
  .CX 522 1557,
  .CX 522 1553,
  .CX 522 789,
  .CX 522 528,
  .CX 522 523,
  .measureX 530 [] [.Z 528, .Z 529, .Z 788, .Z 790, .Z 1554, .Z 1556, .Z 1557, .CZ 522 524, .CZ 522 526, .CZ 522 529, .CZ 522 1552, .CZ 522 1553, .CZ 522 1554, .CZ 522 1556, .CZ 522 1558, .CZ 523 525, .CZ 523 526, .CZ 523 786, .CZ 523 1553, .CZ 523 1554, .CZ 523 1556, .CZ 523 1558, .CZ 524 525, .CZ 524 526, .CZ 524 527, .CZ 524 791, .CZ 524 1551, .CZ 524 1558, .CZ 525 526, .CZ 525 529, .CZ 525 786, .CZ 525 788, .CZ 525 789, .CZ 525 791, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 525 1556, .CZ 526 527, .CZ 526 789, .CZ 526 1551, .CZ 526 1556, .CZ 526 1557, .CZ 526 1558, .CZ 527 529, .CZ 527 786, .CZ 527 787, .CZ 527 1552, .CZ 527 1558, .CZ 528 787, .CZ 529 1551, .CZ 786 1557, .CZ 790 1558],
  .X 1558,
  .measureX 1558 [] [.Z 522, .Z 523, .Z 524, .Z 525, .Z 526, .Z 527, .Z 528, .Z 787, .Z 788, .Z 789, .Z 1554, .Z 1557, .CZ 522 791, .CZ 522 1551, .CZ 522 1552, .CZ 523 525, .CZ 523 786, .CZ 523 1551, .CZ 523 1552, .CZ 524 787, .CZ 524 788, .CZ 524 791, .CZ 524 1551, .CZ 524 1552, .CZ 524 1554, .CZ 524 1557, .CZ 525 527, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 525 790, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 525 1554, .CZ 525 1557, .CZ 526 527, .CZ 526 787, .CZ 526 791, .CZ 526 1551, .CZ 526 1552, .CZ 526 1557, .CZ 527 529, .CZ 527 789, .CZ 527 791, .CZ 527 1551, .CZ 527 1552, .CZ 528 786, .CZ 529 787, .CZ 529 788, .CZ 529 1554, .CZ 786 787, .CZ 786 788, .CZ 786 791, .CZ 786 1551, .CZ 786 1552, .CZ 786 1553, .CZ 786 1554, .CZ 787 1551, .CZ 787 1552],
  .measureX 1557 [] [.CZ 522 525, .CZ 522 526, .CZ 522 791, .CZ 522 1552, .CZ 522 1553, .CZ 522 1556, .CZ 523 527, .CZ 523 786, .CZ 523 787, .CZ 523 1553, .CZ 523 1556, .CZ 524 527, .CZ 527 790],
  .measureX 1556 [] [.CZ 522 526, .CZ 522 529, .CZ 522 790, .CZ 522 1552, .CZ 522 1553, .CZ 522 1554, .CZ 523 524, .CZ 523 525, .CZ 523 526, .CZ 523 527, .CZ 523 786, .CZ 523 1553, .CZ 523 1554, .CZ 524 786, .CZ 524 787, .CZ 524 788, .CZ 524 789, .CZ 524 791, .CZ 524 1551, .CZ 524 1552, .CZ 524 1554, .CZ 525 526, .CZ 525 527, .CZ 525 529, .CZ 525 786, .CZ 525 787, .CZ 525 788, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 525 1554, .CZ 526 527, .CZ 526 786, .CZ 526 789, .CZ 526 791, .CZ 526 1551, .CZ 526 1552, .CZ 526 1554, .CZ 527 787, .CZ 527 789, .CZ 527 791, .CZ 527 1551, .CZ 527 1552, .CZ 528 529, .CZ 528 786, .CZ 528 787, .CZ 529 787, .CZ 529 788, .CZ 529 1554, .CZ 786 787, .CZ 786 788, .CZ 786 1551, .CZ 786 1552, .CZ 786 1553, .CZ 786 1554, .CZ 787 791, .CZ 787 1552, .CZ 1551 1554],
  .measureX 1554 [] [.CZ 522 526, .CZ 522 529, .CZ 522 786, .CZ 522 787, .CZ 522 790, .CZ 522 1551, .CZ 522 1553, .CZ 523 524, .CZ 523 525, .CZ 523 527, .CZ 523 1551, .CZ 523 1553, .CZ 524 525, .CZ 524 527, .CZ 524 786, .CZ 524 788, .CZ 524 791, .CZ 524 1551, .CZ 524 1552, .CZ 525 527, .CZ 525 529, .CZ 525 789, .CZ 525 790, .CZ 525 791, .CZ 525 1551, .CZ 525 1552, .CZ 525 1553, .CZ 526 527, .CZ 526 787, .CZ 526 789, .CZ 526 1551, .CZ 526 1552, .CZ 527 787, .CZ 527 789, .CZ 527 791, .CZ 527 1552, .CZ 528 787, .CZ 529 791, .CZ 786 791, .CZ 786 1551, .CZ 786 1552, .CZ 786 1553, .CZ 787 1551, .CZ 787 1552, .CZ 788 1551],
  .measureX 1553 [] [.CZ 522 529, .CZ 522 786, .CZ 522 790, .CZ 522 791, .CZ 523 524, .CZ 523 527, .CZ 523 786, .CZ 523 1552, .CZ 524 525, .CZ 525 527, .CZ 525 790, .CZ 525 791, .CZ 525 1551, .CZ 525 1552, .CZ 527 1551, .CZ 527 1552, .CZ 529 791, .CZ 791 1551, .CZ 791 1552],
  .measureX 1552 [] [.CZ 523 525, .CZ 523 526, .CZ 523 786, .CZ 523 787, .CZ 524 527, .CZ 524 788, .CZ 524 791, .CZ 525 790, .CZ 529 791, .CZ 786 790],
  .measureX 1551 [] [.CZ 523 526, .CZ 523 787, .CZ 524 529],
  .measureX 791 [] [.CZ 523 525, .CZ 523 527, .CZ 523 786, .CZ 523 788],
  .measureX 790 [] [.CZ 523 524, .CZ 523 529],
  .X 791,
  .CX 791 790,
  .CX 790 791,
  .CX 791 790,
  .CX 791 789,
  .CX 789 791,
  .CX 791 789,
  .CX 790 788,
  .CX 788 790,
  .CX 790 788,
  .CX 789 787,
  .CX 787 789,
  .CX 789 787,
  .CX 788 786,
  .CX 786 788,
  .CX 788 786,
  .CX 787 529,
  .CX 529 787,
  .CX 787 529,
  .CX 523 786
]

def safe15 : Program → Nat → Bool
  | [], _ => true
  | (.measureX t c0 c1)::rest, b =>
    let b' := flipN_t8 b t (b.testBit t)
    c0.isEmpty && (corrP_t8 c1 false b' == b.testBit t) && safe15 rest b'
  | i::rest, b => safe15 rest (runN_t8 [i] [] (false,b)).2

def check15 (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    let pre := MorningFour.pre507 g s uv.1 uv.2
    let e := encN_t8 pre sites15
    let b := (runN_t8 (MorningFour.tick507 ++ tripF) [] (false,e)).2
    safe15 candidate15 b && ((runN_t8 candidate15 [] (false,b)).2 == e)

theorem candidate_case_0 : check15 (0, 1) = true := by decide +kernel
theorem candidate_case_1 : check15 (1, 1) = true := by decide +kernel
theorem candidate_case_2 : check15 (2, 1) = true := by decide +kernel
theorem candidate_case_3 : check15 (3, 1) = true := by decide +kernel
theorem candidate_case_4 : check15 (4, 1) = true := by decide +kernel
theorem candidate_case_5 : check15 (5, 1) = true := by decide +kernel
theorem candidate_case_6 : check15 (6, 1) = true := by decide +kernel
theorem candidate_case_7 : check15 (7, 1) = true := by decide +kernel
theorem candidate_case_8 : check15 (8, 1) = true := by decide +kernel
theorem candidate_case_9 : check15 (9, 1) = true := by decide +kernel
theorem candidate_case_10 : check15 (10, 1) = true := by decide +kernel
theorem candidate_case_11 : check15 (11, 1) = true := by decide +kernel
theorem candidate_case_12 : check15 (12, 1) = true := by decide +kernel
theorem candidate_case_13 : check15 (13, 1) = true := by decide +kernel
theorem candidate_case_14 : check15 (14, 1) = true := by decide +kernel
theorem candidate_case_15 : check15 (15, 1) = true := by decide +kernel
theorem candidate_case_16 : check15 (1, 3) = true := by decide +kernel
theorem candidate_case_17 : check15 (2, 3) = true := by decide +kernel
theorem candidate_case_18 : check15 (4, 3) = true := by decide +kernel
theorem candidate_case_19 : check15 (5, 3) = true := by decide +kernel
theorem candidate_case_20 : check15 (7, 3) = true := by decide +kernel
theorem candidate_case_21 : check15 (10, 3) = true := by decide +kernel
theorem candidate_case_22 : check15 (13, 3) = true := by decide +kernel
theorem candidate_case_23 : check15 (1, 5) = true := by decide +kernel
theorem candidate_case_24 : check15 (2, 5) = true := by decide +kernel
theorem candidate_case_25 : check15 (3, 5) = true := by decide +kernel
theorem candidate_case_26 : check15 (6, 5) = true := by decide +kernel
theorem candidate_case_27 : check15 (7, 5) = true := by decide +kernel
theorem candidate_case_28 : check15 (11, 5) = true := by decide +kernel
theorem candidate_case_29 : check15 (1, 7) = true := by decide +kernel
theorem candidate_case_30 : check15 (2, 7) = true := by decide +kernel
theorem candidate_case_31 : check15 (3, 7) = true := by decide +kernel
theorem candidate_case_32 : check15 (5, 7) = true := by decide +kernel
theorem candidate_case_33 : check15 (9, 7) = true := by decide +kernel
theorem candidate_case_34 : check15 (1, 9) = true := by decide +kernel
theorem candidate_case_35 : check15 (7, 9) = true := by decide +kernel
theorem candidate_case_36 : check15 (1, 11) = true := by decide +kernel
theorem candidate_case_37 : check15 (5, 11) = true := by decide +kernel
theorem candidate_case_38 : check15 (1, 13) = true := by decide +kernel
theorem candidate_case_39 : check15 (3, 13) = true := by decide +kernel
theorem candidate_case_40 : check15 (1, 15) = true := by decide +kernel
theorem check15_all : MorningFour.pairs.all check15 = true := by
  simp only [MorningFour.pairs, List.all_cons, List.all_nil, Bool.and_true, candidate_case_0, candidate_case_1, candidate_case_2, candidate_case_3, candidate_case_4, candidate_case_5, candidate_case_6, candidate_case_7, candidate_case_8, candidate_case_9, candidate_case_10, candidate_case_11, candidate_case_12, candidate_case_13, candidate_case_14, candidate_case_15, candidate_case_16, candidate_case_17, candidate_case_18, candidate_case_19, candidate_case_20, candidate_case_21, candidate_case_22, candidate_case_23, candidate_case_24, candidate_case_25, candidate_case_26, candidate_case_27, candidate_case_28, candidate_case_29, candidate_case_30, candidate_case_31, candidate_case_32, candidate_case_33, candidate_case_34, candidate_case_35, candidate_case_36, candidate_case_37, candidate_case_38, candidate_case_39, candidate_case_40]

theorem corr_add (cs : List Correction) (ph : Bool) (b : Nat) :
    corrP_t8 cs ph b = (ph ^^ corrP_t8 cs false b) := by
  induction cs generalizing ph with
  | nil => cases ph <;> rfl
  | cons c cs ih =>
    cases c with
    | Z t => cases ph <;> cases hb : b.testBit t <;> simp only [corrP_t8, hb, Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false] <;> (first | rfl | (rw [ih true]; cases corrP_t8 cs false b <;> rfl))
    | CZ x y => cases ph <;> cases hx : b.testBit x <;> cases hy : b.testBit y <;> simp only [corrP_t8, hx, hy, Bool.false_and, Bool.true_and, Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false] <;> (first | rfl | (rw [ih true]; cases corrP_t8 cs false b <;> rfl))

theorem safe_sound (P : Program) (b : Nat) (h : safe15 P b = true) (m : List Bool) (ph : Bool) :
  runN_t8 P m (ph,b) = (ph, (runN_t8 P [] (false,b)).2) := by
  induction P generalizing b m ph with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | X t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | CX c t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | CCX a b' t => simp only [safe15,runN_t8,Prod.snd] at h ⊢; exact ih _ h _ _
    | measureX t c0 c1 =>
      simp only [safe15,Bool.and_eq_true,beq_iff_eq] at h
      obtain ⟨⟨hc0,hc1⟩,hr⟩ := h
      have hz : c0 = [] := by simpa using hc0
      subst c0
      cases m with
      | nil => simpa [runN_t8, corrP_t8] using ih _ hr [] ph
      | cons z zs =>
        cases z with
        | false => simpa [runN_t8, corrP_t8] using ih _ hr zs ph
        | true =>
          have eq : corrP_t8 c1 (ph ^^ b.testBit t) (flipN_t8 b t (b.testBit t)) = ph := by
            rw [corr_add, hc1]
            cases ph <;> cases b.testBit t <;> rfl
          simpa [runN_t8, corrP_t8, eq] using ih _ hr zs ph


theorem candidate_sample (g s : Bool) (uv : Nat × Nat) (h : uv ∈ MorningFour.pairs)
    (m : List Bool) (ph : Bool) :
    let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15
    let b := (runN_t8 (MorningFour.tick507 ++ tripF) [] (false,e)).2
    runN_t8 candidate15 m (ph,b) = (ph,e) := by
  have t := check15_all
  simp only [List.all_eq_true] at t
  have row := t uv h
  simp only [check15,List.all_eq_true] at row
  have z := row g (by cases g <;> simp) s (by cases s <;> simp)
  simp only [Bool.and_eq_true, beq_iff_eq] at z
  exact (safe_sound candidate15 _ z.1 m ph).trans (by rw [z.2])

def old15 : Program := tickMR8 ++ W.ReverseCarry.compactReceiverTick base 507

def oldCheck15 (uv : Nat × Nat) : Bool :=
  [false,true].all fun g => [false,true].all fun s =>
    let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15
    let b := (runN_t8 (MorningFour.tick507 ++ tripF) [] (false,e)).2
    phaseClean508 old15 b == some e

theorem old_case_0 : oldCheck15 (0, 1) = true := by decide +kernel
theorem old_case_1 : oldCheck15 (1, 1) = true := by decide +kernel
theorem old_case_2 : oldCheck15 (2, 1) = true := by decide +kernel
theorem old_case_3 : oldCheck15 (3, 1) = true := by decide +kernel
theorem old_case_4 : oldCheck15 (4, 1) = true := by decide +kernel
theorem old_case_5 : oldCheck15 (5, 1) = true := by decide +kernel
theorem old_case_6 : oldCheck15 (6, 1) = true := by decide +kernel
theorem old_case_7 : oldCheck15 (7, 1) = true := by decide +kernel
theorem old_case_8 : oldCheck15 (8, 1) = true := by decide +kernel
theorem old_case_9 : oldCheck15 (9, 1) = true := by decide +kernel
theorem old_case_10 : oldCheck15 (10, 1) = true := by decide +kernel
theorem old_case_11 : oldCheck15 (11, 1) = true := by decide +kernel
theorem old_case_12 : oldCheck15 (12, 1) = true := by decide +kernel
theorem old_case_13 : oldCheck15 (13, 1) = true := by decide +kernel
theorem old_case_14 : oldCheck15 (14, 1) = true := by decide +kernel
theorem old_case_15 : oldCheck15 (15, 1) = true := by decide +kernel
theorem old_case_16 : oldCheck15 (1, 3) = true := by decide +kernel
theorem old_case_17 : oldCheck15 (2, 3) = true := by decide +kernel
theorem old_case_18 : oldCheck15 (4, 3) = true := by decide +kernel
theorem old_case_19 : oldCheck15 (5, 3) = true := by decide +kernel
theorem old_case_20 : oldCheck15 (7, 3) = true := by decide +kernel
theorem old_case_21 : oldCheck15 (10, 3) = true := by decide +kernel
theorem old_case_22 : oldCheck15 (13, 3) = true := by decide +kernel
theorem old_case_23 : oldCheck15 (1, 5) = true := by decide +kernel
theorem old_case_24 : oldCheck15 (2, 5) = true := by decide +kernel
theorem old_case_25 : oldCheck15 (3, 5) = true := by decide +kernel
theorem old_case_26 : oldCheck15 (6, 5) = true := by decide +kernel
theorem old_case_27 : oldCheck15 (7, 5) = true := by decide +kernel
theorem old_case_28 : oldCheck15 (11, 5) = true := by decide +kernel
theorem old_case_29 : oldCheck15 (1, 7) = true := by decide +kernel
theorem old_case_30 : oldCheck15 (2, 7) = true := by decide +kernel
theorem old_case_31 : oldCheck15 (3, 7) = true := by decide +kernel
theorem old_case_32 : oldCheck15 (5, 7) = true := by decide +kernel
theorem old_case_33 : oldCheck15 (9, 7) = true := by decide +kernel
theorem old_case_34 : oldCheck15 (1, 9) = true := by decide +kernel
theorem old_case_35 : oldCheck15 (7, 9) = true := by decide +kernel
theorem old_case_36 : oldCheck15 (1, 11) = true := by decide +kernel
theorem old_case_37 : oldCheck15 (5, 11) = true := by decide +kernel
theorem old_case_38 : oldCheck15 (1, 13) = true := by decide +kernel
theorem old_case_39 : oldCheck15 (3, 13) = true := by decide +kernel
theorem old_case_40 : oldCheck15 (1, 15) = true := by decide +kernel
theorem old_all15 : MorningFour.pairs.all oldCheck15 = true := by
  simp only [MorningFour.pairs, List.all_cons, List.all_nil, Bool.and_true, old_case_0, old_case_1, old_case_2, old_case_3, old_case_4, old_case_5, old_case_6, old_case_7, old_case_8, old_case_9, old_case_10, old_case_11, old_case_12, old_case_13, old_case_14, old_case_15, old_case_16, old_case_17, old_case_18, old_case_19, old_case_20, old_case_21, old_case_22, old_case_23, old_case_24, old_case_25, old_case_26, old_case_27, old_case_28, old_case_29, old_case_30, old_case_31, old_case_32, old_case_33, old_case_34, old_case_35, old_case_36, old_case_37, old_case_38, old_case_39, old_case_40]

theorem candidate_support15 : wires candidate15 ⊆ sites15.toFinset := by decide +kernel
theorem old_support15 : wires old15 ⊆ sites15.toFinset := by decide +kernel

theorem old_sample15 (g s : Bool) (uv : Nat × Nat) (h : uv ∈ MorningFour.pairs) (m : List Bool) :
    let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15
    let b := (runN_t8 (MorningFour.tick507 ++ tripF) [] (false,e)).2
    runN_t8 old15 m (false,b) = (false,e) := by
  have t := old_all15
  simp only [List.all_eq_true] at t
  have row := t uv h
  simp only [oldCheck15,List.all_eq_true] at row
  have z := row g (by cases g <;> simp) s (by cases s <;> simp)
  simp only [beq_iff_eq] at z
  exact phaseClean508_sound old15 _ _ z m

theorem replace_sample15 (g s : Bool) (uv : Nat × Nat) (h : uv ∈ MorningFour.pairs)
    (state : State) (m n : List Bool)
    (agree : ∀ q ∈ sites15,
      state.basis q = tbN_t8 ((runN_t8 (MorningFour.tick507 ++ tripF) []
        (false,encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15)).2) q) :
    run candidate15 m state = run old15 n state := by
  apply Stack5.local_replace candidate15 old15 sites15.toFinset
    candidate_support15 old_support15 state
      ⟨false,tbN_t8 ((runN_t8 (MorningFour.tick507 ++ tripF) []
        (false,encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15)).2)⟩ m n
  · intro q hq
    exact agree q (List.mem_toFinset.mp hq)
  · rw [run_sim_t8,run_sim_t8,candidate_sample g s uv h m false, old_sample15 g s uv h n]

theorem resources : toffoliCount candidate15 = 15 ∧ measurementCount candidate15 = 11 ∧ Challenge.gateSlots candidate15 = 714 := by decide +kernel
theorem physical : GatePhysical candidate15 := by
  simp (config := {maxSteps := 4000000}) [candidate15, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]
open ECDSAAdd.Secp256k1 ECDSAAdd.Entrant.Rolling1588.Integer ECDSAAdd.Entrant.History5 ECDSAAdd.Entrant.OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.Integer.forward Rolling1588.Integer.regularForward
theorem forward_support : wires (MorningFour.tick507 ++ tripF) ⊆ sites15.toFinset := by decide +kernel

theorem local_stage15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a state : State) (stage : Stage base isA x p 507 a.basis) (m n : List Bool)
    (agree : ∀ q ∈ sites15,
      state.basis q = (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run candidate15 m state = run old15 n state := by
  obtain ⟨raw,hraw,hbits⟩ := stage
  obtain ⟨g,s,uv,mem,reads⟩ := MorningFour.raw507 x hx0 hx raw hraw
  have fields := (W.compactSkywalkStage_fields_iff base _ 507 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨_,_,_,_,_,_,_,cleanA,_⟩ := fields
  have free530 : raw.basis 530 = false := cleanA _ (by decide +kernel)
  have used530 : 530 ∈ (W.compactSkywalkTickLayout base 511).wires.toFinset := by decide +kernel
  have kept530 : (run (Rolling1588.Integer.encodePrefix base isA 507) [] raw).basis 530 = raw.basis 530 := by
    apply run_preserves_outside
    intro used
    exact Finset.disjoint_left.mp
      (prefix_disjoint_layout base isA base_pool_nodup 507 511 (by omega) (by omega)) used used530
  have pre : ∀ q ∈ sites15, a.basis q = MorningFour.pre507 g s uv.1 uv.2 q := by
    intro q hq
    have hq' : q ∈ MorningFour.sites ∨ q = 530 := by simpa [sites15] using hq
    rcases hq' with hq | rfl
    · rw [hbits, ←reads q hq]
      apply run_preserves_outside
      rcases MorningPlacement.layouts q hq with h|h|h|h
      all_goals
        exact fun hh => Finset.disjoint_left.mp
          (prefix_disjoint_layout base isA base_pool_nodup 507 _ (by omega) (by omega)) hh h
    · rw [hbits,kept530,free530]
      rfl
  apply replace_sample15 g s uv mem state m n
  intro q hq
  rw [agree q hq]
  rw [site_run (MorningFour.tick507 ++ tripF) sites15 forward_support a
    ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩ pre [] q hq]
  have support : ∀ q, MorningFour.pre507 g s uv.1 uv.2 q = true → q ∈ sites15 := by
    intro q hq
    have old : q ∈ MorningFour.sites := by
      by_contra hn
      have z := MorningFour.pre_supp g s uv.1 uv.2 q hn
      rw [z] at hq
      exact Bool.noConfusion hq
    change q ∈ MorningFour.sites ++ [530]
    exact List.mem_append.mpr (Or.inl old)
  let e := encN_t8 (MorningFour.pre507 g s uv.1 uv.2) sites15
  have encoded : MorningFour.pre507 g s uv.1 uv.2 = tbN_t8 e := tb_enc_t8 _ _ support
  calc
    (run (MorningFour.tick507 ++ tripF) [] ⟨false,MorningFour.pre507 g s uv.1 uv.2⟩).basis q =
        (run (MorningFour.tick507 ++ tripF) [] ⟨false,tbN_t8 e⟩).basis q := by rw [←encoded]
    _ = _ := congrArg (fun t : State => t.basis q) (run_sim_t8 _ [] false e)


theorem codec_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a t : State) (stage : Stage base isA x p 507 a.basis) (codec : Program) (m : List Bool)
    (agree : ∀ q ∈ sites15,
      (run codec (m.take (measurementCount codec)) t).basis q =
        (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run (codec ++ candidate15) m t = run (codec ++ old15) m t := by
  rw [run_append,run_append]
  exact local_stage15 isA x hx0 hx a _ stage _ _ agree

theorem placed_codec_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a t : State) (stage : Stage base isA x p 507 a.basis) (codec : Program) (m : List Bool)
    (agree : ∀ q ∈ sites15,
      (run codec (m.take (measurementCount codec)) t).basis q =
        (run (MorningFour.tick507 ++ tripF) [] a).basis q) :
    run (renameProgram (sig 510) (codec ++ candidate15)) m (pullState (sig 510) t) =
    run (renameProgram (sig 510) (codec ++ old15)) m (pullState (sig 510) t) := by
  rw [OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
    codec_replace15 isA x hx0 hx a t stage codec m agree]
theorem same50715 : renameProgram (sig 507) (W.ReverseCarry.compactReceiverTick base 507) =
    renameProgram (sig 510) (W.ReverseCarry.compactReceiverTick base 507) := by decide +kernel

theorem unpack50715 (isA : Bool) : unpackFirst base isA 507 = [] := by
  simp only [unpackFirst,show ¬(507:Nat)=5 from by decide,if_false,Rolling1588.Integer.decodeBefore,
    show History5.packDue 507=false from by decide,Bool.false_eq_true,if_false]

theorem reverse_shape15 (isA : Bool) :
    Rolling1588.stackReverse isA = renameProgram (sig 511) tickR ++
      (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) := by
  have shape := reverse_snoc isA 1 506
  rw [show (1:Nat)+506=507 by rfl,unpack50715,List.nil_append,
    reverse_eq_packets,same50715] at shape
  rw [reverse_eq_packets] at shape
  rw [Rolling1588.stackReverse,shape]
  simp only [old15,renameProgram,List.map_append,List.append_assoc]

theorem pack_inverse15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) =
        run (MorningFour.tick507 ++ tripF) [] a := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let b8 := run (W.repairedTick base 507) [] a
  let b9 := run (W.repairedTick base 508) [] b8
  let b10 := run (W.repairedTick base 509) [] b9
  let b11 := run (W.repairedTick base 510) [] b10
  have s8 : Stage base isA x p 508 b8.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 507 hp0 hx0 hpo hp gap hx cop (by omega) a [] stage).2
    simpa only [MorningPlacement.pack507,List.append_nil,b8] using h
  have s9 : Stage base isA x p 509 b9.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 508 hp0 hx0 hpo hp gap hx cop (by omega) b8 [] s8).2
    simpa only [pack508,List.append_nil,b9] using h
  have s10 : Stage base isA x p 510 b10.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 509 hp0 hx0 hpo hp gap hx cop (by omega) b9 [] s9).2
    simpa only [pack509,List.append_nil,b10] using h
  have rep : W.repairedTick base 510=W.compactSkywalkTick base 510 := by
    rw [tick510ExF_explicit,tick510ExF_compact]
  have legal := tick_pack_legal base isA base_pool_nodup x p 510 hp0 hx0 hpo hp gap hx cop
    (by omega) b10 [] s10 (by decide)
  rw [←rep] at legal
  have dp : run (Rolling1588.Integer.decodeBefore base isA 510) mD
      (run (packAfter base isA 510) mE b11)=b11 := by
    simpa only [Rolling1588.Integer.packAfter,Rolling1588.Integer.decodeBefore,show History5.packDue 510=true from by decide,if_true,b11] using
      encode_decode_roundtrip base isA base_pool_nodup (510-5) (by omega) b11 mE mD legal
  have eq : run (MorningFour.tick507 ++ tripF) [] a = b11 := by
    simp only [tripF,←MorningFour.explicit507,←tick508ExF_explicit,←tick509ExF_explicit,
      ←tick510ExF_explicit,List.append_assoc,run_append,List.take_nil,List.drop_nil,b8,b9,b10,b11]
  rw [eq,dp]

theorem decoded_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ candidate15) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) =
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ old15) mD
      (run (packAfter base isA 510) mE (run (MorningFour.tick507 ++ tripF) [] a)) := by
  rw [run_append (Rolling1588.Integer.decodeBefore base isA 510) candidate15,
    run_append (Rolling1588.Integer.decodeBefore base isA 510) old15,
    pack_inverse15 isA x hx0 hx a stage mE]
  exact local_stage15 isA x hx0 hx a _ stage _ _ (fun _ _ => rfl)

theorem sites_pool15 : sites15.toFinset ⊆ (skywalkPoolWires base).toFinset := by
  have layout : sites15 = ([506,507,508,509,510,511,512,513,770,771,772,773,774,775,1535,1536,1537,1538,1540,1541,1542,1543,514] : List Nat).map base := by decide +kernel
  intro q hq
  have member : q ∈ sites15 := List.mem_toFinset.mp hq
  rw [layout] at member
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
  apply List.mem_toFinset.mpr
  apply OB5.base_pool i
  have bound : ∀ i ∈ ([506,507,508,509,510,511,512,513,770,771,772,773,774,775,1535,1536,1537,1538,1540,1541,1542,1543,514] : List Nat), i < 1798 := by decide
  exact bound i hi

theorem decoded_replace_pool15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ candidate15) mD u =
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ old15) mD u := by
  let f := MorningFour.tick507 ++ tripF
  let codec := Rolling1588.Integer.decodeBefore base isA 510
  let ref := run (packAfter base isA 510) mE (run f [] a)
  have dec : wires codec ⊆ (skywalkPoolWires base).toFinset := by
    have d := (History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←decodeBefore_support_eq base isA 510] at d
    exact d
  have supportC : wires (codec ++ candidate15) ⊆ (skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,candidate_support15.trans sites_pool15⟩
  have supportO : wires (codec ++ old15) ⊆ (skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,old_support15.trans sites_pool15⟩
  apply Stack5.local_replace _ _ _ supportC supportO u ref mD mD
  · intro q hq
    have eq1 := congrFun (run_basis_records (f ++ packAfter base isA 510) a a mE [] rfl) q
    have eq2 := congrFun (run_basis_records (packAfter base isA 510) (run f [] a) (run f [] a) [] mE rfl) q
    have eq3 : (run (f ++ packAfter base isA 510) [] a).basis q =
        (run (packAfter base isA 510) [] (run f [] a)).basis q := by
      rw [run_append]; simp only [List.take_nil,List.drop_nil]
    exact (agree q (List.mem_toFinset.mp hq)).trans (eq1.trans (eq3.trans eq2))
  · exact decoded_replace15 isA x hx0 hx a stage mE mD

def reverseTail15 (isA : Bool) : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15) ++
    Rolling1588.reverse isA 1 506

theorem unpack51015 (isA : Bool) :
    Rolling1588.unpackAtTick isA 510 = Rolling1588.Integer.decodeBefore base isA 510 := by
  have h := unpackFirst_base isA 510
  simpa only [unpackFirst,show ¬(510:Nat)=5 from by decide,if_false] using h.symm

theorem old_records15 : measurementCount old15 = 11 := by decide +kernel

theorem placed_block15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15)) mD
      (pullState (sig 510) u) =
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15)) mD
      (pullState (sig 510) u) := by
  rw [unpack51015, OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
    decoded_replace_pool15 isA x hx0 hx a u stage mE mD agree]

theorem tail_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 507 a.basis) (mE mD : List Bool)
    (agree : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) mE a).basis q) :
    run (reverseTail15 isA) mD (pullState (sig 510) u) =
      run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) mD (pullState (sig 510) u) := by
  have count : measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15)) =
      measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,
      measurementCount_append,measurementCount_append,resources.2.1,old_records15]
  rw [reverseTail15,run_append,run_append, count,
    placed_block15 isA x hx0 hx a u stage mE _ agree]


theorem tail_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (u : State) (hu : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run (regularForward base isA 1 510) mE s1).basis q) (mD : List Bool) :
    run (reverseTail15 isA) mD (pullState (sig 510) u) =
      run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old15) ++
        Rolling1588.reverse isA 1 506) mD (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  let k := measurementCount (regularForward base isA 1 506)
  have stage0 : Stage base isA x p 507
      (run (regularForward base isA 1 506)
        (mE.take (measurementCount (regularForward base isA 1 506))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 506
      hp0 hx0 hpo hp gap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  change Stage base isA x p 507 (run (regularForward base isA 1 506) (mE.take k) s1).basis at stage0
  obtain ⟨a,ha⟩ : ∃ a : State,run (regularForward base isA 1 506) (mE.take k) s1 = a := ⟨_,rfl⟩
  rw [ha] at stage0
  have fwdP : regularForward base isA 1 510 = regularForward base isA 1 506 ++
      ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) := by
    rw [regularForward_snoc base isA 1 509,show (1:Nat)+509=510 by rfl,
      regularForward_snoc base isA 1 508,show (1:Nat)+508=509 by rfl,
      regularForward_snoc base isA 1 507,show (1:Nat)+507=508 by rfl,
      regularForward_snoc base isA 1 506,show (1:Nat)+506=507 by rfl,
      MorningPlacement.pack507,pack508,pack509,
      MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
    simp only [tripF,List.append_assoc,List.append_nil]
  have agre : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run ((MorningFour.tick507 ++ tripF) ++ packAfter base isA 510) (mE.drop k) a).basis q := by
    intro q hq
    rw [hu q hq,fwdP,run_append,←show measurementCount (regularForward base isA 1 506)=k from rfl,ha]
  exact tail_replace15 isA x hx0 hx a u stage0 (mE.drop k) mD agre

attribute [local irreducible] Stage
def stackReverse15 (isA : Bool) : Program := renameProgram (sig 511) tickR ++ reverseTail15 isA

theorem reverse_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base isA 1 511) mE s1).basis q) (mD : List Bool) :
    run (stackReverse15 isA) mD (pullState (sig 511) t5)=
      run (Rolling1588.stackReverse isA) mD (pullState (sig 511) t5) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base isA x p 511
      (run (regularForward base isA 1 510)
        (mE.take (measurementCount (regularForward base isA 1 510))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  have whole : run (regularForward base isA 1 510)
      (mE.take (measurementCount (regularForward base isA 1 510))) s1=
        run (regularForward base isA 1 510) mE s1 := run_take _ mE s1
  have last : run (regularForward base isA 1 511) mE s1=
      run (W.repairedTick base 511) (mE.drop (measurementCount (regularForward base isA 1 510)))
        (run (regularForward base isA 1 510)
          (mE.take (measurementCount (regularForward base isA 1 510))) s1) := by
    rw [regularForward_snoc base isA 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base isA 1 510)
    (mE.take (measurementCount (regularForward base isA 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits isA x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero isA x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have cn : measurementCount (renameProgram (sig 511) tickR)=0 :=
    (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
  rw [stackReverse15,reverse_shape15,run_append,run_append,cn]
  simp only [List.take_zero,List.drop_zero]
  rw [OB5.run_rename 511 (by omega),tickR_run,move]
  exact tail_actual15 isA x hx0 hx s1 mE first _
    (fun q hq => (uAgree q hq).trans (congrArg (fun st : State => st.basis q) whole)) mD

theorem stack_roundtrip15 (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackReverse15 isA) mD (run (Rolling1588TickGap.stackForward isA) mE s)=s := by
  have fwd : run (Rolling1588TickGap.stackForward isA) mE s =
      pullState (sig 511) (run (regularForward base isA 1 511) mE s) := by
    rw [Rolling1588TickGap.stackForward_run_eq isA x hx0 hx s mE first,
      ←Rolling1588.Integer.stackForward_eq_packets,Rolling1588.Integer.stackForwardT_run isA hn hlo x hx0 hx s mE first,
      Rolling1588.Integer.forward_run isA x hx0 hx s mE first]
  rw [fwd, reverse_actual15 isA x hx0 hx s mE first _ (fun _ _ => rfl) mD,←fwd]
  exact Rolling1588TickGap.stack_roundtrip isA hn hlo x hx0 hx s mE mD first

open ECDSAAdd.Arithmetic.DirectSkywalk
def lastPhase15 (isA : Bool) : Program :=
  skywalkArithmeticClear base ++ stackReverse15 isA ++ FrontierEntry1591NativeH.inverse base

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

attribute [local irreducible] Rolling1588.stackReverse Rolling1588.lastPhase stackReverse15 reverseTail15 lastPhase15 candidate15 old15
theorem cand_extra15 : wires (renameProgram (sig 510) candidate15) ⊆
    wires (renameProgram (sig 510) old15) ∪ {530} := by
  have parts : MorningFour.sites.toFinset ⊆ wires old15 ∪ {1559} := by decide +kernel
  have absent : (1559:Wire) ∉ wires candidate15 := by decide +kernel
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  have member : v ∈ sites15 := List.mem_toFinset.mp (candidate_support15 hv)
  have cases : v ∈ MorningFour.sites ∨ v=530 := by simpa [sites15] using member
  rcases cases with oldsite | extra
  · have member := parts (List.mem_toFinset.mpr oldsite)
    rcases Finset.mem_union.mp member with old | extra
    · apply Finset.mem_union_left
      rw [renameProgram_support]
      exact Finset.mem_image.mpr ⟨v,old,rfl⟩
    · simp only [Finset.mem_singleton] at extra
      exact False.elim (absent (extra ▸ hv))
  · subst v
    apply Finset.mem_union_right
    simp only [Finset.mem_singleton]
    decide +kernel

theorem last_extra15 (isA : Bool) : wires (lastPhase15 isA) ⊆
    wires (Rolling1588.lastPhase isA) ∪ {530} := by
  have ren (p q : Program) : renameProgram (sig 510) (p ++ q) =
      renameProgram (sig 510) p ++ renameProgram (sig 510) q := by simp only [renameProgram,List.map_append]
  have hsub := cand_extra15
  intro q h
  simp only [lastPhase15,stackReverse15,reverseTail15,ren,wires_append,
    Finset.mem_union] at h
  rw [Rolling1588.lastPhase,reverse_shape15]
  simp only [ren,wires_append,Finset.mem_union,Finset.mem_singleton] at h ⊢
  have hh : q ∈ wires (renameProgram (sig 510) candidate15) →
      q ∈ wires (renameProgram (sig 510) old15) ∨ q=530 := by
    intro hc
    have z := hsub hc
    simpa only [Finset.mem_union,Finset.mem_singleton] using z
  rcases h with ((hc | ht | (hcodec | hcand) | hrest) | hinv)
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr (Or.inl ht)))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl hcodec)))))
  · rcases hh hcand with hold | hextra
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr hold)))))
    · exact Or.inr hextra
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr hrest))))
  · exact Or.inl (Or.inr hinv)

theorem extra_pool15 : 530 ∈ (skywalkPoolWires base).toFinset := by
  have h := OB5.base_pool 514 (by decide)
  exact List.mem_toFinset.mpr (by simpa only [show base 514 = 530 from by decide +kernel] using h)

theorem last_pool15 (isA : Bool) : wires (lastPhase15 isA) ⊆ (skywalkPoolWires base).toFinset := by
  intro q h
  rcases Finset.mem_union.mp (last_extra15 isA h) with old | extra
  · exact ((Rolling1588Lifetime.last_support_sub isA).trans FrontierEntry1591Kernel.last_pool) old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_pool15

theorem last_hosts_free15 (isA : Bool) (q : Wire) (hq : q ∈ Rolling1588Lifetime.phaseHosts) :
    q ∉ wires (lastPhase15 isA) := by
  intro h
  rcases Finset.mem_union.mp (last_extra15 isA h) with old | extra
  · exact Rolling1588Lifetime.last_hosts_free isA q hq old
  · simp only [Finset.mem_singleton] at extra
    subst q
    have no : (530:Wire) ∉ Rolling1588Lifetime.phaseHosts := by decide +kernel
    exact no hq

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

theorem last_physical15 (isA : Bool) : GatePhysical (lastPhase15 isA) := by
  have old := Rolling1588.lastPhase_physical isA
  rw [Rolling1588.lastPhase,reverse_shape15] at old
  have ren (p q : Program) : renameProgram (sig 510) (p ++ q) =
      renameProgram (sig 510) p ++ renameProgram (sig 510) q := by simp only [renameProgram,List.map_append]
  simp only [gatePhysical_append,ren] at old
  rw [lastPhase15,stackReverse15,reverseTail15,ren]
  simp only [gatePhysical_append]
  exact ⟨⟨old.1.1,old.1.2.1,⟨old.1.2.2.1.1,
    gatePhysical_rename _ (sig_injective 510 (by omega)) _ physical⟩,old.1.2.2.2⟩,old.2⟩

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

end ECDSAAdd.Entrant.InverseFour15

namespace ECDSAAdd.Entrant.InverseFour15
open ECDSAAdd.Challenge ECDSAAdd.Entrant.Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] Rolling1588.stackReverse Rolling1588.lastPhase stackReverse15 reverseTail15 lastPhase15 candidate15 old15
 theorem reverse_metrics_new (isA : Bool) :
    toffoliCount (stackReverse15 isA) + 1 = toffoliCount (Rolling1588.stackReverse isA) ∧
    measurementCount (stackReverse15 isA) = measurementCount (Rolling1588.stackReverse isA) ∧
    gateSlots (stackReverse15 isA) = gateSlots (Rolling1588.stackReverse isA) + 425 := by
  have old : toffoliCount old15 = 16 ∧ measurementCount old15 = 11 ∧ gateSlots old15 = 289 := by decide +kernel
  have fresh := resources
  rw [reverse_shape15]
  simp only [stackReverse15,reverseTail15,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots] at *
  omega
end ECDSAAdd.Entrant.InverseFour15


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
  skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true ++ x1 k

theorem x1_has530x (k : Nat) : (530:Wire) ∈ wires (x1 k) := by
  rw [x1,renameProgram_support]
  apply Finset.mem_image.mpr
  refine ⟨base 514, ?_, ?_⟩
  · simp only [ExitMerge.program,ExitMerge.fPart,wires_append,Finset.mem_union]
    left; left; left; left; left; left; left; right
    simp [wires,Instr.wires]
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
    run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true) mr
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
      run (InverseFour15.stackReverse15 true) md (run (Rolling1588.stackForward true) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s := by
    have first := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input
    rw [← Rolling1588TickGap.stackForward_run_eq true x hx0 hx _ mf first]
    exact InverseFour15.stack_roundtrip15 true hn hlo x hx0 hx _ mf md first
  simpa only [Rolling1588.firstPhase,List.append_assoc] using
    compose_half (FrontierEntry1591Native.forward base) (Rolling1588.stackForward true)
      (skywalkArithmeticClear base) (InverseFour15.stackReverse15 true) s mp mr clearM twice stack

theorem prefix_pool :
    wires (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)⊆(skywalkPoolWires base).toFinset := by
  intro q hq
  apply InverseFour15.last_pool15 true
  simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union] at hq ⊢
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
      (mr.drop (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)))
      (run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
        (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after) := by
    rw [eqOut,show lastX k=(skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)++x1 k from rfl,
      run_append]
  have agree := pool_run_agrees (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
    (skywalkPoolWires base).toFinset prefix_pool
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after beforeB r1
    (fun q hq => r3 q (num_not_pool q (List.mem_toFinset.mp hq)))
  generalize hv : run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after=v
    at eqOut2 agree
  have vB := prefix_roundtrip hn hlo x y hx0 hx s mp
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) input
  rw [hBefore] at vB
  rw [vB] at agree
  have xr := x1_run k hk x y hx s v _
    (mr.drop (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) input agree.1
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
  have old := InverseFour15.last_hosts_free15 true q hq
  simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union,not_or] at old
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

theorem lx_support (k : Nat) : wires (lastX k) ⊆ wires (Rolling1588.lastPhase true) ∪ wires (x1 k) := by
  intro q hq
  simp only [lastX,wires_append,Finset.mem_union] at hq
  rcases hq with (hc | hs) | hx
  · have h : q ∈ wires (InverseFour15.lastPhase15 true) := by
      simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union]
      exact Or.inl (Or.inl hc)
    rcases Finset.mem_union.mp (InverseFour15.last_extra15 true h) with old | extra
    · exact Finset.mem_union_left _ old
    · simp only [Finset.mem_singleton] at extra
      subst q
      exact Finset.mem_union_right _ (x1_has530x k)
  · have h : q ∈ wires (InverseFour15.lastPhase15 true) := by
      simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union]
      exact Or.inl (Or.inr hs)
    rcases Finset.mem_union.mp (InverseFour15.last_extra15 true h) with old | extra
    · exact Finset.mem_union_left _ old
    · simp only [Finset.mem_singleton] at extra
      subst q
      exact Finset.mem_union_right _ (x1_has530x k)
  · exact Finset.mem_union_right _ hx

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

theorem x1_counts (k : Nat) : toffoliCount (x1 k)=767 ∧ measurementCount (x1 k)=1027 := by
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
    toffoliCount (restXX L k)+254=toffoliCount (ReflectionE1TickGap.restX L)+769 ∧
    measurementCount (restXX L k)+508=measurementCount (ReflectionE1TickGap.restX L)+1027 ∧
    Challenge.gateSlots (restXX L k) ≤ Challenge.gateSlots (ReflectionE1TickGap.restX L)+22425 := by
  have c := x1_counts k
  have rev := InverseFour15.reverse_metrics_new true
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
  have last := InverseFour15.last_physical15 true
  simp only [InverseFour15.lastPhase15,gatePhysical_append] at last
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


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end


set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Generic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square

/-! Keep the checked E1 entries and TickGap tails. Replace only the reflected square prefix. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def squareEntry (L : ControlledPointLayout) (k : Fp) : Program :=
  R2SqEp760.program760 L++E1ReflectedPlacement.entryR L k

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  squareEntry L k++ReflectionE1TickGap.restX L++exitY L cy


theorem squareEntry_base (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m1 m2 : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) m1 s=
      run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++
        E1QubitPlacement.tickF L) m2 s := by
  let n1:=measurementCount (R2SqEp760.program760 L)
  let n2:=measurementCount (SquareCarryLoan719BF.program L)
  obtain ⟨a,ha⟩ : ∃a : State,run (R2SqEp760.program760 L) (m1.take n1) s=a := ⟨_,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : State,run (SquareCarryLoan719BF.program L) (m2.take n2) s=r := ⟨_,rfl⟩
  have fresh:=R2SqEp760.program760_boundary L hw hn X Y G origin s (m1.take n1) v
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

theorem squareEntry_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (mNew mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) mNew s=run (ReflectionE1.squareEntry L k) mOld s :=
  (squareEntry_base L hw hn k X Y G origin s mNew [] v).trans
    (ReflectionE1.squareEntry_eq L hw hn k X Y G origin s mOld [] v).symm

section CorrectStages
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  have prior:=ReflectionE1TickGap.secondStage_step L hw hn X Y k cy G origin hx
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k) (B:=ReflectionE1.squareEntry L k)
    (R:=ReflectionE1TickGap.restX L++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [ReflectionE1TickGap.secondStage,List.append_assoc] using prior

end CorrectStages

/-- The second stage with the last reverse tick and the trailing constant negation merged. -/
def secondStageX (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  squareEntry L k++ExitMergeKernel.restXX L cx.val++exitY L cy

section CorrectStagesX
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem secondStageX_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageX L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=ExitMergeKernel.fusedMultiplyX_step L hw hn
    (FrontierEntry1591Callers.exit (ExitMergeKernel.kernelX cx.val) L) cx
    (ExitMergeKernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageX,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ExitMergeKernel.restXX L cx.val++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ExitMergeKernel.exit_splitX,List.append_assoc,Z] using prior

end CorrectStagesX

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ReflectionE1TickGap.entryStage L (-cx) (-cy)++secondStageX L (ReflectionE1.correction cx) cy cx

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
  have first:=ReflectionE1TickGap.entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageX_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=ReflectionE1TickGap.entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageX_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second


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

attribute [local irreducible] squareEntry secondStage generic mid gen
  ReflectionE1.squareEntry ReflectionE1Square.program ReflectionE1Low48Square.program
  ReflectionE1TickGap.entryStage ReflectionE1TickGap.secondStage ReflectionE1TickGap.restX
  ReflectionE1TickGap.generic ReflectionE1TickGap.gen

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (P Q : Program) : Prop :=
  toffoliCount P+494=toffoliCount Q ∧ measurementCount P+333=measurementCount Q ∧
    gateSlots P≤gateSlots Q+22425

private def context (A P B : Program) : Program := A++(P++B)

private theorem context_facts2 (A P Q B B' : Program)
    (h : toffoliCount P+243=toffoliCount Q ∧ measurementCount P+85=measurementCount Q ∧
      gateSlots P≤gateSlots Q)
    (h' : toffoliCount B+251=toffoliCount B' ∧ measurementCount B+248=measurementCount B' ∧
      gateSlots B≤gateSlots B'+22425) :
    Facts (context A P B) (context A Q B') := by
  rcases h with ⟨ht,hm,hs⟩
  rcases h' with ⟨ht',hm',hs'⟩
  simp only [Facts,context,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem context_wires (A P Q B : Program) :
    wires (context A P B)⊆wires (context A Q B)∪wires P := by
  intro q hq
  simp only [context,wires_append,Finset.mem_union] at hq ⊢
  tauto

private def suffix (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  E1ReflectedPlacement.entryR L (ReflectionE1.correction cx)++ReflectionE1TickGap.restX L++
    exitY L cy++fastConstNeg L cx

/-- The new suffix: the multiplication kernel ends in the merged exit, no trailing negation. -/
private def suffixX (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  E1ReflectedPlacement.entryR L (ReflectionE1.correction cx)++ExitMergeKernel.restXX L cx.val++
    exitY L cy

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=context (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (R2SqEp760.program760 L) (suffixX L cx cy) := by
  unfold generic secondStageX squareEntry context suffixX
  simp only [List.append_assoc]

private theorem suffix_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (suffixX L cx cy)+251=toffoliCount (suffix L cx cy) ∧
    measurementCount (suffixX L cx cy)+248=measurementCount (suffix L cx cy) ∧
    gateSlots (suffixX L cx cy)≤gateSlots (suffix L cx cy)+22425 := by
  have r := ExitMergeKernel.restXX_metrics L cx.val
  have n := fastConstNeg_counts L hw cx
  simp only [suffixX,suffix,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1TickGap.generic L cx cy=context (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (ReflectionE1Square.program L) (suffix L cx cy) := by
  unfold ReflectionE1TickGap.generic ReflectionE1TickGap.secondStage ReflectionE1.squareEntry context suffix
  simp only [List.append_assoc]

private theorem generic_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Facts (generic L cx cy) (ReflectionE1TickGap.generic L cx cy) := by
  exact relation_of_shapes Facts _ _ _ _ (generic_shape L cx cy) (old_generic_shape L cx cy)
    (context_facts2 (ReflectionE1TickGap.entryStage L (-cx) (-cy)) _ _ (suffixX L cx cy) (suffix L cx cy)
      ⟨(R2SqEp760.counts_diff760 L hw).1,(R2SqEp760.counts_diff760 L hw).2,R2SqEp760.slots_le760 L hw⟩
      (suffix_facts L hw cx cy))

/-- The new square adds its host site; the merged exit adds only its placed circuit. -/
theorem generic_support_envelope (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1TickGap.generic L cx cy)∪wires (R2SqEp760.program760 L)∪
      wires (renameProgram (wireFn2 L) (renameProgram Rolling1588Lifetime.phaseHost
        (ExitMergeKernel.x1 cx.val))) := by
  rw [generic_shape,old_generic_shape]
  intro q hq
  have rx := ExitMergeKernel.restXX_support L cx.val
  simp only [context,suffixX,suffix,wires_append,Finset.mem_union] at hq ⊢
  rcases hq with h|h|(h|h)|h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl h))))))
  · rcases Finset.mem_union.mp (rx h) with h'|h'
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h'))))))
    · exact Or.inr h'
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr h)))))

private def logicalTargetX (i : Nat) : Nat :=
  if i=1800 then 2312 else if i=770 then 1026 else if i=1285 then 1541 else
    if i=1286 then 1542 else if i=769 then 1797 else i

private theorem target_factsX (L : ControlledPointLayout) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    wireFn2 L (base (logicalTargetX i))=L.core.poolWire i ∧
    base (logicalTargetX i)∈OB5Support.logicalSites ∧
    logicalTargetX i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨rfl,?_,by decide⟩
  all_goals
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    simp only [logicalTargetX,OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    norm_num

private theorem placedX1_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (renameProgram (wireFn2 L) (renameProgram Rolling1588Lifetime.phaseHost
      (ExitMergeKernel.x1 k))) := by
  obtain ⟨map,logical,target⟩:=target_factsX L i hi
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩:=Finset.mem_image.mp used
  have same : wireFn2 L q=wireFn2 L (base (logicalTargetX i)):=eq.trans map.symm
  have back:=(placement2 L hw hn).injectiveOnSlots q
    (ArithmeticOB5.logical_sub_old (ExitMergeKernel.hostedX1_logical k hq)) (base (logicalTargetX i))
    (ArithmeticOB5.logical_sub_old logical) same
  rw [back] at hq
  obtain ⟨j,e,hj⟩ := ExitMergeKernel.hostedX1_labels k _ hq
  exact E1QubitPlacement.sw_avoid j hj (base_injective e ▸ target)

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_envelope L cx cy).trans (Finset.union_subset (Finset.union_subset
    (ReflectionE1TickGap.generic_sites L hw hn cx cy) (R2SqEp760.program760_support L hw hn))
    (ExitMergeKernel.placedX1_sites L hw cx.val))

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) := by
  intro used
  rcases Finset.mem_union.mp (generic_support_envelope L cx cy used) with old|x
  · rcases Finset.mem_union.mp old with old|sq
    · exact ReflectionE1TickGap.generic_free L hw hn cx cy i hi old
    · exact R2SqEp760.program760_free_old L hw hn i hi sq
  · exact placedX1_free L hw hn cx.val i hi x

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old:=fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1TickGap.generic_physical L hw hn cx cy)
  have rx := ExitMergeKernel.restXX_physical L hw hn cx.val
  simp only [context,suffix,gatePhysical_append] at old
  rw [generic_shape]
  simp only [context,suffixX,gatePhysical_append]
  exact ⟨old.1,R2SqEp760.program760_physical L hw hn,⟨old.2.2.1.1.1,rx⟩,old.2.2.1.2⟩

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program) (h : Facts P Q) :
    Facts (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs⟩
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Facts (gen L cx cy) (ReflectionE1TickGap.gen L cx cy) := by
  apply relation_of_shapes Facts _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1TickGap.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1TickGap.gen ReflectionE1TickGap.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L hw cx cy)

theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+494=toffoliCount (ReflectionE1TickGap.gen L cx cy) ∧
    measurementCount (gen L cx cy)+333=measurementCount (ReflectionE1TickGap.gen L cx cy) ∧
    gateSlots (gen L cx cy)≤gateSlots (ReflectionE1TickGap.gen L cx cy)+22425 :=
  ⟨(gen_facts L hw cx cy).1,(gen_facts L hw cx cy).2.1,(gen_facts L hw cx cy).2.2⟩

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

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts P Q) :
    toffoliCount (Edges.wrapper L C cy P)+494=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)+333=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P)≤gateSlots (Edges.wrapper L C cy Q)+22425 := by
  rcases h with ⟨ht,hm,hs⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2151064 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout layout_widths cx cy)).1
  have old:=ReflectionE1TickGap.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1498883 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout layout_widths cx cy)).2.1
  have old:=ReflectionE1TickGap.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50211624+Rolling1588.slotGrowth := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout layout_widths cx cy)).2.2
  have old:=ReflectionE1TickGap.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end -- original module boundary

-- ===== R2 (retired poolWire 760) =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000


/-! ### R2: the retired pool wire `poolWire 760` is absent from the final generic point program. -/
namespace ECDSAAdd.Entrant.R2Final760
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] wires

theorem logical760 : base 760∈OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨760,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  omega

theorem placed_760 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (K : Program) (ks : wires K⊆OB5Support.logicalSites) (kf : base 760∉wires K) :
    L.core.poolWire 760∉wires (renameProgram (wireFn2 L) K) := by
  have map : wireFn2 L (base 760)=L.core.poolWire 760 := rfl
  rw [renameProgram_support]
  intro used
  obtain ⟨old,oldUsed,eq⟩:=Finset.mem_image.mp used
  have mapped : wireFn2 L old=wireFn2 L (base 760) := by rw [map];exact eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (ks oldUsed)) (base 760)
    (ArithmeticOB5.logical_sub_old logical760) mapped
  exact kf (back ▸ oldUsed)

private theorem sw_rho_760 (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
      j=721 ∨ j=722 ∨ j=2400) :
    E1QubitPlacement.sw (E1QubitPlacement.rhoN j)≠760 := by
  have range:=E1QubitPlacement.rhoN_range j hj
  generalize E1QubitPlacement.rhoN j=i at range ⊢
  unfold E1QubitPlacement.Rng at range
  unfold E1QubitPlacement.sw
  split_ifs <;> omega

theorem entryM_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    L.core.poolWire 760∉wires (E1QubitPlacement.entryM L k) := by
  rw [E1QubitPlacement.entryM_eq]
  apply placed_760 L hw hn _ (E1QubitPlacement.logicalM k.val)
  intro h
  obtain ⟨j,e,hj⟩ := E1QubitPlacement.merged_labels k.val (base 760) h
  exact sw_rho_760 j hj (base_injective e).symm

private theorem reflected_logical (k : Nat) :
    wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k)))⊆OB5Support.logicalSites := by
  intro q hq
  simp only [renameProgram_support,Finset.mem_image] at hq
  obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩:=hq
  obtain ⟨j,rfl,hj⟩:=E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k hb)
  rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range j hj)

theorem entryR_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    L.core.poolWire 760∉wires (E1ReflectedPlacement.entryR L k) := by
  have logicalFree : base 760∉wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k.val))) := by
    intro h
    simp only [renameProgram_support,Finset.mem_image] at h
    obtain ⟨a,⟨b,hb,rfl⟩,eq⟩ := h
    obtain ⟨j,rfl,hj⟩ := E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k.val hb)
    rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base] at eq
    exact sw_rho_760 j hj (base_injective eq)
  have h:=placed_760 L hw hn _ (reflected_logical k.val) logicalFree
  simpa only [E1ReflectedPlacement.entryR,renameProgram_comp,E1QubitPlacement.pmapR,
    E1QubitPlacement.pmap,Function.comp_def] using h

private theorem suffix_free (P Q R : Program) (q : Wire) (shape : P=Q++R) (free : q∉wires P) :
    q∉wires R := by
  rw [shape,wires_append] at free
  exact fun h => free (Finset.mem_union_right _ h)

theorem restE_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (kernel : base 760∉wires Rolling1588TickGap.entryKernel) :
    L.core.poolWire 760∉wires (ReflectionE1TickGap.restE L) :=
  suffix_free _ _ _ _ (ReflectionE1TickGap.entry_split L)
    (placed_760 L hw hn _ Rolling1588TickGap.entryKernel_support kernel)

theorem restX_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (kernel : base 760∉wires Rolling1588TickGap.exitKernel) :
    L.core.poolWire 760∉wires (ReflectionE1TickGap.restX L) :=
  suffix_free _ _ _ _ (ReflectionE1TickGap.exit_split L)
    (placed_760 L hw hn _ Rolling1588TickGap.exitKernel_support kernel)

theorem generic_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryK : base 760∉wires Rolling1588TickGap.entryKernel)
    (_exitK : base 760∉wires Rolling1588TickGap.exitKernel)
    (square : L.core.poolWire 760∉wires (R2SqEp760.program760 L)) (cx cy : Fp) :
    L.core.poolWire 760∉wires (ReflectionE1TickGapLow48.generic L cx cy) := by
  have bounds : 515≤760 ∧ 760<2613 := by omega
  have y := ExitGenericQ5.constant_ports_avoid_large L hw hn 760 bounds L.point.y (Or.inr rfl)
  have ey := exitY_support L hw cy
  have fy := fusedY_support L hw (-cy)
  have rx : L.core.poolWire 760∉wires (ExitMergeKernel.restXX L cx.val) :=
    suffix_free _ _ _ _ (ExitMergeKernel.exit_splitX L cx.val)
      (placed_760 L hw hn _ (ExitMergeKernel.kernelX_support cx.val) (ExitMergeKernel.kernelX_760_free cx.val))
  simp only [ReflectionE1TickGapLow48.generic,ReflectionE1TickGap.entryStage,
    ReflectionE1TickGapLow48.secondStageX,ReflectionE1TickGapLow48.squareEntry,
    wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨fun h=>y (fy h),entryM_760_free L hw hn (-cx)⟩,restE_760_free L hw hn entryK⟩,
    ⟨⟨⟨square,entryR_760_free L hw hn _⟩,rx⟩,fun h=>y (ey h)⟩⟩

end ECDSAAdd.Entrant.R2Final760

namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

theorem generic_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : L.core.poolWire 760∉wires (generic L cx cy) :=
  R2Final760.generic_760_free L hw hn Rolling1588TickGap.entryKernel_760_free
    Rolling1588TickGap.exitKernel_760_free (R2SqEp760.square760_free L hw hn) cx cy

/-- R2: the Low48 point with the lifetime halves and renamed endpoints/square uses 1587 qubits. -/
theorem wrapper_qubits760 (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits760 _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp))
    (generic_760_free layout layout_widths layout_nodup cx cy) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Final =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Low48Generic

/-! E1/reflected Q1588 with TickGap tails and the Low48 square prefix. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151064,1498883,1588,50211624+Rolling1588.slotGrowth⟩

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

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2151064 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1498883 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50211624+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1498883
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50211624+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1

def sentinel : Nat := 115792089237316195423570985008687907853269984665640564039457584007908834671662
def sentinelHigh : Nat := 452312848583266388373324160190187140051835877600158453279131187530910662655

/-- Bits 1, 2, 5, 10..31 and 33..255 of `v`, packed in this order. -/
def probeVal (v : Nat) : Nat :=
  v / 2 % 4 + 4 * (v / 32 % 2) + 8 * (v / 1024 % 4194304) + 33554432 * (v / 8589934592)

theorem nonresidue_0 : ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem nonresidue_1 : ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem nonresidue_2 : ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem interval_nonresidue (n : Nat)
    (hn : n = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      n = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      n = 115792089237316195423570985008687907853269984665640564039457584007908834671662) :
    ((n : Fp)^3 + 7)^((p-1)/2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by norm_num [p]
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  have transport (q a : Nat) (hq : q = p)
      (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
      ((a : Fp)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    subst q
    exact h
  rcases hn with rfl | rfl | rfl
  · exact transport _ _ hp nonresidue_0
  · exact transport _ _ hp nonresidue_1
  · exact transport _ _ hp nonresidue_2

theorem curve_x_not_interval {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ (x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671662) := by
  intro h
  have power := interval_nonresidue x.val h
  rw [ZMod.natCast_zmod_val] at power
  have eq := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at eq
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using eq
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y ≠ 0 := by
    intro hz
    rw [← square,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1 = 2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,square,power] at fermat
  have two : ((2 : Nat) : Fp) = 0 := by
    have sum : (-1 : Fp)+1 = 1+1 := by rw [fermat]
    rw [neg_add_cancel] at sum
    exact_mod_cast (by rw [sum]; norm_num : (2 : Fp) = 0)
  rw [ZMod.natCast_eq_zero_iff] at two
  norm_num [p] at two

theorem probe_cases (v : Nat)
    (hv : v < 115792089237316195423570985008687907853269984665640564039457584007908834671663)
    (h : probeVal v = sentinelHigh) :
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      v = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      v = 115792089237316195423570985008687907853269984665640564039457584007908834671662 := by
  unfold probeVal sentinelHigh at h
  omega

theorem curve_x_high_ne {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    probeVal x.val ≠ sentinelHigh := by
  intro h
  apply curve_x_not_interval hc
  have hv : x.val < 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    have hp : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by norm_num [p]
    exact lt_of_lt_of_eq (ZMod.val_lt x) hp
  exact probe_cases x.val hv h

theorem sentinel_lt : sentinel < p := by norm_num [sentinel,p]
theorem sentinel_val : (sentinel : Fp).val = sentinel :=
  ZMod.val_natCast_of_lt sentinel_lt
theorem sentinel_ne_zero : (sentinel : Fp) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [sentinel_val,ZMod.val_zero] at this
  norm_num [sentinel] at this
theorem sentinel_high : probeVal sentinel = sentinelHigh := by
  unfold probeVal sentinel sentinelHigh
  norm_num

end ECDSAAdd.Entrant.FiniteFlagInterval
end

section
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic

theorem drop_sublist_drop (r : List Wire) (a b : Nat) (hab : a ≤ b) : (r.drop b).Sublist (r.drop a) := by
  have e : r.drop b = (r.drop a).drop (b - a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e]
  exact List.drop_sublist _ _

theorem seg_sublist (r rest : List Wire) (a k : Nat) (h : rest.Sublist (r.drop (a + k))) :
    ((r.drop a).take k ++ rest).Sublist (r.drop a) := by
  have e : (r.drop a).drop k = r.drop (a + k) := by
    rw [List.drop_drop]
  conv_rhs => rw [← List.take_append_drop k (r.drop a)]
  exact List.Sublist.append (List.Sublist.refl _) (e ▸ h)

theorem probe_sublist_gen (r : List Wire) :
    ((r.drop 1).take 2 ++ (r.drop 5).take 1 ++ (r.drop 10).take 22 ++ r.drop 33).Sublist r := by
  simp only [List.append_assoc]
  have hD : (r.drop 33).Sublist (r.drop (10 + 22)) := drop_sublist_drop r _ _ (by omega)
  have hC := seg_sublist r _ 10 22 hD
  have hB := seg_sublist r _ 5 1 ((hC).trans (drop_sublist_drop r _ _ (by omega)))
  have hA := seg_sublist r _ 1 2 ((hB).trans (drop_sublist_drop r _ _ (by omega)))
  exact hA.trans (List.drop_sublist _ _)

theorem probe_value_gen (r : List Wire) (hr : r.length = 256) (s : BasisState) :
    regValue ((r.drop 1).take 2 ++ (r.drop 5).take 1 ++ (r.drop 10).take 22 ++ r.drop 33) s =
      probeVal (regValue r s) := by
  have seg (a k : Nat) (h : a + k ≤ 256) :
      regValue ((r.drop a).take k) s = regValue r s / 2^a % 2^k := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by simp [hr]; omega),
      CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega)]
  have e1 := seg 1 2 (by norm_num)
  have e2 := seg 5 1 (by norm_num)
  have e3 := seg 10 22 (by norm_num)
  have e4 := CuccaroStreamedSquareWideLayout.regValue_drop_div r 33 (by omega) s
  simp only [Arithmetic.regValue_append, List.length_append, List.length_take, List.length_drop, hr,
    e1, e2, e3, e4, probeVal]
  norm_num

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalGadget =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

def probeX (L : ControlledPointLayout) : List Wire :=
  (L.point.x.drop 1).take 2 ++ (L.point.x.drop 5).take 1 ++ (L.point.x.drop 10).take 22 ++ L.point.x.drop 33
def probeControl (L : ControlledPointLayout) : Wire := (probeX L).headD 0
def probeTail (L : ControlledPointLayout) : List Wire := (probeX L).tail
def zrep (L : ControlledPointLayout) : Program :=
  [.X L.point.finite] ++ maskedConstant L.point.finite L.point.x sentinel ++ [.X L.point.finite]
def clrF (L : ControlledPointLayout) : Program :=
  [.X L.point.finite] ++ equalConstant (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw in
theorem probe_length : (probeX L).length = 248 := by
  simp [probeX,show L.point.x.length = 256 from hw.inputX]
include hw in
theorem probe_cons : probeX L = probeControl L :: probeTail L := by
  have h := probe_length L hw
  unfold probeControl probeTail
  cases e : probeX L with
  | nil => simp [e] at h
  | cons a t => rfl
include hw in
theorem probeTail_length : (probeTail L).length = 247 := by
  simp [probeTail,probe_length L hw]
include hw in
theorem probeControl_mem : probeControl L ∈ L.point.x := by
  apply (probe_sublist_gen L.point.x).subset
  change probeControl L ∈ probeX L
  rw [probe_cons L hw]
  simp
theorem probeTail_mem (q : Wire) (hq : q ∈ probeTail L) : q ∈ L.point.x :=
  (probe_sublist_gen L.point.x).subset (show q ∈ probeX L from List.mem_of_mem_tail hq)
include hw in
theorem work_length : (L.dialogPool.take 247).length = 247 := by
  simp [L.dialogPool_length hw]
include hw hn in
theorem probe_nodup :
    (probeControl L :: L.point.finite :: probeTail L ++ L.dialogPool.take 247).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 247 L.dialogPool).count_le q
  have hx := (probe_sublist_gen L.point.x).count_le q
  have hc := congrArg (List.count q) (probe_cons L hw)
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
    List.count_nil,List.cons_append] at h hc ⊢
  change (probeX L).count q ≤ L.point.x.count q at hx
  omega
include hw hn in
theorem finite_ne_probe : L.point.finite ≠ probeControl L := by
  intro h
  apply fin_not_x L hn
  rw [h]
  exact probeControl_mem L hw
include hw in
theorem probe_value_cons (s : BasisState) :
    regValue (probeX L) s = (if s (probeControl L) then 1 else 0) + 2*regValue (probeTail L) s := by
  conv_lhs => rw [probe_cons L hw]
  rfl
include hw in
theorem probe_value (s : BasisState) : regValue (probeX L) s = probeVal (regValue L.point.x s) :=
  probe_value_gen L.point.x hw.inputX s

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (L.dialogPool.take 247) s.basis = 0) :
    run (clrF L) m s = ⟨s.phase, writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ decide (regValue (probeX L) s.basis ≠ sentinelHigh))⟩ := by
  have nd := probe_nodup L hw hn
  have hfx := finite_ne_probe L hw hn
  have hft : L.point.finite ∉ (probeTail L) := by
    intro h; exact fin_not_x L hn (probeTail_mem L _ h)
  have hfp : L.point.finite ∉ L.dialogPool.take 247 := by
    intro h
    have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take h)
    simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons,
      beq_self_eq_true, if_true] at hh
    omega
  let s1 : State := ⟨s.phase, writeBit s.basis L.point.finite (!s.basis L.point.finite)⟩
  have h1 : run [.X L.point.finite] [] s = s1 := rfl
  have hz1 : regValue (L.dialogPool.take 247) s1.basis = 0 := by
    rw [← hz]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfp (e ▸ hq)
    simp [s1, writeBit, this]
  have hh := equalPorts_correct (probeControl L) L.point.finite (probeTail L) (L.dialogPool.take 247) 226156424291633194186662080095093570025917938800079226639565593765455331327
    ((probeTail_length L hw).trans (work_length L hw).symm) nd
    (by rw [probeTail_length L hw]; norm_num) s1 m hz1
  have hm0 : measurementCount [Instr.X L.point.finite] = 0 := rfl
  rw [clrF, run_append, hm0, List.take_zero, List.drop_zero, h1, hh]
  have e1 : s1.basis L.point.finite = !s.basis L.point.finite := by simp [s1, writeBit]
  have e2 : s1.basis (probeControl L) = s.basis (probeControl L) := by simp [s1, writeBit, Ne.symm hfx]
  have e3 : regValue (probeTail L) s1.basis = regValue (probeTail L) s.basis := by
    apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hft (e ▸ hq)
    simp [s1, writeBit, this]
  rw [e1, e2, e3, probe_value_cons L hw]
  congr 1
  funext q
  by_cases hq : q = L.point.finite
  · subst hq
    simp only [s1, writeBit, Function.update_self]
    cases s.basis L.point.finite <;> cases s.basis (probeControl L) <;>
      by_cases ht : regValue (probeTail L) s.basis = 226156424291633194186662080095093570025917938800079226639565593765455331327 <;> simp [ht,sentinelHigh] <;> omega
  · simp [s1, writeBit, Function.update_of_ne hq]

include hw hn in
theorem zrep_run (s : State) (m : List Bool) :
    (run (zrep L) m s).phase = s.phase ∧
    (∀ q, q ∉ L.point.x → (run (zrep L) m s).basis q = s.basis q) ∧
    regValue L.point.x (run (zrep L) m s).basis =
      regValue L.point.x s.basis ^^^ (if s.basis L.point.finite then 0 else sentinel) := by
  have hfx := fin_not_x L hn
  have hnd := finX_nodup L hn
  let s1 : State := ⟨s.phase, writeBit s.basis L.point.finite (!s.basis L.point.finite)⟩
  have h1 : run [.X L.point.finite] [] s = s1 := rfl
  have hm0 : measurementCount [Instr.X L.point.finite] = 0 := rfl
  have hmc := (maskedConstant_counts L.point.finite L.point.x sentinel).2
  have hk : sentinel < 2 ^ L.point.x.length := by
    rw [show L.point.x.length = 256 from hw.inputX]; norm_num [sentinel]
  obtain ⟨tp, tout, tx⟩ := maskedConstant_correct L.point.finite L.point.x sentinel hnd hfx hk s1 []
  obtain ⟨t, ht⟩ : ∃ t : State, t = run (maskedConstant L.point.finite L.point.x sentinel) [] s1 := ⟨_, rfl⟩
  rw [← ht] at tp tout tx
  have hrun : run (zrep L) m s = ⟨t.phase, writeBit t.basis L.point.finite (!t.basis L.point.finite)⟩ := by
    rw [zrep, run_append, run_append, measurementCount_append, hm0, hmc, Nat.add_zero,
      List.take_zero, List.drop_zero, List.take_nil, List.drop_nil, h1, ← ht]
    rfl
  have tf : t.basis L.point.finite = !s.basis L.point.finite := by
    rw [tout _ hfx]; simp [s1, writeBit]
  rw [hrun]
  refine ⟨tp, ?_, ?_⟩
  · intro q hq
    by_cases hqf : q = L.point.finite
    · subst hqf; simp [writeBit, tf]
    · simp only [writeBit, Function.update_of_ne hqf]
      rw [tout q hq]; simp [s1, writeBit, Function.update_of_ne hqf]
  · have e1 : regValue L.point.x (writeBit t.basis L.point.finite (!t.basis L.point.finite)) =
        regValue L.point.x t.basis := by
      apply regValue_congr; intro q hq
      have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
      simp [writeBit, this]
    have e2 : regValue L.point.x s1.basis = regValue L.point.x s.basis := by
      apply regValue_congr; intro q hq
      have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
      simp [s1, writeBit, this]
    show regValue L.point.x (writeBit t.basis L.point.finite (!t.basis L.point.finite)) = _
    rw [e1, tx, e2]
    have : s1.basis L.point.finite = !s.basis L.point.finite := by simp [s1, writeBit]
    rw [this]
    cases s.basis L.point.finite <;> rfl

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))) := by
  intro s m v
  have hz : regValue (L.dialogPool.take 247) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz,probe_value L hw]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite = base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite ∉ L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [← v.x]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit, this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [← v.y]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit, this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit, Ne.symm (fin_ne_generic L hn), v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [← v.clean]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit, this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q = writeBit base L.point.finite _ q
    by_cases hqf : q = L.point.finite
    · subst hqf; simp [writeBit, hfs, v.x]
    · simp [writeBit, hqf, v.rest q hq]

include hw hn in
theorem zrep_step (X X' Y : Fp) (G : Bool) (base : BasisState)
    (hX : X'.val = X.val ^^^ (if base L.point.finite then 0 else sentinel)) :
    Triple (PointDialogValues L X Y G base) (zrep L) (PointDialogValues L X' Y G base) := by
  intro s m v
  obtain ⟨hp, hout, hx⟩ := zrep_run L hw hn s m
  have hf : s.basis L.point.finite = base L.point.finite := v.rest _ (finite_not_x L hn)
  refine ⟨hp, v.withX hn ?_ hout⟩
  rw [hx, v.x, hf, hX]

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalResources =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
theorem ports_length : (zeroPorts (probeTail L) (L.dialogPool.take 247)).length = 247 := by
  have h := (zeroPorts_maps (probeTail L) (L.dialogPool.take 247)
    ((probeTail_length L hw).trans (work_length L hw).symm)).1
  simpa only [List.length_map,probeTail_length L hw] using congrArg List.length h

theorem zrep_counts : toffoliCount (zrep L) = 0 ∧ measurementCount (zrep L) = 0 := by
  have h := maskedConstant_counts L.point.finite L.point.x sentinel
  simp only [zrep,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hw in
theorem clrF_counts : toffoliCount (clrF L) = 247 ∧ measurementCount (clrF L) = 247 := by
  have h := equalConstant_counts (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  simp only [clrF,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hn in
theorem zrep_physical : GatePhysical (zrep L) := by
  simp only [zrep,gatePhysical_append]
  refine ⟨⟨?_,maskedConstant_physical _ _ _ (fin_not_x L hn)⟩,?_⟩
  all_goals intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial

include hw hn in
theorem clrF_physical : GatePhysical (clrF L) := by
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  simp only [clrF,gatePhysical_append]
  refine ⟨?_,equalConstant_physical _ _ _ _ ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial
  · exact (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)

include hw in
theorem old_clrF_support : wires (ECDSAAdd.Entrant.clrF L) =
    (L.point.finite :: (L.point.x ++ L.dialogPool.take 255)).toFinset := by
  have hl := (finTail_length L hw).trans (finWork255_length L hw).symm
  rw [ECDSAAdd.Entrant.clrF,wires_append,equalConstant_wires]
  ext q
  have hp : q ∈ (zeroPorts L.point.x.tail (L.dialogPool.take 255)).flatMap ZeroBit.wires ↔
      q ∈ L.point.x.tail ++ L.dialogPool.take 255 :=
    (zeroPorts_perm L.point.x.tail (L.dialogPool.take 255) hl).mem_iff
  have hx : q ∈ L.point.x ↔ q = x0 L ∨ q ∈ L.point.x.tail := by
    conv_lhs => rw [x_cons L hw]
    simp
  simp only [Finset.mem_union,wires,Instr.wires,Finset.union_empty,Finset.mem_singleton,
    List.mem_toFinset,List.mem_cons] at *
  rw [hp]
  simp only [List.mem_append] at *
  tauto

include hw in
theorem zrep_support_old : wires (zrep L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [old_clrF_support L hw]
  intro q used
  simp only [zrep,wires_append,Finset.mem_union] at used
  rcases used with (h | h) | h
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]
  · have h' := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h' ⊢
    tauto
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]

include hw in
theorem clrF_support_old : wires (clrF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [old_clrF_support L hw]
  intro q used
  simp only [clrF,wires_append,Finset.mem_union] at used
  rcases used with h | h
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]
  · rw [equalConstant_wires] at h
    have h' := List.mem_toFinset.mp h
    rcases List.mem_cons.mp h' with e | h'
    · subst q
      simp [probeControl_mem L hw]
    rcases List.mem_cons.mp h' with e | h'
    · subst q; simp
    have hl := (probeTail_length L hw).trans (work_length L hw).symm
    rcases List.mem_append.mp ((zeroPorts_perm _ _ hl).subset h') with inp | work
    · simp [probeTail_mem L q inp]
    · have included : L.dialogPool.take 247 ⊆ L.dialogPool.take 255 := by
        have h : L.dialogPool.take 247 = (L.dialogPool.take 255).take 247 := by
          rw [List.take_take]; rfl
        rw [h]
        exact List.take_subset _ _
      simp [included work]

include hw in
theorem zrep_slots : gateSlots (zrep L) ≤ 258 := by
  have h := maskedConstant_gateSlots_le L.point.finite L.point.x sentinel
  rw [show L.point.x.length = 256 from hw.inputX] at h
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [zrep,gateSlots_append,one]
  omega

include hw in
theorem clrF_slots : gateSlots (clrF L) ≤ 2261 := by
  have h := equalConstant_gateSlots_le (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [clrF,gateSlots_append,one]
  omega

def constantSlots : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, k => (if k % 2 = 1 then 1 else 0) + constantSlots n (k/2)

theorem xor_slots_exact (r : List Wire) (k : Nat) :
    gateSlots (xorConstant r k) = constantSlots r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [xorConstant,constantSlots,List.length_cons,gateSlots_append]
    split <;> simp [gateSlots_cons,instructionSlots,ih]

theorem masked_slots_exact (c : Wire) (r : List Wire) (k : Nat) :
    gateSlots (maskedConstant c r k) = constantSlots r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [maskedConstant,constantSlots,List.length_cons,gateSlots_append]
    split <;> simp [gateSlots_cons,instructionSlots,ih]

theorem equal_slots_exact (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    gateSlots (equalConstant c t bs k) = 7*bs.length+1+2*constantSlots bs.length k := by
  simp only [equalConstant,gateSlots_append,zeroControlled_gateSlots,xor_slots_exact,List.length_map]
  omega

include hw in
theorem zrep_slots_exact : gateSlots (zrep L) = 251 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [zrep,gateSlots_append,one,masked_slots_exact,
    show L.point.x.length = 256 from hw.inputX]
  decide +kernel

include hw in
theorem old_zrep_slots_exact : gateSlots (ECDSAAdd.Entrant.zrep L) = 4 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [ECDSAAdd.Entrant.zrep,gateSlots_append,one,masked_slots_exact,
    show L.point.x.length = 256 from hw.inputX]
  decide +kernel

include hw in
theorem clrF_slots_exact : gateSlots (clrF L) = 2225 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [clrF,gateSlots_append,one,equal_slots_exact,ports_length L hw]
  decide +kernel

include hw in
theorem old_clrF_slots_exact : gateSlots (ECDSAAdd.Entrant.clrF L) = 1789 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [ECDSAAdd.Entrant.clrF,gateSlots_append,one,equal_slots_exact,finClr_ports_length L hw]
  decide +kernel

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalPoint =====
section
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

def clearF : Program := [.X L.point.finite] ++ MeasuredZeroClear.equalClear
  (probeControl L) L.point.finite (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (L.dialogPool.take 247) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  let bs := zeroPorts (probeTail L) (L.dialogPool.take 247)
  let s1 := run [Instr.X L.point.finite] [] s
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  have nd : (probeControl L::L.point.finite::bs.flatMap ZeroBit.wires).Nodup :=
    (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)
  have hz1 : ∀b∈bs,s1.basis b.work=false := by
    intro b hb
    have mem : b.work∈L.dialogPool.take 247 := by
      rw [←(zeroPorts_maps _ _ hl).2]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    have ne : b.work≠L.point.finite := fun eq =>
      fin_not_pool L hn (eq ▸ List.mem_of_mem_take mem)
    simpa [s1,run,writeBit,ne] using (regValue_zero _ _).mp hz b.work mem
  have zero : (run (equalConstant (probeControl L) L.point.finite bs 226156424291633194186662080095093570025917938800079226639565593765455331327) m s1).basis
      L.point.finite=false := by
    simpa only [clrF,run_append,show measurementCount [Instr.X L.point.finite]=0 from rfl,
      List.take_zero,List.drop_zero] using hzero
  have eq := MeasuredZeroClear.equal_run_eq _ _ bs 226156424291633194186662080095093570025917938800079226639565593765455331327 nd s1 m hz1 zero
  simpa only [clearF,clrF,run_append,show measurementCount [Instr.X L.point.finite]=0 from rfl,
    List.take_zero,List.drop_zero] using eq

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=decide (probeVal X.val ≠ sentinelHigh)) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))) := by
  intro s m v
  have hz : regValue (L.dialogPool.take 247) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz,probe_value L hw,v.x]
    simp [writeBit,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

theorem clearF_support : wires (clearF L) ⊆ wires (clrF L) := by
  simp only [clearF,clrF,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (MeasuredZeroClear.equal_support _ _ _ _)

include hw in
theorem clearF_counts : toffoliCount (clearF L)=246 ∧ measurementCount (clearF L)=247 := by
  have h := MeasuredZeroClear.equal_counts (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  simp only [clearF,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hw in
theorem clearF_slots : gateSlots (clearF L)=2221 := by
  have ne : zeroPorts (probeTail L) (L.dialogPool.take 247)≠[] := by
    intro h
    have len := ports_length L hw
    rw [h] at len
    contradiction
  have h := MeasuredZeroClear.equal_slots (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327 ne
  have old := clrF_slots_exact L hw
  simp only [clearF,clrF,gateSlots_append] at old ⊢
  omega

include hw hn in
theorem clearF_physical : GatePhysical (clearF L) := by
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  simp only [clearF,gatePhysical_append]
  refine ⟨?_,MeasuredZeroClear.equal_physical _ _ _ _ ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial
  · exact (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)

end ECDSAAdd.Entrant.FiniteFlagInterval
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (probeVal X.val ≠ sentinelHigh) = fin) (h2 : decide (probeVal X'.val ≠ sentinelHigh) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
        L.point.finite ^^ decide (probeVal X'.val ≠ sentinelHigh)) = base := by
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
    have z1 := zrep_step L hw hn 0 (sentinel : Fp) 0 false s.basis (by rw [hfin, sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (sentinel : Fp) 0 (sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (sentinel : Fp) 0 cx cy base' sentinel_ne_zero) hfin
      (by rw [sentinel_val, sentinel_high]; decide) (by rw [sentinel_val, sentinel_high]; decide)
    have z2 := zrep_step L hw hn (sentinel : Fp) 0 0 false s.basis (by rw [hfin, sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (probeVal x.val ≠ sentinelHigh) = true := decide_eq_true (curve_x_high_ne hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide (probeVal (genericX x y cx cy).val ≠ sentinelHigh) = true :=
        decide_eq_true (curve_x_high_ne (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalFinal =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  ReflectionE1TickGapLow48.generic

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) := by
  intro q used
  have hz : q ∈ wires (zrep L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => zrep_support_old L hw h
  have hc : q ∈ wires (clrF L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clrF_support_old L hw h
  have he : q ∈ wires (clearF L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => hc (clearF_support L h)
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,
    generic,wires_append,Finset.mem_union] at used ⊢
  tauto

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy) ⊆ (OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (ReflectionE1TickGapLow48.gen_sites L hw hn cx cy)

theorem gen_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+17 = toffoliCount (ReflectionE1TickGapLow48.gen L cx cy) ∧
    measurementCount (gen L cx cy)+16 = measurementCount (ReflectionE1TickGapLow48.gen L cx cy) ∧
    gateSlots (gen L cx cy) = gateSlots (ReflectionE1TickGapLow48.gen L cx cy)+1362 := by
  have z := zrep_counts L
  have c := clrF_counts L hw
  have e := clearF_counts L hw
  have oz := ECDSAAdd.Entrant.zrep_counts L
  have oc := ECDSAAdd.Entrant.clrF_counts L hw
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,generic,
    toffoliCount_append,measurementCount_append,gateSlots_append,z.1,z.2,c.1,c.2,
    oz.1,oz.2,oc.1,oc.2,e.1,e.2,zrep_slots_exact L hw,clrF_slots_exact L hw,clearF_slots L hw,
    old_zrep_slots_exact L hw,old_clrF_slots_exact L hw]
  omega

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := zrep_physical L hn
  have c := clrF_physical L hw hn
  have e := clearF_physical L hw hn
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

theorem wrapper_support_mono (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : wires P ⊆ wires Q) :
    wires (Edges.wrapper L C cy P) ⊆ wires (Edges.wrapper L C cy Q) := by
  simp only [Edges.wrapper,Edges.finiteProgram,wires_append,renameProgram_support]
  repeat' first
    | exact h
    | exact Finset.Subset.refl _
    | apply Finset.union_subset_union
    | apply Finset.image_subset_image

theorem wrapper_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+17 =
      toffoliCount (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+16 =
      measurementCount (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy)) =
      gateSlots (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy))+1362 := by
  have h := gen_counts L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1588 := by
  have h := wrapper_support_mono layout C cy _ _ (gen_support_subset layout layout_widths cx cy)
  have card := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)
  exact card.trans (ReflectionE1TickGapLow48.wrapper_qubits C cx cy)

theorem wrapper_qubits760 (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1587 := by
  have h := wrapper_support_mono layout C cy _ _ (gen_support_subset layout layout_widths cx cy)
  have card := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)
  exact card.trans (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2151047 := by
  have h := (wrapper_counts layout layout_widths (.some hc) cx cy).1
  have old := ReflectionE1TickGapLow48.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1498867 := by
  have h := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
  have old := ReflectionE1TickGapLow48.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50212986+Rolling1588.slotGrowth := by
  have h := (wrapper_counts layout layout_widths C cx cy).2.2
  have old := ReflectionE1TickGapLow48.wrapper_slots C cx cy
  omega

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151047,1498867,1588,50212986+Rolling1588.slotGrowth⟩

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

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2151047 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1498867 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50212986+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1498867
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50212986+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.Main =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.MeasuredDHFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      MeasuredDH.wrapper layout C cy (FiniteFlagInterval.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151084,1498894,1588,50212975+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := FiniteFlagInterval.gen_sites layout layout_widths layout_nodup cx cy
    have support := (MeasuredDH.wrapper_support layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ b R _
      (MeasuredDH.full_spec layout layout_widths layout_nodup R hc b _
        (FiniteFlagInterval.genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151084 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤2151084
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498894 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤1498894
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := MeasuredDH.wrapper_support layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (FiniteFlagInterval.wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact MeasuredDH.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FiniteFlagInterval.gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50212975+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    change gateSlots (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤50212975+Rolling1588.slotGrowth
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498894
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50212975+Rolling1588.slotGrowth
    rw [normalize_slots]; exact program_gateSlots C
end ECDSAAdd.Entrant.MeasuredDHFinal
end
end

-- ===== merged module ECDSAAdd.Submission.Entrant.FusedBoundaryFinal =====
section
namespace ECDSAAdd.Entrant.FusedBoundaryFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (FiniteFlagInterval.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151044,1498865,1587,50236557⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := FiniteFlagInterval.gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (FiniteFlagInterval.gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ b R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc b _
        (FiniteFlagInterval.genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151044 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤2151044
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498865 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤1498865
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1587 := by
  cases C with
  | zero => change qubits []≤1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (FiniteFlagInterval.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (FiniteFlagInterval.wrapper_qubits760 (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FiniteFlagInterval.gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50236557 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=23581 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤50236557
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498865
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50236557
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.FusedBoundaryFinal
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineMath =====
section
/-!
A 247-bit affine finite-point probe. The design follows the unintegrated
research direction in Yukon submission a67cb86c-fb4d-4634-98e9-dcb7b60d563a:
bits 1 and 2 agree; bit 5 and the selected high bits are set.
The case split and field proofs below are independently reconstructed.
-/
namespace ECDSAAdd.Entrant.CodexAffineMath
open Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def matchesX (v : Nat) : Prop :=
  v / 2 % 2 = v / 4 % 2 ∧
  v / 32 % 2 = 1 ∧
  v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607

instance : DecidablePred matchesX := fun v =>
  inferInstanceAs (Decidable (v / 2 % 2 = v / 4 % 2 ∧ v / 32 % 2 = 1 ∧
    v / 1024 % 4194304 = 4194303 ∧
    v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607))

def excluded (v : Nat) : Prop :=
  v = 115792089237316195423570985008687907853269984665640564039457584007908834671648 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671649 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671656 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671657 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671662

theorem matches_cases (v : Nat) (hv : v < p) (h : matchesX v) : excluded v := by
  unfold matchesX at h
  unfold excluded
  norm_num [p] at hv
  omega

theorem sentinel_matches : matchesX (p-1) := by
  norm_num [matchesX,p]

private theorem nonresidue_0 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671648 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_1 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671649 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_2 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_3 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_4 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_5 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671657 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_6 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem excluded_nonresidue (v : Nat) (hv : excluded v) :
    ((v : Fp)^3+7)^((p-1)/2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by norm_num [p]
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  have transport (q a : Nat) (hq : q=p)
      (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
      ((a : Fp)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    subst q
    exact h
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transport _ _ hp nonresidue_0
  · exact transport _ _ hp nonresidue_1
  · exact transport _ _ hp nonresidue_2
  · exact transport _ _ hp nonresidue_3
  · exact transport _ _ hp nonresidue_4
  · exact transport _ _ hp nonresidue_5
  · exact transport _ _ hp nonresidue_6

theorem curve_x_not_matches {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ matchesX x.val := by
  intro h
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have power := excluded_nonresidue x.val (matches_cases x.val (ZMod.val_lt x) h)
  rw [ZMod.natCast_zmod_val] at power
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using equation
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [←square,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1=2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,square,power] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

theorem probe_bridge (a b : Bool) (rest v : Nat)
    (h : (if a then 1 else 0)+2*((if b then 1 else 0)+2*rest) =
      v / 2 % 4 + 4*(v / 32 % 2) + 8*(v / 1024 % 4194304) +
      33554432*(v / 8589934592)) :
    (!(b ^^ a) && decide (rest=2^246-1)) = decide (matchesX v) := by
  change (!(b ^^ a) && decide (rest=113078212145816597093331040047546785012958969400039613319782796882727665663)) = decide (matchesX v)
  have low : v / 2 % 4 = v / 2 % 2 + 2*(v / 4 % 2) := by
    have h4 : v / 2 / 2 = v / 4 := by simp [Nat.div_div_eq_div_mul]
    have h8 : v / 2 / 4 = v / 4 / 2 := by simp [Nat.div_div_eq_div_mul]
    omega
  have tail : rest = v / 32 % 2 + 2*(v / 1024 % 4194304) + 8388608*(v / 8589934592) := by
    have hlt := Nat.mod_lt (v / 2) (by decide : 0 < 4)
    cases a <;> cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
  have bits : (if a then 1 else 0) = v / 2 % 2 ∧ (if b then 1 else 0) = v / 4 % 2 := by
    cases a <;> cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
  have tail_iff : rest=113078212145816597093331040047546785012958969400039613319782796882727665663 ↔ v / 32 % 2 = 1 ∧ v / 1024 % 4194304 = 4194303 ∧ v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607 := by
    omega
  cases a <;> cases b <;> simp_all [matchesX] <;> omega

end ECDSAAdd.Entrant.CodexAffineMath
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineGadget =====
section
namespace ECDSAAdd.Entrant.CodexAffineGadget
open Arithmetic RecordedQuantum Challenge Baselines

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def view (a b : Wire) : Program := [.CX a b, .X b]
def restore (a b : Wire) : Program := [.X b, .CX a b]
def core (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ equalConstant b f (zeroPorts r work) k
def program (a b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view a b ++ core b f r work k ++ restore a b
def clearCore (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ MeasuredZeroClear.equalClear b f (zeroPorts r work) k
def clearProgram (a b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view a b ++ clearCore b f r work k ++ restore a b

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append, run_take]

theorem ports_length (r work : List Wire) (hl : r.length = work.length) :
    (zeroPorts r work).length = r.length := by
  have h := congrArg List.length (zeroPorts_maps r work hl).1
  simpa using h

theorem ports_nodup (a b f : Wire) (r work : List Wire)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    (b :: f :: (zeroPorts r work).flatMap ZeroBit.wires).Nodup := by
  exact (((zeroPorts_perm r work hl).cons f).cons b).nodup_iff.mpr
    (List.nodup_cons.mp hn).2

theorem view_run (a b : Wire) (_hab : a ≠ b) (s : State) (m : List Bool) :
    run (view a b) m s =
      ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ s.basis a))⟩ := by
  simp [view, run, writeBit]

theorem restore_update (a b f : Wire) (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
    (s : State) (m : List Bool) (z : Bool) :
    run (restore a b) m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ s.basis a))) f z⟩ =
      ⟨s.phase, writeBit s.basis f z⟩ := by
  simp only [restore, run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = b
  · subst q
    cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp [writeBit, hab, haf, hbf, ha, hb]
  · by_cases hqf : q = f
    · subst q
      simp [writeBit, hab, haf, hbf, hbf.symm]
    · simp [writeBit, hq, hqf, hab, haf, hbf]

theorem program_run (a b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (a :: b :: f :: (r ++ work)).Nodup) (hl : r.length = work.length)
    (hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0) :
    run (program a b f r work k) m s =
      ⟨s.phase, writeBit s.basis f
        (s.basis f ^^ !((!(s.basis b ^^ s.basis a)) && decide (regValue r s.basis = k)))⟩ := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hab : a ≠ b := sep.1.1
  have haf : a ≠ f := sep.1.2.1
  have hbf : b ≠ f := sep.2.1.1
  have hbr : b ∉ r := sep.2.1.2.1
  have hbw : b ∉ work := sep.2.1.2.2
  have hfr : f ∉ r := sep.2.2.1.1
  have hfw : f ∉ work := sep.2.2.1.2
  let u : State := ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ s.basis a))⟩
  let v : State := ⟨s.phase, writeBit u.basis f (!s.basis f)⟩
  have hu : run (view a b) m s = u := view_run a b hab s m
  have uv : run [.X f] m u = v := by simp [run, u, v, writeBit, hbf.symm]
  have hports := zeroPorts_maps r work hl
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← hports.2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    simpa [v, u, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have hr : regValue r v.basis = regValue r s.basis := by
    apply regValue_congr
    intro q hq
    simp [v, u, writeBit, show q ≠ b from fun e => hbr (e ▸ hq),
      show q ≠ f from fun e => hfr (e ▸ hq)]
  have eq := equalConstant_correct b f (zeroPorts r work) k (ports_nodup a b f r work hl hn)
    (by simpa only [ports_length r work hl] using hk) v m clean
  rw [hports.1, hr] at eq
  have vb : v.basis b = !(s.basis b ^^ s.basis a) := by simp [v, u, writeBit, hbf]
  have vf : v.basis f = !s.basis f := by simp [v, writeBit]
  rw [vb, vf] at eq
  have folded : ((!s.basis f) ^^
      (!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k))) =
      (s.basis f ^^ !(!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k))) := by
    cases s.basis f <;> cases (!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k)) <;> rfl
  rw [folded] at eq
  have shape : run (program a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, hu, uv]
  rw [shape, eq]
  simpa only [v, u, writeBit, Function.update_idem] using
    restore_update a b f hab haf hbf s (m.drop (zeroPorts r work).length)
      (s.basis f ^^ !(!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k)))

theorem program_counts (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (program a b f r work k) = r.length ∧
    measurementCount (program a b f r work k) = r.length := by
  simp [program, core, view, restore, toffoliCount_append, measurementCount_append,
    equalConstant_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem clearProgram_counts (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (clearProgram a b f r work k) = r.length - 1 ∧
    measurementCount (clearProgram a b f r work k) = r.length := by
  simp [clearProgram, clearCore, view, restore, toffoliCount_append, measurementCount_append,
    MeasuredZeroClear.equal_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem program_support (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    wires (program a b f r work k) ⊆ (a :: b :: f :: (r ++ work)).toFinset := by
  intro q hq
  have hp : q ∈ (zeroPorts r work).flatMap ZeroBit.wires ↔ q ∈ r ++ work :=
    (zeroPorts_perm r work hl).mem_iff
  simp only [program, core, view, restore, wires_append, equalConstant_wires, wires,
    Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty, or_false, List.mem_toFinset, List.mem_cons, hp] at hq ⊢
  tauto

theorem clearProgram_support (a b f : Wire) (r work : List Wire) (k : Nat) :
    wires (clearProgram a b f r work k) ⊆ wires (program a b f r work k) := by
  simp only [clearProgram, clearCore, program, core, wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (MeasuredZeroClear.equal_support b f (zeroPorts r work) k)))
    (Finset.Subset.refl _)

theorem clearProgram_run_eq (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup)
    (s : State) (m : List Bool) (hz : regValue work s.basis = 0)
    (hzero : (run (program a b f r work k) m s).basis f = false) :
    run (clearProgram a b f r work k) m s = run (program a b f r work k) m s := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have haf : a ≠ f := sep.1.2.1
  have hbf : b ≠ f := sep.2.1.1
  have haw : a ∉ work := sep.1.2.2.2
  have hbw : b ∉ work := sep.2.1.2.2
  have hfw : f ∉ work := sep.2.2.1.2
  let v := run [Instr.X f] m (run (view a b) m s)
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← (zeroPorts_maps r work hl).2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have nea : p.work ≠ a := fun e => haw (e ▸ mem)
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    have away : p.work ∉ wires (view a b) := by simp [view, wires, Instr.wires, nea, neb]
    change (run [Instr.X f] m (run (view a b) m s)).basis p.work = false
    rw [run_preserves_outside _ _ _ _ (by simp [wires, Instr.wires, nef]),
      run_preserves_outside _ _ _ _ away]
    exact (regValue_zero work s.basis).mp hz p.work mem
  have oldShape : run (program a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have newShape : run (clearProgram a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) m v) := by
    simp only [clearProgram, clearCore, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (MeasuredZeroClear.equal_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have away : f ∉ wires (restore a b) := by
    simp [restore, wires, Instr.wires, haf.symm, hbf.symm]
  have keep := run_preserves_outside (restore a b) (m.drop (zeroPorts r work).length)
    (run (equalConstant b f (zeroPorts r work) k) m v) f away
  have zero : (run (equalConstant b f (zeroPorts r work) k) m v).basis f = false := by
    rw [oldShape] at hzero
    exact keep.symm.trans hzero
  have eq := MeasuredZeroClear.equal_run_eq b f (zeroPorts r work) k
    (ports_nodup a b f r work hl hn) v m clean zero
  rw [oldShape, newShape, eq]

theorem clearProgram_eq (a b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (a :: b :: f :: (r ++ work)).Nodup) (hl : r.length = work.length)
    (_hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0)
    (hzero : (run (program a b f r work k) m s).basis f = false) :
    run (clearProgram a b f r work k) m s = run (program a b f r work k) m s :=
  clearProgram_run_eq a b f r work k hl hn s m hz hzero

theorem program_physical (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    GatePhysical (program a b f r work k) := by
  have hab : a ≠ b := by
    intro e
    exact (List.nodup_cons.mp hn).1 (by simp [e])
  have hv : GatePhysical (view a b) := by simp [view, GatePhysical, PhysicalInstr, ProperGate, hab]
  have hr : GatePhysical (restore a b) := by simp [restore, GatePhysical, PhysicalInstr, ProperGate, hab]
  simp only [program, core, gatePhysical_append]
  exact ⟨⟨hv, ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
    equalConstant_physical b f (zeroPorts r work) k (ports_nodup a b f r work hl hn)⟩⟩, hr⟩

theorem clearProgram_physical (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    GatePhysical (clearProgram a b f r work k) := by
  have old := program_physical a b f r work k hl hn
  simp only [program, core, gatePhysical_append] at old
  simp only [clearProgram, clearCore, gatePhysical_append]
  exact ⟨⟨old.1.1, ⟨old.1.2.1,
    MeasuredZeroClear.equal_physical b f (zeroPorts r work) k
      (ports_nodup a b f r work hl hn)⟩⟩, old.2⟩

theorem program_slots (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (program a b f r work k) ≤ 9 * r.length + 6 := by
  have h := equalConstant_gateSlots_le b f (zeroPorts r work) k
  rw [ports_length r work hl] at h
  simp only [program, core, view, restore, gateSlots_append] at *
  change 2 + (1 + gateSlots (equalConstant b f (zeroPorts r work) k)) + 2 ≤ _
  omega

theorem clearProgram_slots_le (a b f : Wire) (r work : List Wire) (k : Nat) :
    gateSlots (clearProgram a b f r work k) ≤ gateSlots (program a b f r work k) := by
  have h : gateSlots (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) ≤
      gateSlots (equalConstant b f (zeroPorts r work) k) := by
    by_cases he : zeroPorts r work = []
    · rw [he]
      exact Nat.le_refl _
    · have h := MeasuredZeroClear.equal_slots b f (zeroPorts r work) k he
      omega
  simp only [clearProgram, clearCore, program, core, gateSlots_append]
  omega

theorem clearProgram_slots (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (clearProgram a b f r work k) ≤ 9 * r.length + 6 :=
  (clearProgram_slots_le a b f r work k).trans (program_slots a b f r work k hl)

end ECDSAAdd.Entrant.CodexAffineGadget
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineProbe =====
section
/-! A reversible affine view combines the two low probe bits into their equality.
The arithmetic backend and public encoding are inherited unchanged. -/
namespace ECDSAAdd.Entrant.CodexAffineProbe
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def a (L : ControlledPointLayout) : Wire := FiniteFlagInterval.probeControl L
def b (L : ControlledPointLayout) : Wire := (FiniteFlagInterval.probeTail L).headD 0
def rest (L : ControlledPointLayout) : List Wire := (FiniteFlagInterval.probeTail L).tail
def work (L : ControlledPointLayout) : List Wire := L.dialogPool.take 246
def literal : Nat := 2^246-1
def finiteBit (v : Nat) : Bool := decide (¬ CodexAffineMath.matchesX v)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
theorem tail_cons : FiniteFlagInterval.probeTail L = b L :: rest L := by
  have h := FiniteFlagInterval.probeTail_length L hw
  unfold b rest
  cases e : FiniteFlagInterval.probeTail L with
  | nil => simp [e] at h
  | cons q qs => rfl

include hw in
theorem lengths : (rest L).length=246 ∧ (work L).length=246 := by
  simp [rest,work,FiniteFlagInterval.probeTail_length L hw,L.dialogPool_length hw]

theorem work_subset : work L ⊆ L.dialogPool.take 247 := by
  have h : work L=(L.dialogPool.take 247).take 246 := by
    simp only [work,List.take_take]; rfl
  rw [h]
  exact List.take_subset _ _

include hw hn in
theorem ports_nodup : (a L :: b L :: L.point.finite :: (rest L ++ work L)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (FiniteFlagInterval.probe_nodup L hw hn) q
  have hp : (work L).count q ≤ (L.dialogPool.take 247).count q := by
    have sub : (work L).Sublist (L.dialogPool.take 247) := by
      have e : work L=(L.dialogPool.take 247).take 246 := by
        simp only [work,List.take_take]; rfl
      rw [e]; exact List.take_sublist _ _
    exact sub.count_le q
  rw [tail_cons L hw] at h
  simp only [a,List.count_cons,List.count_append] at h ⊢
  omega

include hw in
theorem inputs_mem : a L∈L.point.x ∧ b L∈L.point.x ∧ ∀q∈rest L,q∈L.point.x := by
  refine ⟨FiniteFlagInterval.probeControl_mem L hw,?_,?_⟩
  · apply FiniteFlagInterval.probeTail_mem L
    rw [tail_cons L hw]; simp
  · intro q hq
    exact FiniteFlagInterval.probeTail_mem L q (List.mem_of_mem_tail hq)

include hw in
theorem hit (s : BasisState) :
    (!(s (b L) ^^ s (a L)) && decide (regValue (rest L) s=literal)) =
      decide (CodexAffineMath.matchesX (regValue L.point.x s)) := by
  have h := FiniteFlagInterval.probe_value L hw s
  rw [FiniteFlagInterval.probe_cons L hw,tail_cons L hw] at h
  exact CodexAffineMath.probe_bridge (s (a L)) (s (b L))
    (regValue (rest L) s) (regValue L.point.x s) h

def clrF : Program := CodexAffineGadget.program (a L) (b L) L.point.finite (rest L) (work L) literal
def clearF : Program := CodexAffineGadget.clearProgram (a L) (b L) L.point.finite (rest L) (work L) literal

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0) :
    run (clrF L) m s = ⟨s.phase,writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ finiteBit (regValue L.point.x s.basis))⟩ := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have hk : literal < 2^(rest L).length := by rw [(lengths L hw).1]; decide
  rw [clrF,CodexAffineGadget.program_run _ _ _ _ _ _ (ports_nodup L hw hn) hl hk s m hz,
    hit L hw s.basis]
  simp only [finiteBit,decide_not]

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  exact CodexAffineGadget.clearProgram_eq _ _ _ _ _ _ (ports_nodup L hw hn)
    ((lengths L hw).1.trans (lengths L hw).2.symm)
    (by rw [(lengths L hw).1]; decide) s m hz hzero

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite=base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite∉L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [←v.x]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit,this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [←v.y]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit,this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit,Ne.symm (fin_ne_generic L hn),v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [←v.clean]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit,this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q=writeBit base L.point.finite _ q
    by_cases hqf : q=L.point.finite
    · subst hqf; simp [writeBit,hfs,v.x]
    · simp [writeBit,hqf,v.rest q hq]

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=finiteBit X.val) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz]
    simp [writeBit,v.x,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

include hw in
theorem clrF_support_old : wires (clrF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [FiniteFlagInterval.old_clrF_support L hw]
  intro q hq
  have h := CodexAffineGadget.program_support (a L) (b L) L.point.finite (rest L) (work L) literal
    ((lengths L hw).1.trans (lengths L hw).2.symm) hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  have inputs := inputs_mem L hw
  rcases h with rfl | rfl | rfl | h | h
  · tauto
  · tauto
  · tauto
  · exact Or.inr (Or.inl (inputs.2.2 q h))
  · apply Or.inr; apply Or.inr
    have sub : L.dialogPool.take 247 ⊆ L.dialogPool.take 255 := by
      have e : L.dialogPool.take 247=(L.dialogPool.take 255).take 247 := by rw [List.take_take]; rfl
      rw [e]; exact List.take_subset _ _
    exact sub (work_subset L h)

include hw in
theorem clearF_support_old : wires (clearF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) :=
  (CodexAffineGadget.clearProgram_support (a L) (b L) L.point.finite (rest L) (work L) literal).trans
    (clrF_support_old L hw)

include hw in
theorem counts :
    toffoliCount (clrF L)=246 ∧ measurementCount (clrF L)=246 ∧
    toffoliCount (clearF L)=245 ∧ measurementCount (clearF L)=246 := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have p := CodexAffineGadget.program_counts (a L) (b L) L.point.finite (rest L) (work L) literal hl
  have c := CodexAffineGadget.clearProgram_counts (a L) (b L) L.point.finite (rest L) (work L) literal hl
  simpa only [(lengths L hw).1,clrF,clearF] using And.intro p.1 (And.intro p.2 c)

include hw hn in
theorem physical : GatePhysical (clrF L) ∧ GatePhysical (clearF L) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  exact ⟨CodexAffineGadget.program_physical _ _ _ _ _ _ hl (ports_nodup L hw hn),
    CodexAffineGadget.clearProgram_physical _ _ _ _ _ _ hl (ports_nodup L hw hn)⟩

abbrev zrep := FiniteFlagInterval.zrep
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L

theorem sentinel_finiteBit : finiteBit FiniteFlagInterval.sentinel=false := by
  have eq : FiniteFlagInterval.sentinel=p-1 := by norm_num [FiniteFlagInterval.sentinel,p]
  simp [finiteBit,eq,CodexAffineMath.sentinel_matches]

include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : finiteBit X.val = fin) (h2 : finiteBit X'.val = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
        L.point.finite ^^ finiteBit X'.val) = base := by
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
    have z1 := FiniteFlagInterval.zrep_step L hw hn 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (FiniteFlagInterval.sentinel : Fp) 0 cx cy base' FiniteFlagInterval.sentinel_ne_zero) hfin
      (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit) (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit)
    have z2 := FiniteFlagInterval.zrep_step L hw hn (FiniteFlagInterval.sentinel : Fp) 0 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : finiteBit x.val = true := decide_eq_true (CodexAffineMath.curve_x_not_matches hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : finiteBit (genericX x y cx cy).val = true :=
        decide_eq_true (CodexAffineMath.curve_x_not_matches (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := FiniteFlagInterval.zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))


omit hw hn

attribute [local irreducible] toffoliCount measurementCount gateSlots ReflectionE1TickGapLow48.generic

include hw in
theorem gen_support_subset (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) := by
  intro q used
  have hz : q∈wires (zrep L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => FiniteFlagInterval.zrep_support_old L hw h
  have hc : q∈wires (clrF L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clrF_support_old L hw h
  have he : q∈wires (clearF L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clearF_support_old L hw h
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,
    generic,wires_append,Finset.mem_union] at used ⊢
  tauto

include hw hn in
theorem gen_sites (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (ReflectionE1TickGapLow48.gen_sites L hw hn cx cy)

include hw in
theorem gen_counts (cx cy : Fp) :
    toffoliCount (gen L cx cy)+2=toffoliCount (FiniteFlagInterval.gen L cx cy) ∧
    measurementCount (gen L cx cy)+2=measurementCount (FiniteFlagInterval.gen L cx cy) := by
  have n := counts L hw
  have o := FiniteFlagInterval.clrF_counts L hw
  have e := FiniteFlagInterval.clearF_counts L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,toffoliCount_append,measurementCount_append,n.1,n.2.1,n.2.2.1,n.2.2.2,
    o.1,o.2,e.1,e.2]
  omega

include hw in
theorem gen_slots (cx cy : Fp) : gateSlots (gen L cx cy)≤gateSlots (FiniteFlagInterval.gen L cx cy) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have n := CodexAffineGadget.program_slots (a L) (b L) L.point.finite (rest L) (work L) literal hl
  have e := CodexAffineGadget.clearProgram_slots (a L) (b L) L.point.finite (rest L) (work L) literal hl
  rw [(lengths L hw).1] at n e
  change gateSlots (clrF L)≤9*246+6 at n
  change gateSlots (clearF L)≤9*246+6 at e
  have o := FiniteFlagInterval.clrF_slots_exact L hw
  have c := FiniteFlagInterval.clearF_slots L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,gateSlots_append]
  omega

include hw hn in
theorem gen_physical (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := FiniteFlagInterval.zrep_physical L hn
  have c := (physical L hw hn).1
  have e := (physical L hw hn).2
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic,zrep] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

include hw in
theorem wrapper_counts (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+2=
      toffoliCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+2=
      measurementCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy))≤
      gateSlots (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) := by
  have h := gen_counts L hw cx cy
  have s := gen_slots L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 := by
  have h := FiniteFlagInterval.wrapper_support_mono layout C cy _ _
    (gen_support_subset layout layout_widths cx cy)
  exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
    (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151042,1498863,1587,50236557⟩

theorem program_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ control R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc control _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151042 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤2151042
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498863 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤1498863
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1587 := by
  cases C with
  | zero => change qubits []≤1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50236557 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.2
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=23581 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤50236557
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498863
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50236557
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.CodexAffineProbe
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityMath =====
section
namespace ECDSAAdd.Entrant.CodexYParityMath
open Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def highX (v : Nat) : Prop :=
  v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607

instance : DecidablePred highX := fun v => inferInstanceAs (Decidable
  (v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607))

def yParity (v : Nat) : Bool :=
  decide (v / 6901746346790563787434755862277025452451108972170386555162524223799296 % 2 = 1) ^^
  decide (v / 441711766194596082395824375185729628956870974218904739530401550323154944 % 2 = 1) ^^
  decide (v / 883423532389192164791648750371459257913741948437809479060803100646309888 % 2 = 1) ^^
  decide (v / 1766847064778384329583297500742918515827483896875618958121606201292619776 % 2 = 1) ^^
  decide (v / 113078212145816597093331040047546785012958969400039613319782796882727665664 % 2 = 1) ^^
  decide (v / 226156424291633194186662080095093570025917938800079226639565593765455331328 % 2 = 1) ^^
  decide (v / 452312848583266388373324160190187140051835877600158453279131187530910662656 % 2 = 1) ^^
  decide (v / 3618502788666131106986593281521497120414687020801267626233049500247285301248 % 2 = 1)

def matchesXY (x y : Nat) : Prop := highX x ∧ yParity y = false
instance (x y : Nat) : Decidable (matchesXY x y) := inferInstanceAs (Decidable (highX x ∧ yParity y = false))

theorem highX_range (v : Nat) (hv : v < p) (h : highX v) : p-47 ≤ v := by
  unfold highX at h
  norm_num [p] at hv ⊢
  omega

theorem sentinel_matches : matchesXY (p-1) 0 := by
  norm_num [matchesXY,highX,yParity,p]

private theorem nonsquare {a y : Fp} (power : a^((p-1)/2) = -1) (hs : y^2 = a) : False := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [←hs,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1=2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,hs,power] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

private theorem powerTransport (q a : Nat) (hq : q=p)
    (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
    ((a : Fp)^3+7)^((p-1)/2) = -1 := by
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  subst q
  exact h

private theorem squareTransport (q a r : Nat) (hq : q=p)
    (h : (r : ZMod q)^2 = (a : ZMod q)^3+7) :
    (r : Fp)^2 = (a : Fp)^3+7 := by
  subst q
  exact h

private theorem case_1 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671662 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_2 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671661 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671661 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_3 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671660 : Fp)^3+7) : yParity y.val = true := by
  have hr : (6603225675942137755722016048183769717410321709583529039474051610042430502525 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671660 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_4 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671659 : Fp)^3+7) : yParity y.val = true := by
  have hr : (59494462493979449647570233702496999513658646306271329894531992659739671393069 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671659 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_5 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671658 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671658 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_6 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671657 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671657 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_7 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671656 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_8 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671655 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_9 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671654 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_10 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671653 : Fp)^3+7) : yParity y.val = true := by
  have hr : (32675455276886538377135961527970747392999635122131544003589039477106874644692 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671653 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_11 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671652 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671652 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_12 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671651 : Fp)^3+7) : yParity y.val = true := by
  have hr : (26128689524504706065261118141317656197887299188579002162273527811606361449708 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671651 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_13 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671650 : Fp)^3+7) : yParity y.val = true := by
  have hr : (8577303908373580249506288492821825305199069524882698424576740044335877264616 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671650 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_14 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671649 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671649 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_15 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671648 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671648 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_16 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671647 : Fp)^3+7) : yParity y.val = true := by
  have hr : (91140719503136456702788776376224035068647810528229755089092598492509977513391 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671647 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_17 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671646 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671646 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_18 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671645 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671645 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_19 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671644 : Fp)^3+7) : yParity y.val = true := by
  have hr : (39884473096376270427702265980090836962804851088800575884979558070656540211742 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671644 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_20 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671643 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671643 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_21 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671642 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671642 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_22 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671641 : Fp)^3+7) : yParity y.val = true := by
  have hr : (87858050732041572112946130011090019437744585579749573053061107584625869568789 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671641 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_23 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671640 : Fp)^3+7) : yParity y.val = true := by
  have hr : (108804142492889174614636371636043929694359971927800610566698906308390880838775 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671640 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_24 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671639 : Fp)^3+7) : yParity y.val = true := by
  have hr : (90251269264737004142706139481528124213741093942080018241141466145201744297488 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671639 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_25 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671638 : Fp)^3+7) : yParity y.val = true := by
  have hr : (75235462138975110463823503735425296584550141080759035749156047496719874561987 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671638 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_26 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671637 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671637 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_27 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671636 : Fp)^3+7) : yParity y.val = true := by
  have hr : (86939888355575964094991750730646468908583063016749246259798665632714130501197 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671636 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_28 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671635 : Fp)^3+7) : yParity y.val = true := by
  have hr : (4182962361524284598535907236655905568231458553838165214763798974835028006434 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671635 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_29 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671634 : Fp)^3+7) : yParity y.val = true := by
  have hr : (68955841494607169053734295970461238553869482894404290786540257300019047034624 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671634 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_30 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671633 : Fp)^3+7) : yParity y.val = true := by
  have hr : (49733659202714845321509626322873875871991168724474382738121548382114922697663 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671633 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_31 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671632 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671632 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_32 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671631 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671631 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_33 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671630 : Fp)^3+7) : yParity y.val = true := by
  have hr : (44691740129539857302436916955866976963397033623780589459590642317128159632006 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671630 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_34 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671629 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671629 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_35 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671628 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671628 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_36 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671627 : Fp)^3+7) : yParity y.val = true := by
  have hr : (51193769181865963694859153139841532078256707687335846879742476169529437790917 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671627 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_37 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671626 : Fp)^3+7) : yParity y.val = true := by
  have hr : (103618749943476312868418606276677894873806957446321936724134933650386344711784 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671626 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_38 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671625 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671625 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_39 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671624 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671624 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_40 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671623 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671623 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_41 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671622 : Fp)^3+7) : yParity y.val = true := by
  have hr : (66850597368902350158169512472851730375964505860741535628662529042753517520652 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671622 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_42 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671621 : Fp)^3+7) : yParity y.val = true := by
  have hr : (70401031564568261752508033145049036971610607287643400116337276464925705083252 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671621 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_43 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671620 : Fp)^3+7) : yParity y.val = true := by
  have hr : (16630661555480012533216961328463789703838228518257063889232934184924812474445 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671620 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_44 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671619 : Fp)^3+7) : yParity y.val = true := by
  have hr : (107334166703719341558589207297916674948985469142494621554787815725265730778893 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671619 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_45 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671618 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671618 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_46 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671617 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671617 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_47 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671616 : Fp)^3+7) : yParity y.val = true := by
  have hr : (112234481090334865465835242450756667684869773413855542198653146390767513213554 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671616 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

theorem highX_curve_parity {x y : Fp} (hc : curve.toAffine.Nonsingular x y)
    (hx : highX x.val) : yParity y.val = true := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have hv := ZMod.val_lt x
  have lo := highX_range x.val hv hx
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using equation
  have xv : (x.val : Fp) = x := ZMod.natCast_zmod_val x
  rw [←xv] at square
  have hcases : x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671662 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671661 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671660 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671659 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671658 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671657 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671656 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671653 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671652 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671651 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671650 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671649 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671648 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671647 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671646 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671645 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671644 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671643 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671642 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671641 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671640 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671639 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671638 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671637 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671636 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671635 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671634 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671633 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671632 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671631 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671630 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671629 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671628 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671627 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671626 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671625 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671624 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671623 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671622 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671621 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671620 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671619 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671618 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671617 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671616 := by
    norm_num [p] at lo hv
    omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47
  · rw [h1] at square; exact case_1 y square
  · rw [h2] at square; exact case_2 y square
  · rw [h3] at square; exact case_3 y square
  · rw [h4] at square; exact case_4 y square
  · rw [h5] at square; exact case_5 y square
  · rw [h6] at square; exact case_6 y square
  · rw [h7] at square; exact case_7 y square
  · rw [h8] at square; exact case_8 y square
  · rw [h9] at square; exact case_9 y square
  · rw [h10] at square; exact case_10 y square
  · rw [h11] at square; exact case_11 y square
  · rw [h12] at square; exact case_12 y square
  · rw [h13] at square; exact case_13 y square
  · rw [h14] at square; exact case_14 y square
  · rw [h15] at square; exact case_15 y square
  · rw [h16] at square; exact case_16 y square
  · rw [h17] at square; exact case_17 y square
  · rw [h18] at square; exact case_18 y square
  · rw [h19] at square; exact case_19 y square
  · rw [h20] at square; exact case_20 y square
  · rw [h21] at square; exact case_21 y square
  · rw [h22] at square; exact case_22 y square
  · rw [h23] at square; exact case_23 y square
  · rw [h24] at square; exact case_24 y square
  · rw [h25] at square; exact case_25 y square
  · rw [h26] at square; exact case_26 y square
  · rw [h27] at square; exact case_27 y square
  · rw [h28] at square; exact case_28 y square
  · rw [h29] at square; exact case_29 y square
  · rw [h30] at square; exact case_30 y square
  · rw [h31] at square; exact case_31 y square
  · rw [h32] at square; exact case_32 y square
  · rw [h33] at square; exact case_33 y square
  · rw [h34] at square; exact case_34 y square
  · rw [h35] at square; exact case_35 y square
  · rw [h36] at square; exact case_36 y square
  · rw [h37] at square; exact case_37 y square
  · rw [h38] at square; exact case_38 y square
  · rw [h39] at square; exact case_39 y square
  · rw [h40] at square; exact case_40 y square
  · rw [h41] at square; exact case_41 y square
  · rw [h42] at square; exact case_42 y square
  · rw [h43] at square; exact case_43 y square
  · rw [h44] at square; exact case_44 y square
  · rw [h45] at square; exact case_45 y square
  · rw [h46] at square; exact case_46 y square
  · rw [h47] at square; exact case_47 y square

theorem curve_not_matches {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ matchesXY x.val y.val := by
  rintro ⟨hx,hy⟩
  have yes := highX_curve_parity hc hx
  rw [yes] at hy
  contradiction

end ECDSAAdd.Entrant.CodexYParityMath
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityGadget =====
section
/-
Research helper: generic affine parity view for the 246-condition finite probe.
Standalone real-source compilation passed; full integrated certificate remains pending.
Import is for a minimal helper tree containing the official-validated MeasuredZeroClear module;
when integrated into the consolidated Main, omit this import and retain the namespace.
-/

namespace ECDSAAdd.Entrant.CodexYParityGadget
open Arithmetic RecordedQuantum Challenge Baselines

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def parity (xs : List Wire) (s : BasisState) : Bool :=
  xs.foldr (fun x t => s x ^^ t) false

def fan (xs : List Wire) (b : Wire) : Program := xs.map (fun x => .CX x b)
def view (xs : List Wire) (b : Wire) : Program := fan xs b ++ [.X b]
def restore (xs : List Wire) (b : Wire) : Program := [.X b] ++ fan xs.reverse b
def core (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ equalConstant b f (zeroPorts r work) k
def program (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view xs b ++ core b f r work k ++ restore xs b
def clearCore (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ MeasuredZeroClear.equalClear b f (zeroPorts r work) k
def clearProgram (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view xs b ++ clearCore b f r work k ++ restore xs b

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append, run_take]

theorem ports_length (r work : List Wire) (hl : r.length = work.length) :
    (zeroPorts r work).length = r.length := by
  have h := congrArg List.length (zeroPorts_maps r work hl).1
  simpa using h

theorem parity_congr (xs : List Wire) (s t : BasisState)
    (h : ∀ q ∈ xs, s q = t q) : parity xs s = parity xs t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (s x ^^ parity xs s) = (t x ^^ parity xs t)
    rw [h x (by simp), ih (fun q hq => h q (by simp [hq]))]

theorem parity_append (xs ys : List Wire) (s : BasisState) :
    parity (xs ++ ys) s = (parity xs s ^^ parity ys s) := by
  induction xs with
  | nil => simp [parity]
  | cons x xs ih =>
    change (s x ^^ parity (xs ++ ys) s) = ((s x ^^ parity xs s) ^^ parity ys s)
    rw [ih, Bool.xor_assoc]

theorem parity_reverse (xs : List Wire) (s : BasisState) :
    parity xs.reverse s = parity xs s := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, parity_append, ih]
    change (parity xs s ^^ parity [x] s) = (s x ^^ parity xs s)
    simp [parity, Bool.xor_comm]

theorem fan_counts (xs : List Wire) (b : Wire) :
    toffoliCount (fan xs b) = 0 ∧ measurementCount (fan xs b) = 0 := by
  induction xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih => simpa only [fan, List.map_cons, toffoliCount, measurementCount] using ih

theorem fan_slots (xs : List Wire) (b : Wire) : gateSlots (fan xs b) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa [fan, gateSlots, instructionSlots, Nat.add_comm] using congrArg Nat.succ ih

theorem fan_support (xs : List Wire) (b : Wire) :
    wires (fan xs b) ⊆ (b :: xs).toFinset := by
  induction xs with
  | nil => simp [fan, wires]
  | cons x xs ih =>
    intro q hq
    simp only [fan, List.map_cons, wires, Instr.wires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with (rfl | rfl) | hq
    · simp
    · simp
    · have h := ih hq
      simp only [List.mem_toFinset, List.mem_cons] at h ⊢
      tauto

theorem fan_physical (xs : List Wire) (b : Wire) (hb : b ∉ xs) :
    GatePhysical (fan xs b) := by
  intro i hi
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
  have hqb : q ≠ b := fun e => hb (e ▸ hq)
  simpa [PhysicalInstr, ProperGate] using hqb

-- This induction is the same affine fan semantics already used in TerminalGraph.
theorem fan_run (xs : List Wire) (b : Wire) (hb : b ∉ xs)
    (s : State) (m : List Bool) :
    run (fan xs b) m s =
      ⟨s.phase, writeBit s.basis b (s.basis b ^^ parity xs s.basis)⟩ := by
  induction xs generalizing s with
  | nil =>
    simp only [fan, List.map_nil, run, parity, List.foldr_nil, Bool.xor_false]
    cases s with
    | mk phase basis =>
      apply congrArg (State.mk phase)
      funext q
      by_cases hq : q = b <;> simp [writeBit, hq]
  | cons x xs ih =>
    have tail : b ∉ xs := fun h => hb (by simp [h])
    let t : State := ⟨s.phase, writeBit s.basis b (s.basis b ^^ s.basis x)⟩
    have same : parity xs t.basis = parity xs s.basis := parity_congr _ _ _ (by
      intro q hq
      have hqb : q ≠ b := fun e => tail (e ▸ hq)
      simp [t, writeBit, hqb])
    simp only [fan, List.map_cons, run]
    change run (fan xs b) m t = _
    rw [ih tail t, same]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q = b
    · subst q
      simp [t, writeBit, parity, Bool.xor_assoc]
    · simp [t, writeBit, hq]

theorem view_counts (xs : List Wire) (b : Wire) :
    toffoliCount (view xs b) = 0 ∧ measurementCount (view xs b) = 0 := by
  simp [view, toffoliCount_append, measurementCount_append, fan_counts,
    toffoliCount, measurementCount]

theorem restore_counts (xs : List Wire) (b : Wire) :
    toffoliCount (restore xs b) = 0 ∧ measurementCount (restore xs b) = 0 := by
  simp [restore, toffoliCount_append, measurementCount_append, fan_counts,
    toffoliCount, measurementCount]

theorem view_support (xs : List Wire) (b : Wire) :
    wires (view xs b) ⊆ (b :: xs).toFinset := by
  intro q hq
  simp only [view, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact fan_support xs b hq
  · have hqb : q = b := by simpa [wires, Instr.wires] using hq
    simp [hqb]

theorem restore_support (xs : List Wire) (b : Wire) :
    wires (restore xs b) ⊆ (b :: xs).toFinset := by
  intro q hq
  simp only [restore, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · have hqb : q = b := by simpa [wires, Instr.wires] using hq
    simp [hqb]
  · simpa only [List.mem_toFinset, List.mem_cons, List.mem_reverse] using
      fan_support xs.reverse b hq

theorem ports_nodup (xs : List Wire) (b f : Wire) (r work : List Wire)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    (b :: f :: (zeroPorts r work).flatMap ZeroBit.wires).Nodup := by
  have keep : (b :: f :: (r ++ work)).Nodup := by
    exact List.Nodup.sublist
      (List.Sublist.cons₂ b (List.Sublist.cons₂ f (List.sublist_append_right xs (r ++ work)))) hn
  exact (((zeroPorts_perm r work hl).cons f).cons b).nodup_iff.mpr keep

theorem view_run (xs : List Wire) (b : Wire) (hb : b ∉ xs)
    (s : State) (m : List Bool) :
    run (view xs b) m s =
      ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))⟩ := by
  rw [view, run_concat, (fan_counts xs b).2, List.drop_zero, fan_run xs b hb]
  simp [run, writeBit]

theorem restore_update (xs : List Wire) (b f : Wire)
    (hb : b ∉ xs) (hf : f ∉ xs) (hbf : b ≠ f)
    (s : State) (m : List Bool) (z : Bool) :
    run (restore xs b) m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z⟩ =
      ⟨s.phase, writeBit s.basis f z⟩ := by
  let t : State := ⟨s.phase, writeBit
    (writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z)
    b (s.basis b ^^ parity xs s.basis)⟩
  have first : run [Instr.X b] m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z⟩ = t := by
    simp [run, t, writeBit, hbf]
  have same : parity xs t.basis = parity xs s.basis := parity_congr _ _ _ (by
    intro q hq
    simp [t, writeBit, show q ≠ b from fun e => hb (e ▸ hq),
      show q ≠ f from fun e => hf (e ▸ hq)])
  rw [restore, run_concat, show measurementCount [Instr.X b] = 0 from rfl,
    List.drop_zero, first, fan_run xs.reverse b (by simpa using hb), parity_reverse, same]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = b
  · subst q
    cases hp : parity xs s.basis <;> cases hs : s.basis b <;>
      simp [t, writeBit, hbf, hp, hs]
  · by_cases hqf : q = f
    · subst q
      simp [t, writeBit, hbf.symm]
    · simp [t, writeBit, hq, hqf]

theorem program_run (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) (hl : r.length = work.length)
    (hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0) :
    run (program xs b f r work k) m s =
      ⟨s.phase, writeBit s.basis f
        (s.basis f ^^ !((!(s.basis b ^^ parity xs s.basis)) && decide (regValue r s.basis = k)))⟩ := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hbf : b ≠ f := sep.1.1
  have hbx : b ∉ xs := sep.1.2.1
  have hbr : b ∉ r := sep.1.2.2.1
  have hbw : b ∉ work := sep.1.2.2.2
  have hfx : f ∉ xs := sep.2.1.1
  have hfr : f ∉ r := sep.2.1.2.1
  have hfw : f ∉ work := sep.2.1.2.2
  let u : State := ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))⟩
  let v : State := ⟨s.phase, writeBit u.basis f (!s.basis f)⟩
  have hu : run (view xs b) m s = u := view_run xs b hbx s m
  have uv : run [.X f] m u = v := by simp [run, u, v, writeBit, hbf.symm]
  have hports := zeroPorts_maps r work hl
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← hports.2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    simpa [v, u, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have hr : regValue r v.basis = regValue r s.basis := by
    apply regValue_congr
    intro q hq
    simp [v, u, writeBit, show q ≠ b from fun e => hbr (e ▸ hq),
      show q ≠ f from fun e => hfr (e ▸ hq)]
  have eq := equalConstant_correct b f (zeroPorts r work) k (ports_nodup xs b f r work hl hn)
    (by simpa only [ports_length r work hl] using hk) v m clean
  rw [hports.1, hr] at eq
  have vb : v.basis b = !(s.basis b ^^ parity xs s.basis) := by simp [v, u, writeBit, hbf]
  have vf : v.basis f = !s.basis f := by simp [v, writeBit]
  rw [vb, vf] at eq
  have folded : ((!s.basis f) ^^
      (!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k))) =
      (s.basis f ^^ !(!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k))) := by
    cases s.basis f <;> cases (!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k)) <;> rfl
  rw [folded] at eq
  have shape : run (program xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, hu, uv]
  rw [shape, eq]
  simpa only [v, u, writeBit, Function.update_idem] using
    restore_update xs b f hbx hfx hbf s (m.drop (zeroPorts r work).length)
      (s.basis f ^^ !(!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k)))

theorem program_counts (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (program xs b f r work k) = r.length ∧
    measurementCount (program xs b f r work k) = r.length := by
  simp [program, core, toffoliCount_append, measurementCount_append,
    (view_counts xs b).1, (view_counts xs b).2,
    (restore_counts xs b).1, (restore_counts xs b).2,
    equalConstant_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem clearProgram_counts (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (clearProgram xs b f r work k) = r.length - 1 ∧
    measurementCount (clearProgram xs b f r work k) = r.length := by
  simp [clearProgram, clearCore, toffoliCount_append, measurementCount_append,
    (view_counts xs b).1, (view_counts xs b).2,
    (restore_counts xs b).1, (restore_counts xs b).2,
    MeasuredZeroClear.equal_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem program_support (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    wires (program xs b f r work k) ⊆ (b :: f :: (xs ++ (r ++ work))).toFinset := by
  have hsmall (q : Wire) (hq : q ∈ (b :: xs).toFinset) :
      q ∈ (b :: f :: (xs ++ (r ++ work))).toFinset := by
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq ⊢
    tauto
  intro q hq
  simp only [program, core, wires_append, Finset.mem_union] at hq
  rcases hq with (hq | (hq | hq)) | hq
  · exact hsmall q (view_support xs b hq)
  · have hfq : q = f := by simpa [wires, Instr.wires] using hq
    simp [hfq]
  · have hp : q ∈ (zeroPorts r work).flatMap ZeroBit.wires ↔ q ∈ r ++ work :=
      (zeroPorts_perm r work hl).mem_iff
    simp only [equalConstant_wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, List.mem_toFinset, List.mem_cons, List.mem_append, hp] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  · exact hsmall q (restore_support xs b hq)

theorem clearProgram_support (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) :
    wires (clearProgram xs b f r work k) ⊆ wires (program xs b f r work k) := by
  simp only [clearProgram, clearCore, program, core, wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (MeasuredZeroClear.equal_support b f (zeroPorts r work) k)))
    (Finset.Subset.refl _)

theorem clearProgram_run_eq (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup)
    (s : State) (m : List Bool) (hz : regValue work s.basis = 0)
    (hzero : (run (program xs b f r work k) m s).basis f = false) :
    run (clearProgram xs b f r work k) m s = run (program xs b f r work k) m s := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hbf : b ≠ f := sep.1.1
  have hbx : b ∉ xs := sep.1.2.1
  have hbw : b ∉ work := sep.1.2.2.2
  have hfx : f ∉ xs := sep.2.1.1
  have hfw : f ∉ work := sep.2.1.2.2
  let v := run [Instr.X f] m (run (view xs b) m s)
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← (zeroPorts_maps r work hl).2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    change (run [Instr.X f] m (run (view xs b) m s)).basis p.work = false
    rw [view_run xs b hbx]
    simpa [run, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have oldShape : run (program xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have newShape : run (clearProgram xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) m v) := by
    simp only [clearProgram, clearCore, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (MeasuredZeroClear.equal_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have away : f ∉ wires (restore xs b) := by
    intro hf
    have h := restore_support xs b hf
    simp only [List.mem_toFinset, List.mem_cons] at h
    exact h.elim (fun e => hbf e.symm) hfx
  have keep := run_preserves_outside (restore xs b) (m.drop (zeroPorts r work).length)
    (run (equalConstant b f (zeroPorts r work) k) m v) f away
  have zero : (run (equalConstant b f (zeroPorts r work) k) m v).basis f = false := by
    rw [oldShape] at hzero
    exact keep.symm.trans hzero
  have eq := MeasuredZeroClear.equal_run_eq b f (zeroPorts r work) k
    (ports_nodup xs b f r work hl hn) v m clean zero
  rw [oldShape, newShape, eq]

theorem clearProgram_eq (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) (hl : r.length = work.length)
    (_hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0)
    (hzero : (run (program xs b f r work k) m s).basis f = false) :
    run (clearProgram xs b f r work k) m s = run (program xs b f r work k) m s :=
  clearProgram_run_eq xs b f r work k hl hn s m hz hzero

theorem program_physical (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    GatePhysical (program xs b f r work k) := by
  have hbx : b ∉ xs := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  have hv : GatePhysical (view xs b) := by
    rw [view, gatePhysical_append]
    exact ⟨fan_physical xs b hbx, by simp [GatePhysical, PhysicalInstr, ProperGate]⟩
  have hr : GatePhysical (restore xs b) := by
    rw [restore, gatePhysical_append]
    exact ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
      fan_physical xs.reverse b (by simpa using hbx)⟩
  simp only [program, core, gatePhysical_append]
  exact ⟨⟨hv, ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
    equalConstant_physical b f (zeroPorts r work) k (ports_nodup xs b f r work hl hn)⟩⟩, hr⟩

theorem clearProgram_physical (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    GatePhysical (clearProgram xs b f r work k) := by
  have old := program_physical xs b f r work k hl hn
  simp only [program, core, gatePhysical_append] at old
  simp only [clearProgram, clearCore, gatePhysical_append]
  exact ⟨⟨old.1.1, ⟨old.1.2.1,
    MeasuredZeroClear.equal_physical b f (zeroPorts r work) k
      (ports_nodup xs b f r work hl hn)⟩⟩, old.2⟩

theorem program_slots (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (program xs b f r work k) ≤ 9 * r.length + 2 * xs.length + 4 := by
  have h := equalConstant_gateSlots_le b f (zeroPorts r work) k
  rw [ports_length r work hl] at h
  simp only [program, core, view, restore, gateSlots_append, fan_slots, List.length_reverse]
  change (xs.length + 1) + (1 + gateSlots (equalConstant b f (zeroPorts r work) k)) +
    (1 + xs.length) ≤ _
  omega

theorem clearProgram_slots_le (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) :
    gateSlots (clearProgram xs b f r work k) ≤ gateSlots (program xs b f r work k) := by
  have h : gateSlots (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) ≤
      gateSlots (equalConstant b f (zeroPorts r work) k) := by
    by_cases he : zeroPorts r work = []
    · rw [he]
      exact Nat.le_refl _
    · have h := MeasuredZeroClear.equal_slots b f (zeroPorts r work) k he
      omega
  simp only [clearProgram, clearCore, program, core, gateSlots_append]
  omega

theorem clearProgram_slots (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (clearProgram xs b f r work k) ≤ 9 * r.length + 2 * xs.length + 4 :=
  (clearProgram_slots_le xs b f r work k).trans (program_slots xs b f r work k hl)

end ECDSAAdd.Entrant.CodexYParityGadget
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityBridge =====
section
namespace ECDSAAdd.Entrant.CodexYParityProbe
open Arithmetic ControlledPointLayout
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

def b (L : ControlledPointLayout) : Wire := L.point.y.getD 232 0
def xs (L : ControlledPointLayout) : List Wire :=
  [238,239,240,246,247,248,251].map (fun i => L.point.y.getD i 0)
def rest (L : ControlledPointLayout) : List Wire :=
  (L.point.x.drop 10).take 22 ++ L.point.x.drop 33
def work (L : ControlledPointLayout) : List Wire := L.dialogPool.take 245
def literal : Nat := 2^245-1

private theorem drop_sublist_drop (r : List Wire) (a b : Nat) (hab : a ≤ b) :
    (r.drop b).Sublist (r.drop a) := by
  have e : r.drop b = (r.drop a).drop (b-a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e]
  exact List.drop_sublist _ _

private theorem getD_range (r : List Wire) (n : Nat) (hn : r.length=n) :
    (List.range n).map (fun i => r.getD i 0)=r := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem _ _ hj

theorem rest_sublist (L : ControlledPointLayout) : (rest L).Sublist L.point.x := by
  have h : (L.point.x.drop 33).Sublist ((L.point.x.drop 10).drop 22) := by
    rw [List.drop_drop]
    exact drop_sublist_drop _ _ _ (by omega)
  have h' := List.Sublist.append (List.Sublist.refl ((L.point.x.drop 10).take 22)) h
  rw [List.take_append_drop] at h'
  exact h'.trans (List.drop_sublist _ _)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
private theorem point_x_length : L.point.x.length=256 := hw.inputX
include hw in
private theorem point_y_length : L.point.y.length=256 := hw.inputY

include hw in
theorem y_sublist : (b L :: xs L).Sublist L.point.y := by
  have h : ([232,238,239,240,246,247,248,251] : List Nat).Sublist (List.range 256) := by decide
  have hm := h.map (fun i => L.point.y.getD i 0)
  rw [getD_range L.point.y 256 (point_y_length L hw)] at hm
  simpa only [b,xs,List.map_cons] using hm

include hw in
theorem lengths : (rest L).length=245 ∧ (work L).length=245 := by
  simp [rest,work,point_x_length L hw,L.dialogPool_length hw]

theorem work_subset : work L ⊆ L.dialogPool.take 255 := by
  have h : work L=(L.dialogPool.take 255).take 245 := by
    simp only [work,List.take_take]; rfl
  rw [h]
  exact List.take_subset _ _

include hw hn in
theorem ports_nodup :
    (b L :: L.point.finite :: (xs L ++ (rest L ++ work L))).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hy := (y_sublist L hw).count_le q
  have hx := (rest_sublist L).count_le q
  have hp := (List.take_sublist 245 L.dialogPool).count_le q
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
    List.count_nil,List.cons_append,work] at h hy hp ⊢
  omega

include hw in
theorem inputs_mem : b L∈L.point.y ∧ xs L⊆L.point.y ∧ rest L⊆L.point.x := by
  have hy := (y_sublist L hw).subset
  refine ⟨hy (by simp),?_,(rest_sublist L).subset⟩
  intro q hq
  exact hy (List.mem_cons_of_mem _ hq)

include hw in
theorem rest_value (s : BasisState) :
    regValue (rest L) s = regValue L.point.x s / 1024 % 4194304 +
      4194304 * (regValue L.point.x s / 8589934592) := by
  have lo : regValue ((L.point.x.drop 10).take 22) s =
      regValue L.point.x s / 2^10 % 2^22 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by simp [point_x_length L hw]),
      CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [point_x_length L hw]; omega)]
  have hi := CuccaroStreamedSquareWideLayout.regValue_drop_div L.point.x 33
    (by rw [point_x_length L hw]; omega) s
  simp only [rest,regValue_append,lo,hi,List.length_take,List.length_drop,point_x_length L hw]
  norm_num

private theorem packed_eq_highX (v : Nat) :
    (v/1024%4194304 + 4194304*(v/8589934592)=literal) ↔ CodexYParityMath.highX v := by
  have h := Nat.mod_lt (v/1024) (by decide : 0<4194304)
  norm_num [literal,CodexYParityMath.highX]
  omega

private theorem bit_value (r : List Wire) (i : Nat) (s : BasisState) (hi : i<r.length) :
    s (r.getD i 0) = decide (regValue r s / 2^i % 2 = 1) := by
  rw [←regValue_bit r i 0 s hi]
  cases s (r.getD i 0) <;> rfl

include hw in
theorem parity_value (s : BasisState) :
    (s (b L) ^^ CodexYParityGadget.parity (xs L) s) =
      CodexYParityMath.yParity (regValue L.point.y s) := by
  have h232 := bit_value L.point.y 232 s (by rw [point_y_length L hw]; decide)
  have h238 := bit_value L.point.y 238 s (by rw [point_y_length L hw]; decide)
  have h239 := bit_value L.point.y 239 s (by rw [point_y_length L hw]; decide)
  have h240 := bit_value L.point.y 240 s (by rw [point_y_length L hw]; decide)
  have h246 := bit_value L.point.y 246 s (by rw [point_y_length L hw]; decide)
  have h247 := bit_value L.point.y 247 s (by rw [point_y_length L hw]; decide)
  have h248 := bit_value L.point.y 248 s (by rw [point_y_length L hw]; decide)
  have h251 := bit_value L.point.y 251 s (by rw [point_y_length L hw]; decide)
  simp only [b,xs,CodexYParityGadget.parity,List.map_cons,List.map_nil,List.foldr_cons,
    List.foldr_nil,Bool.xor_false,h232,h238,h239,h240,h246,h247,h248,h251,
    CodexYParityMath.yParity,Bool.xor_assoc]
  norm_num

include hw in
theorem hit (s : BasisState) :
    (!(s (b L) ^^ CodexYParityGadget.parity (xs L) s) &&
      decide (regValue (rest L) s=literal)) =
      decide (CodexYParityMath.matchesXY (regValue L.point.x s) (regValue L.point.y s)) := by
  rw [parity_value L hw s,rest_value L hw s]
  have he : decide (regValue L.point.x s/1024%4194304 +
      4194304*(regValue L.point.x s/8589934592)=literal) =
      decide (CodexYParityMath.highX (regValue L.point.x s)) := by
    simp only [packed_eq_highX]
  rw [he]
  cases h : CodexYParityMath.yParity (regValue L.point.y s) <;>
    simp [CodexYParityMath.matchesXY,h]

end ECDSAAdd.Entrant.CodexYParityProbe
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParitySupport =====
section
/-
Research-only integration bridge. Not yet compiled.
The two imports are conveniences for a temporary minimal test tree; strip them when
inserting these declarations after the new gadget in the consolidated Main.
-/

namespace ECDSAAdd.Entrant.CodexYParitySupport
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  ReflectionE1TickGapLow48.generic

/-- The new y sources are the only support beyond the original x-only finite probe. -/
theorem probe_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (xs : List Wire) (b : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hb : b ∈ L.point.y)
    (hxs : xs ⊆ L.point.y) (hr : r ⊆ L.point.x)
    (hwork : work ⊆ L.dialogPool.take 255) :
    wires (CodexYParityGadget.program xs b L.point.finite r work k) ⊆
      wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset := by
  rw [FiniteFlagInterval.old_clrF_support L hw]
  intro q hq
  have h := CodexYParityGadget.program_support xs b L.point.finite r work k hl hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at h
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
  rcases h with rfl | rfl | h | h | h
  · exact Or.inr hb
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (hxs h)
  · exact Or.inl (Or.inr (Or.inl (hr h)))
  · exact Or.inl (Or.inr (Or.inr (hwork h)))

theorem clear_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (xs : List Wire) (b : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hb : b ∈ L.point.y)
    (hxs : xs ⊆ L.point.y) (hr : r ⊆ L.point.x)
    (hwork : work ⊆ L.dialogPool.take 255) :
    wires (CodexYParityGadget.clearProgram xs b L.point.finite r work k) ⊆
      wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
  (CodexYParityGadget.clearProgram_support xs b L.point.finite r work k).trans
    (probe_support_old L hw xs b r work k hl hb hxs hr hwork)

/-- Apply to the new clearF and clrF after unfolding only the two small wrappers. -/
theorem gen_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (cx cy : Fp) (Clear Restore : Program)
    (he : wires Clear ⊆ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset)
    (hc : wires Restore ⊆ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset) :
    wires (FiniteFlagInterval.zrep L ++
      (Clear ++ renameProgram (swapF L) (ReflectionE1TickGapLow48.generic L cx cy) ++ Restore) ++
      FiniteFlagInterval.zrep L) ⊆
      wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset := by
  intro q used
  have hz : q ∈ wires (FiniteFlagInterval.zrep L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => FiniteFlagInterval.zrep_support_old L hw h
  have heq : q ∈ wires Clear → q ∈ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
    fun h => he h
  have hcq : q ∈ wires Restore → q ∈ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
    fun h => hc h
  simp only [Finset.mem_union] at heq hcq
  simp only [ReflectionE1TickGapLow48.gen, ReflectionE1TickGapLow48.mid,
    wires_append, Finset.mem_union] at used ⊢
  tauto

theorem point_y_generic (L : ControlledPointLayout) :
    L.point.y.toFinset ⊆ (OB5Support.genericSites L).toFinset := by
  intro q hq
  simp only [OB5Support.genericSites, PointAddLayout.pointWires,
    List.mem_toFinset, List.mem_append, List.mem_cons] at hq ⊢
  tauto

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (P : Program)
    (hP : wires P ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset) :
    wires P ⊆ (OB5Support.genericSites L).toFinset := by
  intro q hq
  rcases Finset.mem_union.mp (hP hq) with old | extra
  · exact ReflectionE1TickGapLow48.gen_sites L hw hn cx cy old
  · exact point_y_generic L extra

/-- Relabel an augmented support set when the added set is closed under the map. -/
theorem rename_support_extra (f : Wire → Wire) (P Q : Program) (S : Finset Wire)
    (h : wires P ⊆ wires Q ∪ S) (closed : ∀ q ∈ S, f q ∈ S) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) ∪ S := by
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (h hp) with old | extra
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, old, rfl⟩)
  · exact Finset.mem_union_right _ (closed p extra)

/-- All renamings along the generic-input path are explicit here. -/
theorem wrapper_support_extra (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (S : Finset Wire) (h : wires P ⊆ wires Q ∪ S)
    (hU : ∀ q ∈ S, Wrapper5.U L q ∈ S) (hM : ∀ q ∈ S, tauM L q ∈ S)
    (hE : ∀ q ∈ S, swapE L q ∈ S) (hD : ∀ q ∈ S, swapD L q ∈ S) :
    wires (Edges.wrapper L C cy P) ⊆ wires (Edges.wrapper L C cy Q) ∪ S := by
  have u := rename_support_extra (Wrapper5.U L) P Q S h hU
  have m := rename_support_extra (tauM L) _ _ S u hM
  have e := rename_support_extra (swapE L) _ _ S m hE
  have d := rename_support_extra (swapD L) _ _ S e hD
  have finite :
      wires (Edges.finiteProgram L C cy (renameProgram (Wrapper5.U L) P)) ⊆
      wires (Edges.finiteProgram L C cy (renameProgram (Wrapper5.U L) Q)) ∪ S := by
    intro q hq
    have hd : q ∈ wires (renameProgram (swapD L) (renameProgram (swapE L)
        (renameProgram (tauM L) (renameProgram (Wrapper5.U L) P)))) →
        q ∈ wires (renameProgram (swapD L) (renameProgram (swapE L)
        (renameProgram (tauM L) (renameProgram (Wrapper5.U L) Q)))) ∪ S :=
      fun hh => d hh
    simp only [Finset.mem_union] at hd
    simp only [Edges.finiteProgram, wires_append, Finset.mem_union] at hq ⊢
    tauto
  simpa only [Edges.wrapper] using rename_support_extra (Wrapper5.U L) _ _ S finite hU

/-- The concrete public y register is already counted even if idle. -/
theorem layout_y_io : layout.point.y.toFinset ⊆ ioWires := by decide +kernel

/-- Small finite checks: no arithmetic program is unfolded by these four claims. -/
theorem layout_y_images :
    (layout.point.y.toFinset.image (Wrapper5.U layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (tauM layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (swapE layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (swapD layout) ⊆ layout.point.y.toFinset) := by
  decide +kernel

/-- An old-wrapper-plus-I/O support bound preserves the exact previous static Q bound. -/
theorem wrapper_qubits760 (C : Point) (cx cy : Fp) (P : Program)
    (hP : wires P ⊆ wires (ReflectionE1TickGapLow48.gen layout cx cy) ∪ layout.point.y.toFinset) :
    qubits (Edges.wrapper layout C cy P) ≤ 1587 := by
  have images := layout_y_images
  have image_closed (f : Wire → Wire)
      (h : layout.point.y.toFinset.image f ⊆ layout.point.y.toFinset) :
      ∀ q ∈ layout.point.y.toFinset, f q ∈ layout.point.y.toFinset :=
    fun q hq => h (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have sup := wrapper_support_extra layout C cy P
    (ReflectionE1TickGapLow48.gen layout cx cy) layout.point.y.toFinset hP
    (image_closed _ images.1) (image_closed _ images.2.1)
    (image_closed _ images.2.2.1) (image_closed _ images.2.2.2)
  have absorb : ioWires ∪ wires (Edges.wrapper layout C cy P) ⊆
      ioWires ∪ wires (Edges.wrapper layout C cy (ReflectionE1TickGapLow48.gen layout cx cy)) := by
    intro q hq
    rcases Finset.mem_union.mp hq with io | used
    · exact Finset.mem_union_left _ io
    · rcases Finset.mem_union.mp (sup used) with old | extra
      · exact Finset.mem_union_right _ old
      · exact Finset.mem_union_left _ (layout_y_io extra)
  exact (Finset.card_le_card absorb).trans (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

/-- FusedFlags changes surrounding flag gates but its existing support lemma is sufficient. -/
theorem fused_wrapper_qubits760 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (P : Program)
    (hP : wires P ⊆ wires (ReflectionE1TickGapLow48.gen layout cx cy) ∪ layout.point.y.toFinset) :
    qubits (FusedFlags.wrapper layout (.some hc) cy P) ≤ 1587 := by
  have sub := FusedFlags.wrapper_support layout hc P
  exact (Finset.card_le_card
    (Finset.union_subset_union (Finset.Subset.refl ioWires) sub)).trans
    (wrapper_qubits760 (.some hc) cx cy P hP)

end ECDSAAdd.Entrant.CodexYParitySupport
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityProbe =====
section
/- Research integration draft, not yet compiled as a complete entrant. -/

namespace ECDSAAdd.Entrant.CodexYParityProbe
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def finiteBit (v w : Nat) : Bool := decide (¬ CodexYParityMath.matchesXY v w)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

def clrF : Program := CodexYParityGadget.program (xs L) (b L) L.point.finite (rest L) (work L) literal
def clearF : Program := CodexYParityGadget.clearProgram (xs L) (b L) L.point.finite (rest L) (work L) literal

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0) :
    run (clrF L) m s = ⟨s.phase,writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ finiteBit (regValue L.point.x s.basis) (regValue L.point.y s.basis))⟩ := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have hk : literal < 2^(rest L).length := by rw [(lengths L hw).1]; decide
  rw [clrF,CodexYParityGadget.program_run _ _ _ _ _ _ (ports_nodup L hw hn) hl hk s m hz,
    hit L hw s.basis]
  simp only [finiteBit,decide_not]

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  exact CodexYParityGadget.clearProgram_eq _ _ _ _ _ _ (ports_nodup L hw hn)
    ((lengths L hw).1.trans (lengths L hw).2.symm)
    (by rw [(lengths L hw).1]; decide) s m hz hzero

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite=base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite∉L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [←v.x]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit,this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [←v.y]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit,this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit,Ne.symm (fin_ne_generic L hn),v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [←v.clean]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit,this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q=writeBit base L.point.finite _ q
    by_cases hqf : q=L.point.finite
    · subst hqf; simp [writeBit,hfs,v.x,v.y]
    · simp [writeBit,hqf,v.rest q hq]

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=finiteBit X.val Y.val) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz]
    simp [writeBit,v.x,v.y,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

include hw in
theorem clrF_support_old : wires (clrF L) ⊆
    wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset := by
  have inputs := inputs_mem L hw
  exact CodexYParitySupport.probe_support_old L hw (xs L) (b L) (rest L) (work L) literal
    ((lengths L hw).1.trans (lengths L hw).2.symm) inputs.1 inputs.2.1 inputs.2.2
    (work_subset L)

include hw in
theorem clearF_support_old : wires (clearF L) ⊆
    wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
  (CodexYParityGadget.clearProgram_support (xs L) (b L) L.point.finite (rest L) (work L) literal).trans
    (clrF_support_old L hw)

include hw in
theorem counts :
    toffoliCount (clrF L)=245 ∧ measurementCount (clrF L)=245 ∧
    toffoliCount (clearF L)=244 ∧ measurementCount (clearF L)=245 := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have p := CodexYParityGadget.program_counts (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  have c := CodexYParityGadget.clearProgram_counts (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  simpa only [(lengths L hw).1,clrF,clearF] using And.intro p.1 (And.intro p.2 c)

include hw hn in
theorem physical : GatePhysical (clrF L) ∧ GatePhysical (clearF L) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  exact ⟨CodexYParityGadget.program_physical _ _ _ _ _ _ hl (ports_nodup L hw hn),
    CodexYParityGadget.clearProgram_physical _ _ _ _ _ _ hl (ports_nodup L hw hn)⟩

abbrev zrep := FiniteFlagInterval.zrep
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L

theorem sentinel_finiteBit : finiteBit FiniteFlagInterval.sentinel 0=false := by
  have eq : FiniteFlagInterval.sentinel=p-1 := by norm_num [FiniteFlagInterval.sentinel,p]
  simp [finiteBit,eq,CodexYParityMath.sentinel_matches]

include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : finiteBit X.val Y.val = fin) (h2 : finiteBit X'.val Y'.val = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
        L.point.finite ^^ finiteBit X'.val Y'.val) = base := by
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
    have z1 := FiniteFlagInterval.zrep_step L hw hn 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (FiniteFlagInterval.sentinel : Fp) 0 cx cy base' FiniteFlagInterval.sentinel_ne_zero) hfin
      (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit) (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit)
    have z2 := FiniteFlagInterval.zrep_step L hw hn (FiniteFlagInterval.sentinel : Fp) 0 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : finiteBit x.val y.val = true := decide_eq_true (CodexYParityMath.curve_not_matches hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : finiteBit (genericX x y cx cy).val (genericY x y cx cy).val = true :=
        decide_eq_true (CodexYParityMath.curve_not_matches (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := FiniteFlagInterval.zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))


omit hw hn

attribute [local irreducible] toffoliCount measurementCount gateSlots ReflectionE1TickGapLow48.generic

include hw in
theorem gen_support_subset (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset := by
  exact CodexYParitySupport.gen_support_old L hw cx cy (clearF L) (clrF L)
    (clearF_support_old L hw) (clrF_support_old L hw)

include hw hn in
theorem gen_sites (cx cy : Fp) : wires (gen L cx cy) ⊆ (OB5Support.genericSites L).toFinset :=
  CodexYParitySupport.gen_sites L hw hn cx cy (gen L cx cy) (gen_support_subset L hw cx cy)

include hw in
theorem gen_counts (cx cy : Fp) :
    toffoliCount (gen L cx cy)+4=toffoliCount (FiniteFlagInterval.gen L cx cy) ∧
    measurementCount (gen L cx cy)+4=measurementCount (FiniteFlagInterval.gen L cx cy) := by
  have n := counts L hw
  have o := FiniteFlagInterval.clrF_counts L hw
  have e := FiniteFlagInterval.clearF_counts L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,toffoliCount_append,measurementCount_append,n.1,n.2.1,n.2.2.1,n.2.2.2,
    o.1,o.2,e.1,e.2]
  omega

include hw in
theorem gen_slots (cx cy : Fp) : gateSlots (gen L cx cy)≤gateSlots (FiniteFlagInterval.gen L cx cy) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have n := CodexYParityGadget.program_slots (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  have e := CodexYParityGadget.clearProgram_slots (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  rw [(lengths L hw).1] at n e
  have hxs : (xs L).length = 7 := by simp [xs]
  rw [hxs] at n e
  change gateSlots (clrF L)≤2223 at n
  change gateSlots (clearF L)≤2223 at e
  have o := FiniteFlagInterval.clrF_slots_exact L hw
  have c := FiniteFlagInterval.clearF_slots L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,gateSlots_append]
  omega

include hw hn in
theorem gen_physical (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := FiniteFlagInterval.zrep_physical L hn
  have c := (physical L hw hn).1
  have e := (physical L hw hn).2
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic,zrep] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

include hw in
theorem wrapper_counts (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+4=
      toffoliCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+4=
      measurementCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy))≤
      gateSlots (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) := by
  have h := gen_counts L hw cx cy
  have s := gen_slots L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 :=
  CodexYParitySupport.wrapper_qubits760 C cx cy (gen layout cx cy)
    (gen_support_subset layout layout_widths cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151035,1498861,1587,50236557⟩

theorem program_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ control R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc control _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151035 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤2151035
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498861 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤1498861
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1587 := by
  cases C with
  | zero => change qubits []≤1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50236557 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.2
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=23581 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤50236557
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498861
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50236557
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.CodexYParityProbe
end

