import ECDSAAdd.Submission.Entrant.LaneKernel
import ECDSAAdd.Arithmetic.MappedCompressedPointArithmetic
import ECDSAAdd.Arithmetic.MappedKernelPhysical
import ECDSAAdd.Arithmetic.SkywalkPointPhysical
import ECDSAAdd.Arithmetic.CompressedPointDialogSteps
import ECDSAAdd.Arithmetic.CompressedPointDialogResources
import ECDSAAdd.Baselines.SkywalkSlots

/-! Lane A point arithmetic: zero-divisor wrapper, physical placement and
point-dialog backend around `laneKernel`.  Proofs are the original Skywalk
proofs re-pointed at the Lane A kernel; resources are derived from the
unchanged Skywalk program by support inclusion and exact count differences. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.MappedCompressed.LaneA
open Secp256k1 DirectSkywalk ControlledPointLayout

section Kernel
attribute [local irreducible] ECDSAAdd.Entrant.HalfField.segment ECDSAAdd.Entrant.LaneI.segmentI selectedFieldSegment NativeFirstDirect.forward
  compressedCompactForward compressedCompactReverse NativeFirstKnown.inverse

theorem laneKernel_support (divide : Bool) : wires (laneKernel divide) ⊆ slots.toFinset := by
  have k := kernel_support divide
  have seg := ECDSAAdd.Entrant.LaneI.segmentI_support divide
  simp only [kernel,wires_append,Finset.union_subset_iff] at k
  simp only [laneKernel,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨k.1.1.1.1.1.1,k.1.1.1.1.1.2⟩,k.1.1.1.1.2⟩,seg⟩,k.1.1.2⟩,k.1.2⟩,k.2⟩

attribute [local irreducible] toffoliCount measurementCount in
theorem laneKernel_counts (divide : Bool) :
    toffoliCount (laneKernel divide)=(if divide then 1050180 else 1050690) ∧
    measurementCount (laneKernel divide)=721478 := by
  have f := NativeFirstDirect.forward_counts base
  have r := NativeFirstKnown.inverse_counts base
  have integer := integer_tail_counts
  have clear := skywalkTerminalClear_counts (base 511) (base 512) (base 770)
  have field := ECDSAAdd.Entrant.LaneI.segmentI_counts divide
  simp only [laneKernel,skywalkArithmeticClear,toffoliCount_append,measurementCount_append,
    f.1,f.2,r.1,r.2,integer.1,integer.2.1,integer.2.2.1,integer.2.2.2,
    clear.1,clear.2,field.1,field.2]
  cases divide <;> constructor <;> norm_num

theorem laneKernel_physical (divide : Bool) : GatePhysical (laneKernel divide) := by
  have first := (NativeFirstDirect.programs_physical base base_pool_nodup).1
  have loops := compressedLoops_physical base 1 511 (by decide) base_pool_nodup
  have last := NativeFirstKnown.inverse_physical base base_pool_nodup
  have field := ECDSAAdd.Entrant.LaneI.segmentI_physical divide
  simp only [laneKernel,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨first,loops.1⟩,mappedClear_physical⟩,field⟩,mappedClear_physical⟩,loops.2⟩,last⟩

open Challenge in
theorem laneKernel_gateSlots_le (divide : Bool) :
    gateSlots (laneKernel divide) ≤ 20500000 := by
  have hn := ECDSAAdd.Baselines.nativeFirst_gateSlots_le base
  have hi := ECDSAAdd.Baselines.compactLoops_gateSlots_le base 1 511 (by omega)
  have hf := ECDSAAdd.Entrant.LaneI.segmentI_gateSlots_le divide
  have hc : gateSlots (skywalkArithmeticClear base) = 3 := rfl
  rw [laneKernel]
  simp only [gateSlots_append, hc]
  omega

end Kernel

def laneControlled (divide : Bool) : Program :=
  directZeroControlled (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (laneKernel divide)

section Controlled
attribute [local irreducible] laneKernel kernel directZeroDivisorEnter directZeroDivisorLeave

theorem laneControlled_support (divide : Bool) : wires (laneControlled divide) ⊆ slots.toFinset := by
  have c := controlled_support divide
  simp only [controlled,directZeroControlled,wires_append,Finset.union_subset_iff] at c
  simp only [laneControlled,directZeroControlled,wires_append,Finset.union_subset_iff]
  exact ⟨c.1,laneKernel_support divide,c.2.2⟩

theorem laneControlled_counts (divide : Bool) :
    toffoliCount (laneControlled divide)=(if divide then 1050690 else 1051200) ∧
    measurementCount (laneControlled divide)=721986 := by
  have width : (wireBlock base 0 255).length+1=(wireBlock base 770 256).length := by
    simp [wireBlock]
  have wrapped := directZeroControlled_counts (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (laneKernel divide) width
  have core := laneKernel_counts divide
  simp only [laneControlled] at ⊢
  rw [wrapped.1,wrapped.2,core.1,core.2,wireBlock_length]
  cases divide <;> norm_num

theorem laneControlled_physical (divide : Bool) : GatePhysical (laneControlled divide) := by
  apply directZero_physical _ _ _ _ _ _ (laneKernel_physical divide)
  decide +kernel

open Challenge in
theorem laneControlled_gateSlots_le (divide : Bool) :
    gateSlots (laneControlled divide) ≤ 20600000 := by
  have hk := laneKernel_gateSlots_le divide
  have hz := ECDSAAdd.Baselines.zeroCompare_gateSlots_le (wireBlock base 770 256)
    (wireBlock base 0 255) (base 2313) (base 2411)
  have hm := ECDSAAdd.Baselines.maskedConstant_gateSlots_le (base 2411) (wireBlock base 770 256) 1
  simp only [wireBlock_length] at hz hm
  simp only [laneControlled,directZeroControlled,directZeroDivisorEnter,directZeroDivisorLeave,
    gateSlots_append]; omega

end Controlled

section ControlledSpec
attribute [local irreducible] run measurementCount laneKernel
  directZeroDivisorEnter directZeroDivisorLeave

private theorem controlled_port_nodup :
    (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255++
      wireBlock base 2056 256)).Nodup := by
  have first : (List.range' 770 256++List.range' 0 255).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hx hc
    simp only [List.mem_range'_1] at hx hc
    omega
  have words : (List.range' 770 256++List.range' 0 255++List.range' 2056 256).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨first,List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hxy hz
    simp only [List.mem_append,List.mem_range'_1] at hxy hz
    omega
  have ids : (2411::2313::(List.range' 770 256++List.range' 0 255++List.range' 2056 256)).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
    · apply List.nodup_cons.mpr
      constructor
      · simp only [List.mem_append,List.mem_range'_1]
        omega
      · exact words
  change ((2411::2313::(List.range' 770 256++List.range' 0 255++
    List.range' 2056 256)).map base).Nodup
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact ids

private theorem zero_flag_outside : base 2411 ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hi
  have same := base_injective eq
  omega

/-- The actual zero-divisor wrapper satisfies the original strong port
contract. A zero divisor is allowed on the inactive arithmetic branch;
comparison work and repaired kernel cleanliness come from the caller input. -/
theorem laneControlled_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (zeroBranch : x = 0 → s.basis (base 2400) = false)
    (hflag : s.basis (base 2411) = false)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (laneControlled divide) m s) := by
  let D := directDivisor x
  let R := (directSkywalkResult divide (s.basis (base 2400)) x Y).val
  have positive : 0 < D := Nat.pos_of_ne_zero (directDivisor_ne_zero x)
  have bound : D < p := by
    by_cases zero : x = 0
    · simp only [D,directDivisor,zero,if_true]
      norm_num [p]
    · simpa only [D,directDivisor,zero,if_false] using hx
  have sameResult : directSkywalkResult divide (s.basis (base 2400)) D Y =
      directSkywalkResult divide (s.basis (base 2400)) x Y := by
    by_cases zero : x = 0
    · simp only [directSkywalkResult,zeroBranch zero,Bool.false_eq_true,if_false]
    · simp only [D,directDivisor,zero,if_false]
  have cin : s.basis (base 2313) = false :=
    arith_input_bit base hn x Y.val s.basis hin 2313 (by omega) (by omega) (by omega)
  have carry : ∀ q ∈ wireBlock base 0 255,s.basis q = false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact arith_input_bit base hn x Y.val s.basis hin i (by omega) (by omega) (by omega)
  have callback : ∀ (t : State) (ms : List Bool),
      regValue (wireBlock base 770 256) t.basis = directDivisor (regValue (wireBlock base 770 256) s.basis) →
      regValue (wireBlock base 2056 256) t.basis = regValue (wireBlock base 2056 256) s.basis →
      t.basis (base 2411) = decide (regValue (wireBlock base 770 256) s.basis = 0) →
      (∀ q,q ≠ base 2411 → q ∉ wireBlock base 770 256 → t.basis q = s.basis q) →
      (run (laneKernel divide) ms t).phase = t.phase ∧
      regValue (wireBlock base 2056 256) (run (laneKernel divide) ms t).basis = R ∧
      ∀ q,q ∉ wireBlock base 2056 256 → (run (laneKernel divide) ms t).basis q = t.basis q := by
    intro t ms divisor numerator _ frame
    have input : SkywalkArithmeticInput base D Y.val t.basis := by
      refine ⟨divisor.trans (congrArg directDivisor hin.1),numerator.trans hin.2.1,?_⟩
      intro q hq hdx hdy
      have ne : q ≠ base 2411 := fun eq => zero_flag_outside (eq ▸ hq)
      exact (frame q ne hdx).trans (hin.2.2 q hq hdx hdy)
    have controls (q : Wire) (hq : q ∈ [base 2400,base 2409,base 2410]) :
        t.basis q = s.basis q := by
      have ne : q ≠ base 2411 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl
        all_goals intro eq; have same := base_injective eq; omega
      have away : q ∉ wireBlock base 770 256 :=
        fun bad => ho q hq (arith_block_subset_shared base 770 256 (by omega) bad)
      exact frame q ne away
    have strong := NativeFirstDirect.LaneA.laneKernel_spec divide hn hlo ho hf D Y positive bound t ms input
      ((controls _ (by simp)).trans hg0) ((controls _ (by simp)).trans hs0)
    unfold DirectSkywalkArithmeticStrong at strong
    rw [controls (base 2400) (by simp),sameResult] at strong
    exact strong
  have width : (wireBlock base 0 255).length+1 = (wireBlock base 770 256).length := by
    simp only [wireBlock_length]
  have records := directZeroControlled_states (wireBlock base 770 256) (wireBlock base 2056 256)
    (wireBlock base 0 255) (base 2313) (base 2411) controlled_port_nodup width (laneKernel divide) s
    (m.take (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411))))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).take (measurementCount (laneKernel divide)))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).drop (measurementCount (laneKernel divide)))
    R cin hflag carry callback
  simpa only [DirectSkywalkArithmeticStrong,laneControlled,directZeroControlled,run_append,
    skywalkArithmeticNumerator,R] using records


end ControlledSpec

section Transfer
attribute [local irreducible] run laneControlled

def laneLogicalInput (domain : Finset Wire) (f : Wire → Wire) (s : State) : State :=
  ⟨s.phase,fun q => if q∈domain then s.basis (f q) else false⟩

private theorem divisor_sites : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))
private theorem numerator_sites : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
private theorem control_site : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

private theorem reg_map_agree (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- Transfer the original strong point-arithmetic port contract to physical
wires, using only finite-support injectivity. Logical unused ghost sites are
completed with zero and never impose a condition on physical outsiders. -/
private theorem pointTransfer_core (L : ControlledPointLayout) (f : Wire → Wire)
    (domain : Finset Wire) (divide : Bool)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (zeroFlag : f (base 2411)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (bSite : base 2400∈domain)
    (X : Nat) (Y : Fp) (B : Bool) (hx0 : B=true → X≠0)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (P : Program) (programSites : wires P⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      (X=0 → t.basis (base 2400)=false) →
      t.basis (base 2411)=false → t.basis (base 2409)=false → t.basis (base 2410)=false →
      DirectSkywalkArithmeticStrong divide base (base 2400) X Y t (run P records t)) :
    let out := run (renameProgram f P) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=(directSkywalkResult divide B X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let t := laneLogicalInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [reg_map_agree f _ t.basis s.basis (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [reg_map_agree f _ t.basis s.basis (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,laneLogicalInput,if_neg used]
  have control : t.basis (base 2400)=B := by
    rw [inputBits _ bSite,controlMap,hb]
  have zeroBranch : X=0 → t.basis (base 2400)=false := by
    intro eq
    rw [control]
    cases B
    · rfl
    · exact False.elim ((hx0 rfl) eq)
  have strong := P_spec t m input zeroBranch
    (zero _ zeroFlag) (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective
    P programSites m t s rfl inputBits
  unfold DirectSkywalkArithmeticStrong at strong
  rw [control] at strong
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (reg_map_agree f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q outside
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      have away : a∉skywalkArithmeticNumerator base := by
        intro mem
        apply outside
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨a,mem,rfl⟩
      exact (transfer.2 a ha).trans ((strong.2.2 a away).trans (inputBits a ha))
    · exact run_rename_pool_outside f domain P
        programSites m s q image



theorem laneTransfer_spec (L : ControlledPointLayout) (f : Wire → Wire)
    (placement : PointArithmeticPlacement L f) (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hx : X<p) (hx0 : B=true → X≠0)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) :
    let out := run (renameProgram f (laneControlled divide)) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=(directSkywalkResult divide B X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,selectorG,selectorS,zeroFlag⟩
  exact pointTransfer_core L f slots.toFinset divide injective divisorMap numeratorMap controlMap
    sharedWork selectorG selectorS zeroFlag divisor_sites numerator_sites control_site
    X Y B hx0 s m hb hX hY clean
    (laneControlled divide) (laneControlled_support divide)
    (fun t records input zeroBranch hflag hg hs =>
      laneControlled_spec divide hn hlo ho hf X Y hx t records input zeroBranch hflag hg hs)


end Transfer

def laneArith (L : ControlledPointLayout) (multiply : Bool) : Program :=
  renameProgram (pointWireFn L) (laneControlled (!multiply))

section Arith
attribute [local irreducible] run laneControlled toffoliCount measurementCount
  mixedTranscriptUnitTrace SkywalkTrace.next Nat.iterate

private theorem lane_logical_shared_nodup : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

private theorem lane_logical_scalar_outside (i : Nat) (hi : 2314 ≤ i) :
    base i ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hj
  have same := base_injective eq
  omega

private theorem lane_logical_selectors_outside :
    ∀ q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base := by
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact lane_logical_scalar_outside _ (by omega)

/-- Fixed logical template layout; only pure labels are checked here.
The actual recorded tape, not its numerical contents, supplies the layout. -/
private theorem lane_logical_mixed_layout :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base) := by
  have scalar : [base 2400,base 2409,base 2410].Nodup := by simp [base]
  have disjoint : [base 2400,base 2409,base 2410].Disjoint (skywalkSharedWires base) :=
    List.disjoint_left.mpr (fun q hq => lane_logical_selectors_outside q hq)
  have hall := List.nodup_append'.mpr ⟨scalar,lane_logical_shared_nodup,disjoint⟩
  have unused : skywalkSharedUnused base⊆skywalkSharedWires base := by
    intro q hq
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals exact arith_mem base 0 2314 _ (by omega) (by omega)
  apply mixedTranscriptTape_layout
  intro r hr
  have pair := (List.nodup_cons.mp (skywalkShared_tape_layout base lane_logical_shared_nodup
    (base 2400) (lane_logical_selectors_outside _ (by simp)) r hr)).2
  have sub : (r.2::r.1::(skywalkSharedField base).wires)⊆skywalkSharedWires base := by
    intro q hq
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).2
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).1
    · exact retained_field_subset_shared base hq
  constructor
  · exact lane_logical_shared_nodup
  · apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hall q
    have hp := List.nodup_iff_count.mp pair q
    have hle : (r.2::r.1::(skywalkSharedField base).wires).count q≤
        (skywalkSharedWires base).count q := by
      by_cases hm : q∈r.2::r.1::(skywalkSharedField base).wires
      · have positive := List.count_pos_iff.mpr (sub hm); omega
      · rw [List.count_eq_zero.mpr hm]; omega
    simp only [List.count_append,List.count_cons,List.count_nil] at hh hp hle ⊢
    omega
  · exact fun h => lane_logical_selectors_outside _ (by simp) (fusedSharedSites_subset base h)
  · exact fun h => lane_logical_selectors_outside _ (by simp) (unused h)
  · exact fun h => lane_logical_selectors_outside _ (by simp) (unused h)

theorem laneArith_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (laneArith L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (laneArith L multiply) m s).basis=V ∧
    ∀ q,q∉L.point.y → (run (laneArith L multiply) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  have result := laneTransfer_spec L (pointWireFn L) (pointPlacement L hw hn) (!multiply)
    lane_logical_shared_nodup base_above lane_logical_selectors_outside lane_logical_mixed_layout
    X (Y:Fp) B hX hX0 s m hb hx (hy.trans yValue.symm) hc
  cases B <;> cases multiply <;>
    simpa only [laneArith,directSkywalkResult,skywalkArithmeticResult,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,yValue] using result


theorem laneArith_support (L : ControlledPointLayout) (hw : L.Widths) (multiply : Bool) :
    wires (laneArith L multiply)⊆
      (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).toFinset := by
  intro q hq
  rw [laneArith,renameProgram_support] at hq
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  exact pointWireFn_slots_image L hw (Finset.mem_image.mpr
    ⟨old,laneControlled_support (!multiply) used,rfl⟩)

theorem laneArith_counts (L : ControlledPointLayout) :
    toffoliCount (laneArith L false)=1050690 ∧
    measurementCount (laneArith L false)=721986 ∧
    toffoliCount (laneArith L true)=1051200 ∧
    measurementCount (laneArith L true)=721986 := by
  have div := laneControlled_counts true
  have mul := laneControlled_counts false
  have rd := renameProgram_counts (pointWireFn L) (laneControlled true)
  have rm := renameProgram_counts (pointWireFn L) (laneControlled false)
  simp only [laneArith,Bool.not_false,Bool.not_true]
  rw [rd.1,rd.2,rm.1,rm.2,div.1,div.2,mul.1,mul.2]
  norm_num

theorem laneArith_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) : GatePhysical (laneArith L multiply) := by
  apply gatePhysical_rename_support (pointWireFn L) (laneControlled (!multiply))
  · intro a ha b hb eq
    exact pointWireFn_injective_slots L hw hn a (laneControlled_support (!multiply) ha) b
      (laneControlled_support (!multiply) hb) eq
  · exact laneControlled_physical _

open Challenge in
theorem laneArith_gateSlots_le (L : ControlledPointLayout) (multiply : Bool) :
    gateSlots (laneArith L multiply) ≤ 20600000 := by
  simpa only [laneArith,ECDSAAdd.Baselines.rename_gateSlots] using laneControlled_gateSlots_le (!multiply)

end Arith

/-- The Skywalk generic dialogue with Lane A arithmetic in both calls. -/
def laneGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  laneArith L false ++
  CompressedPointSquare.computableProgram L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++
  laneArith L true ++
  pointRecoveryStage L cx cy

section Generic
attribute [local irreducible] laneArith pointCompressedArithmetic CompressedPointSquare.computableProgram

theorem laneGeneric_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (laneGeneric L cx cy) ⊆ (CompressedPointDialog.sites L).toFinset := by
  have g := CompressedPointDialog.generic_support L hw hn cx cy
  simp only [pointCompressedDialogGeneric,wires_append,Finset.union_subset_iff] at g
  have a : wires (laneArith L false) ⊆ (CompressedPointDialog.sites L).toFinset :=
    laneArith_support L hw false
  have b : wires (laneArith L true) ⊆ (CompressedPointDialog.sites L).toFinset :=
    laneArith_support L hw true
  simp only [laneGeneric,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨g.1.1.1.1.1.1,g.1.1.1.1.1.2⟩,a⟩,g.1.1.1.2⟩,g.1.1.2⟩,b⟩,g.2⟩

theorem laneGeneric_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (laneGeneric L cx cy)=2207162 ∧
    measurementCount (laneGeneric L cx cy)=1548724 := by
  have a k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have b k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have arith := laneArith_counts L
  have square := CompressedPointSquare.counts L hw
  have recovery := pointRecoveryStage_counts L hw cx cy
  simp only [laneGeneric,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,arith.1,arith.2.1,arith.2.2.1,arith.2.2.2,
    square.1,square.2,recovery.1,recovery.2]
  norm_num

theorem laneGeneric_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) : GatePhysical (laneGeneric L cx cy) := by
  have ax (k : Fp) := pointDialogConstantAdd_physical L hw hn L.point.x (Or.inl rfl) k
  have ay (k : Fp) := pointDialogConstantAdd_physical L hw hn L.point.y (Or.inr rfl) k
  have di := laneArith_physical L hw hn false
  have mu := laneArith_physical L hw hn true
  have sq := CompressedPointSquare.computableProgram_physical L hw hn
  have recovery := pointRecoveryStage_physical L hw hn cx cy
  simp only [laneGeneric,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di⟩,sq⟩,ax _⟩,mu⟩,recovery⟩

open Challenge Baselines in
theorem laneGeneric_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (cx cy : Fp) : gateSlots (laneGeneric L cx cy) ≤ 46300000 := by
  have a := recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (-cx)
  have b := recoveryConstant_gateSlots_le L hw L.point.y hw.inputY (-cy)
  have c := recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (3*cx)
  have d := laneArith_gateSlots_le L false
  have e := laneArith_gateSlots_le L true
  have f := skywalkSquare_gateSlots_le L hw
  have g := recoveryStage_gateSlots_le L hw cx cy
  simp only [laneGeneric,gateSlots_append]; omega

end Generic

section GenericSpec
open CompressedPointDialog
attribute [local irreducible] run CompressedPointSquare.computableProgram

theorem lane_step_arithmetic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) (multiply : Bool) (hX : G=true → X≠0) :
    Triple (PointDialogValues L X Y G base) (laneArith L multiply)
      (PointDialogValues L X (if G then (if multiply then Y*X else Y/X) else Y) G base) := by
  intro s m v
  have hX0 : G=true → X.val≠0 := by
    intro hg hx
    apply hX hg
    apply ZMod.val_injective p
    simpa using hx
  obtain ⟨phase,value,rest⟩ := laneArith_correct L hw hn multiply
    X.val Y.val G X.isLt hX0 Y.isLt s m v.generic v.x v.y v.clean
  refine ⟨phase,v.withY hn ?_ rest⟩
  cases G <;> cases multiply <;>
    simpa only [Bool.false_eq_true,if_false,if_true,ZMod.natCast_zmod_val] using value

theorem laneGeneric_true (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (laneGeneric L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := dialogStep_addX L hw hn X Y true base (-cx)
  have h2 := dialogStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := lane_step_arithmetic L hw hn (X-cx) (Y-cy) true base false (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := CompressedPointDialog.step_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := dialogStep_addX L hw hn ((X-cx)-a*a) a true base (3*cx)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := lane_step_arithmetic L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have recovery := pointRecoveryStage_correct L hw hn d (a*d) cx cy true base
  simp only [if_true] at recovery
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at recovery
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [laneGeneric,List.append_assoc] using h

theorem laneGeneric_false (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (laneGeneric L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := dialogStep_addX L hw hn X Y false base (-cx)
  have h2 := dialogStep_addY L hw hn X Y false base (-cy)
  have h3 := lane_step_arithmetic L hw hn X Y false base false (by simp)
  have h4 := CompressedPointDialog.step_square L hw hn X Y false base
  have h5 := dialogStep_addX L hw hn X Y false base (3*cx)
  have h6 := lane_step_arithmetic L hw hn X Y false base true (by simp)
  have recovery := pointRecoveryStage_correct L hw hn X Y cx cy false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [laneGeneric,List.append_assoc] using h


theorem laneBoundary_generic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (laneGeneric L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    obtain ⟨phase,hv⟩ := laneGeneric_false L hw hn _ _ cx cy s.basis s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      obtain ⟨phase,hv⟩ := laneGeneric_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩



end GenericSpec

end ECDSAAdd.Arithmetic.MappedCompressed.LaneA
