import ECDSAAdd.Submission.Entrant.FrontierEntryKernel

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntryDivision
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires

theorem kernelTransferS (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires FrontierEntryKernel.kernel5S⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f FrontierEntryKernel.kernel5S) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits (q : Wire) (hq : q∈domain) : b.basis q=t.basis (f q) := by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside (q : Wire) (hq : q∈domain) (haway : q∉wireBlock base 2056 256) : f q∉L.point.y := by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩ := List.mem_map.mp bad
    have eq : q=r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q := by
    intro q hq
    by_cases used : q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    rw [mapped_regS f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := FrontierEntryKernel.kernel5S_correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective FrontierEntryKernel.kernel5S sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (mapped_regS f _ (run FrontierEntryKernel.kernel5S m b).basis
      (run (renameProgram f FrontierEntryKernel.kernel5S) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain FrontierEntryKernel.kernel5S sites m t q image).trans (same q hq)



open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires toffoliCount measurementCount
def arithEntryS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) FrontierEntryKernel.kernel5S

theorem arithEntryS_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithEntryS L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ FrontierEntryKernel.kernel5S_support

theorem arithEntryS_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (arithEntryS L) := by
  apply gatePhysical_rename_support (wireFn2 L) FrontierEntryKernel.kernel5S
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (FrontierEntryKernel.kernel5S_support ha)) b
      (ArithmeticOB5.logical_sub_old (FrontierEntryKernel.kernel5S_support hb)) eq
  · exact FrontierEntryKernel.kernel5S_physical

private theorem divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem arithEntryS_correct (freeS : base 1541∉wires Q5FusionFields.hostField5S) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (arithEntryS L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact kernelTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    divisor_sitesS numerator_sitesS control_siteS (FrontierEntryKernel.kernel5S_support.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] arithEntryS arithS

theorem arithEntryS_eq (freeS : base 1541∉wires Q5FusionFields.hostField5S) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    run (arithEntryS L) m t=run (arithS L false) [] s := by
  have newer := arithEntryS_correct freeS L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (arithEntryS L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm


open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
open Challenge Baselines
def fusedDivisionF (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ arithEntryS L

section EntryStep
attribute [local irreducible] run arithEntryS arithS fusedY fastConstAdd

theorem fusedDivisionF_step (freeS : base 1541∉wires Q5FusionFields.hostField5S) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedDivisionF L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin) := by
  intro s m v
  let Z : Fp := Y+(if G then k else 0)
  let n := measurementCount (fusedY L k)
  let a := run (fusedY L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase : a.phase=c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis=centerWord (Z/2) := by
    simpa only [v.generic,Z] using fused.2.1
  have hp : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := arithEntryS_eq freeS L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (fusedDivisionF L k) m s=run (arithS L false) [] c := by
    simp only [fusedDivisionF,run_append]
    change run (arithEntryS L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep

theorem fusedDivisionF_support (L : ControlledPointLayout) (hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    wires (fusedDivisionF L k)⊆(OB5Support.sites L).toFinset := by
  simp only [fusedDivisionF,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    arithEntryS_support L hw⟩

theorem fusedDivisionF_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (fusedDivisionF L k) := by
  simp only [fusedDivisionF,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,arithEntryS_physical L hw hn⟩

theorem fusedDivisionF_counts_diff (L : ControlledPointLayout) (_hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    toffoliCount (fusedDivisionF L k)+505=toffoliCount (OwnEntryFuseQ6.fusedDivisionF L k) ∧
      measurementCount (fusedDivisionF L k)+509=measurementCount (OwnEntryFuseQ6.fusedDivisionF L k) := by
  have c:=FrontierEntryKernel.kernel5S_counts_diff
  have a:=renameProgram_counts (wireFn2 L) FrontierEntryKernel.kernel5S
  have b:=renameProgram_counts (wireFn2 L) OwnEntryFuseQ6.kernel5S
  simp only [fusedDivisionF,OwnEntryFuseQ6.fusedDivisionF,arithEntryS,OwnEntryFuseQ6.arithEntryS,
    toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  constructor <;> omega

theorem fusedDivisionF_slots_le (L : ControlledPointLayout) (_hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    gateSlots (fusedDivisionF L k)≤gateSlots (OwnEntryFuseQ6.fusedDivisionF L k) := by
  simp only [fusedDivisionF,OwnEntryFuseQ6.fusedDivisionF,arithEntryS,OwnEntryFuseQ6.arithEntryS,
    gateSlots_append,rename_gateSlots]
  exact Nat.add_le_add_left FrontierEntryKernel.kernel5S_slots_le _

private theorem placed_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i k : Nat) (hi : base i∈OB5Support.logicalSites)
    (hm : wireFn2 L (base i)=L.core.poolWire k)
    (free : base i∉wires FrontierEntryKernel.kernel5S) :
    L.core.poolWire k∉wires (arithEntryS L) := by
  rw [arithEntryS,renameProgram_support]
  intro h
  obtain ⟨old,used,eq⟩:=Finset.mem_image.mp h
  have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (FrontierEntryKernel.kernel5S_support used)) (base i)
    (ArithmeticOB5.logical_sub_old hi) mapped
  exact free (back ▸ used)

private theorem logical_mem (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
    base i∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem arithEntryS_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) :
    L.core.poolWire k∉wires (arithEntryS L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact placed_free L hw hn 2312 1800 (logical_mem _ (by simp)) rfl
      (FrontierEntryKernel.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 766 766 (logical_mem _ (by simp)) rfl
      (FrontierEntryKernel.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 765 765 (logical_mem _ (by simp)) rfl
      (FrontierEntryKernel.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 767 767 (logical_mem _ (by simp)) rfl
      (FrontierEntryKernel.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 1026 770 (logical_mem _ (by simp)) rfl
      (FrontierEntryKernel.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 1541 1285 (logical_mem _ (by simp)) rfl
      (FrontierEntryKernel.kernel5S_free _ (by simp))

theorem fusedDivisionF_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (_freeS : base 1541∉wires Q5FusionFields.hostField5S) (k : Nat)
    (hk : k∈[1800,766,765,767,770,1285]) (c : Fp) :
    L.core.poolWire k∉wires (fusedDivisionF L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have old:=ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [fusedDivisionF,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),arithEntryS_free L hw hn k hk⟩

end ECDSAAdd.Entrant.FrontierEntryDivision
