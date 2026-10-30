import ECDSAAdd.Submission.Entrant.E1Generic

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
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch

/-- The wrapped generic body (same wrapper as the stage-fused producer). -/
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := GenericQ5Geometry.wrapG L (generic L cx cy)

section Wrap
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem mid_values (Gp : Program) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') Gp
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (clrF L ++ renameProgram (swapF L) Gp ++ clrF L)
      (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn Gp X Y X' Y' G _ hP hb2
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




variable (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
  (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
    (mixedTranscriptTape base))
include logicalND hlo logicalAway logicalReplay

theorem ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
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
    have mid := mid_values L hw hn (generic L cx cy) 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn logicalND hlo logicalAway logicalReplay 5 0 cx cy base' finFive_ne_zero) hfin
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
      have mid := mid_values L hw hn (generic L cx cy) x y x y false s.basis true
        (fun base' => generic_false L hw hn logicalND hlo logicalAway logicalReplay x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
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
      have mid := mid_values L hw hn (generic L cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn logicalND hlo logicalAway logicalReplay x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))



end Wrap

section Counts
attribute [local irreducible] toffoliCount measurementCount

theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (generic L cx cy)+496=toffoliCount (All12Generic.generic L
      (FrontierEntry1591Callers.division FrontierEntry1591Kernel.entryKernel L)
      (PrefixFrontierSquare1591.program L) (FrontierEntry1591Callers.exit FrontierEntry1591Kernel.exitKernel L) cx cy
        OwnDiagAll12Square.sqOff) ∧
    measurementCount (generic L cx cy)+496=measurementCount (All12Generic.generic L
      (FrontierEntry1591Callers.division FrontierEntry1591Kernel.entryKernel L)
      (PrefixFrontierSquare1591.program L) (FrontierEntry1591Callers.exit FrontierEntry1591Kernel.exitKernel L) cx cy
        OwnDiagAll12Square.sqOff) := by
  have a1 := fastConstAdd_counts L hw L.point.x (Or.inl rfl) (-cx)
  have a2 := fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(OwnDiagAll12Square.sqOff : Nat))
  have t := tickF_counts L
  have e1 := entryM_counts L (-cx)
  have e2 := entryM_counts L (3*cx-(OwnDiagAll12Square.sqOff : Nat))
  simp only [generic,All12Generic.generic,FrontierEntry1591Callers.division,entry_split,exit_split,
    toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem gen_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+496=toffoliCount (OwnParity1591Actual.gen L cx cy) ∧
    measurementCount (gen L cx cy)+496=measurementCount (OwnParity1591Actual.gen L cx cy) := by
  have h := generic_counts L hw cx cy
  simp only [gen,OwnParity1591Actual.gen,FrontierEntry1591Point.gen,All12Generic.gen_shape,GenericQ5Geometry.wrapG,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega
end Counts

section Res2
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
attribute [local irreducible] wires fastConstAdd fastConstNeg exitY

theorem generic_sites (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset := by
  have dS := FrontierEntry1591Callers.division_support FrontierEntry1591Kernel.entryKernel
    FrontierEntry1591Kernel.entry_support L hw (-cy)
  rw [FrontierEntry1591Callers.division,entry_split] at dS
  simp only [wires_append,Finset.union_subset_iff] at dS
  have pS := FrontierEntry1591Callers.exit_support FrontierEntry1591Kernel.exitKernel
    FrontierEntry1591Kernel.exit_support L hw
  rw [exit_split] at pS
  simp only [wires_append,Finset.union_subset_iff] at pS
  have sS := PrefixFrontierSquare1591.support L hw hn
  have ey := (exitY_support L hw cy).trans (finConst_sites L hw L.point.y (Or.inr rfl))
  have cn := (All12Generic.neg_palette L hw cx).trans (finConst_sites L hw L.point.x (Or.inl rfl))
  simp only [generic,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨dS.1,entryM_sites L hw (-cx)⟩,dS.2.2⟩,sS⟩,entryM_sites L hw (3*cx-(OwnDiagAll12Square.sqOff : Nat))⟩,pS.2⟩,ey⟩,cn⟩

theorem gen_sites (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)

theorem generic_free (kk : Nat) (hk : kk∈Q1591Resources.genericOmissions) (cx cy : Fp) :
    L.core.poolWire kk∉wires (generic L cx cy) := by
  have bounds : 515≤kk ∧ kk<2613 := by
    simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  have dF := FrontierEntry1591Callers.division_free FrontierEntry1591Kernel.entryKernel
    FrontierEntry1591Kernel.entry_support FrontierEntry1591Kernel.entry_free L hw hn (-cy) kk hk
  rw [FrontierEntry1591Callers.division,entry_split] at dF
  simp only [wires_append,Finset.mem_union,not_or] at dF
  have pF := FrontierEntry1591Callers.placed_omissions FrontierEntry1591Kernel.exitKernel
    FrontierEntry1591Kernel.exit_support FrontierEntry1591Kernel.exit_free L hw hn kk hk
  change L.core.poolWire kk∉wires (FrontierEntry1591Callers.exit FrontierEntry1591Kernel.exitKernel L) at pF
  rw [exit_split] at pF
  simp only [wires_append,Finset.mem_union,not_or] at pF
  have sF := PrefixFrontierSquare1591.square_free L hw hn kk hk
  have x := ExitGenericQ5.constant_ports_avoid_large L hw hn kk bounds L.point.x (Or.inl rfl)
  have y := ExitGenericQ5.constant_ports_avoid_large L hw hn kk bounds L.point.y (Or.inr rfl)
  have cn := All12Generic.neg_palette L hw cx
  have ey := exitY_support L hw cy
  simp only [generic,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨dF.1,entryM_free L hw hn (-cx) kk hk⟩,dF.2.2⟩,sF⟩,entryM_free L hw hn (3*cx-(OwnDiagAll12Square.sqOff : Nat)) kk hk⟩,pF.2⟩,
    fun h => y (ey h)⟩,fun h => x (cn h)⟩

theorem generic_physical (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have dP := FrontierEntry1591Callers.division_physical FrontierEntry1591Kernel.entryKernel
    FrontierEntry1591Kernel.entry_support FrontierEntry1591Kernel.entry_physical L hw hn (-cy)
  rw [FrontierEntry1591Callers.division,entry_split] at dP
  simp only [gatePhysical_append] at dP
  have pP := FrontierEntry1591Callers.placed_physical FrontierEntry1591Kernel.exitKernel
    FrontierEntry1591Kernel.exit_support FrontierEntry1591Kernel.exit_physical L hw hn
  change GatePhysical (FrontierEntry1591Callers.exit FrontierEntry1591Kernel.exitKernel L) at pP
  rw [exit_split] at pP
  simp only [gatePhysical_append] at pP
  have sP := PrefixFrontierSquare1591.physical L hw hn
  have ey := exitY_physical L hw hn cy
  have cn : GatePhysical (fastConstNeg L cx) := by
    unfold fastConstNeg
    exact FastConst.fastNeg_physical (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  simp only [generic,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨dP.1,entryM_physical L hw hn (-cx)⟩,dP.2.2⟩,sP⟩,entryM_physical L hw hn (3*cx-(OwnDiagAll12Square.sqOff : Nat))⟩,pP.2⟩,ey⟩,cn⟩

theorem gen_physical (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := zrep_physical L hn
  have c := clrF_physical L hw hn
  have r := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simp only [gen,GenericQ5Geometry.wrapG,gatePhysical_append]
  exact ⟨⟨z,⟨c,r⟩,c⟩,z⟩

omit hn in
theorem generic_slots (cx cy : Fp) : gateSlots (generic L cx cy)≤49140000 := by
  have d := FrontierEntry1591Callers.division_slots FrontierEntry1591Kernel.entryKernel
    FrontierEntry1591Kernel.entry_slots L hw (-cy)
  rw [FrontierEntry1591Callers.division,entry_split] at d
  simp only [gateSlots_append] at d
  have pp := FrontierEntry1591Callers.exit_slots FrontierEntry1591Kernel.exitKernel
    FrontierEntry1591Kernel.exit_slots L
  rw [exit_split] at pp
  simp only [gateSlots_append] at pp
  have s := PrefixFrontierSquare1591.slots L hw
  have e := exitY_slots L hw cy
  have neg : gateSlots (fastConstNeg L cx) ≤ 17928 := by
    simpa only [fastConstNeg] using FastConst.fastNeg_gateSlots_le
      (g:=L.core.generic) 256 p cx.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have m1 : gateSlots (entryM L (-cx))≤25000 := by
    rw [entryM,rename_gateSlots]; exact E1Merge.merged_slots base (base 2400) (-cx).val
  have m2 : gateSlots (entryM L (3*cx-(OwnDiagAll12Square.sqOff : Nat)))≤25000 := by
    rw [entryM,rename_gateSlots]; exact E1Merge.merged_slots base (base 2400) (3*cx-(OwnDiagAll12Square.sqOff : Nat)).val
  simp only [generic,gateSlots_append]
  omega

omit hn in
theorem gen_slots (cx cy : Fp) : gateSlots (gen L cx cy)≤49240000 := by
  have g := generic_slots L hw cx cy
  have z := zrep_gateSlots_le L hw
  have c := clrF_gateSlots_le L hw
  simp only [gen,GenericQ5Geometry.wrapG,gateSlots_append,rename_gateSlots]
  omega
end Res2

theorem gen_qubits (C : Point) (cx cy : Fp) : qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1591 :=
  Q1591Resources.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy)
    (fun k hk => generic_free layout layout_widths layout_nodup k hk cx cy) C cy

end ECDSAAdd.Entrant.E1Generic
