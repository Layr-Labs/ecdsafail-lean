import ECDSAAdd.Submission.Entrant.ParityFinalBothInverse23XY

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
def boundsOpt : Challenge.Bounds := ⟨2150524,1498370,1587,50250310⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150524 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150531 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150524
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

theorem program_slots (C : Point) : gateSlots (programOpt C)≤50250310 := by
  cases C with
  | zero=>simp [programOpt]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_slots530 (.some hc)
    have delta:=(wrapper_metrics hc).2.2
    change gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤50249996 at old
    change gateSlots (wrapperOpt layout (.some hc) cx cy)≤50250310
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
    change gateSlots (normalizeProgram (programOpt C))≤50250310
    rw [normalize_slots];exact program_slots C

end ECDSAAdd.Entrant.ParityFinalBothInverse23Out
