import ECDSAAdd.Submission.Entrant.MainBase
import ECDSAAdd.Submission.Entrant.EntryStage530

open ECDSAAdd.Entrant.InverseFour15

set_option Elab.async false

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires Entry530.generic530

theorem gen_block_run530 {cx cy : Fp} (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      (Entry530.generic530 layout cx cy) (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy)))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy)))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy)))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          (Entry530.generic530 layout cx cy)))))) m t).basis q = t.basis q := by
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
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn (Entry530.generic530 layout cx cy)
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) (Entry530.generic530 layout cx cy)) m t' = R0
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
      (Entry530.generic530 layout cx cy))) m t' = R0 := by
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
      (Entry530.generic530 layout cx cy)))) m t = pullState (tauM layout) R0 := by
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
        (Entry530.generic530 layout cx cy))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy)))))) m t = pullState (tauM layout) R0 := by
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

end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires Entry530.generic530

def genBlock530 (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (Entry530.generic530 L cx cy))
def finiteProgram530 (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlock530 L cx cy))) ++ InputSentinel.outStage L C
def wrapper530 (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram530 L C cx cy)

open Classical in
theorem finite530_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgram530 layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgram530 layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgram530
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
      (genBlock530 layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlock530 layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlock530 layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlock530 layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock530 layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlock530 layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlock530
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run530 x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => Entry530.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run530 (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => Entry530.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run530 x y x y false
        (fun base' => Entry530.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper530_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapper530 layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite530_run hc b R s m hs
  unfold wrapper530
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h


end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout InputSentinel
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires

theorem predec_wire530 (tr : Tri) (yc : Bool) (g c x y z O D H : Wire) :
    O ∈ wires (predecL tr yc g c x y z O D H) := by
  have key : (5:Wire) ∈ wires (predecT tr yc) := by
    unfold predecT
    split <;> simp only [predec1,predec2,wires_append,Finset.mem_union] <;>
      simp [wires,Instr.wires]
  unfold predecL
  rw [renameProgram_support]
  apply Finset.mem_image.mpr
  refine ⟨5,key,?_⟩
  simp [LocalWireModel.label]

theorem out_wire530 (C : Point) : parkWire layout ∈ wires (InputSentinel.outStage layout C) := by
  unfold InputSentinel.outStage
  rw [wires_append,wires_append,wires_append]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact predec_wire530 _ _ _ _ _ _ _ _ _ _

theorem wrapper_wire530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    (4629:Wire) ∈ wires (wrapper2 layout (.some hc) cx cy) := by
  unfold wrapper2
  rw [renameProgram_support]
  apply Finset.mem_image.mpr
  refine ⟨parkWire layout,?_,?_⟩
  · unfold finiteProgram2
    rw [wires_append,wires_append]
    exact Finset.mem_union_right _ (out_wire530 (.some hc))
  · decide +kernel

end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.Entry530
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap ReflectionE1TickGapLow48 OB5 Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  InverseFour15.lastPhase15 Rolling1588.lastPhase Rolling1588TickGap.tailPhase

theorem restE_extra530 (L : ControlledPointLayout) :
    wires (restE530 L) ⊆ wires (ReflectionE1TickGap.restE L) ∪ {wireFn2 L 530} := by
  have inner := InverseFour15.hosted_extra530 false
  unfold restE530 ReflectionE1TickGap.restE
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  simp only [wires_append,Finset.mem_union] at hv
  rcases hv with first | field | last
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨v,?_,rfl⟩
    simp only [wires_append,Finset.mem_union]
    exact Or.inl first
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨v,?_,rfl⟩
    simp only [wires_append,Finset.mem_union]
    exact Or.inr (Or.inl field)
  · rcases Finset.mem_union.mp (inner last) with old | extra
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨v,?_,rfl⟩
      simp only [wires_append,Finset.mem_union]
      exact Or.inr (Or.inr old)
    · simp only [Finset.mem_singleton] at extra
      subst v
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

theorem generic_extra530 (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic530 L cx cy) ⊆
      wires (ReflectionE1TickGapLow48.generic L cx cy) ∪ {wireFn2 L 530} := by
  have h := restE_extra530 L
  intro q hq
  simp only [generic530,entryStage530,ReflectionE1TickGapLow48.generic,
    ReflectionE1TickGap.entryStage,wires_append,Finset.mem_union] at hq ⊢
  rcases hq with (((hy | hm) | he) | hs)
  · exact Or.inl (Or.inl (Or.inl (Or.inl hy)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hm)))
  · rcases Finset.mem_union.mp (h he) with old | extra
    · exact Or.inl (Or.inl (Or.inr old))
    · exact Or.inr extra
  · exact Or.inl (Or.inr hs)
end ECDSAAdd.Entrant.Entry530

namespace ECDSAAdd.Entrant.Entry530
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap ReflectionE1TickGapLow48 OB5 Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  Rolling1588.stackReverse Rolling1588.lastPhase InverseFour15.stackReverse15 InverseFour15.reverseTail15 InverseFour15.lastPhase15 candidate15 old15

theorem old_metrics530 : toffoliCount old15 = 16 ∧ measurementCount old15 = 11 ∧ gateSlots old15 = 289 := by decide +kernel

theorem reverse_metrics530 (isA : Bool) :
    toffoliCount (InverseFour15.stackReverse15 isA) + 1 = toffoliCount (Rolling1588.stackReverse isA) ∧
    measurementCount (InverseFour15.stackReverse15 isA) = measurementCount (Rolling1588.stackReverse isA) ∧
    gateSlots (InverseFour15.stackReverse15 isA) = gateSlots (Rolling1588.stackReverse isA) + 425 := by
  have old := old_metrics530
  have fresh := InverseFour15.resources
  rw [InverseFour15.reverse_shape15]
  simp only [InverseFour15.stackReverse15,InverseFour15.reverseTail15,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots] at *
  omega

theorem last_metrics530 (isA : Bool) :
    toffoliCount (InverseFour15.lastPhase15 isA) + 1 = toffoliCount (Rolling1588.lastPhase isA) ∧
    measurementCount (InverseFour15.lastPhase15 isA) = measurementCount (Rolling1588.lastPhase isA) ∧
    gateSlots (InverseFour15.lastPhase15 isA) = gateSlots (Rolling1588.lastPhase isA) + 425 := by
  have h := reverse_metrics530 isA
  simp only [InverseFour15.lastPhase15,Rolling1588.lastPhase,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem restE_metrics530 (L : ControlledPointLayout) :
    toffoliCount (restE530 L) + 1 = toffoliCount (ReflectionE1TickGap.restE L) ∧
    measurementCount (restE530 L) = measurementCount (ReflectionE1TickGap.restE L) ∧
    gateSlots (restE530 L) = gateSlots (ReflectionE1TickGap.restE L) + 425 := by
  have h := last_metrics530 false
  simp only [restE530,ReflectionE1TickGap.restE,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega

theorem generic_metrics530 (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (generic530 L cx cy) + 1 = toffoliCount (ReflectionE1TickGapLow48.generic L cx cy) ∧
    measurementCount (generic530 L cx cy) = measurementCount (ReflectionE1TickGapLow48.generic L cx cy) ∧
    gateSlots (generic530 L cx cy) = gateSlots (ReflectionE1TickGapLow48.generic L cx cy) + 425 := by
  have h := restE_metrics530 L
  simp only [generic530,entryStage530,ReflectionE1TickGapLow48.generic,
    ReflectionE1TickGap.entryStage,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega
end ECDSAAdd.Entrant.Entry530

namespace ECDSAAdd.Entrant.Entry530
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap ReflectionE1TickGapLow48 OB5 Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  InverseFour15.lastPhase15 Rolling1588.lastPhase Rolling1588TickGap.tailPhase

theorem restE_physical530 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restE530 L) := by
  have p := placed_physical InverseFour15.entryKernel15 InverseFour15.entry_support530 InverseFour15.entry_physical15 L hw hn
  have entryP : GatePhysical (FrontierEntry1591Callers.entry InverseFour15.entryKernel15 L) := by
    simpa only [FrontierEntry1591Callers.entry] using p
  rw [entry_split530,gatePhysical_append] at entryP
  exact entryP.2

theorem generic_physical530 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic530 L cx cy) := by
  have old := ReflectionE1TickGapLow48.generic_physical L hw hn cx cy
  simp only [ReflectionE1TickGapLow48.generic,ReflectionE1TickGap.entryStage,gatePhysical_append] at old
  simp only [generic530,entryStage530,gatePhysical_append]
  exact ⟨⟨⟨old.1.1.1,old.1.1.2⟩,restE_physical530 L hw hn⟩,old.2⟩
end ECDSAAdd.Entrant.Entry530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Entry530.generic530 ReflectionE1TickGapLow48.generic

private theorem mapped_extra530 (f : Wire → Wire) (P Q : Program) (e : Wire)
    (h : wires P ⊆ wires Q ∪ {e}) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) ∪ {f e} := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (h hv) with old | extra
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ old)
  · simp only [Finset.mem_singleton] at extra
    subst v
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

private theorem context_extra530 (A P Q B : Program) (e : Wire)
    (h : wires P ⊆ wires Q ∪ {e}) :
    wires (A ++ P ++ B) ⊆ wires (A ++ Q ++ B) ∪ {e} := by
  intro q hq
  simp only [wires_append,Finset.mem_union] at hq ⊢
  rcases hq with (ha | hp) | hb
  · exact Or.inl (Or.inl (Or.inl ha))
  · rcases Finset.mem_union.mp (h hp) with ho | he
    · exact Or.inl (Or.inl (Or.inr ho))
    · exact Or.inr he
  · exact Or.inl (Or.inr hb)

theorem wrapper_extra530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper530 layout (.some hc) cx cy) ⊆
      wires (wrapper2 layout (.some hc) cx cy) ∪ {4629} := by
  have h0 := Entry530.generic_extra530 layout cx cy
  have h1 := mapped_extra530 (swapF layout) _ _ _ h0
  have h2 := mapped_extra530 (Wrapper5.U layout) _ _ _ h1
  have h3 := mapped_extra530 (tauM layout) _ _ _ h2
  have h4 := mapped_extra530 (swapE layout) _ _ _ h3
  have h5 := mapped_extra530 (swapD layout) _ _ _ h4
  have h6 := context_extra530 (InputSentinel.stage layout (.some hc)) _ _
    (InputSentinel.outStage layout (.some hc)) _ h5
  have h7 := mapped_extra530 (Wrapper5.U layout) _ _ _ h6
  have e : Wrapper5.U layout (swapD layout (swapE layout (tauM layout
      (Wrapper5.U layout (swapF layout (wireFn2 layout 530)))))) = 4629 := by decide +kernel
  simpa only [wrapper530,finiteProgram530,genBlock530,wrapper2,finiteProgram2,genBlock,e] using h7

theorem wrapper_support530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper530 layout (.some hc) cx cy) ⊆ wires (wrapper2 layout (.some hc) cx cy) := by
  intro q hq
  rcases Finset.mem_union.mp (wrapper_extra530 hc hq) with old | extra
  · exact old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact wrapper_wire530 hc

theorem support_used530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper530 layout (.some hc) cx cy) ⊆ layout.dialogUsedWires.toFinset :=
  (wrapper_support530 hc).trans (InputSentinel.support2_used hc)
end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Entry530 Challenge
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  Entry530.generic530 ReflectionE1TickGapLow48.generic

theorem wrapper_metrics530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapper530 layout (.some hc) cx cy) + 1 = toffoliCount (wrapper2 layout (.some hc) cx cy) ∧
    measurementCount (wrapper530 layout (.some hc) cx cy) = measurementCount (wrapper2 layout (.some hc) cx cy) ∧
    gateSlots (wrapper530 layout (.some hc) cx cy) = gateSlots (wrapper2 layout (.some hc) cx cy) + 425 := by
  have h := Entry530.generic_metrics530 layout cx cy
  simp only [wrapper530,finiteProgram530,genBlock530,wrapper2,finiteProgram2,genBlock,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega
end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Entry530 Challenge
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  Entry530.generic530 ReflectionE1TickGapLow48.generic

theorem wrapper_physical530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapper530 layout (.some hc) cx cy) := by
  have p0 := Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapper530
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgram530,genBlock530,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,InputSentinel.outStage_physical hc⟩
end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Entry530 Challenge
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  Entry530.generic530 ReflectionE1TickGapLow48.generic

open Classical in
theorem full_spec530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapper530 layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz : regValue layout.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi : PointDialogBoundary layout R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  have c2 := wrapper530_spec hc b R s m hi
  have a : (run (wrapper' layout (.some hc) (tailGen layout cx cy)) m s).phase = s.phase ∧
      PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
        (run (wrapper' layout (.some hc) (tailGen layout cx cy)) m s).basis := by
    rw [wrapper'_eq hc b R s m hi]
    exact FusedFlags.wrapper_spec layout layout_widths layout_nodup R hc b _
      (CodexYParityProbe.genFFused_ok layout layout_widths layout_nodup hc) s _ hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used530 hc) (support_used' hc) s m _ b c2.2 a.2
    (c2.1.trans a.1.symm)]
  exact full_spec' hc b R s m hs


def program530 (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => wrapper530 layout C cx cy

def entry530 : Challenge.Entry := fun C => normalizeProgram (program530 C)
def bounds530 : Challenge.Bounds := ⟨2150549,1498370,1587,50245837⟩

theorem program_correct530 (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program530 C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program530,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    exact fixed_correct _ control R _ (full_spec530 hc control R) (support_used530 hc)

theorem program_toffoli530 (C : Point) : toffoliCount (program530 C) ≤ 2150549 := by
  cases C with
  | zero => simp [program530, toffoliCount]
  | @some cx cy hc =>
    have old := InputSentinel.program2_toffoli (.some hc)
    have delta := (wrapper_metrics530 hc).1
    change toffoliCount (wrapper2 layout (.some hc) cx cy) ≤ 2150550 at old
    change toffoliCount (wrapper530 layout (.some hc) cx cy) ≤ 2150549
    omega

theorem program_measurements530 (C : Point) : measurementCount (program530 C) ≤ 1498370 := by
  cases C with
  | zero => simp [program530, measurementCount]
  | @some cx cy hc =>
    have old := InputSentinel.program2_measurements (.some hc)
    have delta := (wrapper_metrics530 hc).2.1
    change measurementCount (wrapper2 layout (.some hc) cx cy) ≤ 1498370 at old
    change measurementCount (wrapper530 layout (.some hc) cx cy) ≤ 1498370
    omega

theorem program_qubits530 (C : Point) : qubits (program530 C) ≤ 1587 := by
  cases C with
  | zero => change qubits [] ≤ 1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have old := InputSentinel.program2_qubits (.some hc)
    have sub := wrapper_support530 hc
    change qubits (wrapper2 layout (.some hc) cx cy) ≤ 1587 at old
    change qubits (wrapper530 layout (.some hc) cx cy) ≤ 1587
    refine le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) sub

theorem program_physical530 (C : Point) : GatePhysical (program530 C) := by
  cases C with
  | zero => simp [program530,GatePhysical]
  | @some cx cy hc => exact wrapper_physical530 hc

theorem program_slots530 (C : Point) : gateSlots (program530 C) ≤ 50245837 := by
  cases C with
  | zero => simp [program530]
  | @some cx cy hc =>
    have old := InputSentinel.program2_gateSlots (.some hc)
    have delta := (wrapper_metrics530 hc).2.2
    change gateSlots (wrapper2 layout (.some hc) cx cy) ≤ 50245412 at old
    change gateSlots (wrapper530 layout (.some hc) cx cy) ≤ 50245837
    omega

theorem certificate530 : Challenge.Certificate entry530 bounds530 where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct530 C control R)
  physical C := normalize_physical _ (program_physical530 C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli530 C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program530 C)) ≤ 1498370
    rw [normalize_measurements]; exact program_measurements530 C
  qubits_le C := by
    change qubits (normalizeProgram (program530 C)) ≤ 1587
    rw [normalize_qubits]; exact program_qubits530 C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program530 C)) ≤ 50245837
    rw [normalize_slots]; exact program_slots530 C
end ECDSAAdd.Entrant.InputSentinel530

