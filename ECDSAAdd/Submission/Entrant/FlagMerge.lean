import ECDSAAdd.Submission.Entrant.FastE
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SlotMapped

/-! Flag merge on top of `FlagG`.

* While the generic-branch block runs, its control bit is held in
  `genericSelect`: `genFlagN` folds `(b ∧ finite) ⊕ D ⊕ H` into the
  inverse-point flag (the classes are exclusive, so the result is the generic
  bit), the block runs with `core.generic` and `genericSelect` exchanged, and
  the same gates restore the flag.
* The infinity flag of the output stage (`FlagG` keeps it on `core.generic`)
  lives on pool site 514 instead: that stage is relabelled with
  `core.generic ↔ poolWire 514`.  The stage uses only the first 256 pool sites.

Neither `core.generic` nor `infinitySelect` is used, which removes one more site. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

/-- Exchange of `core.generic` and `genericSelect`. -/
def tauM (L : ControlledPointLayout) (q : Wire) : Wire :=
  if q = L.core.generic then L.genericSelect else if q = L.genericSelect then L.core.generic else q

/-- The pool site that carries the output-stage infinity flag. -/
def parkWire (L : ControlledPointLayout) : Wire := L.core.poolWire 514

/-- Exchange of `core.generic` and the park site. -/
def sigP (L : ControlledPointLayout) (q : Wire) : Wire :=
  if q = L.core.generic then parkWire L else if q = parkWire L then L.core.generic else q

/-- A pool site used only by the generic block; it is relabelled onto
`equalNegY`, which is cleared while the block runs. -/
def spareWire (L : ControlledPointLayout) : Wire := L.core.poolWire 684

/-- Exchange of `equalNegY` and the spare site. -/
def swapE (L : ControlledPointLayout) (q : Wire) : Wire :=
  if q = L.core.equalNegY then spareWire L else if q = spareWire L then L.core.equalNegY else q

/-- `control ^= H`, `double ^= H`, then `H ^= ¬control ∧ double` clears `H`
(the exception class implies `b` and excludes the doubling class). -/
def foldH (L : ControlledPointLayout) : Program :=
  [.CX L.core.equalNegY L.control, .CX L.core.equalNegY L.doubleSelect, .X L.control,
   .CCX L.control L.doubleSelect L.core.equalNegY, .X L.control]

def unfoldH (L : ControlledPointLayout) : Program :=
  [.X L.control, .CCX L.control L.doubleSelect L.core.equalNegY, .X L.control,
   .CX L.core.equalNegY L.doubleSelect, .CX L.core.equalNegY L.control]

/-- `genericSelect ^= (b ∧ finite) ⊕ D ⊕ H`. -/
def genFlagN (L : ControlledPointLayout) : Program :=
  [.CCX L.control L.point.finite L.genericSelect, .CX L.doubleSelect L.genericSelect,
   .CX L.core.equalNegY L.genericSelect]

/-- The output stage of `finiteProgramFG` that holds the infinity flag. -/
def outStage (L : ControlledPointLayout) (C : Point) : Program :=
  zeroFlag L.point.finite L.control L.core.generic ++ corners2 L C ++
  pairEqual L L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)

def finiteProgramN (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  gatedShort L (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C) ++
  genFlagN L ++ foldH L ++ renameProgram (swapE L) (renameProgram (tauM L) Gen) ++ unfoldH L ++
  genFlagN L ++
  renameProgram (sigP L) (outStage L C) ++
  gatedShort L (decide (cy≠-cy)) L.doubleSelect (C+C) ++
  chainErase L.control L.point.finite L.genericSelect

def flagsN (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.genericSelect, L.core.equalNegY]

/-- The pool inventory without the spare site 684. -/
def sharedPoolF2 (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515 ++ wireBlock L.core.poolWire 685 856 ++
    [L.core.poolWire 1800] ++ wireBlock L.core.poolWire 1802 3

def sitesN (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsN L ++ sharedPoolF2 L

/-- Sites of the relabelled generic block before the spare exchange. -/
def sitesNx (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ [L.doubleSelect, L.genericSelect] ++ sharedPoolF L

def flagsG (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.core.generic]

/-- Sites of the generic block: it never touches `genericSelect`. -/
def sitesG (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsG L ++ sharedPoolF L

theorem sitesN_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesN L).length = 1892 := by
  simp [sitesN, flagsN, sharedPoolF2, PointAddLayout.pointWires, wireBlock_length,
    show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]

section Tau
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem generic_ne_select : L.core.generic ≠ L.genericSelect := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  tauto

theorem tauM_invol (q : Wire) : tauM L (tauM L q) = q := by
  have ne := generic_ne_select L hn
  unfold tauM
  by_cases h1 : q = L.core.generic
  · subst h1; simp [ne, ne.symm]
  · by_cases h2 : q = L.genericSelect
    · subst h2; simp [ne, ne.symm]
    · simp [h1, h2]

theorem tauM_injective : Function.Injective (tauM L) := by
  intro a b h
  have := congrArg (tauM L) h
  rwa [tauM_invol L hn, tauM_invol L hn] at this

omit hn in
theorem tauM_fix (q : Wire) (hq : q ∉ L.inPlaceFlags) : tauM L q = q := by
  have h1 : q ≠ L.core.generic := fun h => hq (by simp [h, inPlaceFlags])
  have h2 : q ≠ L.genericSelect := fun h => hq (by simp [h, inPlaceFlags])
  simp [tauM, h1, h2]

omit hn in
theorem tauM_flag (q : Wire) (hq : q ∈ L.inPlaceFlags) : tauM L q ∈ L.inPlaceFlags := by
  unfold tauM
  split_ifs
  · simp [inPlaceFlags]
  · simp [inPlaceFlags]
  · exact hq

theorem boundary_tau {R : Point} {b : Bool} {f s : BasisState} (v : PointDialogBoundary L R b f s) :
    PointDialogBoundary L R b (fun q => f (tauM L q)) (fun q => s (tauM L q)) :=
  v.withFlags hn (fun q hq => v.flags _ (tauM_flag L q hq)) (fun q hq => by rw [tauM_fix L q hq])

/-- The relabelled generic block, controlled by `genericSelect`. -/
theorem genericM_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (Gen : Program)
    (hGen : GenericOK L hc Gen) (R : Point) (b : Bool) (f : BasisState)
    (hg : f L.genericSelect = true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (renameProgram (tauM L) Gen)
      (PointDialogBoundary L (if f L.genericSelect then R+.some hc else R) b f) := by
  intro s m v
  have tg : tauM L L.core.generic = L.genericSelect := by simp [tauM]
  have h := hGen R b (fun q => f (tauM L q)) (by intro e; apply hg; simpa only [tg] using e)
    (pullState (tauM L) s) m (boundary_tau L hn v)
  rw [← run_rename (tauM L) (tauM_injective L hn)] at h
  simp only [tg] at h
  refine ⟨h.1, ?_⟩
  have back := boundary_tau L hn h.2
  simp only [pullState, tauM_invol L hn] at back
  exact back

end Tau

section Park
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem park_pool : parkWire L ∈ L.dialogPool := by
  have h : parkWire L ∈ L.dialogPool.take 515 := by
    rw [pool_block L hw 515 (by omega)]
    simp [parkWire, wireBlock, List.mem_map, List.mem_range'_1]
    exact ⟨514, by omega, rfl⟩
  exact List.mem_of_mem_take h

theorem park_away : parkWire L ∉ PointAddLayout.pointWires L.point ∧ parkWire L ≠ L.control ∧
    parkWire L ∉ L.inPlaceFlags := by
  have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) (parkWire L)
  have hp := List.count_pos_iff.mpr (park_pool L hw)
  simp only [dialogUsedWires, List.count_append] at used
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := List.count_pos_iff.mpr h; omega
  · have : 0 < List.count (parkWire L) [L.control] := List.count_pos_iff.mpr (by simp [h])
    omega
  · have := List.count_pos_iff.mpr h; omega

theorem park_ne_generic : parkWire L ≠ L.core.generic :=
  fun h => (park_away L hw hn).2.2 (by simp [h, inPlaceFlags])

theorem sigP_invol (q : Wire) : sigP L (sigP L q) = q := by
  have ne := park_ne_generic L hw hn
  unfold sigP
  by_cases h1 : q = L.core.generic
  · subst h1; simp [ne, ne.symm]
  · by_cases h2 : q = parkWire L
    · subst h2; simp [ne, ne.symm]
    · simp [h1, h2]

theorem sigP_injective : Function.Injective (sigP L) := by
  intro a b h
  have := congrArg (sigP L) h
  rwa [sigP_invol L hw hn, sigP_invol L hw hn] at this

/-- Relabelling the park site keeps the boundary when the generic flag is clear. -/
theorem boundary_sig {R : Point} {b : Bool} {f s : BasisState} (v : PointDialogBoundary L R b f s)
    (hf : f L.core.generic = false) :
    PointDialogBoundary L R b f (fun q => s (sigP L q)) := by
  have aw := park_away L hw hn
  have ng := park_ne_generic L hw hn
  have fix (q : Wire) (h1 : q ≠ L.core.generic) (h2 : q ≠ parkWire L) : sigP L q = q := by
    simp [sigP, h1, h2]
  have gpt : L.core.generic ∉ PointAddLayout.pointWires L.point := by
    intro h
    have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
    have a := List.count_pos_iff.mpr h
    have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
    simp only [dialogUsedWires, List.count_append] at used
    omega
  have hpt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : sigP L q = q :=
    fix q (fun e => gpt (e ▸ hq)) (fun e => aw.1 (e ▸ hq))
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨(point_holds _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpt _ (by simp [PointAddLayout.pointWires])]; exact hp.1
  · rw [regValue_congr L.point.x _ s (fun q hq => by
      rw [hpt q (by simp [PointAddLayout.pointWires, hq])])]; exact hp.2.1
  · rw [regValue_congr L.point.y _ s (fun q hq => by
      rw [hpt q (by simp [PointAddLayout.pointWires, hq])])]; exact hp.2.2
  · have sep := dialogFlag_separation L hn
    have cg : L.control ≠ L.core.generic := by
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep; tauto
    show s (sigP L L.control) = b
    rw [fix _ cg (fun e => aw.2.1 e.symm)]; exact v.control
  · intro q hq
    show s (sigP L q) = f q
    by_cases hg : q = L.core.generic
    · subst hg
      simp only [sigP, if_true]
      rw [hf]
      exact (regValue_zero _ _).mp v.clean _ (park_pool L hw)
    · rw [fix q hg (fun e => aw.2.2 (e ▸ hq))]; exact v.flags q hq
  · apply (regValue_zero _ _).mpr
    intro q hq
    show s (sigP L q) = false
    by_cases hk : q = parkWire L
    · subst hk
      simp only [sigP, if_neg (park_ne_generic L hw hn), if_true]
      rw [v.flags _ (by simp [inPlaceFlags]), hf]
    · have hg : q ≠ L.core.generic := by
        intro e; subst e
        have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
        have a := List.count_pos_iff.mpr hq
        have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
        simp only [dialogUsedWires, List.count_append] at used
        omega
      rw [fix q hg hk]
      exact (regValue_zero _ _).mp v.clean q hq

theorem park_triple (X : Program) (R R' : Point) (b : Bool) (f f' : BasisState)
    (hf : f L.core.generic = false) (hf' : f' L.core.generic = false)
    (hX : Triple (PointDialogBoundary L R b f) X (PointDialogBoundary L R' b f')) :
    Triple (PointDialogBoundary L R b f) (renameProgram (sigP L) X) (PointDialogBoundary L R' b f') := by
  intro s m v
  have h := hX (pullState (sigP L) s) m (boundary_sig L hw hn v hf)
  rw [← run_rename (sigP L) (sigP_injective L hw hn)] at h
  refine ⟨h.1, ?_⟩
  have back := boundary_sig L hw hn h.2 hf'
  simp only [pullState, sigP_invol L hw hn] at back
  exact back

end Park

section Spare
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem spare_pool : spareWire L ∈ L.dialogPool := by
  apply sharedPool_Q_sub L hw
  simp [spareWire, sharedPoolF, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inr (Or.inl ⟨684, by omega, rfl⟩)

theorem spare_away : spareWire L ∉ PointAddLayout.pointWires L.point ∧ spareWire L ≠ L.control ∧
    spareWire L ∉ L.inPlaceFlags := by
  have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) (spareWire L)
  have hp := List.count_pos_iff.mpr (spare_pool L hw)
  simp only [dialogUsedWires, List.count_append] at used
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := List.count_pos_iff.mpr h; omega
  · have : 0 < List.count (spareWire L) [L.control] := List.count_pos_iff.mpr (by simp [h])
    omega
  · have := List.count_pos_iff.mpr h; omega

theorem spare_ne_exc : spareWire L ≠ L.core.equalNegY :=
  fun h => (spare_away L hw hn).2.2 (by simp [h, inPlaceFlags])

theorem swapE_invol (q : Wire) : swapE L (swapE L q) = q := by
  have ne := spare_ne_exc L hw hn
  unfold swapE
  by_cases h1 : q = L.core.equalNegY
  · subst h1; simp [ne, ne.symm]
  · by_cases h2 : q = spareWire L
    · subst h2; simp [ne, ne.symm]
    · simp [h1, h2]

theorem swapE_injective : Function.Injective (swapE L) := by
  intro a b h
  have := congrArg (swapE L) h
  rwa [swapE_invol L hw hn, swapE_invol L hw hn] at this

/-- Relabelling the park site keeps the boundary when the generic flag is clear. -/
theorem boundary_swapE {R : Point} {b : Bool} {f s : BasisState} (v : PointDialogBoundary L R b f s)
    (hf : f L.core.equalNegY = false) :
    PointDialogBoundary L R b f (fun q => s (swapE L q)) := by
  have aw := spare_away L hw hn
  have ng := spare_ne_exc L hw hn
  have fix (q : Wire) (h1 : q ≠ L.core.equalNegY) (h2 : q ≠ spareWire L) : swapE L q = q := by
    simp [swapE, h1, h2]
  have gpt : L.core.equalNegY ∉ PointAddLayout.pointWires L.point := by
    intro h
    have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
    have a := List.count_pos_iff.mpr h
    have c : 0 < List.count L.core.equalNegY L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
    simp only [dialogUsedWires, List.count_append] at used
    omega
  have hpt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : swapE L q = q :=
    fix q (fun e => gpt (e ▸ hq)) (fun e => aw.1 (e ▸ hq))
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨(point_holds _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpt _ (by simp [PointAddLayout.pointWires])]; exact hp.1
  · rw [regValue_congr L.point.x _ s (fun q hq => by
      rw [hpt q (by simp [PointAddLayout.pointWires, hq])])]; exact hp.2.1
  · rw [regValue_congr L.point.y _ s (fun q hq => by
      rw [hpt q (by simp [PointAddLayout.pointWires, hq])])]; exact hp.2.2
  · have sep := dialogFlag_separation L hn
    have cg : L.control ≠ L.core.equalNegY := by
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep; tauto
    show s (swapE L L.control) = b
    rw [fix _ cg (fun e => aw.2.1 e.symm)]; exact v.control
  · intro q hq
    show s (swapE L q) = f q
    by_cases hg : q = L.core.equalNegY
    · subst hg
      simp only [swapE, if_true]
      rw [hf]
      exact (regValue_zero _ _).mp v.clean _ (spare_pool L hw)
    · rw [fix q hg (fun e => aw.2.2 (e ▸ hq))]; exact v.flags q hq
  · apply (regValue_zero _ _).mpr
    intro q hq
    show s (swapE L q) = false
    by_cases hk : q = spareWire L
    · subst hk
      simp only [swapE, if_neg (spare_ne_exc L hw hn), if_true]
      rw [v.flags _ (by simp [inPlaceFlags]), hf]
    · have hg : q ≠ L.core.equalNegY := by
        intro e; subst e
        have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
        have a := List.count_pos_iff.mpr hq
        have c : 0 < List.count L.core.equalNegY L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
        simp only [dialogUsedWires, List.count_append] at used
        omega
      rw [fix q hg hk]
      exact (regValue_zero _ _).mp v.clean q hq

theorem spare_triple (X : Program) (R R' : Point) (b : Bool) (f f' : BasisState)
    (hf : f L.core.equalNegY = false) (hf' : f' L.core.equalNegY = false)
    (hX : Triple (PointDialogBoundary L R b f) X (PointDialogBoundary L R' b f')) :
    Triple (PointDialogBoundary L R b f) (renameProgram (swapE L) X) (PointDialogBoundary L R' b f') := by
  intro s m v
  have h := hX (pullState (swapE L) s) m (boundary_swapE L hw hn v hf)
  rw [← run_rename (swapE L) (swapE_injective L hw hn)] at h
  refine ⟨h.1, ?_⟩
  have back := boundary_swapE L hw hn h.2 hf'
  simp only [pullState, swapE_invol L hw hn] at back
  exact back

/-- The generic block, relabelled onto `genericSelect` and the cleared exception wire. -/
theorem genericE_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (Gen : Program)
    (hGen : GenericOK L hc Gen) (R : Point) (b : Bool) (f : BasisState)
    (hg : f L.genericSelect = true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc))
    (hx : f L.core.equalNegY = false) :
    Triple (PointDialogBoundary L R b f) (renameProgram (swapE L) (renameProgram (tauM L) Gen))
      (PointDialogBoundary L (if f L.genericSelect then R+.some hc else R) b f) :=
  spare_triple L hw hn _ R _ b f f hx hx (genericM_ok L hn hc Gen hGen R b f hg)

end Spare

section Flags
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem genFlagN_run (s : State) (m : List Bool) :
    run (genFlagN L) m s = ⟨s.phase, writeBit s.basis L.genericSelect
      (((s.basis L.genericSelect ^^ (s.basis L.control && s.basis L.point.finite)) ^^
        s.basis L.doubleSelect) ^^ s.basis L.core.equalNegY)⟩ := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hfin : L.point.finite ∉ L.control :: L.inPlaceFlags := by
    have hh := List.nodup_iff_count_le_one.mp (L.dialogUsed_nodup hn) L.point.finite
    have hp : 1 ≤ (PointAddLayout.pointWires L.point).count L.point.finite :=
      List.count_pos_iff.mpr (by simp [PointAddLayout.pointWires])
    simp only [dialogUsedWires, List.count_append] at hh
    have hc : (L.control :: L.inPlaceFlags).count L.point.finite = 0 := by
      show ([L.control] ++ L.inPlaceFlags).count _ = 0
      rw [List.count_append]; omega
    exact List.count_eq_zero.mp hc
  simp only [inPlaceFlags, List.mem_cons, not_or] at hfin
  have h1 : L.control ≠ L.genericSelect := by tauto
  have h2 : L.point.finite ≠ L.genericSelect := by tauto
  have h3 : L.doubleSelect ≠ L.genericSelect := by tauto
  have h5 : L.core.equalNegY ≠ L.genericSelect := by tauto
  simp only [genFlagN, run]
  congr 1
  funext q
  by_cases hq : q = L.genericSelect
  · subst hq; simp [writeBit, h1, h2, h3, h5]
  · simp [writeBit, hq]

theorem genFlagN_flag (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K)) (genFlagN L)
      (PointDialogBoundary L R b (dialogFlagState L O D
        (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) G E H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  intro s m v
  have hh := genFlagN_run L hn s m
  have hfin : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have rd (q : Wire) (hq : q ∈ L.inPlaceFlags) : s.basis q = dialogFlagState L O D I G E H K q := v.flags q hq
  have eD := rd L.doubleSelect (by simp [inPlaceFlags])
  have eI := rd L.genericSelect (by simp [inPlaceFlags])
  have eH := rd L.core.equalNegY (by simp [inPlaceFlags])
  rw [hr.2.1] at eD; rw [hr.2.2.1] at eI; rw [hr.2.2.2.2.2.1] at eH
  rw [eD, eI, eH, hfin, v.control] at hh
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    have u := (dialogFlagState_update L hn O D I G E H K
      (((I ^^ (b && pointFinite R)) ^^ D) ^^ H)).2.2.1 q hq
    rw [← u]
    by_cases he : q = L.genericSelect
    · subst he; simp [writeBit]
    · simp [writeBit, he, rd q hq]
  · intro q hq
    rw [hh]
    have hqt : q ≠ L.genericSelect := fun he => hq (he ▸ by simp [inPlaceFlags])
    simp [writeBit, hqt]

end Flags

section Fold
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem fold_distinct : L.core.equalNegY ≠ L.control ∧ L.core.equalNegY ≠ L.doubleSelect ∧
    L.control ≠ L.doubleSelect := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  refine ⟨?_, ?_, ?_⟩ <;> intro e <;> simp_all

theorem foldH_run (s : State) (m : List Bool) :
    run (foldH L) m s = ⟨s.phase, fun q =>
      if q = L.control then (s.basis L.control ^^ s.basis L.core.equalNegY)
      else if q = L.doubleSelect then (s.basis L.doubleSelect ^^ s.basis L.core.equalNegY)
      else if q = L.core.equalNegY then (s.basis L.core.equalNegY ^^
        (!(s.basis L.control ^^ s.basis L.core.equalNegY) &&
          (s.basis L.doubleSelect ^^ s.basis L.core.equalNegY)))
      else s.basis q⟩ := by
  obtain ⟨h1, h2, h3⟩ := fold_distinct L hn
  simp only [foldH, run]
  congr 1
  funext q
  by_cases hc : q = L.control <;> by_cases hd : q = L.doubleSelect <;>
    by_cases he : q = L.core.equalNegY <;>
    simp_all [writeBit, Function.update_apply, eq_comm]

theorem unfoldH_run (s : State) (m : List Bool) :
    run (unfoldH L) m s = ⟨s.phase, fun q =>
      let e := (s.basis L.core.equalNegY ^^ (!s.basis L.control && s.basis L.doubleSelect))
      if q = L.control then (s.basis L.control ^^ e)
      else if q = L.doubleSelect then (s.basis L.doubleSelect ^^ e)
      else if q = L.core.equalNegY then e
      else s.basis q⟩ := by
  obtain ⟨h1, h2, h3⟩ := fold_distinct L hn
  simp only [unfoldH, run]
  congr 1
  funext q
  by_cases hc : q = L.control <;> by_cases hd : q = L.doubleSelect <;>
    by_cases he : q = L.core.equalNegY <;>
    simp_all [writeBit, Function.update_apply, eq_comm]

/-- A state that changes only control and flags keeps the point and the pool. -/
theorem boundary_upd {R : Point} {b b' : Bool} {f f' s t : BasisState}
    (v : PointDialogBoundary L R b f s)
    (ht : ∀ q, q ≠ L.control → q ∉ L.inPlaceFlags → t q = s q) (hc : t L.control = b')
    (hf : ∀ q ∈ L.inPlaceFlags, t q = f' q) : PointDialogBoundary L R b' f' t := by
  have pt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ≠ L.control ∧ q ∉ L.inPlaceFlags := by
    have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have a := List.count_pos_iff.mpr hq
    simp only [dialogUsedWires, List.count_append] at used
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have : 0 < List.count q [L.control] := List.count_pos_iff.mpr (by simp [e])
      omega
    · have := List.count_pos_iff.mpr e; omega
  have pl (q : Wire) (hq : q ∈ L.dialogPool) : q ≠ L.control ∧ q ∉ L.inPlaceFlags := by
    have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have a := List.count_pos_iff.mpr hq
    simp only [dialogUsedWires, List.count_append] at used
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have : 0 < List.count q [L.control] := List.count_pos_iff.mpr (by simp [e])
      omega
    · have := List.count_pos_iff.mpr e; omega
  have hpt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : t q = s q :=
    ht q (pt q hq).1 (pt q hq).2
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨(point_holds _ _ _).mpr ⟨?_, ?_, ?_⟩, hc, hf, ?_⟩
  · rw [hpt _ (by simp [PointAddLayout.pointWires])]; exact hp.1
  · rw [regValue_congr L.point.x t s (fun q hq => hpt q (by simp [PointAddLayout.pointWires, hq]))]
    exact hp.2.1
  · rw [regValue_congr L.point.y t s (fun q hq => hpt q (by simp [PointAddLayout.pointWires, hq]))]
    exact hp.2.2
  · rw [regValue_congr L.dialogPool t s (fun q hq => ht q (pl q hq).1 (pl q hq).2)]
    exact v.clean

omit hn in
theorem state_other (D D' G H H' : Bool) (q : Wire)
    (hd : q ≠ L.doubleSelect) (he : q ≠ L.core.equalNegY) :
    dialogFlagState L false D G false false H false q = dialogFlagState L false D' G false false H' false q := by
  simp only [dialogFlagState, writeBit, Function.update_apply, hd, he, if_false]

theorem foldH_flag (R : Point) (b D G H : Bool) (hH : H = true → b = true ∧ D = false)
    (hD : D = true → b = true) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false)) (foldH L)
      (PointDialogBoundary L R (b ^^ H) (dialogFlagState L false (D ^^ H) G false false false false)) := by
  intro s m v
  have hr := dialogFlagState_read L hn false D G false false H false
  have hr' := dialogFlagState_read L hn false (D ^^ H) G false false false false
  have vc := v.control
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.1
  have ve := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.2.2.2.2.1
  obtain ⟨h1, h2, h3⟩ := fold_distinct L hn
  rw [foldH_run L hn]
  refine ⟨rfl, boundary_upd L hn v ?_ ?_ ?_⟩
  · intro q hc hf
    have hd : q ≠ L.doubleSelect := fun e => hf (e ▸ by simp [inPlaceFlags])
    have he : q ≠ L.core.equalNegY := fun e => hf (e ▸ by simp [inPlaceFlags])
    simp [hc, hd, he]
  · simp [vc, ve]
  · intro q hq
    by_cases hc : q = L.control
    · exact absurd (hc ▸ hq) (by
        have sep := dialogFlag_separation L hn
        exact (List.nodup_cons.mp sep).1)
    by_cases hd : q = L.doubleSelect
    · subst hd; simp only [h3.symm, if_false, if_true, vd, ve]; rw [hr'.2.1]
    by_cases he : q = L.core.equalNegY
    · subst he
      simp only [h1, h2, if_false, if_true, vc, vd, ve]
      rw [hr'.2.2.2.2.2.1]
      clear vc vd ve v hr hr'
      cases H <;> cases b <;> cases D <;> simp at hH hD ⊢
    · simp only [hc, hd, he, if_false]
      rw [v.flags q hq]
      exact state_other L D (D ^^ H) G H false q hd he

theorem unfoldH_flag (R : Point) (b D G H : Bool) (hH : H = true → b = true ∧ D = false)
    (hD : D = true → b = true) :
    Triple (PointDialogBoundary L R (b ^^ H) (dialogFlagState L false (D ^^ H) G false false false false))
      (unfoldH L)
      (PointDialogBoundary L R b (dialogFlagState L false D G false false H false)) := by
  intro s m v
  have hr := dialogFlagState_read L hn false (D ^^ H) G false false false false
  have hr' := dialogFlagState_read L hn false D G false false H false
  have vc := v.control
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.1
  have ve := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.2.2.2.2.1
  have key : (false ^^ (!(b ^^ H) && (D ^^ H))) = H := by
    cases H <;> cases b <;> cases D <;> simp at hH hD ⊢
  obtain ⟨h1, h2, h3⟩ := fold_distinct L hn
  rw [unfoldH_run L hn]
  refine ⟨rfl, boundary_upd L hn v ?_ ?_ ?_⟩
  · intro q hc hf
    have hd : q ≠ L.doubleSelect := fun e => hf (e ▸ by simp [inPlaceFlags])
    have he : q ≠ L.core.equalNegY := fun e => hf (e ▸ by simp [inPlaceFlags])
    simp [hc, hd, he]
  · simp only [if_true, vc, vd, ve, key]; cases b <;> cases H <;> rfl
  · intro q hq
    by_cases hc : q = L.control
    · exact absurd (hc ▸ hq) (by
        have sep := dialogFlag_separation L hn
        exact (List.nodup_cons.mp sep).1)
    by_cases hd : q = L.doubleSelect
    · subst hd; simp only [h3.symm, if_false, if_true, vc, vd, ve, key]; rw [hr'.2.1]
      cases D <;> cases H <;> rfl
    by_cases he : q = L.core.equalNegY
    · subst he
      simp only [h1, h2, if_false, if_true, vc, vd, ve, key]
      rw [hr'.2.2.2.2.2.1]
    · simp only [hc, hd, he, if_false]
      rw [v.flags q hq]
      exact state_other L (D ^^ H) D G false H q hd he

end Fold

section SpecN
attribute [local irreducible] run wires shortEqual pairEqual gatedShort genericFlag2 corners2 genFlagN

private theorem equal_simpN [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgramN_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgramN L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  let R1 := if G then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simpN,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simpN]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simpN]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simpN]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simpN]
  have hfin (P : Point) : (b && pointFinite P) = (b ^^ (b && pointEqual P 0)) := by
    rw [pointEqual_zero]; cases b <;> cases pointFinite P <;> rfl
  have hGv : ((((false ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) = G := by
    rw [hfin, hO]; simp only [G, dialogOrdinary, O, D, I, H, Bool.false_xor]
  have hgen := (dialogOrdinary_true b R C hC)
  have hR1fin : (b && pointFinite R1) = (b && pointFinite R) := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have f1 : pointFinite (R+C) = true := by
        have t := pointEqual_zero (R+C)
        have e2 : pointEqual (R+C) 0 = false := by
          cases h : pointEqual (R+C) 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) hs
        rw [e2] at t
        cases h : pointFinite (R+C)
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      have f2 : pointFinite R = true := by
        have t := pointEqual_zero R
        have e2 : pointEqual R 0 = false := by
          cases h : pointEqual R 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) h0
        rw [e2] at t
        cases h : pointFinite R
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      simp only [R1, hg, if_true, f1, f2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg]
  have hR1O : (b && pointEqual R1 0) = O := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have e1 : pointEqual (R+C) 0 = false := by
        cases h : pointEqual (R+C) 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) hs
      have e2 : pointEqual R 0 = false := by
        cases h : pointEqual R 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) h0
      rw [← hO]; simp only [R1, hg, if_true, e1, e2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg, hO]
  have hG1 : (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) = G := by
    rw [← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have hI1 : (((G ^^ (b && pointFinite R1)) ^^ D) ^^ H) = I := by
    rw [hR1fin, ← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have h3 := pairFlag_inputE L hw hn R C cy b false false false false false false false
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := gatedFlag_H L hw hn R (dialogExceptionPoint C) (exceptionBit C) b false D I false false false false
  rw [hH,Bool.false_xor] at h5
  have h6 := genFlagN_flag L hn R b false D I false false H false
  rw [hG1] at h6
  have hHx : H = true → b = true ∧ D = false := by
    intro h
    dsimp only [H, D, dialogException, dialogDouble] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, _, hne, _⟩, hR⟩ := h
    refine ⟨hb, ?_⟩
    simp [hR, hne]
  have hDx : D = true → b = true := by
    intro h
    dsimp only [D, dialogDouble] at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have hf1 := foldH_flag L hn R b D G H hHx hDx
  have read := dialogFlagState_read L hn false (D ^^ H) G false false false false
  have h7 := genericE_ok L hw hn hc Gen hGen R (b ^^ H)
    (dialogFlagState L false (D ^^ H) G false false false false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.1.symm.trans hg)).2) read.2.2.2.2.2.1
  rw [read.2.2.1] at h7
  have hu := unfoldH_flag L hn R1 b D G H hHx hDx
  have h9 := genFlagN_flag L hn R1 b false D G false false H false
  rw [hI1] at h9
  have h10a := zeroFlag_flagG L hn R1 b false D I false false H false
  rw [hR1O, Bool.false_xor] at h10a
  have readO := dialogFlagState_read L hn false D I O false H false
  have h8 := corners2_boundary L hw hn R C hC b (dialogFlagState L false D I O false H false)
    readO.2.2.2.1 readO.2.1 readO.2.2.1 readO.2.2.2.2.2.1
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [H,S,dialogExceptionEnabled,equal_simpN] using hf.2.2.2
  have h10 := pairFlag_outputG L hw hn S C (exceptionBit C) b false D I O false H false
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simpN] at h10
  rw [hf.1,Bool.xor_self] at h10
  have hout := park_triple L hw hn (outStage L C) R1 S b
    (dialogFlagState L false D I false false H false) (dialogFlagState L false D I false false false false)
    (dialogFlagState_read L hn false D I false false H false).2.2.2.1
    (dialogFlagState_read L hn false D I false false false false).2.2.2.1
    (by simpa only [outStage, List.append_assoc] using (h10a.seq h8).seq h10)
  have h11 := gatedFlag_D L hw hn S (C+C) (decide (cy≠-cy)) b false D I false false false false
  have hdo : ((b && decide (cy≠-cy)) && pointEqual S (C+C))=D := by
    change (K && pointEqual S (C+C)) = D
    rw [hK]; simpa only [equal_simpN] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have hzero : decide (S=0) = !pointFinite S := by
    rw [← equal_simpN]
    exact pointEqual_zero S
  have h12 := chainErase_equalI L hn S b false false (dialogInversePoint b R C)
    false false false false (by rw [← hf.2.2.1, hzero])
  have h := (((((((((h3.seq h5).seq h6).seq hf1).seq h7).seq hu).seq h9).seq hout).seq h11).seq h12)
  simpa only [finiteProgramN,List.append_assoc,dialogFlagState_zero] using h

end SpecN

/-! Supports. -/
section Support
attribute [local irreducible] wires shortEqual pairEqual controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

theorem point_G (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesG L := by
  simp [sitesG, hq]
theorem control_G : L.control ∈ sitesG L := by simp [sitesG]
theorem flag_G (t : Wire) (ht : t ∈ flagsG L) : t ∈ sitesG L := by simp [sitesG, ht]
theorem x_G (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesG L :=
  point_G L q (by simp [PointAddLayout.pointWires, hq])
theorem y_G (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesG L :=
  point_G L q (by simp [PointAddLayout.pointWires, hq])
theorem generic_G : L.core.generic ∈ sitesG L := flag_G L _ (by simp [flagsG])
theorem poolQ_G (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ sitesG L := by
  simp only [sitesG, List.mem_append]; exact Or.inr hq

theorem point_N (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesN L := by
  simp [sitesN, hq]
theorem control_N : L.control ∈ sitesN L := by simp [sitesN]
theorem flag_N (t : Wire) (ht : t ∈ flagsN L) : t ∈ sitesN L := by simp [sitesN, ht]
theorem x_N (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesN L :=
  point_N L q (by simp [PointAddLayout.pointWires, hq])
theorem y_N (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesN L :=
  point_N L q (by simp [PointAddLayout.pointWires, hq])
theorem poolQ_N (q : Wire) (hq : q ∈ sharedPoolF2 L) : q ∈ sitesN L := by
  simp only [sitesN, List.mem_append]; exact Or.inr hq

include hw

theorem pool_lowG (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesG L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_G
  simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

theorem pool_lowN (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesN L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_N
  simp only [sharedPoolF2, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

omit hw in
theorem G_of_sites (q : Wire) (hq : q ∈ CompressedPointSquare.residents L ++ CompressedPointSquare.sharedPool L)
    (h1 : q ≠ L.core.poolWire 1801) (h1' : q ≠ L.core.poolWire 1541)
    (h2 : q ≠ L.core.equalX) (h3 : q ≠ L.core.double) (h4 : q ≠ L.infinitySelect)
    (h5 : q ≠ L.genericSelect) (h6 : q ≠ L.core.equalNegY) :
    q ∈ sitesG L := by
  rcases List.mem_append.mp hq with hr | hp
  · simp only [CompressedPointSquare.residents, inPlaceFlags, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (hp | hc) | hf
    · exact point_G L q hp
    · rw [hc]; exact control_G L
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h4
      · exact flag_G L _ (by simp [flagsG])
      · exact absurd rfl h5
      · exact flag_G L _ (by simp [flagsG])
      · exact absurd rfl h2
      · exact absurd rfl h6
      · exact absurd rfl h3
  · exact poolQ_G L q (sharedPool_F L q hp h1 h1')

theorem fastConstG (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).toFinset ⊆ (sitesG L).toFinset := by
  intro q hq
  have pool := L.recoveryConstant_pool hw r
  have hq' := List.mem_toFinset.mp hq
  have inpool (h : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ h
  apply List.mem_toFinset.mpr
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at hq'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at hq'
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  rcases hq' with h | (((h | h) | h) | h | h | h)
  · rw [h]; exact generic_G L
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inl (Or.inl h)))
  · rcases hr with rfl | rfl
    · exact x_G L _ h
    · exact y_G L _ h
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inl (Or.inr h)))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inl h)))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inl h))))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inr h))))

include hn

theorem arithG (multiply : Bool) :
    wires (arith2 L multiply) ⊆ (sitesG L).toFinset := by
  intro q hq
  obtain ⟨old, hslot, hgood, rfl⟩ := arith2_wire L multiply q hq
  have hs2 := swap2_slots old hslot
  have inv := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, hs2, rfl⟩)
  have avoid (k : Nat) (hk : base k ∈ slots.toFinset) (hb : pointWireFn L (base k) = pointWireFn L (swap2 old)) :
      old = swap2 (base k) := by
    have := pointWireFn_injective_slots L hw hn _ hs2 (base k) hk hb.symm
    rw [← this, swap2_involutive]
  have mem (k : Nat) (hk : k ∈ indices) : base k ∈ slots.toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hidx (k : Nat) (h : k = 2313 ∨ k = 2403 ∨ k = 2405 ∨ k = 2406 ∨ k = 2407 ∨ k = 2408 ∨ k = 769) : k ∈ indices := by
    simp only [indices, List.mem_append, List.mem_range'_1]; omega
  apply List.mem_toFinset.mpr
  apply G_of_sites L _ (List.mem_toFinset.mp inv)
  · intro e
    have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
      simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 2313 (mem _ (hidx 2313 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 1797) = L.core.poolWire 1541 := by
      simp only [pointWireFn_base, pointIndexWire, show (1797:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 1797 m1797 (himg.trans e.symm)
    rw [show swap2 (base 1797) = base 769 by simp only [swap2, base]; simp] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2406) = L.core.equalX := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.1
    have := avoid 2406 (mem _ (hidx 2406 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2408) = L.core.double := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.2.1
    have := avoid 2408 (mem _ (hidx 2408 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2403) = L.infinitySelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.1
    have := avoid 2403 (mem _ (hidx 2403 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2405) = L.genericSelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.1
    have := avoid 2405 (mem _ (hidx 2405 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2407) = L.core.equalNegY := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.1
    have := avoid 2407 (mem _ (hidx 2407 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])

attribute [local irreducible] fastCandidate in
theorem fastSquareG : wires (fastSquare L) ⊆ (sitesG L).toFinset := by
  rw [fastSquare_eq L hw hn]
  intro q hq
  rw [fastSquareN, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have supp := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at supp
  apply List.mem_toFinset.mpr
  rcases supp with h | h | h | h
  · rw [h, CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      inPlaceFlags])]
    exact generic_G L
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact y_G L _ h
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact x_G L _ h
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)]
    apply poolQ_G
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have ha := CompressedPointSquare.prefix_allowed i bound
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, by omega, rfl⟩))

theorem fastGenericG (cx cy : Fp) : wires (fastGeneric2 L cx cy) ⊆ (sitesG L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (fastConstAdd L r k) ⊆ (sitesG L).toFinset :=
    (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩).trans
      (fastConstG L hw r hr)
  have cn : wires (fastConstNeg L cx) ⊆ (sitesG L).toFinset :=
    (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstG L hw L.point.x (Or.inl rfl))
  have cr := ca L.point.x (Or.inl rfl) (3*cx)
  simp only [fastGeneric2, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _, ca _ (Or.inr rfl) _⟩, arithG L hw hn false⟩, fastSquareG L hw hn⟩,
    cr⟩, arithG L hw hn true⟩, cn⟩, ca _ (Or.inr rfl) _⟩

/-- The relabelled block lives in `sitesN`. -/
theorem renamedG (Gen : Program) (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (renameProgram (tauM L) Gen) ⊆ (sitesNx L).toFinset := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have h := List.mem_toFinset.mp (hG used)
  apply List.mem_toFinset.mpr
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  by_cases hg : old = L.core.generic
  · rw [hg, show tauM L L.core.generic = L.genericSelect by simp [tauM]]
    simp [sitesNx]
  · have hs : old ≠ L.genericSelect := by
      intro e
      subst e
      simp only [sitesG, flagsG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.genericSelect
      have cG : 0 < List.count L.genericSelect L.inPlaceFlags :=
        List.count_pos_iff.mpr (by simp [inPlaceFlags])
      rcases h with ((hp | hc) | hf) | hp
      · have := List.count_pos_iff.mpr hp
        simp only [dialogUsedWires, List.count_append] at used
        omega
      · exact absurd hc.symm (by tauto)
      · rcases hf with e | e
        · exact absurd e.symm (by tauto)
        · exact hg e
      · have := List.count_pos_iff.mpr (sharedPool_Q_sub L hw _ hp)
        simp only [dialogUsedWires, List.count_append] at used
        omega
    rw [show tauM L old = old by simp [tauM, hg, hs]]
    simp only [sitesG, flagsG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [sitesNx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

/-- The doubly relabelled block lives in `sitesN`. -/
theorem renamedE (Gen : Program) (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ⊆ (sitesN L).toFinset := by
  have h0 := renamedG L hw hn Gen hG
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have h := List.mem_toFinset.mp (h0 used)
  apply List.mem_toFinset.mpr
  have aw := spare_away L hw hn
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  by_cases hk : old = spareWire L
  · rw [hk, show swapE L (spareWire L) = L.core.equalNegY by
      simp [swapE, (spare_ne_exc L hw hn)]]
    exact flag_N L _ (by simp [flagsN])
  · have he : old ≠ L.core.equalNegY := by
      intro e
      subst e
      simp only [sitesNx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
      have cG : 0 < List.count L.core.equalNegY L.inPlaceFlags :=
        List.count_pos_iff.mpr (by simp [inPlaceFlags])
      rcases h with ((hp | hc) | hf) | hp
      · have := List.count_pos_iff.mpr hp
        simp only [dialogUsedWires, List.count_append] at used
        omega
      · exact absurd hc.symm (by tauto)
      · rcases hf with e | e
        · exact absurd e.symm (by tauto)
        · exact absurd e.symm (by tauto)
      · have := List.count_pos_iff.mpr (sharedPool_Q_sub L hw _ hp)
        simp only [dialogUsedWires, List.count_append] at used
        omega
    rw [show swapE L old = old by simp [swapE, he, hk]]
    simp only [sitesNx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with ((hp | hc) | hf) | hp
    · exact point_N L _ hp
    · rw [hc]; exact control_N L
    · rcases hf with rfl | rfl <;> exact flag_N L _ (by simp [flagsN])
    · apply poolQ_N
      simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1,
        List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [sharedPoolF2, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1,
        List.mem_cons, List.not_mem_nil, or_false]
      rcases hp with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | e) | ⟨i, hi, rfl⟩
      · exact Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))
      · have : i ≠ 684 := by rintro rfl; exact hk rfl
        exact Or.inl (Or.inl (Or.inr ⟨i, by omega, rfl⟩))
      · exact Or.inl (Or.inr e)
      · exact Or.inr ⟨i, hi, rfl⟩

omit hn in
/-- Wires of the output stage, before relabelling. -/
theorem outStage_wires (C : Point) (q : Wire) (hq : q ∈ wires (outStage L C)) :
    q ∈ PointAddLayout.pointWires L.point ∨ q = L.control ∨ q = L.core.generic ∨ q ∈ flagsN L ∨
      q ∈ L.dialogPool.take 256 := by
  simp only [outStage, wires_append, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · rw [zeroFlag_wires] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl (by simp [PointAddLayout.pointWires])
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · simp only [corners2, wires_append, Finset.mem_union] at h
    have m (c : Wire) (P : Point) (hm : q ∈ wires (maskedPointConstant c L.point P)) :
        q = c ∨ q ∈ PointAddLayout.pointWires L.point := by
      have := List.mem_toFinset.mp (maskedPointConstant_support c L.point P hm)
      simpa using this
    rcases h with ((((h | h) | h) | h) | h) | h
    · rcases m _ _ h with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inl e
    all_goals first
      | (rcases m _ _ h with e | e
         · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [flagsN, e]))))
         · exact Or.inl e)
  · have hh := pairEqual_wires L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C) h
    have hy := yLow_mem L hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at hh
    rcases hh with rfl | rfl | rfl | rfl | h' | h'
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (by simp [PointAddLayout.pointWires, hy])
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [flagsN]))))
    · exact Or.inl (by simp [PointAddLayout.pointWires, h'])
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

theorem outStageN (C : Point) :
    wires (renameProgram (sigP L) (outStage L C)) ⊆ (sitesN L).toFinset := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  apply List.mem_toFinset.mpr
  have aw := park_away L hw hn
  have pk : parkWire L ∉ L.dialogPool.take 256 := by
    rw [pool_block L hw 256 (by omega)]
    intro h
    obtain ⟨i, hi, e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hi
    have := pool_inj L hw hn i 514 (by omega) (by omega) e
    omega
  have parkN : parkWire L ∈ sitesN L := by
    apply poolQ_N
    simp [parkWire, sharedPoolF2, wireBlock, List.mem_map, List.mem_range'_1]
    exact Or.inl ⟨514, by omega, rfl⟩
  rcases outStage_wires L hw C old used with h | h | h | h | h
  · have hg : old ≠ L.core.generic := by
      intro e; subst e
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
      have a := List.count_pos_iff.mpr h
      have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
      simp only [dialogUsedWires, List.count_append] at used
      omega
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => aw.1 (e ▸ h)
      simp [sigP, hg, hk]]
    exact point_N L _ h
  · subst h
    have sep := dialogFlag_separation L hn
    have cg : L.control ≠ L.core.generic := by
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep; tauto
    rw [show sigP L L.control = L.control by
      have hk : L.control ≠ parkWire L := fun e => aw.2.1 e.symm
      simp [sigP, cg, hk]]
    exact control_N L
  · subst h; simpa [sigP] using parkN
  · have hfl : old ∈ L.inPlaceFlags := by
      simp only [flagsN, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [inPlaceFlags]
    have hg : old ≠ L.core.generic := by
      intro e; subst e
      have sep := dialogFlag_separation L hn
      simp only [flagsN, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
      rcases h with e | e | e
      · exact absurd e.symm (by tauto)
      · exact absurd e.symm (by tauto)
      · exact absurd e (by tauto)
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => aw.2.2 (e ▸ hfl)
      simp [sigP, hg, hk]]
    exact flag_N L _ h
  · have hg : old ≠ L.core.generic := by
      intro e; subst e
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
      have a := List.count_pos_iff.mpr (List.mem_of_mem_take h)
      have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
      simp only [dialogUsedWires, List.count_append] at used
      omega
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => pk (e ▸ h)
      simp [sigP, hg, hk]]
    exact pool_lowN L hw 256 (by omega) _ h

omit hn in
theorem pairN (t₁ t₂ : Wire) (h1 : t₁ ∈ flagsN L) (h2 : t₂ ∈ flagsN L) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (sitesN L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | rfl | rfl | h | h
  · exact control_N L
  · exact y_N L _ hy
  · exact flag_N L _ h1
  · exact flag_N L _ h2
  · exact x_N L _ h
  · exact pool_lowN L hw 256 (by omega) q h

omit hn in
theorem gatedN (en : Bool) (t : Wire) (ht : t ∈ flagsN L) (P : Point) :
    wires (gatedShort L en t P) ⊆ (sitesN L).toFinset := by
  cases en
  · simp [gatedShort, wires]
  · intro q hq
    simp only [gatedShort, if_true] at hq
    have h := shortEqual_wires_subset L hw L.control t P (pointCode P) hq
    rw [equalConstant_wires] at h
    have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp [PointAddLayout.pointWires, L.dialogPool_length hw,
        show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]))
    simp only [List.mem_toFinset, List.mem_cons] at h
    apply List.mem_toFinset.mpr
    rcases h with rfl | rfl | h
    · exact control_N L
    · exact flag_N L _ ht
    · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h' | h'
      · exact point_N L _ h'
      · exact pool_lowN L hw 513 (by omega) _ h'

omit hw hn in
theorem zeroFlagN (t : Wire) (ht : t ∈ flagsN L) :
    wires (zeroFlag L.point.finite L.control t) ⊆ (sitesN L).toFinset := by
  rw [zeroFlag_wires]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl
  · exact point_N L _ (by simp [PointAddLayout.pointWires])
  · exact control_N L
  · exact flag_N L _ ht

omit hw hn in
theorem chainEraseN (t : Wire) (ht : t ∈ flagsN L) :
    wires (chainErase L.control L.point.finite t) ⊆ (sitesN L).toFinset := by
  intro q hq
  have hw' : wires (chainErase L.control L.point.finite t) = {L.control, L.point.finite, t} := by
    ext q
    simp only [chainErase, wires, Instr.wires, correctionWires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  rw [hw'] at hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact List.mem_toFinset.mpr (control_N L)
  · exact List.mem_toFinset.mpr (point_N L L.point.finite (by simp [PointAddLayout.pointWires]))
  · exact List.mem_toFinset.mpr (flag_N L _ ht)

omit hw hn in
theorem foldH_support : wires (foldH L) ⊆ (sitesN L).toFinset := by
  intro q hq
  simp [foldH, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl <;> simp [sitesN, flagsN]

omit hw hn in
theorem unfoldH_support : wires (unfoldH L) ⊆ (sitesN L).toFinset := by
  intro q hq
  simp [unfoldH, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl <;> simp [sitesN, flagsN]

omit hw hn in
theorem genFlagN_support : wires (genFlagN L) ⊆ (sitesN L).toFinset := by
  intro q hq
  simp [genFlagN, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl | rfl | rfl
  all_goals simp [sitesN, flagsN, PointAddLayout.pointWires]

theorem finiteProgramN_support (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (finiteProgramN L C cy Gen) ⊆ (sitesN L).toFinset := by
  have fS : flagsN L = [L.doubleSelect, L.genericSelect, L.core.equalNegY] := rfl
  simp only [finiteProgramN, wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨pairN L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _,
    gatedN L hw _ _ (by simp [fS]) _⟩, genFlagN_support L⟩, foldH_support L⟩, renamedE L hw hn Gen hG⟩,
    unfoldH_support L⟩, genFlagN_support L⟩,
    outStageN L hw hn C⟩, gatedN L hw _ _ (by simp [fS]) _⟩, chainEraseN L _ (by simp [fS])⟩

omit hw hn in
theorem sitesN_sub (q : Wire) (hq : q ∈ sitesN L) : q ∈ sitesE L := by
  simp only [sitesN, flagsN, sitesE, flagsE, sharedPoolF2, sharedPoolF, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, wireBlock, List.mem_map, List.mem_range'_1] at hq ⊢
  rcases hq with ((hp | hc) | hf) | ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | e) | ⟨i, hi, rfl⟩
  · exact Or.inl (Or.inl (Or.inl hp))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr (by tauto))
  · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨i, by omega, rfl⟩)))
  · exact Or.inr (Or.inl (Or.inr e))
  · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)

omit hn in
theorem sitesN_used : (sitesN L).toFinset ⊆ L.dialogUsedWires.toFinset := by
  intro q hq
  exact sitesE_used L hw (List.mem_toFinset.mpr (sitesN_sub L q (List.mem_toFinset.mp hq)))

end Support

/-! Frame, resources and validity. -/
section Frame
attribute [local irreducible] run wires

private theorem boundary_frame_valuesN (L : ControlledPointLayout) (P : Program)
    (hP : wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

private theorem boundary_work_subsetN (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_pointN (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

theorem finiteProgramN_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) (hG : wires Gen ⊆ (sitesG L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} finiteProgramN L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subsetN L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finiteProgramN_spec L hw hn R hc b Gen hGen s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (finiteProgramN_support L hw hn (.some hc) cy Gen hG).trans (sitesN_used L hw)
  rw [boundary_frame_valuesN L _ hsup R _ b s m hi ho q (work_not_pointN L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end Frame

section Resources
open Challenge Baselines

theorem finiteProgramN_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) {cx : Fp} (hc : curve.toAffine.Nonsingular cx cy) (hC : C = .some hc) :
    toffoliCount (finiteProgramN L C cy Gen) ≤ 1033 + toffoliCount Gen ∧
    measurementCount (finiteProgramN L C cy Gen) ≤ 1027 + measurementCount Gen := by
  have p1 := pairEqual_counts L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_counts L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)
  have c1 : tailCost (decide (cy≠-cy)) (yBit C) true (yBit (-C)) = 1 := by
    subst hC
    rw [cy_ne_neg hc, yBit_neg hc]
    cases yBit (.some hc) <;> decide
  have c2 : tailCost true (yBit C) (exceptionBit C) (yBit (-C)) ≤ 1 := by
    subst hC
    rw [yBit_neg hc]
    cases yBit (.some hc) <;> cases exceptionBit (.some hc) <;> decide
  have g1 := gatedShort_counts L hw (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C)
  have g2 := gatedShort_counts L hw (decide (cy≠-cy)) L.doubleSelect (C+C)
  have z1 := zeroFlag_counts L.point.finite L.control L.core.generic
  have z2 : toffoliCount (chainErase L.control L.point.finite L.genericSelect) = 0 ∧
      measurementCount (chainErase L.control L.point.finite L.genericSelect) = 1 := by
    simp [chainErase, toffoliCount, measurementCount]
  have f : toffoliCount (genFlagN L) = 1 ∧ measurementCount (genFlagN L) = 0 := by
    simp [genFlagN, toffoliCount, measurementCount]
  have r := renameProgram_counts (tauM L) Gen
  have r' := renameProgram_counts (swapE L) (renameProgram (tauM L) Gen)
  have fo : toffoliCount (foldH L) = 1 ∧ measurementCount (foldH L) = 0 := by
    simp [foldH, toffoliCount, measurementCount]
  have uf : toffoliCount (unfoldH L) = 1 ∧ measurementCount (unfoldH L) = 0 := by
    simp [unfoldH, toffoliCount, measurementCount]
  have r2 := renameProgram_counts (sigP L) (outStage L C)
  have c := (show toffoliCount (corners2 L C) = 0 ∧ measurementCount (corners2 L C) = 0 by
    simp only [corners2, toffoliCount_append, measurementCount_append,
      (maskedPointConstant_counts _ _ _).1, (maskedPointConstant_counts _ _ _).2]; decide)
  simp only [outStage, toffoliCount_append, measurementCount_append] at r2
  simp only [finiteProgramN, outStage, toffoliCount_append, measurementCount_append]
  omega

theorem finiteProgramN_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : GatePhysical Gen) :
    GatePhysical (finiteProgramN L C cy Gen) := by
  have sep := dialogFlag_separation (L:=L) hn
  have hz (t : Wire) (ht : t∈L.inPlaceFlags) : GatePhysical (zeroFlag L.point.finite L.control t) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    have hnd := L.dialogPointZero_nodup hn L.control t hct (Or.inl rfl) ht
    simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
      List.mem_append, not_or] at hnd
    exact zeroFlag_physical _ _ _ (fun h => hnd.2.1.1 h.symm) hct
  have hg (en : Bool) (t : Wire) (ht : t∈L.inPlaceFlags) (P : Point) : GatePhysical (gatedShort L en t P) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    cases en
    · simp [gatedShort, GatePhysical]
    · simpa only [gatedShort, if_true] using shortEqual_physical L hw hn L.control t hct (Or.inl rfl) ht P
  have z1 := hz L.core.generic (by simp [inPlaceFlags])
  have z2 : GatePhysical (chainErase L.control L.point.finite L.genericSelect) := by
    intro i hi
    simp only [chainErase, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals trivial
  have away (c : Wire) (hc : c ∈ L.inPlaceFlags) : c ∉ PointAddLayout.pointWires L.point := by
    intro hm
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) c
    have hf := List.count_pos_iff.mpr hc
    have hp := List.count_pos_iff.mpr hm
    simp only [dialogUsedWires,List.count_append,List.count_cons] at h
    omega
  have all (c : Wire) (hc : c ∈ L.inPlaceFlags) (D : Point) : GatePhysical (maskedPointConstant c L.point D) :=
    maskedPointConstant_physical c L.point D (away c hc)
  have co : GatePhysical (corners2 L C) := by
    simp only [corners2, gatePhysical_append]
    repeat constructor
    all_goals apply all _ (by simp [inPlaceFlags])
  have rn0 := gatePhysical_rename (tauM L) (tauM_injective L hn) Gen hG
  have rn := gatePhysical_rename (swapE L) (swapE_injective L hw hn) _ rn0
  obtain ⟨fd1, fd2, fd3⟩ := fold_distinct L hn
  have fo : GatePhysical (foldH L) := by
    intro i hi
    simp only [foldH, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact fd1
    · exact fd2
    · trivial
    · exact ⟨fd1.symm, fd2.symm⟩
    · trivial
  have uf : GatePhysical (unfoldH L) := by
    intro i hi
    simp only [unfoldH, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact ⟨fd1.symm, fd2.symm⟩
    · trivial
    · exact fd2
    · exact fd1
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hfin : L.point.finite ≠ L.genericSelect := by
    intro e
    exact away L.genericSelect (by simp [inPlaceFlags]) (e ▸ by simp [PointAddLayout.pointWires])
  have fl : GatePhysical (genFlagN L) := by
    intro i hi
    simp only [genFlagN, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨by tauto, hfin⟩
    · exact (by tauto : L.doubleSelect ≠ L.genericSelect)
    · exact (by tauto : L.core.equalNegY ≠ L.genericSelect)
  have q3 := hg (exceptionBit C) L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have q5 := hg (decide (cy≠-cy)) L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have p1 := pairEqual_physical L hw hn L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_physical L hw hn L.core.generic L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) true (exceptionBit C) C (-C)
  have os : GatePhysical (outStage L C) := by
    simp only [outStage, gatePhysical_append]
    exact ⟨⟨z1, co⟩, p2⟩
  have rs := gatePhysical_rename (sigP L) (sigP_injective L hw hn) _ os
  simp only [finiteProgramN, gatePhysical_append]
  tauto

theorem finiteProgramN_gateSlots (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) : gateSlots (finiteProgramN L C cy Gen) ≤ 20000 + gateSlots Gen := by
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have hf : gateSlots (genFlagN L) = 3 := rfl
  have hzf (t : Wire) : gateSlots (zeroFlag L.point.finite L.control t) = 3 := rfl
  have hgs (en : Bool) (t : Wire) (P : Point) : gateSlots (gatedShort L en t P) ≤ 2314 := by
    cases en
    · simp [gatedShort]
    · simpa only [gatedShort, if_true] using shortEqual_gateSlots_le L hw L.control t P
  have z2 := pairEqual_gateSlots_le L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have z4 := hgs (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C)
  have z5 := pairEqual_gateSlots_le L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)
  have z6 := hgs (decide (cy≠-cy)) L.doubleSelect (C+C)
  have m1 := hm L.core.generic C
  have m2 := hm L.doubleSelect C
  have m3 := hm L.doubleSelect (C+C)
  have m4 := hm L.genericSelect (-C)
  have m5 := hm L.core.equalNegY (dialogExceptionPoint C)
  have m6 := hm L.core.equalNegY (-C)
  have hze : gateSlots (chainErase L.control L.point.finite L.genericSelect) = 4 := rfl
  have rs := rename_gateSlots (tauM L) Gen
  have rs' := rename_gateSlots (swapE L) (renameProgram (tauM L) Gen)
  have hfo : gateSlots (foldH L) = 5 := rfl
  have huf : gateSlots (unfoldH L) = 5 := rfl
  have rs2 := rename_gateSlots (sigP L) (outStage L C)
  simp only [finiteProgramN, gateSlots_append, hf, hzf, hze, hfo, huf, rs', rs, rs2]
  simp only [outStage, corners2, gateSlots_append, hzf]
  omega

end Resources

end ECDSAAdd.Entrant
