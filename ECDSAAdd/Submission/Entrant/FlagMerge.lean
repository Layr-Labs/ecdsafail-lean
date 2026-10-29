import ECDSAAdd.Submission.Entrant.FlagAvoid
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SlotMapped

/-! Flag merge on top of `FlagG`.

* While the generic-branch block runs, its control bit is held in
  `genericSelect`: `genFlagN` folds `(b ∧ finite) ⊕ D ⊕ H` into the
  inverse-point flag (the classes are exclusive, so the result is the generic
  bit), and the block runs with `core.generic` and `genericSelect` exchanged.
  One shared Toffoli then restores the inverse flag and computes infinity.
* The infinity flag of the output stage (`FlagG` keeps it on `core.generic`)
  lives on pool site 514 instead: that stage is relabelled with
  `core.generic ↔ poolWire 514`.  The stage uses only the first 256 pool sites.

Neither `core.generic` nor `infinitySelect` is used. The shared pool also
excludes site 1800, which the short arithmetic copies do not use. -/
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

/-- `genericSelect ^= (b ∧ finite) ⊕ D ⊕ H`. -/
def genFlagN (L : ControlledPointLayout) : Program :=
  [.CCX L.control L.point.finite L.genericSelect, .CX L.doubleSelect L.genericSelect,
   .CX L.core.equalNegY L.genericSelect]

/-- Restore the inverse flag and compute infinity with one shared Toffoli. -/
def mergeFlagsN (L : ControlledPointLayout) : Program :=
  [.CX L.genericSelect (parkWire L), .CCX L.control L.point.finite L.genericSelect,
   .CX L.genericSelect (parkWire L), .CX L.control (parkWire L),
   .CX L.doubleSelect L.genericSelect, .CX L.core.equalNegY L.genericSelect]

/-- The output stage after the infinity flag has been computed. -/
def outTail (L : ControlledPointLayout) (C : Point) : Program :=
  corners2 L C ++ pairEqual L L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)

/-- The output stage of `finiteProgramFG` that holds the infinity flag. -/
def outStage (L : ControlledPointLayout) (C : Point) : Program :=
  zeroFlag L.point.finite L.control L.core.generic ++ corners2 L C ++
  pairEqual L L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)

def finiteProgramN (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  gatedShort L (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C) ++
  genFlagN L ++ renameProgram (tauM L) Gen ++ mergeFlagsN L ++
  renameProgram (sigP L) (outTail L C) ++
  gatedShort L (decide (cy≠-cy)) L.doubleSelect (C+C) ++
  chainErase L.control L.point.finite L.genericSelect

def flagsN (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.genericSelect, L.core.equalNegY]

def sitesN (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsN L ++ sharedPoolF L

def flagsG (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.core.generic, L.core.equalNegY]

/-- Sites of the generic block: it never touches `genericSelect`. -/
def sitesG (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsG L ++ sharedPoolF L

theorem sitesN_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesN L).length = 1892 := by
  simp [sitesN, flagsN, sharedPoolF, PointAddLayout.pointWires, wireBlock_length,
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

section Fusion
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem sigP_zeroFlag :
    renameProgram (sigP L) (zeroFlag L.point.finite L.control L.core.generic) =
      zeroFlag L.point.finite L.control (parkWire L) := by
  have aw := park_away L hw hn
  have fd := flags_distinct L hn
  have cp : L.control ≠ parkWire L := Ne.symm aw.2.1
  have fp : L.point.finite ≠ parkWire L := fun e => aw.1 (by simp [← e, PointAddLayout.pointWires])
  simp [zeroFlag, renameProgram, renameInstr, sigP, fd.1, fd.2.1, cp, fp]

/-- Equality includes every basis bit and phase for every measurement record. -/
theorem mergeFlagsN_run_eq (s : State) (m : List Bool) :
    run (mergeFlagsN L) m s =
      run (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)) m s := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have ci : L.control ≠ L.genericSelect := by tauto
  have di : L.doubleSelect ≠ L.genericSelect := by tauto
  have hi : L.core.equalNegY ≠ L.genericSelect := by tauto
  have nd := L.dialogPointZero_nodup hn L.control L.genericSelect ci
    (Or.inl rfl) (by simp [inPlaceFlags])
  simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
    List.mem_append, not_or] at nd
  have fi : L.point.finite ≠ L.genericSelect := fun e => nd.2.1.1 e.symm
  have aw := park_away L hw hn
  have cp : L.control ≠ parkWire L := Ne.symm aw.2.1
  have fp : L.point.finite ≠ parkWire L := fun e => aw.1 (by simp [← e, PointAddLayout.pointWires])
  have ip : L.genericSelect ≠ parkWire L := fun e => aw.2.2 (by simp [← e, inPlaceFlags])
  have dp : L.doubleSelect ≠ parkWire L := fun e => aw.2.2 (by simp [← e, inPlaceFlags])
  have hp : L.core.equalNegY ≠ parkWire L := fun e => aw.2.2 (by simp [← e, inPlaceFlags])
  rw [run_append, run_take]
  simp only [show measurementCount (genFlagN L) = 0 from rfl, List.drop_zero]
  rw [genFlagN_run L hn s m, zeroFlag_run _ _ _ (flags_distinct L hn).2.2.2.2.2 fp]
  simp only [mergeFlagsN, run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases qi : q = L.genericSelect
  · subst q
    simp only [writeBit, Function.update_apply, ci, di, hi, fi, cp, fp, ip, ip.symm,
      dp, hp, if_false, if_true]
  · by_cases qp : q = parkWire L
    · subst q
      simp only [writeBit, Function.update_apply, ci, di, hi, fi, cp, fp, ip, ip.symm,
        dp, hp, if_false, if_true]
      cases s.basis L.genericSelect <;> cases s.basis (parkWire L) <;>
        cases s.basis L.control <;> cases s.basis L.point.finite <;>
        cases s.basis L.doubleSelect <;> cases s.basis L.core.equalNegY <;> rfl
    · simp [writeBit, qi, qp]

theorem mergeStage_shape (C : Point) :
    genFlagN L ++ renameProgram (sigP L) (outStage L C) =
      (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)) ++
        renameProgram (sigP L) (outTail L C) := by
  simp only [outStage, outTail, renameProgram, List.map_append]
  change genFlagN L ++
    ((renameProgram (sigP L) (zeroFlag L.point.finite L.control L.core.generic) ++
      renameProgram (sigP L) (corners2 L C)) ++
      renameProgram (sigP L) (pairEqual L L.core.generic L.core.equalNegY true (exceptionBit C) C (-C))) = _
  rw [sigP_zeroFlag L hw hn]
  simp only [renameProgram, List.map_append, List.append_assoc]

theorem mergeStage_run_eq (C : Point) (s : State) (m : List Bool) :
    run (mergeFlagsN L ++ renameProgram (sigP L) (outTail L C)) m s =
      run (genFlagN L ++ renameProgram (sigP L) (outStage L C)) m s := by
  rw [mergeStage_shape L hw hn C, run_append, run_take]
  rw [run_append (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)), run_take]
  simp only [show measurementCount (mergeFlagsN L) = 0 from rfl,
    show measurementCount (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)) = 0 from rfl,
    List.drop_zero]
  rw [mergeFlagsN_run_eq L hw hn s m]

theorem mergeStage_wires (C : Point) :
    wires (mergeFlagsN L ++ renameProgram (sigP L) (outTail L C)) =
      wires (genFlagN L ++ renameProgram (sigP L) (outStage L C)) := by
  rw [mergeStage_shape L hw hn C, wires_append, wires_append]
  congr 1
  ext q
  simp [mergeFlagsN, genFlagN, zeroFlag, wires, Instr.wires]
  tauto

end Fusion

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
  have read := dialogFlagState_read L hn false D G false false H false
  have h7 := genericM_ok L hn hc Gen hGen R b (dialogFlagState L false D G false false H false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.1.symm.trans hg)).2)
  rw [read.2.2.1] at h7
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
  have hmerged : Triple (PointDialogBoundary L R1 b (dialogFlagState L false D G false false H false))
      (mergeFlagsN L ++ renameProgram (sigP L) (outTail L C))
      (PointDialogBoundary L S b (dialogFlagState L false D I false false false false)) := by
    intro s m hs
    rw [mergeStage_run_eq L hw hn C s m]
    exact (h9.seq hout) s m hs
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
  have h := ((((((h3.seq h5).seq h6).seq h7).seq hmerged).seq h11).seq h12)
  simpa only [finiteProgramN,List.append_assoc,dialogFlagState_zero] using h

end SpecN

/-! Supports. -/
section Support
attribute [local irreducible] wires shortEqual pairEqual controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

theorem point_N (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesN L := by
  simp [sitesN, hq]
theorem control_N : L.control ∈ sitesN L := by simp [sitesN]
theorem flag_N (t : Wire) (ht : t ∈ flagsN L) : t ∈ sitesN L := by simp [sitesN, ht]
theorem x_N (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesN L :=
  point_N L q (by simp [PointAddLayout.pointWires, hq])
theorem y_N (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesN L :=
  point_N L q (by simp [PointAddLayout.pointWires, hq])
theorem poolQ_N (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ sitesN L := by
  simp only [sitesN, List.mem_append]; exact Or.inr hq

include hw

theorem pool_lowN (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesN L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_N
  simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl ⟨i, by omega, rfl⟩)

include hn

/-- Reuse the certified support and remove its unused inverse flag. -/
theorem fastGenericG (cx cy : Fp) : wires (fastGeneric2 L cx cy) ⊆ (sitesG L).toFinset := by
  intro q hq
  have hE := List.mem_toFinset.mp (fastGenericE L hw hn cx cy hq)
  have hI : q ≠ L.genericSelect := by
    intro e
    exact fastGeneric2_no_genericSelect L hw hn cx cy (e ▸ hq)
  apply List.mem_toFinset.mpr
  simp only [sitesE, flagsE, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hE
  simp only [sitesG, flagsG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- The relabelled block lives in `sitesN`. -/
theorem renamedG (Gen : Program) (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (renameProgram (tauM L) Gen) ⊆ (sitesN L).toFinset := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have h := List.mem_toFinset.mp (hG used)
  apply List.mem_toFinset.mpr
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  by_cases hg : old = L.core.generic
  · rw [hg, show tauM L L.core.generic = L.genericSelect by simp [tauM]]
    exact flag_N L _ (by simp [flagsN])
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
      · rcases hf with e | e | e
        · exact absurd e.symm (by tauto)
        · exact hg e
        · exact absurd e (by tauto)
      · have := List.count_pos_iff.mpr (sharedPool_Q_sub L hw _ hp)
        simp only [dialogUsedWires, List.count_append] at used
        omega
    rw [show tauM L old = old by simp [tauM, hg, hs]]
    simp only [sitesG, flagsG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [sitesN, flagsN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

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
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    exact Or.inl (Or.inl ⟨514, by omega, rfl⟩)
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
  have stage : wires (mergeFlagsN L ++ renameProgram (sigP L) (outTail L C)) ⊆ (sitesN L).toFinset := by
    rw [mergeStage_wires L hw hn C, wires_append, Finset.union_subset_iff]
    exact ⟨genFlagN_support L, outStageN L hw hn C⟩
  have sides : wires (mergeFlagsN L) ⊆ (sitesN L).toFinset ∧
      wires (renameProgram (sigP L) (outTail L C)) ⊆ (sitesN L).toFinset := by
    simpa only [wires_append, Finset.union_subset_iff] using stage
  simp only [finiteProgramN, wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨pairN L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _,
    gatedN L hw _ _ (by simp [fS]) _⟩, genFlagN_support L⟩, renamedG L hw hn Gen hG⟩, sides.1⟩,
    sides.2⟩, gatedN L hw _ _ (by simp [fS]) _⟩, chainEraseN L _ (by simp [fS])⟩

omit hw hn in
theorem sitesN_sub (q : Wire) (hq : q ∈ sitesN L) : q ∈ sitesE L := by
  simp only [sitesN, flagsN, sitesE, flagsE, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hq ⊢
  tauto

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
    toffoliCount (finiteProgramN L C cy Gen) ≤ 1030 + toffoliCount Gen ∧
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
  have z2 : toffoliCount (chainErase L.control L.point.finite L.genericSelect) = 0 ∧
      measurementCount (chainErase L.control L.point.finite L.genericSelect) = 1 := by
    simp [chainErase, toffoliCount, measurementCount]
  have f : toffoliCount (genFlagN L) = 1 ∧ measurementCount (genFlagN L) = 0 := by
    simp [genFlagN, toffoliCount, measurementCount]
  have mf : toffoliCount (mergeFlagsN L) = 1 ∧ measurementCount (mergeFlagsN L) = 0 := by
    simp [mergeFlagsN, toffoliCount, measurementCount]
  have r := renameProgram_counts (tauM L) Gen
  have r2 := renameProgram_counts (sigP L) (outTail L C)
  have c := (show toffoliCount (corners2 L C) = 0 ∧ measurementCount (corners2 L C) = 0 by
    simp only [corners2, toffoliCount_append, measurementCount_append,
      (maskedPointConstant_counts _ _ _).1, (maskedPointConstant_counts _ _ _).2]; decide)
  simp only [outTail, toffoliCount_append, measurementCount_append] at r2
  simp only [finiteProgramN, outTail, toffoliCount_append, measurementCount_append]
  omega

theorem finiteProgramN_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : GatePhysical Gen) :
    GatePhysical (finiteProgramN L C cy Gen) := by
  have sep := dialogFlag_separation (L:=L) hn
  have hg (en : Bool) (t : Wire) (ht : t∈L.inPlaceFlags) (P : Point) : GatePhysical (gatedShort L en t P) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    cases en
    · simp [gatedShort, GatePhysical]
    · simpa only [gatedShort, if_true] using shortEqual_physical L hw hn L.control t hct (Or.inl rfl) ht P
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
  have rn := gatePhysical_rename (tauM L) (tauM_injective L hn) Gen hG
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
  have aw := park_away L hw hn
  have ip : L.genericSelect ≠ parkWire L := fun e => aw.2.2 (by simp [← e, inPlaceFlags])
  have cp : L.control ≠ parkWire L := Ne.symm aw.2.1
  have mf : GatePhysical (mergeFlagsN L) := by
    intro i hi
    simp only [mergeFlagsN, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ip
    · exact ⟨by tauto, hfin⟩
    · exact ip
    · exact cp
    · exact (by tauto : L.doubleSelect ≠ L.genericSelect)
    · exact (by tauto : L.core.equalNegY ≠ L.genericSelect)
  have q3 := hg (exceptionBit C) L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have q5 := hg (decide (cy≠-cy)) L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have p1 := pairEqual_physical L hw hn L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_physical L hw hn L.core.generic L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) true (exceptionBit C) C (-C)
  have os : GatePhysical (outTail L C) := by
    simp only [outTail, gatePhysical_append]
    exact ⟨co, p2⟩
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
  have hmf : gateSlots (mergeFlagsN L) = 6 := rfl
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
  have rs2 := rename_gateSlots (sigP L) (outTail L C)
  simp only [finiteProgramN, gateSlots_append, hf, hmf, hze, rs, rs2]
  simp only [outTail, corners2, gateSlots_append]
  omega

end Resources

end ECDSAAdd.Entrant
