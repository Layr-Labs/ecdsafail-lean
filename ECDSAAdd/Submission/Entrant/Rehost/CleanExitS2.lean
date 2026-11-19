import ECDSAAdd.Submission.Entrant.Rehost.Flat
/-!
# S2 rehost (port of the record-era `CleanExit` to S1): Z8, 4112 is clean before the body of `x1N`

Boundary 10 (after the park of `x1N`) is the output of the hosted multiplication kernel. It is reached
forward: input -> stage / encode / eraseB (outer pieces, `fU`) -> the generic block start (pulled through
`fG = U ∘ swap ∘ rho`) -> entry stage -> square -> hosted exit rest. There, the record's
`hosted_rest_pwD` says the state is the record kernel's output with the parked flag put on `pkW`, and
`ParityXExitInverse23Kernel.exitX_correct` says the record kernel leaves every wire outside `x`, `y`
unchanged. Hence every dialog-pool wire except `pkW` is false at boundary 10 (`clean10_pool`).
Boundaries 9 and 8 follow backwards through p9 (two CNOTs) and p8 (untouched wires).
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1 MappedCompressed

namespace ExitAux

/-! ## Small state lemmas -/

theorem put_basis_ne (s : State) (q r : Wire) (v : Bool) (h : r ≠ q) :
    (ParityEven.put s q v).basis r = s.basis r := by
  simp [ParityEven.put, writeBit, Function.update_apply, h]

theorem put_basis_reg (r : List Wire) (s : State) (q : Wire) (v : Bool) (h : q ∉ r) :
    regValue r (ParityEven.put s q v).basis = regValue r s.basis :=
  regValue_congr _ _ _ (fun w hw => put_basis_ne _ _ _ _ (fun e => h (e ▸ hw)))

/-! ## Generic level: boundary 10 inside the generic block -/

/-- The hosted generic program up to the end of the multiplication kernel (before `exitYAll`). -/
def g10 (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ((ParityUniform.entryYAll L (-cy) ++ FlagEntry.entryXNew L (FlagEntry.pkW L) (-cx)) ++
      StairConcreteAssembly.hostedEntryRest L) ++
    (StairSquareFinal.squareEntryHL StairSqLoopA.holes L (ReflectionE1.correction cx) ++
      StairConcreteAssembly.hostedExitRest L cx.val)

section Generic
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out ParityEven ParityUniform
open FlagExit
open ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic ParityXEntry
attribute [local irreducible] run wires measurementCount
attribute [local irreducible] ParityUniform.entryYAll FlagEntry.entryXNew
  StairConcreteAssembly.hostedEntryRest StairSquareFinal.squareEntryHL
  StairConcreteAssembly.hostedExitRest ParityStageBothInverse23.restEntry A161Generic.squareEntry
  SquareCarryLoan719BF.program fastConstAdd E1QubitPlacement.tickF ParityXExitInverse23Kernel.restXX
  FrontierEntry1591Callers.exit ParityXExitInverse23Kernel.kernelX

set_option maxHeartbeats 8000000 in
/-- At the end of the hosted multiplication kernel (generic coordinates, layout `layout`), every
dialog-pool wire except the parked flag `pkW` is false. Hypotheses exactly those of
`StairSemanticFinal.generic_eqD`. -/
theorem g10_pool
    (H : ∀ k, StairSemanticComposition.HostedReplayInterface k)
    (hE : StairSemanticFinal.EntrySupportD)
    (hX : StairSemanticFinal.ExitSupportD)
    (cx cy X Y : Fp) (G : Bool) (s : State) (e : Bool)
    (hv : PointDialogValues layout X Y G s.basis s.basis)
    (he : e = (if s.basis layout.core.generic then
      decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hx1 : X+(if G then -cx else 0)≠0)
    (hx2 : (X+(if G then -cx else 0))-
        (if G then ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0)))*
          ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) else 0)+
        (if G then (SquareCarryLoan719BF.K:Fp) else 0)+
        (if G then ReflectionE1.correction cx else 0)≠0)
    (m : List Bool) (q : Wire) (hq : q ∈ layout.dialogPool) (hpk : q ≠ pkW layout) :
    (run (g10 layout cx cy) m (put s (pkW layout) e)).basis q = false := by
  subst he
  have hw := layout_widths
  have hn := layout_nodup
  have hg : pkW layout ≠ layout.core.generic :=
    FlagTop.pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  have hEq := StairSemanticFinal.entryStage_eqD H hE layout hw hn cx cy X Y G s hv hg hx1
    (m.take (measurementCount ((entryYAll layout (-cy) ++ entryXNew layout (pkW layout) (-cx)) ++
      StairConcreteAssembly.hostedEntryRest layout))) []
  have w0v := entryStageAll_step layout hw hn X Y (-cx) (-cy) G s.basis hx1 s
    (padE layout cy cx []) hv
  rw [← (head_pad layout hw hn cx cy X Y s hv.x hv.y hv.clean hg).run_eq []] at w0v
  generalize hs2 : run ((entryYAll layout (-cy) ++ entryXNew layout (pkW layout) (-cx)) ++
      restEntry layout) [] (put s (pkW layout) (if s.basis layout.core.generic then
        decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false)) = s2 at w0v
  have v2 := w0v.2
  rw [g10, run_append, hEq, hs2, run_append]
  generalize (m.drop _).take _ = a
  generalize (m.drop _).drop _ = r
  -- the record's square on the same state
  let k := ReflectionE1.correction cx
  let X1 := X+(if G then -cx else 0)
  let Y1 := (Y+(if G then -cy else 0))/(X+(if G then -cx else 0))
  have e1 : run (StairSquareFinal.squareEntryHL StairSqLoopA.holes layout k) a s2 =
      run (squareEntry layout k) [] s2 :=
    (StairSquareFinal.squareEntryHL_base StairSqLoopA.holes (List.Sublist.refl _) layout hw hn k
      X1 Y1 G s.basis s2 a [] v2).trans
    (squareEntry_base layout hw hn k X1 Y1 G s.basis s2 [] [] v2).symm
  refine (congrArg (fun t => (run (StairConcreteAssembly.hostedExitRest layout cx.val) r t).basis q)
    e1).trans ?_
  beta_reduce
  have e2 := StairSemanticFinal.hosted_rest_pwD H hX layout hw hn k cx X1 Y1 G s.basis s2 v2 hx2 [] r
  refine (congrArg (fun t : State => t.basis q) e2).trans ?_
  beta_reduce
  refine (put_basis_ne _ _ _ _ hpk).trans ?_
  -- the record kernel leaves everything outside x, y unchanged
  let Z := X1-(if G then Y1*Y1 else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square := SquareCarryLoan719BF.step layout hw hn X1 Y1 G s.basis
  have add := fastStep_addX layout hw hn Z Y1 G s.basis k
  obtain ⟨-, vW⟩ := (square.seq add) s2 [] v2
  generalize hwd : run (SquareCarryLoan719BF.program layout ++ fastConstAdd layout layout.point.x k)
    [] s2 = w at vW
  have eu : run (squareEntry layout k) [] s2 = run (E1QubitPlacement.tickF layout) [] w :=
    (squareEntry_base layout hw hn k X1 Y1 G s.basis s2 [] [] v2).trans
      ((run_append _ _ [] s2).trans (by simp only [List.take_nil, List.drop_nil, hwd]))
  refine (congrArg (fun t => (run (ParityXExitInverse23Kernel.restXX layout cx.val) r t).basis q)
    eu).trans ?_
  beta_reduce
  have e3 : run (ParityXExitInverse23Kernel.restXX layout cx.val) r
      (run (E1QubitPlacement.tickF layout) [] w) =
      run (FrontierEntry1591Callers.exit (kernelX cx.val) layout)
        (pfx (measurementCount (E1QubitPlacement.tickF layout)) [] ++ r) w :=
    (FlagExit.run_pre _ _ r w).symm.trans
      (congrArg (fun P => run P (pfx (measurementCount (E1QubitPlacement.tickF layout)) [] ++ r) w)
        (exit_splitX layout cx.val).symm)
  refine (congrArg (fun t : State => t.basis q) e3).trans ?_
  beta_reduce
  have hpos : 0 < (Z+(if G then k else 0)).val :=
    Nat.pos_of_ne_zero (fun hz => hx2 ((ZMod.val_eq_zero _).mp hz))
  have fr := exitX_correct layout hw hn cx.val cx.isLt (Z+(if G then k else 0)).val Y1.val
    (ZMod.val_lt _) hpos (ZMod.val_lt _) w
    (pfx (measurementCount (E1QubitPlacement.tickF layout)) [] ++ r) vW.x vW.y vW.clean
  have hxy := ControlPointEncodingDevelop.pool_off_xy q hq
  refine (fr.2.2.2 q (fun h => hxy (List.mem_append_right _ h))
    (fun h => hxy (List.mem_append_left _ h))).trans ?_
  exact (regValue_zero _ _).mp vW.clean q hq

end Generic

/-! ## Block level: the generic block start, pulled through `rho`, with the case split on `G` -/

theorem pull_put_fix (f : Wire → Wire) (hf : Function.Injective f) (pk : Wire) (hfix : f pk = pk)
    (t : State) (v : Bool) :
    pullState f (ParityEven.put t pk v) = ParityEven.put (pullState f t) pk v := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases h : q = pk
    · subst h
      show Function.update t.basis q v (f q) = Function.update (fun r => t.basis (f r)) q v q
      rw [hfix]
      simp
    · have h' : f q ≠ pk := fun e => h (hf (e.trans hfix.symm))
      simp [pullState, ParityEven.put, writeBit, Function.update_apply, h, h']

section Block
open Arithmetic Baselines Secp256k1 ControlledPointLayout InputSentinel FlagEntry FlagTop ParityEven
attribute [local irreducible] run wires measurementCount g10

set_option maxHeartbeats 8000000 in
open Classical in
/-- From the state at the start of the generic block (the hypotheses of the record's
`hosted_format_runD`), every dialog-pool wire except `pkW` is false at the end of the hosted
multiplication kernel, in the coordinates pulled through `rho`. -/
theorem block10_pool
    (H : ∀ k, StairSemanticComposition.HostedReplayInterface k)
    (hE : StairSemanticFinal.EntrySupportD) (hX : StairSemanticFinal.ExitSupportD)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) (u : State)
    (hx : regValue layout.point.x u.basis =
      ControlPointEncodingDevelop.formatX (.some hc) b (dialogOrdinary b R (.some hc)) R)
    (hy : regValue layout.point.y u.basis =
      AboveFieldTagDevelop.formatY (.some hc) b (dialogOrdinary b R (.some hc)) R)
    (hf : u.basis layout.point.finite = false)
    (hg : u.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (he : u.basis layout.core.equalNegY = false) (hd : u.basis layout.doubleSelect = false)
    (hz : ∀q∈layout.dialogPool,q≠pkW layout→u.basis q=false)
    (hpk : u.basis (pkW layout)=(dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < ControlSentinelDevelop.ordinaryX R)))
    (m : List Bool) (q : Wire) (hq : q ∈ layout.dialogPool) (hqp : q ≠ pkW layout) :
    (run (g10 layout cx cy) m (pullState (rho layout) u)).basis q = false := by
  have hpkxy := ControlPointEncodingDevelop.pool_off_xy _ (FlagEntry.pk_pool layout layout_widths)
  let a := put u (pkW layout) false
  have ax : regValue layout.point.x a.basis = regValue layout.point.x u.basis :=
    regValue_congr _ _ _ (fun r hr => put_basis_ne _ _ _ _
      (fun e => hpkxy (e ▸ List.mem_append_left _ hr)))
  have ay : regValue layout.point.y a.basis = regValue layout.point.y u.basis :=
    regValue_congr _ _ _ (fun r hr => put_basis_ne _ _ _ _
      (fun e => hpkxy (e ▸ List.mem_append_right _ hr)))
  have af : a.basis layout.point.finite = false :=
    (put_basis_ne _ _ _ _ (by decide +kernel)).trans hf
  have ag : a.basis layout.genericSelect = dialogOrdinary b R (.some hc) :=
    (put_basis_ne _ _ _ _ (by decide +kernel)).trans hg
  have ae : a.basis layout.core.equalNegY = false :=
    (put_basis_ne _ _ _ _ (by decide +kernel)).trans he
  have ad : a.basis layout.doubleSelect = false :=
    (put_basis_ne _ _ _ _ (by decide +kernel)).trans hd
  have az : regValue layout.dialogPool a.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro r hr
    by_cases hp : r = pkW layout
    · subst hp
      simp [a, put, writeBit]
    · exact (put_basis_ne _ _ _ _ hp).trans (hz r hr hp)
  have restore : put a (pkW layout) (u.basis (pkW layout)) = u := by
    apply State.extensionality _ u
    · rfl
    funext r
    by_cases hp : r = pkW layout
    · subst hp
      simp [a, put, writeBit]
    · simp [a, put, writeBit, Function.update_apply, hp]
  have pu : pullState (rho layout) u =
      put (pullState (rho layout) a) (pkW layout) (u.basis (pkW layout)) := by
    rw [← pull_put_fix (rho layout) rho_injective (pkW layout) rho_pk, restore]
  refine (congrArg (fun t => (run (g10 layout cx cy) m t).basis q) pu).trans ?_
  beta_reduce
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  cases hG : dialogOrdinary b R (.some hc)
  · -- the ordinary point arithmetic is off: X, Y are the formatted words
    let X : Fp := ControlPointEncodingDevelop.formatX (.some hc) b false R
    let Y : Fp := AboveFieldTagDevelop.formatY (.some hc) b false R
    have hXv : X.val = ControlPointEncodingDevelop.formatX (.some hc) b false R :=
      ZMod.val_natCast_of_lt (AboveFieldTagDevelop.format_bounds (.some hc) b false R).1
    have hYv : Y.val = AboveFieldTagDevelop.formatY (.some hc) b false R :=
      ZMod.val_natCast_of_lt (AboveFieldTagDevelop.format_bounds (.some hc) b false R).2
    have pv := pulled_values a X Y false (ax.trans (hx.trans (by rw [hG, hXv])))
      (ay.trans (hy.trans (by rw [hG, hYv]))) af (ag.trans hG) ae ad az
    have hv : PointDialogValues layout X Y false (pullState (rho layout) a).basis
        (pullState (rho layout) a).basis := ⟨pv.1, pv.2.1, pv.2.2.1, pv.2.2.2, fun _ _ => rfl⟩
    have hpk0 : u.basis (pkW layout) = false := by simpa only [hG, Bool.false_and] using hpk
    have hX0 := ControlPointEncodingDevelop.formatX_fp_ne_zero (.some hc) b false R
    exact g10_pool H hE hX cx cy X Y false (pullState (rho layout) a) (u.basis (pkW layout)) hv
      (by rw [hpk0, pv.2.2.1]; rfl)
      (by simpa only [Bool.false_eq_true, if_false, add_zero] using hX0)
      (by simpa only [Bool.false_eq_true, if_false, add_zero, sub_zero] using hX0) m q hq hqp
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have hx' : regValue layout.point.x u.basis = x.val := by
        have e : regValue layout.point.x u.basis = codeX (.some hr) := by
          rw [ControlPointEncodingDevelop.codeX_ordinary]
          simpa only [ControlPointEncodingDevelop.formatX, hG, Bool.not_true, Bool.and_false,
            Bool.false_eq_true, if_false] using hx
        exact e
      have hy' : regValue layout.point.y u.basis = y.val := by
        have e : regValue layout.point.y u.basis = pointY (.some hr) := by
          simpa only [AboveFieldTagDevelop.formatY, hG, Bool.not_true, Bool.and_false,
            Bool.false_eq_true, if_false] using hy
        exact e
      have pv := pulled_values a x y true (ax.trans hx') (ay.trans hy') af (ag.trans hG) ae ad az
      have hv : PointDialogValues layout x y true (pullState (rho layout) a).basis
          (pullState (rho layout) a).basis := ⟨pv.1, pv.2.1, pv.2.2.1, pv.2.2.2, fun _ _ => rfl⟩
      have hflag : u.basis (pkW layout) = (if (pullState (rho layout) a).basis layout.core.generic then
          decide (EntryFuseArithmetic.prime ≤ x.val + (-cx).val) else false) := by
        rw [hpk, ← ControlPointEncodingDevelop.codeX_ordinary, flag_eq hc b (.some hr) x rfl, pv.2.2.1,
          hG]
      let sl := genericSlope x y cx cy
      let d := cx - genericX x y cx cy
      have hvv := generic_inplace_values x y cx cy den.1
      have ha : (y-cy)/(x-cx) = sl := rfl
      have hd4 : (x-cx)-sl*sl+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx = d := by
        have e := hvv.2.1
        change (x-cx)-sl*sl+3*cx = d at e
        rw [← e]
        unfold ReflectionE1.correction
        ring
      refine g10_pool H hE hX cx cy x y true (pullState (rho layout) a) (u.basis (pkW layout)) hv
        hflag ?_ ?_ m q hq hqp
      · simpa only [if_true, ← sub_eq_add_neg] using sub_ne_zero.mpr den.1
      · simp only [if_true, ← sub_eq_add_neg, ha]
        rw [hd4]
        exact den.2

end Block

/-! ## Outer level: from the encoded input to the generic block start -/

open Classical in
/-- The state after `stageNew ++ encode ++ eraseB` (logical coordinates of `fU`): the hypotheses of the
record's `hosted_format_runD` plus a clean control wire. -/
structure GenericStart {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (u : State) : Prop where
  x : regValue Baselines.layout.point.x u.basis =
    ControlPointEncodingDevelop.formatX (.some hc) b (dialogOrdinary b R (.some hc)) R
  y : regValue Baselines.layout.point.y u.basis =
    AboveFieldTagDevelop.formatY (.some hc) b (dialogOrdinary b R (.some hc)) R
  finite : u.basis Baselines.layout.point.finite = false
  generic : u.basis Baselines.layout.genericSelect = dialogOrdinary b R (.some hc)
  eneg : u.basis Baselines.layout.core.equalNegY = false
  double : u.basis Baselines.layout.doubleSelect = false
  control : u.basis Baselines.layout.control = false
  clean : ∀ q ∈ Baselines.layout.dialogPool, q ≠ FlagEntry.pkW Baselines.layout → u.basis q = false
  parked : u.basis (FlagEntry.pkW Baselines.layout) = (dialogOrdinary b R (.some hc) &&
    decide ((InputSentinel.triOf (.some hc)).A < ControlSentinelDevelop.ordinaryX R))

/-- The outer prefix of the record program (pieces 0, 1, 2 before placement). -/
def outerHead (C : Point) : Program :=
  FlagTop.stageNew Baselines.layout C (FlagEntry.pkW Baselines.layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB

section Outer
open ControlPointEncodingDevelop
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel FlagTop FlagExit
  FlagTop2 ParityEven ControlGenericPointDevelop
attribute [local irreducible] layout run wires

set_option maxHeartbeats 8000000 in
open Classical in
theorem genericStart_of_encodes {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (R : Point) (s : State) (hs : encodes b R s.basis) (m : List Bool) :
    GenericStart hc b R (run (outerHead (.some hc)) m s) := by
  let C : Point := .some hc
  have hi := StairCallerMiddle.boundary_of_encodes b R s hs
  suffices key : ∀ m0 me ma, GenericStart hc b R (run AboveFieldPointDevelop.eraseB ma
      (run (AboveFieldPointDevelop.encode C) me (run (stageNew layout C (FlagEntry.pkW layout)) m0 s))) by
    rw [outerHead, run_append, run_append]
    exact key _ _ _
  intro m0 me ma
  have st := stage_values hc b R s m0 hi
  generalize run (stageNew layout C (FlagEntry.pkW layout)) m0 s = t at st ⊢
  let G := dialogOrdinary b R C
  have hG : G = ControlSentinelDevelop.generic C b R :=
    ControlSentinelDevelop.generic_agrees C R b (WeierstrassCurve.Affine.Point.some_ne_zero hc)
  have hcorner : (b && !G) = true → ControlSentinelDevelop.corner C R := by
    rw [hG]
    cases b <;> by_cases hr : ControlSentinelDevelop.corner C R <;>
      simp [ControlSentinelDevelop.generic, hr]
  have hgb : G = true → b = true := by
    rw [hG]
    cases b <;> simp [ControlSentinelDevelop.generic]
  have hp := AboveFieldPointDevelop.encode_spec hc b G R t me hgb hcorner st.x st.y st.control
    st.generic (fun i => st.clean _ (work_pool i) (work_off_pk i))
  generalize run (AboveFieldPointDevelop.encode C) me t = a at hp ⊢
  have ha : XYResult t a (formatX C b G R) (AboveFieldTagDevelop.formatY C b G R) := hp.1
  have apool : ∀ q ∈ layout.dialogPool, q ≠ FlagEntry.pkW layout → a.basis q = false := by
    intro q hq hpq
    exact (ha.rest q (pool_off_xy q hq)).trans (st.clean q hq hpq)
  have af : a.basis layout.point.finite = false := (ha.rest _ finite_off_xy).trans st.finite
  have ag : a.basis layout.genericSelect = G := (ha.rest _ generic_off_xy).trans st.generic
  have ab : a.basis layout.control = b := (ha.rest _ control_off_xy).trans st.control
  have ae : a.basis layout.core.equalNegY = false := (ha.rest _ eneg_off_xy).trans st.eneg
  have ad : a.basis layout.doubleSelect = false := (ha.rest _ double_off_xy).trans st.double
  have apk : a.basis (FlagEntry.pkW layout) =
      (G && decide ((triOf C).A < ControlSentinelDevelop.ordinaryX R)) :=
    (ha.rest _ (pool_off_xy _ (FlagEntry.pk_pool layout layout_widths))).trans st.parked
  have erase : run AboveFieldPointDevelop.eraseB ma a = put a layout.control false := by
    apply AboveFieldPointDevelop.eraseB_run a ma (formatX C b G R)
      (AboveFieldTagDevelop.formatY C b G R) ha.x ha.y af
      (fun q hq => apool _ (AboveFieldPointDevelop.marker_work_pool q hq)
        (AboveFieldPointDevelop.marker_work_off_pk q hq))
    rw [ag, AboveFieldPointDevelop.format_recover C b G R hgb]
    exact ab
  rw [erase]
  exact
    { x := (put_basis_reg _ _ _ _ (by decide +kernel)).trans ha.x
      y := (put_basis_reg _ _ _ _ (by decide +kernel)).trans ha.y
      finite := (put_basis_ne a _ _ false finite_off_control).trans af
      generic := (put_basis_ne a _ _ false generic_off_control).trans ag
      eneg := (put_basis_ne a _ _ false eneg_off_control).trans ae
      double := (put_basis_ne a _ _ false double_off_control).trans ad
      control := by simp [put, writeBit]
      clean := fun q hq hpq => (put_basis_ne a _ _ false (pool_off_control q hq)).trans (apool q hq hpq)
      parked := (put_basis_ne a _ _ false pk_off_control).trans apk }

end Outer

/-! ## Physical level: the first ten pieces -/

theorem renameProgram_app (f : Wire → Wire) (a b : Program) :
    renameProgram f (a ++ b) = renameProgram f a ++ renameProgram f b := by
  simp only [renameProgram, List.map_append]

theorem fU_injective : Function.Injective fU := (Wrapper5.U L0).injective

theorem fG_injective : Function.Injective fG := fun a b h =>
  FlagTop.rho_injective ((Equiv.swap L0.doubleSelect L0.control).injective
    ((Wrapper5.U L0).injective h))

section Phys
attribute [local irreducible] FlagTop.stageNew AboveFieldTagDevelop.encode AboveFieldPointDevelop.eraseB
  ParityUniform.entryYAll FlagEntry.entryXNew StairConcreteAssembly.hostedEntryRest
  StairSquareFinal.squareEntryHL Rolling1588TickGap.tailPhase StairHostsSchedule.exitFieldHosted
  StairSchedule.stackReverse15 ParityXExit.prefixAll wireFn2 Rolling1588Lifetime.phaseHost
  ParityXExitInverse23Kernel.pi FlagTop.rho Wrapper5.U

theorem exitRest_pieces (cx : Fp) :
    renameProgram fG (StairConcreteAssembly.hostedExitRest L0 cx.val) = p7 ++ p8 cx ++ p9 := by
  simp only [StairConcreteAssembly.hostedExitRest, StairHostsSchedule.lastXN,
    ParityXExitInverse23Kernel.x1N, ParityXExitInverse23Kernel.x1N0, ParityXExit.programN, p7, p8, p9,
    fP_eq, fK_eq, renameProgram_app, List.append_assoc]

theorem pre10_eq {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    pre (.some hc) cx cy 10 =
      renameProgram fU (outerHead (.some hc)) ++ renameProgram fG (g10 L0 cx cy) := by
  have e : pre (.some hc) cx cy 10 = p0 (.some hc) ++ p1 (.some hc) ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++
      p6 cx ++ p7 ++ p8 cx ++ p9 := rfl
  rw [e]
  simp only [outerHead, g10, renameProgram_app, exitRest_pieces, p0, p1, p2, p3, p4, p5, p6,
    List.append_assoc]

end Phys

/-- Removing a final piece that does not touch `w` does not change `w` (same tape). -/
theorem back_step (A P : Program) (w : Wire) (hw : w ∉ wires P) (m : List Bool) (s : State) :
    (run (A ++ P) m s).basis w = (run A m s).basis w :=
  (congrArg (fun t : State => t.basis w) (run_append A P m s)).trans
    ((run_preserves_outside P _ _ w hw).trans
      (congrArg (fun t : State => t.basis w) (run_take A m s)))

/-- The park: two CNOTs between physical 4629 and 4839. -/
theorem p9_eq : p9 = [.CX 4629 4839, .CX 4839 4629] := by decide +kernel

theorem run_park (m : List Bool) (t : State) : (run p9 m t).basis 4629 = t.basis 4839 := by
  rw [p9_eq]
  simp only [run, writeBit, Function.update_apply]
  cases t.basis 4629 <;> cases t.basis 4839 <;> decide

theorem notIn9_of_park (w : Wire) (h1 : w ≠ 4629) (h2 : w ≠ 4839) : w ∉ wires p9 := by
  rw [p9_eq]
  simp [wires, Instr.wires, h1, h2]

end ExitAux

open ExitAux

/-- Boundary 10 (the output of the hosted multiplication kernel): every dialog-pool wire of the generic
layout except the parked flag is clean, at its physical placement `fG`. -/
theorem clean10_pool {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (q : Wire)
    (hq : q ∈ L0.dialogPool) (hqp : q ≠ FlagEntry.pkW L0) : CleanAt hc 10 (fG q) := by
  have H : ∀ k, StairSemanticComposition.HostedReplayInterface k :=
    StairSemanticComposition.hostedReplayInterface_of
      (StairHostReplayField.hostReplay_of_field
        (StairOpenWiring.host_replay_of StairOpenWiring.remaining))
      (StairCertificate.replay_interfaces
        (StairOpenWiring.stairOpen_of_remaining StairOpenWiring.remaining))
  intro b R s hs m
  refine (congrArg (fun P => (run P m s).basis (fG q)) (pre10_eq hc)).trans ?_
  beta_reduce
  refine (congrArg (fun t : State => t.basis (fG q)) (run_append _ _ m s)).trans ?_
  beta_reduce
  generalize m.take _ = m1
  generalize m.drop _ = m2
  generalize ht1 : run (renameProgram fU (outerHead (.some hc))) m1 s = t1
  have pr := run_rename fG fG_injective (g10 L0 cx cy) m2 t1
  refine (congrArg (fun t : State => t.basis q) pr).trans ?_
  beta_reduce
  have pulled : pullState fU s = s := by
    change pullState (Equiv.swap (L0.core.poolWire 684) (L0.core.poolWire 717)) s = s
    exact FieldFrameOB5.pull_swap_zero _ _ s (hs.2.2 _ (by decide +kernel))
      (hs.2.2 _ (by decide +kernel))
  have hu : pullState fU t1 = run (outerHead (.some hc)) m1 s := by
    rw [← ht1, run_rename fU fU_injective, pulled]
  have start := genericStart_of_encodes hc b R s hs m1
  have e2 : pullState fG t1 = pullState (FlagTop.rho L0) (run (outerHead (.some hc)) m1 s) := by
    change pullState (FlagTop.rho L0)
      (pullState (Equiv.swap L0.doubleSelect L0.control) (pullState fU t1)) = _
    rw [hu, FieldFrameOB5.pull_swap_zero _ _ _ start.double start.control]
  refine (congrArg (fun t => (run (g10 L0 cx cy) m2 t).basis q) e2).trans ?_
  exact block10_pool H StairSemanticFinal.entrySupportV3 StairSemanticFinal.exitSupportV3 hc b R _
    start.x start.y start.finite start.generic start.eneg start.double start.clean start.parked
    m2 q hq hqp

/-- Boundary 10 for 4112 (`fG (poolWire 717)`). -/
theorem clean10_wZ {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : CleanAt hc 10 wZ := by
  have e : fG (L0.core.poolWire 717) = wZ := by decide +kernel
  exact e ▸ clean10_pool hc _ (Square5Placement.pool_member L0 Baselines.layout_widths 717 (by omega))
    (by decide +kernel)

namespace ExitAux

theorem pre10_split {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    pre (.some hc) cx cy 10 = pre (.some hc) cx cy 9 ++ p9 := rfl

theorem pre9_split {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    pre (.some hc) cx cy 9 = pre (.some hc) cx cy 8 ++ p8 cx := rfl

end ExitAux

section Back
attribute [local irreducible] run pre

namespace ExitAux

/-- A wire clean at boundary 10 and untouched by the park is clean at boundary 9. -/
theorem clean9_of {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (w : Wire)
    (h10 : CleanAt hc 10 w) (h9 : w ∉ wires p9) : CleanAt hc 9 w := by
  intro b R s hs m
  exact (back_step _ p9 w h9 m s).symm.trans
    ((congrArg (fun P => (run P m s).basis w) (pre10_split hc)).symm.trans (h10 b R s hs m))

/-- A wire clean at boundary 9 and untouched by the body of `x1N` is clean at boundary 8. -/
theorem clean8_of {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (w : Wire)
    (h9c : CleanAt hc 9 w) (h8 : w ∉ wires (p8 cx)) : CleanAt hc 8 w := by
  intro b R s hs m
  exact (back_step _ (p8 cx) w h8 m s).symm.trans
    ((congrArg (fun P => (run P m s).basis w) (pre9_split hc)).symm.trans (h9c b R s hs m))

end ExitAux


theorem clean9_wZ {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : CleanAt hc 9 wZ :=
  clean9_of hc wZ (clean10_wZ hc) (notIn9_of_park wZ (by decide) (by decide))

/-- **Z8** (S1): 4112 is clean before the body of `x1N`, given that `p8` does not touch it. -/
theorem clean8_wZ_of {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (h8 : wZ ∉ wires (p8 cx)) : CleanAt hc 8 wZ :=
  clean8_of hc wZ (clean9_wZ hc) h8

end Back

end ECDSAAdd.Entrant.Rehost
