import ECDSAAdd.Submission.Entrant.SharedBlock

/-! Shared point tests on the public controlled layout.

For a finite classical `C = (cx, cy)` a valid point `R` equals `C` exactly when
its finite flag is set, `x = cx`, and the low bit of `y` equals the low bit of
`cy`: by the curve equation a finite `R` with `x = cx` has `y = ±cy`, and since
`p` is odd, `cy` and `-cy` have different low bits whenever they differ.  So
the tests `R = C` and `R = -C` share the finite/`x` part of one AND chain,
followed by a single `y` parity link, and `R = -C` is obtained from the `x`
link and the full link with Clifford gates. -/
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout

def ptXB (L : ControlledPointLayout) : List ZeroBit :=
  zeroPorts (L.point.finite :: L.point.x) (L.dialogPool.take 257)
def ptYB (L : ControlledPointLayout) : List ZeroBit :=
  zeroPorts (L.point.y.take 1) ((L.dialogPool.take 258).drop 257)

def sharedPoint (L : ControlledPointLayout) (k tk tc : Wire) (cx cy : Fp) (kSplit cSplit : Bool) : Program :=
  sharedBlock L.control k tk tc (ptXB L) (ptYB L) (1 + 2 * cx.val) (cy.val % 2) kSplit cSplit

section
variable (L : ControlledPointLayout) (hw : L.Widths)
include hw

theorem point_lengths : L.point.x.length = 256 ∧ L.point.y.length = 256 := ⟨hw.inputX, hw.inputY⟩

theorem ptXB_maps : (ptXB L).map ZeroBit.input = L.point.finite :: L.point.x ∧
    (ptXB L).map ZeroBit.work = L.dialogPool.take 257 :=
  zeroPorts_maps _ _ (by simp [(point_lengths L hw).1, L.dialogPool_length hw])

theorem ptYB_maps : (ptYB L).map ZeroBit.input = L.point.y.take 1 ∧
    (ptYB L).map ZeroBit.work = (L.dialogPool.take 258).drop 257 :=
  zeroPorts_maps _ _ (by simp [(point_lengths L hw).2, L.dialogPool_length hw])

theorem ptXB_length : (ptXB L).length = 257 := by
  have h := congrArg List.length (ptXB_maps L hw).1
  simpa [(point_lengths L hw).1] using h

theorem ptYB_length : (ptYB L).length = 1 := by
  have h := congrArg List.length (ptYB_maps L hw).1
  simpa [(point_lengths L hw).2] using h

omit hw in
theorem pool_split : L.dialogPool.take 257 ++ (L.dialogPool.take 258).drop 257 = L.dialogPool.take 258 := by
  have h : (L.dialogPool.take 258).take 257 = L.dialogPool.take 257 := by
    rw [List.take_take]; rfl
  rw [← h, List.take_append_drop]

include hw

theorem sharedPoint_names (hn : L.wires.Nodup) (k tk tc : Wire) (hf : [k, tk, tc].Nodup)
    (hmem : ∀ q ∈ [k, tk, tc], q ∈ L.inPlaceFlags) :
    SharedNames L.control k tk tc (ptXB L) (ptYB L) := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.nodup_iff_count_le_one.mpr
    intro w
    have hU := List.nodup_iff_count_le_one.mp (L.dialogUsed_nodup hn) w
    have hX := (zeroPorts_perm (L.point.finite :: L.point.x) (L.dialogPool.take 257)
      (by simp [(point_lengths L hw).1, L.dialogPool_length hw])).count_eq w
    have hY := (zeroPorts_perm (L.point.y.take 1) ((L.dialogPool.take 258).drop 257)
      (by simp [(point_lengths L hw).2, L.dialogPool_length hw])).count_eq w
    have hYt := (List.take_sublist 1 L.point.y).count_le w
    have hF := (List.subperm_of_subset hf hmem).count_le w
    have hP : (L.dialogPool.take 257).count w + ((L.dialogPool.take 258).drop 257).count w ≤
        L.dialogPool.count w := by
      rw [← List.count_append, pool_split L]
      exact (List.take_sublist _ _).count_le w
    change ([k, tk, tc] ++ ([L.control] ++ (ptXB L).flatMap ZeroBit.wires ++
      (ptYB L).flatMap ZeroBit.wires)).count w ≤ 1
    simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append] at hU hX hY ⊢
    simp only [ptXB, ptYB] at ⊢
    omega
  · intro h; have := ptXB_length L hw; rw [h] at this; simp at this
  · intro h; have := ptYB_length L hw; rw [h] at this; simp at this

end

theorem code_decide (F : Bool) (X c : Nat) :
    decide ((if F then 1 else 0) + 2 * X = 1 + 2 * c) = (F && decide (X = c)) := by
  cases F
  · simp; omega
  · simp

theorem regValue_cons (w : Wire) (ws : List Wire) (s : BasisState) :
    regValue (w :: ws) s = (if s w then 1 else 0) + 2 * regValue ws s := rfl

theorem regValue_take_one (ws : List Wire) (s : BasisState) :
    regValue (ws.take 1) s = regValue ws s % 2 := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    rw [List.take_succ_cons, List.take_zero, regValue_cons, regValue_cons]
    change (if s w then 1 else 0) + 2 * 0 = ((if s w then 1 else 0) + 2 * regValue ws s) % 2
    split <;> omega

/-- Distinct field values that are negatives of each other differ in their low bit. -/
theorem neg_parity {y : Fp} (hy : y ≠ -y) : (-y).val % 2 ≠ y.val % 2 := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have h0 : y ≠ 0 := by rintro rfl; simp at hy
  have hv := ZMod.neg_val y
  rw [if_neg h0] at hv
  have hlt := ZMod.val_lt y
  have hp : p % 2 = 1 := by norm_num [p]
  rw [hv]
  omega

theorem sharedPoint_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (b : Bool) (f : BasisState) (k tk tc : Wire) (hf : [k, tk, tc].Nodup)
    (hmem : ∀ q ∈ [k, tk, tc], q ∈ L.inPlaceFlags) (cx cy : Fp) (kSplit cSplit : Bool) :
    Triple (PointDialogBoundary L R b f) (sharedPoint L k tk tc cx cy kSplit cSplit)
      (PointDialogBoundary L R b (upd2 f tk tc
        (f k && ((kSplit && (b && (pointFinite R && decide (pointX R = cx.val)))) ^^
          ((b && (pointFinite R && decide (pointX R = cx.val))) && decide (pointY R % 2 = cy.val % 2))))
        ((cSplit && (b && (pointFinite R && decide (pointX R = cx.val)))) ^^
          ((b && (pointFinite R && decide (pointX R = cx.val))) && decide (pointY R % 2 = cy.val % 2))))) := by
  intro s m v
  have names := sharedPoint_names L hw hn k tk tc hf hmem
  have htc : tk ≠ tc := by
    intro h; simp [h] at hf
  have clean (q : Wire) (hq : q ∈ L.dialogPool.take 258) : s.basis q = false :=
    (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq)
  have hzx : ∀ bb ∈ ptXB L, s.basis bb.work = false := by
    intro bb hb
    apply clean
    rw [← pool_split L]
    apply List.mem_append_left
    rw [← (ptXB_maps L hw).2]
    exact List.mem_map.mpr ⟨bb, hb, rfl⟩
  have hzy : ∀ bb ∈ ptYB L, s.basis bb.work = false := by
    intro bb hb
    apply clean
    rw [← pool_split L]
    apply List.mem_append_right
    rw [← (ptYB_maps L hw).2]
    exact List.mem_map.mpr ⟨bb, hb, rfl⟩
  have hkx : 1 + 2 * cx.val < 2 ^ (ptXB L).length := by
    rw [ptXB_length L hw]; have := ZMod.val_lt cx; norm_num [p] at this ⊢; omega
  have hky : cy.val % 2 < 2 ^ (ptYB L).length := by
    rw [ptYB_length L hw]; exact Nat.mod_lt _ (by norm_num)
  have hrun := sharedBlock_run L.control k tk tc (ptXB L) (ptYB L) (1 + 2 * cx.val) (cy.val % 2)
    kSplit cSplit names hkx hky s m hzx hzy
  have hpt := (point_holds _ _ _).mp v.point
  have hex : (s.basis L.control && decide (regValue ((ptXB L).map ZeroBit.input) s.basis = 1 + 2 * cx.val)) =
      (b && (pointFinite R && decide (pointX R = cx.val))) := by
    rw [(ptXB_maps L hw).1, regValue_cons, hpt.1, hpt.2.1, code_decide, v.control]
  have hey : decide (regValue ((ptYB L).map ZeroBit.input) s.basis = cy.val % 2) =
      decide (pointY R % 2 = cy.val % 2) := by
    rw [(ptYB_maps L hw).1, regValue_take_one, hpt.2.2]
  have hkf : s.basis k = f k := v.flags k (hmem k (by simp))
  simp only at hrun
  rw [hex, hey, hkf] at hrun
  change run (sharedBlock L.control k tk tc (ptXB L) (ptYB L) (1 + 2 * cx.val) (cy.val % 2) kSplit cSplit) m s = _ at hrun
  refine ⟨by simp only [sharedPoint]; rw [hrun], v.withFlags hn ?_ ?_⟩
  · intro q hq
    simp only [sharedPoint]
    rw [hrun]
    simp only [upd2_apply _ _ _ _ _ htc]
    rw [v.flags tc (hmem tc (by simp)), v.flags tk (hmem tk (by simp)), v.flags q hq]
  · intro q hq
    simp only [sharedPoint]
    rw [hrun]
    have h1 : q ≠ tc := fun h => hq (h ▸ hmem tc (by simp))
    have h2 : q ≠ tk := fun h => hq (h ▸ hmem tk (by simp))
    simp [upd2_apply _ _ _ _ _ htc, h1, h2]

/-- Point-test identities used by the shared chain. -/
theorem shared_math (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    pointEqual R (.some hc) = ((pointFinite R && decide (pointX R = cx.val)) &&
      decide (pointY R % 2 = cy.val % 2)) ∧
    pointEqual R (-(.some hc)) = ((decide (cy ≠ -cy) && (pointFinite R && decide (pointX R = cx.val))) ^^
      ((pointFinite R && decide (pointX R = cx.val)) && decide (pointY R % 2 = cy.val % 2))) := by
  classical
  have hneg : (-(WeierstrassCurve.Affine.Point.some hc : Point)) =
      WeierstrassCurve.Affine.Point.some ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hc) :=
    WeierstrassCurve.Affine.Point.neg_some hc
  cases R with
  | zero =>
    have h1 : pointEqual 0 (.some hc) = false := by
      cases h : pointEqual 0 (.some hc)
      · rfl
      · exact absurd ((pointEqual_true_iff _ _).mp h).symm (WeierstrassCurve.Affine.Point.some_ne_zero hc)
    have h2 : pointEqual 0 (-(.some hc)) = false := by
      cases h : pointEqual 0 (-(.some hc))
      · rfl
      · have := ((pointEqual_true_iff _ _).mp h).symm
        rw [hneg] at this
        exact absurd this (WeierstrassCurve.Affine.Point.some_ne_zero _)
    change pointEqual 0 (.some hc) = _ ∧ pointEqual 0 (-(.some hc)) = _
    rw [h1, h2]
    simp [pointFinite, coordinates]
  | @some x y h =>
    have hx : decide (pointX (.some h) = cx.val) = decide (x = cx) := by
      simp [pointX, coordinates, ZMod.val_injective _ |>.eq_iff]
    have hy : decide (pointY (.some h) % 2 = cy.val % 2) = decide (y.val % 2 = cy.val % 2) := by
      simp [pointY, coordinates]
    have hf : pointFinite (.some h) = true := rfl
    rw [hx, hy, hf]
    have e1 : pointEqual (.some h) (.some hc) = decide (x = cx ∧ y = cy) := by
      apply Bool.eq_iff_iff.mpr
      rw [pointEqual_true_iff, decide_eq_true_eq, WeierstrassCurve.Affine.Point.some.injEq]
    have e2 : pointEqual (.some h) (-(.some hc)) = decide (x = cx ∧ y = -cy) := by
      apply Bool.eq_iff_iff.mpr
      rw [pointEqual_true_iff, decide_eq_true_eq, hneg, WeierstrassCurve.Affine.Point.some.injEq,
        negY_eq_neg]
    rw [e1, e2]
    by_cases hxc : x = cx
    · subst hxc
      have hyy := WeierstrassCurve.Affine.Y_eq_of_X_eq h.1 hc.1 rfl
      rw [negY_eq_neg] at hyy
      simp only [decide_true, Bool.true_and, true_and]
      rcases hyy with h1 | h1
      · subst h1
        by_cases h' : y = -y
        · simp [← h']
        · simp [h']
      · subst h1
        by_cases h' : cy = -cy
        · rw [show -cy = cy from h'.symm]; simp
        · have hp := neg_parity h'
          have hne : -cy ≠ cy := fun e => h' e.symm
          simp [h', hne, hp]
    · simp [hxc]

end ECDSAAdd.Entrant
