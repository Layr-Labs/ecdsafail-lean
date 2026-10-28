import ECDSAAdd.Arithmetic.SkywalkControlled
import ECDSAAdd.Arithmetic.SkywalkPointLayout
import ECDSAAdd.Arithmetic.SkywalkArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- Safe controlled point arithmetic on the existing caller coordinates.
The original multiply selector is retained; the underlying port uses divide. -/
def pointSkywalkArithmetic (L : ControlledPointLayout) (multiply : Bool) : Program :=
  skywalkControlledProgram (skywalkArithmetic (!multiply) L.skywalkSharedMap)
    L.core.generic L.point.x L.skywalkSafeX

attribute [local irreducible] skywalkArithmetic skywalkControlledProgram pointSkywalkArithmetic run SkywalkArithmeticStrong

private theorem caller_regions (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.core.generic::L.point.x++L.skywalkSafeX++L.point.y++wireBlock L.core.poolWire 0 1802).Nodup := by
  have hcaller := L.skywalkCaller_nodup hw hn
  have hp : wireBlock L.core.poolWire 0 2058=
      wireBlock L.core.poolWire 0 1802++L.skywalkSafeX := by
    exact (wireBlock_append _ 0 1802 256).symm
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hcaller q
  rw [hp] at h
  simp only [List.count_cons,List.count_append] at h ⊢
  omega

/-- Replacement for pointDialog_arithmetic_correct with exactly its guarded
zero-divisor contract and full outside-callerY frame. -/
theorem pointSkywalkArithmetic_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (pointSkywalkArithmetic L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (pointSkywalkArithmetic L multiply) m s).basis=V ∧
      ∀q,q∉L.point.y → (run (pointSkywalkArithmetic L multiply) m s).basis q=s.basis q := by
  dsimp only
  let D := if B then X else 1
  let R := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
  have hYval : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  have hpositive : 0<D := by
    dsimp only [D]
    split
    · exact Nat.pos_of_ne_zero (hX0 (by assumption))
    · omega
  have hbound : D<p := by
    dsimp only [D]
    split
    · exact hX
    · norm_num [p]
  have hresult : (skywalkArithmeticResult (!multiply) D (Y:Fp)).val=R := by
    cases B with
    | true => cases multiply <;> rfl
    | false => cases multiply <;> simpa [D,R,skywalkArithmeticResult] using hYval
  have hpool := L.skywalkCaller_zero hw s.basis hc
  have hd0 : regValue L.skywalkSafeX s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    apply (regValue_zero _ _).mp hpool q
    rw [show wireBlock L.core.poolWire 0 2058=
      wireBlock L.core.poolWire 0 1802++L.skywalkSafeX from (wireBlock_append _ 0 1802 256).symm]
    exact List.mem_append_right _ hq
  have hp0 : regValue (wireBlock L.core.poolWire 0 1802) s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    apply (regValue_zero _ _).mp hpool q
    rw [show wireBlock L.core.poolWire 0 2058=
      wireBlock L.core.poolWire 0 1802++L.skywalkSafeX from (wireBlock_append _ 0 1802 256).symm]
    exact List.mem_append_left _ hq
  have kernel : ∀ (st : State) (ms : List Bool),
      regValue L.skywalkSafeX st.basis=D → regValue L.point.y st.basis=Y →
      regValue (wireBlock L.core.poolWire 0 1802) st.basis=0 →
      (run (skywalkArithmetic (!multiply) L.skywalkSharedMap) ms st).phase=st.phase ∧
      regValue L.point.y (run (skywalkArithmetic (!multiply) L.skywalkSharedMap) ms st).basis=R ∧
      ∀q,q∉L.point.y →
        (run (skywalkArithmetic (!multiply) L.skywalkSharedMap) ms st).basis q=st.basis q := by
    intro st ms hd hy hp
    generalize hout : run (skywalkArithmetic (!multiply) L.skywalkSharedMap) ms st=out
    have input : SkywalkArithmeticInput L.skywalkSharedMap D (Y:Fp).val st.basis := by
      unfold SkywalkArithmeticInput skywalkArithmeticDivisor skywalkArithmeticNumerator
      change regValue (wireBlock (skywalkPointWire L.core.poolWire L.skywalkSafeX L.point.y) 770 256) st.basis=D ∧
        regValue (wireBlock (skywalkPointWire L.core.poolWire L.skywalkSafeX L.point.y) 2056 256) st.basis=(Y:Fp).val ∧
        ∀ q∈skywalkSharedWires (skywalkPointWire L.core.poolWire L.skywalkSafeX L.point.y),
          q∉wireBlock (skywalkPointWire L.core.poolWire L.skywalkSafeX L.point.y) 770 256 →
          q∉wireBlock (skywalkPointWire L.core.poolWire L.skywalkSafeX L.point.y) 2056 256 → st.basis q=false
      rw [skywalkPointWire_x L.core.poolWire L.skywalkSafeX L.point.y L.skywalkSafeX_length,
        skywalkPointWire_y L.core.poolWire L.skywalkSafeX L.point.y hw.inputY]
      exact ⟨hd,hy.trans hYval.symm,
        skywalkPointWire_clean L.core.poolWire L.skywalkSafeX L.point.y L.skywalkSafeX_length hw.inputY st.basis hp⟩
    have strong := skywalkArithmetic_run (!multiply) L.skywalkSharedMap
      (L.skywalkSharedMap_nodup hw hn) L.core.generic (L.skywalkSharedMap_control hw hn)
      D (Y:Fp) hpositive hbound st ms input
    rw [hout] at strong
    unfold SkywalkArithmeticStrong at strong
    have hread : regValue L.point.y out.basis=R := by
      have hyw := skywalkPointWire_y L.core.poolWire L.skywalkSafeX L.point.y hw.inputY
      have hh := strong.2.1
      change regValue (wireBlock (skywalkPointWire L.core.poolWire L.skywalkSafeX L.point.y) 2056 256) _=_ at hh
      rw [hyw,hresult] at hh
      exact hh
    have hframe : ∀q,q∉L.point.y → out.basis q=st.basis q := by
      simpa only [skywalkArithmeticNumerator,skywalkSharedMap,
        skywalkPointWire_y L.core.poolWire L.skywalkSafeX L.point.y hw.inputY] using strong.2.2
    exact ⟨strong.1,hread,hframe⟩
  have h := skywalkControlled_core_correct (skywalkArithmetic (!multiply) L.skywalkSharedMap)
    L.core.generic L.point.x L.skywalkSafeX L.point.y (wireBlock L.core.poolWire 0 1802)
    (hw.inputX.trans L.skywalkSafeX_length.symm) (caller_regions L hw hn)
    (by rw [L.skywalkSafeX_length]; norm_num) X Y R B kernel s m hb hx hy hd0 hp0
  simpa only [pointSkywalkArithmetic] using h

/-- Counts are those of the actual kernel plus the two256-bit safe copies. -/
theorem pointSkywalkArithmetic_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (pointSkywalkArithmetic L false)=1315329 ∧
    measurementCount (pointSkywalkArithmetic L false)=986367 ∧
    toffoliCount (pointSkywalkArithmetic L true)=1315330 ∧
    measurementCount (pointSkywalkArithmetic L true)=986368 := by
  have ha := skywalkArithmetic_counts L.skywalkSharedMap (L.skywalkSharedMap_nodup hw hn)
    L.core.generic (L.skywalkSharedMap_control hw hn)
  have hdiv := skywalkControlled_core_counts (skywalkArithmetic true L.skywalkSharedMap)
    L.core.generic L.point.x L.skywalkSafeX (hw.inputX.trans L.skywalkSafeX_length.symm)
  have hmul := skywalkControlled_core_counts (skywalkArithmetic false L.skywalkSharedMap)
    L.core.generic L.point.x L.skywalkSafeX (hw.inputX.trans L.skywalkSafeX_length.symm)
  simp only [pointSkywalkArithmetic,Bool.not_false,Bool.not_true] at ⊢
  have hxlen : L.point.x.length=256 := hw.inputX
  rw [hdiv.1,hdiv.2,hmul.1,hmul.2,ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hxlen]
  norm_num

/-- Physical support fits the old caller workspace; no functional-frame-to-
support inference or old3134-wire equality is used. -/
theorem pointSkywalkArithmetic_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointSkywalkArithmetic L multiply) ⊆
      (L.core.generic::L.point.x++L.point.y++wireBlock L.core.poolWire 0 2058).toFinset := by
  have hwrap := skywalkControlled_core_support (skywalkArithmetic (!multiply) L.skywalkSharedMap)
    L.core.generic L.point.x L.skywalkSafeX (hw.inputX.trans L.skywalkSafeX_length.symm)
  have hk := skywalkArithmetic_support (!multiply) L.skywalkSharedMap (L.skywalkSharedMap_nodup hw hn)
  have split : wireBlock L.core.poolWire 0 2058=
      wireBlock L.core.poolWire 0 1802++L.skywalkSafeX := (wireBlock_append _ 0 1802 256).symm
  have pmem (q : Wire) (hq : q∈wireBlock L.core.poolWire 0 1802) :
      q∈wireBlock L.core.poolWire 0 2058 := by
    rw [split]
    exact List.mem_append_left _ hq
  have dmem (q : Wire) (hq : q∈L.skywalkSafeX) : q∈wireBlock L.core.poolWire 0 2058 := by
    rw [split]
    exact List.mem_append_right _ hq
  intro q hq
  unfold pointSkywalkArithmetic at hq
  have hh := hwrap hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc]
  rcases Finset.mem_union.mp hh with hs|ha
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hs
    rcases hs with hc|hx|hd
    · exact Or.inl hc
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inr (dmem q hd)))
  · have ha' := List.mem_toFinset.mp (hk ha)
    change q∈skywalkSharedWires (skywalkPointWire L.core.poolWire L.skywalkSafeX L.point.y) at ha'
    rcases (skywalkPointWire_mem _ _ _ L.skywalkSafeX_length hw.inputY q).mp ha' with hp|hd|hy
    · exact Or.inr (Or.inr (Or.inr (pmem q hp)))
    · exact Or.inr (Or.inr (Or.inr (dmem q hd)))
    · exact Or.inr (Or.inr (Or.inl hy))

end ECDSAAdd.Arithmetic
