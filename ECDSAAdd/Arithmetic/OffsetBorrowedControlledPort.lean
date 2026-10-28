import ECDSAAdd.Arithmetic.CompactOffsetCallerArithmetic
import ECDSAAdd.Arithmetic.DirectSkywalkControlledPort
import ECDSAAdd.Arithmetic.DirectZeroControlled
import ECDSAAdd.Arithmetic.SkywalkDirectPointLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout DirectSkywalk

/-- Actual caller-X repair, mixed transcript arithmetic, and exact repair
uncomputation. The existing integer borrow scratch is reused for comparison. -/
def pointOffsetBorrowedArithmetic (L : ControlledPointLayout) (multiply : Bool) : Program :=
  directZeroControlled L.point.x (directSkywalkCarry L) (directSkywalkCin L)
    L.skywalkDirectZero (compactOffsetCallerArithmetic (!multiply) L.skywalkDirectMap
      L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS)

attribute [local irreducible] run compactOffsetCallerArithmetic pointOffsetBorrowedArithmetic

private theorem offsetPort_regions (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.skywalkDirectZero::directSkywalkCin L::
      (L.point.x++directSkywalkCarry L++L.point.y)).Nodup ∧
    (L.skywalkDirectZero::L.point.x++wireBlock L.core.poolWire 0 1802++L.point.y).Nodup := by
  have h := L.skywalkCaller_nodup hw hn
  have split : wireBlock L.core.poolWire 0 2058=directSkywalkCarry L++
      wireBlock L.core.poolWire 255 1546++[directSkywalkCin L]++
      wireBlock L.core.poolWire 1802 2++[L.skywalkDirectZero]++
      wireBlock L.core.poolWire 1805 253 := by
    rw [←wireBlock_append L.core.poolWire 0 255 1803,
      ←wireBlock_append L.core.poolWire 255 1546 257,
      ←wireBlock_append L.core.poolWire 1801 1 256,
      ←wireBlock_append L.core.poolWire 1802 2 254,
      ←wireBlock_append L.core.poolWire 1804 1 253]
    rfl
  have small : wireBlock L.core.poolWire 0 1802=directSkywalkCarry L++
      wireBlock L.core.poolWire 255 1546++[directSkywalkCin L] := by
    rw [←wireBlock_append L.core.poolWire 0 255 1547,
      ←wireBlock_append L.core.poolWire 255 1546 1]
    rfl
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp h q
    rw [split] at hh
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  ·
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp h q
    rw [split] at hh
    simp only [small,List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega

private theorem offsetPort_subset (pool : Nat → Wire) (a n : Nat) (h : a+n≤2058) :
    wireBlock pool a n⊆wireBlock pool 0 2058 := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hj
  exact arith_mem pool 0 2058 j (by omega) (by omega)

/-- Replacement for the original guarded point arithmetic contract. The
incoming divisor can be zero exactly when the arithmetic branch is inactive.
All valid X,Y, phases, and measurement records are covered. -/
theorem pointOffsetBorrowedArithmetic_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (pointOffsetBorrowedArithmetic L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (pointOffsetBorrowedArithmetic L multiply) m s).basis=V ∧
    ∀ q,q∉L.point.y → (run (pointOffsetBorrowedArithmetic L multiply) m s).basis q=s.basis q := by
  dsimp only
  let D := directDivisor X
  let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
  let kernel := compactOffsetCallerArithmetic (!multiply) L.skywalkDirectMap
    L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS
  have hxlen : L.point.x.length=256 := hw.inputX
  have hp := L.skywalkCaller_zero hw s.basis hc
  have cleanBit (i : Nat) (hi : i<2058) : s.basis (L.core.poolWire i)=false :=
    (regValue_zero _ _).mp hp _ (arith_mem _ 0 2058 i (by omega) hi)
  have regions := offsetPort_regions L hw hn
  have hci : s.basis (directSkywalkCin L)=false := cleanBit 1801 (by omega)
  have hz : s.basis L.skywalkDirectZero=false := cleanBit 1804 (by omega)
  have hcarry : ∀ q∈directSkywalkCarry L,s.basis q=false := by
    intro q hq; exact (regValue_zero _ _).mp hp q (offsetPort_subset _ 0 255 (by omega) hq)
  have hd0 : 0<D := Nat.pos_of_ne_zero (directDivisor_ne_zero X)
  have hdp : D<p := by
    by_cases h : X=0
    · simp only [D,directDivisor,h,if_true]; norm_num [p]
    · simpa [D,directDivisor,h] using hX
  have hYval : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  have result : (directSkywalkResult (!multiply) B D (Y:Fp)).val=V := by
    cases B with
    | false => simpa [V,directSkywalkResult] using hYval
    | true =>
      have h : X≠0 := hX0 rfl
      cases multiply <;> simp [V,D,directDivisor,h,directSkywalkResult,skywalkArithmeticResult]
  have scalar := List.nodup_append'.mp (show
      ([L.core.generic,L.skywalkDirectSelectorG,L.skywalkDirectSelectorS,L.skywalkDirectZero]++
        skywalkSharedWires L.skywalkDirectMap).Nodup from L.skywalkDirectScalar_nodup hw hn)
  have outside (q : Wire) (hq : q∈[L.core.generic,L.skywalkDirectSelectorG,
      L.skywalkDirectSelectorS,L.skywalkDirectZero]) : q∉skywalkSharedWires L.skywalkDirectMap :=
    fun hs => List.disjoint_left.mp scalar.2.2 hq hs
  have awayX (q : Wire) (hq : q∈[L.core.generic,L.skywalkDirectSelectorG,
      L.skywalkDirectSelectorS,L.skywalkDirectZero]) : q∉L.point.x := by
    intro hxq
    apply outside q hq
    have hh := arith_block_subset_shared L.skywalkDirectMap 770 256 (by omega)
    rw [(L.skywalkDirectMap_coordinates hw).1] at hh
    exact hh hxq
  have neZero : L.core.generic≠L.skywalkDirectZero ∧
      L.skywalkDirectSelectorG≠L.skywalkDirectZero ∧
      L.skywalkDirectSelectorS≠L.skywalkDirectZero := by
    have h1 := List.nodup_cons.mp scalar.1
    have h2 := List.nodup_cons.mp h1.2
    have h3 := List.nodup_cons.mp h2.2
    exact ⟨fun he => h1.1 (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton.mpr he))),
      fun he => h2.1 (List.mem_cons_of_mem _ (List.mem_singleton.mpr he)),
      fun he => h3.1 (List.mem_singleton.mpr he)⟩
  have callback : ∀ (t : State) (ms : List Bool),
      regValue L.point.x t.basis=directDivisor (regValue L.point.x s.basis) →
      regValue L.point.y t.basis=regValue L.point.y s.basis →
      t.basis L.skywalkDirectZero=decide (regValue L.point.x s.basis=0) →
      (∀ q,q≠L.skywalkDirectZero → q∉L.point.x → t.basis q=s.basis q) →
      (run kernel ms t).phase=t.phase ∧ regValue L.point.y (run kernel ms t).basis=V ∧
        ∀ q,q∉L.point.y → (run kernel ms t).basis q=t.basis q := by
    intro t ms hdx hdy _ frame
    rw [hx] at hdx
    rw [hy] at hdy
    have poolClean : regValue (wireBlock L.core.poolWire 0 1802) t.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have nod := List.nodup_cons.mp regions.2
      have nz : q≠L.skywalkDirectZero := fun he => nod.1 (by simp [←he,hq])
      have nx : q∉L.point.x := by
        have first := (List.nodup_append'.mp nod.2).1
        have dis := (List.nodup_append'.mp first).2.2
        exact fun hxx => List.disjoint_left.mp dis hxx hq
      exact (frame q nz nx).trans ((regValue_zero _ _).mp hp q (offsetPort_subset _ 0 1802 (by omega) hq))
    have input : SkywalkArithmeticInput L.skywalkDirectMap D (Y:Fp).val t.basis := by
      unfold SkywalkArithmeticInput skywalkArithmeticDivisor skywalkArithmeticNumerator
      rw [(L.skywalkDirectMap_coordinates hw).1,(L.skywalkDirectMap_coordinates hw).2]
      exact ⟨hdx,hdy.trans hYval.symm,
        skywalkPointWire_clean L.core.poolWire L.point.x L.point.y hw.inputX hw.inputY t.basis poolClean⟩
    have gt : t.basis L.skywalkDirectSelectorG=false :=
      (frame _ neZero.2.1 (awayX _ (by simp))).trans (cleanBit 1802 (by omega))
    have st : t.basis L.skywalkDirectSelectorS=false :=
      (frame _ neZero.2.2 (awayX _ (by simp))).trans (cleanBit 1803 (by omega))
    have bt : t.basis L.core.generic=B := (frame _ neZero.1 (awayX _ (by simp))).trans hb
    have strong := compactOffsetCallerArithmetic_run (!multiply) L.skywalkDirectMap
      (L.skywalkDirectMap_nodup hw hn) L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS
      (fun q hq => outside q (List.mem_append_left [L.skywalkDirectZero] hq)) (L.skywalkDirectMixed_layout hw hn)
      D (Y:Fp) hd0 hdp t ms input gt st
    unfold DirectSkywalkArithmeticStrong at strong
    have ys : skywalkArithmeticNumerator L.skywalkDirectMap=L.point.y :=
      (L.skywalkDirectMap_coordinates hw).2
    rw [ys,bt,result] at strong
    exact strong
  have records := directZeroControlled_states L.point.x L.point.y (directSkywalkCarry L)
    (directSkywalkCin L) L.skywalkDirectZero regions.1
    (by change 255+1=L.point.x.length; exact hxlen.symm) kernel s
    (m.take (measurementCount (directZeroDivisorEnter L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero)))
    ((m.drop (measurementCount (directZeroDivisorEnter L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero))).take (measurementCount kernel))
    ((m.drop (measurementCount (directZeroDivisorEnter L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero))).drop (measurementCount kernel))
    V hci hz hcarry callback
  simpa only [pointOffsetBorrowedArithmetic,directZeroControlled,run_append,kernel] using records

theorem pointOffsetBorrowedArithmetic_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    toffoliCount (pointOffsetBorrowedArithmetic L false)=1055219 ∧
    measurementCount (pointOffsetBorrowedArithmetic L false)=726769 ∧
    toffoliCount (pointOffsetBorrowedArithmetic L true)=1055732 ∧
    measurementCount (pointOffsetBorrowedArithmetic L true)=726770 := by
  have outside : ∀ q∈[L.core.generic,L.skywalkDirectSelectorG,L.skywalkDirectSelectorS],
      q∉skywalkSharedWires L.skywalkDirectMap := by
    have hd := List.nodup_append'.mp (show
      ([L.core.generic,L.skywalkDirectSelectorG,L.skywalkDirectSelectorS]++
        (L.skywalkDirectZero::skywalkSharedWires L.skywalkDirectMap)).Nodup from
      L.skywalkDirectScalar_nodup hw hn)
    intro q hq hs
    exact List.disjoint_left.mp hd.2.2 hq (List.mem_cons_of_mem _ hs)
  have h := compactOffsetCallerArithmetic_counts L.skywalkDirectMap (L.skywalkDirectMap_nodup hw hn)
    L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS outside (L.skywalkDirectMixed_layout hw hn)
  have hxlen : L.point.x.length=256 := hw.inputX
  have c (multiply : Bool) := directZeroControlled_counts L.point.x (directSkywalkCarry L)
    (directSkywalkCin L) L.skywalkDirectZero (compactOffsetCallerArithmetic (!multiply) L.skywalkDirectMap
      L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS)
    (by change 255+1=L.point.x.length; exact hxlen.symm)
  have cd := c false
  have cm := c true
  simp only [Bool.not_false] at cd
  simp only [Bool.not_true] at cm
  simp only [pointOffsetBorrowedArithmetic,Bool.not_false,Bool.not_true] at ⊢
  rw [cd.1,cd.2,cm.1,cm.2]
  rw [h.1,h.2.1,h.2.2.1,h.2.2.2,hxlen]
  norm_num

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.pointOffsetBorrowedArithmetic_correct
#print axioms ECDSAAdd.Arithmetic.pointOffsetBorrowedArithmetic_counts
