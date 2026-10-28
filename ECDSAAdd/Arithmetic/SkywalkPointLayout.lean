import ECDSAAdd.Arithmetic.PointDialogLayout
import ECDSAAdd.Arithmetic.SkywalkPointPool

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

/-- A clean temporary divisor makes the inactive branch use one without
changing the caller's X word. Its 256 sites follow the shared workspace. -/
def skywalkSafeX (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 1802 256

def skywalkSharedMap (L : ControlledPointLayout) : Nat → Wire :=
  skywalkPointWire L.core.poolWire L.skywalkSafeX L.point.y

theorem skywalkSafeX_length (L : ControlledPointLayout) : L.skywalkSafeX.length=256 := by
  simp [skywalkSafeX,wireBlock]

/-- All arithmetic scratch fits inside 2,058 already allocated caller sites. -/
theorem skywalkCaller_nodup (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    (L.core.generic::L.point.x++wireBlock L.core.poolWire 0 2058++L.point.y).Nodup := by
  rw [L.core.pool_prefix hw 2058 (by omega)]
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp : (L.core.pool.take 2058).count q≤L.dialogPool.count q := by
    have ht := (List.take_sublist 2058 L.dialogPool).count_le q
    simpa only [dialogPool,List.take_take,Nat.min_eq_left (show 2058≤2613 by omega)] using ht
  simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
    List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

theorem skywalkSharedMap_nodup (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : (skywalkSharedWires L.skywalkSharedMap).Nodup := by
  apply skywalkPointWire_nodup L.core.poolWire L.skywalkSafeX L.point.y
    L.skywalkSafeX_length hw.inputY
  have h := (List.nodup_cons.mp (L.skywalkCaller_nodup hw hn)).2
  have hsub : (wireBlock L.core.poolWire 0 2058++L.point.y).Sublist
      (L.point.x++wireBlock L.core.poolWire 0 2058++L.point.y) := by
    exact (List.sublist_append_right _ _).append (List.Sublist.refl _)
  have hh := hsub.nodup h
  have hp : wireBlock L.core.poolWire 0 1802++L.skywalkSafeX=
      wireBlock L.core.poolWire 0 2058 :=
    wireBlock_append L.core.poolWire 0 1802 256
  rw [hp]
  exact hh

theorem skywalkSharedMap_control (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : L.core.generic∉skywalkSharedWires L.skywalkSharedMap := by
  apply skywalkPointWire_control_outside L.core.poolWire L.skywalkSafeX L.point.y
    L.skywalkSafeX_length hw.inputY L.core.generic
  have h := L.skywalkCaller_nodup hw hn
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp h q
  have hp : wireBlock L.core.poolWire 0 1802++L.skywalkSafeX=
      wireBlock L.core.poolWire 0 2058 :=
    wireBlock_append L.core.poolWire 0 1802 256
  simp only [List.count_cons,List.count_append] at hh ⊢
  have hc := congrArg (List.count q) hp
  simp only [List.count_append] at hc
  omega

theorem skywalkCaller_zero (L : ControlledPointLayout) (hw : L.Widths) (s : BasisState)
    (hc : regValue L.dialogPool s=0) : regValue (wireBlock L.core.poolWire 0 2058) s=0 := by
  rw [L.core.pool_prefix hw 2058 (by omega)]
  apply (regValue_zero _ _).mpr
  intro q hq
  have ht : L.core.pool.take 2058=L.dialogPool.take 2058 := by
    simp only [dialogPool,List.take_take,Nat.min_eq_left (show 2058≤2613 by omega)]
  rw [ht] at hq
  exact (regValue_zero _ _).mp hc q (List.take_subset _ _ hq)

end ECDSAAdd.Arithmetic.ControlledPointLayout
