import ECDSAAdd.Arithmetic.PointDialogLayout
import ECDSAAdd.Arithmetic.CompactRecoveryConstant
import ECDSAAdd.Arithmetic.CompactRecoveryNegateProof

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

def recoveryConstant (L : ControlledPointLayout) (r : List Wire) : MeasuredCanonicalModLayout :=
  {src:=L.dialogPool.take 256,out:=r,carry:=(L.dialogPool.drop 256).take 256,
    high:=L.core.poolWire 512,cin:=L.core.poolWire 513,flag:=L.core.poolWire 514}

def recoveryNegate (L : ControlledPointLayout) : CompactRecoveryNegateLayout :=
  {word:=L.point.x,work:=L.dialogPool.take 256,cin:=L.core.poolWire 256,zero:=L.core.poolWire 257}

def recoveryStageSites (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags++L.dialogPool.take 515

theorem recoveryConstant_widths (L : ControlledPointLayout) (hw : L.Widths) (r : List Wire)
    (hr : r.length=256) : (L.recoveryConstant r).Widths 256 := by
  constructor <;> simp [recoveryConstant,L.dialogPool_length hw,hr]

theorem recoveryConstant_pool (L : ControlledPointLayout) (hw : L.Widths) (r : List Wire) :
    (L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]=L.dialogPool.take 515 := by
  simp only [recoveryConstant]
  rw [←List.take_add]
  norm_num
  calc
    L.dialogPool.take 512++[L.core.poolWire 512,L.core.poolWire 513,L.core.poolWire 514]=
      (L.dialogPool.take 512++[L.core.poolWire 512])++[L.core.poolWire 513,L.core.poolWire 514] := by simp
    _=(L.dialogPool.take 513++[L.core.poolWire 513])++[L.core.poolWire 514] := by
      rw [L.dialogBit_prefix hw 512 (by omega)]
      simp [List.append_assoc]
    _=L.dialogPool.take 514++[L.core.poolWire 514] := by rw [L.dialogBit_prefix hw 513 (by omega)]
    _=L.dialogPool.take 515 := L.dialogBit_prefix hw 514 (by omega)

theorem recoveryConstant_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have pool := (List.take_sublist 515 L.dialogPool).count_le q
  rw [←L.recoveryConstant_pool hw r] at pool
  rcases hr with rfl|rfl
  all_goals
    simp only [recoveryConstant,MeasuredCanonicalModLayout.wires,dialogUsedWires,inPlaceFlags,
      PointAddLayout.pointWires,List.count_cons,List.count_append,List.count_nil] at h pool ⊢
    omega

theorem recoveryNegate_pool (L : ControlledPointLayout) (hw : L.Widths) :
    L.recoveryNegate.work++[L.recoveryNegate.cin,L.recoveryNegate.zero]=L.dialogPool.take 258 := by
  simp only [recoveryNegate]
  calc
    L.dialogPool.take 256++[L.core.poolWire 256,L.core.poolWire 257]=
      (L.dialogPool.take 256++[L.core.poolWire 256])++[L.core.poolWire 257] := by simp
    _=L.dialogPool.take 257++[L.core.poolWire 257] := by rw [L.dialogBit_prefix hw 256 (by omega)]
    _=L.dialogPool.take 258 := L.dialogBit_prefix hw 257 (by omega)

theorem recoveryNegate_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.recoveryNegate.wires L.core.generic).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have pool := (List.take_sublist 258 L.dialogPool).count_le q
  rw [←L.recoveryNegate_pool hw] at pool
  simp only [recoveryNegate,CompactRecoveryNegateLayout.wires,dialogUsedWires,inPlaceFlags,
    PointAddLayout.pointWires,List.count_cons,List.count_append,List.count_nil] at h pool ⊢
  omega

theorem recoveryStageSites_certified (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.recoveryStageSites.Nodup ∧ L.recoveryStageSites.length=1036 := by
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have ht := (List.take_sublist 515 L.dialogPool).count_le q
    simp only [recoveryStageSites,dialogUsedWires,List.count_append] at h ⊢
    omega
  · simp [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags,point,hw.inputX,hw.inputY,L.dialogPool_length hw]

end ECDSAAdd.Arithmetic.ControlledPointLayout
