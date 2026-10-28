import ECDSAAdd.Arithmetic.PointDialogSteps

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Stage 6: conditional canonical x reflection followed by the two classical
coordinate corrections. Every scratch bank is cleaned before reuse. -/
def pointRecoveryStage (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointRecoveryReflection L++pointDialogConstantAdd L L.point.x (cx+1)++pointDialogConstantAdd L L.point.y (-cy)

theorem pointRecoveryReflection_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (pointRecoveryReflection L)
      (PointDialogValues L (if G then -1-X else X) Y G base) := by
  intro s m v
  obtain ⟨phase,value,same⟩ := pointRecoveryReflection_correct L hw hn X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨phase,v.withX hn ?_ same⟩
  cases G
  · simpa only [Bool.false_eq_true,if_false] using value
  · have xb : X.val<p := X.isLt
    have hp : 1≤p := by norm_num [p]
    have cast : ((p-1-X.val : Nat) : Fp)=-1-X := by
      rw [Nat.cast_sub (by omega : X.val≤p-1),Nat.cast_sub hp]
      simp only [ZMod.natCast_self,Nat.cast_one,zero_sub,ZMod.natCast_zmod_val]
    have val := congrArg ZMod.val cast
    rw [ZMod.val_natCast_of_lt (by omega : p-1-X.val<p)] at val
    exact (show regValue L.point.x (run (pointRecoveryReflection L) m s).basis=p-1-X.val from value).trans val

theorem pointRecoveryStage_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (pointRecoveryStage L cx cy)
      (PointDialogValues L (if G then cx-X else X) (if G then Y-cy else Y) G base) := by
  have a := pointRecoveryReflection_step L hw hn X Y G base
  have b := dialogStep_addX L hw hn (if G then -1-X else X) Y G base (cx+1)
  have c := dialogStep_addY L hw hn ((if G then -1-X else X)+(if G then cx+1 else 0)) Y G base (-cy)
  have all := (a.seq b).seq c
  have x : (if G then -1-X else X)+(if G then cx+1 else 0)=(if G then cx-X else X) := by
    cases G <;> simp; ring
  have y : Y+(if G then -cy else 0)=(if G then Y-cy else Y) := by cases G <;> simp [sub_eq_add_neg]
  rw [x,y] at all
  exact all

theorem pointRecoveryStage_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (pointRecoveryStage L cx cy)=2301 ∧ measurementCount (pointRecoveryStage L cx cy)=2301 := by
  have neg := pointRecoveryReflection_counts L hw
  have x := pointRecoveryConstantAdd_counts L hw L.point.x (Or.inl rfl) (cx+1)
  have y := pointRecoveryConstantAdd_counts L hw L.point.y (Or.inr rfl) (-cy)
  simp only [pointRecoveryStage,pointDialogConstantAdd,toffoliCount_append,
    measurementCount_append,neg.1,neg.2,x.1,x.2,y.1,y.2]
  decide

theorem pointRecoveryStage_support (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (pointRecoveryStage L cx cy)⊆L.recoveryStageSites.toFinset := by
  have neg := pointRecoveryReflection_support L hw
  have x := pointRecoveryConstantAdd_support L hw L.point.x (cx+1)
  have y := pointRecoveryConstantAdd_support L hw L.point.y (-cy)
  have small : L.dialogPool.take 258⊆L.dialogPool.take 515 := by
    intro q hq
    have eq : (L.dialogPool.take 515).take 258=L.dialogPool.take 258 := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    rw [←eq] at hq
    exact List.mem_of_mem_take hq
  have en : (L.core.generic::L.point.x++L.dialogPool.take 258).toFinset⊆L.recoveryStageSites.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    have ht : q∈L.dialogPool.take 258 → q∈L.dialogPool.take 515 := fun h => small h
    tauto
  have ex : (L.core.generic::L.point.x++L.dialogPool.take 515).toFinset⊆L.recoveryStageSites.toFinset := by
    intro q hq
    simp [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags] at hq ⊢
    tauto
  have ey : (L.core.generic::L.point.y++L.dialogPool.take 515).toFinset⊆L.recoveryStageSites.toFinset := by
    intro q hq
    simp [recoveryStageSites,PointAddLayout.pointWires,inPlaceFlags] at hq ⊢
    tauto
  simpa only [pointRecoveryStage,pointDialogConstantAdd,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (neg.trans en) (x.trans ex)) (y.trans ey)

/-- A certified allocation including residents bounds peak-live qubits;
this is not a measurement of the exact or minimum live peak. -/
theorem pointRecoveryStage_resource_targets (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (pointRecoveryStage L cx cy)=2301 ∧
    measurementCount (pointRecoveryStage L cx cy)=2301 ∧
    qubitCount (pointRecoveryStage L cx cy)≤1036 ∧ L.recoveryStageSites.length=1036 ∧ 1036<1297 ∧ 2301<8000 := by
  have sites := L.recoveryStageSites_certified hw hn
  have counts := pointRecoveryStage_counts L hw cx cy
  refine ⟨counts.1,counts.2,?_,sites.2,by decide,by decide⟩
  rw [qubitCount]
  calc
    _ ≤ L.recoveryStageSites.toFinset.card := Finset.card_le_card (pointRecoveryStage_support L hw cx cy)
    _ = 1036 := by rw [List.toFinset_card_of_nodup sites.1,sites.2]

end ECDSAAdd.Arithmetic
