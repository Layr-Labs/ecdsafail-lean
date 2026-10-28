import ECDSAAdd.Arithmetic.ValueWalkPointProgram
import ECDSAAdd.Arithmetic.DialogPhysical
import ECDSAAdd.Arithmetic.PointFixedPhysical
import ECDSAAdd.Arithmetic.SquareSubPhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum ControlledPointLayout Secp256k1

theorem valueWalkConstant_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    GatePhysical (valueWalkPointDialogConstantAdd L r k) := by
  have nd := L.dialogUnary_nodup hw hn r hr
  have away : L.core.generic ∉ (L.dialogUnary r).a := by
    intro hm
    apply (List.nodup_cons.mp nd).1
    simp [ModInPlaceLayout.wires,hm]
  have cp := maskedConstant_physical L.core.generic _ k.val away
  have ad := (modInPlace_physical (L.dialogUnary r) p nd.tail).1
  simpa only [valueWalkPointDialogConstantAdd,gatePhysical_append] using And.intro (And.intro cp ad) cp

theorem valueWalkSquare_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (valueWalkPointDialogSquare L) := by
  have nd : (L.point.y++L.dialogPool.take 256).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) w
    have ht := (List.take_sublist 256 L.dialogPool).count_le w
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons] at h ⊢
    omega
  have away : L.core.generic ∉ L.dialogPool.take 256 := by
    intro hm
    have ht := List.count_pos_iff.mpr (List.mem_of_mem_take hm)
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
    simp only [dialogUsedWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have cp := copyRegister_physical (some L.core.generic) L.point.y (L.dialogPool.take 256) nd (by intro c hc; cases hc; exact away)
  have sq := squareSub_physical L.dialogSquare (L.dialogSquare_widths hw) (L.dialogSquare_nodup hw hn)
  simpa only [valueWalkPointDialogSquare,gatePhysical_append] using And.intro (And.intro cp sq) cp

theorem valueWalkNegate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (valueWalkPointDialogNegate L) := by
  have nd := L.dialogNegate_nodup hw hn
  have he : L.dialogNegate.a=L.point.x++[L.core.poolWire 0] := by simp only [dialogNegate]
  have sw : (L.core.generic::L.point.x++L.dialogNegate.low).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [ModInPlaceLayout.wires,he,ModInPlaceLayout.z,ModAddCoreLayout.z,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [valueWalkPointDialogNegate,gatePhysical_append]
  exact ⟨⟨controlledModSub_physical _ _ _ nd,swapRegisters_physical _ _ _ sw⟩,controlledModAdd_physical _ _ _ nd⟩

theorem valueWalkGeneric_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) : GatePhysical (valueWalkPointDialogGeneric L cx cy) := by
  have ax (k : Fp) := valueWalkConstant_physical L hw hn L.point.x (Or.inl rfl) k
  have ay (k : Fp) := valueWalkConstant_physical L hw hn L.point.y (Or.inr rfl) k
  have di := dialogs_physical L.dialogPort p (DialogLayout.fromPool_widths _ _ _ _) (L.dialogPort_nodup hw hn)
  simp only [valueWalkPointDialogGeneric,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di.1⟩,valueWalkSquare_physical L hw hn⟩,ax _⟩,di.2⟩,valueWalkNegate_physical L hw hn⟩,ax _⟩,ay _⟩

theorem valueWalkFinite_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    GatePhysical (valueWalkPointDialogFinite L C cx cy) := by
  have sep := dialogFlag_separation (L:=L) hn
  have eq1 (k : Nat) := dialogEqual_physical L hw hn L.control L.infinitySelect
    (Or.inl rfl) (by simp [inPlaceFlags])
    (by simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at sep; tauto) k
  have eq2 (k : Nat) := dialogEqual_physical L hw hn L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags])
    (by simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at sep; tauto) k
  have eq3 (k : Nat) := dialogEqual_physical L hw hn L.control L.genericSelect
    (Or.inl rfl) (by simp [inPlaceFlags])
    (by simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at sep; tauto) k
  have eq4 (k : Nat) := dialogEqual_physical L hw hn L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags])
    (by simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at sep; tauto) k
  have fl := pointDialogFlags_physical L hn cy C
  have ge := valueWalkGeneric_physical L hw hn cx cy
  have co := pointDialogCorners_physical L hn C
  simp only [valueWalkPointDialogFinite,gatePhysical_append]
  simp only [eq1,eq2,eq3,eq4,fl.1,fl.2.1,fl.2.2,ge,co,and_self]

end ECDSAAdd.Arithmetic
