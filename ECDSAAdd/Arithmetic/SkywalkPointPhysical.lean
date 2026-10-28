import ECDSAAdd.Arithmetic.MappedKernelPhysical
import ECDSAAdd.Arithmetic.PhysicalSupportRename
import ECDSAAdd.Arithmetic.CompressedPointDialogProgram
import ECDSAAdd.Arithmetic.PointFixedPhysical
namespace ECDSAAdd.Arithmetic
open RecordedQuantum Secp256k1 ControlledPointLayout MappedCompressed
attribute [local irreducible] controlled wires

theorem pointCompressedArithmetic_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) : GatePhysical (pointCompressedArithmetic L multiply) := by
  apply gatePhysical_rename_support (pointWireFn L) (controlled (!multiply))
  · intro a ha b hb eq
    exact pointWireFn_injective_slots L hw hn a (controlled_support (!multiply) ha) b (controlled_support (!multiply) hb) eq
  · exact mappedControlled_physical _

theorem skywalkGeneric_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) : GatePhysical (pointCompressedDialogGeneric L cx cy) := by
  have ax (k : Fp) := pointDialogConstantAdd_physical L hw hn L.point.x (Or.inl rfl) k
  have ay (k : Fp) := pointDialogConstantAdd_physical L hw hn L.point.y (Or.inr rfl) k
  have di := pointCompressedArithmetic_physical L hw hn false
  have mu := pointCompressedArithmetic_physical L hw hn true
  have sq := CompressedPointSquare.computableProgram_physical L hw hn
  have recovery := pointRecoveryStage_physical L hw hn cx cy
  simp only [pointCompressedDialogGeneric,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di⟩,sq⟩,ax _⟩,mu⟩,recovery⟩
theorem skywalkFinite_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    GatePhysical (pointCompressedDialogFinite L C cx cy) := by
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
  have ge := skywalkGeneric_physical L hw hn cx cy
  have co := pointDialogCorners_physical L hn C
  simp only [pointCompressedDialogFinite,gatePhysical_append]
  simp only [eq1,eq2,eq3,eq4,fl.1,fl.2.1,fl.2.2,ge,co,and_self]

end ECDSAAdd.Arithmetic
