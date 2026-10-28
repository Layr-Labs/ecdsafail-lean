import ECDSAAdd.Arithmetic.ValueBodyPhysical
import ECDSAAdd.Arithmetic.CounterPhysical
import ECDSAAdd.Arithmetic.ControlledUnaryResources

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem maskedSubConst_physical (c : Wire) (T y carry : List Wire) (cin K : Nat)
    (hn : (cin::T++y++carry).Nodup) (hc : c ∉ T) :
    GatePhysical (maskedSubConst c T y carry cin K) := by
  simp only [maskedSubConst,gatePhysical_append]
  exact ⟨⟨maskedConstant_physical _ _ _ hc,subInPlace_physical _ _ _ _ hn⟩,
    maskedConstant_physical _ _ _ hc⟩

theorem controlledUnary_physical (c : Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hn : (c::U.wires).Nodup) (hpos : 0<n) :
    GatePhysical (controlledHalf c U p) ∧ GatePhysical (controlledDouble c U p) := by
  have ndadd : (U.cin::U.constant++U.z++U.carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have H := List.nodup_iff_count.mp hn w
    have ht := (List.take_sublist U.low.length U.constant).count_le w
    have hk := (List.take_sublist (U.low.length-1) U.carry).count_le w
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil] at H ⊢
    omega
  have ndshift : (c::U.z).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have H := List.nodup_iff_count.mp hn w
    have ht := (List.take_sublist U.low.length U.constant).count_le w
    have hk := (List.take_sublist (U.low.length-1) U.carry).count_le w
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil] at H ⊢
    omega
  have ndcmp : (U.flag::U.cin::U.low++U.constant.take U.low.length++U.carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have H := List.nodup_iff_count.mp hn w
    have ht := (List.take_sublist U.low.length U.constant).count_le w
    have hk := (List.take_sublist (U.low.length-1) U.carry).count_le w
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil] at H ⊢
    omega
  have ndlow : (U.cin::U.constant.take U.low.length++U.low++U.carry.take (U.low.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have H := List.nodup_iff_count.mp hn w
    have ht := (List.take_sublist U.low.length U.constant).count_le w
    have hk := (List.take_sublist (U.low.length-1) U.carry).count_le w
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil] at H ⊢
    omega
  have flagNot : U.flag ∉ U.constant := by
    intro hm
    have hp := List.count_pos_iff.mpr hm
    have H := List.nodup_iff_count.mp hn U.flag
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at H
    omega
  have controlNot : c ∉ U.constant := by
    intro hm
    have hp := List.count_pos_iff.mpr hm
    have H := List.nodup_iff_count.mp hn c
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at H
    omega
  have highNot : U.high ∉ U.constant := by
    intro hm
    have hp := List.count_pos_iff.mpr hm
    have H := List.nodup_iff_count.mp hn U.high
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at H
    omega
  have bits := U.bit_mem n hw hpos
  have cf : c ≠ U.flag := by
    intro he
    have H := List.nodup_iff_count.mp hn U.flag
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,he,beq_self_eq_true,if_true] at H
    omega
  have ch : c ≠ U.high := by
    intro he
    have H := List.nodup_iff_count.mp hn U.high
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,he,beq_self_eq_true,if_true] at H
    omega
  have bf : U.bit ≠ U.flag := by
    intro he
    have H := List.nodup_iff_count.mp hn U.flag
    have hp := List.count_pos_iff.mpr (he ▸ bits)
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at H
    omega
  have bh : U.bit ≠ U.high := by
    intro he
    have H := List.nodup_iff_count.mp hn U.high
    have hp := List.count_pos_iff.mpr (he ▸ bits)
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at H
    omega
  have sh := shifts_physical c U.z ndshift
  have ma := maskedAddConst_physical U.flag U.constant U.z U.carry U.cin p ndadd flagNot
  have ms := maskedSubConst_physical c U.constant U.z U.carry U.cin p ndadd controlNot
  have ml := maskedAddConst_physical U.high (U.constant.take U.low.length) U.low
    (U.carry.take (U.low.length-1)) U.cin p ndlow
    (fun h => highNot (List.mem_of_mem_take h))
  have cmp := compareLtConst_physical (some c) U.low (U.constant.take U.low.length)
    U.carry U.cin U.flag ((p+1)/2) ndcmp (by intro q h; cases h; exact cf)
  simp only [controlledHalf,controlledDouble,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate,cf,bf],ma⟩,sh.1⟩,cmp⟩,
      by simp [GatePhysical,PhysicalInstr,ProperGate,cf]⟩,
    ⟨⟨⟨sh.2,ms⟩,ml⟩,by simp [GatePhysical,PhysicalInstr,ProperGate,ch,bh]⟩⟩

end ECDSAAdd.Arithmetic
