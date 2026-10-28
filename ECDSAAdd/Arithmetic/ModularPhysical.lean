import ECDSAAdd.Arithmetic.ComparePhysical
import ECDSAAdd.Arithmetic.ModInPlaceSubtract

namespace ECDSAAdd.Arithmetic

theorem modAddCore_physical (L : ModAddCoreLayout) (p : Nat) (hn : L.wires.Nodup) :
    GatePhysical (modAddCore L p) := by
  have hcount := List.nodup_iff_count.mp hn
  have nda : (L.cin :: L.a ++ L.z ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcount q
    simp only [ModAddCoreLayout.wires,ModAddCoreLayout.work,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ndc : (L.cin :: L.constant ++ L.z ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcount q
    simp only [ModAddCoreLayout.wires,ModAddCoreLayout.work,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ndm : (L.cin :: L.constant.take L.low.length ++ L.low ++ L.carry.take (L.low.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcount q
    have ht := (List.take_sublist L.low.length L.constant).count_le q
    have hk := (List.take_sublist (L.low.length-1) L.carry).count_le q
    simp only [ModAddCoreLayout.wires,ModAddCoreLayout.work,ModAddCoreLayout.z,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have hc : L.high ∉ L.constant.take L.low.length := by
    intro hh
    have hm := List.count_pos_iff.mpr (List.mem_of_mem_take hh)
    have h := hcount L.high
    simp only [ModAddCoreLayout.wires,ModAddCoreLayout.work,ModAddCoreLayout.z,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have ndcmp : (L.high :: L.cin :: L.low ++ L.a.take L.low.length ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcount q
    have ht := (List.take_sublist L.low.length L.a).count_le q
    simp only [ModAddCoreLayout.wires,ModAddCoreLayout.work,ModAddCoreLayout.z,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  simp only [modAddCore,gatePhysical_append]
  refine ⟨⟨⟨⟨⟨⟨addInPlace_physical _ _ _ _ nda,xorConstant_physical _ _⟩,
    subInPlace_physical _ _ _ _ ndc⟩,xorConstant_physical _ _⟩,
    maskedAddConst_physical _ _ _ _ _ _ ndm hc⟩,
    compareLt_physical _ _ _ _ _ _ ndcmp (by simp)⟩,?_⟩
  simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]

theorem negRaw_physical (L : ModInPlaceLayout) (p : Nat) (hn : L.wires.Nodup) :
    GatePhysical (negRaw L p) := by
  have nd : (L.cin :: L.constant ++ L.a ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [negRaw,gatePhysical_append]
  exact ⟨⟨⟨notRegister_physical _,xorConstant_physical _ _⟩,
    addInPlace_physical _ _ _ _ nd⟩,xorConstant_physical _ _⟩

theorem controlledModAdd_physical (c : Wire) (L : ModInPlaceLayout) (p : Nat)
    (hn : (c :: L.wires).Nodup) : GatePhysical (controlledModAdd c L p) := by
  have hcount := List.nodup_iff_count.mp hn
  have ndcopy : (L.a.take L.low.length ++ L.mask.take L.low.length).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcount q
    have ha := (List.take_sublist L.low.length L.a).count_le q
    have hm := (List.take_sublist L.low.length L.mask).count_le q
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,List.count_cons,List.count_append] at h ⊢
    omega
  have cm : c ∉ L.mask.take L.low.length := by
    intro hh
    have hm := List.count_pos_iff.mpr (List.mem_of_mem_take hh)
    have h := hcount c
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,List.count_cons,List.count_append,
      beq_self_eq_true,if_true] at h
    omega
  have ndcore : L.maskedCore.wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcount q
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.z,
      ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.z,ModAddCoreLayout.work,List.count_cons,List.count_append] at h ⊢
    omega
  have cp := copyRegister_physical (some c) _ _ ndcopy (by intro q hq; cases hq; exact cm)
  simp only [controlledModAdd,gatePhysical_append]
  exact ⟨⟨cp,modAddCore_physical _ _ ndcore⟩,cp⟩

theorem controlledModSub_physical (c : Wire) (L : ModInPlaceLayout) (p : Nat)
    (hn : (c :: L.wires).Nodup) : GatePhysical (controlledModSub c L p) := by
  simp only [controlledModSub,gatePhysical_append]
  exact ⟨⟨negRaw_physical _ _ hn.tail,controlledModAdd_physical _ _ _ hn⟩,
    negRaw_physical _ _ hn.tail⟩

end ECDSAAdd.Arithmetic
