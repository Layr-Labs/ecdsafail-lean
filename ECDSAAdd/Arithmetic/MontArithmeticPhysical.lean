import ECDSAAdd.Arithmetic.ModularPhysical
import ECDSAAdd.Arithmetic.MontStagePorts

namespace ECDSAAdd.Arithmetic

private theorem digit_port (L : MontStageLayout) (x y : List Wire) (j i : Nat)
    (hn : (x++y++L.wires).Nodup) (hy : 4*i+j < y.length) :
    (y.getD (4*i+j) L.flag :: L.cin :: L.source x j ++ L.mask ++ L.acc ++ L.carry).Nodup := by
  have hnd := L.digit_nodup x y hn
  let c := y.getD (4*i+j) L.flag
  have cmem : c ∈ y := mont_bit_mem y _ L.flag hy
  have hsrc (w : Wire) : List.count w (L.source x j) ≤ List.count w x + List.count w L.pad := by
    have hp := congrArg (List.count w) (List.take_append_drop j L.pad)
    have ht := (List.take_sublist 256 x).count_le w
    simp only [MontStageLayout.source,List.count_append] at hp ⊢; omega
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hnd w
  have hs := hsrc w
  have hcm := List.count_pos_iff.mpr cmem
  change List.count w (c :: L.cin :: L.source x j ++ L.mask ++ L.acc ++ L.carry) ≤ 1
  by_cases he : c=w
  · subst w
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h ⊢; omega
  · simp only [List.count_cons,List.count_append] at h ⊢
    have hb : (c==w)=false := by simpa using he
    rw [hb]; simp only [Bool.false_eq_true,if_false]; omega

theorem montDigit_physical (L : MontStageLayout) (x y : List Wire) (i : Nat)
    (hn : (x++y++L.wires).Nodup) (hi : 4*i+4 ≤ y.length) :
    GatePhysical (montAddDigit L x y i) ∧ GatePhysical (montSubDigit L x y i) := by
  have hbit (j : Nat) (hj : j<4) := measuredMasked_physical (y.getD (4*i+j) L.flag)
    L.cin (L.source x j) L.mask L.acc L.carry (digit_port L x y j i hn (by omega))
  constructor
  · intro gate hg
    obtain ⟨j,hj,hg⟩ := List.mem_flatMap.mp hg
    exact (hbit j (List.mem_range.mp hj)).1 gate hg
  · intro gate hg
    obtain ⟨j,hj,hg⟩ := List.mem_flatMap.mp hg
    exact (hbit j (List.mem_range.mp (List.mem_reverse.mp hj))).2 gate hg

theorem montConstant_physical (L : MontStageLayout) (K : Nat) (hn : L.wires.Nodup) :
    GatePhysical (montConstantAdd L K) ∧ GatePhysical (montConstantSub L K) := by
  have nd : (L.cin :: L.table ++ L.acc ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [MontStageLayout.wires,MontStageLayout.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [montConstantAdd,montConstantSub,gatePhysical_append]
  exact ⟨⟨⟨xorConstant_physical _ _,addInPlace_physical _ _ _ _ nd⟩,xorConstant_physical _ _⟩,
    ⟨⟨xorConstant_physical _ _,subInPlace_physical _ _ _ _ nd⟩,xorConstant_physical _ _⟩⟩

theorem montNormalize_physical (L : MontStageLayout) (p : Nat)
    (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (montNormalize L p) ∧ GatePhysical (montDenormalize L p) := by
  have nd : (L.cin :: L.table ++ L.acc ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [MontStageLayout.wires,MontStageLayout.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have flagaway (r : List Wire) (hr : r ⊆ L.acc ++ L.table) : L.flag ∉ r := by
    intro hh
    have h := List.nodup_iff_count.mp hn L.flag
    have hm := List.count_pos_iff.mpr (hr hh)
    simp only [MontStageLayout.wires,MontStageLayout.work,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h hm
    omega
  have ft : L.flag ∉ L.table := flagaway _ (List.subset_append_right _ _)
  have fa : L.flag ∉ L.acc := flagaway _ (List.subset_append_left _ _)
  have bmem := mont_bit_mem L.acc 260 L.flag (by rw [hw.acc]; omega)
  have bf : L.acc.getD 260 L.flag ≠ L.flag := by intro e; exact fa (e ▸ bmem)
  have gate : GatePhysical [.CX (L.acc.getD 260 L.flag) L.flag] := by
    simpa [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate] using bf
  have ma := maskedAddConst_physical L.flag L.table L.acc L.carry L.cin p nd ft
  have ms : GatePhysical (maskedSubConst L.flag L.table L.acc L.carry L.cin p) := by
    simp only [maskedSubConst,gatePhysical_append]
    exact ⟨⟨maskedConstant_physical _ _ _ ft,subInPlace_physical _ _ _ _ nd⟩,
      maskedConstant_physical _ _ _ ft⟩
  simp only [montNormalize,montDenormalize,gatePhysical_append]
  exact ⟨⟨⟨(montConstant_physical L p hn).2,gate⟩,ma⟩,
    ⟨⟨ms,gate⟩,(montConstant_physical L p hn).1⟩⟩

end ECDSAAdd.Arithmetic
