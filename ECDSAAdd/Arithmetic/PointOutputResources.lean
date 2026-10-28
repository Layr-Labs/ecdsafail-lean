import ECDSAAdd.Arithmetic.PointOutput

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem maskedPointConstant_counts (c : Wire) (r : PointReg) (C : Point) :
    toffoliCount (maskedPointConstant c r C)=0 ∧ measurementCount (maskedPointConstant c r C)=0 := by
  simp [maskedPointConstant,toffoliCount_append,measurementCount_append,maskedConstant_counts]

theorem negativePointConstant_counts (c : Wire) (r : PointReg) (C : Point) :
    toffoliCount (negativePointConstant c r C)=0 ∧ measurementCount (negativePointConstant c r C)=0 := by
  simp [negativePointConstant,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    maskedPointConstant_counts]

theorem pointGenericOutput_counts (L : PointAddLayout) (h : L.Widths) :
    toffoliCount (pointGenericOutput L)=512 ∧ measurementCount (pointGenericOutput L)=0 := by
  have hx := h.words L.candidateX (by simp [PointAddLayout.words])
  have hy := h.words L.candidateY (by simp [PointAddLayout.words])
  have cX := copyRegister_counts (some L.generic) (L.candidateX.take 256) L.output.x (by simp [hx,h.outputX])
  have cY := copyRegister_counts (some L.generic) (L.candidateY.take 256) L.output.y (by simp [hy,h.outputY])
  simp [pointGenericOutput,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    cX.1,cX.2,cY.1,cY.2,hx,hy]

theorem pointOutput_counts (L : PointAddLayout) (h : L.Widths) (C : Point) :
    toffoliCount (pointOutput L C)=512 ∧ measurementCount (pointOutput L C)=0 := by
  simp [pointOutput,toffoliCount_append,measurementCount_append,pointGenericOutput_counts L h,
    maskedPointConstant_counts,negativePointConstant_counts]

theorem pointCopy_counts (a b : PointReg) (hx : a.x.length=b.x.length) (hy : a.y.length=b.y.length) :
    toffoliCount (pointCopy a b)=0 ∧ measurementCount (pointCopy a b)=0 := by
  simp [pointCopy,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    copyRegister_counts _ _ _ hx,copyRegister_counts _ _ _ hy]

theorem maskedPointConstant_support (c : Wire) (r : PointReg) (C : Point) :
    wires (maskedPointConstant c r C) ⊆ (c::PointAddLayout.pointWires r).toFinset := by
  simp only [maskedPointConstant,wires_append,Finset.union_subset_iff]
  have hh (a : List Wire) (k : Nat) (ha : a⊆PointAddLayout.pointWires r) :
      wires (maskedConstant c a k) ⊆ (c::PointAddLayout.pointWires r).toFinset := by
    intro w hw
    have hm := maskedConstant_wires_subset c a k hw
    simp only [List.mem_toFinset,List.mem_cons] at hm ⊢
    exact hm.imp_right (fun hw => ha hw)
  exact ⟨⟨hh _ _ (by simp [PointAddLayout.pointWires]),hh _ _ (by simp [PointAddLayout.pointWires])⟩,
    hh _ _ (by simp [PointAddLayout.pointWires])⟩

theorem negativePointConstant_support (c : Wire) (r : PointReg) (C : Point) :
    wires (negativePointConstant c r C) ⊆ (c::PointAddLayout.pointWires r).toFinset := by
  simp only [negativePointConstant,wires_append,Finset.union_subset_iff]
  exact ⟨⟨by simp [wires,Instr.wires],maskedPointConstant_support c r C⟩,by simp [wires,Instr.wires]⟩

theorem pointGenericOutput_support (L : PointAddLayout) (h : L.Widths) :
    wires (pointGenericOutput L)=
      (L.generic::L.candidateX.take 256++L.candidateY.take 256++PointAddLayout.pointWires L.output).toFinset := by
  have hx := h.words L.candidateX (by simp [PointAddLayout.words])
  have hy := h.words L.candidateY (by simp [PointAddLayout.words])
  have hnX : (L.candidateX.take 256).isEmpty=false := by cases he : L.candidateX <;> simp_all
  have hnY : (L.candidateY.take 256).isEmpty=false := by cases he : L.candidateY <;> simp_all
  rw [pointGenericOutput,wires_append,wires_append,
    copyRegister_wires _ _ _ (by simp [hx,h.outputX]),copyRegister_wires _ _ _ (by simp [hy,h.outputY])]
  ext w
  simp only [hnX,hnY,Bool.false_eq_true,if_false,wires,Instr.wires,Finset.union_empty,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Option.toList_some,
    List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,PointAddLayout.pointWires]
  tauto

theorem pointCopy_support (a b : PointReg) (hx : a.x.length=256) (hy : a.y.length=256)
    (hx' : b.x.length=256) (hy' : b.y.length=256) :
    wires (pointCopy a b)=(PointAddLayout.pointWires a++PointAddLayout.pointWires b).toFinset := by
  have hnX : a.x.isEmpty=false := by cases he : a.x <;> simp_all
  have hnY : a.y.isEmpty=false := by cases he : a.y <;> simp_all
  rw [pointCopy,wires_append,wires_append,copyRegister_wires _ _ _ (hx.trans hx'.symm),
    copyRegister_wires _ _ _ (hy.trans hy'.symm)]
  ext w
  simp only [hnX,hnY,Bool.false_eq_true,if_false,wires,Instr.wires,Finset.union_empty,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Option.toList_none,
    List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,PointAddLayout.pointWires]
  tauto

end ECDSAAdd.Arithmetic
