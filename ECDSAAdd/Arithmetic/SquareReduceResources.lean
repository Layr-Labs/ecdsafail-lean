import ECDSAAdd.Arithmetic.SquareReduce

namespace ECDSAAdd.Arithmetic

theorem squareNormalize_counts (L : SquareReduceLayout) (hw : L.Widths) :
    (toffoliCount (squareNormalize L)=511 ∧ measurementCount (squareNormalize L)=511) ∧
    (toffoliCount (squareDenormalize L)=511 ∧ measurementCount (squareDenormalize L)=511) := by
  have hv : L.value.length=256 := by simp [SquareReduceLayout.value,hw.r]
  have ha := addInPlace_counts L.mask L.value (L.carry.take 255) L.cin
    (hw.mask.trans hv.symm) (by simp [hw.carry,hv])
  have hs := subInPlace_counts L.mask L.value (L.carry.take 255) L.cin
    (hw.mask.trans hv.symm) (by simp [hw.carry,hv])
  have hc := (compareLt_counts none L.value L.mask (L.carry.take 256) L.cin L.flag
    (hv.trans hw.mask.symm) (by simp [hw.carry,hw.mask])).2.2 SquareReduction.p
  simp [squareNormalize,squareDenormalize,maskedAddConst,maskedSubConst,
    toffoliCount_append,measurementCount_append,hc.1,hc.2,ha.1,ha.2,hs.1,hs.2,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2,
    hw.mask,hv,toffoliCount,measurementCount]

theorem squareReduce_counts (L : SquareReduceLayout) (hw : L.Widths) :
    (toffoliCount (squareReduce L)=4574 ∧ measurementCount (squareReduce L)=4574) ∧
    (toffoliCount (squareReduceClear L)=4574 ∧ measurementCount (squareReduceClear L)=4574) := by
  have hv : L.value.length=256 := by simp [SquareReduceLayout.value,hw.r]
  have hq : L.quotient.length=33 := by simp [SquareReduceLayout.quotient,hw.r]
  have he : L.extended.length=257 := by simp [SquareReduceLayout.extended,hv]
  have hr := hw.r
  have hh := hw.high
  have hpad := hw.pad
  have hcarry := hw.carry
  have hf := squareFold_counts L.high L.r L.pad L.carry L.cin squareFoldShifts
    (by omega) (by intro j hj; simp [squareFoldShifts] at hj; omega)
    (by omega) (by omega)
  have hg := squareFold_counts L.quotient L.extended L.pad L.carry L.cin squareFoldShifts
    (by omega) (by intro j hj; simp [squareFoldShifts] at hj; omega)
    (by omega) (by omega)
  have hp := copyRegister_counts none L.low L.value (hw.low.trans hv.symm)
  have ha := addInPlace_counts L.mask L.value (L.carry.take 255) L.cin
    (hw.mask.trans hv.symm) (by simp [hw.carry,hv])
  have hs := subInPlace_counts L.mask L.value (L.carry.take 255) L.cin
    (hw.mask.trans hv.symm) (by simp [hw.carry,hv])
  have hn := squareNormalize_counts L hw
  simp only [squareReduce,squareReduceClear,toffoliCount_append,measurementCount_append,
    hp.1,hp.2,hf.1.1,hf.1.2,hf.2.1,hf.2.2,hg.1.1,hg.1.2,hg.2.1,hg.2.2,
    hn.1.1,hn.1.2,hn.2.1,hn.2.2,maskedAddConst,maskedSubConst,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2,
    ha.1,ha.2,hs.1,hs.2,hw.r,he,hv]
  norm_num [squareFoldShifts]

/-- 所有约减门均落在该视图内；未声明分配尾部一定被施门。 -/
theorem squareReduce_wires_subset (L : SquareReduceLayout) (hw : L.Widths) :
    wires (squareReduce L)⊆L.wires.toFinset ∧
    wires (squareReduceClear L)⊆L.wires.toFinset := by
  have hv : L.value.length=256 := by simp [SquareReduceLayout.value,hw.r]
  have hq : L.quotient.length=33 := by simp [SquareReduceLayout.quotient,hw.r]
  have he : L.extended.length=257 := by simp [SquareReduceLayout.extended,hv]
  have hr := hw.r
  have hh := hw.high
  have hpad := hw.pad
  have hcarry := hw.carry
  have subv : L.value⊆L.r := List.take_subset _ _
  have subq : L.quotient⊆L.r := List.drop_subset _ _
  have subc (n : Nat) : L.carry.take n⊆L.carry := List.take_subset _ _
  have hf := squareFold_wires_subset L.high L.r L.pad L.carry L.cin squareFoldShifts
    (by omega) (by intro j hj; simp [squareFoldShifts] at hj; omega) (by omega) (by omega)
  have hg := squareFold_wires_subset L.quotient L.extended L.pad L.carry L.cin squareFoldShifts
    (by omega) (by intro j hj; simp [squareFoldShifts] at hj; omega) (by omega) (by omega)
  have embed1 : (L.cin::(L.high++L.r++L.pad++L.carry)).toFinset⊆L.wires.toFinset := by
    intro w h
    simp only [SquareReduceLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil] at h ⊢
    tauto
  have embed2 : (L.cin::(L.quotient++L.extended++L.pad++L.carry)).toFinset⊆L.wires.toFinset := by
    intro w h
    simp only [SquareReduceLayout.extended,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil] at h
    have qmem : w∈L.quotient → w∈L.r := fun h => subq h
    have vmem : w∈L.value → w∈L.r := fun h => subv h
    simp only [SquareReduceLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil]
    tauto
  have masked (c : Wire) (hc : c=L.b ∨ c=L.flag) (K : Nat) :
      wires (maskedAddConst c L.mask L.value (L.carry.take 255) L.cin K)⊆L.wires.toFinset ∧
      wires (maskedSubConst c L.mask L.value (L.carry.take 255) L.cin K)⊆L.wires.toFinset := by
    have h := maskedConst_wires_subset c L.mask L.value (L.carry.take 255) L.cin K
      (hw.mask.trans hv.symm) (by simp [hw.carry,hv])
    have sub : (c::L.cin::(L.mask++L.value++L.carry.take 255)).toFinset⊆L.wires.toFinset := by
      intro w hm
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hm
      have vmem : w∈L.value → w∈L.r := fun h => subv h
      have cmem : w∈L.carry.take 255 → w∈L.carry := fun h => subc _ h
      simp only [SquareReduceLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil]
      rcases hc with rfl|rfl <;> tauto
    exact ⟨h.1.trans sub,h.2.trans sub⟩
  have comp : wires (compareLtConst none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p)⊆L.wires.toFinset := by
    rw [(compareLt_wires none L.value L.mask (L.carry.take 256) L.cin L.flag
      (hv.trans hw.mask.symm) (by simp [hw.carry,hw.mask])).2]
    intro w hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,Option.toList_none,List.not_mem_nil] at hm
    have vmem : w∈L.value → w∈L.r := fun h => subv h
    have cmem : w∈L.carry.take 256 → w∈L.carry := fun h => subc _ h
    simp only [SquareReduceLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil]
    tauto
  have flip : wires [.X L.flag]⊆L.wires.toFinset := by
    simp only [wires,Instr.wires]
    simp [SquareReduceLayout.wires]
  have copy : wires (copyRegister none L.low L.value)⊆L.wires.toFinset := by
    rw [copyRegister_wires none L.low L.value (hw.low.trans hv.symm)]
    split
    · exact Finset.empty_subset _
    · intro w hm
      simp only [List.mem_toFinset,List.mem_append,Option.toList_none,List.not_mem_nil] at hm
      have vmem : w∈L.value → w∈L.r := fun h => subv h
      simp only [SquareReduceLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil]
      tauto
  have norm : wires (squareNormalize L)⊆L.wires.toFinset := by
    simpa only [squareNormalize,wires_append] using
      (Finset.union_subset (Finset.union_subset comp flip) (masked L.flag (Or.inr rfl) _).2)
  have denorm : wires (squareDenormalize L)⊆L.wires.toFinset := by
    simpa only [squareDenormalize,wires_append] using
      (Finset.union_subset (Finset.union_subset (masked L.flag (Or.inr rfl) _).1 flip) comp)
  constructor
  · simpa only [squareReduce,wires_append] using
      (Finset.union_subset (Finset.union_subset (Finset.union_subset (Finset.union_subset copy
        (hf.1.trans embed1)) (hg.1.trans embed2)) (masked L.b (Or.inl rfl) _).1) norm)
  · simpa only [squareReduceClear,wires_append] using
      (Finset.union_subset (Finset.union_subset (Finset.union_subset (Finset.union_subset denorm
        (masked L.b (Or.inl rfl) _).2) (hg.2.trans embed2)) (hf.2.trans embed1)) copy)

end ECDSAAdd.Arithmetic
