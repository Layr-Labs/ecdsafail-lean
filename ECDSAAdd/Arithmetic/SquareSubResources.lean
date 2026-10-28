import ECDSAAdd.Arithmetic.SquareSubLayout

namespace ECDSAAdd.Arithmetic

theorem squareSub_counts (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (squareSub L)=275129 ∧ measurementCount (squareSub L)=275129 := by
  have hk := karatsubaSquare_counts L.integer (L.integer_valid hw hn)
  have hr := squareReduce_counts L.reduction (L.reduction_widths hw)
  have ho := modSubInPlace_resources L.output 256 SquareReduction.p (L.output_widths hw)
    (L.output_nodup hn) (by omega)
  simp only [squareSub,toffoliCount_append,measurementCount_append,hk.1.1,hk.1.2,hk.2.1,hk.2.2,
    hr.1.1,hr.1.2,hr.2.1,hr.2.2,ho.1,ho.2.1]
  norm_num

/-- 全部门列均位于输入、目标及2217位工作区内。 -/
theorem squareSub_wires_subset (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (squareSub L)⊆L.wires.toFinset := by
  have ik : L.integer.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hx := congrArg (List.count w) (List.take_append_drop 128 L.x)
    have hp := congrArg (List.count w) (List.take_append_drop 128 L.pad)
    have hr := (List.take_sublist 258 L.r).count_le w
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.integer,
      KaratsubaSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h hx hp ⊢
    omega
  have ir : L.reduction.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hz := congrArg (List.count w) (List.take_append_drop 256 L.z)
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.reduction,
      SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h hz ⊢
    omega
  have io : L.output.toModAddCoreLayout.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hr := (List.take_sublist 256 L.r).count_le w
    have hc := (List.take_sublist 256 L.carry).count_le w
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.output,
      ModAddCoreLayout.wires,ModAddCoreLayout.z,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hk := karatsubaSquare_wires_subset L.integer (L.integer_valid hw hn)
  have hr := squareReduce_wires_subset L.reduction (L.reduction_widths hw)
  have ho : wires (modSubInPlace L.output SquareReduction.p)⊆L.wires.toFinset := by
    rw [modSubInPlace_wires L.output 256 SquareReduction.p (L.output_widths hw) (by omega)]
    exact io
  simp only [squareSub,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨hk.1.trans ik,hr.1.trans ir⟩,ho⟩,hr.2.trans ir⟩,hk.2.trans ik⟩

end ECDSAAdd.Arithmetic
