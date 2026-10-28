import ECDSAAdd.Arithmetic.PointFlagLayout

namespace ECDSAAdd.Arithmetic

theorem pointBranchFlags_wires (f ex ey g d : Wire) :
    wires (pointBranchFlags f ex ey g d)=[f,ex,ey,g,d].toFinset := by
  ext w; simp [pointBranchFlags,wires,Instr.wires]; tauto

theorem pointFlags_counts (L : PointAddLayout) (h : L.Widths) (cx cy : Fp) :
    (toffoliCount (pointFlagsCompute L cx cy)=514 ∧ measurementCount (pointFlagsCompute L cx cy)=512) ∧
    (toffoliCount (pointFlagsClear L cx cy)=514 ∧ measurementCount (pointFlagsClear L cx cy)=512) := by
  have hx := (zeroPorts_maps L.input.x (L.pool.take 256) (by simp [h.inputX,h.pool])).1
  have hy := (zeroPorts_maps L.input.y (L.pool.take 256) (by simp [h.inputY,h.pool])).1
  have hlx : L.zeroX.length=256 := by simpa [PointAddLayout.zeroX,h.inputX] using congrArg List.length hx
  have hly : L.zeroY.length=256 := by simpa [PointAddLayout.zeroY,h.inputY] using congrArg List.length hy
  simp [pointFlagsCompute,pointFlagsClear,toffoliCount_append,measurementCount_append,
    equalConstant_counts,pointBranchFlags_counts,hlx,hly]

theorem pointFlags_support (L : PointAddLayout) (h : L.Widths) (cx cy : Fp) :
    wires (pointFlagsCompute L cx cy)=
      (L.input.finite::L.input.x++L.input.y++L.flags++L.pool.take 256).toFinset ∧
    wires (pointFlagsClear L cx cy)=
      (L.input.finite::L.input.x++L.input.y++L.flags++L.pool.take 256).toFinset := by
  have hx := zeroPorts_perm L.input.x (L.pool.take 256) (by simp [h.inputX,h.pool])
  have hy := zeroPorts_perm L.input.y (L.pool.take 256) (by simp [h.inputY,h.pool])
  change (L.zeroX.flatMap ZeroBit.wires).Perm (L.input.x++L.pool.take 256) at hx
  change (L.zeroY.flatMap ZeroBit.wires).Perm (L.input.y++L.pool.take 256) at hy
  have heX := equalConstant_wires L.input.finite L.equalX L.zeroX cx.val
  have heY := equalConstant_wires L.input.finite L.equalNegY L.zeroY (-cy).val
  rw [List.toFinset_eq_of_perm _ _ (hx.cons L.equalX |>.cons L.input.finite)] at heX
  rw [List.toFinset_eq_of_perm _ _ (hy.cons L.equalNegY |>.cons L.input.finite)] at heY
  simp only [pointFlagsCompute,pointFlagsClear,wires_append,heX,heY,pointBranchFlags_wires]
  constructor <;> ext w <;>
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,Finset.mem_union,
      PointAddLayout.flags,List.not_mem_nil,or_false] <;> tauto

end ECDSAAdd.Arithmetic
