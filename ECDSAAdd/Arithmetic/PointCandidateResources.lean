import ECDSAAdd.Arithmetic.PointCandidateLayout

namespace ECDSAAdd.Arithmetic

theorem pointSubConstant_counts (L : PointAddLayout) (h : L.Widths)
    (x out : List Wire) (hx : x.length=257) (ho : out.length=257)
    (hnd : (x++L.constant++out++L.pool).Nodup) (k : Nat) :
    toffoliCount (pointSubConstant L x out k)=1284 ∧
    measurementCount (pointSubConstant L x out k)=1028 := by
  have hk := h.words L.constant (by simp [PointAddLayout.words])
  have hc := fieldSub_resources _ (L.poolSub_nodup h x L.constant out hx hk ho hnd)
    (poolSub_width _ _ _ _)
  simp only [pointSubConstant,toffoliCount_append,measurementCount_append,
    (xorConstant_counts _ _).1,(xorConstant_counts _ _).2,hc.1,hc.2.1,
    Nat.zero_add,Nat.add_zero,and_self]

theorem pointSquare_counts (L : PointAddLayout) (h : L.Widths)
    (hnd : (L.slope++L.constant.take 256++L.square++L.pool).Nodup) :
    toffoliCount (pointSquare L)=379424 ∧ measurementCount (pointSquare L)=379424 := by
  have hs := h.words L.slope (by simp [PointAddLayout.words])
  have hk := h.words L.constant (by simp [PointAddLayout.words])
  have ho := h.words L.square (by simp [PointAddLayout.words])
  have hy : (L.constant.take 256).length=256 := by simp [hk]
  have hc := fieldMul_resources _ (L.poolMul_nodup h _ _ _ hnd)
    (poolMul_widths _ _ _ _ hs hy ho)
  have hcopy := copyRegister_counts none L.slope L.constant (hs.trans hk.symm)
  simp only [Option.isSome_none,Bool.false_eq_true,if_false] at hcopy
  simp only [pointSquare,toffoliCount_append,measurementCount_append,hcopy.1,hcopy.2,
    hc.1,hc.2.1,Nat.zero_add,Nat.add_zero,and_self]

/-- 候选计算和按依赖逆序清理调用相同的前向模块，因此门数和测量数相同。 -/
theorem pointCandidate_counts (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (cx cy : Fp) :
    (toffoliCount (pointCandidateCompute L cx cy)=4646783 ∧
      measurementCount (pointCandidateCompute L cx cy)=3062911) ∧
    (toffoliCount (pointCandidateClear L cx cy)=4646783 ∧
      measurementCount (pointCandidateClear L cx cy)=3062911) := by
  obtain ⟨nDx,nDy,nOffset,nX,nDelta,nY,nSlope,nSquare,nProduct,nInverse⟩ :=
    L.candidate_interfaces_nodup hnd
  have hdx := h.words L.dx (by simp [PointAddLayout.words])
  have hdy := h.words L.dy (by simp [PointAddLayout.words])
  have hslope := h.words L.slope (by simp [PointAddLayout.words])
  have hsquare := h.words L.square (by simp [PointAddLayout.words])
  have hoffset := h.words L.offset (by simp [PointAddLayout.words])
  have hx := h.words L.candidateX (by simp [PointAddLayout.words])
  have hdelta := h.words L.delta (by simp [PointAddLayout.words])
  have hproduct := h.words L.product (by simp [PointAddLayout.words])
  have hy := h.words L.candidateY (by simp [PointAddLayout.words])
  obtain ⟨heX,heY⟩ := L.extended_lengths h
  have cDx := pointSubConstant_counts L h _ _ heX hdx nDx cx.val
  have cDy := pointSubConstant_counts L h _ _ heY hdy nDy cy.val
  have cX := pointSubConstant_counts L h _ _ hoffset hx nX cx.val
  have cOffset := fieldSub_resources _
    (L.poolSub_nodup h _ _ _ hsquare heX hoffset nOffset) (poolSub_width _ _ _ _)
  have cDelta := fieldSub_resources _
    (L.poolSub_nodup h _ _ _ heX hx hdelta nDelta) (poolSub_width _ _ _ _)
  have cY := fieldSub_resources _
    (L.poolSub_nodup h _ _ _ hproduct heY hy nY) (poolSub_width _ _ _ _)
  have cSlope := fieldMul_resources _
    (L.poolMul_nodup h _ _ _ nSlope) (poolMul_widths _ _ _ _ hdy h.inverse hslope)

  have cProduct := fieldMul_resources _
    (L.poolMul_nodup h _ _ _ nProduct)
    (poolMul_widths _ _ _ _ hdelta (by simp [hslope]) hproduct)
  have cSquare := pointSquare_counts L h nSquare
  have cInverse := fieldInverse_resources _ (L.poolInverse_nodup h _ _ h.inverse nInverse)
    (poolInverse_widths _ _ _ h.divisor h.inverse)
  have hd : L.divisor.head!::L.divisor.tail=L.divisor :=
    List.cons_head!_tail (by intro he; have hh := h.divisor; rw [he] at hh; simp at hh)
  have cSafe := safeDivisor_counts L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail
    (by rw [hd]; simp [hdx,h.divisor])
  simp only [List.length_take,hdx] at cSafe
  simp only [pointCandidateCompute,pointCandidateClear,toffoliCount_append,measurementCount_append,
    cDx.1,cDx.2,cDy.1,cDy.2,cX.1,cX.2,cOffset.1,cOffset.2.1,cDelta.1,cDelta.2.1,cY.1,cY.2.1,
    cSlope.1,cSlope.2.1,cProduct.1,cProduct.2.1,cSquare.1,cSquare.2,cInverse.1,cInverse.2.1,
    cSafe.1,cSafe.2]
  norm_num

end ECDSAAdd.Arithmetic
