import ECDSAAdd.Arithmetic.PointAddState
import ECDSAAdd.Arithmetic.PointFlagResources
import ECDSAAdd.Arithmetic.PointOutputResources

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 有限常量分支实际触及的线路；dx/dy/delta/yg 的填充最高位不列入。 -/
def PointAddLayout.usedWires (L : PointAddLayout) : List Wire := L.candidateUsed++L.boundaryWires

theorem PointAddLayout.usedWires_nodup (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup) :
    L.usedWires.Nodup := L.candidate_boundary_nodup h hn

theorem PointAddLayout.usedWires_length (L : PointAddLayout) (h : L.Widths) :
    L.usedWires.length=6727 := by
  have hd := h.words L.dx (by simp [PointAddLayout.words])
  have hy := h.words L.candidateY (by simp [PointAddLayout.words])
  have hdy := h.words L.dy (by simp [PointAddLayout.words])
  have hs := h.words L.slope (by simp [PointAddLayout.words])
  have hsq := h.words L.square (by simp [PointAddLayout.words])
  have ho := h.words L.offset (by simp [PointAddLayout.words])
  have hx := h.words L.candidateX (by simp [PointAddLayout.words])
  have hdel := h.words L.delta (by simp [PointAddLayout.words])
  have hp := h.words L.product (by simp [PointAddLayout.words])
  have hk := h.words L.constant (by simp [PointAddLayout.words])
  simp [usedWires,candidateUsed,boundaryWires,extendedX,extendedY,pointWires,hd,hy,hdy,hs,hsq,ho,hx,hdel,hp,hk,
    h.inputX,h.inputY,h.outputX,h.outputY,h.divisor,h.inverse,candidatePool_length]

theorem pointAddOut_support (L : PointAddLayout) (h : L.Widths) (cx cy : Fp)
    (hc : curve.toAffine.Nonsingular cx cy) :
    wires (pointAddOut L (.some hc))=L.usedWires.toFinset := by
  have hflags : (L.input.finite::L.input.x++L.input.y++L.flags++L.pool.take 256).toFinset ⊆
      L.usedWires.toFinset := by
    intro w hw
    have hp : w∈L.pool.take 256 → w∈candidatePool L.poolWire := L.pool_prefix_used h 256 (by omega) w
    simp only [PointAddLayout.usedWires,PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
      PointAddLayout.extendedX,PointAddLayout.extendedY,PointAddLayout.flags,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with (((hw|hw)|hw)|(hw|hw|hw|hw))|hw
    all_goals simp_all only [true_or,or_true]
  have hgeneric : (L.generic::L.candidateX.take 256++L.candidateY.take 256++PointAddLayout.pointWires L.output).toFinset ⊆
      L.usedWires.toFinset := by
    intro w hw
    have hx : w∈L.candidateX.take 256 → w∈L.candidateX := List.mem_of_mem_take
    simp only [PointAddLayout.usedWires,PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with ((hw|hw)|hw)|hw
    all_goals simp_all only [true_or,or_true]
  have hdouble : (L.double::PointAddLayout.pointWires L.output).toFinset ⊆ L.usedWires.toFinset := by
    intro w hw
    simp only [PointAddLayout.usedWires,PointAddLayout.boundaryWires,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have hinf : (L.input.finite::PointAddLayout.pointWires L.output).toFinset ⊆ L.usedWires.toFinset := by
    intro w hw
    simp only [PointAddLayout.usedWires,PointAddLayout.boundaryWires,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have hcandidate : L.candidateUsed.toFinset ⊆ L.usedWires.toFinset := by
    simp [PointAddLayout.usedWires]
  have cC := (pointCandidate_support L h cx cy).1
  have cU := (pointCandidate_support L h cx cy).2
  have fC := (pointFlags_support L h cx cy).1
  have fU := (pointFlags_support L h cx cy).2
  have oG := pointGenericOutput_support L h
  have oD := maskedPointConstant_support L.double L.output ((.some hc : Point)+.some hc)
  have oO := negativePointConstant_support L.input.finite L.output (.some hc)
  rw [pointAddOut,wires_append,wires_append,wires_append,wires_append,cC,cU,fC,fU,
    pointOutput,wires_append,wires_append,oG]
  apply Finset.Subset.antisymm
  · simp only [Finset.union_subset_iff]
    exact ⟨⟨⟨⟨hflags,hcandidate⟩,⟨⟨hgeneric,oD.trans hdouble⟩,oO.trans hinf⟩⟩,hcandidate⟩,hflags⟩
  · intro w hw
    simp only [PointAddLayout.usedWires,List.mem_toFinset,List.mem_append] at hw
    rcases hw with hw|hw
    · simp only [Finset.mem_union,List.mem_toFinset]
      clear cC cU fC fU oG oD oO
      simp only [hw,true_or,or_true]
    · simp only [PointAddLayout.boundaryWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
        PointAddLayout.flags,List.not_mem_nil,or_false]
      clear cC cU fC fU oG oD oO
      rcases hw with (hw|hw|hw|hw)|hw
      all_goals simp_all only [true_or,or_true]

end ECDSAAdd.Arithmetic
