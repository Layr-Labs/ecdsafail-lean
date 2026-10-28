import ECDSAAdd.Arithmetic.ControlledPointAddSpec

namespace ECDSAAdd.Arithmetic
open Secp256k1

def ControlledPointLayout.usedWires (L : ControlledPointLayout) := L.core.usedWires++L.extras

theorem ControlledPointLayout.used_subset (L : ControlledPointLayout) (h : L.Widths) :
    L.core.usedWires.toFinset⊆L.core.wires.toFinset := by
  intro w hw
  simp only [PointAddLayout.usedWires,List.toFinset_append,Finset.mem_union] at hw
  rcases hw with hw|hw
  · exact L.candidate_subset h hw
  · simpa only [List.mem_toFinset] using (show w∈L.core.wires from by
      simp only [PointAddLayout.boundaryWires,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (rfl|rfl|rfl|rfl)|hw
      all_goals simp_all [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.flags] <;> tauto)

theorem ControlledPointLayout.used_nodup (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup) :
    L.usedWires.Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨L.core.usedWires_nodup h (L.core_nodup hn),(List.nodup_append'.mp hn).2.1,?_⟩
  exact List.disjoint_left.mpr (fun w hw he => L.extra_not_core hn w he
    (List.mem_toFinset.mp (L.used_subset h (List.mem_toFinset.mpr hw))))

theorem controlledPointAddOut_support (L : ControlledPointLayout) (h : L.Widths) (cx cy : Fp)
    (hc : curve.toAffine.Nonsingular cx cy) :
    wires (controlledPointAddOut L (.some hc))=L.usedWires.toFinset := by
  have hflags : (L.core.input.finite::L.core.input.x++L.core.input.y++L.core.flags++L.core.pool.take 256).toFinset ⊆
      L.usedWires.toFinset := by
    intro w hw
    have hp : w∈L.core.pool.take 256 → w∈candidatePool L.core.poolWire := L.core.pool_prefix_used h 256 (by omega) w
    simp only [ControlledPointLayout.usedWires,PointAddLayout.usedWires,PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
      PointAddLayout.extendedX,PointAddLayout.extendedY,PointAddLayout.flags,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with (((hw|hw)|hw)|(hw|hw|hw|hw))|hw
    all_goals simp_all only [true_or,or_true]
  have hgeneric : (L.genericSelect::L.core.candidateX.take 256++L.core.candidateY.take 256++PointAddLayout.pointWires L.core.output).toFinset ⊆
      L.usedWires.toFinset := by
    intro w hw
    have hx : w∈L.core.candidateX.take 256 → w∈L.core.candidateX := List.mem_of_mem_take
    simp only [ControlledPointLayout.usedWires,ControlledPointLayout.extras,ControlledPointLayout.selectors,
      PointAddLayout.usedWires,PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with ((hw|hw)|hw)|hw
    all_goals simp_all only [true_or,or_true]
  have hconstant (q : Wire) (hq : q∈L.extras) :
      (q::PointAddLayout.pointWires L.core.output).toFinset ⊆ L.usedWires.toFinset := by
    intro w hw
    simp only [ControlledPointLayout.usedWires,PointAddLayout.usedWires,PointAddLayout.boundaryWires,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with rfl|hw
    · exact Or.inr hq
    · tauto
  have hsel : [L.control,L.core.generic,L.core.double,L.core.input.finite,L.genericSelect,L.doubleSelect,L.infinitySelect].toFinset⊆L.usedWires.toFinset := by
    intro w hw
    simp only [ControlledPointLayout.usedWires,ControlledPointLayout.extras,ControlledPointLayout.selectors,
      PointAddLayout.usedWires,PointAddLayout.candidateUsed,PointAddLayout.boundaryWires,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [true_or,or_true]
  have hcandidate : L.core.candidateUsed.toFinset⊆L.usedWires.toFinset := by
    simp [ControlledPointLayout.usedWires,PointAddLayout.usedWires]
  have cC := (pointCandidate_support L.core h cx cy).1
  have cU := (pointCandidate_support L.core h cx cy).2
  have fC := (pointFlags_support L.core h cx cy).1
  have fU := (pointFlags_support L.core h cx cy).2
  have oG := pointGenericOutput_support L.selected (L.selected_widths h)
  have oD := (maskedPointConstant_support L.doubleSelect L.core.output ((.some hc : Point)+.some hc)).trans
    (hconstant L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]))
  have oO := (maskedPointConstant_support L.infinitySelect L.core.output (.some hc)).trans
    (hconstant L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]))
  rw [controlledPointAddOut,wires_append,wires_append,wires_append,wires_append,cC,cU,fC,fU,
    controlledPointOutput,wires_append,wires_append,selectedPointOutput,wires_append,wires_append,oG,pointSelectors_wires]
  change _ = L.usedWires.toFinset
  apply Finset.Subset.antisymm
  · simp only [Finset.union_subset_iff]
    exact ⟨⟨⟨⟨hflags,hcandidate⟩,⟨⟨hsel,⟨⟨hgeneric,oD⟩,oO⟩⟩,hsel⟩⟩,hcandidate⟩,hflags⟩
  · intro w hw
    simp only [ControlledPointLayout.usedWires,PointAddLayout.usedWires,List.mem_toFinset,List.mem_append] at hw
    simp only [ControlledPointLayout.selected,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
      PointAddLayout.flags,List.not_mem_nil,or_false]
    clear cC cU fC fU oG oD oO
    rcases hw with (hw|hw)|hw
    · simp only [hw,true_or,or_true]
    · simp only [PointAddLayout.boundaryWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (hw|hw|hw|hw)|hw
      all_goals simp_all only [true_or,or_true]
    · simp only [ControlledPointLayout.extras,ControlledPointLayout.selectors,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with hw|hw|hw|hw
      all_goals simp_all only [true_or,or_true]

end ECDSAAdd.Arithmetic
