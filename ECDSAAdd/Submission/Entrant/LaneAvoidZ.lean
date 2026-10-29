import ECDSAAdd.Submission.Entrant.AvoidZ
import ECDSAAdd.Submission.Entrant.HalfLane

/-! The Lane A arithmetic avoids the same logical labels (`2313`, `2401`–`2408`)
as the Skywalk arithmetic: every piece is either an unchanged Skywalk piece or
a Lane A target converter on field sites. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Z
open Arithmetic MappedCompressed MappedCompressed.LaneA CompressedAllocation Secp256k1
attribute [local irreducible] wires NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse
  compressedCompactForward compressedCompactReverse PenultimateMapped.replay laneKernel kernel

theorem targetLayout_good : ∀ q ∈ (balancedSharedTargetConvert base).wires, goodW q := by
  intro q hq
  simp only [balancedSharedTargetConvert,BalancedConvert.Layout.wires,wireBlock,List.mem_append,
    List.mem_cons,List.mem_map,List.mem_range'_1,List.not_mem_nil,or_false,List.cons_append,
    List.nil_append] at hq
  rcases hq with h|h|h|h|h|h
  all_goals first
    | (subst h; apply base_good; unfold badIdx; omega)
    | (obtain ⟨i,hi,rfl⟩ := h; apply base_good; unfold badIdx; omega)

theorem fastTarget_avoid : Avoid centTarget ∧ Avoid canonTarget := by
  have s := BalancedConvert.LaneA.fast_support (balancedSharedTargetConvert base)
  exact ⟨fun q hq => targetLayout_good q (List.mem_toFinset.mp (s.1 hq)),
    fun q hq => targetLayout_good q (List.mem_toFinset.mp (s.2 hq))⟩

theorem laneSegment_avoid (divide : Bool) : Avoid (laneSegment divide) := by
  have old := selectedFieldSegment_avoid divide
  have f := fastTarget_avoid
  cases divide
  · simp only [selectedFieldSegment] at old
    rw [old_split] at old
    simp only [avoid_append] at old
    simp only [laneSegment,Bool.false_eq_true,if_false,mulSeg,avoid_append]
    exact ⟨⟨⟨f.1,old.1⟩,old.2.2.2.1⟩,f.2⟩
  · simp only [selectedFieldSegment] at old
    rw [old_div_split] at old
    simp only [avoid_append] at old
    simp only [laneSegment,if_true,divSeg,avoid_append]
    exact ⟨f.1,⟨old.2.1.1,old.2.2⟩,f.2⟩

/-- The halving-endpoint field segment (`HalfField.segment`, now inside `laneKernel`)
avoids the same labels: its replay is a sub-program of the selected field segment, and its
converters and copy sit on `HalfField.ids`, none of which is a bad label. -/
theorem halfSegment_avoid (divide : Bool) : Avoid (HalfField.segment divide) := by
  have rp : Avoid (PenultimateMapped.replay divide) :=
    avoid_sub (HalfField.replay_sub divide) (selectedFieldSegment_avoid divide)
  have idsGood (P : Program) (h : wires P⊆(HalfField.ids.map base).toFinset) : Avoid P := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (h hq))
    apply base_good
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
      or_false] at hi
    unfold badIdx
    omega
  have ce := idsGood _ HalfField.centerT_sites
  have ca := idsGood _ HalfField.canonT_sites
  have co := idsGood _ HalfField.copyN_sites
  cases divide <;> simp only [HalfField.segment,Bool.false_eq_true,if_false,if_true,avoid_append]
  · exact ⟨ce,co,rp,ca⟩
  · exact ⟨ce,rp,co,ca⟩

theorem laneKernel_avoid (divide : Bool) : Avoid (laneKernel divide) := by
  have k := kernel_avoid divide
  simp only [kernel,avoid_append] at k
  simp only [laneKernel,avoid_append]
  exact ⟨⟨⟨⟨⟨⟨k.1.1.1.1.1.1,k.1.1.1.1.1.2⟩,k.1.1.1.1.2⟩,halfSegment_avoid divide⟩,k.1.1.2⟩,k.1.2⟩,k.2⟩


end ECDSAAdd.Entrant.Z
