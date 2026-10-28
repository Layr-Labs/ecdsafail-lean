import ECDSAAdd.Arithmetic.EntryFieldSeedCancellation
import ECDSAAdd.Arithmetic.MappedCompressedReplayCounts

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 MappedCompressed CompressedAllocation
attribute [local irreducible] wires logicalCell compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] dblInPlace halfInPlace copyRegister
attribute [local irreducible] toffoliCount measurementCount
private theorem emptyW : wires ([] : Program)=∅ := by simp [wires]
private theorem emptyT : toffoliCount ([] : Program)=0 := by simp [toffoliCount]
private theorem emptyM : measurementCount ([] : Program)=0 := by simp [measurementCount]

/-- Cell zero retains its original recorded S selection and quantum control. -/
def logicalZero : Program :=
  EntryFieldSeedCancellation.selectedSwap id 2400 1028 2409 2410
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2

def firstGroup (divide : Bool) : Program :=
  compressedHistoryDecode (placed 0) 0 ++
  (if divide then renameProgram (placed 0) logicalZero ++
      renameProgram (placed 0) (logicalCell divide 1) ++
      renameProgram (placed 0) (logicalCell divide 2)
   else renameProgram (placed 0) (logicalCell divide 2) ++
      renameProgram (placed 0) (logicalCell divide 1) ++
      renameProgram (placed 0) logicalZero) ++
  compressedHistoryEncode (placed 0) 0

/-- The remaining 169 packets and both raw tail cells are unchanged. -/
def replay (divide : Bool) : Program :=
  if divide then firstGroup divide ++ mappedGroups divide 1 169 ++
      renameProgram allPlaced (logicalCell divide 510) ++
      renameProgram allPlaced (logicalCell divide 511)
  else renameProgram allPlaced (logicalCell divide 511) ++
      renameProgram allPlaced (logicalCell divide 510) ++
      mappedGroups divide 1 169 ++ firstGroup divide

def fieldSegment (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (converterPair false) ++ replay divide ++
  renameProgram allPlaced (converterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

private theorem window_mono (b source flag : Wire) (v : Bool) (P Q : Program)
    (h : wires P ⊆ wires Q) :
    wires (transcriptSelectWindow b source flag v P) ⊆
      wires (transcriptSelectWindow b source flag v Q) := by
  simp only [transcriptSelectWindow,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _))
    (Finset.Subset.refl _)

private theorem body_in_window (b source flag : Wire) (v : Bool) (P : Program) :
    wires P ⊆ wires (transcriptSelectWindow b source flag v P) := by
  intro q hq
  simp only [transcriptSelectWindow,wires_append,Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hq))

private theorem rename_mono (f : Wire → Wire) (P Q : Program)
    (h : wires P ⊆ wires Q) : wires (renameProgram f P) ⊆ wires (renameProgram f Q) := by
  rw [renameProgram_support,renameProgram_support]
  exact Finset.image_mono _ h

theorem logicalZero_support_sub (divide : Bool) : wires logicalZero ⊆ wires (logicalCell divide 0) := by
  let sw := swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y
  have leaf : wires sw ⊆ wires (if divide then OffsetBorrowedCanonical.body id 2409 2410
      else OffsetBorrowedInverseCanonical.body id 2409 2410) := by
    cases divide
    · simp only [Bool.false_eq_true,if_false,OffsetBorrowedInverseCanonical.body,wires_append]
      exact Finset.subset_union_left
    · simp only [if_true,OffsetBorrowedCanonical.body,wires_append]
      exact Finset.subset_union_right
  cases divide <;>
    simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,logicalCell,
      Bool.false_eq_true,if_false,if_true,OffsetBorrowedCanonical.cell,
      OffsetBorrowedInverseCanonical.cell] at ⊢
  all_goals exact (window_mono _ _ _ _ _ _ leaf).trans (body_in_window _ _ _ _ _)

theorem firstGroup_support_sub (divide : Bool) :
    wires (firstGroup divide) ⊆ wires (mappedGroup divide 0) := by
  have sub := rename_mono (placed 0) _ _ (logicalZero_support_sub divide)
  cases divide <;> simp only [firstGroup,mappedGroup,Bool.false_eq_true,if_false,if_true,
    Nat.mul_zero,Nat.zero_add,wires_append,Finset.union_assoc]
  · exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union (Finset.Subset.refl _)
          (Finset.union_subset_union sub (Finset.Subset.refl _))))
  · exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union sub (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union (Finset.Subset.refl _) (Finset.Subset.refl _))))

theorem replay_support_sub (divide : Bool) : wires (replay divide) ⊆ wires (mappedReplay divide) := by
  have sub := firstGroup_support_sub divide
  have unfoldGroups : mappedGroups divide 0 170 =
      if divide then mappedGroup divide 0 ++ mappedGroups divide 1 169
      else mappedGroups divide 1 169 ++ mappedGroup divide 0 := by rfl
  cases divide <;> simp only [replay,mappedReplay,unfoldGroups,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_assoc]
  · exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union (Finset.Subset.refl _) sub))
  · exact Finset.union_subset_union sub (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _) (Finset.Subset.refl _)))

theorem fieldSegment_support (divide : Bool) :
    wires (fieldSegment divide) ⊆ slots.toFinset := by
  have rp := (replay_support_sub divide).trans (mappedReplay_support divide)
  have a := converters_support false
  have b := converters_support true
  cases divide <;> simp only [fieldSegment,Bool.false_eq_true,if_false,if_true,
    wires_append,emptyW,Finset.empty_union,Finset.union_empty,Finset.union_subset_iff,and_assoc]
  · exact ⟨copy_support,a,rp,b⟩
  · exact ⟨a,rp,b,copy_support⟩

private theorem swap_nd :
    (2410::(balancedSharedPorts id 2409).r++(balancedSharedPorts id 2409).y).Nodup := by
  rw [balancedSharedPorts_r,balancedSharedPorts_y]
  simp only [wireBlock,List.map_id]
  apply List.nodup_cons.mpr
  constructor
  · intro h
    rcases List.mem_append.mp h with h|h
    all_goals have bound := List.mem_range'_1.mp h; omega
  · apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hr hy
    simp only [List.mem_range'_1] at hr hy
    omega

theorem logicalZero_counts : toffoliCount logicalZero=257 ∧ measurementCount logicalZero=1 := by
  have width := BalancedCleanup.widths (balancedSharedPorts id 2409).toLayout (balancedSharedPorts_widths id 2409)
  have sw := swapRegisters_resources 2410 _ _ (width.2.1.trans width.2.2.1.symm) swap_nd
  have sel := transcriptSelectWindow_counts 2400 1028 2410
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)
  simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,sel.1,sel.2,sw.1,sw.2.1,width.2.1]
  norm_num

private theorem renameT (f : Wire → Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem renameM (f : Wire → Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem firstGroup_counts (divide : Bool) :
    toffoliCount (firstGroup divide)=(if divide then 2824 else 2826) ∧ measurementCount (firstGroup divide)=2052 := by
  have codec := compressedHistory_counts (placed 0) 0
  have a := logicalCell_counts divide 1
  have b := logicalCell_counts divide 2
  cases divide <;> simp only [firstGroup,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,renameT,renameM,logicalZero_counts.1,
    logicalZero_counts.2,a.1,a.2,b.1,b.2,codec.1,codec.2.1,codec.2.2.1,codec.2.2.2]
  all_goals norm_num

theorem replay_counts (divide : Bool) :
    toffoliCount (replay divide)=(if divide then 655527 else 656038) ∧ measurementCount (replay divide)=523946 := by
  have groups := mappedGroups_counts divide 1 169
  have first := firstGroup_counts divide
  have a := logicalCell_counts divide 510
  have b := logicalCell_counts divide 511
  cases divide <;> simp only [replay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,renameT,renameM,groups.1,groups.2,
    first.1,first.2,a.1,a.2,b.1,b.2]
  all_goals norm_num

private theorem copy_counts :
    toffoliCount (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)=0 ∧
    measurementCount (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)=0 := by
  have len : (skywalkSharedField id).z.length=(skywalkSharedField id).a.length := by
    rw [skywalkShared_field_z]
    change (wireBlock id 2056 257).length=(wireBlock id 770 257).length
    simp [wireBlock]
  have copy := copyRegister_counts none (skywalkSharedField id).z (skywalkSharedField id).a len
  simpa only [Option.isSome_none,Bool.false_eq_true,if_false] using copy

theorem fieldSegment_counts (divide : Bool) :
    toffoliCount (fieldSegment divide)=(if divide then 658587 else 659098) ∧ measurementCount (fieldSegment divide)=527006 := by
  have center := converterPair_counts false
  have canonical := converterPair_counts true
  have rp := replay_counts divide
  cases divide <;> simp only [fieldSegment,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,emptyT,emptyM,
    renameT,renameM,copy_counts.1,copy_counts.2,center.1,center.2,canonical.1,canonical.2,rp.1,rp.2]
  all_goals norm_num

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.fieldSegment_support
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.fieldSegment_counts
