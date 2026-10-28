import ECDSAAdd.Arithmetic.MappedCompressedReplayCounts

set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation
attribute [local irreducible] wires toffoliCount measurementCount logicalCell mappedGroups

/-- Only the field replay is trimmed. Integer recording and its170 codecs
remain unchanged; the single raw residual field letter is logical510. -/
def trimReplay (divide : Bool) : Program :=
  if divide then mappedGroups divide 0 170 ++ renameProgram allPlaced (logicalCell divide 510)
  else renameProgram allPlaced (logicalCell divide 510) ++ mappedGroups divide 0 170

theorem trimReplay_join (divide : Bool) :
    mappedReplay divide = if divide then trimReplay divide ++ renameProgram allPlaced (logicalCell divide 511)
      else renameProgram allPlaced (logicalCell divide 511) ++ trimReplay divide := by
  cases divide <;> simp only [mappedReplay,trimReplay,Bool.false_eq_true,if_false,if_true,List.append_assoc]

theorem trimReplay_support (divide : Bool) : wires (trimReplay divide) ⊆ slots.toFinset := by
  have full := mappedReplay_support divide
  cases divide <;> simp only [mappedReplay,trimReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff,and_assoc] at full ⊢
  · exact ⟨full.2.1,full.2.2⟩
  · exact ⟨full.1,full.2.1⟩

theorem trimReplay_counts (divide : Bool) :
    toffoliCount (trimReplay divide)=(if divide then 655270 else 655781) ∧ measurementCount (trimReplay divide)=523945 := by
  have groups := mappedGroups_counts divide 0 170
  have cell := logicalCell_counts divide 510
  have counts := renameProgram_counts allPlaced (logicalCell divide 510)
  cases divide <;> simp only [trimReplay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,counts.1,counts.2,
    groups.1,groups.2,cell.1,cell.2]
  all_goals norm_num

theorem trimReplay_count_saving (divide : Bool) :
    toffoliCount (mappedReplay divide)=toffoliCount (trimReplay divide)+(if divide then 1280 else 1281) ∧
    measurementCount (mappedReplay divide)=measurementCount (trimReplay divide)+1025 := by
  rw [(mappedReplay_counts divide).1,(mappedReplay_counts divide).2,
    (trimReplay_counts divide).1,(trimReplay_counts divide).2]
  cases divide <;> norm_num

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimReplay_support
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimReplay_counts
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimReplay_count_saving
