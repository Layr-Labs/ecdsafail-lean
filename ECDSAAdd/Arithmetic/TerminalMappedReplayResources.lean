import ECDSAAdd.Arithmetic.TerminalMappedFieldSegment
import ECDSAAdd.Arithmetic.MappedCompressedReplayCounts

set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation
attribute [local irreducible] wires toffoliCount measurementCount mappedReplay trimReplay

theorem fieldTrimSegment_support (divide : Bool) :
    wires (fieldTrimSegment divide) ⊆ slots.toFinset := by
  have full := fieldSegment_support divide
  rw [fieldSegment_join] at full
  simp only [fieldTrimSegment,canonicalTrimReplay,canonicalMappedReplay,wires_append,
    Finset.union_subset_iff,and_assoc] at full ⊢
  exact ⟨full.1,full.2.1,trimReplay_support divide,full.2.2.2.1,full.2.2.2.2⟩

theorem fieldTrimSegment_saving (divide : Bool) :
    toffoliCount (fieldSegment divide)=toffoliCount (fieldTrimSegment divide)+(if divide then 1280 else 1281) ∧
    measurementCount (fieldSegment divide)=measurementCount (fieldTrimSegment divide)+1025 := by
  have saving := trimReplay_count_saving divide
  rw [fieldSegment_join]
  simp only [fieldTrimSegment,canonicalTrimReplay,canonicalMappedReplay,toffoliCount_append,
    measurementCount_append]
  constructor <;> omega

theorem fieldTrimSegment_counts (divide : Bool) :
    toffoliCount (fieldTrimSegment divide)=(if divide then 658841 else 659353) ∧
    measurementCount (fieldTrimSegment divide)=(if divide then 527516 else 527517) := by
  have old := fieldSegment_counts divide
  have saving := fieldTrimSegment_saving divide
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at old saving ⊢
  all_goals constructor <;> omega

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.fieldTrimSegment_support
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.fieldTrimSegment_counts
