import ECDSAAdd.Arithmetic.PenultimateSwapIdentity
import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrimInverse

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.PenultimateMapped
open Secp256k1 MappedCompressed CompressedAllocation
attribute [local irreducible] run wires toffoliCount measurementCount logicalCell

/-- Keep all packets and the entry cancellation; replace only raw cell510. -/
def replay (divide : Bool) : Program :=
  if divide then EntryMappedFieldSegmentTrim.firstGroup divide ++ mappedGroups divide 1 169 ++
      renameProgram allPlaced (PenultimateSwapIdentity.cell divide)
  else renameProgram allPlaced (PenultimateSwapIdentity.cell divide) ++
      mappedGroups divide 1 169 ++ EntryMappedFieldSegmentTrim.firstGroup divide

def fieldSegment (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (converterPair false) ++ replay divide ++
  renameProgram allPlaced (converterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

theorem replay_counts (divide : Bool) :
    toffoliCount (replay divide)=(if divide then 653990 else 654500) ∧ measurementCount (replay divide)=522920 := by
  have groups := mappedGroups_counts divide 1 169
  have first := EntryMappedFieldSegmentTrim.firstGroup_counts divide
  have cell := PenultimateSwapIdentity.cell_counts divide
  have renamed := renameProgram_counts allPlaced (PenultimateSwapIdentity.cell divide)
  cases divide <;> simp only [replay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,groups.1,groups.2,first.1,first.2,
    renamed.1,renamed.2,cell.1,cell.2]
  all_goals norm_num

theorem fieldSegment_counts (divide : Bool) :
    toffoliCount (fieldSegment divide)=(if divide then 657050 else 657560) ∧ measurementCount (fieldSegment divide)=525980 := by
  have old := EntryMappedFieldSegmentTrim.terminalFieldSegment_counts divide
  have oldReplay := EntryMappedFieldSegmentTrim.terminalReplay_counts divide
  have fresh := replay_counts divide
  simp only [EntryMappedFieldSegmentTrim.terminalFieldSegment,toffoliCount_append,
    measurementCount_append,oldReplay.1,oldReplay.2] at old
  simp only [fieldSegment,toffoliCount_append,measurementCount_append,fresh.1,fresh.2]
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at old oldReplay fresh ⊢
  all_goals constructor <;> omega

theorem saving (divide : Bool) :
    toffoliCount (EntryMappedFieldSegmentTrim.terminalFieldSegment divide)=
      toffoliCount (fieldSegment divide)+257 ∧
    measurementCount (EntryMappedFieldSegmentTrim.terminalFieldSegment divide)=
      measurementCount (fieldSegment divide)+1 := by
  rw [(EntryMappedFieldSegmentTrim.terminalFieldSegment_counts divide).1,
    (EntryMappedFieldSegmentTrim.terminalFieldSegment_counts divide).2,
    (fieldSegment_counts divide).1,(fieldSegment_counts divide).2]
  cases divide <;> norm_num

end ECDSAAdd.Arithmetic.PenultimateMapped
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.replay_counts
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.fieldSegment_counts
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.saving
