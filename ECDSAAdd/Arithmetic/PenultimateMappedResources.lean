import ECDSAAdd.Arithmetic.PenultimateMappedProgram
import ECDSAAdd.Arithmetic.PenultimateMappedCellProof

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.PenultimateMapped
open Secp256k1 MappedCompressed CompressedAllocation
attribute [local irreducible] wires logicalCell PenultimateSwapIdentity.cell
  EntryMappedFieldSegmentTrim.firstGroup mappedGroups mixedTranscriptUnitTrace

private theorem append_mono (A B C D : Program)
    (ha : wires A⊆wires C) (hb : wires B⊆wires D) :
    wires (A++B)⊆wires (C++D) := by
  rw [wires_append,wires_append]
  exact Finset.union_subset_union ha hb

theorem replay_support_sub (divide : Bool) :
    wires (replay divide)⊆wires (EntryMappedFieldSegmentTrim.terminalReplay divide) := by
  have small := PenultimateMappedCellProof.support_subset divide
  cases divide
  · simpa only [replay,EntryMappedFieldSegmentTrim.terminalReplay,Bool.false_eq_true,if_false]
      using append_mono _ _ _ _
        (append_mono _ _ _ _ small (Finset.Subset.refl _)) (Finset.Subset.refl _)
  · simpa only [replay,EntryMappedFieldSegmentTrim.terminalReplay,if_true]
      using append_mono _ _ _ _ (Finset.Subset.refl _) small

theorem fieldSegment_support_sub (divide : Bool) :
    wires (fieldSegment divide)⊆wires (EntryMappedFieldSegmentTrim.terminalFieldSegment divide) := by
  let P : Program := if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)
  let C : Program := renameProgram allPlaced (converterPair false)
  let D : Program := renameProgram allPlaced (converterPair true)
  let S : Program := if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else []
  have middle := append_mono (P++C) (replay divide) (P++C)
    (EntryMappedFieldSegmentTrim.terminalReplay divide) (Finset.Subset.refl _)
    (replay_support_sub divide)
  have tail := append_mono _ D _ D middle (Finset.Subset.refl _)
  have whole := append_mono _ S _ S tail (Finset.Subset.refl _)
  simpa only [fieldSegment,EntryMappedFieldSegmentTrim.terminalFieldSegment,P,C,D,S]
    using whole

theorem fieldSegment_support (divide : Bool) :
    wires (fieldSegment divide)⊆slots.toFinset :=
  (fieldSegment_support_sub divide).trans
    (EntryMappedFieldSegmentTrim.terminalFieldSegment_support divide)

end ECDSAAdd.Arithmetic.PenultimateMapped
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.replay_support_sub
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.fieldSegment_support_sub
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.fieldSegment_support
