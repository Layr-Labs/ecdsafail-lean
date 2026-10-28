import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrimProof

namespace ECDSAAdd.Arithmetic.EntryBodySupport
open MappedCompressed CompressedFieldSupport
attribute [local irreducible] wires logicalCell renameProgram
  OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell

/-- Support composition is checked over abstract programs. Neither the
renamed cell programs nor their concrete256-bit gate lists are normalized. -/
theorem renamed_three_support (f : Wire → Wire) (P Q R S : Program) (W : Finset Wire)
    (sub : wires P ⊆ wires Q)
    (hq : wires (renameProgram f Q) ⊆ W)
    (hr : wires (renameProgram f R) ⊆ W)
    (hs : wires (renameProgram f S) ⊆ W) :
    wires (renameProgram f P ++ renameProgram f R ++ renameProgram f S) ⊆ W := by
  have renamed : wires (renameProgram f P) ⊆ wires (renameProgram f Q) := by
    rw [renameProgram_support,renameProgram_support]
    exact Finset.image_mono f sub
  rw [wires_append,wires_append]
  exact Finset.union_subset (Finset.union_subset (renamed.trans hq) hr) hs

/-- The naturality conversion is checked with an abstract placement and
cell index, before any caller instantiates its recorded constants or wires. -/
theorem renamed_logical_support (f : Nat → Wire) (divide : Bool) (i start : Nat)
    (hg : f i ∈ wires (compressedHistoryEncode f start))
    (hs : f (1028+i) ∈ wires (compressedHistoryEncode f start)) :
    wires (renameProgram f (logicalCell divide i)) ⊆
      groupReadSites f (f 2400) (f 2409) (f 2410) start := by
  have leaf := current_cells_support f (f 2400) (f 2409) (f 2410) start
    (f i) (f (1028+i)) (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 hg hs
  rw [FieldRename.logical_cell_natural]
  cases divide
  · simpa only [Bool.false_eq_true,if_false] using leaf.2
  · simpa only [if_true] using leaf.1

end ECDSAAdd.Arithmetic.EntryBodySupport
#print axioms ECDSAAdd.Arithmetic.EntryBodySupport.renamed_three_support
#print axioms ECDSAAdd.Arithmetic.EntryBodySupport.renamed_logical_support
