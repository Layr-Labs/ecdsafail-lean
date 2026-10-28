import ECDSAAdd.Arithmetic.EntryBodySupport

namespace ECDSAAdd.Arithmetic.EntryBodySupport
open MappedCompressed CompressedFieldSupport EntryMappedFieldSegmentTrim
attribute [local irreducible] wires logicalCell renameProgram logicalZero
  compressedHistoryEncode OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell

/-- Isolated concrete instantiation of the abstract support contracts.
There is no raw-packet or naturality conversion at this specialization. -/
theorem first_body_support (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) :
    wires (renameProgram base logicalZero ++ renameProgram base (logicalCell true 1) ++
      renameProgram base (logicalCell true 2)) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) 0 := by
  have pool := skywalkShared_integer_nodup base hn
  have site (k : Fin 6) := compressedHistory_site_mem base pool hlo 0 (by decide) k
  exact renamed_three_support base logicalZero (logicalCell true 0) (logicalCell true 1)
    (logicalCell true 2) (groupReadSites base (base 2400) (base 2409) (base 2410) 0)
    (logicalZero_support_sub true)
    (renamed_logical_support base true 0 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 0)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 1))
    (renamed_logical_support base true 1 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 2)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 3))
    (renamed_logical_support base true 2 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 4)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 5))

end ECDSAAdd.Arithmetic.EntryBodySupport
#print axioms ECDSAAdd.Arithmetic.EntryBodySupport.first_body_support
