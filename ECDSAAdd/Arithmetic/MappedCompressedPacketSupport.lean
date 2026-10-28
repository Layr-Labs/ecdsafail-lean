import ECDSAAdd.Arithmetic.MappedCompressedPacketCorrect
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedFieldSupport
attribute [local irreducible] mixedTranscriptTape mixedTranscriptUnitTrace

theorem packet_controls (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base) :
    ∀ l ∈ packetLetters j,
      l.1.1 ∈ wires (compressedHistoryEncode base (3*j)) ∧
      l.1.2 ∈ wires (compressedHistoryEncode base (3*j)) := by
  have pool := skywalkShared_integer_nodup base hn
  have site (k : Fin 6) := compressedHistory_site_mem base pool hlo (3*j) (by omega) k
  have a := mixedTape_base_getD (3*j) (by omega)
  have c := mixedTape_base_getD (3*j+1) (by omega)
  have d := mixedTape_base_getD (3*j+2) (by omega)
  intro l hl
  simp only [packetLetters,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl|rfl
  · rw [a]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId] using site 0
    · simpa [compressedHistoryMap,compressedHistoryId] using site 1
  · rw [c]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId] using site 2
    · simpa [compressedHistoryMap,compressedHistoryId] using site 3
  · rw [d]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using site 4
    · simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using site 5

/-- The actual three cells meet the structural support premise of their
correctness proof; no support oracle is required from the arithmetic caller. -/
theorem packet_structural_support (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base) :
    wires (if divide then rawForwardPacket base (base 2400) (base 2409) (base 2410)
      ((packetLetters j).getD 0 ((0,0),(false,false))) ((packetLetters j).getD 1 ((0,0),(false,false)))
      ((packetLetters j).getD 2 ((0,0),(false,false)))
    else rawBackwardPacket base (base 2400) (base 2409) (base 2410)
      ((packetLetters j).getD 0 ((0,0),(false,false))) ((packetLetters j).getD 1 ((0,0),(false,false)))
      ((packetLetters j).getD 2 ((0,0),(false,false)))) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) (3*j) := by
  have both := packet_active_support base (base 2400) (base 2409) (base 2410)
    (3*j) (packetLetters j) (packet_controls j hj hn hlo)
  cases divide
  · simpa [packetLetters,rawBackwardPacket,OffsetBorrowedInverseCanonical.replay,List.append_assoc] using both.2
  · simpa [packetLetters,rawForwardPacket,OffsetBorrowedCanonical.replay,List.append_assoc] using both.1

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.packet_structural_support
