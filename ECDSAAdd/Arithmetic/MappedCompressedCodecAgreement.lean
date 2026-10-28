import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites

namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation

/-- The currently decoded record packet is fixed by its public placement.
Its actual six-wire codec therefore uses the same labels as base encoding. -/
theorem current_history_map (j : Nat) (hj : j < 170) :
    compressedHistoryMap (placed j) (3*j)=compressedHistoryMap base (3*j) := by
  funext u
  change placed j (compressedHistoryId (3*j) u)=base (compressedHistoryId (3*j) u)
  unfold placed base
  rw [packet_fixed j _ hj (history_packet j u)]

theorem current_codec_equal (j : Nat) (hj : j < 170) :
    compressedHistoryEncode (placed j) (3*j)=compressedHistoryEncode base (3*j) ∧
    compressedHistoryDecode (placed j) (3*j)=compressedHistoryDecode base (3*j) := by
  have eq := current_history_map j hj
  constructor
  · change TranscriptCodec3.encode (compressedHistoryMap (placed j) (3*j))=
      TranscriptCodec3.encode (compressedHistoryMap base (3*j))
    rw [eq]
  · change TranscriptCodec3.decode (compressedHistoryMap (placed j) (3*j))=
      TranscriptCodec3.decode (compressedHistoryMap base (3*j))
    rw [eq]

/-- Every measurement correction is part of the equality, not just the
classical packet bits or its number of gates. Independent records are allowed. -/
theorem current_codec_run_equal (j : Nat) (hj : j < 170) (m : List Bool) (s : State) :
    run (compressedHistoryEncode (placed j) (3*j)) m s=
      run (compressedHistoryEncode base (3*j)) m s ∧
    run (compressedHistoryDecode (placed j) (3*j)) m s=
      run (compressedHistoryDecode base (3*j)) m s := by
  rw [(current_codec_equal j hj).1,(current_codec_equal j hj).2]
  exact ⟨rfl,rfl⟩

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.current_history_map
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.current_codec_equal
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.current_codec_run_equal
