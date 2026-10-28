import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalReplay
namespace ECDSAAdd.Arithmetic

/-- Proof-independent emission on the original shared point-addition ports. -/
def offsetBorrowedSharedReplayProgram (w : Nat → Wire) (b effG effS : Wire) : Program :=
  BalancedConvert.center (balancedSharedTargetConvert w)++
  BalancedConvert.center (balancedSharedSourceConvert w)++
  OffsetBorrowedCanonical.replay w b effG effS (mixedTranscriptTape w)++
  BalancedConvert.canonical (balancedSharedTargetConvert w)++
  BalancedConvert.canonical (balancedSharedSourceConvert w)

theorem offsetBorrowedSharedReplayProgram_eq (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    offsetBorrowedSharedReplayProgram w b effG effS=
      OffsetBorrowedCanonical.canonicalTapeReplay w b effG effS hn := by
  simp only [offsetBorrowedSharedReplayProgram,OffsetBorrowedCanonical.canonicalTapeReplay,
    OffsetBorrowedCanonical.canonicalReplay,balancedTranscriptCenterPair,
    balancedTranscriptCanonicalPair,balancedSharedBoundary,List.append_assoc]

theorem offsetBorrowedSharedReplayProgram_counts (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    toffoliCount (offsetBorrowedSharedReplayProgram w b effG effS)=658420 ∧
    measurementCount (offsetBorrowedSharedReplayProgram w b effG effS)=527860 := by
  rw [offsetBorrowedSharedReplayProgram_eq w b effG effS hn]
  exact OffsetBorrowedCanonical.canonicalTapeReplay_counts w b effG effS hn
    (mixedTranscriptTape_layout w b effG effS hf) ho

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.offsetBorrowedSharedReplayProgram_counts
