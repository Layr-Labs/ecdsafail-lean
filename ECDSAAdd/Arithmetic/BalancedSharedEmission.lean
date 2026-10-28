import ECDSAAdd.Arithmetic.BalancedSharedLayoutReplay

namespace ECDSAAdd.Arithmetic

/-- Production emission is independent of proof arguments. The concrete
layout certificate is supplied only when proving its semantics/resources. -/
def balancedSharedReplayProgram (w : Nat → Wire) (b effG effS : Wire) : Program :=
  BalancedConvert.center (balancedSharedTargetConvert w)++
  BalancedConvert.center (balancedSharedSourceConvert w)++
  balancedTranscriptReplay (balancedSharedPorts w effG) b effS (mixedTranscriptTape w)++
  BalancedConvert.canonical (balancedSharedTargetConvert w)++
  BalancedConvert.canonical (balancedSharedSourceConvert w)

theorem balancedSharedReplayProgram_eq (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    balancedSharedReplayProgram w b effG effS=
      balancedSharedCanonicalTapeReplay w b effG effS hn := by
  simp only [balancedSharedReplayProgram,balancedSharedCanonicalTapeReplay,
    balancedSharedCanonicalReplay,balancedTranscriptCanonicalReplay,
    balancedTranscriptCenterPair,balancedTranscriptCanonicalPair,balancedSharedBoundary,
    List.append_assoc]

theorem balancedSharedReplayProgram_counts (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    toffoliCount (balancedSharedReplayProgram w b effG effS)=788980 ∧
    measurementCount (balancedSharedReplayProgram w b effG effS)=657908 := by
  rw [balancedSharedReplayProgram_eq w b effG effS hn]
  exact balancedSharedCanonicalTapeReplay_counts w b effG effS hn hf ho

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.balancedSharedReplayProgram_eq
#print axioms ECDSAAdd.Arithmetic.balancedSharedReplayProgram_counts
