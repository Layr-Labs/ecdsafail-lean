import ECDSAAdd.Arithmetic.BalancedSharedLayoutBoundary
import ECDSAAdd.Arithmetic.BalancedTranscriptSupport
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptSupport
import ECDSAAdd.Arithmetic.BalancedSharedFieldSupportHelpers
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BalancedSharedFieldSupport

private theorem mappedSites (w : Nat → Wire) (ids : List Nat) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) (hb : ∀i∈ids,i < 2314) :
    (ids.map w).toFinset⊆W := by
  intro q hq
  exact hW (List.mem_toFinset.mpr
    (balancedSharedLayout_mapSubset w ids hb (List.mem_toFinset.mp hq)))

/-- The physical kernel uses only its external sign and borrowed shared sites. -/
theorem kernelSites (w : Nat → Wire) (sign : Wire) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) (hs : sign∈W) :
    (balancedSharedPorts w sign).wires.toFinset⊆W := by
  have mapped := mappedSites w balancedSharedIds W hW balancedSharedIds_bound
  have view (q : Wire) : q∈(balancedSharedPorts w sign).wires ↔
      q=sign ∨ q∈balancedSharedIds.map w := by
    simp only [balancedSharedPorts,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,balancedSharedIds,wireBlock,List.map_append,
      List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  intro q hq
  rcases (view q).mp (List.mem_toFinset.mp hq) with rfl|hm
  · exact hs
  · exact mapped (List.mem_toFinset.mpr hm)

private def targetIds :=
  [1797,1027,1796,2311]++List.range' 2056 255++List.range' 1540 255
private def sourceIds :=
  [1797,1027,1796,1025]++List.range' 770 255++List.range' 1540 255

/-- Both endpoint converters borrow their data and scratch from the shared bank. -/
theorem converterSites (w : Nat → Wire) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) :
    (balancedSharedTargetConvert w).wires.toFinset⊆W ∧
    (balancedSharedSourceConvert w).wires.toFinset⊆W := by
  have t : (balancedSharedTargetConvert w).wires=targetIds.map w := by
    simp [balancedSharedTargetConvert,BalancedConvert.Layout.wires,targetIds,wireBlock]
  have s : (balancedSharedSourceConvert w).wires=sourceIds.map w := by
    simp [balancedSharedSourceConvert,BalancedConvert.Layout.wires,sourceIds,wireBlock]
  have bound (i : Nat) : i∈targetIds ∨ i∈sourceIds → i < 2314 := by
    simp only [targetIds,sourceIds,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega
  rw [t,s]
  exact ⟨mappedSites w targetIds W hW (fun i hi => bound i (Or.inl hi)),
    mappedSites w sourceIds W hW (fun i hi => bound i (Or.inr hi))⟩

theorem converters (w : Nat → Wire) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) :
    (wires (BalancedConvert.center (balancedSharedTargetConvert w))⊆W ∧
      wires (BalancedConvert.center (balancedSharedSourceConvert w))⊆W) ∧
    (wires (BalancedConvert.canonical (balancedSharedTargetConvert w))⊆W ∧
      wires (BalancedConvert.canonical (balancedSharedSourceConvert w))⊆W) := by
  have own := converterSites w W hW
  have t := BalancedConvert.support (balancedSharedTargetConvert w)
  have s := BalancedConvert.support (balancedSharedSourceConvert w)
  exact ⟨⟨t.1.trans own.1,s.1.trans own.2⟩,⟨t.2.trans own.1,s.2.trans own.2⟩⟩

/-- This allocation includes b because every emitted selection window reads it. -/
theorem replay (w : Nat → Wire) (b effG effS : Wire) (ls : List MixedTranscriptLetter)
    (W : Finset Wire) (hW : (skywalkSharedWires w).toFinset⊆W)
    (hb : b∈W) (hg : effG∈W) (hs : effS∈W)
    (ht : ∀l∈ls,l.1.1∈W ∧ l.1.2∈W) :
    wires (balancedTranscriptReplay (balancedSharedPorts w effG) b effS ls)⊆W ∧
    wires (balancedInverseTranscriptReplay (balancedSharedPorts w effG) b effS ls)⊆W := by
  have own := kernelSites w effG W hW hg
  have used : (balancedTranscriptSupport (balancedSharedPorts w effG) b effS ls).toFinset⊆W := by
    intro q hq
    simp only [balancedTranscriptSupport,List.mem_toFinset,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with rfl|rfl|hk|htape
    · exact hb
    · exact hs
    · exact own (List.mem_toFinset.mpr hk)
    · obtain ⟨l,hl,hq⟩ := List.mem_flatMap.mp htape
      have record := ht l hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl
      · exact record.1
      · exact record.2
  have invUsed : (balancedInverseTranscriptSupport (balancedSharedPorts w effG) b effS ls).toFinset⊆W := used
  exact ⟨(balancedTranscriptReplay_support _ _ _ ls (balancedSharedPorts_widths w effG)).trans used,
    (balancedInverseTranscriptReplay_support _ _ _ ls (balancedSharedPorts_widths w effG)).trans invUsed⟩
end ECDSAAdd.Arithmetic.BalancedSharedFieldSupport
#print axioms ECDSAAdd.Arithmetic.BalancedSharedFieldSupport.kernelSites
#print axioms ECDSAAdd.Arithmetic.BalancedSharedFieldSupport.converters
#print axioms ECDSAAdd.Arithmetic.BalancedSharedFieldSupport.replay
