import ECDSAAdd.Arithmetic.BalancedSharedLayoutBoundary
import ECDSAAdd.Arithmetic.BalancedTranscriptSupport
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Compact logical allocation omits the seed constant and old unary mask bank. -/
def compactSharedSites (w : Nat → Wire) : List Wire :=
  wireBlock w 0 1798 ++ wireBlock w 2056 257

def CompactSharedIndex (i : Nat) : Prop := i < 1798 ∨ 2056 ≤ i ∧ i < 2313

namespace BorrowedSkywalkCompactSupport

theorem index_mem (w : Nat → Wire) (i : Nat) (hi : CompactSharedIndex i) :
    w i∈compactSharedSites w := by
  rcases hi with hi|hi
  · apply List.mem_append_left
    simp only [wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by omega,rfl⟩
  · apply List.mem_append_right
    simp only [wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by omega,rfl⟩


private theorem mappedSites (w : Nat → Wire) (ids : List Nat) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hb : ∀i∈ids,CompactSharedIndex i) :
    (ids.map w).toFinset⊆W := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  exact hW (List.mem_toFinset.mpr (index_mem w i (hb i hi)))

theorem blockSites (w : Nat → Wire) (offset count : Nat) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W)
    (hb : ∀i,offset ≤ i → i < offset + count → CompactSharedIndex i) :
    (wireBlock w offset count).toFinset⊆W := by
  apply mappedSites w (List.range' offset count) W hW
  intro i hi
  simp only [List.mem_range'_1] at hi
  exact hb i hi.1 hi.2

theorem balancedIds_compact (i : Nat) (hi : i∈balancedSharedIds) : CompactSharedIndex i := by
  simp only [balancedSharedIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hi
  unfold CompactSharedIndex
  omega

/-- The physical kernel uses only its external sign and borrowed shared sites. -/
theorem kernelSites (w : Nat → Wire) (sign : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hs : sign∈W) :
    (balancedSharedPorts w sign).wires.toFinset⊆W := by
  have mapped := mappedSites w balancedSharedIds W hW balancedIds_compact
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
    (hW : (compactSharedSites w).toFinset⊆W) :
    (balancedSharedTargetConvert w).wires.toFinset⊆W ∧
    (balancedSharedSourceConvert w).wires.toFinset⊆W := by
  have t : (balancedSharedTargetConvert w).wires=targetIds.map w := by
    simp [balancedSharedTargetConvert,BalancedConvert.Layout.wires,targetIds,wireBlock]
  have s : (balancedSharedSourceConvert w).wires=sourceIds.map w := by
    simp [balancedSharedSourceConvert,BalancedConvert.Layout.wires,sourceIds,wireBlock]
  have bound (i : Nat) : i∈targetIds ∨ i∈sourceIds → CompactSharedIndex i := by
    simp only [targetIds,sourceIds,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    unfold CompactSharedIndex
    omega
  rw [t,s]
  exact ⟨mappedSites w targetIds W hW (fun i hi => bound i (Or.inl hi)),
    mappedSites w sourceIds W hW (fun i hi => bound i (Or.inr hi))⟩

theorem converters (w : Nat → Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) :
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
    (W : Finset Wire) (hW : (compactSharedSites w).toFinset⊆W)
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
end BorrowedSkywalkCompactSupport
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.kernelSites
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.converters
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.replay
