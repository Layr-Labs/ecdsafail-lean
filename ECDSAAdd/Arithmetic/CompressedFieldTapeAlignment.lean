import ECDSAAdd.Arithmetic.CompressedFieldInvariantStep
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport

def IndexedLetters (w : Nat → Wire) : Nat → List MixedTranscriptLetter → Prop
  | _,[] => True
  | i,l::ls => l.1=(w i,w (1028+i)) ∧ IndexedLetters w (i+1) ls

theorem indexed_zip (w : Nat → Wire) (n i : Nat) (cs : List (Bool×Bool)) :
    IndexedLetters w i (((List.range n).map (fun k => (w (i+k),w (1028+i+k)))).zip cs) := by
  induction n generalizing i cs with
  | zero => simp [IndexedLetters]
  | succ n ih =>
    cases cs with
    | nil => simp [IndexedLetters]
    | cons c cs =>
      rw [List.range_succ_eq_map,List.map_cons,List.zip_cons_cons]
      change (w (i+0),w (1028+i+0))=(w i,w (1028+i)) ∧ _
      refine ⟨by simp,?_⟩
      simpa only [List.map_map,Function.comp_def,Nat.succ_eq_add_one,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1) cs

theorem mixedTape_indexed (w : Nat → Wire) : IndexedLetters w 0 (mixedTranscriptTape w) := by
  simpa only [mixedTranscriptTape,skywalkSharedTape,Nat.zero_add] using
    indexed_zip w 512 0 mixedTranscriptUnitTrace

theorem indexed_three_tail (w : Nat → Wire) (i : Nat) (a c d : MixedTranscriptLetter)
    (tail : List MixedTranscriptLetter) (h : IndexedLetters w i (a::c::d::tail)) :
    IndexedLetters w (i+3) tail := by
  have next := h.2.2.2
  simpa only [Nat.add_assoc] using next

theorem indexed_packet_controls (w : Nat → Wire) (j : Nat) (hj : j < 170)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (a c d : MixedTranscriptLetter) (tail : List MixedTranscriptLetter)
    (h : IndexedLetters w (3*j) (a::c::d::tail)) :
    ∀ l ∈ [a,c,d],l.1.1 ∈ wires (compressedHistoryEncode w (3*j)) ∧
      l.1.2 ∈ wires (compressedHistoryEncode w (3*j)) := by
  have site (k : Fin 6) := compressedHistory_site_mem w hn hlo (3*j) (by omega) k
  have ha := h.1
  have hc := h.2.1
  have hd := h.2.2.1
  intro l hl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl|rfl
  · rw [ha]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId] using site 0
    · simpa [compressedHistoryMap,compressedHistoryId] using site 1
  · rw [hc]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId] using site 2
    · simpa [compressedHistoryMap,compressedHistoryId] using site 3
  · rw [hd]
    constructor
    · simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using site 4
    · simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using site 5

theorem packet_active_support (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (ls : List MixedTranscriptLetter)
    (h : ∀ l ∈ ls,l.1.1 ∈ wires (compressedHistoryEncode w start) ∧
      l.1.2 ∈ wires (compressedHistoryEncode w start)) :
    wires (OffsetBorrowedCanonical.replay w b sign eff ls) ⊆ groupReadSites w b sign eff start ∧
    wires (OffsetBorrowedInverseCanonical.replay w b sign eff ls) ⊆ groupReadSites w b sign eff start := by
  induction ls with
  | nil => simp [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,wires]
  | cons l ls ih =>
    have own := h l (by simp)
    have first := current_cells_support w b sign eff start l.1.1 l.1.2 l.2.1 l.2.2 own.1 own.2
    have rest := ih (fun q hq => h q (by simp [hq]))
    simp only [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,
      wires_append,Finset.union_subset_iff]
    exact ⟨⟨first.1,rest.1⟩,⟨rest.2,first.2⟩⟩

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.mixedTape_indexed
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.indexed_packet_controls
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.packet_active_support
