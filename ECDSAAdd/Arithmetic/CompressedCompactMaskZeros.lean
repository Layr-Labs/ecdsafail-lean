import ECDSAAdd.Arithmetic.CompressedCompactZeroSlots
import ECDSAAdd.Arithmetic.SkywalkArithmeticCore

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] compressedHistoryEncode compressedEncodePrefix run

private theorem block_mem (w : Nat → Wire) (a n i : Nat)
    (ha : a ≤ i) (hi : i < a+n) : w i∈wireBlock w a n := by
  simp only [wireBlock,List.mem_map,List.mem_range'_1]
  exact ⟨i,⟨ha,hi⟩,rfl⟩

theorem compressedPrefix_history_support (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n : Nat) (hn512 : n ≤ 512) :
    wires (compressedEncodePrefix w n)⊆
      (wireBlock w 0 512++wireBlock w 1028 512).toFinset := by
  induction n with
  | zero => simp [compressedEncodePrefix,wires]
  | succ n ih =>
    have old := ih (by omega)
    have now : wires (compressedPackAfter w n)⊆
        (wireBlock w 0 512++wireBlock w 1028 512).toFinset := by
      intro q hq
      cases due : compressedPackDue n
      · simp [compressedPackAfter,due,wires] at hq
      · have hd := compressedPackDue_true n due
        have qenc : q∈wires (compressedHistoryEncode w (n-3)) := by
          simpa only [compressedPackAfter,due,if_true] using hq
        obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo (n-3) (by omega)
          _ (Or.inl rfl) q qenc
        have region := compressedHistoryId_region (n-3) (by omega) j
        apply List.mem_toFinset.mpr
        rcases region with h|h
        · apply List.mem_append_left
          exact block_mem w 0 512 _ (by omega) h
        · apply List.mem_append_right
          exact block_mem w 1028 512 _ h.1 h.2
    simpa only [compressedEncodePrefix,wires_append,Finset.union_subset_iff] using
      And.intro old now

/-- The170 reusable mask positions are actual compact terminal tail zeros. -/
theorem compactTerminal_mask_zero (w : Nat → Wire) (r : SkywalkRails.State)
    (s : BasisState) (h : CompactSkywalkStage w r 512 s) (j : Nat) (hj : j < 170) :
    s (w (515+j))=false := by
  have clean := h.2.1
  have released : (compactSkywalkSignPoolA w 512).released=wireBlock w 514 256 := by
    change (wireBlock w 512 258).drop 2=wireBlock w 514 256
    rw [←wireBlock_append w 512 2 256]
    simp [wireBlock_length]
  apply clean
  rw [released]
  exact block_mem w 514 256 (515+j) (by omega) (by omega)

/-- History packing preserves every terminal mask zero, for all records. -/
theorem compressedCompactStage_512_mask_zero (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (s : State) (h : CompressedCompactStage w x p 512 s.basis)
    (j : Nat) (hj : j < 170) : s.basis (w (515+j))=false := by
  obtain ⟨raw,hraw,bits⟩ := h
  have zero := compactTerminal_mask_zero w _ raw.basis hraw j hj
  have support := compressedPrefix_history_support w hn hlo 512 (by decide)
  have away : w (515+j)∉wires (compressedEncodePrefix w 512) := by
    intro hq
    have hhist := List.mem_toFinset.mp (support hq)
    rcases List.mem_append.mp hhist with hq|hq
    all_goals
      obtain ⟨k,hk,he⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hk
      have eq := skywalkPool_index_inj w hn k (515+j) (by omega) (by omega) he
      omega
  rw [bits]
  exact (run_preserves_outside _ [] raw _ away).trans zero

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compressedPrefix_history_support
#print axioms ECDSAAdd.Arithmetic.compactTerminal_mask_zero
#print axioms ECDSAAdd.Arithmetic.compressedCompactStage_512_mask_zero
