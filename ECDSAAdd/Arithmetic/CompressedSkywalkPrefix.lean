import ECDSAAdd.Arithmetic.CompressedSkywalkLoop
import ECDSAAdd.Arithmetic.CompressedSkywalkSchedule

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- Pure reference encoding of the history groups packed before tick n.
This is also an executable program, not a circuit oracle. -/
def compressedEncodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => compressedEncodePrefix w n ++ compressedPackAfter w n

def compressedDecodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => compressedDecodeBefore w n ++ compressedDecodePrefix w n

attribute [local irreducible] run narrowSkywalkScheduledTick narrowSkywalkScheduledUntick
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] compressedEncodePrefix compressedDecodePrefix

theorem compressedPackDue_true (i : Nat) (h : compressedPackDue i=true) :
    3 ≤ i ∧ i%3=0 := by
  simpa only [compressedPackDue,decide_eq_true_eq] using h

theorem compressedPrefix_disjoint_tick (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n i : Nat) (hni : n ≤ i) (hi : i < 512) :
    Disjoint (wires (compressedEncodePrefix w n)) (wires (narrowSkywalkScheduledTick w i)) ∧
    Disjoint (wires (compressedDecodePrefix w n)) (wires (narrowSkywalkScheduledUntick w i)) := by
  induction n with
  | zero => simp [compressedEncodePrefix,compressedDecodePrefix,wires]
  | succ n ih =>
    have hprev := ih (by omega)
    have hcurrent : Disjoint (wires (compressedPackAfter w n)) (wires (narrowSkywalkScheduledTick w i)) ∧
        Disjoint (wires (compressedDecodeBefore w n)) (wires (narrowSkywalkScheduledUntick w i)) := by
      cases he : compressedPackDue n
      · simp [compressedPackAfter,compressedDecodeBefore,he,wires]
      · have hd := compressedPackDue_true n he
        have hh := compressedHistory_disjoint_later w hn hlo (n-3) i (by omega) (by omega) hi
        simpa only [compressedPackAfter,compressedDecodeBefore,he,if_true] using hh
    simp only [compressedEncodePrefix,compressedDecodePrefix,wires_append,Finset.disjoint_union_left]
    exact ⟨⟨hprev.1,hcurrent.1⟩,⟨hcurrent.2,hprev.2⟩⟩

theorem compressedHistory_windows_disjoint (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (a b : Nat) (ha : a+3 ≤ 512) (hb : b+3 ≤ 512) (hab : a+3 ≤ b) :
    Disjoint (wires (compressedHistoryEncode w a)) (wires (compressedHistoryEncode w b)) := by
  apply Finset.disjoint_left.mpr
  intro q hqa hqb
  obtain ⟨j,hj⟩ := compressedHistory_gate_mem w hn hlo a ha _ (Or.inl rfl) q hqa
  obtain ⟨k,hk⟩ := compressedHistory_gate_mem w hn hlo b hb _ (Or.inl rfl) q hqb
  have he := skywalkPool_index_inj w hn _ _
    (compressedHistoryId_bound a ha j) (compressedHistoryId_bound b hb k) (hj.symm.trans hk)
  have hji := j.isLt
  have hki := k.isLt
  unfold compressedHistoryId at he
  split_ifs at he <;> omega

/-- Earlier packed groups cannot change the raw inputs of the next group.
Divisibility by three supplies the exact three-symbol separation. -/
theorem compressedPrefix_disjoint_next (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n i : Nat) (hni : n ≤ i) (hi : i < 512) (hdue : compressedPackDue i=true) :
    Disjoint (wires (compressedEncodePrefix w n)) (wires (compressedHistoryEncode w (i-3))) := by
  induction n with
  | zero => simp [compressedEncodePrefix,wires]
  | succ n ih =>
    have hp := ih (by omega)
    have hc : Disjoint (wires (compressedPackAfter w n)) (wires (compressedHistoryEncode w (i-3))) := by
      cases he : compressedPackDue n
      · simp [compressedPackAfter,he,wires]
      · have hn3 := compressedPackDue_true n he
        have hi3 := compressedPackDue_true i hdue
        have hsep : n+3 ≤ i := by omega
        have hh := compressedHistory_windows_disjoint w hn hlo (n-3) (i-3) (by omega) (by omega) (by omega)
        simpa only [compressedPackAfter,he,if_true] using hh
    simp only [compressedEncodePrefix,wires_append,Finset.disjoint_union_left]
    exact ⟨hp,hc⟩

/-- Every raw group site is present in encoder support, including the site
which becomes zero after packing. -/
theorem compressedHistory_site_mem (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (start : Nat) (hs : start+3 ≤ 512) (j : Fin 6) :
    compressedHistoryMap w start j∈wires (compressedHistoryEncode w start) := by
  let f := compressedHistoryMap w start
  have hf := compressedHistoryMap_injective w hn start hs
  have hl := compressedHistoryMap_above w start hs hlo
  have he := TranscriptCodec3.placement_apply f hf hl j
  unfold compressedHistoryEncode
  change f j∈wires (TranscriptCodec3.encode f)
  rw [TranscriptCodec3.encode,renameProgram_support,TranscriptCodec3.support.1]
  apply Finset.mem_image.mpr
  exact ⟨j,Finset.mem_range.mpr j.isLt,he⟩

theorem compressedPrefix_raw_next (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i : Nat) (hi : i < 512) (hdue : compressedPackDue i=true)
    (s : State) (m : List Bool) (j : Fin 6) :
    (run (compressedEncodePrefix w i) m s).basis (compressedHistoryMap w (i-3) j)=
      s.basis (compressedHistoryMap w (i-3) j) := by
  apply run_preserves_outside
  have hd := compressedPrefix_disjoint_next w hn hlo i i (Nat.le_refl i) hi hdue
  have h3 := compressedPackDue_true i hdue
  intro hq
  exact Finset.disjoint_left.mp hd hq
    (compressedHistory_site_mem w hn hlo (i-3) (by omega) j)

end ECDSAAdd.Arithmetic
