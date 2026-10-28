import ECDSAAdd.Arithmetic.CompressedSkywalkLayout
import ECDSAAdd.Arithmetic.DisjointPrograms

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] narrowSkywalkScheduledTick narrowSkywalkScheduledUntick
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

/-- All codec instructions and corrections stay on the six real history
sites. This includes both encoder and decoder support. -/
theorem compressedHistory_gate_mem (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (start : Nat) (hs : start+3 ≤ 512)
    (p : Program) (hp : p=compressedHistoryEncode w start ∨ p=compressedHistoryDecode w start)
    (q : Wire) (hq : q∈wires p) :
    ∃ j : Fin 6,q=w (compressedHistoryId start j) := by
  let f := compressedHistoryMap w start
  have hf := compressedHistoryMap_injective w hn start hs
  have hl := compressedHistoryMap_above w start hs hlo
  have hw : wires p=(Finset.range 6).image (TranscriptCodec3.placement f) := by
    rcases hp with rfl|rfl
    · simp only [f,compressedHistoryEncode,TranscriptCodec3.encode,renameProgram_support,
        TranscriptCodec3.support.1]
    · simp only [f,compressedHistoryDecode,TranscriptCodec3.decode,renameProgram_support,
        TranscriptCodec3.support.2]
  rw [hw] at hq
  obtain ⟨j,hj,hjq⟩ := Finset.mem_image.mp hq
  have hlt := Finset.mem_range.mp hj
  have he : TranscriptCodec3.placement f j=f ⟨j,hlt⟩ :=
    TranscriptCodec3.placement_apply f hf hl ⟨j,hlt⟩
  exact ⟨⟨j,hlt⟩,hjq.symm.trans he⟩

private theorem compressedHistory_away_tick (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (start i : Nat)
    (hs : start+3 ≤ 512) (hlate : start+4 ≤ i) (hi : i < 512) (j : Fin 6) :
    w (compressedHistoryId start j)∉(skywalkPoolTick w i).wires.toFinset := by
  intro h
  have hlist := List.mem_toFinset.mp h
  rw [skywalkPool_wires_map] at hlist
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hlist
  have hid := skywalkPool_index_inj w hn k (compressedHistoryId start j)
    (skywalkPool_id_bound i k hi hk) (compressedHistoryId_bound start hs j) he
  have hq := j.isLt
  have hpos : i≠0 := by omega
  simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hpos,List.mem_cons,
    List.mem_append,List.mem_range'_1] at hk
  unfold compressedHistoryId at hid
  split_ifs at hid <;> omega

/-- A group can commute past later ticks only after the following tick has
consumed its final orientation. The boundary is an exact support theorem. -/
theorem compressedHistory_disjoint_later (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (start i : Nat) (hs : start+3 ≤ 512) (hlate : start+4 ≤ i) (hi : i < 512) :
    Disjoint (wires (compressedHistoryEncode w start)) (wires (narrowSkywalkScheduledTick w i)) ∧
    Disjoint (wires (compressedHistoryDecode w start)) (wires (narrowSkywalkScheduledUntick w i)) := by
  have ht := narrowSkywalkScheduledTick_support w i hn hi
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hq htq
    obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo start hs _ (Or.inl rfl) q hq
    exact compressedHistory_away_tick w hn start i hs hlate hi j (ht.1 htq)
  · apply Finset.disjoint_left.mpr
    intro q hq htq
    obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo start hs _ (Or.inr rfl) q hq
    exact compressedHistory_away_tick w hn start i hs hlate hi j (ht.2 htq)

theorem compressedHistory_commute_later (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (start i : Nat) (hs : start+3 ≤ 512) (hlate : start+4 ≤ i) (hi : i < 512)
    (s : State) (mc mt : List Bool) :
    run (compressedHistoryEncode w start) mc (run (narrowSkywalkScheduledTick w i) mt s)=
      run (narrowSkywalkScheduledTick w i) mt (run (compressedHistoryEncode w start) mc s) ∧
    run (compressedHistoryDecode w start) mc (run (narrowSkywalkScheduledUntick w i) mt s)=
      run (narrowSkywalkScheduledUntick w i) mt (run (compressedHistoryDecode w start) mc s) := by
  have hd := compressedHistory_disjoint_later w hn hlo start i hs hlate hi
  exact ⟨run_disjoint_commute _ _ hd.1 mc mt s,run_disjoint_commute _ _ hd.2 mc mt s⟩

end ECDSAAdd.Arithmetic
