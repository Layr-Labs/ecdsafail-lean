import ECDSAAdd.Arithmetic.CompressedCompactFrame
import ECDSAAdd.Arithmetic.CompactSkywalkReverseFrame
import ECDSAAdd.Arithmetic.CompressedSkywalkReverse
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Actual compact reverse ticks; only each tick's local pre/post tails
are expanded, and the unchanged delayed codec schedule is decoded. -/
def compressedCompactReverse (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compressedCompactReverse w (i+1) n++compressedDecodeBefore w i++
      compactSkywalkReverseTick w i

attribute [local irreducible] run compactSkywalkReverseTick compactSkywalkReverse
attribute [local irreducible] compressedCompactReverse compressedHistoryDecode
attribute [local irreducible] compressedDecodeRange compressedDecodePrefix

theorem compressedHistory_disjoint_compactReverseTick (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (start i : Nat) (hs : start+3 ≤ 512) (hlate : start+4 ≤ i) (hi : i < 512) :
    Disjoint (wires (compressedHistoryDecode w start)) (wires (compactSkywalkReverseTick w i)) := by
  apply Finset.disjoint_left.mpr
  intro q hq ht
  obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo start hs _ (Or.inr rfl) q hq
  have mem := List.mem_toFinset.mp (compactSkywalkReverseTick_support w i hi hn ht)
  have width := compactSkywalkTick_width_bounds i hi
  have hpos : i ≠ 0 := by omega
  have away : w (compressedHistoryId start j) ∉ (compactSkywalkTickLayout w i).wires := by
    apply compactSkywalkStage_tick_away w i hi hn (compressedHistoryId start j)
      (compressedHistoryId_bound start hs j)
    all_goals
      have hj := j.isLt
      unfold compressedHistoryId
      split_ifs <;> (try simp only [skywalkPoolPreviousId,if_neg hpos]) <;> omega
  exact away mem

/-- Component charge equality also supplies exact record alignment when
zero-measurement decoders are moved before disjoint compact inverse ticks. -/
theorem compressedCompactReverse_counts_relative (w : Nat → Wire) (i n : Nat) :
    toffoliCount (compressedCompactReverse w i n) =
      toffoliCount (compactSkywalkReverse w i n)+4*compressedPackCount i n ∧
    measurementCount (compressedCompactReverse w i n) = measurementCount (compactSkywalkReverse w i n) := by
  induction n generalizing i with
  | zero => simp [compressedCompactReverse,compactSkywalkReverse,compressedPackCount,toffoliCount,measurementCount]
  | succ n ih =>
    have pack := compressedPackAfter_counts w i
    have tail := ih (i+1)
    simp only [compressedCompactReverse,compactSkywalkReverse,compressedPackCount,
      toffoliCount_append,measurementCount_append,pack.2.2.1,pack.2.2.2,tail.1,tail.2]
    constructor <;> omega

theorem compressedDecodeBefore_disjoint_compactReverse (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i j n : Nat) (hgap : i < j) (hbound : j+n ≤ 512) :
    Disjoint (wires (compressedDecodeBefore w i)) (wires (compactSkywalkReverse w j n)) := by
  induction n generalizing j with
  | zero => simp [compactSkywalkReverse,wires]
  | succ n ih =>
    have ht := ih (j+1) (by omega) (by omega)
    have hh : Disjoint (wires (compressedDecodeBefore w i)) (wires (compactSkywalkReverseTick w j)) := by
      cases he : compressedPackDue i
      · simp [compressedDecodeBefore,he,wires]
      · have hi3 := compressedPackDue_true i he
        have hs := compressedHistory_disjoint_compactReverseTick w hn hlo (i-3) j (by omega) (by omega) (by omega)
        simpa only [compressedDecodeBefore,he,if_true] using hs
    simp only [compactSkywalkReverse,wires_append,Finset.disjoint_union_right]
    exact ⟨ht,hh⟩

/-- Exact normalization of the emitted reverse program. Decoders consume no
measurements, so moving them ahead of disjoint later ticks preserves the same
record list, not merely a suitably relabeled list. This holds for all states. -/
theorem compressedCompactReverse_normalize (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hbound : i+n ≤ 512) (s : State) (m : List Bool) :
    run (compressedCompactReverse w i n) m s=
      run (compressedDecodeRange w i n ++ compactSkywalkReverse w i n) m s := by
  induction n generalizing i s m with
  | zero => simp [compressedCompactReverse,compressedDecodeRange,compactSkywalkReverse,run]
  | succ n ih =>
    have hm := (compressedCompactReverse_counts_relative w (i+1) n).2
    have hd := compressedDecodeBefore_disjoint_compactReverse w hn hlo i (i+1) n (by omega) (by omega)
    have hc := run_disjoint_commute (compressedDecodeBefore w i)
      (compactSkywalkReverse w (i+1) n) hd []
      (m.take (measurementCount (compactSkywalkReverse w (i+1) n)))
      (run (compressedDecodeRange w (i+1) n) [] s)
    rw [compressedCompactReverse,compressedDecodeRange,compactSkywalkReverse]
    simp only [run_append,measurementCount_append,hm,
      (compressedPackAfter_counts w i).2.2.2,compressedDecodeRange_measurements,
      Nat.add_zero,List.take_zero,List.drop_zero]
    rw [ih (i+1) (by omega)]
    have hzero : min 0 (measurementCount (compactSkywalkReverse w (i+1) n))=0 :=
      Nat.min_eq_left (Nat.zero_le _)
    simp only [run_append,compressedDecodeRange_measurements,List.take_zero,List.drop_zero,
      List.take_take,Nat.min_self,List.drop_take_self,hzero]
    rw [hc]

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compressedHistory_disjoint_compactReverseTick
#print axioms ECDSAAdd.Arithmetic.compressedCompactReverse_counts_relative
#print axioms ECDSAAdd.Arithmetic.compressedCompactReverse_normalize
