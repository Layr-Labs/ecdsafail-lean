import ECDSAAdd.Arithmetic.CompressedSkywalkDecode

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

def compressedDecodeRange (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compressedDecodeRange w (i+1) n ++ compressedDecodeBefore w i

attribute [local irreducible] run narrowSkywalkRoutedUnloop narrowSkywalkScheduledUntick
attribute [local irreducible] compressedSkywalkUnloop compressedHistoryDecode
attribute [local irreducible] compressedDecodeRange compressedDecodePrefix

theorem compressedDecodeRange_measurements (w : Nat → Wire) (i n : Nat) :
    measurementCount (compressedDecodeRange w i n)=0 := by
  induction n generalizing i with
  | zero => simp [compressedDecodeRange,measurementCount]
  | succ n ih =>
    simp only [compressedDecodeRange,measurementCount_append,ih,
      (compressedPackAfter_counts w i).2.2.2,Nat.zero_add]

theorem compressedDecodeBefore_disjoint_unloop (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i j n : Nat) (hgap : i < j) (hbound : j+n ≤ 512) :
    Disjoint (wires (compressedDecodeBefore w i)) (wires (narrowSkywalkRoutedUnloop w j n)) := by
  induction n generalizing j with
  | zero => simp [narrowSkywalkRoutedUnloop,wires]
  | succ n ih =>
    have ht := ih (j+1) (by omega) (by omega)
    have hh : Disjoint (wires (compressedDecodeBefore w i)) (wires (narrowSkywalkScheduledUntick w j)) := by
      cases he : compressedPackDue i
      · simp [compressedDecodeBefore,he,wires]
      · have hi3 := compressedPackDue_true i he
        have hs := (compressedHistory_disjoint_later w hn hlo (i-3) j (by omega) (by omega) (by omega)).2
        simpa only [compressedDecodeBefore,he,if_true] using hs
    simp only [narrowSkywalkRoutedUnloop,wires_append,Finset.disjoint_union_right]
    exact ⟨ht,hh⟩

/-- Exact normalization of the emitted reverse program. Decoders consume no
measurements, so moving them ahead of disjoint later ticks preserves the same
record list, not merely a suitably relabeled list. This holds for all states. -/
theorem compressedSkywalkUnloop_normalize (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hbound : i+n ≤ 512) (s : State) (m : List Bool) :
    run (compressedSkywalkUnloop w i n) m s=
      run (compressedDecodeRange w i n ++ narrowSkywalkRoutedUnloop w i n) m s := by
  induction n generalizing i s m with
  | zero => simp [compressedSkywalkUnloop,compressedDecodeRange,narrowSkywalkRoutedUnloop,run]
  | succ n ih =>
    have hm := (compressedSkywalkLoop_counts w (i+1) n).2.2.2
    have hd := compressedDecodeBefore_disjoint_unloop w hn hlo i (i+1) n (by omega) (by omega)
    have hc := run_disjoint_commute (compressedDecodeBefore w i)
      (narrowSkywalkRoutedUnloop w (i+1) n) hd []
      (m.take (measurementCount (narrowSkywalkRoutedUnloop w (i+1) n)))
      (run (compressedDecodeRange w (i+1) n) [] s)
    rw [compressedSkywalkUnloop,compressedDecodeRange,narrowSkywalkRoutedUnloop]
    simp only [run_append,measurementCount_append,hm,
      (compressedPackAfter_counts w i).2.2.2,compressedDecodeRange_measurements,
      Nat.add_zero,List.take_zero,List.drop_zero]
    rw [ih (i+1) (by omega)]
    have hzero : min 0 (measurementCount (narrowSkywalkRoutedUnloop w (i+1) n))=0 :=
      Nat.min_eq_left (Nat.zero_le _)
    simp only [run_append,compressedDecodeRange_measurements,List.take_zero,List.drop_zero,
      List.take_take,Nat.min_self,List.drop_take_self,hzero]
    rw [hc]

theorem compressedDecodeRange_last (w : Nat → Wire) (i n : Nat) :
    compressedDecodeRange w i (n+1)=compressedDecodeBefore w (i+n) ++ compressedDecodeRange w i n := by
  induction n generalizing i with
  | zero => simp [compressedDecodeRange]
  | succ n ih =>
    rw [compressedDecodeRange,ih]
    have hi : (i+1)+n=i+(n+1) := by omega
    rw [hi]
    simp only [compressedDecodeRange,List.append_assoc]

theorem compressedDecodeRange_zero (w : Nat → Wire) (n : Nat) :
    compressedDecodeRange w 0 n=compressedDecodePrefix w n := by
  induction n with
  | zero => simp [compressedDecodeRange,compressedDecodePrefix]
  | succ n ih =>
    rw [compressedDecodeRange_last,compressedDecodePrefix,ih,Nat.zero_add]

end ECDSAAdd.Arithmetic
