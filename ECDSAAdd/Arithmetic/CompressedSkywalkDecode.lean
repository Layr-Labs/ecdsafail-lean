import ECDSAAdd.Arithmetic.CompressedSkywalkPrefix

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] run compressedEncodePrefix compressedDecodePrefix
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

theorem compressedDecodePrefix_measurements (w : Nat → Wire) (n : Nat) :
    measurementCount (compressedDecodePrefix w n)=0 := by
  induction n with
  | zero => simp [compressedDecodePrefix,measurementCount]
  | succ n ih =>
    simp only [compressedDecodePrefix,measurementCount_append,
      (compressedPackAfter_counts w n).2.2.2,ih,Nat.zero_add]

private theorem no_measurement_records (p : Program) (hp : measurementCount p=0)
    (s : State) (m n : List Bool) : run p m s=run p n s := by
  rw [← run_take p m s,← run_take p n s,hp]
  rfl

/-- Every compressed priorEncoded has a separately emitted coherent inverse.
The input domain comes from the actual exact integer-history assertion. -/
theorem compressedDecodePrefix_inverse (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p n i : Nat) (hp0 : 0 < p) (hpo : p%2=1) (hni : n ≤ i) (hi : i ≤ 512)
    (s : State) (mE mD : List Bool)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (compressedDecodePrefix w n) mD (run (compressedEncodePrefix w n) mE s)=s := by
  induction n generalizing mE mD with
  | zero => simp [compressedEncodePrefix,compressedDecodePrefix,run]
  | succ n ih =>
    have hbound : n < 512 := by omega
    let priorEncoded := run (compressedEncodePrefix w n)
      (mE.take (measurementCount (compressedEncodePrefix w n))) s
    have clean : run (compressedDecodeBefore w n) []
        (run (compressedPackAfter w n) (mE.drop (measurementCount (compressedEncodePrefix w n))) priorEncoded)=priorEncoded := by
      cases he : compressedPackDue n
      · simp only [compressedDecodeBefore,compressedPackAfter,he,Bool.false_eq_true,if_false,run]
      · have hn3 := compressedPackDue_true n he
        have same (j : Fin 6) : priorEncoded.basis (compressedHistoryMap w (n-3) j)=
            s.basis (compressedHistoryMap w (n-3) j) := by
          exact compressedPrefix_raw_next w hn hlo n hbound he s _ j
        have rawLegal := compressedHistoryStage_legal w x p i (n-3) hp0 hpo (by omega) s.basis h
        have legal :
            (priorEncoded.basis (compressedHistoryMap w (n-3) 0) && priorEncoded.basis (compressedHistoryMap w (n-3) 1))=false ∧
            (priorEncoded.basis (compressedHistoryMap w (n-3) 2) && priorEncoded.basis (compressedHistoryMap w (n-3) 3))=false ∧
            (priorEncoded.basis (compressedHistoryMap w (n-3) 4) && priorEncoded.basis (compressedHistoryMap w (n-3) 5))=false := by
          rw [same 0,same 1,same 2,same 3,same 4,same 5]
          exact rawLegal
        have hc := TranscriptCodec3.decode_encode (compressedHistoryMap w (n-3))
          (compressedHistoryMap_injective w hn (n-3) (by omega))
          (compressedHistoryMap_above w (n-3) (by omega) hlo) priorEncoded
          (mE.drop (measurementCount (compressedEncodePrefix w n))) [] legal
        simpa only [compressedDecodeBefore,compressedPackAfter,he,if_true,
          compressedHistoryEncode,compressedHistoryDecode] using hc
    rw [compressedEncodePrefix,compressedDecodePrefix,run_append,run_append]
    have hd0 := (compressedPackAfter_counts w n).2.2.2
    rw [hd0]
    simp only [List.take_zero,List.drop_zero]
    rw [clean]
    exact ih (by omega) _ _

end ECDSAAdd.Arithmetic
