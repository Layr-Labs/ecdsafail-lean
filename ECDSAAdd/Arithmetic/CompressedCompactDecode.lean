import ECDSAAdd.Arithmetic.CompressedCompactReverseProgram
import ECDSAAdd.Arithmetic.CompressedSkywalkRestore
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run compressedDecodePrefix compressedEncodePrefix
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

/-- Every compressed priorEncoded has a separately emitted coherent inverse.
The input domain comes from the actual exact integer-history assertion. -/
theorem compressedCompactDecodePrefix_inverse (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p n i : Nat) (hp0 : 0 < p) (hpo : p%2 = 1) (hni : n ≤ i) (hi : i ≤ 512)
    (s : State) (mE mD : List Bool)
    (h : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
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
        have rawLegal := compressedCompactHistory_legal w hn x p i (n-3) hp0 hpo (by omega) hi s.basis h
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

/-- The actual coherent decoder recovers the compact raw state, including
caller outsiders, and preserves the current input phase independently of records. -/
theorem compressedCompactStage_decoded (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p n : Nat) (hp0 : 0 < p) (hpo : p%2 = 1) (hn512 : n ≤ 512)
    (s : State) (h : CompressedCompactStage w x p n s.basis) :
    (run (compressedDecodePrefix w n) [] s).phase = s.phase ∧
    CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) n
      (run (compressedDecodePrefix w n) [] s).basis := by
  obtain ⟨raw,hraw,hbasis⟩ := h
  have inverse := compressedCompactDecodePrefix_inverse w hn hlo x p n n hp0 hpo
    (Nat.le_refl n) hn512 raw [] [] hraw
  have records := run_basis_records (compressedDecodePrefix w n) s
    (run (compressedEncodePrefix w n) [] raw) [] [] hbasis
  have bits : (run (compressedDecodePrefix w n) [] s).basis = raw.basis :=
    records.trans (congrArg State.basis inverse)
  refine ⟨run_no_measurement_phase _ (compressedDecodePrefix_measurements w n) s [],?_⟩
  rw [bits]
  exact hraw

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compressedCompactDecodePrefix_inverse
#print axioms ECDSAAdd.Arithmetic.compressedCompactStage_decoded
