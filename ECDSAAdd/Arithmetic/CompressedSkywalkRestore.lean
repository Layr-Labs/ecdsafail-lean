import ECDSAAdd.Arithmetic.CompressedSkywalkForward
import ECDSAAdd.Arithmetic.CompressedSkywalkReverse

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

attribute [local irreducible] run compressedDecodePrefix compressedEncodePrefix
attribute [local irreducible] compressedSkywalkUnloop narrowSkywalkRoutedUnloop

theorem run_no_measurement_phase (p : Program) (hm : measurementCount p=0)
    (s : State) (m : List Bool) : (run p m s).phase=s.phase := by
  induction p generalizing s m with
  | nil => simp only [run]
  | cons i p ih =>
    cases i with
    | X q =>
      simp only [run]
      exact ih hm ⟨s.phase,writeBit s.basis q (!s.basis q)⟩ m
    | CX a q =>
      simp only [run]
      exact ih hm ⟨s.phase,writeBit s.basis q (s.basis q ^^ s.basis a)⟩ m
    | CCX a b q =>
      simp only [run]
      exact ih hm ⟨s.phase,writeBit s.basis q (s.basis q ^^ (s.basis a && s.basis b))⟩ m
    | measureX q c0 c1 =>
      simp only [measurementCount] at hm
      omega

/-- Decoding the model recovers the full raw caller basis, including any
outside coordinate update. The decoder itself preserves incoming phase. -/
theorem compressedIntegerStage_decoded (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p n : Nat) (hp0 : 0 < p) (hpo : p%2=1) (hn512 : n ≤ 512)
    (s : State) (h : CompressedIntegerStage w x p n s.basis) :
    (run (compressedDecodePrefix w n) [] s).phase=s.phase ∧
    SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) n
      (run (compressedDecodePrefix w n) [] s).basis := by
  obtain ⟨raw,hraw,hbasis⟩ := h
  have hi := compressedDecodePrefix_inverse w hn hlo x p n n hp0 hpo
    (Nat.le_refl n) hn512 raw [] [] hraw
  have hb := run_basis_records (compressedDecodePrefix w n) s
    (run (compressedEncodePrefix w n) [] raw) [] [] hbasis
  have he : (run (compressedDecodePrefix w n) [] s).basis=raw.basis :=
    hb.trans (congrArg State.basis hi)
  refine ⟨run_no_measurement_phase _ (compressedDecodePrefix_measurements w n) s [],?_⟩
  rw [he]
  exact hraw

/-- Full 512-step reverse restoration after an external numerator update.
All integer-pool sites return to the initial seed; the current phase is kept. -/
theorem compressedSkywalkUnloop_restore_pool (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (hfinal : CompressedIntegerStage w x p 512 s.basis) :
    (run (compressedSkywalkUnloop w 0 512) m s).phase=s.phase ∧
    ∀ q∈skywalkPoolWires w,(run (compressedSkywalkUnloop w 0 512) m s).basis q=initial.basis q := by
  have hd := compressedIntegerStage_decoded w hn hlo x p 512 hp0 hpo (Nat.le_refl _) s hfinal
  have hr := narrowSkywalkRoutedUnloop_restore_pool w hn x p hp0 hx0 hpo hp hx hc
    initial (run (compressedDecodePrefix w 512) [] s) m hinit hd.2
  rw [compressedSkywalkUnloop_normalize w hn hlo 0 512 (by omega),compressedDecodeRange_zero,run_append,
    compressedDecodePrefix_measurements]
  simp only [List.take_zero,List.drop_zero]
  exact ⟨hr.1.trans hd.1,hr.2⟩

end ECDSAAdd.Arithmetic
