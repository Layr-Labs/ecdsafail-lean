import ECDSAAdd.Arithmetic.CompressedCompactRestore

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run compactSkywalkForward compactSkywalkReverse
  compressedCompactReverse compressedDecodeRange compressedDecodePrefix

/-- The unchanged 511-tick reverse restores the exact first-tick pool.
Field data outside that pool may already have changed. -/
private theorem raw_tail_restore (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x prime : Nat) (hp0 : 0<prime) (hx0 : 0<x) (hpo : prime%2=1)
    (hp : prime<2^256) (hx : x<prime) (hc : x.Coprime prime)
    (initial s : State) (m : List Bool)
    (hinit : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (prime:Int)) 1 initial.basis)
    (hfinal : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (prime:Int)) 512 s.basis) :
    (run (compactSkywalkReverse w 1 511) m s).phase=s.phase ∧
    ∀q∈skywalkPoolWires w,(run (compactSkywalkReverse w 1 511) m s).basis q=initial.basis q := by
  let start : State := ⟨s.phase,initial.basis⟩
  have f := compactSkywalkForward_spec w hn x prime 1 511 hp0 hx0 hpo hp hx hc
    (by omega) start [] hinit
  have own := (compactSkywalkStage_terminal w hn x prime hp0 hx0 hpo hp hx hc s.basis hfinal).2
  have reference := (compactSkywalkStage_terminal w hn x prime hp0 hx0 hpo hp hx hc _ f.2).2
  have inverse := compactSkywalkReverse_roundtrip w hn x prime 1 511 hp0 hx0 hpo hp hx hc
    (by omega) start [] m hinit
  have bits : ∀q∈(skywalkPoolWires w).toFinset,
      s.basis q=(run (compactSkywalkForward w 1 511) [] start).basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w _ 512 (by omega) _ _ own reference q (List.mem_toFinset.mp hq)
  have agrees := pool_run_agrees (compactSkywalkReverse w 1 511) (skywalkPoolWires w).toFinset
    (compactSkywalkReverse_support w hn 1 511 (by omega)) m s
    (run (compactSkywalkForward w 1 511) [] start) f.1.symm bits
  rw [inverse] at agrees
  refine ⟨agrees.1,?_⟩
  intro q hq
  exact agrees.2 q (List.mem_toFinset.mpr hq)

private theorem decode_zero_step (w : Nat → Wire) (n : Nat) :
    compressedDecodeRange w 0 (n+1)=compressedDecodeRange w 1 n ++ compressedDecodeBefore w 0 := by
  rw [compressedDecodeRange]

private theorem tail_decoder (w : Nat → Wire) :
    compressedDecodeRange w 1 511=compressedDecodePrefix w 512 := by
  have h := compressedDecodeRange_zero w 512
  have zero : compressedDecodeBefore w 0=[] := rfl
  rw [decode_zero_step w 511,zero,List.append_nil] at h
  exact h

theorem tail_restore_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (x prime : Nat)
    (hp0 : 0<prime) (hx0 : 0<x) (hpo : prime%2=1)
    (hp : prime<2^256) (hx : x<prime) (hc : x.Coprime prime)
    (initial s : State) (m : List Bool)
    (hinit : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (prime:Int)) 1 initial.basis)
    (hfinal : CompressedCompactStage w x prime 512 s.basis) :
    (run (compressedCompactReverse w 1 511) m s).phase=s.phase ∧
    (∀q∈skywalkPoolWires w,(run (compressedCompactReverse w 1 511) m s).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w → (run (compressedCompactReverse w 1 511) m s).basis q=s.basis q) := by
  have decoded := compressedCompactStage_decoded w hn hlo x prime 512 hp0 hpo (by omega) s hfinal
  have restored := raw_tail_restore w hn x prime hp0 hx0 hpo hp hx hc
    initial (run (compressedDecodePrefix w 512) [] s) m hinit decoded.2
  have actual : run (compressedCompactReverse w 1 511) m s=
      run (compactSkywalkReverse w 1 511) m (run (compressedDecodePrefix w 512) [] s) := by
    rw [compressedCompactReverse_normalize w hn hlo 1 511 (by omega),tail_decoder,
      run_append,compressedDecodePrefix_measurements,List.take_zero,List.drop_zero]
  refine ⟨?_,?_,?_⟩
  · rw [actual]; exact restored.1.trans decoded.1
  · rw [actual]; exact restored.2
  · intro q hq
    exact compressedCompactReverse_frame w hn hlo 1 511 (by omega) s m q hq

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.tail_restore_pool
