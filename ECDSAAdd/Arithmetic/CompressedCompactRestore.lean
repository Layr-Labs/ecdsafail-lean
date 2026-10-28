import ECDSAAdd.Arithmetic.CompressedCompactDecode
import ECDSAAdd.Arithmetic.CompactSkywalkStageTerminal
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run compactSkywalkForward compactSkywalkReverse compressedCompactReverse

private theorem decode_support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (i : Nat) (hi : i < 512) :
    wires (compressedDecodeBefore w i) ⊆ (skywalkPoolWires w).toFinset := by
  intro q hq
  cases due : compressedPackDue i
  · simp [compressedDecodeBefore,due,wires] at hq
  · have h3 := compressedPackDue_true i due
    have hq' : q ∈ wires (compressedHistoryDecode w (i-3)) := by
      simpa only [compressedDecodeBefore,due,if_true] using hq
    obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo (i-3) (by omega) _ (Or.inr rfl) q hq'
    have bound := compressedHistoryId_bound (i-3) (by omega) j
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨compressedHistoryId (i-3) j,by omega,rfl⟩

theorem compressedCompactReverse_support (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    wires (compressedCompactReverse w i n) ⊆ (skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [compressedCompactReverse,wires]
  | succ n ih =>
    have tick : wires (compactSkywalkReverseTick w i) ⊆ (skywalkPoolWires w).toFinset := by
      intro q hq
      exact List.mem_toFinset.mpr (compactSkywalkTick_local_support w i (by omega)
        (List.mem_toFinset.mp (compactSkywalkReverseTick_support w i (by omega) hn hq)))
    simp only [compressedCompactReverse,wires_append,Finset.union_subset_iff]
    exact ⟨⟨ih (i+1) (by omega),decode_support w hn hlo i (by omega)⟩,tick⟩

theorem compressedCompactReverse_frame (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hsteps : i+n ≤ 512) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ skywalkPoolWires w) :
    (run (compressedCompactReverse w i n) m s).basis q = s.basis q := by
  apply run_preserves_outside
  intro h
  exact hq (List.mem_toFinset.mp (compressedCompactReverse_support w hn hlo i n hsteps h))

/-- The terminal compact predicate determines the physical integer pool.
The reference emitter and its inverse here are both genuinely compact. -/
private theorem terminal_restore (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (hfinal : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s.basis) :
    (run (compactSkywalkReverse w 0 512) m s).phase = s.phase ∧
    ∀ q ∈ skywalkPoolWires w,(run (compactSkywalkReverse w 0 512) m s).basis q = initial.basis q := by
  let start : State := ⟨s.phase,initial.basis⟩
  have forward := compactSkywalkForward_512 w hn x p hp0 hx0 hpo hp hx hc start [] hinit
  have own := (compactSkywalkStage_terminal w hn x p hp0 hx0 hpo hp hx hc s.basis hfinal).2
  have reference := (compactSkywalkStage_terminal w hn x p hp0 hx0 hpo hp hx hc _ forward.2).2
  have inverse := compactSkywalkReverse_512_roundtrip w hn x p hp0 hx0 hpo hp hx hc start [] m hinit
  have bits : ∀ q ∈ (skywalkPoolWires w).toFinset,
      s.basis q = (run (compactSkywalkForward w 0 512) [] start).basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w _ 512 (by decide) _ _ own reference q (List.mem_toFinset.mp hq)
  have agrees := pool_run_agrees (compactSkywalkReverse w 0 512) (skywalkPoolWires w).toFinset
    (compactSkywalkReverse_support w hn 0 512 (by decide)) m s
    (run (compactSkywalkForward w 0 512) [] start) forward.1.symm bits
  rw [inverse] at agrees
  refine ⟨agrees.1,?_⟩
  intro q hq
  exact agrees.2 q (List.mem_toFinset.mpr hq)

/-- Complete512 compact-plus-codec restoration from the encoded terminal
pool. Outsiders may already contain arbitrary coexisting field updates. -/
theorem compressedCompactReverse_restore_pool (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (initial s : State) (m : List Bool)
    (hinit : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (hfinal : CompressedCompactStage w x p 512 s.basis) :
    (run (compressedCompactReverse w 0 512) m s).phase = s.phase ∧
    ∀ q ∈ skywalkPoolWires w,(run (compressedCompactReverse w 0 512) m s).basis q = initial.basis q := by
  have decoded := compressedCompactStage_decoded w hn hlo x p 512 hp0 hpo (by decide) s hfinal
  have restored := terminal_restore w hn x p hp0 hx0 hpo hp hx hc
    initial (run (compressedDecodePrefix w 512) [] s) m hinit decoded.2
  rw [compressedCompactReverse_normalize w hn hlo 0 512 (by decide),compressedDecodeRange_zero,
    run_append,compressedDecodePrefix_measurements]
  simp only [List.take_zero,List.drop_zero]
  exact ⟨restored.1.trans decoded.1,restored.2⟩

/-- Forward and inverse records are independent, and the full physical
caller State returns, including arbitrary incoming phase and every outsider. -/
theorem compressedCompactReverse_512_roundtrip (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (s : State) (mForward mReverse : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    run (compressedCompactReverse w 0 512) mReverse
      (run (compressedCompactForward w 0 512) mForward s) = s := by
  have forward := compressedCompactForward_512_spec w hn hlo x p hp0 hx0 hpo hp hx hc s mForward hin
  have reverse := compressedCompactReverse_restore_pool w hn hlo x p hp0 hx0 hpo hp hx hc
    s (run (compressedCompactForward w 0 512) mForward s) mReverse hin forward.2
  apply State.extensionality
  · exact reverse.1.trans forward.1
  · funext q
    by_cases hq : q ∈ skywalkPoolWires w
    · exact reverse.2 q hq
    · exact (compressedCompactReverse_frame w hn hlo 0 512 (by decide) _ mReverse q hq).trans
        (compressedCompactForward_frame w hn hlo 0 512 (by decide) s mForward q hq)

/-- A field operation need only retain the actual encoded integer pool and
phase. The emitted compact reverse restores it and keeps all field outsiders. -/
theorem compressedCompactReverse_restore_after_outside (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (s field : State) (mForward mReverse : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis)
    (hphase : field.phase = (run (compressedCompactForward w 0 512) mForward s).phase)
    (hpool : ∀ q ∈ skywalkPoolWires w,
      field.basis q = (run (compressedCompactForward w 0 512) mForward s).basis q) :
    (run (compressedCompactReverse w 0 512) mReverse field).phase = s.phase ∧
    (∀ q ∈ skywalkPoolWires w,(run (compressedCompactReverse w 0 512) mReverse field).basis q = s.basis q) ∧
    (∀ q,q ∉ skywalkPoolWires w → (run (compressedCompactReverse w 0 512) mReverse field).basis q = field.basis q) := by
  have inverse := compressedCompactReverse_512_roundtrip w hn hlo x p hp0 hx0 hpo hp hx hc s mForward mReverse hin
  have agrees := pool_run_agrees (compressedCompactReverse w 0 512) (skywalkPoolWires w).toFinset
    (compressedCompactReverse_support w hn hlo 0 512 (by decide)) mReverse field
    (run (compressedCompactForward w 0 512) mForward s) hphase
    (fun q hq => hpool q (List.mem_toFinset.mp hq))
  rw [inverse] at agrees
  refine ⟨agrees.1,?_,?_⟩
  · intro q hq; exact agrees.2 q (List.mem_toFinset.mpr hq)
  · intro q hq; exact compressedCompactReverse_frame w hn hlo 0 512 (by decide) field mReverse q hq

/-- Actual reverse component prices; no whole-point allocation claim. -/
theorem compressedCompactReverse_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    toffoliCount (compressedCompactReverse w i n) = compactSkywalkForwardT i n+4*compressedPackCount i n ∧
    measurementCount (compressedCompactReverse w i n) = compactSkywalkForwardM i n := by
  have relative := compressedCompactReverse_counts_relative w i n
  have compact := compactSkywalkReverse_counts w hn i n hsteps
  rw [compact.1,compact.2] at relative
  exact relative

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compressedCompactReverse_support
#print axioms ECDSAAdd.Arithmetic.compressedCompactReverse_restore_pool
#print axioms ECDSAAdd.Arithmetic.compressedCompactReverse_512_roundtrip
#print axioms ECDSAAdd.Arithmetic.compressedCompactReverse_restore_after_outside
#print axioms ECDSAAdd.Arithmetic.compressedCompactReverse_counts
