import ECDSAAdd.Arithmetic.CompressedCompactStage
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run compactSkywalkTick compressedHistoryEncode compressedCompactForward

/-- The existing seed assertion starts the exact512 compact-plus-codec
campaign, with no changed divisor or shortened integer transcript. -/
theorem compressedCompactForward_512_spec (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) :
    Triple (SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0)
      (compressedCompactForward w 0 512) (CompressedCompactStage w x p 512) := by
  intro s m h
  have compact := (compactSkywalkStage_zero_iff w _ s.basis).mpr h
  exact CompressedCompactStage_spec w hn hlo x p 0 512 hp0 hx0 hpo hp hx hc (by decide)
    s m (compressedCompactStage_zero w x p s compact)

private theorem pack_support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (i : Nat) (hi : i < 512) :
    wires (compressedPackAfter w i) ⊆ (skywalkPoolWires w).toFinset := by
  intro q hq
  cases due : compressedPackDue i
  · simp [compressedPackAfter,due,wires] at hq
  · have h3 := compressedPackDue_true i due
    have hq' : q ∈ wires (compressedHistoryEncode w (i-3)) := by
      simpa only [compressedPackAfter,due,if_true] using hq
    obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo (i-3) (by omega) _ (Or.inl rfl) q hq'
    have bound := compressedHistoryId_bound (i-3) (by omega) j
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨compressedHistoryId (i-3) j,by omega,rfl⟩

/-- Actual instruction support includes compact sign release and all
measurement corrections of the history encoder. -/
theorem compressedCompactForward_support (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hi : i+n ≤ 512) :
    wires (compressedCompactForward w i n) ⊆ (skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,wires]
  | succ n ih =>
    have first : wires (compactSkywalkTick w i) ⊆ (skywalkPoolWires w).toFinset := by
      intro q hq
      exact List.mem_toFinset.mpr (compactSkywalkTick_local_support w i (by omega)
        (List.mem_toFinset.mp (compactSkywalkTick_support w i (by omega) hn hq)))
    have pack := pack_support w hn hlo i (by omega)
    simp only [compressedCompactForward,wires_append,Finset.union_subset_iff]
    exact ⟨⟨first,pack⟩,ih (i+1) (by omega)⟩

/-- Every caller bit outside the original integer pool restores, for all
input states and independent measurement records. -/
theorem compressedCompactForward_frame (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (i n : Nat) (hi : i+n ≤ 512) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ skywalkPoolWires w) :
    (run (compressedCompactForward w i n) m s).basis q = s.basis q := by
  apply run_preserves_outside
  intro h
  exact hq (List.mem_toFinset.mp (compressedCompactForward_support w hn hlo i n hi h))

/-- Component resource recurrence for this actual emission. It is not a
whole-point qubit or stage resource claim. -/
theorem compressedCompactForward_counts (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (i n : Nat) (hi : i+n ≤ 512) :
    toffoliCount (compressedCompactForward w i n) = compactSkywalkForwardT i n+3*compressedPackCount i n ∧
    measurementCount (compressedCompactForward w i n) = compactSkywalkForwardM i n+compressedPackCount i n := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,compactSkywalkForwardT,compactSkywalkForwardM,
      compressedPackCount,toffoliCount,measurementCount]
  | succ n ih =>
    have tick := compactSkywalkTick_counts w i (by omega) hn
    have pack := compressedPackAfter_counts w i
    have tail := ih (i+1) (by omega)
    simp only [compressedCompactForward,toffoliCount_append,measurementCount_append,
      tick.1,tick.2,pack.1,pack.2.1,tail.1,tail.2,compactSkywalkForwardT,
      compactSkywalkForwardM,compressedPackCount]
    constructor <;> omega

#print axioms ECDSAAdd.Arithmetic.compressedCompactForward_512_spec
#print axioms ECDSAAdd.Arithmetic.compressedCompactForward_support
#print axioms ECDSAAdd.Arithmetic.compressedCompactForward_frame
#print axioms ECDSAAdd.Arithmetic.compressedCompactForward_counts
end ECDSAAdd.Arithmetic
