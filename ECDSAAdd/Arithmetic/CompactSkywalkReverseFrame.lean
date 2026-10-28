import ECDSAAdd.Arithmetic.CompactSkywalkReverseLoop

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] compactSkywalkReverseTick

/-- Independently emitted reverse instructions touch only the integer pool. -/
theorem compactSkywalkReverse_support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    wires (compactSkywalkReverse w i n) ⊆ (skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [compactSkywalkReverse,wires]
  | succ n ih =>
    have hi : i < 512 := by omega
    have hs := compactSkywalkReverseTick_support w i hi hn
    have hl := compactSkywalkTick_local_support w i hi
    have tick : wires (compactSkywalkReverseTick w i) ⊆ (skywalkPoolWires w).toFinset := by
      intro q hq
      exact List.mem_toFinset.mpr (hl (List.mem_toFinset.mp (hs hq)))
    rw [compactSkywalkReverse,wires_append,Finset.union_subset_iff]
    exact ⟨ih (i+1) (by omega),tick⟩

theorem compactSkywalkReverse_frame (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ skywalkPoolWires w) :
    (run (compactSkywalkReverse w i n) m s).basis q = s.basis q :=
  run_preserves_outside _ m s q (fun h => hq
    (List.mem_toFinset.mp (compactSkywalkReverse_support w hn i n hsteps h)))

/-- A coexisting field operation may change every outsider while retaining
integer-pool bits and phase. Actual reverse then restores the original pool,
preserves the field's outsider values, and restores incoming phase. -/
theorem compactSkywalkReverse_restore_after_outside (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p i n : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (hsteps : i+n ≤ 512)
    (s field : State) (mForward mReverse : List Bool)
    (hin : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis)
    (hphase : field.phase = (run (compactSkywalkForward w i n) mForward s).phase)
    (hpool : ∀q ∈ skywalkPoolWires w,
      field.basis q = (run (compactSkywalkForward w i n) mForward s).basis q) :
    (run (compactSkywalkReverse w i n) mReverse field).phase = s.phase ∧
    (∀q ∈ skywalkPoolWires w,
      (run (compactSkywalkReverse w i n) mReverse field).basis q = s.basis q) ∧
    (∀q,q ∉ skywalkPoolWires w →
      (run (compactSkywalkReverse w i n) mReverse field).basis q = field.basis q) := by
  have inverse := compactSkywalkReverse_roundtrip w hn x p i n hp0 hx0 hpo hp hx hc
    hsteps s mForward mReverse hin
  have agrees := pool_run_agrees (compactSkywalkReverse w i n) (skywalkPoolWires w).toFinset
    (compactSkywalkReverse_support w hn i n hsteps) mReverse field
    (run (compactSkywalkForward w i n) mForward s) hphase
    (fun q hq => hpool q (List.mem_toFinset.mp hq))
  rw [inverse] at agrees
  refine ⟨agrees.1,?_,?_⟩
  · intro q hq
    exact agrees.2 q (List.mem_toFinset.mpr hq)
  · intro q hq
    exact compactSkywalkReverse_frame w hn i n hsteps field mReverse q hq

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkReverse_support
#print axioms ECDSAAdd.Arithmetic.compactSkywalkReverse_restore_after_outside
