import ECDSAAdd.Arithmetic.CompactSkywalkForward

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] compactSkywalkTick

/-- Every actual forward tick remains inside the original integer pool.
This support ceiling is not a compact whole-point allocation certificate. -/
theorem compactSkywalkForward_support (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    wires (compactSkywalkForward w i n) ⊆ (skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [compactSkywalkForward,wires]
  | succ n ih =>
    have hi : i < 512 := by omega
    have ht := compactSkywalkTick_support w i hi hn
    have hl := compactSkywalkTick_local_support w i hi
    have first : wires (compactSkywalkTick w i) ⊆ (skywalkPoolWires w).toFinset := by
      intro q hq
      exact List.mem_toFinset.mpr (hl (List.mem_toFinset.mp (ht hq)))
    rw [compactSkywalkForward,wires_append,Finset.union_subset_iff]
    exact ⟨first,ih (i+1) (by omega)⟩

/-- All caller wires outside the integer pool are preserved for arbitrary
input basis/phase and arbitrary complete measurement streams. -/
theorem compactSkywalkForward_frame (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) (s : State) (m : List Bool) (q : Wire)
    (hq : q ∉ skywalkPoolWires w) :
    (run (compactSkywalkForward w i n) m s).basis q = s.basis q :=
  run_preserves_outside _ m s q (fun h => hq
    (List.mem_toFinset.mp (compactSkywalkForward_support w hn i n hsteps h)))

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkForward_support
#print axioms ECDSAAdd.Arithmetic.compactSkywalkForward_frame
