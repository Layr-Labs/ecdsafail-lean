import ECDSAAdd.Arithmetic.CompactSkywalkForwardFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Expand only the tails removed at the previous local tick. Their lengths
are preN-postN (zero or one), not258-postN. -/
def compactSkywalkReverseExpand (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkSignExpand (compactSkywalkTickBRelease w i)++
    compactSkywalkSignExpand (compactSkywalkTickARelease w i)

/-- Fresh independently measured signed unrecord, then local half/route
reversal. No forward measurement instruction is reversed. -/
def compactSkywalkReverseTick (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkReverseExpand w i++
    narrowSkywalkUntick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)

attribute [local irreducible] narrowSkywalkTick narrowSkywalkUntick
attribute [local irreducible] compactSkywalkSignRelease compactSkywalkSignExpand

theorem compactSkywalkReverseExpand_counts (w : Nat → Wire) (i : Nat) :
    toffoliCount (compactSkywalkReverseExpand w i) = 0 ∧
    measurementCount (compactSkywalkReverseExpand w i) = 0 := by
  have a := compactSkywalkSignRelease_counts (compactSkywalkTickARelease w i)
  have b := compactSkywalkSignRelease_counts (compactSkywalkTickBRelease w i)
  rw [compactSkywalkReverseExpand,toffoliCount_append,measurementCount_append,
    b.2.2.1,b.2.2.2,a.2.2.1,a.2.2.2]
  exact ⟨rfl,rfl⟩

/-- Local-tail expansion exactly cancels actual compact cleanup, with
independent record lists and arbitrary initial data in both local tails. -/
theorem compactSkywalkReverseExpand_cleanup (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m1 m2 : List Bool) :
    run (compactSkywalkReverseExpand w i) m2
      (run (compactSkywalkTickCleanup w i) m1 s) = s := by
  let A := compactSkywalkTickARelease w i
  let B := compactSkywalkTickBRelease w i
  have hv := compactSkywalkTick_release_valid w i hi hn
  have ca := compactSkywalkSignRelease_counts A
  have cb := compactSkywalkSignRelease_counts B
  change run (compactSkywalkSignExpand B++compactSkywalkSignExpand A) m2
    (run (compactSkywalkSignRelease A++compactSkywalkSignRelease B) m1 s) = s
  rw [compactSkywalkSign_no_measure_append _ _ ca.2.1,
    compactSkywalkSign_no_measure_append _ _ cb.2.2.2]
  rw [(compactSkywalkSignRelease_roundtrip B hv.2
    (run (compactSkywalkSignRelease A) m1 s) m1 m2).1]
  exact (compactSkywalkSignRelease_roundtrip A hv.1 s m1 m2).1

/-- Exact complete State inverse of the actual compact tick. Only its fresh
history and clean local carry are needed; measurement lists are independent. -/
theorem compactSkywalkReverseTick_roundtrip (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m1 m2 : List Bool)
    (hh : s.basis (compactSkywalkTickLayout w i).history = false)
    (hc : regValue (compactSkywalkTickLayout w i).carry s.basis = 0) :
    run (compactSkywalkReverseTick w i) m2 (run (compactSkywalkTick w i) m1 s) = s := by
  have hz := (compactSkywalkReverseExpand_counts w i).2
  have hr := compactSkywalkTickOutput_run w i s m1
  rw [hr,compactSkywalkReverseTick,compactSkywalkSign_no_measure_append _ _ hz]
  rw [compactSkywalkReverseExpand_cleanup w i hi hn _ m1 m2]
  have width := compactSkywalkTick_width_bounds i hi
  exact narrowSkywalkTick_roundtrip _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1) s m1 m2 hh hc

theorem compactSkywalkReverseTick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (compactSkywalkReverseTick w i) =
      (compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1) ∧
    measurementCount (compactSkywalkReverseTick w i) = compactSkywalkTickPostWidth i-1 := by
  have width := compactSkywalkTick_width_bounds i hi
  have c := narrowSkywalkTick_counts _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1)
  have z := compactSkywalkReverseExpand_counts w i
  rw [compactSkywalkReverseTick,toffoliCount_append,measurementCount_append,
    z.1,z.2,c.2.2.1,c.2.2.2,compactSkywalkTick_ah w i hi,wireBlock_length]
  exact ⟨by omega,by omega⟩

theorem compactSkywalkReverseExpand_support (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    wires (compactSkywalkReverseExpand w i) ⊆ (compactSkywalkTickLayout w i).wires.toFinset := by
  have h := compactSkywalkTick_width_bounds i hi
  have a := (compactSkywalkSignWord_support (compactSkywalkTickLayout w i).half
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)).2
  have b := (compactSkywalkSignWord_support (compactSkywalkTickLayout w i).b
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_b w i hi,wireBlock_length]; exact h.2.2.1)).2
  intro q hq
  simp only [compactSkywalkReverseExpand,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have hb := List.mem_toFinset.mp (b hq)
    simp only [SkywalkIntegerLayout.b,SkywalkIntegerLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons] at hb ⊢
    tauto
  · have ha := List.mem_toFinset.mp (a hq)
    simp only [SkywalkIntegerLayout.half,SkywalkIntegerLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
    tauto

theorem compactSkywalkReverseTick_support (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    wires (compactSkywalkReverseTick w i) ⊆ (compactSkywalkTickLayout w i).wires.toFinset := by
  have h := compactSkywalkTick_width_bounds i hi
  have n := (narrowSkywalkTick_wires_subset _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)).2
  rw [compactSkywalkReverseTick,wires_append,Finset.union_subset_iff]
  exact ⟨compactSkywalkReverseExpand_support w i hi,n⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkReverseTick_roundtrip
#print axioms ECDSAAdd.Arithmetic.compactSkywalkReverseTick_counts
