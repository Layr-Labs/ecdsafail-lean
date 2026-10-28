import ECDSAAdd.Arithmetic.CompactSkywalkStageStepGeometry

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Both next full-word tails are clean: the native local tail is cleared by
actual CX, the previously omitted suffix is a frame, and A's new last site is fresh. -/
theorem compactSkywalkStageStep_clean_tails (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (r : SkywalkRails.State) (s : State) (m : List Bool)
    (hin : CompactSkywalkStageFields w r i s.basis) (A B : Int) (G : Bool)
    (hout : CompactSkywalkTickOutput w i A B G (run (compactSkywalkTick w i) m s).basis) :
    (compactSkywalkSignPoolA w (i+1)).Clean (run (compactSkywalkTick w i) m s).basis ∧
    (compactSkywalkSignPoolB w (i+1)).Clean (run (compactSkywalkTick w i) m s).basis := by
  rcases hin with ⟨ha,hb,hprev,hpast,hfuture,hcarry,horient,oldA,oldB⟩
  have width := compactSkywalkTick_width_bounds i hi
  have tv := compactSkywalkStageStep_tail_views w i hi
  have nowA := hout.2.2.2.2.2.2.1
  have nowB := hout.2.2.2.2.2.2.2
  have keepA (j : Nat) (hj0 : i+compactSkywalkTickPreWidth i+1 ≤ j) (hj1 : j ≤ i+258) :
      (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) := by
    have hp : j ≠ skywalkPoolPreviousId i := by
      unfold skywalkPoolPreviousId; split_ifs <;> omega
    exact compactSkywalkStage_tick_keep w i hi hn j (by omega) hp
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) s m
  have keepB (j : Nat) (hj0 : 770+compactSkywalkTickPreWidth i ≤ j) (hj1 : j < 1028) :
      (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) := by
    have hp : j ≠ skywalkPoolPreviousId i := by
      unfold skywalkPoolPreviousId; split_ifs <;> omega
    exact compactSkywalkStage_tick_keep w i hi hn j (by omega) hp
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) s m
  constructor
  · intro q hq
    rw [tv.2.2.1] at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    by_cases current : j < i+1+compactSkywalkTickPreWidth i
    · apply nowA
      rw [tv.1]
      apply List.mem_map.mpr
      exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩
    · rw [keepA j (by omega) (by omega)]
      by_cases last : j = i+258
      · subst j
        exact (hfuture i (Nat.le_refl i) hi).1
      · apply oldA
        rw [tv.2.2.2.2.1]
        apply List.mem_map.mpr
        exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩
  · intro q hq
    rw [tv.2.2.2.1] at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    by_cases current : j < 770+compactSkywalkTickPreWidth i
    · apply nowB
      rw [tv.2.1]
      apply List.mem_map.mpr
      exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩
    · rw [keepB j (by omega) (by omega)]
      apply oldB
      rw [tv.2.2.2.2.2]
      apply List.mem_map.mpr
      exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageStep_clean_tails
