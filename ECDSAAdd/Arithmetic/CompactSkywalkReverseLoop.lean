import ECDSAAdd.Arithmetic.CompactSkywalkReverseProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Walk back the actual compact ticks, with independent inverse measurements
and local sign expansion only at the immediately preceding width. -/
def compactSkywalkReverse (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compactSkywalkReverse w (i+1) n++compactSkywalkReverseTick w i

attribute [local irreducible] compactSkywalkTick compactSkywalkReverseTick

/-- Complete physical State restoration on every valid compact forward path.
No arbitrary-poststate reachability premise or reused measurement stream is assumed. -/
theorem compactSkywalkReverse_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hsteps : i+n ≤ 512)
    (s : State) (m1 m2 : List Bool)
    (hin : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (compactSkywalkReverse w i n) m2 (run (compactSkywalkForward w i n) m1 s) = s := by
  induction n generalizing i s m1 m2 with
  | zero => rfl
  | succ n ih =>
    have hi : i < 512 := by omega
    let tick := compactSkywalkTick w i
    simp only [compactSkywalkForward,compactSkywalkReverse]
    rw [run_append,run_append]
    generalize htick : run tick (m1.take (measurementCount tick)) s = t
    have hs := compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hx hc hi
      s (m1.take (measurementCount tick)) hin
    rw [htick] at hs
    have htail := ih (i+1) (by omega) t (m1.drop (measurementCount tick))
      (m2.take (measurementCount (compactSkywalkReverse w (i+1) n))) hs.2
    have localInput := compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hx hc hi s hin
    have restore := compactSkywalkReverseTick_roundtrip w i hi hn s
      (m1.take (measurementCount tick))
      (m2.drop (measurementCount (compactSkywalkReverse w (i+1) n)))
      localInput.2.2.2.2.1 localInput.2.2.2.2.2
    rw [htick] at restore
    rw [htail]
    exact restore

/-- The old canonical seed-stage input gives a full512-tick measured roundtrip. -/
theorem compactSkywalkReverse_512_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (s : State) (m1 m2 : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    run (compactSkywalkReverse w 0 512) m2 (run (compactSkywalkForward w 0 512) m1 s) = s :=
  compactSkywalkReverse_roundtrip w hn x p 0 512 hp0 hx0 hpo hp hx hc (by decide) s m1 m2
    ((compactSkywalkStage_zero_iff w _ s.basis).mpr hin)

theorem compactSkywalkReverse_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    toffoliCount (compactSkywalkReverse w i n) = compactSkywalkForwardT i n ∧
    measurementCount (compactSkywalkReverse w i n) = compactSkywalkForwardM i n := by
  induction n generalizing i with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have first := compactSkywalkReverseTick_counts w i (by omega) hn
    have rest := ih (i+1) (by omega)
    rw [compactSkywalkReverse,toffoliCount_append,measurementCount_append,
      first.1,first.2,rest.1,rest.2]
    change compactSkywalkForwardT (i+1) n+
      ((compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1)) =
        (compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1)+
          compactSkywalkForwardT (i+1) n ∧
      compactSkywalkForwardM (i+1) n+(compactSkywalkTickPostWidth i-1) =
        (compactSkywalkTickPostWidth i-1)+compactSkywalkForwardM (i+1) n
    exact ⟨Nat.add_comm _ _,Nat.add_comm _ _⟩

theorem compactSkywalkReverse_512_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (compactSkywalkReverse w 0 512) = 197632 ∧
    measurementCount (compactSkywalkReverse w 0 512) = 98688 := by
  have r := compactSkywalkReverse_counts w hn 0 512 (by decide)
  have f := compactSkywalkForward_counts w hn 0 512 (by decide)
  have exactCounts := compactSkywalkForward_512_counts w hn
  exact ⟨r.1.trans (f.1.symm.trans exactCounts.1),r.2.trans (f.2.symm.trans exactCounts.2)⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkReverse_roundtrip
#print axioms ECDSAAdd.Arithmetic.compactSkywalkReverse_512_counts
