import ECDSAAdd.Arithmetic.CompactSkywalkStageStepProof

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Actual forward compact ticks only; no high-word reconstruction or reverse
measurement instruction is inserted between physical compact boundaries. -/
def compactSkywalkForward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => compactSkywalkTick w i++compactSkywalkForward w (i+1) n

attribute [local irreducible] compactSkywalkTick

/-- Exact stage induction includes phase, raw history, future zero sites,
full clean carry, initial orientation, and both omitted physical tails. -/
theorem compactSkywalkForward_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hsteps : i+n ≤ 512) :
    Triple (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i)
      (compactSkywalkForward w i n)
      (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) (i+n)) := by
  induction n generalizing i with
  | zero =>
    intro s m hin
    exact ⟨rfl,hin⟩
  | succ n ih =>
    have first := compactSkywalkStageStep w hn x p i hp0 hx0 hpo hp hx hc (by omega)
    have rest := ih (i+1) (by omega)
    simpa only [compactSkywalkForward,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using first.seq rest

/-- The existing seed-stage input starts the full512 compact campaign directly. -/
theorem compactSkywalkForward_512 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) :
    Triple (SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0)
      (compactSkywalkForward w 0 512)
      (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512) := by
  intro s m hin
  exact compactSkywalkForward_spec w hn x p 0 512 hp0 hx0 hpo hp hx hc (by decide) s m
    ((compactSkywalkStage_zero_iff w _ s.basis).mpr hin)

/-- Pure arithmetic charge recurrences mirror actual per-tick resources. -/
def compactSkywalkForwardT (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1)+
      compactSkywalkForwardT (i+1) n

def compactSkywalkForwardM (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (compactSkywalkTickPostWidth i-1)+compactSkywalkForwardM (i+1) n

theorem compactSkywalkForward_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i n : Nat) (hsteps : i+n ≤ 512) :
    toffoliCount (compactSkywalkForward w i n) = compactSkywalkForwardT i n ∧
    measurementCount (compactSkywalkForward w i n) = compactSkywalkForwardM i n := by
  induction n generalizing i with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have first := compactSkywalkTick_counts w i (by omega) hn
    have rest := ih (i+1) (by omega)
    rw [compactSkywalkForward,toffoliCount_append,measurementCount_append,
      first.1,first.2,rest.1,rest.2]
    exact ⟨rfl,rfl⟩

private theorem fullCharges : compactSkywalkForwardT 0 512 = 197632 ∧
    compactSkywalkForwardM 0 512 = 98688 := by decide

/-- Full forward integer-leg cost, excluding seed, field replay and point glue. -/
theorem compactSkywalkForward_512_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (compactSkywalkForward w 0 512) = 197632 ∧
    measurementCount (compactSkywalkForward w 0 512) = 98688 := by
  have h := compactSkywalkForward_counts w hn 0 512 (by decide)
  rw [fullCharges.1,fullCharges.2] at h
  exact h

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkForward_spec
#print axioms ECDSAAdd.Arithmetic.compactSkywalkForward_512_counts
