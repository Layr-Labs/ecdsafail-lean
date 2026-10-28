import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotCompiler
import ECDSAAdd.Arithmetic.Paper935.TrajectoryMass

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- Length before stage `t`; growth requests never shrink a retained record. -/
def historyLength (initial : Nat) (request : Nat → Nat) : Nat → Nat
  | 0 => initial
  | t+1 => max (request t) (historyLength initial request t)

/-- The failure event uses the length AFTER growth at the indexed stage. -/
def historyCapacity (initial : Nat) (request : Nat → Nat) (t : Nat) : Nat :=
  historyLength initial request (t+1)

/-- A compiled sequence with the actual growth equation has this unique length
schedule. The equation is required only on its successfully compiled prefix. -/
theorem historyLength_eq (initial steps : Nat) (request lengths : Nat → Nat)
    (seed : lengths 0=initial)
    (grow : ∀ t,t<steps → lengths (t+1)=max (request t) (lengths t)) :
    ∀ t,t≤steps → lengths t=historyLength initial request t := by
  intro t
  induction t with
  | zero => intro _; exact seed
  | succ t ih =>
    intro ht
    rw [grow t (by omega),historyLength,ih (by omega)]

/-- Increasing actual capacity can only remove history overflow events. -/
theorem HistoryFailure.capacity_mono (tmin depth steps : Nat) (small large : Nat → Nat)
    (h : ∀ t,t<steps → small t≤large t) (p x : Int) :
    HistoryFailure tmin depth steps large p x → HistoryFailure tmin depth steps small p x := by
  rintro ⟨t,ht,hs,hbad⟩
  refine ⟨t,ht,hs,fun hfit => hbad (lt_of_lt_of_le hfit ?_)⟩
  exact Nat.pow_le_pow_right (by decide) (h t ht)

/-- Requests alone give a conservative event, even when requests decrease. -/
theorem historyCapacity_failure_subset (initial tmin depth steps : Nat) (request : Nat → Nat)
    (p x : Int) :
    HistoryFailure tmin depth steps (historyCapacity initial request) p x →
      HistoryFailure tmin depth steps request p x := by
  exact HistoryFailure.capacity_mono tmin depth steps request (historyCapacity initial request)
    (fun _ _ => Nat.le_max_left _ _) p x

/-- Existing four-category accounting transports a conservative capacity bound
without changing the original input law or assuming independent calls. -/
theorem trajectory_mass_capacity_mono {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (tmin depth steps width : Nat)
    (small large : Nat → Nat) (exits : List RowWindow) (μ : InputLaw X)
    (h : ∀ t,t<steps → small t≤large t) :
    μ.mass (trajectoryEvents input p tmin depth steps width large exits).bad ≤
      μ.mass (trajectoryEvents input p tmin depth steps width small exits).bad := by
  apply μ.mass_mono
  intro x hx
  rw [mem_trajectory_bad] at hx ⊢
  rcases hx with hc | hh | hd | hw
  · exact Or.inl hc
  · exact Or.inr (Or.inl (HistoryFailure.capacity_mono tmin depth steps small large h p (input x) hh))
  · exact Or.inr (Or.inr (Or.inl hd))
  · exact Or.inr (Or.inr (Or.inr hw))

/-- The precise symbolic four-event budget for the actual retained-capacity
schedule. This is an exact expression, not a numerical upper-bound claim. -/
theorem historyBudget_total {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (tmin steps width initial : Nat)
    (request : Nat → Nat) (exits : List RowWindow) (μ : InputLaw X) :
    (trajectoryBounds input p tmin 7 steps width (historyCapacity initial request) exits μ).total =
      μ.mass (trajectoryEvents input p tmin 7 steps width (historyCapacity initial request) exits).bad := by
  exact trajectoryBounds_total input p tmin 7 steps width (historyCapacity initial request) exits μ

/-- Outside the existing union, the history obligation uses actual accumulated
capacity; no fifth failure category is introduced by this adapter. -/
theorem historyBudget_good {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (tmin steps width initial : Nat)
    (request : Nat → Nat) (exits : List RowWindow) (x : X)
    (h : x∉(trajectoryEvents input p tmin 7 steps width (historyCapacity initial request) exits).bad) :
    ¬HistoryFailure tmin 7 steps (historyCapacity initial request) p (input x) := by
  intro hh
  exact h ((mem_trajectory_bad input p tmin 7 steps width (historyCapacity initial request) exits x).mpr
    (Or.inr (Or.inl hh)))

/-- Actual slot selector and depth binding discharge the abstract selector
obligation of the growing-history bridge. Record contents still require the
inductive execution invariant; a capacity equation alone cannot prove them. -/
theorem compileHistoricalSlot_trajectory_fit
    (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset request : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset request=some Q)
    (s : BasisState) (ready : Q.slot.front.exitArena.Ready s)
    (hn : record.Nodup) (owned : record.toFinset⊆Q.slot.front.exitArena.live)
    (tmin steps initial : Nat) (requests : Nat → Nat) (p x : Int) (t : Nat) (ht : t<steps)
    (values : F.OutputValues s (pinWalk tmin p x t) (pinWalk tmin p x (t+1)))
    (rows : Q.slot.front.exitBank.Encodes s (pinWalk tmin p x (t+1)).rows)
    (inv : Inv p (pinWalk tmin p x (t+1)).rows)
    (good : ¬HistoryFailure tmin 7 steps (historyCapacity initial requests) p x)
    (request_eq : request=requests t)
    (length_eq : record.length=historyLength initial requests t)
    (oldOdd : (pinWalk tmin p x t).rows.f%2=1)
    (history : regValue record s=trajectoryHistory tmin 7 p x t) :
    Q.history.selected s=true →
      2*regValue Q.history.record s+(s Q.history.port).toNat<2^Q.history.record.length := by
  have hc := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset request Q h
  have selector := compileHistoricalSlot_selector A b record addWidth exitWidth F armed probeWidth offset request Q h
    (pinWalk tmin p x t) (pinWalk tmin p x (t+1)) s values rows p inv
  have depth : (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6).length+1=7 := by
    rw [hc.2.2.2.1]
  apply compileGrowingHistory_fit Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork request F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2 hn owned s ready
    tmin steps (historyCapacity initial requests) p x t ht
  · simpa only [depth] using good
  · simp only [historyCapacity,historyLength,request_eq,length_eq]
  · simpa only [depth,trajectoryStore] using selector
  · have grow := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record
      Q.detectorWork request F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
      F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2
    have ids := compileHistory_identity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
      F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history.record Q.detectorWork Q.history grow.2.2
    rw [ids.2.2.2.2.2,values.parity]
    unfold bbit parityControl
    split_ifs with swap
    · rw [oldOdd,swap.2]
    · rfl
  · simpa only [depth] using history

end ECDSAAdd.Arithmetic.Paper935
