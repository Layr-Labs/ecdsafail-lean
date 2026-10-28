import ECDSAAdd.Arithmetic.Paper935.WalkForwardInputs

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Select any actual forward prefix from the connected input invariant.
All returned state and allocator views are computed from that same prefix. -/
theorem walkForwardInputs_prefix (F : SlotRegisters) (tmin : Nat) (p x : Int)
    (m : List Bool) (index ordinal : Nat) (s : State) (A : Arena) (b : WindowBank)
    (record : List Wire) (slots : List HistoricalSlot)
    (h : WalkForwardInputs F tmin p x m index ordinal s A b record slots)
    (i : Nat) (hi : i<slots.length) :
    let pre := slots.take i
    let t := runWithTape (historicalWalkProgram F pre) m ordinal s
    (walkExitArena A pre).Ready t.basis ∧
    (walkExitBank b pre).Encodes t.basis (pinWalk tmin p x (index+i)).rows ∧
    F.Values t.basis (pinWalk tmin p x (index+i)) ∧
    regValue (walkExitRecord record pre) t.basis=trajectoryHistory tmin 7 p x (index+i) := by
  induction slots generalizing index ordinal s A b record i with
  | nil => simp at hi
  | cons Q rest ih =>
    cases i with
    | zero => simpa only [List.take_zero,historicalWalkProgram,List.flatMap_nil,runWithTape,
        walkExitArena,walkExitBank,walkExitRecord,Nat.add_zero] using h.1
    | succ i =>
      have bound : i<rest.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      have tail := ih (index+1) (ordinal+recordedMeasurementCount (Q.program F))
        (runWithTape (Q.program F) m ordinal s) Q.historyArena Q.slot.front.exitBank Q.history.record h.2 i bound
      have program : historicalWalkProgram F (Q::rest.take i)=Q.program F++historicalWalkProgram F (rest.take i) := rfl
      dsimp only
      simpa only [List.take_succ_cons,program,runWithTape_append,walkExitArena,walkExitBank,walkExitRecord,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tail

end ECDSAAdd.Arithmetic.Paper935
