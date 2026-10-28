import ECDSAAdd.Arithmetic.CompactSkywalkStageFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Past G records strictly before the predecessor site lie outside the
actual native and cleanup instruction support. -/
theorem compactSkywalkStageMetadata_pastG (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj : j+1 < i)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : j ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn j (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

theorem compactSkywalkStageMetadata_pastS (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj : j < i)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w (1028+j)) = s.basis (w (1028+j)) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : 1028+j ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn (1028+j) (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

/-- Future extensions of the original full-width words remain untouched;
the compact physical A prefix ends no later than site 514. -/
theorem compactSkywalkStageMetadata_futureExtension (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj0 : i+1 ≤ j) (hj : j < 512)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w (j+258)) = s.basis (w (j+258)) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : j+258 ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn (j+258) (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

theorem compactSkywalkStageMetadata_futureS (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj0 : i+1 ≤ j) (hj : j < 512)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w (1028+j)) = s.basis (w (1028+j)) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : 1028+j ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn (1028+j) (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

/-- The unused suffix of the original carry bank is a frame, with no
cleanliness premise on those untouched bits. -/
theorem compactSkywalkStageMetadata_carryTail (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat)
    (hj0 : 1540+(compactSkywalkTickPreWidth i-1) ≤ j) (hj : j < 1797)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : j ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn j (by omega) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

theorem compactSkywalkStageMetadata_orientation (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (hi0 : 0 < i) (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w 1797) = s.basis (w 1797) := by
  have width := compactSkywalkTick_width_bounds i hi
  have hp : 1797 ≠ skywalkPoolPreviousId i := by
    unfold skywalkPoolPreviousId
    split_ifs <;> omega
  exact compactSkywalkStage_tick_keep w i hi hn 1797 (by decide) hp
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s m

/-- The record at the current index is the proved physical output history. -/
theorem compactSkywalkStageMetadata_history (w : Nat → Wire) (i : Nat)
    (A B : Int) (G : Bool) (out : BasisState)
    (h : CompactSkywalkTickOutput w i A B G out) :
    out (w (1028+i)) = (SkywalkRails.step ⟨A,B,G⟩).s := h.2.2.2.1

/-- The predecessor is preserved by the native output contract, including
the special initial orientation site. -/
theorem compactSkywalkStageMetadata_previous (w : Nat → Wire) (i : Nat)
    (A B : Int) (G : Bool) (before out : BasisState)
    (hin : SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G before)
    (hout : CompactSkywalkTickOutput w i A B G out) :
    out (w (skywalkPoolPreviousId i)) = before (w (skywalkPoolPreviousId i)) :=
  hout.2.2.2.2.1.trans hin.2.2.1.symm

theorem compactSkywalkStageMetadata_previousG (w : Nat → Wire) (i : Nat) (hi0 : 0 < i)
    (A B : Int) (G : Bool) (before out : BasisState)
    (hin : SkywalkIntegerInput (compactSkywalkTickLayout w i) A B G before)
    (hout : CompactSkywalkTickOutput w i A B G out) :
    out (w (i-1)) = before (w (i-1)) := by
  have h := compactSkywalkStageMetadata_previous w i A B G before out hin hout
  simpa only [skywalkPoolPreviousId,if_neg (by omega : i ≠ 0)] using h

theorem compactSkywalkStageMetadata_orientation_zero (w : Nat → Wire)
    (A B : Int) (G : Bool) (before out : BasisState)
    (hin : SkywalkIntegerInput (compactSkywalkTickLayout w 0) A B G before)
    (hout : CompactSkywalkTickOutput w 0 A B G out) :
    out (w 1797) = before (w 1797) := by
  simpa only [skywalkPoolPreviousId,if_pos rfl] using
    (compactSkywalkStageMetadata_previous w 0 A B G before out hin hout)

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_pastG
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_pastS
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_futureExtension
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_futureS
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_carryTail
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_orientation
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_history
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_previous
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_previousG
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageMetadata_orientation_zero
