import ECDSAAdd.Arithmetic.CompactSkywalkStageFields
import ECDSAAdd.Arithmetic.CompactSkywalkStageMetadata

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem blockPrefix (w : Nat → Wire) (start len n : Nat) (hn : n ≤ len) :
    (wireBlock w start len).take n = wireBlock w start n := by
  have h := wireBlock_append w start n (len-n)
  rw [show n+(len-n) = len by omega] at h
  rw [←h]
  have ht : (wireBlock w start n++wireBlock w (start+n) (len-n)).take
    (wireBlock w start n).length = wireBlock w start n := List.take_left
  simpa only [wireBlock_length] using ht

private theorem blockDrop (w : Nat → Wire) (start len n : Nat) (hn : n ≤ len) :
    (wireBlock w start len).drop n = wireBlock w (start+n) (len-n) := by
  have h := wireBlock_append w start n (len-n)
  rw [show n+(len-n) = len by omega] at h
  rw [←h]
  have ht : (wireBlock w start n++wireBlock w (start+n) (len-n)).drop
    (wireBlock w start n).length = wireBlock w (start+n) (len-n) := List.drop_left
  simpa only [wireBlock_length] using ht

/-- Next retained words are precisely the physically computed output prefixes. -/
theorem compactSkywalkStageStep_retained (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkSignPoolA w (i+1)).retained = (compactSkywalkTickARelease w i).retained ∧
    (compactSkywalkSignPoolB w (i+1)).retained = (compactSkywalkTickBRelease w i).retained := by
  have h := compactSkywalkTick_width_bounds i hi
  have a := compactSkywalkStage_width (i+1) (by omega)
  have e : narrowSkywalkRouteWidth (i+1) = compactSkywalkTickPostWidth i := h.2.2.2.2.2.symm
  have pos : 0 < compactSkywalkTickPostWidth i := by omega
  have nextA := compactSkywalkSignWord_retained (skywalkPoolA w (i+1))
    (narrowSkywalkRouteWidth (i+1)) (by omega) (by simpa only [skywalkPoolA,wireBlock_length] using a.2)
  have nextB := compactSkywalkSignWord_retained (skywalkPoolB w)
    (narrowSkywalkRouteWidth (i+1)) (by omega) (by simpa only [skywalkPoolB,wireBlock_length] using a.2)
  have curA := compactSkywalkSignWord_retained (compactSkywalkTickLayout w i).half
    (compactSkywalkTickPostWidth i) pos (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)
  have curB := compactSkywalkSignWord_retained (compactSkywalkTickLayout w i).b
    (compactSkywalkTickPostWidth i) pos (by
      rw [compactSkywalkTick_b w i hi,wireBlock_length]; exact h.2.2.1)
  constructor
  · change (compactSkywalkSignWord _ _).retained = (compactSkywalkSignWord _ _).retained
    rw [nextA,curA,e,compactSkywalkTick_half w i hi,skywalkPoolA]
    rw [blockPrefix w (i+1) 258 _ (by omega),blockPrefix w (i+1) _ _ h.2.2.1]
  · change (compactSkywalkSignWord _ _).retained = (compactSkywalkSignWord _ _).retained
    rw [nextB,curB,e,compactSkywalkTick_b w i hi,skywalkPoolB]
    rw [blockPrefix w 770 258 _ (by omega),blockPrefix w 770 _ _ h.2.2.1]

/-- Current cleanup tails and next full-word tails are concrete intervals. -/
theorem compactSkywalkStageStep_tail_views (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickARelease w i).released =
      wireBlock w (i+1+compactSkywalkTickPostWidth i)
        (compactSkywalkTickPreWidth i-compactSkywalkTickPostWidth i) ∧
    (compactSkywalkTickBRelease w i).released =
      wireBlock w (770+compactSkywalkTickPostWidth i)
        (compactSkywalkTickPreWidth i-compactSkywalkTickPostWidth i) ∧
    (compactSkywalkSignPoolA w (i+1)).released =
      wireBlock w (i+1+compactSkywalkTickPostWidth i) (258-compactSkywalkTickPostWidth i) ∧
    (compactSkywalkSignPoolB w (i+1)).released =
      wireBlock w (770+compactSkywalkTickPostWidth i) (258-compactSkywalkTickPostWidth i) ∧
    (compactSkywalkSignPoolA w i).released =
      wireBlock w (i+compactSkywalkTickPreWidth i) (258-compactSkywalkTickPreWidth i) ∧
    (compactSkywalkSignPoolB w i).released =
      wireBlock w (770+compactSkywalkTickPreWidth i) (258-compactSkywalkTickPreWidth i) := by
  have h := compactSkywalkTick_width_bounds i hi
  have e : narrowSkywalkRouteWidth (i+1) = compactSkywalkTickPostWidth i := h.2.2.2.2.2.symm
  simp only [compactSkywalkTickARelease,compactSkywalkTickBRelease,compactSkywalkSignPoolA,
    compactSkywalkSignPoolB,compactSkywalkSignWord,compactSkywalkTick_half w i hi,
    compactSkywalkTick_b w i hi,skywalkPoolA,skywalkPoolB,e]
  change (wireBlock w (i+1) (compactSkywalkTickPreWidth i)).drop (compactSkywalkTickPostWidth i) = _ ∧
    (wireBlock w 770 (compactSkywalkTickPreWidth i)).drop (compactSkywalkTickPostWidth i) = _ ∧
    (wireBlock w (i+1) 258).drop (compactSkywalkTickPostWidth i) = _ ∧
    (wireBlock w 770 258).drop (compactSkywalkTickPostWidth i) = _ ∧
    (wireBlock w i 258).drop (compactSkywalkTickPreWidth i) = _ ∧
    (wireBlock w 770 258).drop (compactSkywalkTickPreWidth i) = _
  exact ⟨blockDrop _ _ _ _ h.2.2.1,blockDrop _ _ _ _ h.2.2.1,
    blockDrop _ _ _ _ (by omega),blockDrop _ _ _ _ (by omega),
    blockDrop _ _ _ _ h.2.2.2.1,blockDrop _ _ _ _ h.2.2.2.1⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageStep_retained
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageStep_tail_views
