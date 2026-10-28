import ECDSAAdd.Arithmetic.CompressedFieldFullEncoding
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
attribute [local irreducible] run compressedHistoryEncode

def otherGroupEncode (w : Nat → Wire) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if n=j then otherGroupEncode w j n else
      otherGroupEncode w j n++compressedHistoryEncode w (3*n)

theorem otherGroupEncode_outside (w : Nat → Wire) (n j : Nat) (h : n ≤ j) :
    otherGroupEncode w j n = allGroupEncode w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [otherGroupEncode,if_neg (by omega),ih (by omega),allGroupEncode]

theorem otherGroupEncode_member (w : Nat → Wire) (n j : Nat) (q : Wire)
    (h : q ∈ wires (otherGroupEncode w j n)) :
    ∃ k,k < n ∧ k ≠ j ∧ q ∈ wires (compressedHistoryEncode w (3*k)) := by
  induction n with
  | zero => simp [otherGroupEncode,wires] at h
  | succ n ih =>
    by_cases same : n=j
    · simp only [otherGroupEncode,if_pos same] at h
      obtain ⟨k,hk,hj,member⟩ := ih h
      exact ⟨k,by omega,hj,member⟩
    · simp only [otherGroupEncode,if_neg same,wires_append,Finset.mem_union] at h
      rcases h with h|h
      · obtain ⟨k,hk,hj,member⟩ := ih h
        exact ⟨k,by omega,hj,member⟩
      · exact ⟨n,by omega,same,h⟩

theorem otherGroupEncode_disjoint (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n j : Nat) (bound : 3*n ≤ 512) (hj : j < n) :
    Disjoint (wires (otherGroupEncode w j n)) (wires (compressedHistoryEncode w (3*j))) := by
  apply Finset.disjoint_left.mpr
  intro q hq hc
  obtain ⟨k,hk,ne,member⟩ := otherGroupEncode_member w n j q hq
  have sep : 3*k+3 ≤ 3*j ∨ 3*j+3 ≤ 3*k := by omega
  have dis : Disjoint (wires (compressedHistoryEncode w (3*k)))
      (wires (compressedHistoryEncode w (3*j))) := by
    rcases sep with h|h
    · exact compressedHistory_windows_disjoint w hn hlo _ _ (by omega) (by omega) h
    · exact (compressedHistory_windows_disjoint w hn hlo _ _ (by omega) (by omega) h).symm
  exact Finset.disjoint_left.mp dis member hc

/-- Extract the current encoder from the actual full170-group circuit;
all remaining groups stay encoded in their original order. -/
theorem allGroupEncode_factor (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n j : Nat) (bound : 3*n ≤ 512) (hj : j < n) (s : State) :
    run (allGroupEncode w n) [] s =
      run (otherGroupEncode w j n) [] (run (compressedHistoryEncode w (3*j)) [] s) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    by_cases same : j=n
    · subst j
      have dis := allGroupEncode_disjoint w hn hlo n n (by omega) (Nat.le_refl _) (by omega)
      rw [allGroupEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [otherGroupEncode,if_pos rfl,otherGroupEncode_outside w n n (Nat.le_refl _)]
      exact (run_disjoint_commute (allGroupEncode w n) (compressedHistoryEncode w (3*n)) dis [] [] s).symm
    · have small : j < n := by omega
      have prior := ih j (by omega) small
      have right : run (otherGroupEncode w j (n+1)) []
          (run (compressedHistoryEncode w (3*j)) [] s) =
          run (compressedHistoryEncode w (3*n)) []
            (run (otherGroupEncode w j n) [] (run (compressedHistoryEncode w (3*j)) [] s)) := by
        rw [otherGroupEncode,if_neg (Ne.symm same),run_append]
        simp only [List.take_nil,List.drop_nil]
      rw [allGroupEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [prior,right]

/-- The complete foreign encoder is disjoint from an actual current
three-cell packet; this supplies the packet theorem's concrete premise. -/
theorem otherGroupEncode_body_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hb : b ∉ skywalkPoolWires w) (hs : sign ∉ skywalkPoolWires w) (he : eff ∉ skywalkPoolWires w)
    (n j : Nat) (bound : 3*n ≤ 512) (hj : j < n) (body : Program)
    (support : wires body ⊆ groupReadSites w b sign eff (3*j)) :
    Disjoint (wires (otherGroupEncode w j n)) (wires body) := by
  apply Finset.disjoint_left.mpr
  intro q hq hbody
  obtain ⟨k,hk,ne,member⟩ := otherGroupEncode_member w n j q hq
  have dis := other_encoder_disjoint w b sign eff hn hlo hb hs he (3*k) (3*j)
    (by omega) (by omega) (by omega) body support
  exact Finset.disjoint_left.mp dis member hbody

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.allGroupEncode_factor
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.otherGroupEncode_body_disjoint
