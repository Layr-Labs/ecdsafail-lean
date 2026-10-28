import ECDSAAdd.Arithmetic.CompactSkywalkStageFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Physical form of the compact invariant. Only the current signed reads
are shortened; all stored controls and fresh/work bits remain explicit. -/
def CompactSkywalkStageFields (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (s : BasisState) : Prop :=
  let ri := SkywalkTrace.next^[i] r
  signedRegValue (compactSkywalkSignPoolA w i).retained s=ri.a ∧
  signedRegValue (compactSkywalkSignPoolB w i).retained s=ri.b ∧
  s (w (skywalkPoolPreviousId i))=ri.g ∧
  (∀j,j < i → s (w j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 ∧
    s (w (1028+j))=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).2) ∧
  (∀j,i ≤ j → j < 512 → s (w (j+258))=false ∧ s (w (1028+j))=false) ∧
  regValue (wireBlock w 1540 257) s=0 ∧ s (w 1797)=false ∧
  (compactSkywalkSignPoolA w i).Clean s ∧ (compactSkywalkSignPoolB w i).Clean s

private theorem metadata_reads (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (hi : i ≤ 512) (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    SkywalkIntegerStage w r i (compactSkywalkStageVirtual w i s) ↔
      signedRegValue (compactSkywalkSignPoolA w i).retained s=(SkywalkTrace.next^[i] r).a ∧
      signedRegValue (compactSkywalkSignPoolB w i).retained s=(SkywalkTrace.next^[i] r).b ∧
      s (w (skywalkPoolPreviousId i))=(SkywalkTrace.next^[i] r).g ∧
      (∀j,j < i → s (w j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 ∧
        s (w (1028+j))=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).2) ∧
      (∀j,i ≤ j → j < 512 → s (w (j+258))=false ∧ s (w (1028+j))=false) ∧
      regValue (wireBlock w 1540 257) s=0 ∧ s (w 1797)=false := by
  have values := compactSkywalkStage_virtual_values w i hi hn s
  have keep (j : Nat) (hj : j < 1798) (ha : j < i ∨ i+258 ≤ j)
      (hb : j < 770 ∨ 1028 ≤ j) := compactSkywalkStage_virtual_index w i hi hn s j hj ha hb
  have prev := keep (skywalkPoolPreviousId i) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega)
  have initial := keep 1797 (by omega) (by omega) (by omega)
  have carry : regValue (wireBlock w 1540 257) (compactSkywalkStageVirtual w i s)=
      regValue (wireBlock w 1540 257) s := by
    apply regValue_congr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact keep j (by omega) (by omega) (by omega)
  have oldG (j : Nat) (hj : j < i) := keep j (by omega) (by omega) (by omega)
  have oldS (j : Nat) (hj : j < i) := keep (1028+j) (by omega) (by omega) (by omega)
  have freshE (j : Nat) (hj : i ≤ j) (h512 : j < 512) :=
    keep (j+258) (by omega) (by omega) (by omega)
  have freshS (j : Nat) (hj : i ≤ j) (h512 : j < 512) :=
    keep (1028+j) (by omega) (by omega) (by omega)
  unfold SkywalkIntegerStage
  rw [values.1,values.2,prev,carry,initial]
  constructor
  · intro h
    refine ⟨h.1,h.2.1,h.2.2.1,?_,?_,h.2.2.2.2.2⟩
    · intro j hj
      have t := h.2.2.2.1 j hj
      simpa only [oldG j hj,oldS j hj] using t
    · intro j hj hk
      have t := h.2.2.2.2.1 j hj hk
      simpa only [freshE j hj hk,freshS j hj hk] using t
  · intro h
    refine ⟨h.1,h.2.1,h.2.2.1,?_,?_,h.2.2.2.2.2⟩
    · intro j hj
      rw [oldG j hj,oldS j hj]
      exact h.2.2.2.1 j hj
    · intro j hj hk
      rw [freshE j hj hk,freshS j hj hk]
      exact h.2.2.2.2.1 j hj hk

/-- Equivalence introduces no predicate about unseen high qubits. The
mathematical virtual view is exactly the physical prefix/clean-tail assertion. -/
theorem compactSkywalkStage_fields_iff (w : Nat → Wire) (r : SkywalkRails.State)
    (i : Nat) (hi : i ≤ 512) (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    CompactSkywalkStage w r i s ↔ CompactSkywalkStageFields w r i s := by
  unfold CompactSkywalkStage CompactSkywalkStageFields
  rw [metadata_reads w r i hi hn s]
  constructor
  · rintro ⟨⟨ha,hb,hg,hpast,hfuture,hcarry,horient⟩,hcleanA,hcleanB⟩
    exact ⟨ha,hb,hg,hpast,hfuture,hcarry,horient,hcleanA,hcleanB⟩
  · rintro ⟨ha,hb,hg,hpast,hfuture,hcarry,horient,hcleanA,hcleanB⟩
    exact ⟨⟨ha,hb,hg,hpast,hfuture,hcarry,horient⟩,hcleanA,hcleanB⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_fields_iff
