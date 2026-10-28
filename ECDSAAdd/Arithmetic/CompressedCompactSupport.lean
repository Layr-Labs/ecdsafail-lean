import ECDSAAdd.Arithmetic.CompressedSkywalkPrefix
import ECDSAAdd.Arithmetic.CompactSkywalkForwardFrame
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] compactSkywalkTick compressedHistoryEncode compressedEncodePrefix

/-- Exact local support of the actual compact native tick and sign-tail
cleanup excludes any group whose final orientation was already consumed. -/
theorem compressedHistory_disjoint_compactTick (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (start i : Nat) (hs : start+3 ≤ 512) (hlate : start+4 ≤ i) (hi : i < 512) :
    Disjoint (wires (compressedHistoryEncode w start)) (wires (compactSkywalkTick w i)) := by
  apply Finset.disjoint_left.mpr
  intro q hq ht
  obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w hn hlo start hs _ (Or.inl rfl) q hq
  have mem := List.mem_toFinset.mp (compactSkywalkTick_support w i hi hn ht)
  have width := compactSkywalkTick_width_bounds i hi
  have hpos : i ≠ 0 := by omega
  have away : w (compressedHistoryId start j) ∉ (compactSkywalkTickLayout w i).wires := by
    apply compactSkywalkStage_tick_away w i hi hn (compressedHistoryId start j)
      (compressedHistoryId_bound start hs j)
    all_goals
      have hj := j.isLt
      unfold compressedHistoryId
      split_ifs <;> (try simp only [skywalkPoolPreviousId,if_neg hpos]) <;> omega
  exact away mem

/-- Prefix packing remains disjoint from every later compact tick. The
existing delayed pack schedule is retained verbatim. -/
theorem compressedPrefix_disjoint_compactTick (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n i : Nat) (hni : n ≤ i) (hi : i < 512) :
    Disjoint (wires (compressedEncodePrefix w n)) (wires (compactSkywalkTick w i)) := by
  induction n with
  | zero => simp [compressedEncodePrefix,wires]
  | succ n ih =>
    have old := ih (by omega)
    have now : Disjoint (wires (compressedPackAfter w n)) (wires (compactSkywalkTick w i)) := by
      cases due : compressedPackDue n
      · simp [compressedPackAfter,due,wires]
      · have h3 := compressedPackDue_true n due
        have h := compressedHistory_disjoint_compactTick w hn hlo (n-3) i (by omega) (by omega) hi
        simpa only [compressedPackAfter,due,if_true] using h
    simp only [compressedEncodePrefix,wires_append,Finset.disjoint_union_left]
    exact ⟨old,now⟩

/-- The compact physical stage supplies the exact legal ternary tape to
all codec groups. No expanded-tail circuit is needed for this argument. -/
theorem compressedCompactHistory_legal (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p i start : Nat)
    (hp0 : 0 < p) (hpo : p%2 = 1) (hs : start+3 ≤ i) (hi : i ≤ 512)
    (s : BasisState)
    (h : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s) :
    (s (compressedHistoryMap w start 0) && s (compressedHistoryMap w start 1)) = false ∧
    (s (compressedHistoryMap w start 2) && s (compressedHistoryMap w start 3)) = false ∧
    (s (compressedHistoryMap w start 4) && s (compressedHistoryMap w start 5)) = false := by
  have fields := (compactSkywalkStage_fields_iff w _ i hi hn s).mp h
  have tape := fields.2.2.2.1
  have ternary (j : Nat) (hj : j < i) : (s (w j) && s (w (1028+j))) = false := by
    rw [(tape j hj).1,(tape j hj).2]
    exact skywalkRecordedSymbol_legal x p j hp0 hpo
  have a := ternary start (by omega)
  have b := ternary (start+1) (by omega)
  have c := ternary (start+2) (by omega)
  simpa [compressedHistoryMap,compressedHistoryId,Nat.add_assoc] using And.intro a (And.intro b c)

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compressedHistory_disjoint_compactTick
#print axioms ECDSAAdd.Arithmetic.compressedPrefix_disjoint_compactTick
#print axioms ECDSAAdd.Arithmetic.compressedCompactHistory_legal
