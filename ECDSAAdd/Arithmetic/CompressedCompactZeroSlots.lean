import ECDSAAdd.Arithmetic.CompressedCompactFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] run compressedEncodePrefix compressedHistoryEncode

/-- Every group actually packed in a prefix has a proved-zero fourth site.
The proof uses codec legality and instruction disjointness, never sampled bits. -/
theorem compressedPrefix_zero_slots (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (s : State) (legal : ∀ j, j+3 ≤ 512 →
      (s.basis (compressedHistoryMap w j 0) && s.basis (compressedHistoryMap w j 1))=false ∧
      (s.basis (compressedHistoryMap w j 2) && s.basis (compressedHistoryMap w j 3))=false ∧
      (s.basis (compressedHistoryMap w j 4) && s.basis (compressedHistoryMap w j 5))=false)
    (n : Nat) (hn512 : n ≤ 512) (m : List Bool)
    (start : Nat) (hmod : start%3=0) (hbound : start+4 ≤ n) :
    (run (compressedEncodePrefix w n) m s).basis (w (1028+start+1))=false := by
  induction n generalizing m start with
  | zero => omega
  | succ n ih =>
    have hi : n < 512 := by omega
    cases due : compressedPackDue n
    · have before : start+4 ≤ n := by
        by_contra h
        have e : n=start+3 := by omega
        have yes : compressedPackDue n=true := by
          simp [compressedPackDue,e,hmod]
        rw [yes] at due
        contradiction
      have old := ih (by omega) (m.take (measurementCount (compressedEncodePrefix w n)))
        start hmod before
      simp only [compressedEncodePrefix,run_append,compressedPackAfter,due,
        Bool.false_eq_true,if_false]
      simpa only [run] using old
    · have ndue := compressedPackDue_true n due
      let before := run (compressedEncodePrefix w n)
        (m.take (measurementCount (compressedEncodePrefix w n))) s
      rw [compressedEncodePrefix,run_append]
      simp only [compressedPackAfter,due,if_true]
      change (run (compressedHistoryEncode w (n-3))
        (m.drop (measurementCount (compressedEncodePrefix w n))) before).basis _=false
      by_cases same : start=n-3
      · have reads (j : Fin 6) : before.basis (compressedHistoryMap w (n-3) j)=
            s.basis (compressedHistoryMap w (n-3) j) :=
          compressedPrefix_raw_next w hn hlo n hi due s _ j
        have domain := legal (n-3) (by omega)
        have actualLegal :
            (before.basis (compressedHistoryMap w (n-3) 0) && before.basis (compressedHistoryMap w (n-3) 1))=false ∧
            (before.basis (compressedHistoryMap w (n-3) 2) && before.basis (compressedHistoryMap w (n-3) 3))=false ∧
            (before.basis (compressedHistoryMap w (n-3) 4) && before.basis (compressedHistoryMap w (n-3) 5))=false := by
          rw [reads 0,reads 1,reads 2,reads 3,reads 4,reads 5]
          exact domain
        have codec := TranscriptCodec3.placement_correct (compressedHistoryMap w (n-3))
          (compressedHistoryMap_injective w hn (n-3) (by omega))
          (compressedHistoryMap_above w (n-3) (by omega) hlo) before
          (m.drop (measurementCount (compressedEncodePrefix w n))) actualLegal
        simpa only [same,compressedHistoryEncode,compressedHistoryMap,compressedHistoryId,
          Nat.reduceMod,Nat.reduceDiv,Nat.reduceEqDiff,if_false] using codec.2.1
      · have sep : start+3 ≤ n-3 := by omega
        have old := ih (by omega) (m.take (measurementCount (compressedEncodePrefix w n)))
          start hmod (by omega)
        have disjoint := compressedHistory_windows_disjoint w hn hlo start (n-3)
          (by omega) (by omega) sep
        have site : w (1028+start+1)∈wires (compressedHistoryEncode w start) := by
          simpa only [compressedHistoryMap,compressedHistoryId,Nat.reduceMod,Nat.reduceDiv,
            Nat.reduceEqDiff,if_false] using compressedHistory_site_mem w hn hlo start (by omega) 3
        have keep := run_preserves_outside (compressedHistoryEncode w (n-3))
          (m.drop (measurementCount (compressedEncodePrefix w n))) before (w (1028+start+1))
          (fun h => Finset.disjoint_left.mp disjoint site h)
        exact keep.trans old

/-- The complete compact integer caller supplies legality for all170 groups. -/
theorem compressedCompactStage_512_zero_slots (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1) (s : State)
    (h : CompressedCompactStage w x p 512 s.basis)
    (j : Nat) (hj : j < 170) : s.basis (w (1029+3*j))=false := by
  obtain ⟨raw,hraw,bits⟩ := h
  have legal (start : Nat) (hs : start+3 ≤ 512) :=
    compressedCompactHistory_legal w hn x p 512 start hp0 hpo hs (by decide) raw.basis hraw
  have zero := compressedPrefix_zero_slots w hn hlo raw legal 512 (by decide) []
    (3*j) (by omega) (by omega)
  rw [bits]
  have index : 1028+3*j+1=1029+3*j := by omega
  simpa only [index] using zero

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compressedPrefix_zero_slots
#print axioms ECDSAAdd.Arithmetic.compressedCompactStage_512_zero_slots
