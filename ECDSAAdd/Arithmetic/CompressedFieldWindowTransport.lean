import ECDSAAdd.Arithmetic.CompressedFieldCellSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
attribute [local irreducible] run wires compressedHistoryEncode compressedHistoryDecode

/-- A current three-cell group reads only its own six raw controls, plus
nonhistory data/work and external activation/selection controls. -/
def groupReadSites (w : Nat → Wire) (b sign eff : Wire) (start : Nat) : Finset Wire :=
  (sharedSites w sign).toFinset ∪ {b,eff} ∪ wires (compressedHistoryEncode w start)

theorem current_cells_support (w : Nat → Wire) (b sign eff : Wire) (start : Nat)
    (g swap : Wire) (ig is : Bool)
    (hg : g ∈ wires (compressedHistoryEncode w start))
    (hs : swap ∈ wires (compressedHistoryEncode w start)) :
    wires (OffsetBorrowedCanonical.cell w b g swap sign eff ig is) ⊆ groupReadSites w b sign eff start ∧
    wires (OffsetBorrowedInverseCanonical.cell w b g swap sign eff ig is) ⊆ groupReadSites w b sign eff start := by
  apply cells_active
  · intro q hq
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hq)
  · simp [groupReadSites]
  · exact Finset.mem_union_right _ hg
  · exact Finset.mem_union_right _ hs
  · simp [groupReadSites]

/-- Every other history encoder is disjoint from a current field group.
The actual strong support excludes descriptor-only history0/1. -/
theorem other_encoder_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hb : b ∉ skywalkPoolWires w) (hsign : sign ∉ skywalkPoolWires w)
    (heff : eff ∉ skywalkPoolWires w) (a start : Nat)
    (ha : a+3 ≤ 512) (hst : start+3 ≤ 512) (sep : a+3 ≤ start ∨ start+3 ≤ a)
    (body : Program) (support : wires body ⊆ groupReadSites w b sign eff start) :
    Disjoint (wires (compressedHistoryEncode w a)) (wires body) := by
  have pool := skywalkShared_integer_nodup w hn
  have groups : Disjoint (wires (compressedHistoryEncode w a)) (wires (compressedHistoryEncode w start)) := by
    rcases sep with h|h
    · exact compressedHistory_windows_disjoint w pool hlo a start ha hst h
    · exact (compressedHistory_windows_disjoint w pool hlo start a hst ha h).symm
  apply Finset.disjoint_left.mpr
  intro q hq ht
  obtain ⟨j,rfl⟩ := compressedHistory_gate_mem w pool hlo a ha _ (Or.inl rfl) q hq
  have bound := compressedHistoryId_bound a ha j
  have own : w (compressedHistoryId a j) ∈ skywalkPoolWires w := by
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨compressedHistoryId a j,by omega,rfl⟩
  have away := history_active_away w sign hn hsign a ha j
  have read := support ht
  simp only [groupReadSites,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at read
  rcases read with (read|read)|read
  · exact away (List.mem_toFinset.mp read)
  · rcases read with eq|eq
    · exact hb (eq ▸ own)
    · exact heff (eq ▸ own)
  · exact Finset.disjoint_left.mp groups hq read

/-- Exact current-window transport with independently supplied records.
Other groups may already be encoded: their actual program is commuted,
never interpreted using a false raw-history PairFrame premise. -/
theorem window_transport_other (w : Nat → Wire) (start : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hs : start+3 ≤ 512) (other body : Program)
    (he : Disjoint (wires other) (wires (compressedHistoryEncode w start)))
    (hb : Disjoint (wires other) (wires body))
    (s : State) (mOther m0 m1 m2 m3 : List Bool)
    (legal : (s.basis (compressedHistoryMap w start 0) && s.basis (compressedHistoryMap w start 1)) = false ∧
      (s.basis (compressedHistoryMap w start 2) && s.basis (compressedHistoryMap w start 3)) = false ∧
      (s.basis (compressedHistoryMap w start 4) && s.basis (compressedHistoryMap w start 5)) = false) :
    run (compressedHistoryEncode w start) m3
      (run body m2 (run (compressedHistoryDecode w start) m1
        (run other mOther (run (compressedHistoryEncode w start) m0 s)))) =
      run other mOther (run (compressedHistoryEncode w start) m3 (run body m2 s)) := by
  have same (j : Fin 6) : (run other mOther s).basis (compressedHistoryMap w start j) =
      s.basis (compressedHistoryMap w start j) := by
    apply run_preserves_outside
    intro h
    exact Finset.disjoint_left.mp he h (compressedHistory_site_mem w hn hlo start hs j)
  have legalOther :
      ((run other mOther s).basis (compressedHistoryMap w start 0) &&
        (run other mOther s).basis (compressedHistoryMap w start 1)) = false ∧
      ((run other mOther s).basis (compressedHistoryMap w start 2) &&
        (run other mOther s).basis (compressedHistoryMap w start 3)) = false ∧
      ((run other mOther s).basis (compressedHistoryMap w start 4) &&
        (run other mOther s).basis (compressedHistoryMap w start 5)) = false := by
    rw [same 0,same 1,same 2,same 3,same 4,same 5]
    exact legal
  rw [run_disjoint_commute other (compressedHistoryEncode w start) he mOther m0 s]
  have window := TranscriptCodec3.window_states (compressedHistoryMap w start)
    (compressedHistoryMap_injective w hn start hs) (compressedHistoryMap_above w start hs hlo)
    body (run other mOther s) m0 m1 m2 m3 legalOther
  have window' : run (compressedHistoryEncode w start) m3
      (run body m2 (run (compressedHistoryDecode w start) m1
        (run (compressedHistoryEncode w start) m0 (run other mOther s)))) =
      run (compressedHistoryEncode w start) m3 (run body m2 (run other mOther s)) := by
    simpa only [compressedHistoryEncode,compressedHistoryDecode] using window
  rw [window']
  rw [←run_disjoint_commute other body hb mOther m2 s]
  exact (run_disjoint_commute other (compressedHistoryEncode w start) he mOther m3 (run body m2 s)).symm

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.current_cells_support
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.other_encoder_disjoint
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.window_transport_other
