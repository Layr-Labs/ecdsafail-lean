import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportLayout
import ECDSAAdd.Arithmetic.BalancedSharedDivision
import ECDSAAdd.Arithmetic.BalancedInverseSharedMultiplication
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
attribute [local irreducible] wireBlock copyRegister
attribute [local irreducible] balancedTranscriptReplay balancedInverseTranscriptReplay

private theorem zip_record (rs : List (Wire×Wire)) (cs : List (Bool×Bool))
    (l : MixedTranscriptLetter) (hl : l∈rs.zip cs) : l.1∈rs := by
  induction rs generalizing cs with
  | nil => simp at hl
  | cons r rs ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      simp only [List.zip_cons_cons,List.mem_cons] at hl
      rcases hl with rfl|hl
      · simp
      · exact List.mem_cons_of_mem r (ih cs hl)

theorem tapeSupport (w : Nat → Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) :
    ∀l∈mixedTranscriptTape w,l.1.1∈W ∧ l.1.2∈W := by
  intro l hl
  have recorded := zip_record (skywalkSharedTape w) mixedTranscriptUnitTrace l hl
  change l.1∈(List.range 512).map (fun i => (w i,w (1028+i))) at recorded
  obtain ⟨i,hi,he⟩ := List.mem_map.mp recorded
  have hi' : i < 512 := List.mem_range.mp hi
  rw [←he]
  exact ⟨hW (List.mem_toFinset.mpr (index_mem w i (Or.inl (by omega)))),
    hW (List.mem_toFinset.mpr (index_mem w (1028+i) (Or.inl (by omega))))⟩

/-- Actual centered replay and endpoint converters need no omitted virtual bank. -/
theorem replayPrograms (w : Nat → Wire) (b effG effS : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hb : b∈W) (hg : effG∈W) (hs : effS∈W) :
    wires (balancedSharedReplayProgram w b effG effS)⊆W ∧
    wires (balancedInverseSharedReplayProgram w b effG effS)⊆W := by
  have hc := converters w W hW
  have hr := replay w b effG effS (mixedTranscriptTape w) W hW hb hg hs (tapeSupport w W hW)
  simp only [balancedSharedReplayProgram,balancedInverseSharedReplayProgram,
    wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨hc.1.1,hc.1.2⟩,hr.1⟩,hc.2.1⟩,hc.2.2⟩,
    ⟨⟨⟨⟨hc.1.1,hc.1.2⟩,hr.2⟩,hc.2.1⟩,hc.2.2⟩⟩

/-- Full 257-bit copy used by the production field endpoint wrappers. -/
theorem copy (w : Nat → Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) :
    wires (copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a)⊆W := by
  have hw := skywalkShared_field_widths w
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hz : ((skywalkSharedField w).z).toFinset⊆W := by
    rw [skywalkShared_field_z]
    exact blockSites w 2056 257 W hW (by intro i h₁ h₂; exact Or.inr ⟨h₁,by omega⟩)
  have ha : ((skywalkSharedField w).a).toFinset⊆W :=
    blockSites w 770 257 W hW (by intro i _ h₂; exact Or.inl (by omega))
  rw [copyRegister_wires none (skywalkSharedField w).z (skywalkSharedField w).a hlen]
  split
  · exact Finset.empty_subset _
  · intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hq|hq
    · exact hz (List.mem_toFinset.mpr hq)
    · exact ha (List.mem_toFinset.mpr hq)

/-- The narrow centered data ports use the same compact allocation. -/
theorem copyLow (w : Nat → Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) :
    wires (copyRegister none (wireBlock w 2056 256) (wireBlock w 770 256))⊆W := by
  have hlen : (wireBlock w 2056 256).length=(wireBlock w 770 256).length := by
    rw [wireBlock_length,wireBlock_length]
  have hz := blockSites w 2056 256 W hW (by intro i h₁ h₂; exact Or.inr ⟨h₁,by omega⟩)
  have ha := blockSites w 770 256 W hW (by intro i _ h₂; exact Or.inl (by omega))
  rw [copyRegister_wires none (wireBlock w 2056 256) (wireBlock w 770 256) hlen]
  split
  · exact Finset.empty_subset _
  · intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hq|hq
    · exact hz (List.mem_toFinset.mpr hq)
    · exact ha (List.mem_toFinset.mpr hq)
end ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.tapeSupport
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.replayPrograms
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.copy
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.copyLow
