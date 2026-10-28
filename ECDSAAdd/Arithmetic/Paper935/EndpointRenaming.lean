import ECDSAAdd.Arithmetic.Paper935.ArenaPermutation
import ECDSAAdd.Arithmetic.Paper935.OwnedOutputAssembly
import ECDSAAdd.Arithmetic.Paper935.OutputSlotAssembly

namespace ECDSAAdd.Arithmetic.Paper935

def renamedEndpointSlot (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot) (E : RecordedProgram) : RecordedProgram :=
  renameRecordedProgram e.equiv (endpointSlotProgram p k slots E)

def renamedEndpointClosed (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (m : List Bool) (s : State) : State :=
  run (renameProgram e.equiv (closerProgram (walkExitBank walkSeedBank slots) p))
    (m.drop (endpointCursor p k slots))
    (runWithTape (renameRecordedProgram e.equiv (seededAuthorWalkProgram p slots)) m k s)

def renamedEndpointAfter (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (m : List Bool) (s : State) : State :=
  runWithTape (renameRecordedProgram e.equiv E) m (endpointCursor p k slots)
    (renamedEndpointClosed e p k slots m s)

attribute [local irreducible] seededAuthorWalkProgram seededAuthorWalkReverse closerProgram actualHistoryDecoder

theorem renamedEndpointClosed_pull (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (m : List Bool) (s : State) :
    pullState e.equiv (renamedEndpointClosed e p k slots m s)=endpointClosed p k slots m (pullState e.equiv s) := by
  rw [renamedEndpointClosed,run_rename e.equiv e.equiv.injective,runWithTape_rename e.equiv e.equiv.injective]
  rfl

theorem renamedEndpointAfter_pull (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (m : List Bool) (s : State) :
    pullState e.equiv (renamedEndpointAfter e p k slots E m s)=endpointAfter p k slots E m (pullState e.equiv s) := by
  rw [renamedEndpointAfter,runWithTape_rename e.equiv e.equiv.injective,renamedEndpointClosed_pull]
  rfl

/-- Recorded support is renamed exactly; sources and cursor increments are not
renumbered. Gate counts retain the original three-segment sum. -/
def RenamedEndpointResources (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) : Prop :=
  RecordedWellFormedAt k (renamedEndpointSlot e p k slots E) ∧
  recordedWires (renamedEndpointSlot e p k slots E)=(recordedWires (endpointSlotProgram p k slots E)).image e.equiv ∧
  (∀q∈recordedWires (renamedEndpointSlot e p k slots E),q<935) ∧
  recordedSources (renamedEndpointSlot e p k slots E)=recordedSources (endpointSlotProgram p k slots E) ∧
  recordedToffoliCount (renamedEndpointSlot e p k slots E)=recordedToffoliCount (endpointSlotProgram p k slots E) ∧
  recordedMeasurementCount (renamedEndpointSlot e p k slots E)=recordedMeasurementCount (endpointSlotProgram p k slots E) ∧
  recordedToffoliCount (renamedEndpointSlot e p k slots E)=
    recordedToffoliCount (seededAuthorWalkProgram p slots)+recordedToffoliCount E+
    recordedToffoliCount (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) k slots) ∧
  recordedMeasurementCount (renamedEndpointSlot e p k slots E)=
    recordedMeasurementCount (seededAuthorWalkProgram p slots)+recordedMeasurementCount E+
    recordedMeasurementCount (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) k slots)

theorem renamedEndpoint_resources (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (wf : RecordedWellFormedAt k (endpointSlotProgram p k slots E))
    (bound : ∀q∈recordedWires (endpointSlotProgram p k slots E),q<935) :
    RenamedEndpointResources e p k slots E := by
  have counts := renameRecorded_counts e.equiv (endpointSlotProgram p k slots E)
  refine ⟨(renameRecorded_wellFormed _ _ _).mpr wf,renameRecorded_wires _ _,?_,
    renameRecorded_sources _ _,counts.1,counts.2,counts.1.trans (endpointSlot_counts _ _ _ _).1,
    counts.2.trans (endpointSlot_counts _ _ _ _).2⟩
  intro q hq
  rw [renamedEndpointSlot,renameRecorded_wires] at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  have inside : a∈arenaWires := by simpa only [arenaWires,Finset.mem_range] using bound a ha
  simpa only [arenaWires,Finset.mem_range] using (e.preserves a).mpr inside

theorem renamedEndpoint_aHost_isolated (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    Disjoint (aHost.image e.equiv) (recordedWires (renameRecordedProgram e.equiv
      (seededAuthorWalkProgram p slots ++ embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p) ++
      embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
      seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) k slots))) := by
  rw [renameRecorded_wires,e.disjoint_image]
  exact authorWalk_aHost_support p k slots compiled

/-- Any finite arena self-bijection has this identical physical gate stream;
its arbitrary values outside the arena impose no new premise. -/
theorem renamedEndpoint_ofFinite (f : Wire → Wire) (inj : Set.InjOn f arenaWires)
    (image : arenaWires.image f=arenaWires) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (support : recordedWires (endpointSlotProgram p k slots E)⊆arenaWires) :
    renamedEndpointSlot (ArenaPermutation.ofFinite f inj image) p k slots E=
      renameRecordedProgram f (endpointSlotProgram p k slots E) :=
  finiteWirePermutation_program arenaWires f inj image _ support

/-- Actual temporary transactions are transported, including the final basis
on which release checks cleanliness. -/
theorem EndpointBorrow.renamed (A : Arena) (e : ArenaPermutation) (E : RecordedProgram) (out : State)
    (h : EndpointBorrow A E (pullState e.equiv out)) :
    EndpointBorrow (A.renamed e) (renameRecordedProgram e.equiv E) out := by
  obtain ⟨qs,during,free,reserved,support,released⟩ := h
  refine ⟨qs.image e.equiv,during.renamed e,?_,A.renamed_reserve during qs e reserved,?_,
    during.renamed_release A qs e out.basis released⟩
  · intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    have hf := Finset.mem_sdiff.mp (free ha)
    refine Finset.mem_sdiff.mpr ⟨(e.preserves a).mpr hf.1,?_⟩
    simpa only [Arena.renamed,Finset.mem_image,e.equiv.injective.eq_iff,exists_eq_right] using hf.2
  · rw [renameRecorded_wires]
    exact Finset.image_subset_image support

end ECDSAAdd.Arithmetic.Paper935
