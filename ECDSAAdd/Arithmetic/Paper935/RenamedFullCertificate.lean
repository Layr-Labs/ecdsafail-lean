import ECDSAAdd.Arithmetic.Paper935.EndpointRenaming

namespace ECDSAAdd.Arithmetic.Paper935

/-- Physical-image version of the full-restoration certificate, with every
allocator boundary referring to actual renamed execution. -/
def RenamedFullCertificate (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (m : List Bool) (s : State) : Prop :=
  runWithTape (renamedEndpointSlot e p k slots E) m k s=s ∧
  RenamedEndpointResources e p k slots E ∧
  ((walkExitArena walkSeedArena slots).renamed e).release
    ((closerPayloads (walkExitBank walkSeedBank slots)).toFinset.image e.equiv)
    (renamedEndpointClosed e p k slots m s).basis=some ((authorClosedArena slots).renamed e) ∧
  ((authorClosedArena slots).renamed e).Ready (renamedEndpointClosed e p k slots m s).basis ∧
  (∃ qs : Finset Wire, ∃ during : Arena,
    qs⊆arenaWires\((authorClosedArena slots).renamed e).live ∧
    ((authorClosedArena slots).renamed e).reserve qs=some during ∧
    recordedWires (renameRecordedProgram e.equiv E)⊆during.live ∧
    during.release qs (renamedEndpointAfter e p k slots E m s).basis=some ((authorClosedArena slots).renamed e) ∧
    qs.card≤315 ∧ during.live.card≤935) ∧
  ((authorClosedArena slots).renamed e).Ready (renamedEndpointAfter e p k slots E m s).basis ∧
  ((authorClosedArena slots).renamed e).reserve ((closerPayloads (walkExitBank walkSeedBank slots)).toFinset.image e.equiv)=
    some ((walkExitArena walkSeedArena slots).renamed e)

attribute [local irreducible] seededAuthorWalkProgram seededAuthorWalkReverse closerProgram actualHistoryDecoder

theorem endpointSlotCertificate_renamed (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (m : List Bool) (s : State)
    (h : EndpointSlotCertificate p k slots E m (pullState e.equiv s)) :
    RenamedFullCertificate e p k slots E m s := by
  rcases h with ⟨restored,wf,bound,_,_,closedRelease,closedReady,borrow,afterReady,reclaim⟩
  have closed := renamedEndpointClosed_pull e p k slots m s
  have closedBasis : (fun q => (renamedEndpointClosed e p k slots m s).basis (e.equiv q)) =
      (endpointClosed p k slots m (pullState e.equiv s)).basis := congrArg State.basis closed
  have after := renamedEndpointAfter_pull e p k slots E m s
  have afterBasis : (fun q => (renamedEndpointAfter e p k slots E m s).basis (e.equiv q)) =
      (endpointAfter p k slots E m (pullState e.equiv s)).basis := congrArg State.basis after
  have rel := Arena.renamed_release (walkExitArena walkSeedArena slots) (authorClosedArena slots)
    (closerPayloads (walkExitBank walkSeedBank slots)).toFinset e (renamedEndpointClosed e p k slots m s).basis
    (by simpa only [←closedBasis] using closedRelease)
  have cr := (Arena.renamed_ready (authorClosedArena slots) e (renamedEndpointClosed e p k slots m s).basis).mpr
    (by simpa only [←closedBasis] using closedReady)
  have ar := (Arena.renamed_ready (authorClosedArena slots) e (renamedEndpointAfter e p k slots E m s).basis).mpr
    (by simpa only [←afterBasis] using afterReady)
  refine ⟨runWithTape_permutation_restore e.equiv _ m k s restored,
    renamedEndpoint_resources e p k slots E wf bound,rel,cr,?_,ar,Arena.renamed_reserve _ _ _ e reclaim⟩
  obtain ⟨qs,during,free,reserved,support,released,cap,peak⟩ := borrow
  -- Keep the original witnesses' images so their exact capacities transport.
  refine ⟨qs.image e.equiv,during.renamed e,?_,Arena.renamed_reserve _ _ _ e reserved,?_,?_,?_,?_⟩
  · intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    have hh := Finset.mem_sdiff.mp (free ha)
    refine Finset.mem_sdiff.mpr ⟨(e.preserves a).mpr hh.1,?_⟩
    simpa only [Arena.renamed,Finset.mem_image,e.equiv.injective.eq_iff,exists_eq_right] using hh.2
  · rw [renameRecorded_wires]
    exact Finset.image_subset_image support
  · apply Arena.renamed_release
    simpa only [←afterBasis] using released
  · simpa only [Finset.card_image_of_injective _ e.equiv.injective] using cap
  · simpa only [Arena.renamed_card] using peak

end ECDSAAdd.Arithmetic.Paper935
