import ECDSAAdd.Arithmetic.Paper935.RenamedFullCertificate

namespace ECDSAAdd.Arithmetic.Paper935

def RenamedOwnedOutputCertificate (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State) : Prop :=
  runWithTape (renamedEndpointSlot e p k slots E) m k s=withOutput (O.image e.equiv) v s ∧
  RenamedEndpointResources e p k slots E ∧
  (O.image e.equiv).card≤256 ∧ O.image e.equiv⊆((authorClosedArena slots).renamed e).live ∧
  (∃ temporary : Finset Wire, ∃ during : Arena,
    temporary⊆arenaWires\((authorClosedArena slots).renamed e).live ∧
    ((authorClosedArena slots).renamed e).reserve temporary=some during ∧
    recordedWires (renameRecordedProgram e.equiv E)⊆during.live ∧
    during.release temporary (renamedEndpointAfter e p k slots E m s).basis=some ((authorClosedArena slots).renamed e) ∧
    Disjoint (O.image e.equiv) temporary ∧
    ((authorClosedArena slots).renamed e).Ready (renamedEndpointAfter e p k slots E m s).basis ∧
    temporary.card≤315 ∧ during.live.card≤935 ∧ during.live.card=620+temporary.card) ∧
  (seedBefore.renamed e).Ready (runWithTape (renamedEndpointSlot e p k slots E) m k s).basis

attribute [local irreducible] seededAuthorWalkProgram seededAuthorWalkReverse closerProgram actualHistoryDecoder

theorem endpointOwnedOutputCertificate_renamed (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State)
    (h : EndpointOwnedOutputCertificate p k slots E O (fun q => v (e.equiv q)) m (pullState e.equiv s)) :
    RenamedOwnedOutputCertificate e p k slots E O v m s := by
  rcases h with ⟨result,wf,bound,_,_,ocap,owned,borrow,finalReady⟩
  have after := renamedEndpointAfter_pull e p k slots E m s
  have afterBasis : (fun q => (renamedEndpointAfter e p k slots E m s).basis (e.equiv q)) =
      (endpointAfter p k slots E m (pullState e.equiv s)).basis := congrArg State.basis after
  refine ⟨runWithTape_permutation_output e.equiv _ O v m k s result,
    renamedEndpoint_resources e p k slots E wf bound,?_,Finset.image_subset_image owned,?_,?_⟩
  · simpa only [Finset.card_image_of_injective _ e.equiv.injective] using ocap
  · obtain ⟨qs,during,free,reserved,support,released,apart,ready,cap,peak,card⟩ := borrow
    refine ⟨qs.image e.equiv,during.renamed e,?_,Arena.renamed_reserve _ _ _ e reserved,?_,?_,
      (e.disjoint_image O qs).mpr apart,?_,?_,?_,?_⟩
    · intro q hq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
      have hh := Finset.mem_sdiff.mp (free ha)
      refine Finset.mem_sdiff.mpr ⟨(e.preserves a).mpr hh.1,?_⟩
      simpa only [Arena.renamed,Finset.mem_image,e.equiv.injective.eq_iff,exists_eq_right] using hh.2
    · rw [renameRecorded_wires]
      exact Finset.image_subset_image support
    · apply Arena.renamed_release
      simpa only [←afterBasis] using released
    · apply (Arena.renamed_ready _ e _).mpr
      simpa only [←afterBasis] using ready
    · simpa only [Finset.card_image_of_injective _ e.equiv.injective] using cap
    · simpa only [Arena.renamed_card] using peak
    · simpa only [Arena.renamed_card,Finset.card_image_of_injective _ e.equiv.injective] using card
  · apply (Arena.renamed_ready _ e _).mpr
    have pull := runWithTape_rename e.equiv e.equiv.injective (endpointSlotProgram p k slots E) m k s
    have basis : (fun q => (runWithTape (renamedEndpointSlot e p k slots E) m k s).basis (e.equiv q)) =
        (runWithTape (endpointSlotProgram p k slots E) m k (pullState e.equiv s)).basis := congrArg State.basis pull
    rw [basis]
    exact finalReady

end ECDSAAdd.Arithmetic.Paper935
