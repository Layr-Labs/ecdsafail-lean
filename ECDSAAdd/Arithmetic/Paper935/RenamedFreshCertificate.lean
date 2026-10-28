import ECDSAAdd.Arithmetic.Paper935.RenamedOwnedCertificate

namespace ECDSAAdd.Arithmetic.Paper935

def RenamedFreshOutputCertificate (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State) : Prop :=
  runWithTape (renamedEndpointSlot e p k slots E) m k s=withOutput (O.image e.equiv) v s ∧
  RenamedEndpointResources e p k slots E ∧ (O.image e.equiv).card≤28 ∧
  (∃ retained : Arena, ∃ temporary : Finset Wire, ∃ during : Arena,
    ((authorClosedArena slots).renamed e).reserve (O.image e.equiv)=some retained ∧
    retained.reserve temporary=some during ∧ recordedWires (renameRecordedProgram e.equiv E)⊆during.live ∧
    during.release temporary (renamedEndpointAfter e p k slots E m s).basis=some retained ∧
    O.image e.equiv⊆retained.live ∧ Disjoint (O.image e.equiv) temporary ∧
    retained.Ready (renamedEndpointAfter e p k slots E m s).basis ∧
    (O.image e.equiv).card+temporary.card≤315 ∧ during.live.card≤935) ∧
  (∀q∈arenaWires,q∉(seedBefore.live∪O).image e.equiv →
    (runWithTape (renamedEndpointSlot e p k slots E) m k s).basis q=false)

attribute [local irreducible] seededAuthorWalkProgram seededAuthorWalkReverse closerProgram actualHistoryDecoder

theorem endpointOutputCertificate_renamed (e : ArenaPermutation) (p k : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State)
    (h : EndpointOutputCertificate p k slots E O (fun q => v (e.equiv q)) m (pullState e.equiv s)) :
    RenamedFreshOutputCertificate e p k slots E O v m s := by
  rcases h with ⟨result,wf,bound,_,_,ocap,borrow,finalReady⟩
  have after := renamedEndpointAfter_pull e p k slots E m s
  have afterBasis : (fun q => (renamedEndpointAfter e p k slots E m s).basis (e.equiv q)) =
      (endpointAfter p k slots E m (pullState e.equiv s)).basis := congrArg State.basis after
  refine ⟨runWithTape_permutation_output e.equiv _ O v m k s result,
    renamedEndpoint_resources e p k slots E wf bound,?_,?_,?_⟩
  · simpa only [Finset.card_image_of_injective _ e.equiv.injective] using ocap
  · obtain ⟨retained,qs,during,resO,reserved,support,released,owned,apart,ready,cap,peak⟩ := borrow
    refine ⟨retained.renamed e,qs.image e.equiv,during.renamed e,
      Arena.renamed_reserve _ _ _ e resO,Arena.renamed_reserve _ _ _ e reserved,?_,?_,
      Finset.image_subset_image owned,(e.disjoint_image O qs).mpr apart,?_,?_,?_⟩
    · rw [renameRecorded_wires]
      exact Finset.image_subset_image support
    · apply Arena.renamed_release
      simpa only [←afterBasis] using released
    · apply (Arena.renamed_ready _ e _).mpr
      simpa only [←afterBasis] using ready
    · simpa only [Finset.card_image_of_injective _ e.equiv.injective] using cap
    · simpa only [Arena.renamed_card] using peak
  · have clean := runWithTape_permutation_clean e.equiv (endpointSlotProgram p k slots E)
      arenaWires (seedBefore.live∪O) m k s finalReady
    rw [e.image_arena] at clean
    exact clean

end ECDSAAdd.Arithmetic.Paper935
