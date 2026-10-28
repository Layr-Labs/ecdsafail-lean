import ECDSAAdd.Arithmetic.Paper935.OwnedOutputSlot

namespace ECDSAAdd.Arithmetic.Paper935

/-- A temporary-only endpoint transaction restores arena readiness from actual
execution and release. Existing owned output wires are not reserved again. -/
theorem endpointOwnedOutputBorrow_ready (A : Arena) (O : Finset Wire) (E : RecordedProgram)
    (s : State) (m : List Bool) (k : Nat) (ready : A.Ready s.basis) (owned : O⊆A.live)
    (borrow : EndpointBorrow A E (runWithTape E m k s)) :
    ∃ temporary : Finset Wire, ∃ during : Arena,
      temporary⊆arenaWires\A.live ∧ A.reserve temporary=some during ∧
      recordedWires E⊆during.live ∧ during.release temporary (runWithTape E m k s).basis=some A ∧
      Disjoint O temporary ∧ A.Ready (runWithTape E m k s).basis ∧ during.live.card≤935 ∧
      A.live.card+temporary.card=during.live.card := by
  obtain ⟨temporary,during,free,reserved,support,released⟩ := borrow
  have apart : Disjoint O temporary := Finset.disjoint_left.mpr (by
    intro q hq ht
    exact (Finset.mem_sdiff.mp (free ht)).2 (owned hq))
  have dready := (A.reserve_ready during temporary s.basis ready reserved).1
  have after : during.Ready (runWithTape E m k s).basis := by
    intro q hq hn
    rw [runWithTape_preserves_outside E m k s q (fun h => hn (support h))]
    exact dready q hq hn
  have live : during.live=A.live∪temporary := by
    unfold Arena.reserve at reserved
    split at reserved
    next valid => cases reserved; rfl
    next invalid => simp at reserved
  have fresh := (A.reserve_success temporary).mp ⟨during,reserved⟩
  refine ⟨temporary,during,free,reserved,support,released,apart,
    during.release_ready A temporary _ after released,during.peak_bound,?_⟩
  rw [live,Finset.card_union_of_disjoint fresh.2]

/-- Output occupies existing live host storage. Its 256-site bound is separate
from the 315 temporary sites available after closing the endpoint. -/
theorem endpointOwnedOutputBorrow_capacity (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (O : Finset Wire) (host : O⊆aHost) (E : RecordedProgram) (s : State) (m : List Bool) (k : Nat)
    (ready : (authorClosedArena slots).Ready s.basis)
    (borrow : EndpointBorrow (authorClosedArena slots) E (runWithTape E m k s)) :
    O.card≤256 ∧ O⊆(authorClosedArena slots).live ∧
    ∃ temporary : Finset Wire, ∃ during : Arena,
      temporary⊆arenaWires\(authorClosedArena slots).live ∧
      (authorClosedArena slots).reserve temporary=some during ∧ recordedWires E⊆during.live ∧
      during.release temporary (runWithTape E m k s).basis=some (authorClosedArena slots) ∧
      Disjoint O temporary ∧ (authorClosedArena slots).Ready (runWithTape E m k s).basis ∧
      temporary.card≤315 ∧ during.live.card≤935 ∧
      during.live.card=620+temporary.card := by
  have owned := host.trans (authorClosedArena_aHost slots compiled)
  obtain ⟨temporary,during,free,reserved,support,released,apart,after,peak,card⟩ :=
    endpointOwnedOutputBorrow_ready (authorClosedArena slots) O E s m k ready owned borrow
  have live := compileAuthorWalk_closed_card slots compiled
  refine ⟨aHost_output_card O host,owned,temporary,during,free,reserved,support,released,apart,after,?_,peak,?_⟩
  all_goals omega

end ECDSAAdd.Arithmetic.Paper935
