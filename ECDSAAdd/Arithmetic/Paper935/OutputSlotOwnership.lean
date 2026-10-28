import ECDSAAdd.Arithmetic.Paper935.OutputSlot

namespace ECDSAAdd.Arithmetic.Paper935

private theorem reserve_live (A B : Arena) (qs : Finset Wire) (h : A.reserve qs=some B) :
    B.live=A.live∪qs := by
  unfold Arena.reserve at h
  split at h
  next valid => cases h; rfl
  next invalid => simp at h

/-- The output remains owned after E: only temporary work is released. The
Ready invariant is derived from actual execution and support, not assumed. -/
theorem endpointOutputBorrow_ready (A : Arena) (O : Finset Wire) (E : RecordedProgram)
    (s : State) (m : List Bool) (k : Nat) (ready : A.Ready s.basis)
    (borrow : EndpointOutputBorrow A O E (runWithTape E m k s)) :
    ∃ retained : Arena, ∃ temporary : Finset Wire, ∃ during : Arena,
      A.reserve O=some retained ∧ temporary⊆arenaWires\retained.live ∧
      retained.reserve temporary=some during ∧ recordedWires E⊆during.live ∧
      during.release temporary (runWithTape E m k s).basis=some retained ∧
      O⊆retained.live ∧ Disjoint O temporary ∧
      retained.Ready (runWithTape E m k s).basis ∧ during.live.card≤935 ∧
      A.live.card+O.card+temporary.card=during.live.card := by
  obtain ⟨retained,temporary,during,hO,free,hT,support,released⟩ := borrow
  have ro := reserve_live A retained O hO
  have rt := reserve_live retained during temporary hT
  have owned : O⊆retained.live := by rw [ro]; exact Finset.subset_union_right
  have apart : Disjoint O temporary := Finset.disjoint_left.mpr (by
    intro q hq ht
    exact (Finset.mem_sdiff.mp (free ht)).2 (owned hq))
  have rready := (A.reserve_ready retained O s.basis ready hO).1
  have dready := (retained.reserve_ready during temporary s.basis rready hT).1
  have after : during.Ready (runWithTape E m k s).basis := by
    intro q hq hn
    rw [runWithTape_preserves_outside E m k s q (fun h => hn (support h))]
    exact dready q hq hn
  have roApart := (A.reserve_success O).mp ⟨retained,hO⟩
  have rtApart := (retained.reserve_success temporary).mp ⟨during,hT⟩
  refine ⟨retained,temporary,during,hO,free,hT,support,released,owned,apart,
    during.release_ready retained temporary _ after released,during.peak_bound,?_⟩
  rw [rt,Finset.card_union_of_disjoint rtApart.2,ro,Finset.card_union_of_disjoint roApart.2]

/-- Output plus temporary storage share the existing 315-site closed free
budget. The retained output is not counted as released workspace. -/
theorem endpointOutputBorrow_capacity (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (O : Finset Wire) (E : RecordedProgram) (s : State) (m : List Bool) (k : Nat)
    (ready : (authorClosedArena slots).Ready s.basis)
    (borrow : EndpointOutputBorrow (authorClosedArena slots) O E (runWithTape E m k s)) :
    ∃ retained : Arena, ∃ temporary : Finset Wire, ∃ during : Arena,
      (authorClosedArena slots).reserve O=some retained ∧
      retained.reserve temporary=some during ∧ recordedWires E⊆during.live ∧
      during.release temporary (runWithTape E m k s).basis=some retained ∧
      O⊆retained.live ∧ Disjoint O temporary ∧
      retained.Ready (runWithTape E m k s).basis ∧
      O.card+temporary.card≤315 ∧ during.live.card≤935 := by
  obtain ⟨retained,temporary,during,hO,_,hT,support,released,owned,apart,after,peak,card⟩ :=
    endpointOutputBorrow_ready (authorClosedArena slots) O E s m k ready borrow
  have live := compileAuthorWalk_closed_card slots compiled
  refine ⟨retained,temporary,during,hO,hT,support,released,owned,apart,after,?_,peak⟩
  omega

end ECDSAAdd.Arithmetic.Paper935
