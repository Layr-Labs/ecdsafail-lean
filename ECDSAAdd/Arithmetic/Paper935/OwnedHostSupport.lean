import ECDSAAdd.Arithmetic.Paper935.WalkExternalSupport
import ECDSAAdd.Arithmetic.Paper935.EndpointSlotResources

namespace ECDSAAdd.Arithmetic.Paper935

attribute [local irreducible] seededAuthorWalkProgram seededAuthorWalkReverse closerProgram actualHistoryDecoder

private theorem seed_aHost_away (p : Nat) (q : Wire) (hq : q∈aHost) :
    q∉wires (seedRows p) ∧ q∉wires seedWalkMetadata := by
  have bounds : 512≤q ∧ q<768 := Finset.mem_Ico.mp hq
  constructor
  · intro hh
    have hm := seed_support p hh
    simp only [seedBorrowed,yHost,Finset.mem_union,Finset.mem_Ico] at hm
    dsimp only [Wire] at *
    omega
  · simp only [seedWalkMetadata,wires,Instr.wires,Finset.union_empty,Finset.mem_singleton]
    dsimp only [Wire] at *
    omega

/-- The actual seeded walk, endpoint closer, uncloser and actual reverse have
no address in the retained 256-bit host. No gate-semantics oracle is assumed. -/
theorem authorWalk_aHost_support (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    Disjoint aHost (recordedWires (seededAuthorWalkProgram p slots ++
      embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p) ++
      embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
      seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots)) := by
  apply Finset.disjoint_left.mpr
  intro q hq
  have walk := compileAuthorWalk_aHost_external slots compiled p ordinal q hq
  have seed := seed_aHost_away p q hq
  have closer : q∉wires (closerProgram (walkExitBank walkSeedBank slots) p) :=
    fun h => walk.2.1 (List.mem_toFinset.mp (closerProgram_support _ _ h))
  simp only [recordedWires_append,seededAuthorWalkProgram,seededAuthorWalkReverse,
    recordedWires_append,embedRecorded_wires,seedWalk,unseedWalk,wires_append,wires_reverse,
    Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨seed.1,seed.2⟩,walk.2.2.1⟩,closer⟩,closer⟩,walk.2.2.2,seed.2,seed.1⟩

/-- The whole return stream leaves an owned-host output untouched. -/
theorem authorReturn_aHost_support (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    Disjoint aHost (recordedWires (embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
      seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots)) := by
  apply Finset.disjoint_left.mpr
  intro q hq hh
  apply Finset.disjoint_left.mp (authorWalk_aHost_support p ordinal slots compiled) hq
  simp only [recordedWires_append,Finset.mem_union] at hh ⊢
  rcases hh with hh|hh
  · exact Or.inl (Or.inr hh)
  · exact Or.inr hh

/-- Closing the endpoint frees row payloads, never the retained host. -/
theorem authorClosedArena_aHost (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    aHost⊆(authorClosedArena slots).live := by
  intro q hq
  have walk := compileAuthorWalk_aHost_external slots compiled 0 0 q hq
  refine Finset.mem_sdiff.mpr ⟨walk.1,?_⟩
  intro hp
  apply walk.2.1
  simp only [closerPayloads,List.mem_toFinset,List.mem_append] at hp
  simp only [WindowBank.rows,WindowRow.wires,List.flatMap_cons,List.flatMap_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hp with (hp|hp)|hp
  · exact Or.inl (Or.inl hp)
  · exact Or.inr (Or.inl (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))

theorem aHost_output_card (O : Finset Wire) (owned : O⊆aHost) : O.card≤256 := by
  have hc := Finset.card_le_card owned
  simpa [aHost] using hc

end ECDSAAdd.Arithmetic.Paper935
