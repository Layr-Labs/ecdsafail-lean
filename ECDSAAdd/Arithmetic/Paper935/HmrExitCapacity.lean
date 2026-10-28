import ECDSAAdd.Arithmetic.Paper935.ExitCapacityWidth
import ECDSAAdd.Arithmetic.Paper935.HmrWalkStaticTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- Kernel evaluation of only the public scalar schedule. -/
theorem hmrExitLiveCount : exitLiveCountWidth 4 793 initialWindow 0 authorHistoricalRequests=906 := by
  decide +kernel

attribute [local irreducible] exitLiveCountWidth compileHistoricalWalkWidth historicalBudgetsWidth

theorem compileHmrWalk_exit_card (slots : List HistoricalSlot) (compiled : compileHmrWalk=some slots) :
    (walkExitArena hmrWalkSeedArena slots).live.card=906 := by
  have h := compileHistoricalWalkWidth_exit_card 4 hmrWalkRegisters 6 hmrWalkSeedArena walkSeedBank []
    authorHistoricalRequests slots compiled (by decide) hmrWalkSeed_distinct hmrWalkSeed_owned
    (by simpa only [hmrWalkSeed_card,hmrWalkSeed_widths,List.length_nil] using hmrHistoricalBudgets)
  simpa only [hmrWalkSeed_card,hmrWalkSeed_widths,List.length_nil,hmrExitLiveCount] using h

theorem compileHmrWalk_free_card (slots : List HistoricalSlot) (compiled : compileHmrWalk=some slots) :
    (arenaWires \ (walkExitArena hmrWalkSeedArena slots).live).card=29 := by
  rw [Finset.card_sdiff_of_subset (walkExitArena hmrWalkSeedArena slots).bounded,
    compileHmrWalk_exit_card slots compiled]
  simp [arenaWires]

/-- Preserving the complete exit live set rules out a fresh 256-wire output
plus 17 distinct auxiliary wires. This does not rule out reversible reuse. -/
theorem compileHmrWalk_no_fresh_output (slots : List HistoricalSlot) (compiled : compileHmrWalk=some slots)
    (fresh : Finset Wire) (inside : fresh⊆arenaWires)
    (separate : Disjoint fresh (walkExitArena hmrWalkSeedArena slots).live) : fresh.card≤29 := by
  have sub : fresh⊆arenaWires \ (walkExitArena hmrWalkSeedArena slots).live := by
    intro q h
    exact Finset.mem_sdiff.mpr ⟨inside h,fun bad => Finset.disjoint_left.mp separate h bad⟩
  have h := Finset.card_le_card sub
  rw [compileHmrWalk_free_card slots compiled] at h
  exact h

end ECDSAAdd.Arithmetic.Paper935
