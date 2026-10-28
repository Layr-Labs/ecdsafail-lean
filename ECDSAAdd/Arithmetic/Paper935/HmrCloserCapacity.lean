import ECDSAAdd.Arithmetic.Paper935.CloserRelease
import ECDSAAdd.Arithmetic.Paper935.HmrExitOwned
import ECDSAAdd.Arithmetic.Paper935.HmrExitWidths
import ECDSAAdd.Arithmetic.Paper935.HmrExitCapacity

namespace ECDSAAdd.Arithmetic.Paper935

def hmrClosedArena (slots : List HistoricalSlot) : Arena :=
  (walkExitArena hmrWalkSeedArena slots).retireSet (closerPayloads (walkExitBank walkSeedBank slots)).toFinset

theorem compileHmrWalk_closed_card (slots : List HistoricalSlot) (compiled : compileHmrWalk=some slots) :
    (hmrClosedArena slots).live.card=619 := by
  have widths := compileHmrWalk_exit_widths slots compiled
  rw [hmrClosedArena,closer_retired_card _ _ (compileHmrWalk_exit_owned slots compiled),
    compileHmrWalk_exit_card slots compiled,widths.1,widths.2.1,widths.2.2.2]
  rfl

theorem compileHmrWalk_closed_free (slots : List HistoricalSlot) (compiled : compileHmrWalk=some slots) :
    (arenaWires \ (hmrClosedArena slots).live).card=316 := by
  rw [Finset.card_sdiff_of_subset (hmrClosedArena slots).bounded,
    compileHmrWalk_closed_card slots compiled]
  simp [arenaWires]

end ECDSAAdd.Arithmetic.Paper935
