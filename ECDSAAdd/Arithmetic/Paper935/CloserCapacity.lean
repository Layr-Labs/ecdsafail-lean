import ECDSAAdd.Arithmetic.Paper935.CloserRelease
import ECDSAAdd.Arithmetic.Paper935.ExitOwned
import ECDSAAdd.Arithmetic.Paper935.ExitWidths
import ECDSAAdd.Arithmetic.Paper935.ExitCapacity

namespace ECDSAAdd.Arithmetic.Paper935

def authorClosedArena (slots : List HistoricalSlot) : Arena :=
  (walkExitArena walkSeedArena slots).retireSet (closerPayloads (walkExitBank walkSeedBank slots)).toFinset

theorem compileAuthorWalk_closed_card (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    (authorClosedArena slots).live.card=620 := by
  have widths := compileAuthorWalk_exit_widths slots compiled
  rw [authorClosedArena,closer_retired_card _ _ (compileAuthorWalk_exit_owned slots compiled),
    compileAuthorWalk_exit_card slots compiled,widths.1,widths.2.1,widths.2.2.2]
  rfl

theorem compileAuthorWalk_closed_free (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    (arenaWires \ (authorClosedArena slots).live).card=315 := by
  rw [Finset.card_sdiff_of_subset (authorClosedArena slots).bounded,
    compileAuthorWalk_closed_card slots compiled]
  simp [arenaWires]

end ECDSAAdd.Arithmetic.Paper935
