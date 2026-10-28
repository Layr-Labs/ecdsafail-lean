import ECDSAAdd.Arithmetic.MappedCompressedTailFrame
import ECDSAAdd.Arithmetic.MappedCompressedPacketCorrect
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run

private theorem getD_member {α : Type} (ls : List α) (i : Nat) (fallback : α)
    (hi : i < ls.length) : ls.getD i fallback ∈ ls := by
  induction ls generalizing i with
  | nil => simp at hi
  | cons a ls ih =>
    cases i with
    | zero => simp
    | succ i =>
      have bound : i < ls.length := by simpa using hi
      exact List.mem_cons_of_mem a (ih i bound)

theorem layout_of_subset (w : Nat → Wire) (b sign eff : Wire)
    (ls full : List MixedTranscriptLetter) (subset : ∀l∈ls,l∈full)
    (hf : MixedTranscriptReplayLayout w b sign eff full) :
    MixedTranscriptReplayLayout w b sign eff ls :=
  fun l hl => hf l (subset l hl)

/-- Full-tape layout supplies the actual stored unit constants and control
coordinates at every valid original round. -/
theorem mixedTape_getD_layout (w : Nat → Wire) (b sign eff : Wire)
    (hf : MixedTranscriptReplayLayout w b sign eff (mixedTranscriptTape w))
    (i : Nat) (hi : i < 512) :
    MixedTranscriptFieldLayout w b
      ((mixedTranscriptTape w).getD i ((0,0),(false,false))).1.1
      ((mixedTranscriptTape w).getD i ((0,0),(false,false))).1.2 sign eff := by
  apply hf
  apply getD_member
  simpa only [mixedTranscriptTape_length] using hi

theorem packetLetters_subset (j : Nat) (hj : j < 170) :
    ∀l∈packetLetters j,l∈mixedTranscriptTape base := by
  intro l hl
  simp only [packetLetters,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl|rfl
  all_goals
    apply getD_member
    rw [mixedTranscriptTape_length]
    omega

/-- All170 packet contracts are consequences of one original full layout. -/
theorem packet_layouts (b sign eff : Wire)
    (hf : MixedTranscriptReplayLayout base b sign eff (mixedTranscriptTape base)) :
    ∀j,j < 170 → MixedTranscriptReplayLayout base b sign eff (packetLetters j) := by
  intro j hj
  exact layout_of_subset base b sign eff _ _ (packetLetters_subset j hj) hf

theorem tailLetters_subset : ∀l∈tailLetters,l∈mixedTranscriptTape base := by
  intro l hl
  simp only [tailLetters,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl
  all_goals
    apply getD_member
    rw [mixedTranscriptTape_length]
    decide

/-- The last two raw cells need no separately assumed field layout. -/
theorem tail_layout (b sign eff : Wire)
    (hf : MixedTranscriptReplayLayout base b sign eff (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base b sign eff tailLetters :=
  layout_of_subset base b sign eff _ _ tailLetters_subset hf

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mixedTape_getD_layout
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.packet_layouts
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.tail_layout
