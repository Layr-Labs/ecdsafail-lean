import ECDSAAdd.Arithmetic.EndpointSwapTrimProof
import ECDSAAdd.Arithmetic.TerminalMappedReplayPayload
import ECDSAAdd.Arithmetic.MappedCompressedReplayCounts

namespace ECDSAAdd.Arithmetic.PenultimateSwapIdentity
open Secp256k1 MappedCompressed
attribute [local irreducible] run mixedTranscriptUnitTrace indexedLetters trimLetters

/-- Proposed raw510 replacement: only the S-selected swap/window disappears.
The incumbent arithmetic, G selection and all original field ports remain. -/
def cell (divide : Bool) : Program :=
  let unit := mixedTranscriptUnitTrace.getD 510 (false,false)
  if divide then EndpointSwapTrim.forward id 2400 510 2409 unit.1
  else EndpointSwapTrim.inverse id 2400 510 2409 unit.1

theorem cell_counts (divide : Bool) :
    toffoliCount (cell divide)=(if divide then 1023 else 1024) ∧ measurementCount (cell divide)=1024 := by
  have h := EndpointSwapTrim.counts id 2400 510 2409
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  cases divide <;> simp only [cell,Bool.false_eq_true,if_false,if_true]
  · exact h.2.2
  · exact ⟨h.1,h.2.1⟩

theorem cell_saving (divide : Bool) :
    toffoliCount (logicalCell divide 510)=toffoliCount (cell divide)+257 ∧
    measurementCount (logicalCell divide 510)=measurementCount (cell divide)+1 := by
  have old := logicalCell_counts divide 510
  have fresh := cell_counts divide
  rw [old.1,old.2,fresh.1,fresh.2]
  cases divide <;> norm_num

def penultimatePayload (origin : BasisState) (Y : Fp) : Fp×Fp :=
  skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (indexedLetters 0 510)) (2*Y,0)

private theorem trimLetters_penultimate :
    trimLetters=indexedLetters 0 510++[tapeLetter 510] := by
  have last : indexedLetters 510 1=[tapeLetter 510] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  have split := indexedLetters_append 0 510 1
  rw [last] at split
  simpa only [Nat.zero_add,Nat.reduceAdd,trimLetters] using split

private theorem replay_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)

/-- Derived from the original512-trace contract, not a new terminal/input
assumption. The final forward swap acts on equal words for either S polarity. -/
theorem penultimate_half_dup (origin : BasisState) (x : Nat) (Y : Fp)
    (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    ((penultimatePayload origin Y).1+
      (if mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.1 (tapeLetter 510).2.1
        then (penultimatePayload origin Y).2 else -(penultimatePayload origin Y).2))/2=
      (penultimatePayload origin Y).2 := by
  have whole := trimLetters_quotient origin x Y hx0 hx trace
  rw [trimLetters_penultimate] at whole
  simp only [mixedTranscriptControls,List.map_append,List.map_cons,List.map_nil,
    replay_append,skywalkPayloadReplay] at whole
  apply EndpointSwapTrim.forward_dup_of_payload_equal
    (mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.1 (tapeLetter 510).2.1)
    (mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.2 (tapeLetter 510).2.2)
    (penultimatePayload origin Y).1 (penultimatePayload origin Y).2
  simpa only [penultimatePayload,mixedTranscriptControls] using
    (congrArg Prod.fst whole).trans (congrArg Prod.snd whole).symm

/- Caller bridge still required; this file does not claim whole-segment equivalence.
1. Forward: obtain the actual raw510 input EncodedFieldFrame from the modified
   firstGroup + remaining169 packet frames, with payload penultimatePayload.
   Rewrite tapeLetter510 to its concrete base510/base1538/unit controls.
   Apply accepted EndpointSwapTrim.forward_oldcell_eq using penultimate_half_dup.
2. Inverse: inverseEntryPrefix already gives EncodedFieldFrame Y Y; apply
   accepted EndpointSwapTrim.inverse_oldcell_eq before mappedGroups/firstGroup.
3. Both: extract the complete raw PairFrame/Env witness from EncodedFieldFrame,
   then transport the new program from base to allPlaced using the same zero-
   region allocation argument as trimCell_step. Prove its wire support is a
   subset of logicalCell510 and retain slots/whole1899 bound.
4. Rewrite terminalReplay's single raw510 cell only, compose independent record
   lists through converter suffixes, and inherit the existing full field spec.
   The raw511 omission and entry cancellation are unchanged; no double credit.
   New field segment target:657560T/525980MX, saving257T/1MX in each direction.
-/
end ECDSAAdd.Arithmetic.PenultimateSwapIdentity
#print axioms ECDSAAdd.Arithmetic.PenultimateSwapIdentity.cell_counts
#print axioms ECDSAAdd.Arithmetic.PenultimateSwapIdentity.cell_saving
#print axioms ECDSAAdd.Arithmetic.PenultimateSwapIdentity.penultimate_half_dup
