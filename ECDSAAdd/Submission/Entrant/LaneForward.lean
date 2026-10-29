import ECDSAAdd.Arithmetic.PenultimateMappedForward

/-! Lane A forward replay: the public output frame of the division replay
alone.  From the centered pair (Y,0) the 170 packets reach the penultimate
payload; the swap-free cell 510 equals the logical cell 510 there, whose
output is the full trim-letter payload (Y/x,Y/x) (or (Y,Y) when inactive). -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.PenultimateMapped.LaneA
open Secp256k1 MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run groupsPayload indexedLetters packetLetters
  mixedTranscriptTape mixedTranscriptUnitTrace mappedGroups logicalCell
  EntryMappedFieldSegmentTrim.firstGroup measurementCount
  PenultimateSwapIdentity.cell fieldSegment
  baseGroups converterPair copyPairAt

private theorem replay_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)

private theorem packet_indexed (j : Nat) : packetLetters j=indexedLetters (3*j) 3 := by
  simp [packetLetters,indexedLetters,tapeLetter,List.range_succ]

private theorem groups_succ (origin : BasisState) (j n : Nat) (Q : Fp×Fp) :
    groupsPayload true origin j (n+1) Q=groupsPayload true origin (j+1) n
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters j)) Q) := by
  simp only [groupsPayload,if_true,Bool.not_true,directionalPayload,Bool.false_eq_true,if_false]

/-- Abstract packet recursion avoids expanding the concrete170-packet list. -/
theorem forward_groups_payload (j n : Nat) (origin : BasisState) (Q : Fp×Fp) :
    groupsPayload true origin j n Q=
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
        (indexedLetters (3*j) (3*n))) Q := by
  induction n generalizing j Q with
  | zero => simp only [groupsPayload,indexedLetters,Nat.mul_zero,List.range_zero,List.map_nil,
      mixedTranscriptControls,skywalkPayloadReplay]
  | succ n ih =>
    have len : 3*(n+1)=3+3*n := by omega
    have start : 3*(j+1)=3*j+3 := by omega
    rw [groups_succ,len,indexedLetters_append]
    simp only [mixedTranscriptControls,List.map_append,replay_append,ih,start,←packet_indexed]

private theorem first_rest_payload (origin : BasisState) (Y : Fp) :
    groupsPayload true origin 1 169
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0))=
      PenultimateSwapIdentity.penultimatePayload origin Y := by
  have start : groupsPayload true origin 0 170 (2*Y,0)=
      groupsPayload true origin 1 169
        (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)) :=
    groups_succ origin 0 169 (2*Y,0)
  have generic : groupsPayload true origin 0 170 (2*Y,0)=
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
        (indexedLetters (3*0) (3*170))) (2*Y,0) :=
    forward_groups_payload 0 170 origin (2*Y,0)
  have zero : 3*0=0 := by decide
  have length : 3*170=510 := by decide
  have lettersEq : indexedLetters (3*0) (3*170)=indexedLetters 0 510 :=
    congrArg₂ indexedLetters zero length
  have lifted : skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
      (indexedLetters (3*0) (3*170))) (2*Y,0)=
        skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
          (indexedLetters 0 510)) (2*Y,0) :=
    congrArg (fun ls : List MixedTranscriptLetter =>
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) ls) (2*Y,0)) lettersEq
  have fold : skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
      (indexedLetters 0 510)) (2*Y,0)=PenultimateSwapIdentity.penultimatePayload origin Y := by
    unfold PenultimateSwapIdentity.penultimatePayload
    rfl
  exact start.symm.trans (generic.trans (lifted.trans fold))



private theorem trimLetters_penultimate :
    trimLetters=indexedLetters 0 510++[tapeLetter 510] := by
  have last : indexedLetters 510 1=[tapeLetter 510] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  have split := indexedLetters_append 0 510 1
  rw [last] at split
  simpa only [Nat.zero_add,Nat.reduceAdd,trimLetters] using split

theorem replay_forward_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin Y 0 s) :
    let Z := fieldResult true origin x Y
    (run (replay true) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Z Z (run (replay true) m s) := by
  let Z := fieldResult true origin x Y
  let A := PenultimateSwapIdentity.penultimatePayload origin Y
  let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
  let P : State → State → Prop := fun initial out => EncodedFieldFrame base (base 2409) origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin Z Z out
  have all := run_three_states (EntryMappedFieldSegmentTrim.firstGroup true) (mappedGroups true 1 169)
    (renameProgram allPlaced (PenultimateSwapIdentity.cell true)) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have b := EntryMappedFieldSegmentTrim.firstGroup_forward_step hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal Y initial m1 hin
      rw [h1] at b
      have frame1 : EncodedFieldFrame base (base 2409) origin Q.1 Q.2 s1 := b.2
      have cAll := mappedGroups_frame true 1 169 (by decide) hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf)
        origin hg0 hs0 env legal Q.1 Q.2 s1 m2 frame1
      have cPhase : (run (mappedGroups true 1 169) m2 s1).phase=s1.phase := cAll.2.1
      have cFrame : EncodedFieldFrame base (base 2409) origin
          (groupsPayload true origin 1 169 (Q.1,Q.2)).1
          (groupsPayload true origin 1 169 (Q.1,Q.2)).2
          (run (mappedGroups true 1 169) m2 s1) := cAll.2.2
      rw [h2] at cPhase cFrame
      have payload : groupsPayload true origin 1 169 (Q.1,Q.2)=A := by
        change groupsPayload true origin 1 169 Q=A
        exact first_rest_payload origin Y
      rw [payload] at cFrame
      have cellEq := PenultimateMappedCellProof.forward_cell_eq hn hlo ho hp hf
        origin hg0 hs0 env legal A.1 A.2 s2 m3 m3 cFrame
        (PenultimateSwapIdentity.penultimate_half_dup origin x Y hx0 hx trace)
      have step := trimCell_step true hn hlo ho hp hf origin hg0 hs0 env legal A.1 A.2 s2 m3 cFrame
      rw [←cellEq,h3] at step
      have whole := trimLetters_quotient origin x Y hx0 hx trace
      rw [trimLetters_penultimate] at whole
      simp only [mixedTranscriptControls,List.map_append,replay_append] at whole
      have pay : directionalPayload (!true) (mixedTranscriptControls origin (base 2400) [tapeLetter 510])
          (A.1,A.2)=(Z,Z) := by
        simp only [directionalPayload,Bool.not_true,Bool.false_eq_true,if_false]
        change skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) [tapeLetter 510])
          (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (indexedLetters 0 510)) (2*Y,0))=_
        simp only [mixedTranscriptControls]
        rw [whole]
        simp only [Z,fieldResult,if_true]
      rw [pay] at step
      exact ⟨step.2.1.trans (cPhase.trans b.1),step.2.2⟩) s m input
  have join : replay true=EntryMappedFieldSegmentTrim.firstGroup true++(mappedGroups true 1 169++
      renameProgram allPlaced (PenultimateSwapIdentity.cell true)) := by
    simp only [replay,if_true,List.append_assoc]
  rw [join]
  exact all

end ECDSAAdd.Arithmetic.PenultimateMapped.LaneA
