import ECDSAAdd.Submission.Entrant.LaneITop

/-! The entry-trimmed replay with every field cell using the 256-wide fold. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
  CompressedFieldSupport EntryMappedFieldSegmentTrim
attribute [local irreducible] run logicalCell compressedHistoryEncode compressedHistoryDecode
  allGroupEncode mixedTranscriptUnitTrace

theorem replayI_sub (divide : Bool) : InstrSub (replayI divide) (PenultimateMapped.replay divide) := by
  have g := mappedGroupsI_sub divide 1 169 (by decide)
  cases divide <;> simp only [replayI,PenultimateMapped.replay,Bool.false_eq_true,if_false,if_true]
  · exact ((endI_sub false).append g).append (firstGroupI_sub false)
  · exact ((firstGroupI_sub true).append g).append (endI_sub true)

theorem replayI_counts (divide : Bool) :
    measurementCount (replayI divide)=measurementCount (PenultimateMapped.replay divide) ∧
    toffoliCount (replayI divide)+510=toffoliCount (PenultimateMapped.replay divide) := by
  have g := mappedGroupsI_counts divide 1 169 (by decide)
  have f := firstGroupI_counts divide
  have t := endI_counts divide
  cases divide <;> simp only [replayI,PenultimateMapped.replay,Bool.false_eq_true,if_false,if_true,
    measurementCount_append,toffoliCount_append] <;> constructor <;> omega

/-- Replay equality; the entry payload is the one both segments present. -/
theorem replayI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin Y (if divide then 0 else Y) s) :
    run (replayI divide) m s=run (PenultimateMapped.replay divide) m s := by
  have layouts := packet_layouts (base 2400) (base 2409) (base 2410) hf
  let E : Fp → Fp → State → Prop := fun X Y t => EncodedFieldFrame base (base 2409) origin X Y t
  cases divide
  · simp only [Bool.false_eq_true,if_false] at input
    have shapeI : replayI false=endI false ++ (mappedGroupsI false 1 169 ++ firstGroupI false) := by
      simp only [replayI,Bool.false_eq_true,if_false,List.append_assoc]
    have shapeO : PenultimateMapped.replay false=renameProgram allPlaced (PenultimateSwapIdentity.cell false) ++
        (mappedGroups false 1 169 ++ firstGroup false) := by
      simp only [PenultimateMapped.replay,Bool.false_eq_true,if_false,List.append_assoc]
    rw [shapeI,shapeO]
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s m (endI_counts false).1
      (fun r => endI_eq false hn hlo ho hp hf origin hg0 hs0 env Y Y s r input)
      (fun r => by
        rw [PenultimateMappedCellProof.inverse_cell_eq hn hlo ho hp hf origin hg0 hs0 env legal Y s r r input]
        exact ⟨_,_,(trimCell_step false hn hlo ho hp hf origin hg0 hs0 env legal Y Y s r input).2.2⟩)
    rintro s3 m3 ⟨X3,Y3,c3⟩
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s3 m3
      (mappedGroupsI_counts false 1 169 (by decide)).1
      (fun r => mappedGroupsI_eq false 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal _ _ s3 r c3)
      (fun r => ⟨_,_,(mappedGroups_frame false 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal
        _ _ s3 r c3).2.2⟩)
    rintro s4 m4 ⟨X4,Y4,c4⟩
    exact firstGroupI_eq false hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal _ _ s4 _ c4
  · simp only [if_true] at input
    have shapeI : replayI true=firstGroupI true ++ (mappedGroupsI true 1 169 ++ endI true) := by
      simp only [replayI,if_true,List.append_assoc]
    have shapeO : PenultimateMapped.replay true=firstGroup true ++ (mappedGroups true 1 169 ++
        renameProgram allPlaced (PenultimateSwapIdentity.cell true)) := by
      simp only [PenultimateMapped.replay,if_true,List.append_assoc]
    rw [shapeI,shapeO]
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s m (firstGroupI_counts true).1
      (fun r => firstGroupI_eq true hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal Y 0 s r input)
      (fun r => ⟨_,_,(firstGroup_forward_step hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal
        Y s r input).2⟩)
    rintro s2 m2 ⟨X2,Y2,c2⟩
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s2 m2
      (mappedGroupsI_counts true 1 169 (by decide)).1
      (fun r => mappedGroupsI_eq true 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal _ _ s2 r c2)
      (fun r => ⟨_,_,(mappedGroups_frame true 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal
        _ _ s2 r c2).2.2⟩)
    rintro s3 m3 ⟨X3,Y3,c3⟩
    exact endI_eq true hn hlo ho hp hf origin hg0 hs0 env _ _ s3 _ c3

end ECDSAAdd.Entrant.LaneI
