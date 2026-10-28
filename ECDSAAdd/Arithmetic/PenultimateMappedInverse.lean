import ECDSAAdd.Arithmetic.PenultimateMappedProgram
import ECDSAAdd.Arithmetic.PenultimateMappedCellProof

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.PenultimateMapped
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run measurementCount logicalCell mappedGroups

private def oldHead : Program := renameProgram allPlaced (logicalCell false 510)
private def newHead : Program := renameProgram allPlaced (PenultimateSwapIdentity.cell false)
private def commonSuffix : Program := mappedGroups false 1 169 ++
  EntryMappedFieldSegmentTrim.firstGroup false

private theorem replay_inverse_join : replay false=newHead++commonSuffix := by
  simp only [replay,newHead,commonSuffix,Bool.false_eq_true,if_false,List.append_assoc]

private theorem old_replay_inverse_join :
    EntryMappedFieldSegmentTrim.terminalReplay false=oldHead++commonSuffix := by
  simp only [EntryMappedFieldSegmentTrim.terminalReplay,oldHead,commonSuffix,
    Bool.false_eq_true,if_false,List.append_assoc]

-- Keep programs symbolic so kernel conversion does not evaluate concrete gate lists.
private theorem replace_prefix (P Q R : Program) (s : State) (m : List Bool)
    (same : ∀ a b, run P a s = run Q b s) :
    run (P ++ R) (List.replicate (measurementCount P) false ++
      m.drop (measurementCount Q)) s = run (Q ++ R) m s := by
  rw [run_append,run_append,same _ (m.take (measurementCount Q))]
  simp only [List.drop_append,List.length_replicate,Nat.sub_self,List.drop_zero,
    List.drop_replicate,List.replicate_zero,List.nil_append]

/-- Complete encoded inverse replay under the existing caller domain.
Only cell510 changes; the common packet/entry suffix keeps its actual record
stream, and the legacy head uses an independent padded record prefix. -/
theorem replay_inverse_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Z 0 (run (replay false) m s) := by
  let records := List.replicate (measurementCount oldHead) false ++
    m.drop (measurementCount newHead)
  have old := EntryMappedFieldSegmentTrim.terminalReplay_inverse_spec hn hlo ho hp hf
    origin hg0 hs0 env legal x Y hx0 hx trace s records input
  have stateEq : run (replay false) m s=
      run (EntryMappedFieldSegmentTrim.terminalReplay false) records s := by
    rw [replay_inverse_join,old_replay_inverse_join]
    exact (replace_prefix oldHead newHead commonSuffix s m (fun a b =>
      (PenultimateMappedCellProof.inverse_cell_eq hn hlo ho hp hf
        origin hg0 hs0 env legal Y s b a input).symm)).symm
  rw [←stateEq] at old
  exact old

private def inversePrefix : Program := renameProgram allPlaced (copyPairAt id) ++
  renameProgram allPlaced (converterPair false)

private theorem inversePrefix_spec
    (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run inversePrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Y Y (run inversePrefix m s) := by
  let copy := renameProgram allPlaced (copyPairAt id)
  let t := run copy (m.take (measurementCount copy)) s
  have first := mapped_copy_fill hn origin Y s (m.take (measurementCount copy)) input
  have second := encoded_center_pair hn origin hw hu hr hy Y Y t
    (m.drop (measurementCount copy)) first.2
  simp only [inversePrefix,run_append,converterPair_placement]
  exact ⟨second.1.trans first.1,second.2⟩

private theorem fieldSegment_inverse_join : fieldSegment false=inversePrefix++
    (replay false++renameProgram allPlaced (converterPair true)) := by
  simp only [fieldSegment,inversePrefix,copyPairAt,Bool.false_eq_true,if_false,
    List.append_nil,List.append_assoc]

/-- Original full field contract, with no additional endpoint or measurement
assumption. The duplicate inverse head is derived from the emitted copy and
conversion prefix. All work, source, controls, transcript and phase retain
 the accepted encoded canonical frame. -/
theorem fieldSegment_inverse_spec
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (fieldSegment false) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin Z 0 out
  have all := run_three_states inversePrefix (replay false)
    (renameProgram allPlaced (converterPair true)) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have first := inversePrefix_spec hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at first
      have middle := replay_inverse_spec hn hlo ho hp hf origin hg0 hs0 env legal
        x Y hx0 hx trace s1 m2 first.2
      rw [h2] at middle
      have last := encoded_canonical_pair hn origin hw hu hr hy Z 0 s2 m3 middle.2
      rw [converterPair_placement true] at h3
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m input
  rw [fieldSegment_inverse_join]
  simpa only [fieldResult,Bool.false_eq_true,if_false,Z] using all

end ECDSAAdd.Arithmetic.PenultimateMapped
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.replay_inverse_spec
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.fieldSegment_inverse_spec
