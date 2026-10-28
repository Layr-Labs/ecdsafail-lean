import ECDSAAdd.Arithmetic.EntryInverseFirstGroupFrame
import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrimTerminal
import ECDSAAdd.Arithmetic.TerminalMappedReplayResources

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run logicalCell terminalReplay terminalFieldSegment groupsPayload

private theorem inverse_groups_succ (origin : BasisState) (j n : Nat) (Q : Fp×Fp) :
    groupsPayload false origin j (n+1) Q=
      skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) (packetLetters j))
        (groupsPayload false origin (j+1) n Q) := by
  simp only [groupsPayload,Bool.false_eq_true,if_false,Bool.not_false,directionalPayload,if_true]

/-- The actual inverse emission retains raw510, all169 later native packets,
and the cell-zero S window. Its final zero source follows from the accepted
whole inverse payload identity under the original512 recorded trace. -/
theorem terminalReplay_inverse_spec
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
    (run (terminalReplay false) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Z 0 (run (terminalReplay false) m s) := by
  let A := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (Y,Y)
  let B := groupsPayload false origin 1 169 A
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have old : skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) (packetLetters 0)) B=(2*Z,0) := by
    have result := EntryInversePayload.inverse_boundary origin x Y hx0 hx trace
    rw [inverse_groups_succ origin 0 169 A] at result
    exact result
  have removed := inverseZeroPayload_of_old origin B.1 B.2 Z old
  let P : State → State → Prop := fun initial out => EncodedFieldFrame base (base 2409) origin Y Y initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin Z 0 out
  have all := run_three_states (renameProgram allPlaced (logicalCell false 510))
    (mappedGroups false 1 169) (firstGroup false) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have first := trimCell_step false hn hlo ho hp hf origin hg0 hs0 env legal Y Y initial m1 hin
      rw [h1] at first
      have frame1 : EncodedFieldFrame base (base 2409) origin A.1 A.2 s1 := by
        simpa only [directionalPayload,Bool.not_false,if_true,A] using first.2.2
      have later := mappedGroups_frame false 1 169 (by decide) hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf) origin hg0 hs0 env legal
        A.1 A.2 s1 m2 frame1
      rw [h2] at later
      have last := firstGroup_inverse_step hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal B.1 B.2 s2 m3 later.2.2
      rw [h3,removed] at last
      exact ⟨last.1.trans (later.2.1.trans first.2.1),last.2⟩) s m input
  have shape : terminalReplay false=renameProgram allPlaced (logicalCell false 510)++
      (mappedGroups false 1 169++firstGroup false) := by
    simp only [terminalReplay,Bool.false_eq_true,if_false,List.append_assoc]
  rw [←shape] at all
  exact all

private def inverseEntryPrefix : Program := renameProgram allPlaced (copyPairAt id)++
  renameProgram allPlaced (converterPair false)

private theorem inverseEntryPrefix_step
    (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run inverseEntryPrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Y Y (run inverseEntryPrefix m s) := by
  let copy := renameProgram allPlaced (copyPairAt id)
  let t := run copy (m.take (measurementCount copy)) s
  have first := mapped_copy_fill hn origin Y s (m.take (measurementCount copy)) input
  have second := encoded_center_pair hn origin hw hu hr hy Y Y t
    (m.drop (measurementCount copy)) first.2
  simp only [inverseEntryPrefix,run_append,converterPair_placement]
  exact ⟨second.1.trans first.1,second.2⟩

private theorem inverse_entry_join : terminalFieldSegment false=inverseEntryPrefix++
    (terminalReplay false++renameProgram allPlaced (converterPair true)) := by
  simp only [terminalFieldSegment,inverseEntryPrefix,copyPairAt,Bool.false_eq_true,if_false,
    List.append_nil,List.append_assoc]

/-- Full actual inverse field wrapper under the unchanged public contract.
Both original high bits, workspace, transcript, activation control and phase
are restored for every independent measurement stream. The terminal511 cell
remains omitted, and the final inverse arithmetic/unseed pair is cancelled. -/
theorem terminalFieldTrimSegment_inverse_spec
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
    let out := run (terminalFieldSegment false) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin Z 0 out
  have all := run_three_states inverseEntryPrefix (terminalReplay false)
    (renameProgram allPlaced (converterPair true)) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have first := inverseEntryPrefix_step hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at first
      have middle := terminalReplay_inverse_spec hn hlo ho hp hf origin hg0 hs0 env legal
        x Y hx0 hx trace s1 m2 first.2
      rw [h2] at middle
      have last := encoded_canonical_pair hn origin hw hu hr hy Z 0 s2 m3 middle.2
      rw [converterPair_placement true] at h3
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m input
  rw [inverse_entry_join]
  simpa only [fieldResult,Bool.false_eq_true,if_false,Z] using all

theorem inverse_entry_resources : toffoliCount (terminalFieldSegment false)=657817 ∧
    measurementCount (terminalFieldSegment false)=525981 := terminalFieldSegment_counts false

theorem inverse_entry_support : wires (terminalFieldSegment false) ⊆ slots.toFinset :=
  terminalFieldSegment_support false

/-- Entry/unseed savings relative to the already terminal-trim production
wrapper; the previously integrated1281-T terminal saving is not recounted. -/
theorem inverse_entry_saving :
    toffoliCount (MappedCompressed.fieldTrimSegment false)=toffoliCount (terminalFieldSegment false)+1536 ∧
    measurementCount (MappedCompressed.fieldTrimSegment false)=measurementCount (terminalFieldSegment false)+1536 := by
  have old := MappedCompressed.fieldTrimSegment_counts false
  rw [old.1,old.2,inverse_entry_resources.1,inverse_entry_resources.2]
  norm_num

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.terminalReplay_inverse_spec
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.terminalFieldTrimSegment_inverse_spec
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.inverse_entry_resources
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.inverse_entry_support
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.inverse_entry_saving
