import ECDSAAdd.Arithmetic.PenultimateMappedProgram
import ECDSAAdd.Arithmetic.PenultimateMappedCellProof
import ECDSAAdd.Framework.ProgramContextEq
import ECDSAAdd.Framework.RecordPadding
import ECDSAAdd.Framework.CertifiedProgram

set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.PenultimateMapped
open Secp256k1 MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run groupsPayload indexedLetters packetLetters
  mixedTranscriptTape mixedTranscriptUnitTrace mappedGroups logicalCell
  EntryMappedFieldSegmentTrim.firstGroup measurementCount
  PenultimateSwapIdentity.cell PenultimateSwapIdentity.penultimatePayload fieldSegment replay
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


private def rawPrefix : Program := renameProgram allPlaced (converterPair false) ++
  (EntryMappedFieldSegmentTrim.firstGroup true ++ mappedGroups true 1 169)
private def headPrefix : Program := sealedProgram rawPrefix
private def oldHead : Program := sealedProgram (headPrefix ++ renameProgram allPlaced (logicalCell true 510))
private def newHead : Program := sealedProgram (headPrefix ++ renameProgram allPlaced (PenultimateSwapIdentity.cell true))
private def commonTail : Program := renameProgram allPlaced (converterPair true) ++
  renameProgram allPlaced (copyPairAt id)
attribute [local irreducible] rawPrefix headPrefix oldHead newHead commonTail

private theorem headPrefix_eq : headPrefix=rawPrefix := by
  unfold headPrefix
  exact sealedProgram_eq _
private theorem oldHead_eq : oldHead=headPrefix++renameProgram allPlaced (logicalCell true 510) := by
  unfold oldHead
  exact sealedProgram_eq _
private theorem newHead_eq : newHead=headPrefix++renameProgram allPlaced (PenultimateSwapIdentity.cell true) := by
  unfold newHead
  exact sealedProgram_eq _

/-- The actual entry-cancelled first packet and169 native packets expose the
same penultimate payload as the original510-letter mathematical prefix. -/
private theorem headPrefix_step
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let A := PenultimateSwapIdentity.penultimatePayload origin Y
    (run headPrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A.1 A.2 (run headPrefix m s) := by
  let A := PenultimateSwapIdentity.penultimatePayload origin Y
  let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin A.1 A.2 out
  have all := run_three_states (renameProgram allPlaced (converterPair false))
    (EntryMappedFieldSegmentTrim.firstGroup true) (mappedGroups true 1 169) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have a := encoded_center_pair hn origin hw hu hr hy Y 0 initial m1 hin
      rw [converterPair_placement false] at h1
      rw [h1] at a
      have b := EntryMappedFieldSegmentTrim.firstGroup_forward_step hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal Y s1 m2 a.2
      rw [h2] at b
      have frame2 : EncodedFieldFrame base (base 2409) origin Q.1 Q.2 s2 := b.2
      have cAll := mappedGroups_frame true 1 169 (by decide) hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf)
        origin hg0 hs0 env legal Q.1 Q.2 s2 m3 frame2
      have cPhase : (run (mappedGroups true 1 169) m3 s2).phase=s2.phase := cAll.2.1
      have cFrame : EncodedFieldFrame base (base 2409) origin
          (groupsPayload true origin 1 169 (Q.1,Q.2)).1
          (groupsPayload true origin 1 169 (Q.1,Q.2)).2
          (run (mappedGroups true 1 169) m3 s2) := cAll.2.2
      rw [h3] at cPhase cFrame
      have payload : groupsPayload true origin 1 169 (Q.1,Q.2)=A := by
        change groupsPayload true origin 1 169 Q=A
        exact first_rest_payload origin Y
      rw [payload] at cFrame
      exact ⟨cPhase.trans (b.1.trans a.1),cFrame⟩) s m input
  have rawResult : (run rawPrefix m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A.1 A.2 (run rawPrefix m s) := by
    simpa only [rawPrefix] using all
  have eval : run headPrefix m s=run rawPrefix m s := by
    unfold headPrefix
    exact sealedProgram_run rawPrefix m s
  exact Eq.mp (congrArg (fun out : State => out.phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin A.1 A.2 out) eval.symm) rawResult


/- Head States agree when their internal prefix records coincide; local cell
records remain independent. This record condition is proved by construction in
the public wrapper and adds no public input or outcome restriction. -/
private theorem head_state_eq
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
    (Y : Fp) (s : State) (mOld mNew : List Bool)
    (hprefix : mOld.take (measurementCount headPrefix)=mNew.take (measurementCount headPrefix))
    (input : EncodedCanonicalFrame origin Y 0 s) :
    run oldHead mOld s=run newHead mNew s := by
  let A := PenultimateSwapIdentity.penultimatePayload origin Y
  let newState := run headPrefix (mNew.take (measurementCount headPrefix)) s
  have newFrame : newState.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin A.1 A.2 newState :=
    headPrefix_step hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy Y s _ input
  have last := PenultimateMappedCellProof.forward_cell_eq hn hlo ho hp hf
    origin hg0 hs0 env legal A.1 A.2 newState
    (mNew.drop (measurementCount headPrefix)) (mOld.drop (measurementCount headPrefix))
    newFrame.2 (PenultimateSwapIdentity.penultimate_half_dup origin x Y hx0 hx trace)
  have prefixStates := congrArg (fun rs : List Bool => run headPrefix rs s) hprefix
  have transport := congrArg (fun t : State =>
    run (renameProgram allPlaced (logicalCell true 510)) (mOld.drop (measurementCount headPrefix)) t) prefixStates
  have context := append_context_eq headPrefix
    (renameProgram allPlaced (logicalCell true 510))
    (renameProgram allPlaced (PenultimateSwapIdentity.cell true)) s mOld mNew (transport.trans last.symm)
  have oldShape : oldHead=headPrefix++renameProgram allPlaced (logicalCell true 510) := oldHead_eq
  have newShape : newHead=headPrefix++renameProgram allPlaced (PenultimateSwapIdentity.cell true) := newHead_eq
  exact program_shape_context_eq oldHead newHead
    (headPrefix++renameProgram allPlaced (logicalCell true 510))
    (headPrefix++renameProgram allPlaced (PenultimateSwapIdentity.cell true))
    s mOld mNew oldShape newShape context


private theorem old_join : EntryMappedFieldSegmentTrim.terminalFieldSegment true=oldHead++commonTail := by
  have raw : EntryMappedFieldSegmentTrim.terminalFieldSegment true=
      (rawPrefix++renameProgram allPlaced (logicalCell true 510))++commonTail := by
    simp only [EntryMappedFieldSegmentTrim.terminalFieldSegment,EntryMappedFieldSegmentTrim.terminalReplay,
      rawPrefix,commonTail,copyPairAt,if_true,List.nil_append,List.append_assoc]
  have shape := oldHead_eq.trans (congrArg (fun q : Program =>
    q++renameProgram allPlaced (logicalCell true 510)) headPrefix_eq)
  exact raw.trans (congrArg (fun q : Program => q++commonTail) shape).symm

private theorem new_join : fieldSegment true=newHead++commonTail := by
  have raw : fieldSegment true=
      (rawPrefix++renameProgram allPlaced (PenultimateSwapIdentity.cell true))++commonTail := by
    simp only [fieldSegment,replay,rawPrefix,commonTail,copyPairAt,if_true,List.nil_append,List.append_assoc]
  have shape := newHead_eq.trans (congrArg (fun q : Program =>
    q++renameProgram allPlaced (PenultimateSwapIdentity.cell true)) headPrefix_eq)
  exact raw.trans (congrArg (fun q : Program => q++commonTail) shape).symm


private theorem splice_records (n a b : Nat) (m : List Bool) :
    let padded := m++List.replicate (n+b) false
    let records := padded.take n++(List.replicate a false++padded.drop (n+b))
    records.take n=padded.take n ∧ records.drop (n+a)=padded.drop (n+b) := by
  let padded := m++List.replicate (n+b) false
  have bound : n≤padded.length := by simp only [padded,List.length_append,List.length_replicate]; omega
  have len : (padded.take n).length=n := List.length_take_of_le bound
  constructor
  · change ((padded.take n)++(List.replicate a false++padded.drop (n+b))).take n=padded.take n
    rw [List.take_append_of_le_length len.symm.le,List.take_take,Nat.min_self]
  · have gone : (padded.take n).drop (n+a)=[] := List.drop_eq_nil_of_le (by rw [len]; omega)
    have sub : n+a-n=a := by omega
    change ((padded.take n)++(List.replicate a false++padded.drop (n+b))).drop (n+a)=padded.drop (n+b)
    rw [List.drop_append,len,gone,sub,List.nil_append]
    rw [List.drop_append,List.length_replicate,List.drop_replicate,Nat.sub_self,
      List.replicate_zero,List.nil_append,List.drop_zero]

/-- Only raw510's S window is removed. The original complete point-input,
trace, activation, workspace and encoding contract is retained. Every fresh
MX outcome and arbitrary incoming phase are covered by State equality. -/
theorem fieldSegment_forward_spec
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
    let out := run (fieldSegment true) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out := by
  let p := measurementCount headPrefix
  let a := measurementCount (renameProgram allPlaced (logicalCell true 510))
  let b := measurementCount (renameProgram allPlaced (PenultimateSwapIdentity.cell true))
  have oldCount : measurementCount oldHead=p+a :=
    (congrArg measurementCount oldHead_eq).trans (measurementCount_append _ _)
  have newCount : measurementCount newHead=p+b :=
    (congrArg measurementCount newHead_eq).trans (measurementCount_append _ _)
  let padded := m++List.replicate (p+b) false
  let records := padded.take p++(List.replicate a false++padded.drop (p+b))
  have splice := splice_records p a b m
  have prefixRecords : records.take p=padded.take p := splice.1
  have tailRecords : records.drop (measurementCount oldHead)=padded.drop (measurementCount newHead) := by
    simpa only [oldCount,newCount] using splice.2
  have oldBound : p≤measurementCount oldHead := by rw [oldCount]; omega
  have newBound : p≤measurementCount newHead := by rw [newCount]; omega
  have prefixTakes : (records.take (measurementCount oldHead)).take p=
      (padded.take (measurementCount newHead)).take p := by
    simpa only [List.take_take,Nat.min_eq_left oldBound,Nat.min_eq_left newBound] using prefixRecords
  have headEq := head_state_eq hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy
    x hx0 hx trace Y s (records.take (measurementCount oldHead))
    (padded.take (measurementCount newHead)) prefixTakes input
  have context := suffix_context_eq oldHead newHead commonTail s records padded headEq tailRecords
  have programEq : run (EntryMappedFieldSegmentTrim.terminalFieldSegment true) records s=
      run (fieldSegment true) padded s :=
    (congrArg (fun q : Program => run q records s) old_join).trans
      (context.trans (congrArg (fun q : Program => run q padded s) new_join).symm)
  have padEq : run (fieldSegment true) padded s=run (fieldSegment true) m s :=
    run_pad_false (fieldSegment true) m (p+b) s
  have actualStateEq := programEq.trans padEq
  have old := EntryMappedFieldSegmentTrim.terminalFieldTrimSegment_forward_spec
    hn hlo ho hp hf origin hg0 hs0 env legal hw hu hr hy x hx0 hx trace Y s records input
  exact Eq.mp (congrArg (fun out : State =>
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out) actualStateEq) old

end ECDSAAdd.Arithmetic.PenultimateMapped
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.forward_groups_payload
#print axioms ECDSAAdd.Arithmetic.PenultimateMapped.fieldSegment_forward_spec
