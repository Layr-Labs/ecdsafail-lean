import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrimProof
import ECDSAAdd.Arithmetic.EntrySelectedSwapFrame
import ECDSAAdd.Arithmetic.EntryBodySupportConcrete
import ECDSAAdd.Arithmetic.MappedCompressedFieldSegmentSpec

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires logicalCell compressedHistoryEncode compressedHistoryDecode
  OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
  OffsetBorrowedField.program TerminalParityOffset.program TerminalParityOffset.core
  TerminalParityMeasure.chain TerminalParityMeasure.leaf

private theorem zero_natural : renameProgram base logicalZero =
    EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028) (base 2409) (base 2410)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 := by
  have rmap : (balancedSharedPorts base (base 2409)).r=
      (balancedSharedPorts id 2409).r.map base := by
    simpa only [Function.comp_id] using FieldRename.shared_r_map base id 2409
  have ymap : (balancedSharedPorts base (base 2409)).y=
      (balancedSharedPorts id 2409).y.map base := by
    simpa only [Function.comp_id] using FieldRename.shared_y_map base id 2409
  simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,FieldRename.selectWindow_natural,
    FieldRename.swapRegisters_natural,rmap,ymap]

private def firstBody : Program := renameProgram base logicalZero ++
    renameProgram base (logicalCell true 1) ++ renameProgram base (logicalCell true 2)

private theorem payload_zero (g sw : Bool) (Y : Fp) :
    skywalkPayloadCell g sw (2*Y,0)=(if sw then 0 else Y,if sw then Y else 0) := by
  have two : (2:Fp)≠0 := by decide
  have half : (2*Y)/2=Y := mul_div_cancel_left₀ Y two
  simp only [skywalkPayloadCell,neg_zero,ite_self,add_zero,half]
  cases sw <;> rfl

/-- The retained S window followed by the two unchanged cells realizes
exactly the original three-cell update on the seeded payload. -/
theorem firstBody_frame
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord Y) (centerWord 0)) firstBody
      (PairFrame (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y origin
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)).1)
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)).2)) := by
  let a := (mixedTranscriptTape base).getD 0 ((0,0),(false,false))
  let c := (mixedTranscriptTape base).getD 1 ((0,0),(false,false))
  let d := (mixedTranscriptTape base).getD 2 ((0,0),(false,false))
  have aEq := mixedTape_base_getD 0 (by decide)
  have cEq := mixedTape_base_getD 1 (by decide)
  have dEq := mixedTape_base_getD 2 (by decide)
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) a.1.1 a.1.2
    (base 2409) (base 2410) (hf a (by simp [a,packetLetters])) ho
  rw [show a=((base 0,base 1028),mixedTranscriptUnitTrace.getD 0 (false,false)) from aEq] at layout
  have sw := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 layout origin hs0 Y 0
  let A := if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then 0 else Y
  let B := if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then Y else 0
  have rest := OffsetBorrowedCanonical.replay_frame base (base 2400) (base 2409) (base 2410)
    hn [c,d] (by
      intro l hl
      apply hf l
      simp only [packetLetters,Nat.mul_zero,Nat.zero_add,List.mem_cons,List.not_mem_nil,or_false]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      exact Or.inr (by simpa only [c,d] using hl))
    ho origin hg0 hs0 env A B
  have result := sw.seq rest
  have bodyEq : firstBody=EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028)
      (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 ++
      OffsetBorrowedCanonical.replay base (base 2400) (base 2409) (base 2410) [c,d] := by
    simp only [firstBody,zero_natural,OffsetBorrowedCanonical.replay,base_cell_eq,
      if_true,List.append_nil,c,d,cEq,dEq,List.append_assoc]
  rw [bodyEq]
  simpa only [packetLetters,Nat.mul_zero,Nat.zero_add,mixedTranscriptControls,List.map_cons,
    List.map_nil,skywalkPayloadReplay,aEq,payload_zero,A,B,a,c,d] using result

private theorem firstBody_support (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) : wires firstBody ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) 0 := by
  unfold firstBody
  exact EntryBodySupport.first_body_support hn hlo

-- Check the transport once on arbitrary programs, before specializing to the packet.
private theorem transport_encoded (P Q : Program)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (X Y A B : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (ref : (run P m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A B (run P m s))
    (same : (∀q,zeroRegion q → s.basis (base q)=false) →
      (∀q,zeroRegion q → (run P m s).basis (base q)=false) →
      run Q m s=run P m s) :
    (run Q m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A B (run Q m s) := by
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env A B (run P m s) ref.2
  rw [same cleanIn cleanOut]
  exact ref

/-- Exact native first packet, with both clean placement boundaries derived
from the encoded frame and the accepted selected-swap frame. -/
theorem firstGroup_forward_step
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin Y 0 s) :
    let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
    (run (firstGroup true) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Q.1 Q.2 (run (firstGroup true) m s) := by
  have ref := EntrySelectedSwapFrame.encoded_window_step base (base 2400) (base 2409) (base 2410)
    hn hlo hp 0 (by decide) origin legal Y 0 _ _ firstBody (firstBody_support hn hlo)
    (firstBody_frame hn ho hf origin hg0 hs0 env Y) s m input
  simp only [Nat.mul_zero] at ref
  have shape : baseFirstGroup true=compressedHistoryDecode base 0++firstBody++compressedHistoryEncode base 0 := by
    simp only [baseFirstGroup,firstBody,if_true]
  rw [←shape] at ref
  exact transport_encoded (baseFirstGroup true) (firstGroup true) hn hlo origin env Y 0 _ _
    s m input ref (firstGroup_state_eq true s m)

private def oldPrefix : Program := fieldPrefix true ++
  renameProgram allPlaced (converterPair false) ++ mappedGroup true 0
private def newPrefix : Program := renameProgram allPlaced (converterPair false) ++ firstGroup true
private def commonSuffix : Program := mappedGroups true 1 169 ++ tailProgram true ++
  renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced (copyPairAt id)

/-- Independent record streams identify one full encoded packet output.
The unary endpoint is evaluated on its encoded input before any decoder. -/
theorem forward_prefix_state_eq
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s : State) (mOld mNew : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    run oldPrefix mOld s=run newPrefix mNew s := by
  let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin Q.1 Q.2 out
  have old := run_three_states (fieldPrefix true) (renameProgram allPlaced (converterPair false))
    (mappedGroup true 0) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have a := mapped_unary_step true hn hlo origin hw hu Y 0 initial m1 hin
      simp only [fieldPrefix,if_true] at h1
      simp only [if_true] at a
      rw [h1] at a
      have b := encoded_center_pair hn origin hw hu hr hy (2*Y) 0 s1 m2 a.2
      rw [converterPair_placement false] at h2
      rw [h2] at b
      have c := mappedGroup_encoded_step true 0 (by decide) hn hlo ho hp hf origin hg0 hs0
        env legal (2*Y) 0 s2 m3 b.2
      rw [h3] at c
      exact ⟨c.1.trans (b.1.trans a.1),by simpa only [directionalPayload,Bool.not_true,
        Bool.false_eq_true,if_false,Q] using c.2⟩) s mOld input
  have oldShape : oldPrefix=fieldPrefix true ++
      (renameProgram allPlaced (converterPair false)++mappedGroup true 0) := by
    simp only [oldPrefix,List.append_assoc]
  rw [←oldShape] at old
  let center := renameProgram allPlaced (converterPair false)
  let t := run center (mNew.take (measurementCount center)) s
  have first := encoded_center_pair hn origin hw hu hr hy Y 0 s
    (mNew.take (measurementCount center)) input
  have first' : t.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin Y 0 t := by
    simpa only [t,center,converterPair_placement] using first
  have last := firstGroup_forward_step hn hlo ho hp hf origin hg0 hs0 env legal Y t
    (mNew.drop (measurementCount center)) first'.2
  have current : (run newPrefix mNew s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin Q.1 Q.2 (run newPrefix mNew s) := by
    simp only [newPrefix,run_append]
    exact ⟨last.1.trans first'.1,last.2⟩
  exact encoded_field_unique origin Q.1 Q.2 _ _ old.2 current.2 (old.1.trans current.1.symm)

private theorem forward_groups_succ (j n : Nat) :
    mappedGroups true j (n+1)=mappedGroup true j++mappedGroups true (j+1) n := by
  simp only [mappedGroups,if_true]

private theorem old_forward_join : MappedCompressed.fieldSegment true=oldPrefix++commonSuffix := by
  have groups : mappedGroups true 0 170=mappedGroup true 0++mappedGroups true 1 169 :=
    forward_groups_succ 0 169
  simp only [MappedCompressed.fieldSegment,oldPrefix,commonSuffix,fieldPrefix,copyPairAt,
    if_true,MappedCompressed.mappedReplay,groups,tailProgram,List.append_assoc]
private theorem new_forward_join : fieldSegment true=newPrefix++commonSuffix := by
  simp only [fieldSegment,newPrefix,commonSuffix,replay,copyPairAt,if_true,tailProgram,
    List.nil_append,List.append_assoc]

-- Keep programs symbolic so kernel conversion does not evaluate concrete gate lists.
private theorem replace_prefix (P Q R : Program) (s : State) (m : List Bool)
    (same : ∀ a b, run P a s = run Q b s) :
    run (P ++ R) (List.replicate (measurementCount P) false ++
      m.drop (measurementCount Q)) s = run (Q ++ R) m s := by
  rw [run_append,run_append,same _ (m.take (measurementCount Q))]
  simp only [List.drop_append,List.length_replicate,Nat.sub_self,List.drop_zero,
    List.drop_replicate,List.replicate_zero,List.nil_append]

/-- Full actual forward field wrapper. The fixed170 packet encoding, raw
510/511 tail and complete caller State are retained for all independent MX
records. The old endpoint is replaced only at the closed first-packet boundary. -/
theorem fieldTrimSegment_forward_spec
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
  let suffixRecords := m.drop (measurementCount newPrefix)
  let records := List.replicate (measurementCount oldPrefix) false ++ suffixRecords
  have old := MappedCompressed.fieldSegment_spec true hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s records input
  have actualStateEq : run (MappedCompressed.fieldSegment true) records s=run (fieldSegment true) m s := by
    rw [old_forward_join,new_forward_join]
    exact replace_prefix oldPrefix newPrefix commonSuffix s m (fun a b =>
      forward_prefix_state_eq hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal hw hu hr hy Y s a b input)
  rw [actualStateEq] at old
  exact old

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.firstBody_frame
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.firstGroup_forward_step

#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.forward_prefix_state_eq
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.fieldTrimSegment_forward_spec
