import ECDSAAdd.Arithmetic.EntryBodySupport
import ECDSAAdd.Arithmetic.EntrySelectedSwapFrame
import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrimProof
import ECDSAAdd.Arithmetic.EntryInversePayload

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires logicalCell renameProgram
  OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
  compressedHistoryEncode compressedHistoryDecode

private theorem selected_natural (f : Nat → Wire) : renameProgram f logicalZero =
    EntryFieldSeedCancellation.selectedSwap f (f 2400) (f 1028) (f 2409) (f 2410)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 := by
  have rmap : (balancedSharedPorts f (f 2409)).r=(balancedSharedPorts id 2409).r.map f := by
    simpa only [Function.comp_id] using FieldRename.shared_r_map f id 2409
  have ymap : (balancedSharedPorts f (f 2409)).y=(balancedSharedPorts id 2409).y.map f := by
    simpa only [Function.comp_id] using FieldRename.shared_y_map f id 2409
  simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,FieldRename.selectWindow_natural,
    FieldRename.swapRegisters_natural,rmap,ymap]

def inverseBody : Program := renameProgram base (logicalCell false 2) ++
  renameProgram base (logicalCell false 1) ++ renameProgram base logicalZero

def inverseZeroPayload (origin : BasisState) (X Y : Fp) : Fp×Fp :=
  let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400)
    [(mixedTranscriptTape base).getD 1 ((0,0),(false,false)),
     (mixedTranscriptTape base).getD 2 ((0,0),(false,false))]) (X,Y)
  if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then (Q.2,Q.1) else Q

private theorem reversed_three_support (f : Wire → Wire) (P Q R S : Program) (W : Finset Wire)
    (sub : wires P ⊆ wires Q) (hq : wires (renameProgram f Q) ⊆ W)
    (hr : wires (renameProgram f R) ⊆ W) (hs : wires (renameProgram f S) ⊆ W) :
    wires (renameProgram f S++renameProgram f R++renameProgram f P) ⊆ W := by
  have renamed : wires (renameProgram f P) ⊆ wires (renameProgram f Q) := by
    rw [renameProgram_support,renameProgram_support]
    exact Finset.image_mono f sub
  rw [wires_append,wires_append]
  exact Finset.union_subset (Finset.union_subset hs hr) (renamed.trans hq)

theorem inverseBody_support (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base) :
    wires inverseBody ⊆ groupReadSites base (base 2400) (base 2409) (base 2410) 0 := by
  have pool := skywalkShared_integer_nodup base hn
  have site (k : Fin 6) := compressedHistory_site_mem base pool hlo 0 (by decide) k
  unfold inverseBody
  exact reversed_three_support base logicalZero (logicalCell false 0) (logicalCell false 1)
    (logicalCell false 2) (groupReadSites base (base 2400) (base 2409) (base 2410) 0)
    (logicalZero_support_sub false)
    (EntryBodySupport.renamed_logical_support base false 0 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 0)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 1))
    (EntryBodySupport.renamed_logical_support base false 1 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 2)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 3))
    (EntryBodySupport.renamed_logical_support base false 2 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 4)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 5))

/-- Both remaining inverse cells and the recorded S window are retained. -/
theorem inverseBody_frame
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord X) (centerWord Y)) inverseBody
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (inverseZeroPayload origin X Y).1) (centerWord (inverseZeroPayload origin X Y).2)) := by
  let a := (mixedTranscriptTape base).getD 0 ((0,0),(false,false))
  let c := (mixedTranscriptTape base).getD 1 ((0,0),(false,false))
  let d := (mixedTranscriptTape base).getD 2 ((0,0),(false,false))
  let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) [c,d]) (X,Y)
  have aEq := mixedTape_base_getD 0 (by decide)
  have cEq := mixedTape_base_getD 1 (by decide)
  have dEq := mixedTape_base_getD 2 (by decide)
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) a.1.1 a.1.2
    (base 2409) (base 2410) (hf a (by simp [a,packetLetters])) ho
  rw [show a=((base 0,base 1028),mixedTranscriptUnitTrace.getD 0 (false,false)) from aEq] at layout
  have rest := OffsetBorrowedInverseCanonical.replay_frame base (base 2400) (base 2409) (base 2410)
    hn [c,d] (by
      intro l hl
      apply hf l
      simp only [packetLetters,Nat.mul_zero,Nat.zero_add,List.mem_cons,List.not_mem_nil,or_false]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      exact Or.inr (by simpa only [c,d] using hl)) ho origin hg0 hs0 env X Y
  have sw := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 layout origin hs0 Q.1 Q.2
  have result := rest.seq sw
  have bodyEq : inverseBody=OffsetBorrowedInverseCanonical.replay base (base 2400) (base 2409)
      (base 2410) [c,d]++EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028)
        (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 := by
    simp only [inverseBody,selected_natural,OffsetBorrowedInverseCanonical.replay,base_cell_eq,
      Bool.false_eq_true,if_false,List.append_nil,List.nil_append,c,d,cEq,dEq,List.append_assoc]
  rw [bodyEq]
  cases bit : mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 <;>
    simpa only [inverseZeroPayload,bit,if_true,if_false,Bool.false_eq_true,Q,c,d] using result

/-- The existing complete inverse result forces the retained window's
output. Neither source-zero nor fixed measurement results are assumed. -/
theorem inverseZeroPayload_of_old (origin : BasisState) (X Y Z : Fp)
    (old : skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (X,Y)=(2*Z,0)) :
    inverseZeroPayload origin X Y=(Z,0) := by
  have aEq := mixedTape_base_getD 0 (by decide)
  have value : skywalkPayloadUncell
      (mixedTranscriptBit origin (base 2400) (base 0) (mixedTranscriptUnitTrace.getD 0 (false,false)).1)
      (mixedTranscriptBit origin (base 2400) (base 1028) (mixedTranscriptUnitTrace.getD 0 (false,false)).2)
      (skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400)
        [(mixedTranscriptTape base).getD 1 ((0,0),(false,false)),
         (mixedTranscriptTape base).getD 2 ((0,0),(false,false))]) (X,Y))=(2*Z,0) := by
    simpa only [packetLetters,Nat.mul_zero,Nat.zero_add,mixedTranscriptControls,List.map_cons,
      List.map_nil,skywalkPayloadReplayInverse,aEq] using old
  exact EntryInversePayload.remove_final_double _ _ _ Z value

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

/-- Actual mapped packet-zero inverse, with clean placement boundaries
derived from its complete encoded field frames. -/
theorem firstGroup_inverse_step
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (X Y : Fp) (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    (run (firstGroup false) m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (inverseZeroPayload origin X Y).1 (inverseZeroPayload origin X Y).2 (run (firstGroup false) m s) := by
  have ref := EntrySelectedSwapFrame.encoded_window_step base (base 2400) (base 2409) (base 2410)
    hn hlo hp 0 (by decide) origin legal X Y _ _ inverseBody (inverseBody_support hn hlo)
    (inverseBody_frame hn ho hf origin hg0 hs0 env X Y) s m input
  simp only [Nat.mul_zero] at ref
  have shape : baseFirstGroup false=compressedHistoryDecode base 0++inverseBody++compressedHistoryEncode base 0 := by
    simp only [baseFirstGroup,inverseBody,Bool.false_eq_true,if_false]
  rw [←shape] at ref
  exact transport_encoded (baseFirstGroup false) (firstGroup false) hn hlo origin env X Y _ _
    s m input ref (firstGroup_state_eq false s m)

end ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.inverseBody_support
#print axioms ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrim.firstGroup_inverse_step
