import ECDSAAdd.Submission.Entrant.LaneISegment
import ECDSAAdd.Arithmetic.MappedFieldPhysical

/-! First packet, endpoint cell, and the complete field segment with the
256-wide fold in every field cell. -/
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

def unitI (i : Nat) : Bool×Bool := mixedTranscriptUnitTrace.getD i (false,false)

/-! ### First packet -/

def firstBodyFI : Program :=
  renameProgram base logicalZero ++
  cellFI base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410) (unitI 1).1 (unitI 1).2 ++
  cellFI base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410) (unitI 2).1 (unitI 2).2

def firstBodyII : Program :=
  cellII base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410) (unitI 2).1 (unitI 2).2 ++
  cellII base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410) (unitI 1).1 (unitI 1).2 ++
  renameProgram base logicalZero

def baseFirstGroupI (divide : Bool) : Program :=
  compressedHistoryDecode base 0 ++ (if divide then firstBodyFI else firstBodyII) ++
  compressedHistoryEncode base 0

def firstGroupI (divide : Bool) : Program :=
  renameProgram (shifted (pi 0)) (baseFirstGroupI divide)

def oldFirstBody (divide : Bool) : Program :=
  if divide then renameProgram base logicalZero ++
      OffsetBorrowedCanonical.cell base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410)
        (unitI 1).1 (unitI 1).2 ++
      OffsetBorrowedCanonical.cell base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410)
        (unitI 2).1 (unitI 2).2
  else OffsetBorrowedInverseCanonical.cell base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410)
        (unitI 2).1 (unitI 2).2 ++
      OffsetBorrowedInverseCanonical.cell base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410)
        (unitI 1).1 (unitI 1).2 ++
      renameProgram base logicalZero

theorem baseFirstGroup_shape (divide : Bool) :
    baseFirstGroup divide=compressedHistoryDecode base 0 ++ oldFirstBody divide ++
      compressedHistoryEncode base 0 := by
  cases divide <;> simp only [baseFirstGroup,oldFirstBody,base_cell_eq,unitI,
    Bool.false_eq_true,if_false,if_true]

theorem firstBody_sub (divide : Bool) :
    InstrSub (if divide then firstBodyFI else firstBodyII) (oldFirstBody divide) := by
  cases divide <;> simp only [firstBodyFI,firstBodyII,oldFirstBody,Bool.false_eq_true,if_false,if_true]
  · exact ((cellII_sub _ _ _ _ _ _ _ _).append (cellII_sub _ _ _ _ _ _ _ _)).append (InstrSub.refl _)
  · exact ((InstrSub.refl _).append (cellFI_sub _ _ _ _ _ _ _ _)).append (cellFI_sub _ _ _ _ _ _ _ _)

theorem firstBody_counts (divide : Bool) :
    measurementCount (if divide then firstBodyFI else firstBodyII)=measurementCount (oldFirstBody divide) ∧
    toffoliCount (if divide then firstBodyFI else firstBodyII)+2=toffoliCount (oldFirstBody divide) := by
  have a1 := cellFI_counts base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410) (unitI 1).1 (unitI 1).2
  have a2 := cellFI_counts base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410) (unitI 2).1 (unitI 2).2
  have b1 := cellII_counts base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410) (unitI 1).1 (unitI 1).2
  have b2 := cellII_counts base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410) (unitI 2).1 (unitI 2).2
  cases divide <;> simp only [firstBodyFI,firstBodyII,oldFirstBody,Bool.false_eq_true,if_false,if_true,
    measurementCount_append,toffoliCount_append] <;> constructor <;> omega

private theorem first_layouts
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0)) (i : Nat)
    (hi : i < 3) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409)) (base 2400) (base i) (base (1028+i))
      (base 2410) := by
  have eq := mixedTape_base_getD i (by omega)
  have mem : (mixedTranscriptTape base).getD i ((0,0),(false,false))∈packetLetters 0 := by
    rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with rfl|rfl|rfl <;> simp [packetLetters]
  have layout := balancedSharedTranscriptLayout_direct base (base 2400)
    ((mixedTranscriptTape base).getD i ((0,0),(false,false))).1.1
    ((mixedTranscriptTape base).getD i ((0,0),(false,false))).1.2
    (base 2409) (base 2410) (hf _ mem) ho
  rw [eq] at layout
  exact layout

theorem firstBody_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (X Y : Fp) (t : State) (r : List Bool)
    (h : PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y) t.basis) :
    run (if divide then firstBodyFI else firstBodyII) r t=run (oldFirstBody divide) r t := by
  have l0 := first_layouts ho hf 0 (by decide)
  have l1 := first_layouts ho hf 1 (by decide)
  have l2 := first_layouts ho hf 2 (by decide)
  have hS := ho (base 2409) (by simp)
  have hE := ho (base 2410) (by simp)
  cases divide
  · simp only [firstBodyII,oldFirstBody,Bool.false_eq_true,if_false]
    have m2 := (cellII_counts base (base 2400) (base 2) (base (1028+2)) (base 2409) (base 2410)
      (unitI 2).1 (unitI 2).2).1
    have m1 := (cellII_counts base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410)
      (unitI 1).1 (unitI 1).2).1
    apply seq_eq _ _ _ _ t r (by simp only [measurementCount_append,m1,m2]) ?_ rfl
    · have fr := OffsetBorrowedInverseCanonical.cell_frame base (base 2400) (base 2) (base (1028+2))
        (base 2409) (base 2410) (unitI 2).1 (unitI 2).2 hn l2 hS hE origin hg0 hs0 env X Y
      apply seq_eq _ _ _ _ t _ (cellII_counts _ _ _ _ _ _ _ _).1
        (cellII_eq _ _ _ _ _ _ _ _ hn l2 hS hE origin hg0 hs0 env X Y t _ h)
      exact cellII_eq _ _ _ _ _ _ _ _ hn l1 hS hE origin hg0 hs0 env _ _ _ _ (fr t _ h).2
  · simp only [firstBodyFI,oldFirstBody,if_true]
    have sw := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base (1028+0))
      (base 2409) (base 2410) (unitI 0).2 l0 origin hs0 X Y
    have zeroEq : renameProgram base logicalZero=EntryFieldSeedCancellation.selectedSwap base (base 2400)
        (base (1028+0)) (base 2409) (base 2410) (unitI 0).2 := by
      have rmap : (balancedSharedPorts base (base 2409)).r=
          (balancedSharedPorts id 2409).r.map base := by
        simpa only [Function.comp_id] using FieldRename.shared_r_map base id 2409
      have ymap : (balancedSharedPorts base (base 2409)).y=
          (balancedSharedPorts id 2409).y.map base := by
        simpa only [Function.comp_id] using FieldRename.shared_y_map base id 2409
      simp only [logicalZero,EntryFieldSeedCancellation.selectedSwap,FieldRename.selectWindow_natural,
        FieldRename.swapRegisters_natural,rmap,ymap,unitI]
    have fr1 := OffsetBorrowedCanonical.cell_frame base (base 2400) (base 1) (base (1028+1))
      (base 2409) (base 2410) (unitI 1).1 (unitI 1).2 hn l1 hS hE origin hg0 hs0 env
    have mc1 := (cellFI_counts base (base 2400) (base 1) (base (1028+1)) (base 2409) (base 2410)
      (unitI 1).1 (unitI 1).2).1
    rw [zeroEq]
    apply seq_eq _ _ _ _ t r (by simp only [measurementCount_append,mc1]) ?_ ?_
    · apply seq_eq _ _ _ _ t _ rfl rfl
      exact cellFI_eq _ _ _ _ _ _ _ _ hn l1 hS hE origin hg0 hs0 env _ _ _ _ (sw t _ h).2
    · exact cellFI_eq _ _ _ _ _ _ _ _ hn l2 hS hE origin hg0 hs0 env _ _ _ _
        ((sw.seq (fr1 _ _)) t _ h).2

theorem firstGroupI_sub (divide : Bool) : InstrSub (firstGroupI divide) (firstGroup divide) := by
  rw [firstGroup_eq_rename]
  apply InstrSub.rename
  rw [baseFirstGroup_shape]
  exact ((InstrSub.refl _).append (firstBody_sub divide)).append (InstrSub.refl _)

theorem firstGroupI_counts (divide : Bool) :
    measurementCount (firstGroupI divide)=measurementCount (firstGroup divide) ∧
    toffoliCount (firstGroupI divide)+2=toffoliCount (firstGroup divide) := by
  have a := renameProgram_counts (shifted (pi 0)) (baseFirstGroupI divide)
  have b := renameProgram_counts (shifted (pi 0))
    (compressedHistoryDecode base 0 ++ oldFirstBody divide ++ compressedHistoryEncode base 0)
  have c := firstBody_counts divide
  rw [firstGroup_eq_rename,baseFirstGroup_shape]
  simp only [firstGroupI]
  rw [a.1,a.2,b.1,b.2]
  simp only [baseFirstGroupI,measurementCount_append,toffoliCount_append]
  constructor <;> omega

theorem firstGroupI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters 0))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (firstGroupI divide) m s=run (firstGroup divide) m s := by
  have hin := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  rw [firstGroup_eq_rename]
  apply rename_eq (pi 0) (fun q hq => pi_outside 0 q (by decide) hq) _ _ s m hin
  have support : wires (oldFirstBody divide) ⊆ groupReadSites base (base 2400) (base 2409) (base 2410) (3*0) := by
    cases divide
    · have h := inverseBody_support hn hlo
      simpa only [inverseBody,oldFirstBody,base_cell_eq,unitI,Bool.false_eq_true,if_false,Nat.mul_zero] using h
    · have h := EntryBodySupport.first_body_support hn hlo
      simpa only [oldFirstBody,base_cell_eq,unitI,if_true,Nat.mul_zero] using h
  have w := encoded_window_eq base _ _ _ hn hlo hp 0 (by decide) origin legal X Y _ _ support
    (firstBody_sub divide) (firstBody_counts divide).1
    (fun t r ht => firstBody_eq divide hn ho hf origin hg0 hs0 env X Y t r ht) s m input
  simp only [Nat.mul_zero] at w
  rw [baseFirstGroup_shape]
  exact w

/-! ### Endpoint cell 510 -/

def endBaseI (divide : Bool) : Program :=
  if divide then trimFI base (base 2400) (base 510) (base 2409) (unitI 510).1
  else trimII base (base 2400) (base 510) (base 2409) (unitI 510).1

def endI (divide : Bool) : Program := renameProgram (shifted pi0) (endBaseI divide)

theorem end_old_shape (divide : Bool) :
    renameProgram allPlaced (PenultimateSwapIdentity.cell divide)=
      renameProgram (shifted pi0) (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1) := by
  have rename : renameProgram allPlaced (PenultimateSwapIdentity.cell divide)=
      renameProgram (shifted pi0) (renameProgram base (PenultimateSwapIdentity.cell divide)) := by
    rw [renameProgram_comp]
    congr 1
  rw [rename,PenultimateMappedCellProof.cell_natural]
  rfl

theorem endBaseI_sub (divide : Bool) :
    InstrSub (endBaseI divide) (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1) := by
  have h := trim_sub base (base 2400) (base 510) (base 2409) (unitI 510).1
  cases divide <;> simp only [endBaseI,Bool.false_eq_true,if_false,if_true]
  · exact h.2
  · exact h.1

theorem endI_sub (divide : Bool) :
    InstrSub (endI divide) (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) := by
  rw [end_old_shape]
  exact (endBaseI_sub divide).rename _

theorem endI_counts (divide : Bool) :
    measurementCount (endI divide)=measurementCount (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) ∧
    toffoliCount (endI divide)+1=toffoliCount (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) := by
  rw [end_old_shape]
  have a := renameProgram_counts (shifted pi0) (endBaseI divide)
  have b := renameProgram_counts (shifted pi0) (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1)
  have c := trim_counts base (base 2400) (base 510) (base 2409) (unitI 510).1
  simp only [endI]
  cases divide <;> simp only [endBaseI,Bool.false_eq_true,if_false,if_true] at a b ⊢ <;> constructor <;> omega

theorem endI_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (endI divide) m s=run (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) m s := by
  have hin := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  rw [end_old_shape]
  apply rename_eq pi0 pi0_outside _ _ s m hin
  let unit := mixedTranscriptUnitTrace.getD 510 (false,false)
  have letter : tapeLetter 510=((base 510,base 1538),unit) := by
    simp only [tapeLetter,mixedTape_base_getD 510 (by decide),Nat.reduceAdd,unit]
  have layout : MixedTranscriptFieldLayout base (base 2400) (base 510) (base 1538)
      (base 2409) (base 2410) := by
    simpa only [mixedTape_base_getD 510 (by decide),Nat.reduceAdd] using
      mixedTape_getD_layout base (base 2400) (base 2409) (base 2410) hf 510 (by decide)
  have hl := balancedSharedTranscriptLayout_direct base (base 2400) (base 510)
    (base 1538) (base 2409) (base 2410) layout ho
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have rawEq : run (endBaseI divide) m raw=
      run (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1) m raw :=
    trim_eq divide base (base 2400) (base 510) (base 1538) (base 2409) (base 2410) (unitI 510).1
      hn hl (ho _ (by simp)) origin hg0 env X Y raw m frame
  have aligned : IndexedLetters base 510 [tapeLetter 510] := by
    simp only [letter,IndexedLetters]
    exact ⟨trivial,trivial⟩
  have dis := tail_replay_disjoint base (base 2400) (base 2409) (base 2410)
    hn hlo hp 510 [tapeLetter 510] (by omega) (by simp) aligned
  have oldDis : Disjoint (wires (allGroupEncode base 170))
      (wires (renameProgram base (logicalCell divide 510))) := by
    rw [FieldRename.logical_cell_natural]
    cases divide
    · simpa only [OffsetBorrowedInverseCanonical.replay,letter,List.append_nil,List.nil_append,
        Bool.false_eq_true,if_false,Nat.reduceAdd] using dis.2
    · simpa only [OffsetBorrowedCanonical.replay,letter,List.append_nil,List.nil_append,
        if_true,Nat.reduceAdd] using dis.1
  have sub : wires (if divide then EndpointSwapTrim.forward base (base 2400) (base 510)
        (base 2409) (unitI 510).1 else EndpointSwapTrim.inverse base (base 2400) (base 510)
        (base 2409) (unitI 510).1)⊆wires (renameProgram base (logicalCell divide 510)) := by
    have e := PenultimateMappedCellProof.cell_natural base divide
    have s2 : wires (renameProgram base (PenultimateSwapIdentity.cell divide))⊆
        wires (renameProgram base (logicalCell divide 510)) := by
      rw [renameProgram_support,renameProgram_support]
      exact Finset.image_mono base (PenultimateMappedCellProof.logical_support_subset divide)
    rw [e] at s2
    exact s2
  have oldDis' := oldDis.mono_right sub
  have newDis := oldDis'.mono_right (endBaseI_sub divide).wires_sub
  have newCommute := (run_disjoint_commute (allGroupEncode base 170) (endBaseI divide) newDis [] m raw).symm
  have oldCommute := (run_disjoint_commute (allGroupEncode base 170) _ oldDis' [] m raw).symm
  rw [encoded,newCommute,oldCommute,rawEq]

/-! ### Complete field segment -/

def replayI (divide : Bool) : Program :=
  if divide then firstGroupI true ++ mappedGroupsI true 1 169 ++ endI true
  else endI false ++ mappedGroupsI false 1 169 ++ firstGroupI false

def fieldSegmentI (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (converterPair false) ++ replayI divide ++
  renameProgram allPlaced (converterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

theorem fieldSegmentI_sub (divide : Bool) :
    InstrSub (fieldSegmentI divide) (PenultimateMapped.fieldSegment divide) := by
  have g := mappedGroupsI_sub divide 1 169 (by decide)
  cases divide <;> simp only [fieldSegmentI,PenultimateMapped.fieldSegment,replayI,PenultimateMapped.replay,
    Bool.false_eq_true,if_false,if_true]
  · exact ((((InstrSub.refl _).append (InstrSub.refl _)).append
      (((endI_sub false).append g).append (firstGroupI_sub false))).append (InstrSub.refl _)).append
      (InstrSub.refl _)
  · exact ((((InstrSub.refl _).append (InstrSub.refl _)).append
      (((firstGroupI_sub true).append g).append (endI_sub true))).append (InstrSub.refl _)).append
      (InstrSub.refl _)

theorem fieldSegmentI_counts (divide : Bool) :
    measurementCount (fieldSegmentI divide)=measurementCount (PenultimateMapped.fieldSegment divide) ∧
    toffoliCount (fieldSegmentI divide)+510=toffoliCount (PenultimateMapped.fieldSegment divide) := by
  have g := mappedGroupsI_counts divide 1 169 (by decide)
  have f := firstGroupI_counts divide
  have t := endI_counts divide
  cases divide <;> simp only [fieldSegmentI,PenultimateMapped.fieldSegment,replayI,PenultimateMapped.replay,
    Bool.false_eq_true,if_false,if_true,measurementCount_append,toffoliCount_append] <;>
    constructor <;> omega

theorem seq_eq_frame (P P' Q Q' : Program) (F : State → Prop) (s : State) (m : List Bool)
    (hc : measurementCount P'=measurementCount P)
    (hp : ∀ r, run P' r s=run P r s) (hF : ∀ r, F (run P r s))
    (hq : ∀ t r, F t → run Q' r t=run Q r t) :
    run (P'++Q') m s=run (P++Q) m s :=
  seq_eq P P' Q Q' s m hc (hp _) (hq _ _ (hF _))

theorem fieldSegmentI_eq (divide : Bool)
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
    run (fieldSegmentI divide) m s=run (PenultimateMapped.fieldSegment divide) m s := by
  have layouts := packet_layouts (base 2400) (base 2409) (base 2410) hf
  let E : Fp → Fp → State → Prop := fun X Y t => EncodedFieldFrame base (base 2409) origin X Y t
  cases divide
  · have shapeI : fieldSegmentI false=renameProgram allPlaced
        (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) ++
        (renameProgram allPlaced (converterPair false) ++ (endI false ++ (mappedGroupsI false 1 169 ++
        (firstGroupI false ++ renameProgram allPlaced (converterPair true))))) := by
      simp only [fieldSegmentI,replayI,Bool.false_eq_true,if_false,List.append_nil,List.append_assoc]
    have shapeO : PenultimateMapped.fieldSegment false=renameProgram allPlaced
        (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) ++
        (renameProgram allPlaced (converterPair false) ++
        (renameProgram allPlaced (PenultimateSwapIdentity.cell false) ++ (mappedGroups false 1 169 ++
        (firstGroup false ++ renameProgram allPlaced (converterPair true))))) := by
      simp only [PenultimateMapped.fieldSegment,PenultimateMapped.replay,Bool.false_eq_true,if_false,
        List.append_nil,List.append_assoc]
    rw [shapeI,shapeO]
    apply seq_eq_frame _ _ _ _ (fun t => EncodedCanonicalFrame origin Y Y t) s m rfl (fun _ => rfl)
      (fun r => by simpa only [copyPairAt] using (mapped_copy_fill hn origin Y s r input).2)
    intro s1 m1 c1
    apply seq_eq_frame _ _ _ _ (E Y Y) s1 m1 rfl (fun _ => rfl)
      (fun r => by
        have c := (encoded_center_pair hn origin hw hu hr hy Y Y s1 r c1).2
        rw [←converterPair_placement false] at c
        exact c)
    intro s2 m2 c2
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s2 m2 (endI_counts false).1
      (fun r => endI_eq false hn hlo ho hp hf origin hg0 hs0 env Y Y s2 r c2)
      (fun r => by
        rw [PenultimateMappedCellProof.inverse_cell_eq hn hlo ho hp hf origin hg0 hs0 env legal Y s2 r r c2]
        exact ⟨_,_,(trimCell_step false hn hlo ho hp hf origin hg0 hs0 env legal Y Y s2 r c2).2.2⟩)
    rintro s3 m3 ⟨X3,Y3,c3⟩
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s3 m3
      (mappedGroupsI_counts false 1 169 (by decide)).1
      (fun r => mappedGroupsI_eq false 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal _ _ s3 r c3)
      (fun r => ⟨_,_,(mappedGroups_frame false 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal
        _ _ s3 r c3).2.2⟩)
    rintro s4 m4 ⟨X4,Y4,c4⟩
    exact seq_eq _ _ _ _ s4 m4 (firstGroupI_counts false).1
      (firstGroupI_eq false hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal _ _ s4 _ c4) rfl
  · have shapeI : fieldSegmentI true=renameProgram allPlaced (converterPair false) ++
        (firstGroupI true ++ (mappedGroupsI true 1 169 ++ (endI true ++
        (renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced
          (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))))) := by
      simp only [fieldSegmentI,replayI,if_true,List.nil_append,List.append_assoc]
    have shapeO : PenultimateMapped.fieldSegment true=renameProgram allPlaced (converterPair false) ++
        (firstGroup true ++ (mappedGroups true 1 169 ++
        (renameProgram allPlaced (PenultimateSwapIdentity.cell true) ++
        (renameProgram allPlaced (converterPair true) ++ renameProgram allPlaced
          (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))))) := by
      simp only [PenultimateMapped.fieldSegment,PenultimateMapped.replay,if_true,List.nil_append,
        List.append_assoc]
    rw [shapeI,shapeO]
    apply seq_eq_frame _ _ _ _ (E Y 0) s m rfl (fun _ => rfl)
      (fun r => by
        have c := (encoded_center_pair hn origin hw hu hr hy Y 0 s r input).2
        rw [←converterPair_placement false] at c
        exact c)
    intro s1 m1 c1
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s1 m1 (firstGroupI_counts true).1
      (fun r => firstGroupI_eq true hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal Y 0 s1 r c1)
      (fun r => ⟨_,_,(firstGroup_forward_step hn hlo ho hp (layouts 0 (by decide)) origin hg0 hs0 env legal
        Y s1 r c1).2⟩)
    rintro s2 m2 ⟨X2,Y2,c2⟩
    apply seq_eq_frame _ _ _ _ (fun t => ∃ X' Y', E X' Y' t) s2 m2
      (mappedGroupsI_counts true 1 169 (by decide)).1
      (fun r => mappedGroupsI_eq true 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal _ _ s2 r c2)
      (fun r => ⟨_,_,(mappedGroups_frame true 1 169 (by decide) hn hlo ho hp layouts origin hg0 hs0 env legal
        _ _ s2 r c2).2.2⟩)
    rintro s3 m3 ⟨X3,Y3,c3⟩
    exact seq_eq _ _ _ _ s3 m3 (endI_counts true).1
      (endI_eq true hn hlo ho hp hf origin hg0 hs0 env _ _ s3 _ c3) rfl

/-! ### Public segment facts (same statements as for `selectedFieldSegment`) -/

theorem fieldSegmentI_support (divide : Bool) : wires (fieldSegmentI divide) ⊆ slots.toFinset :=
  (fieldSegmentI_sub divide).wires_sub.trans (selectedFieldSegment_support divide)

theorem fieldSegmentI_physical (divide : Bool) : GatePhysical (fieldSegmentI divide) :=
  (fieldSegmentI_sub divide).physical (selectedFieldSegment_physical divide)

theorem fieldSegmentI_resources (divide : Bool) :
    toffoliCount (fieldSegmentI divide)=(if divide then 656540 else 657050) ∧
    measurementCount (fieldSegmentI divide)=525980 := by
  have c := fieldSegmentI_counts divide
  have o := selectedFieldSegment_counts divide
  simp only [selectedFieldSegment] at o
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at o ⊢ <;> constructor <;> omega

end ECDSAAdd.Entrant.LaneI
