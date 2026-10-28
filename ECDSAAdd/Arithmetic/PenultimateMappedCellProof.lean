import ECDSAAdd.Arithmetic.PenultimateSwapIdentity
import ECDSAAdd.Arithmetic.TerminalMappedReplayReference
import ECDSAAdd.Arithmetic.FieldRenameCells

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.PenultimateMappedCellProof
open Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
open OffsetBorrowedCanonical
attribute [local irreducible] run wires mixedTranscriptUnitTrace mixedTranscriptTape

private theorem forward_natural (f w : Wire → Wire) (b g flag : Wire) (ig : Bool) :
    renameProgram f (EndpointSwapTrim.forward w b g flag ig)=
      EndpointSwapTrim.forward (f ∘ w) (f b) (f g) (f flag) ig := by
  simp only [EndpointSwapTrim.forward,FieldRename.selectWindow_natural,
    FieldRename.rename_append,FieldRename.forward_program_natural]
  rfl

private theorem inverse_natural (f w : Wire → Wire) (b g flag : Wire) (ig : Bool) :
    renameProgram f (EndpointSwapTrim.inverse w b g flag ig)=
      EndpointSwapTrim.inverse (f ∘ w) (f b) (f g) (f flag) ig := by
  simp only [EndpointSwapTrim.inverse,FieldRename.selectWindow_natural,
    FieldRename.rename_append,FieldRename.inverse_program_natural]
  rfl

/-- Naturality of the actual new raw cell; no input-state premise. -/
theorem cell_natural (f : Wire → Wire) (divide : Bool) :
    renameProgram f (PenultimateSwapIdentity.cell divide)=
      if divide then EndpointSwapTrim.forward f (f 2400) (f 510) (f 2409)
        (mixedTranscriptUnitTrace.getD 510 (false,false)).1
      else EndpointSwapTrim.inverse f (f 2400) (f 510) (f 2409)
        (mixedTranscriptUnitTrace.getD 510 (false,false)).1 := by
  cases divide <;> simp only [PenultimateSwapIdentity.cell,Bool.false_eq_true,
    if_false,if_true,forward_natural,inverse_natural,Function.comp_id]

private theorem window_mono (b src flag : Wire) (constant : Bool) (P Q : Program)
    (h : wires P⊆wires Q) :
    wires (transcriptSelectWindow b src flag constant P)⊆
      wires (transcriptSelectWindow b src flag constant Q) := by
  intro q hq
  have body : q∈wires P → q∈wires Q := fun hp => h hp
  simp only [transcriptSelectWindow,wires_append,Finset.mem_union] at hq ⊢
  tauto

private theorem body_window (b src flag : Wire) (constant : Bool) (P : Program) :
    wires P⊆wires (transcriptSelectWindow b src flag constant P) := by
  intro q hq
  simp only [transcriptSelectWindow,wires_append,Finset.mem_union]
  tauto

/-- The omitted S window/swap introduce no replacement sites or corrections. -/
theorem logical_support_subset (divide : Bool) :
    wires (PenultimateSwapIdentity.cell divide)⊆wires (logicalCell divide 510) := by
  cases divide
  · simp only [PenultimateSwapIdentity.cell,logicalCell,Bool.false_eq_true,if_false,
      EndpointSwapTrim.inverse,OffsetBorrowedInverseCanonical.cell]
    apply window_mono
    have inner : wires ([.X 2409]++OffsetBorrowedInverse.program id 2409++[.X 2409])⊆
        wires (OffsetBorrowedInverseCanonical.body id 2409 2410) := by
      intro q hq
      simp only [OffsetBorrowedInverseCanonical.body,OffsetBorrowedInverseCanonical.double,
        wires_append,Finset.mem_union] at hq ⊢
      tauto
    exact inner.trans (body_window _ _ _ _ _)
  · simp only [PenultimateSwapIdentity.cell,logicalCell,if_true,
      EndpointSwapTrim.forward,OffsetBorrowedCanonical.cell]
    apply window_mono
    have inner : wires ([.X 2409]++OffsetBorrowedField.program id 2409++[.X 2409])⊆
        wires (OffsetBorrowedCanonical.body id 2409 2410) := by
      intro q hq
      simp only [OffsetBorrowedCanonical.body,wires_append,Finset.mem_union] at hq ⊢
      tauto
    exact inner.trans (body_window _ _ _ _ _)

theorem support_subset (divide : Bool) :
    wires (renameProgram allPlaced (PenultimateSwapIdentity.cell divide))⊆
      wires (renameProgram allPlaced (logicalCell divide 510)) := by
  rw [renameProgram_support,renameProgram_support]
  exact Finset.image_mono allPlaced (logical_support_subset divide)

/-- Forward duplication is the actual half output; inverse duplication is its input. -/
def Condition (divide : Bool) (origin : BasisState) (X Y : Fp) : Prop :=
  if divide then
    (X+(if mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.1
      (tapeLetter 510).2.1 then Y else -Y))/2=Y
  else X=Y

private theorem base_cell_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (X Y : Fp) (s : State) (mNew mOld : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (cond : Condition divide origin X Y) :
    run (renameProgram base (PenultimateSwapIdentity.cell divide)) mNew s=
      run (renameProgram base (logicalCell divide 510)) mOld s := by
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
  have rawEq : run (renameProgram base (PenultimateSwapIdentity.cell divide)) mNew raw=
      run (renameProgram base (logicalCell divide 510)) mOld raw := by
    rw [cell_natural,FieldRename.logical_cell_natural]
    simp only [Nat.reduceAdd]
    cases divide
    · simp only [Condition,Bool.false_eq_true,if_false] at cond
      subst X
      simp only [Bool.false_eq_true,if_false]
      exact EndpointSwapTrim.inverse_oldcell_eq base _ _ _ _ _ unit.1 unit.2
        hn hl (ho _ (by simp)) (ho _ (by simp)) origin hg0 hs0 env Y raw mNew mOld frame
    · simp only [Condition,if_true,letter] at cond
      simp only [if_true]
      exact EndpointSwapTrim.forward_oldcell_eq base _ _ _ _ _ unit.1 unit.2
        hn hl (ho _ (by simp)) (ho _ (by simp)) origin hg0 hs0 env X Y cond raw mNew mOld frame
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
  have sub : wires (renameProgram base (PenultimateSwapIdentity.cell divide))⊆
      wires (renameProgram base (logicalCell divide 510)) := by
    rw [renameProgram_support,renameProgram_support]
    exact Finset.image_mono base (logical_support_subset divide)
  have newDis := oldDis.mono_right sub
  have newCommute := (run_disjoint_commute (allGroupEncode base 170)
    (renameProgram base (PenultimateSwapIdentity.cell divide)) newDis [] mNew raw).symm
  have oldCommute := (run_disjoint_commute (allGroupEncode base 170)
    (renameProgram base (logicalCell divide 510)) oldDis [] mOld raw).symm
  rw [encoded,newCommute,oldCommute,rawEq]

/-- Complete mapped State equality, including spectators and every independent tape. -/
theorem cell_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (mNew mOld : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (cond : Condition divide origin X Y) :
    run (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) mNew s=
      run (renameProgram allPlaced (logicalCell divide 510)) mOld s := by
  have eq := base_cell_eq divide hn hlo ho hp hf origin hg0 hs0 env X Y s mNew mOld input cond
  have old := trimCell_step divide hn hlo ho hp hf origin hg0 hs0 env legal X Y s mOld input
  have hin := encoded_zero_region base _ hn hlo origin env X Y s input
  have hout := encoded_zero_region base _ hn hlo origin env _ _ _ old.2.2
  have newOutZero : ∀q,zeroRegion q →
      (run (renameProgram base (PenultimateSwapIdentity.cell divide)) mNew s).basis (base q)=false := by
    rw [eq,←old.1]
    exact hout
  have pin := shifted_zero_boundary pi0 pi0_outside s hin
  have pout := shifted_zero_boundary pi0 pi0_outside _ newOutZero
  have rename : renameProgram allPlaced (PenultimateSwapIdentity.cell divide)=
      renameProgram (shifted pi0) (renameProgram base (PenultimateSwapIdentity.cell divide)) := by
    rw [renameProgram_comp]
    congr 1
  have placed : run (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) mNew s=
      run (renameProgram base (PenultimateSwapIdentity.cell divide)) mNew s := by
    apply pullState_perm_injective (shifted pi0)
    rw [rename,run_rename _ (shifted pi0).injective,pin,pout]
  exact placed.trans (eq.trans old.1.symm)

theorem forward_cell_eq
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (mNew mOld : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s)
    (dup : (X+(if mixedTranscriptBit origin (base 2400) (tapeLetter 510).1.1
      (tapeLetter 510).2.1 then Y else -Y))/2=Y) :
    run (renameProgram allPlaced (PenultimateSwapIdentity.cell true)) mNew s=
      run (renameProgram allPlaced (logicalCell true 510)) mOld s :=
  cell_eq true hn hlo ho hp hf origin hg0 hs0 env legal X Y s mNew mOld input dup

theorem inverse_cell_eq
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (Y : Fp)
    (s : State) (mNew mOld : List Bool) (input : EncodedFieldFrame base (base 2409) origin Y Y s) :
    run (renameProgram allPlaced (PenultimateSwapIdentity.cell false)) mNew s=
      run (renameProgram allPlaced (logicalCell false 510)) mOld s :=
  cell_eq false hn hlo ho hp hf origin hg0 hs0 env legal Y Y s mNew mOld input rfl

end ECDSAAdd.Arithmetic.PenultimateMappedCellProof
#print axioms ECDSAAdd.Arithmetic.PenultimateMappedCellProof.cell_natural
#print axioms ECDSAAdd.Arithmetic.PenultimateMappedCellProof.support_subset
#print axioms ECDSAAdd.Arithmetic.PenultimateMappedCellProof.forward_cell_eq
#print axioms ECDSAAdd.Arithmetic.PenultimateMappedCellProof.inverse_cell_eq
