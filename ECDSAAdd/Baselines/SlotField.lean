import ECDSAAdd.Baselines.SlotParity
import ECDSAAdd.Baselines.SlotCodec

namespace ECDSAAdd.Baselines
open Arithmetic Challenge
attribute [local irreducible] renameProgram copyRegister mixedTranscriptUnitTrace MappedCompressed.logicalCell
  MappedCompressed.mappedGroup MappedCompressed.mappedGroups
  OffsetBorrowedField.program OffsetBorrowedInverse.program
  compressedHistoryEncode compressedHistoryDecode
  EntryMappedFieldSegmentTrim.logicalZero EntryMappedFieldSegmentTrim.firstGroup
  PenultimateSwapIdentity.cell MappedCompressed.converterPair
  transcriptSelectWindow OffsetBorrowedCanonical.body OffsetBorrowedInverseCanonical.body

theorem selectWindow_gateSlots_le (b s f : Wire) (c : Bool) (p : Program) :
    gateSlots (transcriptSelectWindow b s f c p) ≤ gateSlots p+8 := by
  cases c <;> simp [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
    transcriptSelectErase,gateSlots_cons,instructionSlots] <;> omega

theorem borrowedField_gateSlots_le (w : Nat → Wire) (sign : Wire) :
    gateSlots (OffsetBorrowedField.program w sign) ≤ 26000 ∧
    gateSlots (OffsetBorrowedInverse.program w sign) ≤ 26000 := by
  have h := balancedCore_gateSlots_le (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  have p := offsetParity_gateSlots_le (OffsetCleanupBorrowedCaller.layout w sign) (OffsetCleanupBorrowedCaller.widths w sign)
  simp only [OffsetBorrowedField.program,OffsetBorrowedInverse.program,OffsetBorrowedInverse.recoverParity,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

theorem borrowedCell_gateSlots_le (w : Nat → Wire) (b g sw sign eff : Wire) (ig is : Bool) :
    gateSlots (OffsetBorrowedCanonical.cell w b g sw sign eff ig is) ≤ 27000 ∧
    gateSlots (OffsetBorrowedInverseCanonical.cell w b g sw sign eff ig is) ≤ 27000 := by
  have h := borrowedField_gateSlots_le w sign
  have len := (BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)).2.1
  have hs : gateSlots (swapRegisters eff (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y) ≤ 768 := by
    rw [swapRegisters_gateSlots]
    rw [len]; omega
  have a := selectWindow_gateSlots_le b sw eff is (OffsetBorrowedCanonical.body w sign eff)
  have aa := selectWindow_gateSlots_le b g sign ig (transcriptSelectWindow b sw eff is (OffsetBorrowedCanonical.body w sign eff))
  have z := selectWindow_gateSlots_le b sw eff is (OffsetBorrowedInverseCanonical.body w sign eff)
  have zz := selectWindow_gateSlots_le b g sign ig (transcriptSelectWindow b sw eff is (OffsetBorrowedInverseCanonical.body w sign eff))
  simp only [OffsetBorrowedCanonical.cell,OffsetBorrowedInverseCanonical.cell,
    OffsetBorrowedCanonical.body,OffsetBorrowedInverseCanonical.body,OffsetBorrowedInverseCanonical.double,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots] at a z aa zz ⊢
  omega

theorem logicalCell_gateSlots_le (divide : Bool) (i : Nat) :
    gateSlots (MappedCompressed.logicalCell divide i) ≤ 27000 := by
  have h := borrowedCell_gateSlots_le id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1 (mixedTranscriptUnitTrace.getD i (false,false)).2
  cases divide <;> simp only [MappedCompressed.logicalCell,Bool.false_eq_true,↓reduceIte]
  · exact h.2
  · exact h.1

theorem mappedGroup_gateSlots_le (divide : Bool) (j : Nat) :
    gateSlots (MappedCompressed.mappedGroup divide j) ≤ 82000 := by
  have a := logicalCell_gateSlots_le divide (3*j)
  have b := logicalCell_gateSlots_le divide (3*j+1)
  have c := logicalCell_gateSlots_le divide (3*j+2)
  have h := codec_gateSlots_le (MappedCompressed.placed j) (3*j)
  cases divide <;> simp only [MappedCompressed.mappedGroup,Bool.false_eq_true,↓reduceIte,
    gateSlots_append,rename_gateSlots] <;> omega

theorem mappedGroups_gateSlots_le (divide : Bool) (j n : Nat) :
    gateSlots (MappedCompressed.mappedGroups divide j n) ≤ n*82000 := by
  induction n generalizing j with
  | zero => simp only [MappedCompressed.mappedGroups,gateSlots_nil,Nat.zero_mul,Nat.le_refl]
  | succ n ih =>
    have h := mappedGroup_gateSlots_le divide j
    have ht := ih (j+1)
    cases divide <;> simp only [MappedCompressed.mappedGroups,Bool.false_eq_true,↓reduceIte,
      gateSlots_append,Nat.succ_mul] <;> omega

theorem firstGroup_gateSlots_le (divide : Bool) :
    gateSlots (EntryMappedFieldSegmentTrim.firstGroup divide) ≤ 56000 := by
  have a := logicalCell_gateSlots_le divide 1
  have b := logicalCell_gateSlots_le divide 2
  have hc := codec_gateSlots_le (MappedCompressed.placed 0) 0
  have hz : gateSlots EntryMappedFieldSegmentTrim.logicalZero ≤ 800 := by
    have h := selectWindow_gateSlots_le 2400 1028 2410
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2
      (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)
    have hl := (BalancedCleanup.widths (balancedSharedPorts id 2409).toLayout (balancedSharedPorts_widths id 2409)).2.1
    rw [swapRegisters_gateSlots] at h
    change _ ≤ 3*min (balancedSharedPorts id 2409).toLayout.r.length _ + 8 at h
    rw [hl] at h
    have hb : gateSlots (transcriptSelectWindow 2400 1028 2410
        (mixedTranscriptUnitTrace.getD 0 (false,false)).2
        (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)) ≤ 800 := by omega
    simpa only [EntryMappedFieldSegmentTrim.logicalZero,EntryFieldSeedCancellation.selectedSwap] using hb
  cases divide <;> simp only [EntryMappedFieldSegmentTrim.firstGroup,Bool.false_eq_true,↓reduceIte,
    gateSlots_append,rename_gateSlots] <;> omega

theorem endpointCell_gateSlots_le (w : Nat → Wire) (b g flag : Wire) (ig : Bool) :
    gateSlots (EndpointSwapTrim.forward w b g flag ig) ≤ 27000 ∧
    gateSlots (EndpointSwapTrim.inverse w b g flag ig) ≤ 27000 := by
  have h := borrowedField_gateSlots_le w flag
  have a := selectWindow_gateSlots_le b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])
  have z := selectWindow_gateSlots_le b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])
  simp only [EndpointSwapTrim.forward,EndpointSwapTrim.inverse,gateSlots_append,
    gateSlots_cons,gateSlots_nil,instructionSlots] at a z ⊢
  omega

theorem penultimateCell_gateSlots_le (divide : Bool) :
    gateSlots (PenultimateSwapIdentity.cell divide) ≤ 27000 := by
  have bound (unit : Bool × Bool) : gateSlots
      (if divide then EndpointSwapTrim.forward id 2400 510 2409 unit.1
        else EndpointSwapTrim.inverse id 2400 510 2409 unit.1) ≤ 27000 := by
    have h := endpointCell_gateSlots_le id 2400 510 2409 unit.1
    cases divide
    · exact h.2
    · exact h.1
  simpa only [PenultimateSwapIdentity.cell] using bound (mixedTranscriptUnitTrace.getD 510 (false,false))

theorem converterPair_gateSlots_le (canonical : Bool) :
    gateSlots (MappedCompressed.converterPair canonical) ≤ 24000 := by
  have a := balancedConvert_gateSlots_le (balancedSharedTargetConvert id) (balancedSharedTargetConvert_widths id)
  have b := balancedConvert_gateSlots_le (balancedSharedSourceConvert id) (balancedSharedSourceConvert_widths id)
  cases canonical <;> simp only [MappedCompressed.converterPair,Bool.false_eq_true,↓reduceIte,
    gateSlots_append] <;> omega

theorem fieldSegment_gateSlots_le (divide : Bool) :
    gateSlots (MappedCompressed.selectedFieldSegment divide) ≤ 14100000 := by
  have g := mappedGroups_gateSlots_le divide 1 169
  have f := firstGroup_gateSlots_le divide
  have p := penultimateCell_gateSlots_le divide
  have a := converterPair_gateSlots_le false
  have b := converterPair_gateSlots_le true
  have hcopy : gateSlots (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) ≤ 257 := by
    rw [copyRegister_gateSlots]
    have hl : (skywalkSharedField id).z.length = 257 := by simp only [ModInPlaceLayout.z,ModAddCoreLayout.z,skywalkSharedField,List.length_append,List.length_singleton,wireBlock_length]
    rw [hl]; omega
  have replayEq (A B C : Program) (d : Bool) :
      gateSlots (if d then A++B++C else C++B++A) = gateSlots A+gateSlots B+gateSlots C := by
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte,gateSlots_append]
    omega
  have rep : gateSlots (PenultimateMapped.replay divide) ≤ 13941000 := by
    rw [PenultimateMapped.replay, replayEq,rename_gateSlots]
    omega
  have segmentEq (P Q R S : Program) (d : Bool) :
      gateSlots ((if d then [] else P)++Q++R++S++(if d then P else [])) =
        gateSlots P+gateSlots Q+gateSlots R+gateSlots S := by
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte,gateSlots_append,gateSlots_nil] <;> omega
  rw [MappedCompressed.selectedFieldSegment,PenultimateMapped.fieldSegment,segmentEq,
    rename_gateSlots,rename_gateSlots,rename_gateSlots]
  omega

end ECDSAAdd.Baselines
