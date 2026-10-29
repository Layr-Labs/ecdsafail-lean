import ECDSAAdd.Submission.Entrant.HalfField
import ECDSAAdd.Submission.Entrant.ArithAvoid
import ECDSAAdd.Baselines.SlotField

/-! Resource facts for the halving-endpoint field segment that the Lane A
kernel needs besides its contract: avoided logical labels and a gate-slot
bound.  The segment is the unchanged entry-trimmed replay plus two halving
converters and one narrow copy, all on field sites. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HalfLane
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed Secp256k1

section Avoid
attribute [local irreducible] wires

theorem segment_avoid (divide : Bool) : Avoid (HalfField.segment divide) := by
  have rp : Avoid (PenultimateMapped.replay divide) :=
    avoid_sub (HalfField.replay_sub divide) (selectedFieldSegment_avoid divide)
  have idsGood (P : Program) (h : wires P⊆(HalfField.ids.map base).toFinset) : Avoid P := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (h hq))
    apply base_good
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
      or_false] at hi
    unfold badIdx
    omega
  have ce := idsGood _ HalfField.centerT_sites
  have ca := idsGood _ HalfField.canonT_sites
  have co := idsGood _ HalfField.copyN_sites
  cases divide <;> simp only [HalfField.segment,Bool.false_eq_true,if_false,if_true,avoid_append]
  · exact ⟨ce,co,rp,ca⟩
  · exact ⟨ce,rp,co,ca⟩

end Avoid

section Slots
open Challenge Baselines
attribute [local irreducible] renameProgram copyRegister mixedTranscriptUnitTrace MappedCompressed.logicalCell
  MappedCompressed.mappedGroup MappedCompressed.mappedGroups
  EntryMappedFieldSegmentTrim.firstGroup PenultimateSwapIdentity.cell
  mappedAdd mappedSub rotateRight rotateLeft

theorem replay_gateSlots_le (divide : Bool) :
    gateSlots (PenultimateMapped.replay divide) ≤ 13941000 := by
  have g := mappedGroups_gateSlots_le divide 1 169
  have f := firstGroup_gateSlots_le divide
  have p := penultimateCell_gateSlots_le divide
  have replayEq (A B C : Program) (d : Bool) :
      gateSlots (if d then A++B++C else C++B++A) = gateSlots A+gateSlots B+gateSlots C := by
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte,gateSlots_append]
    omega
  rw [PenultimateMapped.replay,replayEq,rename_gateSlots]
  omega

theorem convert_gateSlots_le :
    gateSlots HalfField.centerT ≤ 6000 ∧ gateSlots HalfField.canonT ≤ 6000 := by
  have w : HalfField.tgt.word.length=256 :=
    BalancedConvert.word_length _ (balancedSharedTargetConvert_widths base)
  have a := mappedAdd_gateSlots_le (HalfConvert.correction HalfField.tgt)
    HalfField.tgt.word HalfField.tgt.carry HalfField.tgt.cin
  have b := mappedSub_gateSlots_le (HalfConvert.correction HalfField.tgt)
    HalfField.tgt.word HalfField.tgt.carry HalfField.tgt.cin
  obtain ⟨r1,r2⟩ := rotate_gateSlots_le HalfField.tgt.word
  rw [HalfConvert.correction_length] at a b
  rw [w] at r1 r2 b
  simp only [HalfField.centerT,HalfField.canonT,HalfConvert.center,HalfConvert.canonical,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

theorem segment_gateSlots_le (divide : Bool) :
    gateSlots (HalfField.segment divide) ≤ 14100000 := by
  have rp := replay_gateSlots_le divide
  have cv := convert_gateSlots_le
  have cp : gateSlots HalfField.copyN ≤ 256 := by
    simp only [HalfField.copyN,HalfField.ports,copyRegister_gateSlots,balancedSharedPorts_r,wireBlock_length]
    omega
  cases divide <;> simp only [HalfField.segment,Bool.false_eq_true,↓reduceIte,gateSlots_append] <;> omega

end Slots

end ECDSAAdd.Entrant.HalfLane
