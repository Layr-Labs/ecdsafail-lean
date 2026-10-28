import ECDSAAdd.Arithmetic.Paper935.WalkDecoderResources
import ECDSAAdd.Arithmetic.Paper935.SeededDecoderUndo
import ECDSAAdd.Arithmetic.Paper935.WalkRecoveryRecords

namespace ECDSAAdd.Arithmetic.Paper935

/-- Recovery uses the same history addresses plus the supplied decoder. -/
theorem HistoryLayout.recovery_support (H : HistoryLayout) (decoder : Program) (ordinal : Nat) :
    recordedWires (H.recovery decoder ordinal)=wires decoder∪recordedWires H.program := by
  have shifts : wires (popHistory H.output H.port H.record)=wires (pushHistory H.output H.port H.record) :=
    (ECDSAAdd.Arithmetic.shift_wires _ _).1.trans (ECDSAAdd.Arithmetic.shift_wires _ _).2.symm
  rw [HistoryLayout.recovery,recordedWires_append,
    (ECDSAAdd.Arithmetic.Divsteps.recoverBranch_resources _ _ _).2.2.1,embedRecorded_wires,
    storePop_support,shifts,HistoryLayout.program,storePushForget_support,storePush_support]
  ext q
  simp only [Finset.mem_union]
  tauto

/-- Compiler checks bound the inverse arithmetic and the recorded history
recovery; only the supplied decoder's support must be added. -/
theorem HistoricalWalkCompiled.reverse_support (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : HistoricalWalkCompiled F probeWidth A b record requests slots)
    (decoder : Nat → HistoricalSlot → Program)
    (support : ∀ Q∈slots,∀ i,wires (decoder i Q)⊆arenaWires) (index ordinal : Nat) :
    recordedWires (historicalWalkReverse F decoder index ordinal slots)⊆arenaWires := by
  induction compiled generalizing index ordinal with
  | nil => simp [historicalWalkReverse,recordedWires]
  | cons A b record r rs Q rest head tail ih =>
    have checked := compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ head
    have arithmeticCompiled := (compileHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ checked.1).1
    have arithmetic := (compileCheckedPublicSlot_resources _ _ _ _ _ _ _ _ _ arithmeticCompiled).2.2
    have restSupport := ih (fun P hp i => support P (List.mem_cons_of_mem Q hp) i) (index+1)
      (ordinal+recordedMeasurementCount (Q.program F))
    rw [historicalWalkReverse,recordedWires_append]
    refine Finset.union_subset restSupport ?_
    rw [HistoricalSlot.undo,recordedWires_append,HistoryLayout.recovery_support,embedRecorded_wires]
    exact Finset.union_subset (Finset.union_subset (support Q (by simp) index) checked.2.2) arithmetic

theorem compileAuthorWalk_reverse_support (p : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (ordinal : Nat) :
    recordedWires (historicalWalkReverse walkRegisters (actualHistoryDecoder walkRegisters p) 0 ordinal slots)⊆arenaWires := by
  have contract := compileHistoricalWalk_contract walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots compiled
  exact contract.reverse_support _ _ _ _ _ _ _ (actualHistoryDecoder walkRegisters p)
    (fun Q hQ i => compileAuthorWalk_decoder_support slots compiled Q hQ p i) 0 ordinal

end ECDSAAdd.Arithmetic.Paper935
