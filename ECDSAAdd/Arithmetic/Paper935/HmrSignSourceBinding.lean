import ECDSAAdd.Arithmetic.Paper935.SignPlacedExecution
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulPrefixEquivalence
import ECDSAAdd.Arithmetic.Paper935.HmrSourceLifecycleFacts

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def s2SignMap : Wire → Wire := fusedPlacementMap (768 :: s2HmrSourceOut ++ s2HmrSeamPorts.anc)
def s6SignMap : Wire → Wire := fusedPlacementMap (795 :: s6HmrSourceOut ++ s6HmrSeamPorts.anc)

theorem s2SignMap_injective : Set.InjOn s2SignMap (Finset.range 281) := by
  apply fusedPlacementMap_injective
  · decide +kernel
  · exact List.Nodup.injective_get (by decide +kernel)

theorem s6SignMap_injective : Set.InjOn s6SignMap (Finset.range 281) := by
  apply fusedPlacementMap_injective
  · decide +kernel
  · exact List.Nodup.injective_get (by decide +kernel)

theorem s2SignMap_rowSign_outside : s2HmrSourceRow.sign∉(Finset.range 281).image s2SignMap := by decide +kernel
theorem s6SignMap_rowSign_outside : s6HmrSourceRow.sign∉(Finset.range 281).image s6SignMap := by decide +kernel

private theorem s2_checked : rowMulPrefixEq s2SourceSign
    (embedRecorded (placedSignFix s2SignMap s2HmrSourceRow.sign false)) = true := by decide +kernel
private theorem s6_checked : rowMulPrefixEq s6SourceSign
    (embedRecorded (placedSignFix s6SignMap s6HmrSourceRow.sign false)) = true := by decide +kernel
private theorem s6_inv_checked : rowMulPrefixEq s6SourceUnsign
    (embedRecorded (placedSignFix s6SignMap s6HmrSourceRow.sign true)) = true := by decide +kernel

theorem s2SignMap_pool : (List.range 24).map (fun i => s2SignMap (257+i)) = s2HmrSeamPorts.anc := by decide +kernel
theorem s6SignMap_pool : (List.range 24).map (fun i => s6SignMap (257+i)) = s6HmrSeamPorts.anc := by decide +kernel

attribute [local irreducible] s2SourceSign s6SourceSign s6SourceUnsign placedSignFix s2SignMap s6SignMap

theorem s2SourceSign_run (tape : List Bool) (cursor : Nat) (s : State) :
    runWithTape s2SourceSign tape cursor s =
      run (placedSignFix s2SignMap s2HmrSourceRow.sign false) (tape.drop cursor) s := by
  have h := congrArg Prod.fst (rowMulPrefixEq_sound _ _ s2_checked ⟨tape,cursor⟩ s)
  exact h.trans (runWithTape_embedRecorded _ tape cursor s)

theorem s6SourceSign_run (tape : List Bool) (cursor : Nat) (s : State) :
    runWithTape s6SourceSign tape cursor s =
      run (placedSignFix s6SignMap s6HmrSourceRow.sign false) (tape.drop cursor) s := by
  have h := congrArg Prod.fst (rowMulPrefixEq_sound _ _ s6_checked ⟨tape,cursor⟩ s)
  exact h.trans (runWithTape_embedRecorded _ tape cursor s)

theorem s6SourceUnsign_run (tape : List Bool) (cursor : Nat) (s : State) :
    runWithTape s6SourceUnsign tape cursor s =
      run (placedSignFix s6SignMap s6HmrSourceRow.sign true) (tape.drop cursor) s := by
  have h := congrArg Prod.fst (rowMulPrefixEq_sound _ _ s6_inv_checked ⟨tape,cursor⟩ s)
  exact h.trans (runWithTape_embedRecorded _ tape cursor s)

end ECDSAAdd.Arithmetic.Paper935
