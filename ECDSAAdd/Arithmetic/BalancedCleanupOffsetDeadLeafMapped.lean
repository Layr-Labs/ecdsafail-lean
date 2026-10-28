import ECDSAAdd.Arithmetic.BalancedCleanupOffsetDeadLeaf
import ECDSAAdd.Framework.WireRenameEquivalence
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetDeadLeaf

def sites : Finset Wire := {16,17,18,19,20,21,22}

theorem old_support : wires oldLeaf⊆sites := by
  simp [oldLeaf,sites,BalancedCleanupOffset.prepareHead,BalancedCleanupOffset.releaseHead,
    bit,mappedMajority,mappedSum,mappedEraseCarry,majority,eraseCarry,flipBelow,
    wires,Instr.wires,correctionWires]
  decide

theorem new_support : wires newLeaf⊆sites := by
  simp [newLeaf,sites,bit,mappedSum,compareChain,majority,eraseCarry,flipBelow,
    wires,Instr.wires,correctionWires]
  decide

/-- Actual leaf equivalence on any injective physical placement of its seven
sites. No conditions are imposed on unrelated physical or logical positions. -/
theorem mapped_leaf_equiv (f : Wire → Wire)
    (hf : ∀a∈sites,∀b∈sites,f a=f b → a=b) (s : State) (mOld mNew : List Bool)
    (hc : s.basis (f 20)=false) (hd : s.basis (f 21)=false) :
    run (renameProgram f oldLeaf) mOld s=run (renameProgram f newLeaf) mNew s := by
  let t : State := ⟨s.phase,fun q => s.basis (f q)⟩
  apply run_rename_eq_of_eq f sites hf oldLeaf newLeaf old_support new_support
    mOld mNew t s rfl (fun _ _ => rfl)
  exact leaf_equiv t mOld mNew hc hd

end ECDSAAdd.Arithmetic.BalancedCleanupOffsetDeadLeaf
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetDeadLeaf.mapped_leaf_equiv
