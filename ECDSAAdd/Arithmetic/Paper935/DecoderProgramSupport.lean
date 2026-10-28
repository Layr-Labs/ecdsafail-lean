import ECDSAAdd.Arithmetic.Paper935.SlotDecoderCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- A single support calculation covers control reconstruction, the shared
finite-depth program, and control cleanup. -/
theorem paddedCleanBranch_support (padding : Program) (layouts : List DepthLayout) (p : Int)
    (frozen fire active second sigma port : Wire) (rb : List ZeroBit) (k : Nat)
    (W : Finset Wire) (hp : wires padding⊆W)
    (hd : wires (finiteDepthProgram layouts p)⊆W)
    (hc : (frozen::fire::active::second::sigma::port::rb.flatMap ZeroBit.wires).toFinset⊆W) :
    wires (paddedCleanBranch padding layouts p frozen fire active second sigma port rb k)⊆W := by
  have core : wires (historyControlCore frozen fire active second sigma)⊆W := by
    intro q hq
    apply hc
    simp [historyControlCore,wires,Instr.wires] at hq
    simp only [List.mem_toFinset,List.mem_cons]
    tauto
  have finish : wires (finishBranch sigma fire port)⊆W := by
    intro q hq
    apply hc
    simp [finishBranch,wires,Instr.wires] at hq
    simp only [List.mem_toFinset,List.mem_cons]
    tauto
  have compare : wires (equalConstant frozen fire rb k)⊆W := by
    rw [equalConstant_wires]
    intro q hq
    apply hc
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    tauto
  simp only [paddedCleanBranch,cleanBranchProgram,mintHistoryControls,clearHistoryControls,
    finiteBranchProgram,wires_append,wires_reverse]
  exact Finset.union_subset hp (Finset.union_subset
    (Finset.union_subset (Finset.union_subset compare core)
      (Finset.union_subset (Finset.union_subset hd finish) (Finset.union_subset core compare))) hp)

end ECDSAAdd.Arithmetic.Paper935
