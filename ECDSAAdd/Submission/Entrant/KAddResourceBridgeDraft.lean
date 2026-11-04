import ECDSAAdd.Submission.Entrant.KAddCallerBridgeDraft

/-! Private generic full-adder support and conditional validity transport.
No actual caller, certificate, aggregate resource count or retirement claim. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.KAddResourceBridgeResearch
open Arithmetic RecordedQuantum Challenge KAddCallerBridgeResearch HighOutputTailStructuredResearch
attribute [local irreducible] ECDSAAdd.wires

/-- Splice a finite leaf while keeping the arbitrary prefix/suffix opaque. -/
private theorem splice_support (p old new r : Program) (extra : Finset Wire)
    (hn : wires new ⊆ wires old ∪ extra) :
    wires (p++new++r) ⊆ wires (p++old++r) ∪ extra := by
  simp only [wires_append]
  intro q h
  rcases Finset.mem_union.mp h with hLeft | hR
  · rcases Finset.mem_union.mp hLeft with hP | hNew
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hP))
    · rcases Finset.mem_union.mp (hn hNew) with hOld | hExtra
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hOld))
      · exact Finset.mem_union_right _ hExtra
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hR)

private theorem zero_leaf_support (a b c A B z : Wire) :
    wires (newLeafAt false a b c A B) ⊆ wires (oldLeafAt a b c A B z) := by
  rw [(HighOutputTailStructuredResearch.support false a b c A B z).2,
    (HighOutputTailStructuredResearch.support false a b c A B z).1]
  intro q h
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem flag_leaf_support (flag a b c A B z : Wire) :
    wires (HighOutputFlagResearch.newFlagAt flag a b c A B) ⊆
      wires (oldLeafAt a b c A B z) ∪ {flag} := by
  rw [HighOutputFlagResearch.support,
    (HighOutputTailStructuredResearch.support false a b c A B z).1]
  intro q h
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The support bound is structural and needs no injectivity premise. -/
theorem flag_support (w : Nat → Wire) :
    wires (flagKAdd w) ⊆ wires (literalKAdd w) ∪ {w 1028} := by
  have h := splice_support (P w)
    (oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796))
    (HighOutputFlagResearch.newFlagAt (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027))
    (R w) {w 1028} (flag_leaf_support _ _ _ _ _ _ _)
  exact (congrArg (fun s : Finset Wire => wires (flagKAdd w) ⊆ s ∪ {w 1028})
    (congrArg ECDSAAdd.wires (literal_split w))).mpr h

theorem zero_support (w : Nat → Wire) :
    wires (zeroKAdd w) ⊆ wires (literalKAdd w) := by
  have h := splice_support (P w)
    (oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796))
    (newLeafAt false (w 256) (w 1026) (w 1795) (w 257) (w 1027)) (R w) ∅
    (by simpa only [Finset.union_empty] using zero_leaf_support (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796))
  have hs : wires (zeroKAdd w) ⊆ wires (P w++oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)++R w) := by
    simpa only [Finset.union_empty] using h
  exact (congrArg (fun s : Finset Wire => wires (zeroKAdd w) ⊆ s)
    (congrArg ECDSAAdd.wires (literal_split w))).mpr hs

/-- Pointwise properties of unchanged P/R inherit from the old whole program. -/
private theorem splice_valid (V : Instr → Prop) (p old new r : Program)
    (ho : ∀i∈p++old++r,V i) (hn : ∀i∈new,V i) : ∀i∈p++new++r,V i := by
  intro i hi
  rcases List.mem_append.mp hi with hLeft | hR
  · rcases List.mem_append.mp hLeft with hP | hNew
    · exact ho i (List.mem_append_left r (List.mem_append_left old hP))
    · exact hn i hNew
  · exact ho i (List.mem_append_right (p++old) hR)

/-- Weak recorded-gate physicality is transported as exactly that property. -/
theorem flag_gatePhysical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ho : GatePhysical (literalKAdd w)) : GatePhysical (flagKAdd w) := by
  have old := (congrArg GatePhysical (literal_split w)).mp ho
  exact splice_valid (fun i => PhysicalInstr (.gate i)) (P w)
    (oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796))
    (HighOutputFlagResearch.newFlagAt (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027)) (R w) old
    (HighOutputFlagResearch.physical _ _ _ _ _ _ _ (tail_nd_pool w hn))

theorem zero_gatePhysical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ho : GatePhysical (literalKAdd w)) : GatePhysical (zeroKAdd w) := by
  have old := (congrArg GatePhysical (literal_split w)).mp ho
  exact splice_valid (fun i => PhysicalInstr (.gate i)) (P w)
    (oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796))
    (newLeafAt false (w 256) (w 1026) (w 1795) (w 257) (w 1027)) (R w) old
    (HighOutputTailStructuredResearch.physical false _ _ _ _ _ _
      (List.nodup_cons.mp (tail_nd_pool w hn)).2).2

/-- Contract validity also checks distinct CCX controls and both CZ correction branches.
This stronger leaf proof unfolds only the finite leaf, never the full adder. -/
private theorem zero_leaf_contract_valid (a b c A B z : Wire)
    (nd : [a,b,c,A,B,z].Nodup) : ∀i∈newLeafAt false a b c A B,instructionValid i := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [newLeafAt,eraseCarry,instructionValid,correctionValid,ne_comm]

private theorem flag_leaf_contract_valid (flag a b c A B z : Wire)
    (nd : [flag,a,b,c,A,B,z].Nodup) :
    ∀i∈HighOutputFlagResearch.newFlagAt flag a b c A B,instructionValid i := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [HighOutputFlagResearch.newFlagAt,newLeafAt,eraseCarry,instructionValid,correctionValid,ne_comm]

/-- Strong Contract validity is inherited only from an old strong-Contract premise. -/
theorem flag_contract_valid (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ho : ∀i∈literalKAdd w,instructionValid i) : ∀i∈flagKAdd w,instructionValid i := by
  have old := (congrArg (fun p : Program => ∀i∈p,instructionValid i) (literal_split w)).mp ho
  exact splice_valid instructionValid (P w)
    (oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796))
    (HighOutputFlagResearch.newFlagAt (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027)) (R w) old
    (flag_leaf_contract_valid _ _ _ _ _ _ _ (tail_nd_pool w hn))

theorem zero_contract_valid (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ho : ∀i∈literalKAdd w,instructionValid i) : ∀i∈zeroKAdd w,instructionValid i := by
  have old := (congrArg (fun p : Program => ∀i∈p,instructionValid i) (literal_split w)).mp ho
  exact splice_valid instructionValid (P w)
    (oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796))
    (newLeafAt false (w 256) (w 1026) (w 1795) (w 257) (w 1027)) (R w) old
    (zero_leaf_contract_valid _ _ _ _ _ _ (List.nodup_cons.mp (tail_nd_pool w hn)).2)

#check flag_support
#print axioms flag_support
#check zero_support
#print axioms zero_support
#check flag_gatePhysical
#print axioms flag_gatePhysical
#check zero_gatePhysical
#print axioms zero_gatePhysical
#check flag_contract_valid
#print axioms flag_contract_valid
#check zero_contract_valid
#print axioms zero_contract_valid
end ECDSAAdd.Entrant.KAddResourceBridgeResearch
