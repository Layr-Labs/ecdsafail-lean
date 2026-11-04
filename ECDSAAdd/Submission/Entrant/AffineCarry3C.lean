import ECDSAAdd.Submission.Entrant.AffineCarry3B
import ECDSAAdd.Submission.Entrant.KAddResourceBridgeDraft

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 400

namespace Verifier.Leaf3
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge RecordedQuantum
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

-- Keep support proof elaboration from eagerly expanding whole-program wire sets.
attribute [local irreducible] ECDSAAdd.wires

/-- Unchanged prefix/suffix inherit pointwise properties. -/
private theorem splice_valid3 (V : Instr → Prop) (p old new r : Program)
    (ho : ∀i∈p++old++r,V i) (hn : ∀i∈new,V i) : ∀i∈p++new++r,V i := by
  intro i hi
  simp only [List.mem_append] at hi ⊢
  rcases hi with (hp|hnw)|hr
  · exact ho i (by simp [hp])
  · exact hn i hnw
  · exact ho i (by simp [hr])

private theorem splice_support3 (p old new r : Program)
    (hleaf : wires new ⊆ wires old) : wires (p++new++r) ⊆ wires (p++old++r) := by
  simp only [wires_append]
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with (hp|hn)|hr
  · exact Or.inl (Or.inl hp)
  · exact Or.inl (Or.inr (hleaf hn))
  · exact Or.inr hr

/-- Explicit wire sets, mirroring `HighOutputTailStructuredResearch.support`. -/
theorem support3 (a b c A B A' B' z z' : Wire) :
    wires (oldLeaf3At a b c A B A' B' z z') = {a,b,c,A,B,A',B',z,z'} ∧
    wires (newLeaf3At a b c A B A' B') = {a,b,c,A,B,A',B'} := by
  constructor
  · rw [old3_unfold]
    ext q
    (simp [oldLeafAt,majority,eraseCarry,wires,Instr.wires,correctionWires]; tauto)
  · ext q
    (simp [newLeaf3At,wires,Instr.wires,correctionWires]; tauto)

theorem leaf3_support (a b c A B A' B' z z' : Wire) :
    wires (newLeaf3At a b c A B A' B') ⊆ wires (oldLeaf3At a b c A B A' B' z z') := by
  rw [(support3 a b c A B A' B' z z').1, (support3 a b c A B A' B' z z').2]
  intro q h
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem zero3_support (w : Nat → Wire) :
    wires (zero3KAdd w) ⊆ wires (literalKAdd w) := by
  have h := splice_support3 (P3 w)
    (oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796))
    (newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)) (R3 w)
    (leaf3_support _ _ _ _ _ _ _ _ _)
  exact (congrArg (fun s : Finset Wire => wires (zero3KAdd w) ⊆ s)
    (congrArg ECDSAAdd.wires (literal_split3 w))).mpr h


theorem nd7 (w : Nat→Wire) (hinj : Function.Injective w) :
    [w 255,w 1025,w 1794,w 256,w 1026,w 257,w 1027].Nodup :=
  List.Nodup.map hinj (by decide : [255,1025,1794,256,1026,257,1027].Nodup)

private theorem leaf3_physical (a b c A B A' B' : Wire)
    (nd : [a,b,c,A,B,A',B'].Nodup) : GatePhysical (newLeaf3At a b c A B A' B') := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [newLeaf3At,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

private theorem leaf3_contract_valid (a b c A B A' B' : Wire)
    (nd : [a,b,c,A,B,A',B'].Nodup) : ∀i∈newLeaf3At a b c A B A' B',instructionValid i := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [newLeaf3At,instructionValid,correctionValid,ne_comm]

theorem zero3_gatePhysical (w : Nat → Wire) (hinj : Function.Injective w)
    (ho : GatePhysical (literalKAdd w)) : GatePhysical (zero3KAdd w) := by
  have old := (congrArg GatePhysical (literal_split3 w)).mp ho
  exact splice_valid3 (fun i => PhysicalInstr (.gate i)) (P3 w)
    (oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796))
    (newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)) (R3 w) old
    (leaf3_physical _ _ _ _ _ _ _ (nd7 w hinj))

theorem zero3_contract_valid (w : Nat → Wire) (hinj : Function.Injective w)
    (ho : ∀i∈literalKAdd w,instructionValid i) : ∀i∈zero3KAdd w,instructionValid i := by
  have old := (congrArg (fun p : Program => ∀i∈p,instructionValid i) (literal_split3 w)).mp ho
  exact splice_valid3 instructionValid (P3 w)
    (oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796))
    (newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)) (R3 w) old
    (leaf3_contract_valid _ _ _ _ _ _ _ (nd7 w hinj))

#print axioms zero3_gatePhysical
#print axioms zero3_contract_valid


/-! ### Pool-Nodup variants, matching the ExitMerge call sites -/

theorem nd7_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) :
    [w 255,w 1025,w 1794,w 256,w 1026,w 257,w 1027].Nodup := by
  have neq (i j : Nat) (hi : i<1798) (hj : j<1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

theorem tail3_nd_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) :
    [w 255,w 1025,w 1794,w 256,w 1026,w 257,w 1027,w 1795,w 1796].Nodup := by
  have neq (i j : Nat) (hi : i<1798) (hj : j<1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

theorem low_avoid3_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) :
    w i ∉ spinePorts (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255) (w 1797) := by
  have ir : i<1798 := by omega
  intro h
  simp only [spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e := skywalkPool_index_inj w hn i 1797 ir (by decide) h
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have e := skywalkPool_index_inj w hn i j ir (by omega) hji.symm
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have e := skywalkPool_index_inj w hn i j ir (by omega) hji.symm
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have e := skywalkPool_index_inj w hn i j ir (by omega) hji.symm
    omega

theorem P3_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) : w i∉wires (P3 w) := by
  intro h
  exact low_avoid3_pool w hn i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section R3PoolOpaque
theorem R3_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) : w i∉wires (R3 w) := by
  intro h
  have support := suffix_support (wireBlock w 0 255) (wireBlock w 770 255)
    (wireBlock w 1540 255) (w 1797)
  exact low_avoid3_pool w hn i hi (List.mem_toFinset.mp (support h))
end R3PoolOpaque


set_option maxHeartbeats 16000000 in
theorem exit3_run_eq_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (clean5 : s.basis (w 1795)=false) (clean6 : s.basis (w 1796)=false)
    (topB  : (run (literalKAdd w) [] s).basis (w 1026)=false)
    (topB' : (run (literalKAdd w) [] s).basis (w 1027)=false) :
    run (literalKAdd w) m s=run (zero3KAdd w) m s := by
  rw [literal_split3] at topB topB'
  rw [literal_split3, zero3KAdd]
  exact whole_zero3 (P3 w) (R3 w) (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
    (w 1795) (w 1796) (tail3_nd_pool w hn) s m clean5 clean6
    (P3_avoid_pool w hn 1795 (Or.inl rfl)) (P3_avoid_pool w hn 1796 (Or.inr (Or.inl rfl)))
    (R3_avoid_pool w hn 1026 (Or.inr (Or.inr (Or.inl rfl))))
    (R3_avoid_pool w hn 1027 (Or.inr (Or.inr (Or.inr rfl)))) topB topB'

theorem zero3_gatePhysical_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ho : GatePhysical (literalKAdd w)) : GatePhysical (zero3KAdd w) := by
  have old := (congrArg GatePhysical (literal_split3 w)).mp ho
  exact splice_valid3 (fun i => PhysicalInstr (.gate i)) (P3 w)
    (oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796))
    (newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)) (R3 w) old
    (leaf3_physical _ _ _ _ _ _ _ (nd7_pool w hn))

theorem zero3_contract_valid_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ho : ∀i∈literalKAdd w,instructionValid i) : ∀i∈zero3KAdd w,instructionValid i := by
  have old := (congrArg (fun p : Program => ∀i∈p,instructionValid i) (literal_split3 w)).mp ho
  exact splice_valid3 instructionValid (P3 w)
    (oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796))
    (newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)) (R3 w) old
    (leaf3_contract_valid _ _ _ _ _ _ _ (nd7_pool w hn))

#print axioms exit3_run_eq_pool
#print axioms zero3_gatePhysical_pool
#print axioms zero3_contract_valid_pool

#print axioms nd7_pool
#print axioms P3_avoid_pool
#print axioms R3_avoid_pool


theorem leaf3_slots (a b c A B A' B' z z' : Wire) :
    Challenge.gateSlots (oldLeaf3At a b c A B A' B' z z') = 26 ∧
    Challenge.gateSlots (newLeaf3At a b c A B A' B') = 12 := by
  constructor <;> rfl

#print axioms leaf3_slots


theorem zero3_slots (w : Nat → Wire) :
    Challenge.gateSlots (zero3KAdd w) + 14 = Challenge.gateSlots (literalKAdd w) := by
  have hl := leaf3_slots (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796)
  rw [literal_split3 w]
  simp only [zero3KAdd, Challenge.gateSlots_append, hl.1, hl.2]
  omega

#print axioms zero3_slots

#print axioms zero3_support
end Verifier.Leaf3
