import ECDSAAdd.Submission.Entrant.AffineCarry4B
import ECDSAAdd.Submission.Entrant.AffineCarry3C
import ECDSAAdd.Submission.Entrant.KAddResourceBridgeDraft

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 400

namespace Verifier.Leaf4
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge RecordedQuantum
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

-- Keep support proof elaboration from eagerly expanding whole-program wire sets.
attribute [local irreducible] ECDSAAdd.wires

private theorem splice_valid4 (V : Instr → Prop) (p old new r : Program)
    (ho : ∀i∈p++old++r,V i) (hn : ∀i∈new,V i) : ∀i∈p++new++r,V i := by
  intro i hi
  simp only [List.mem_append] at hi ⊢
  rcases hi with (hp|hnw)|hr
  · exact ho i (by simp [hp])
  · exact hn i hnw
  · exact ho i (by simp [hr])

private theorem splice_support4 (p old new r : Program)
    (hleaf : wires new ⊆ wires old) : wires (p++new++r) ⊆ wires (p++old++r) := by
  simp only [wires_append]
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with (hp|hn)|hr
  · exact Or.inl (Or.inl hp)
  · exact Or.inl (Or.inr (hleaf hn))
  · exact Or.inr hr

theorem new4_support (a b c A B A' B' A'' B'' : Wire) :
    wires (newLeaf4At a b c A B A' B' A'' B'') = {a,b,c,A,B,A',B',A'',B''} := by
  ext q
  (simp [newLeaf4At,wires,Instr.wires,correctionWires]; tauto)

theorem leaf4_support (a b c A B A' B' A'' B'' z z' z'' : Wire) :
    wires (newLeaf4At a b c A B A' B' A'' B'')
      ⊆ wires (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') := by
  rw [new4_support, old4_unfold, wires_append, wires_append, wires_append,
      (Verifier.Leaf3.support3 A B z A' B' A'' B'' z' z'').1]
  intro q h
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [majority,eraseCarry,wires,Instr.wires,correctionWires]

theorem zero4_support (w : Nat → Wire) :
    wires (zero4KAdd w) ⊆ wires (literalKAdd w) := by
  have h := splice_support4 (P4 w)
    (oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027)
      (w 1794) (w 1795) (w 1796))
    (newLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027))
    (R4 w) (leaf4_support _ _ _ _ _ _ _ _ _ _ _ _)
  exact (congrArg (fun s : Finset Wire => wires (zero4KAdd w) ⊆ s)
    (congrArg ECDSAAdd.wires (literal_split4 w))).mpr h

theorem nd9 (w : Nat→Wire) (hinj : Function.Injective w) :
    [w 254,w 1024,w 1793,w 255,w 1025,w 256,w 1026,w 257,w 1027].Nodup :=
  List.Nodup.map hinj (by decide : [254,1024,1793,255,1025,256,1026,257,1027].Nodup)

private theorem leaf4_physical (a b c A B A' B' A'' B'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B''].Nodup) :
    GatePhysical (newLeaf4At a b c A B A' B' A'' B'') := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [newLeaf4At,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

private theorem leaf4_contract_valid (a b c A B A' B' A'' B'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B''].Nodup) :
    ∀i∈newLeaf4At a b c A B A' B' A'' B'',instructionValid i := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [newLeaf4At,instructionValid,correctionValid,ne_comm]

/-! ### Pool-Nodup variants, matching the ExitMerge call sites -/

theorem nd9_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) :
    [w 254,w 1024,w 1793,w 255,w 1025,w 256,w 1026,w 257,w 1027].Nodup := by
  have neq (i j : Nat) (hi : i<1798) (hj : j<1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

theorem tail4_nd_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) :
    [w 254,w 1024,w 1793,w 255,w 1025,w 256,w 1026,w 257,w 1027,
      w 1794,w 1795,w 1796].Nodup := by
  have neq (i j : Nat) (hi : i<1798) (hj : j<1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

theorem low_avoid4_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) :
    w i ∉ spinePorts (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797) := by
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

theorem P4_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) : w i∉wires (P4 w) := by
  intro h
  exact low_avoid4_pool w hn i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section R4PoolOpaque
theorem R4_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) : w i∉wires (R4 w) := by
  intro h
  have support := suffix_support (wireBlock w 0 254) (wireBlock w 770 254)
    (wireBlock w 1540 254) (w 1797)
  exact low_avoid4_pool w hn i hi (List.mem_toFinset.mp (support h))
end R4PoolOpaque

set_option maxHeartbeats 16000000 in
theorem exit4_run_eq_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool)
    (clean4 : s.basis (w 1794)=false) (clean5 : s.basis (w 1795)=false)
    (clean6 : s.basis (w 1796)=false)
    (topB   : (run (literalKAdd w) [] s).basis (w 1025)=false)
    (topB'  : (run (literalKAdd w) [] s).basis (w 1026)=false)
    (topB'' : (run (literalKAdd w) [] s).basis (w 1027)=false) :
    run (literalKAdd w) m s=run (zero4KAdd w) m s := by
  rw [literal_split4] at topB topB' topB''
  rw [literal_split4, zero4KAdd]
  exact whole_zero4 (P4 w) (R4 w) (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
    (w 257) (w 1027) (w 1794) (w 1795) (w 1796) (tail4_nd_pool w hn) s m clean4 clean5 clean6
    (P4_avoid_pool w hn 1794 (Or.inl rfl))
    (P4_avoid_pool w hn 1795 (Or.inr (Or.inl rfl)))
    (P4_avoid_pool w hn 1796 (Or.inr (Or.inr (Or.inl rfl))))
    (R4_avoid_pool w hn 1025 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (R4_avoid_pool w hn 1026 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (R4_avoid_pool w hn 1027 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    topB topB' topB''

theorem zero4_gatePhysical_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ho : GatePhysical (literalKAdd w)) : GatePhysical (zero4KAdd w) := by
  have old := (congrArg GatePhysical (literal_split4 w)).mp ho
  exact splice_valid4 (fun i => PhysicalInstr (.gate i)) (P4 w)
    (oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027)
      (w 1794) (w 1795) (w 1796))
    (newLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027))
    (R4 w) old (leaf4_physical _ _ _ _ _ _ _ _ _ (nd9_pool w hn))

theorem zero4_contract_valid_pool (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ho : ∀i∈literalKAdd w,instructionValid i) : ∀i∈zero4KAdd w,instructionValid i := by
  have old := (congrArg (fun p : Program => ∀i∈p,instructionValid i) (literal_split4 w)).mp ho
  exact splice_valid4 instructionValid (P4 w)
    (oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027)
      (w 1794) (w 1795) (w 1796))
    (newLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027))
    (R4 w) old (leaf4_contract_valid _ _ _ _ _ _ _ _ _ (nd9_pool w hn))

theorem leaf4_slots (a b c A B A' B' A'' B'' z z' z'' : Wire) :
    Challenge.gateSlots (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') = 38 ∧
    Challenge.gateSlots (newLeaf4At a b c A B A' B' A'' B'') = 17 := by
  refine ⟨?_, by rfl⟩
  rw [old4_unfold, Challenge.gateSlots_append, Challenge.gateSlots_append,
      Challenge.gateSlots_append,
      (Verifier.Leaf3.leaf3_slots A B z A' B' A'' B'' z' z'').1]
  rfl

theorem zero4_slots (w : Nat → Wire) :
    Challenge.gateSlots (zero4KAdd w) + 21 = Challenge.gateSlots (literalKAdd w) := by
  have hl := leaf4_slots (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
    (w 257) (w 1027) (w 1794) (w 1795) (w 1796)
  rw [literal_split4 w]
  simp only [zero4KAdd, Challenge.gateSlots_append, hl.1, hl.2]
  omega

#print axioms zero4_support
#print axioms exit4_run_eq_pool
#print axioms zero4_gatePhysical_pool
#print axioms zero4_contract_valid_pool
#print axioms zero4_slots
end Verifier.Leaf4
