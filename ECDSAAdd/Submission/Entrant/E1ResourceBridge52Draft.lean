import ECDSAAdd.Submission.Entrant.E1WholeKAdd52Draft

/-! SOURCE-ONLY resource transport for the actual four-bit tail52 splice.
This file has not been compiled or replayed. It leaves every imported ancestor
unchanged and keeps the254-bit prefix/suffix opaque. The three descending
measurements are retained. No qubit-retirement or whole-candidate claim. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1ResourceBridge52Research
open Arithmetic RecordedQuantum Challenge
open KAddCallerBridgeResearch AffineCarryTail52Research
open E1CarrySplice52Research E1WholeKAdd52Research

attribute [local irreducible] ECDSAAdd.wires

/-- Only the finite old four-bit tail is unfolded. Its12 ports all remain live. -/
theorem old_tail_support52 (p : Ports) :
    wires (oldTail p)=(wireList p).toFinset := by
  ext q
  simp [oldTail,oldPrefix,commonSuffix,majority,eraseCarry,wireList,
    wires,Instr.wires,correctionWires,or_assoc,or_left_comm,or_comm]

/-- The forward tail adds only the actual parity flag; all three carry
measurement targets still occur in commonSuffix. No alias premise is needed. -/
theorem forward_tail_support52 (p : Ports) (flag : Wire) :
    wires (forwardTail p flag)=(wireList p).toFinset ∪ {flag} := by
  ext q
  simp [forwardTail,forwardPrefix,clone255,clone256,commonSuffix,
    majority,eraseCarry,wireList,wires,Instr.wires,correctionWires,
    or_assoc,or_left_comm,or_comm]

theorem exit_tail_support52 (p : Ports) :
    wires (exitTail p)=(wireList p).toFinset := by
  ext q
  simp [exitTail,exitPrefix,commonSuffix,eraseCarry,wireList,
    wires,Instr.wires,correctionWires,or_assoc,or_left_comm,or_comm]

private theorem splice_support52 (pre old new post : Program) (extra : Finset Wire)
    (localSupport : wires new ⊆ wires old ∪ extra) :
    wires (pre++new++post) ⊆ wires (pre++old++post) ∪ extra := by
  simp only [wires_append]
  intro q h
  rcases Finset.mem_union.mp h with hLeft | hPost
  · rcases Finset.mem_union.mp hLeft with hPre | hNew
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hPre))
    · rcases Finset.mem_union.mp (localSupport hNew) with hOld | hExtra
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _ hOld))
      · exact Finset.mem_union_right _ hExtra
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hPost)

/-- Whole-program support needs no pool injectivity or arithmetic promise. -/
theorem flag_support52 (w : Nat → Wire) :
    wires (flagKAdd52 w) ⊆ wires (literalKAdd w) ∪ {w 1028} := by
  have localSupport : wires (forwardTail (actualPorts w) (w 1028)) ⊆
      wires (oldTail (actualPorts w)) ∪ {w 1028} := by
    rw [forward_tail_support52,old_tail_support52]
  have h := splice_support52 (lowPrefix52 w) (oldTail (actualPorts w))
    (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w) {w 1028} localSupport
  exact (congrArg (fun s : Finset Wire => wires (flagKAdd52 w) ⊆ s ∪ {w 1028})
    (congrArg ECDSAAdd.wires (literal_split_four52 w))).mpr h

theorem zero_support52 (w : Nat → Wire) :
    wires (zeroKAdd52 w) ⊆ wires (literalKAdd w) := by
  have localSupport : wires (exitTail (actualPorts w)) ⊆
      wires (oldTail (actualPorts w)) ∪ (∅ : Finset Wire) := by
    rw [exit_tail_support52,old_tail_support52,Finset.union_empty]
  have h := splice_support52 (lowPrefix52 w) (oldTail (actualPorts w))
    (exitTail (actualPorts w)) (lowSuffix52 w) ∅ localSupport
  have hs : wires (zeroKAdd52 w) ⊆
      wires (lowPrefix52 w++oldTail (actualPorts w)++lowSuffix52 w) := by
    simpa only [Finset.union_empty] using h
  exact (congrArg (fun s : Finset Wire => wires (zeroKAdd52 w) ⊆ s)
    (congrArg ECDSAAdd.wires (literal_split_four52 w))).mpr hs

/-- Strong Contract validity checks distinct CCX controls and each CZ in
both correction branches. Only the finite12-port old tail is unfolded. -/
theorem old_tail_contract_valid52 (p : Ports) (nd : (wireList p).Nodup) :
    ∀ i ∈ oldTail p, instructionValid i := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  simp_all [oldTail,oldPrefix,commonSuffix,majority,eraseCarry,
    instructionValid,correctionValid,ne_comm]

/-- The only extra finite distinctness requirement is flag versus the12
actual ports. No global injectivity of the placement is assumed. -/
theorem forward_tail_contract_valid52 (p : Ports) (flag : Wire)
    (nd : (flag::wireList p).Nodup) :
    ∀ i ∈ forwardTail p flag, instructionValid i := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  simp_all [forwardTail,forwardPrefix,clone255,clone256,commonSuffix,
    majority,eraseCarry,instructionValid,correctionValid,ne_comm]

theorem exit_tail_contract_valid52 (p : Ports) (nd : (wireList p).Nodup) :
    ∀ i ∈ exitTail p, instructionValid i := by
  simp only [wireList,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  simp_all [exitTail,exitPrefix,commonSuffix,eraseCarry,
    instructionValid,correctionValid,ne_comm]

/-- Strong-to-weak is valid. The opposite implication is deliberately absent:
GatePhysical admits measurements without checking their CZ correction lists. -/
private theorem instruction_physical52 (i : Instr) (h : instructionValid i) :
    PhysicalInstr (.gate i) := by
  cases i <;> simp_all [instructionValid,PhysicalInstr,ProperGate]

private theorem program_physical52 (p : Program)
    (h : ∀ i ∈ p, instructionValid i) : GatePhysical p := by
  intro i hi
  exact instruction_physical52 i (h i hi)

theorem old_tail_gatePhysical52 (p : Ports) (nd : (wireList p).Nodup) :
    GatePhysical (oldTail p) :=
  program_physical52 _ (old_tail_contract_valid52 p nd)

theorem forward_tail_gatePhysical52 (p : Ports) (flag : Wire)
    (nd : (flag::wireList p).Nodup) : GatePhysical (forwardTail p flag) :=
  program_physical52 _ (forward_tail_contract_valid52 p flag nd)

theorem exit_tail_gatePhysical52 (p : Ports) (nd : (wireList p).Nodup) :
    GatePhysical (exitTail p) :=
  program_physical52 _ (exit_tail_contract_valid52 p nd)

/-- Pointwise transport extracts unchanged prefix/suffix obligations from
exactly the old property V. It never unfolds either254-bit list. -/
private theorem splice_valid52 (V : Instr → Prop) (pre old new post : Program)
    (oldValid : ∀ i ∈ pre++old++post, V i)
    (newValid : ∀ i ∈ new, V i) : ∀ i ∈ pre++new++post, V i := by
  intro i hi
  rcases List.mem_append.mp hi with hLeft | hPost
  · rcases List.mem_append.mp hLeft with hPre | hNew
    · exact oldValid i (List.mem_append_left post (List.mem_append_left old hPre))
    · exact newValid i hNew
  · exact oldValid i (List.mem_append_right (pre++old) hPost)

/-- The whole weak property is inherited only as a weak property. -/
theorem flag_gatePhysical52 (w : Nat → Wire)
    (nd : ((w 1028)::wireList (actualPorts w)).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (flagKAdd52 w) := by
  have old := (congrArg GatePhysical (literal_split_four52 w)).mp oldPhysical
  exact splice_valid52 (fun i => PhysicalInstr (.gate i)) (lowPrefix52 w)
    (oldTail (actualPorts w)) (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w)
    old (forward_tail_gatePhysical52 (actualPorts w) (w 1028) nd)

theorem zero_gatePhysical52 (w : Nat → Wire)
    (nd : (wireList (actualPorts w)).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (zeroKAdd52 w) := by
  have old := (congrArg GatePhysical (literal_split_four52 w)).mp oldPhysical
  exact splice_valid52 (fun i => PhysicalInstr (.gate i)) (lowPrefix52 w)
    (oldTail (actualPorts w)) (exitTail (actualPorts w)) (lowSuffix52 w)
    old (exit_tail_gatePhysical52 (actualPorts w) nd)

/-- Strong whole-program validity requires an OLD STRONG premise. The weak
GatePhysical premise from the preceding theorems cannot replace this premise. -/
theorem flag_contract_valid52 (w : Nat → Wire)
    (nd : ((w 1028)::wireList (actualPorts w)).Nodup)
    (oldValid : ∀ i ∈ literalKAdd w, instructionValid i) :
    ∀ i ∈ flagKAdd52 w, instructionValid i := by
  have old := (congrArg (fun p : Program => ∀ i ∈ p, instructionValid i)
    (literal_split_four52 w)).mp oldValid
  exact splice_valid52 instructionValid (lowPrefix52 w) (oldTail (actualPorts w))
    (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w) old
    (forward_tail_contract_valid52 (actualPorts w) (w 1028) nd)

theorem zero_contract_valid52 (w : Nat → Wire)
    (nd : (wireList (actualPorts w)).Nodup)
    (oldValid : ∀ i ∈ literalKAdd w, instructionValid i) :
    ∀ i ∈ zeroKAdd52 w, instructionValid i := by
  have old := (congrArg (fun p : Program => ∀ i ∈ p, instructionValid i)
    (literal_split_four52 w)).mp oldValid
  exact splice_valid52 instructionValid (lowPrefix52 w) (oldTail (actualPorts w))
    (exitTail (actualPorts w)) (lowSuffix52 w) old
    (exit_tail_contract_valid52 (actualPorts w) nd)

/-- Pool-level convenience uses bounded index injectivity only at these13
indices; it is independent of the private whole-adder nodup helper. -/
theorem actual_flag_ports_nodup52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    ((w 1028)::wireList (actualPorts w)).Nodup := by
  have neq (i j : Nat) (hi : i < 1798) (hj : j < 1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [wireList,actualPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

theorem actual_ports_nodup52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    (wireList (actualPorts w)).Nodup :=
  (List.nodup_cons.mp (actual_flag_ports_nodup52 w hn)).2

theorem flag_gatePhysical_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (flagKAdd52 w) :=
  flag_gatePhysical52 w (actual_flag_ports_nodup52 w hn) oldPhysical

theorem zero_gatePhysical_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldPhysical : GatePhysical (literalKAdd w)) : GatePhysical (zeroKAdd52 w) :=
  zero_gatePhysical52 w (actual_ports_nodup52 w hn) oldPhysical

theorem flag_contract_valid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldValid : ∀ i ∈ literalKAdd w, instructionValid i) :
    ∀ i ∈ flagKAdd52 w, instructionValid i :=
  flag_contract_valid52 w (actual_flag_ports_nodup52 w hn) oldValid

theorem zero_contract_valid_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (oldValid : ∀ i ∈ literalKAdd w, instructionValid i) :
    ∀ i ∈ zeroKAdd52 w, instructionValid i :=
  zero_contract_valid52 w (actual_ports_nodup52 w hn) oldValid

#print axioms flag_support52
#print axioms zero_support52
#print axioms forward_tail_contract_valid52
#print axioms exit_tail_contract_valid52
#print axioms flag_gatePhysical52
#print axioms zero_gatePhysical52
#print axioms flag_contract_valid52
#print axioms zero_contract_valid52
end ECDSAAdd.Entrant.E1ResourceBridge52Research
