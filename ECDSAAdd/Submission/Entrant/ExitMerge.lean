import ECDSAAdd.Submission.Entrant.TerminalGraph
import ECDSAAdd.Arithmetic.PoolLayout
import ECDSAAdd.Arithmetic.SkywalkPool
import ECDSAAdd.Arithmetic.NativeFirstDirectProgram
import Mathlib.Tactic
import ECDSAAdd.Arithmetic.DisjointPrograms
import ECDSAAdd.Submission.Entrant.Prelude
import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
import ECDSAAdd.Arithmetic.NativeFirstDirectValues
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ComparePhysical
import ECDSAAdd.Arithmetic.MaskedConstant
import ECDSAAdd.Arithmetic.MappedSources
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.Rotate
import ECDSAAdd.Arithmetic.Reduction
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
import ECDSAAdd.Arithmetic.KnownOutputAdder
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Baselines.SlotAlgebra
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Baselines.SlotNativeFirst


-- Consolidated source module: KAddCallerStructureDraft
section

/-! Private structural decomposition/support/cost module. No real MF caller premise is discharged. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.KAddCallerBridgeResearch
open Arithmetic RecordedQuantum Challenge HighOutputTailStructuredResearch AdderSpineBridgeResearch

-- Keep support/cost proof elaboration from eagerly expanding whole program wire sets.
attribute [local irreducible] ECDSAAdd.wires

/-- This is literally both E1Merge.kAddM and E1Reflected.kAddM. -/
def literalKAdd (w : Nat→Wire) : Program :=
  mappedAdd (mappedRead (wireBlock w 0 258) false) (wireBlock w 770 258)
    (wireBlock w 1540 257) (w 1797)

def P (w : Nat→Wire) : Program :=
  adderPrefix (wireBlock w 0 256) (wireBlock w 770 256) (wireBlock w 1540 256) (w 1797)

def R (w : Nat→Wire) : Program :=
  adderSuffix (wireBlock w 0 256) (wireBlock w 770 256) (wireBlock w 1540 256) (w 1797)

def lowPorts (w : Nat→Wire) : List Wire :=
  spinePorts (wireBlock w 0 256) (wireBlock w 770 256) (wireBlock w 1540 256) (w 1797)

def flagKAdd (w : Nat→Wire) : Program :=
  P w++HighOutputFlagResearch.newFlagAt (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027)++R w

def zeroKAdd (w : Nat→Wire) : Program :=
  P w++newLeafAt false (w 256) (w 1026) (w 1795) (w 257) (w 1027)++R w

private theorem lastCarry_cat (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs ++ ys) cin = lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => exact ih x

/-- Split the final carry by one list append instead of reducing 256 entries. -/
theorem literal_split (w : Nat→Wire) :
    literalKAdd w=P w++oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)++R w := by
  have hx : wireBlock w 0 258=wireBlock w 0 256++[w 256,w 257] := by
    rw [←wireBlock_append w 0 256 2]
    rfl
  have hy : wireBlock w 770 258=wireBlock w 770 256++[w 1026,w 1027] := by
    rw [←wireBlock_append w 770 256 2]
    rfl
  have hc : wireBlock w 1540 257=wireBlock w 1540 256++[w 1796] := by
    rw [←wireBlock_append w 1540 256 1]
    rfl
  have lastBlock : wireBlock w 1540 256 = wireBlock w 1540 255 ++ [w 1795] := by
    rw [←wireBlock_append w 1540 255 1]
    rfl
  have last : lastCarry (wireBlock w 1540 256) (w 1797)=w 1795 := by
    rw [lastBlock,lastCarry_cat]
    rfl
  rw [literalKAdd,read_add,hx,hy,hc]
  simpa only [P,R,last] using add_split
    (wireBlock w 0 256) (wireBlock w 770 256) (wireBlock w 1540 256)
    (w 1797) (w 256) (w 257) (w 1026) (w 1027) (w 1796)
    (by simp [wireBlock_length]) (by simp [wireBlock_length])

theorem low_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉lowPorts w := by
  intro h
  simp only [lowPorts,spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e:=hinj h
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji
    subst j
    simp only [List.mem_range'_1] at hj
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji
    subst j
    simp only [List.mem_range'_1] at hj
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji
    subst j
    simp only [List.mem_range'_1] at hj
    omega

theorem P_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉wires (P w) := by
  intro h
  exact low_avoid w hinj i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section RSupportWireOpaque

theorem R_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉wires (R w) := by
  intro h
  have support := suffix_support (wireBlock w 0 256) (wireBlock w 770 256)
    (wireBlock w 1540 256) (w 1797)
  exact low_avoid w hinj i hi (List.mem_toFinset.mp (support h))
end RSupportWireOpaque

theorem tail_nd (w : Nat→Wire) (hinj : Function.Injective w) :
    [w 1028,w 256,w 1026,w 1795,w 257,w 1027,w 1796].Nodup := by
  exact List.Nodup.map hinj (by decide : [1028,256,1026,1795,257,1027,1796].Nodup)

/-- A post-word value/division fact gives its actual high physical bit.
The original MF supplies postWord, not an unrelated abstract integer bound. -/
theorem top_from_div (w : Nat→Wire) (s : BasisState) (W : Nat) (flag : Bool)
    (postWord : regValue (wireBlock w 770 258) s=W) (hdiv : W/2^257=flag.toNat) :
    s (w 1027)=flag := by
  have h:=regValue_bit (wireBlock w 770 258) 257 0 s (by simp [wireBlock_length])
  have port : (wireBlock w 770 258).getD 257 0=w 1027 := by rfl
  rw [port,postWord,hdiv] at h
  cases hs : s (w 1027) <;> cases flag <;> simp [hs] at h ⊢

theorem flag_counts (w : Nat→Wire) :
    toffoliCount (literalKAdd w)=toffoliCount (flagKAdd w)+1 ∧
    measurementCount (literalKAdd w)=measurementCount (flagKAdd w) ∧
    gateSlots (literalKAdd w)=gateSlots (flagKAdd w)+5 := by
  have o:=HighOutputTailStructuredResearch.counts false (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
  have n:=HighOutputFlagResearch.counts (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027)
  have os:=HighOutputTailStructuredResearch.slots false (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
  simp only [literal_split,flagKAdd,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem zero_counts (w : Nat→Wire) :
    toffoliCount (literalKAdd w)=toffoliCount (zeroKAdd w)+1 ∧
    measurementCount (literalKAdd w)=measurementCount (zeroKAdd w) ∧
    gateSlots (literalKAdd w)=gateSlots (zeroKAdd w)+7 := by
  have o:=HighOutputTailStructuredResearch.counts false (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
  have os:=HighOutputTailStructuredResearch.slots false (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
  change gateSlots (oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)) = 14 ∧
    gateSlots (newLeafAt false (w 256) (w 1026) (w 1795) (w 257) (w 1027)) = 7 at os
  simp only [literal_split,zeroKAdd,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem flag_retired (w : Nat→Wire) (hinj : Function.Injective w) : w 1796∉wires (flagKAdd w) := by
  have hp:=P_avoid w hinj 1796 (Or.inl rfl)
  have hr:=R_avoid w hinj 1796 (Or.inl rfl)
  have hl:=HighOutputFlagResearch.retired _ _ _ _ _ _ _ (tail_nd w hinj)
  simp only [flagKAdd,wires_append,Finset.mem_union]
  intro h
  rcases h with hLeft | hR
  · rcases hLeft with hP | hLeaf
    · exact hp hP
    · exact hl hLeaf
  · exact hr hR

theorem zero_retired (w : Nat→Wire) (hinj : Function.Injective w) : w 1796∉wires (zeroKAdd w) := by
  have hp:=P_avoid w hinj 1796 (Or.inl rfl)
  have hr:=R_avoid w hinj 1796 (Or.inl rfl)
  have hl:=HighOutputTailStructuredResearch.retired false _ _ _ _ _ _ (List.nodup_cons.mp (tail_nd w hinj)).2
  simp only [zeroKAdd,wires_append,Finset.mem_union]
  intro h
  rcases h with hLeft | hR
  · rcases hLeft with hP | hLeaf
    · exact hp hP
    · exact hl hLeaf
  · exact hr hR


/-- Bounded alternative rooted in the actual real-caller pool Nodup premise.
The old globally injective research theorem above is retained unchanged. -/
theorem low_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉lowPorts w := by
  have ir : i<1798 := by omega
  intro h
  simp only [lowPorts,spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e := skywalkPool_index_inj w hn i 1797 ir (by decide) h
    omega
  all_goals
    obtain ⟨j,hj,hji⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have jr : j<1798 := by omega
    have e := skywalkPool_index_inj w hn j i jr ir hji
    omega

theorem P_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉wires (P w) := by
  intro h
  exact low_avoid_pool w hn i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section RPoolSupportWireOpaque

theorem R_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉wires (R w) := by
  intro h
  have support := suffix_support (wireBlock w 0 256) (wireBlock w 770 256)
    (wireBlock w 1540 256) (w 1797)
  exact low_avoid_pool w hn i hi (List.mem_toFinset.mp (support h))
end RPoolSupportWireOpaque

theorem tail_nd_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) :
    [w 1028,w 256,w 1026,w 1795,w 257,w 1027,w 1796].Nodup := by
  have neq (i j : Nat) (hi : i<1798) (hj : j<1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

end ECDSAAdd.Entrant.KAddCallerBridgeResearch
end


-- Consolidated source module: E1CallerValueFactsDraft
section

/-! Source-only numerical caller facts. These do not assert the MF-to-tail
prefix bridge, any program equivalence, or a full candidate certificate. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.E1CallerValueFactsResearch
open Arithmetic NativeFirstDirect

def Kword (D : Nat) (par : Bool) : Nat := (D/2+kConstant false par)%2^258

/-- Both forward selected callers have this identical numerical K output.
The parity premise excludes D=p-1 in the true branch, where a naive bound
without the actual caller condition would wrap exactly to zero. -/
theorem Kword_high_div (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) :
    Kword D par<2^258 ∧ (Kword D par)/2^257=par.toNat ∧
      (par=true → (Kword D par)/2^256=3) := by
  cases par <;> norm_num [Kword,kConstant,ECDSAAdd.p] at * <;> omega

/-- The exit's literal mapped-adder output is Y/2, not an unbounded MF word. -/
theorem exit_half_bound (Y : Nat) (hY : Y<ECDSAAdd.p) : Y/2<2^255 := by
  norm_num [ECDSAAdd.p] at hY ⊢
  omega

/-- Three final zero output bits justify the optional affine-carry extension.
A whole-adder prefix/cleanup proof is still required to use these facts. -/
theorem exit_top3 (Y : Nat) (hY : Y<ECDSAAdd.p) :
    (Y/2).testBit 255=false ∧ (Y/2).testBit 256=false ∧ (Y/2).testBit 257=false := by
  have h := exit_half_bound Y hY
  refine ⟨Nat.testBit_eq_false_of_lt h,?_,?_⟩
  · apply Nat.testBit_eq_false_of_lt
    norm_num at h ⊢
    omega
  · apply Nat.testBit_eq_false_of_lt
    norm_num at h ⊢
    omega

end ECDSAAdd.Entrant.E1CallerValueFactsResearch
end


-- Consolidated source module: KAddCallerBridgeDraft
section

/-! Private whole-adder substitutions. The actual real-MF postWord premise
remains explicit; no three-call program gain or full candidate is established. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.KAddCallerBridgeResearch
open Arithmetic RecordedQuantum Challenge HighOutputTailStructuredResearch AdderSpineBridgeResearch

/-- The two forward s6 callers instantiate D=dx, par=dx%2, and the existing
MF output Kword. Their loadK/tk derivations remain the original verified ones. -/
theorem forward_run_eq (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean : s.basis (w 1796)=false) (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) (flagIn : s.basis (w 1028)=par)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=
      E1CallerValueFactsResearch.Kword D par) :
    run (literalKAdd w) m s=run (flagKAdd w) m s := by
  have facts:=E1CallerValueFactsResearch.Kword_high_div D hD par hp
  have top:=top_from_div w (run (literalKAdd w) [] s).basis _ par postWord facts.2.1
  rw [literal_split] at top ⊢
  unfold flagKAdd
  apply whole_flag (P w) (R w) (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
    (tail_nd w hinj) s m clean (P_avoid w hinj 1796 (Or.inl rfl))
    (P_avoid w hinj 1028 (Or.inr (Or.inl rfl))) (R_avoid w hinj 1027 (Or.inr (Or.inr rfl)))
  exact top.trans flagIn.symm

/-- Exit s12 supplies the actual canonical Y/2 MF result, including G=false. -/
theorem exit_run_eq (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean : s.basis (w 1796)=false) (Y : Nat) (hY : Y<ECDSAAdd.p)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Y/2) :
    run (literalKAdd w) m s=run (zeroKAdd w) m s := by
  have hlt : Y/2<2^257 := lt_trans (E1CallerValueFactsResearch.exit_half_bound Y hY)
    (pow_lt_pow_right₀ (a := (2 : Nat)) (m := 255) (n := 257) (by decide) (by decide))
  have hdiv : (Y/2)/2^257=Bool.toNat false := Nat.div_eq_of_lt hlt
  have top:=top_from_div w (run (literalKAdd w) [] s).basis _ false postWord hdiv
  rw [literal_split] at top ⊢
  unfold zeroKAdd
  exact whole_zero (P w) (R w) (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
    (List.nodup_cons.mp (tail_nd w hinj)).2 s m clean
    (P_avoid w hinj 1796 (Or.inl rfl)) (R_avoid w hinj 1027 (Or.inr (Or.inr rfl))) top


/-- Pool-Nodup variant; the real MF postWord premise is still not discharged. -/
theorem forward_run_eq_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (clean : s.basis (w 1796)=false) (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) (flagIn : s.basis (w 1028)=par)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=
      E1CallerValueFactsResearch.Kword D par) :
    run (literalKAdd w) m s=run (flagKAdd w) m s := by
  have facts:=E1CallerValueFactsResearch.Kword_high_div D hD par hp
  have top:=top_from_div w (run (literalKAdd w) [] s).basis _ par postWord facts.2.1
  rw [literal_split] at top ⊢
  unfold flagKAdd
  apply whole_flag (P w) (R w) (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
    (tail_nd_pool w hn) s m clean (P_avoid_pool w hn 1796 (Or.inl rfl))
    (P_avoid_pool w hn 1028 (Or.inr (Or.inl rfl))) (R_avoid_pool w hn 1027 (Or.inr (Or.inr rfl)))
  exact top.trans flagIn.symm

/-- Pool-Nodup variant; the real MF postWord premise is still not discharged. -/
theorem exit_run_eq_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (clean : s.basis (w 1796)=false) (Y : Nat) (hY : Y<ECDSAAdd.p)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Y/2) :
    run (literalKAdd w) m s=run (zeroKAdd w) m s := by
  have hlt : Y/2<2^257 := lt_trans (E1CallerValueFactsResearch.exit_half_bound Y hY)
    (pow_lt_pow_right₀ (a := (2 : Nat)) (m := 255) (n := 257) (by decide) (by decide))
  have hdiv : (Y/2)/2^257=Bool.toNat false := Nat.div_eq_of_lt hlt
  have top:=top_from_div w (run (literalKAdd w) [] s).basis _ false postWord hdiv
  rw [literal_split] at top ⊢
  unfold zeroKAdd
  exact whole_zero (P w) (R w) (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
    (List.nodup_cons.mp (tail_nd_pool w hn)).2 s m clean
    (P_avoid_pool w hn 1796 (Or.inl rfl)) (R_avoid_pool w hn 1027 (Or.inr (Or.inr rfl))) top

end ECDSAAdd.Entrant.KAddCallerBridgeResearch
end


-- Consolidated source module: KAddResourceBridgeDraft
section

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
end


-- Consolidated source module: AffineCarry3A
section

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 400

namespace Verifier.Leaf3
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge

/-- The three-bit terminal suffix: two retired clean carries `z`, `z'`. -/
def oldLeaf3At (a b c A B A' B' z z' : Wire) : Program :=
  addInPlace [a,A,A'] [b,B,B'] [z,z'] c

/-- Mirror of the two-bit leaf, for the nesting check. -/
def oldLeafAt (a b c A B z : Wire) : Program :=
  majority a b c z ++ [.CX A B,.CX z B] ++ eraseCarry a b c z ++ [.CX a b,.CX c b]

/-- Zero-Toffoli replacement. Order is load-bearing: B' is measured while B is live. -/
def newLeaf3At (a b c A B A' B' : Wire) : Program :=
  [.measureX B' [] [.Z A, .Z B, .Z A', .CZ A B],
   .measureX B  [] [.Z A, .CZ a b, .CZ a c, .CZ b c],
   .CX a b, .CX c b]

/-- Output bits 256 and 257 of the sum are zero. Bit 255 is not needed. -/
def Ready3 (a b c A B A' B' : Wire) (s : BasisState) : Prop :=
  ((s A ^^ s B) ^^ carryBit (s a) (s b) (s c)) = false ∧
  ((s A' ^^ s B') ^^
     carryBit (s A) (s B) (carryBit (s a) (s b) (s c))) = false

-- structural checks
theorem old3_unfold (a b c A B A' B' z z' : Wire) :
    oldLeaf3At a b c A B A' B' z z'
      = majority a b c z ++ oldLeafAt A B z A' B' z'
        ++ eraseCarry a b c z ++ [.CX a b,.CX c b] := by rfl

theorem old3_counts (a b c A B A' B' z z' : Wire) :
    toffoliCount (oldLeaf3At a b c A B A' B' z z') = 2 ∧
    measurementCount (oldLeaf3At a b c A B A' B' z z') = 2 := by
  exact ⟨rfl, rfl⟩

theorem new3_counts (a b c A B A' B' : Wire) :
    toffoliCount (newLeaf3At a b c A B A' B') = 0 ∧
    measurementCount (newLeaf3At a b c A B A' B') = 2 := by
  exact ⟨rfl, rfl⟩


/-- Common final state: `b` holds the low sum, both high outputs are zeroed,
phase is untouched. -/
private def post3 (a b c B B' : Wire) (s : State) : State :=
  ⟨s.phase,
   writeBit (writeBit (writeBit s.basis B' false) B false) b
     (sumBit (s.basis a) (s.basis b) (s.basis c))⟩

/-- Boolean value a correction list contributes to the phase. -/
def cval : List Correction → BasisState → Bool
  | [], _ => false
  | .Z t :: cs, f => f t ^^ cval cs f
  | .CZ x y :: cs, f => (f x && f y) ^^ cval cs f

private theorem correct_eq (cs : List Correction) (s : State) :
    correct cs s = ⟨s.phase ^^ cval cs s.basis, s.basis⟩ := by
  induction cs generalizing s with
  | nil => simp [correct,cval]
  | cons d cs ih =>
    cases d <;>
      simp [correct,cval,ih,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

/-- A measurement whose correction list reproduces the measured value on the
post-zeroing basis leaves the phase untouched, for either outcome. -/
private theorem meas_clean (t : Wire) (cs : List Correction) (s : State) (m : List Bool)
    (h : s.basis t = cval cs (writeBit s.basis t false)) :
    run [.measureX t [] cs] m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases hm : m.headD false
  · simp [correct,cval]
  · simp only [Bool.true_and,if_true,correct_eq,←h]
    simp [Bool.xor_assoc]

private theorem st_eq {p q : Bool} {f g : BasisState}
    (hp : p = q) (hf : ∀ w, f w = g w) : (⟨p,f⟩ : State) = ⟨q,g⟩ := by
  subst hp; exact congrArg _ (funext hf)

private theorem run_cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s = run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

private theorem cx2 (x y t : Wire) (hx : x≠t) (hy : y≠t) (s : State) (m : List Bool) :
    run [.CX x t,.CX y t] m s =
      ⟨s.phase,writeBit s.basis t ((s.basis t ^^ s.basis x) ^^ s.basis y)⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=t <;> simp_all [writeBit,Function.update]

theorem new3_run (a b c A B A' B' : Wire) (nd : [a,b,c,A,B,A',B'].Nodup)
    (s : State) (m : List Bool) (ready : Ready3 a b c A B A' B' s.basis) :
    run (newLeaf3At a b c A B A' B') m s = post3 a b c B B' s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB'⟩,⟨hbc,hbA,hbB,hbA',hbB'⟩,
    ⟨hcA,hcB,hcA',hcB'⟩,⟨hAB,hAA',hAB'⟩,⟨hBA',hBB'⟩,hA'B'⟩ := nd
  obtain ⟨r1,r2⟩ := ready
  have h1 : s.basis B' = cval [.Z A,.Z B,.Z A',.CZ A B] (writeBit s.basis B' false) := by
    simp only [cval,writeBit,Function.update_of_ne hAB',Function.update_of_ne hBB',
      Function.update_of_ne hA'B',Bool.xor_false]
    revert r1 r2
    simp only [carryBit]
    cases s.basis a <;> cases s.basis b <;> cases s.basis c <;>
      cases s.basis A <;> cases s.basis B <;> cases s.basis A' <;>
      cases s.basis B' <;> decide
  have e1 := meas_clean B' [.Z A,.Z B,.Z A',.CZ A B] s m h1
  have h2 : (⟨s.phase,writeBit s.basis B' false⟩ : State).basis B
      = cval [.Z A,.CZ a b,.CZ a c,.CZ b c]
          (writeBit (⟨s.phase,writeBit s.basis B' false⟩ : State).basis B false) := by
    simp only [cval,writeBit,Function.update_of_ne hAB,Function.update_of_ne hAB',
      Function.update_of_ne haB,Function.update_of_ne haB',
      Function.update_of_ne hbB,Function.update_of_ne hbB',
      Function.update_of_ne hcB,Function.update_of_ne hcB',
      Function.update_of_ne hBB',Bool.xor_false]
    revert r1
    simp only [carryBit]
    cases s.basis a <;> cases s.basis b <;> cases s.basis c <;>
      cases s.basis A <;> cases s.basis B <;> decide
  have e2 := meas_clean B [.Z A,.CZ a b,.CZ a c,.CZ b c] ⟨s.phase,writeBit s.basis B' false⟩
    (m.drop (measurementCount [Instr.measureX B' [] [.Z A,.Z B,.Z A',.CZ A B]])) h2
  show run ([Instr.measureX B' [] [.Z A,.Z B,.Z A',.CZ A B]]
      ++ ([Instr.measureX B [] [.Z A,.CZ a b,.CZ a c,.CZ b c]] ++ [.CX a b,.CX c b])) m s
    = post3 a b c B B' s
  rw [run_cat,e1,run_cat,e2,cx2 a c b hab (Ne.symm hbc)]
  refine st_eq rfl (fun w => ?_)
  simp only [post3,writeBit,
    Function.update_of_ne haB,Function.update_of_ne haB',
    Function.update_of_ne hbB,Function.update_of_ne hbB',
    Function.update_of_ne hcB,Function.update_of_ne hcB',sumBit]
  by_cases hw : w = b
  · subst w
    simp only [Function.update_self]
    exact Bool.xor_comm _ _ ▸ (by
      cases s.basis a <;> cases s.basis b <;> cases s.basis c <;> decide)
  · simp only [Function.update_of_ne hw]

theorem old3_run (a b c A B A' B' z z' : Wire)
    (nd : [a,b,c,A,B,A',B',z,z'].Nodup)
    (s : State) (m : List Bool)
    (cz : s.basis z = false) (cz' : s.basis z' = false) :
    run (oldLeaf3At a b c A B A' B' z z') m s =
      ⟨s.phase,
       writeBit (writeBit (writeBit (writeBit (writeBit s.basis
         z' (carryBit (s.basis A) (s.basis B)
               (carryBit (s.basis a) (s.basis b) (s.basis c))))
         B' ((s.basis B' ^^ s.basis A') ^^
               carryBit (s.basis A) (s.basis B)
                 (carryBit (s.basis a) (s.basis b) (s.basis c))))
         z' false)
         B ((s.basis B ^^ s.basis A) ^^
               carryBit (s.basis a) (s.basis b) (s.basis c)))
         b (sumBit (s.basis a) (s.basis b) (s.basis c))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haz,haz'⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbz,hbz'⟩,
          ⟨hcA,hcB,hcA',hcB',hcz,hcz'⟩,
          ⟨hAB,hAA',hAB',hAz,hAz'⟩,
          ⟨hBA',hBB',hBz,hBz'⟩,
          ⟨hA'B',hA'z,hA'z'⟩,
          ⟨hB'z,hB'z'⟩,hzz'⟩ := nd
  set K := carryBit (s.basis a) (s.basis b) (s.basis c) with hK
  set K' := carryBit (s.basis A) (s.basis B) K with hK'
  show run (majority a b c z ++ (majority A B z z' ++ ([Instr.CX A' B',.CX z' B'] ++
      (eraseCarry A B z z' ++ ([Instr.CX A B,.CX z B] ++
      (eraseCarry a b c z ++ [Instr.CX a b,.CX c b])))))) m s = _
  have n1 : [a,b,c,z].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]; exact ⟨⟨hab,hac,haz⟩,⟨hbc,hbz⟩,hcz⟩
  have n2 : [A,B,z,z'].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]; exact ⟨⟨hAB,hAz,hAz'⟩,⟨hBz,hBz'⟩,hzz'⟩
  rw [run_cat,majority_correct a b c z n1]
  simp only [cz,Bool.false_xor,←hK]
  rw [run_cat,majority_correct A B z z' n2]
  simp only [writeBit,Function.update_of_ne hAz,Function.update_of_ne hBz,
    Function.update_self,Function.update_of_ne (Ne.symm hzz'),cz',Bool.false_xor,←hK']
  rw [run_cat,cx2 A' z' B' hA'B' (Ne.symm hB'z')]
  simp only [writeBit,Function.update_of_ne hA'z,Function.update_of_ne (Ne.symm hA'z'),
    Function.update_self,Function.update_of_ne hB'z,Function.update_of_ne hB'z']
  rw [run_cat,eraseCarry_correct A B z z' hAz' hBz' hzz' _ (by
    simp only [writeBit,
      Function.update_of_ne (Ne.symm hB'z'),Function.update_self,
      Function.update_of_ne hAB',Function.update_of_ne hAz',Function.update_of_ne hAz,
      Function.update_of_ne hBB',Function.update_of_ne hBz',Function.update_of_ne hBz,
      Function.update_of_ne (Ne.symm hB'z),Function.update_of_ne hzz',←hK'])]
  rw [run_cat,cx2 A z B hAB (Ne.symm hBz)]
  rw [run_cat,eraseCarry_correct a b c z haz hbz hcz _ (by
    simp only [writeBit,
      Function.update_of_ne (Ne.symm hBz),Function.update_of_ne hzz',
      Function.update_of_ne (Ne.symm hB'z),Function.update_self,
      Function.update_of_ne haB,Function.update_of_ne haz',Function.update_of_ne haB',
      Function.update_of_ne haz,
      Function.update_of_ne hbB,Function.update_of_ne hbz',Function.update_of_ne hbB',
      Function.update_of_ne hbz,
      Function.update_of_ne hcB,Function.update_of_ne hcz',Function.update_of_ne hcB',
      Function.update_of_ne hcz,←hK])]
  rw [cx2 a c b hab (Ne.symm hbc)]
  have q1 := Ne.symm hB'z; have q2 := Ne.symm hBz; have q3 := Ne.symm hzz'
  have q4 := Ne.symm hbz; have q5 := Ne.symm hB'z'; have q6 := Ne.symm hBz'
  have q7 := Ne.symm hbz'; have q8 := Ne.symm hbB; have q9 := Ne.symm hbB'
  have q10 := Ne.symm hA'z; have q11 := Ne.symm hA'z'; have q12 := Ne.symm hAz
  have q13 := Ne.symm hAz'; have q14 := Ne.symm haz; have q15 := Ne.symm haz'
  have q16 := Ne.symm hcz; have q17 := Ne.symm hcz'; have q18 := Ne.symm haB
  have q19 := Ne.symm haB'; have q20 := Ne.symm hcB; have q21 := Ne.symm hcB'
  have q22 := Ne.symm hAB'; have q23 := Ne.symm hA'B'; have q24 := Ne.symm hBA'
  have q25 := Ne.symm hAA'; have q26 := Ne.symm hAB; have q27 := Ne.symm hBB'
  refine st_eq rfl (fun w => ?_)
  by_cases hwz : w = z <;> by_cases hwb : w = b <;>
    by_cases hwB : w = B <;> by_cases hwB' : w = B' <;> by_cases hwz' : w = z' <;>
    subst_vars <;>
    simp_all [writeBit,Function.update,sumBit,
      Bool.xor_comm,Bool.xor_assoc,Bool.xor_left_comm]

/-- **Main result.** On the restriction that output bits 256 and 257 are zero,
the two-Toffoli three-bit leaf and the zero-Toffoli replacement agree as complete
States — phase included — for arbitrary and independent measurement records. -/
theorem full_state3 (a b c A B A' B' z z' : Wire)
    (nd : [a,b,c,A,B,A',B',z,z'].Nodup) (s : State) (m n : List Bool)
    (cz : s.basis z = false) (cz' : s.basis z' = false)
    (ready : Ready3 a b c A B A' B' s.basis) :
    run (oldLeaf3At a b c A B A' B' z z') m s
      = run (newLeaf3At a b c A B A' B') n s := by
  have nd7 : [a,b,c,A,B,A',B'].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd ⊢
    tauto
  rw [old3_run a b c A B A' B' z z' nd s m cz cz',
      new3_run a b c A B A' B' nd7 s n ready]
  obtain ⟨r1,r2⟩ := ready
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haz,haz'⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbz,hbz'⟩,
          ⟨hcA,hcB,hcA',hcB',hcz,hcz'⟩,
          ⟨hAB,hAA',hAB',hAz,hAz'⟩,
          ⟨hBA',hBB',hBz,hBz'⟩,
          ⟨hA'B',hA'z,hA'z'⟩,
          ⟨hB'z,hB'z'⟩,hzz'⟩ := nd
  have v2 : (s.basis B ^^ s.basis A) ^^
      carryBit (s.basis a) (s.basis b) (s.basis c) = false := by
    simpa [Bool.xor_comm] using r1
  have v1 : (s.basis B' ^^ s.basis A') ^^
      carryBit (s.basis A) (s.basis B)
        (carryBit (s.basis a) (s.basis b) (s.basis c)) = false := by
    simpa [Bool.xor_comm] using r2
  have q5 := Ne.symm hB'z'; have q7 := Ne.symm hbz'; have q6 := Ne.symm hBz'
  have q8 := Ne.symm hbB; have q9 := Ne.symm hbB'; have q27 := Ne.symm hBB'
  refine st_eq rfl (fun w => ?_)
  by_cases hwz' : w = z' <;> by_cases hwb : w = b <;>
    by_cases hwB : w = B <;> by_cases hwB' : w = B' <;>
    subst_vars <;>
    simp_all [writeBit,Function.update,post3,v1,v2]

/-! ### Wrapper: substitution inside a surrounding program. -/

/-- The two high output bits of the whole program determine `Ready3` at the leaf boundary. -/
theorem prefix_leaf3_high (P R : Program) (a b c A B A' B' z z' : Wire)
    (nd : [a,b,c,A,B,A',B',z,z'].Nodup) (s : State) (m : List Bool)
    (cz : s.basis z=false) (cz' : s.basis z'=false)
    (hzP : z∉wires P) (hz'P : z'∉wires P) (hBR : B∉wires R) (hB'R : B'∉wires R)
    (topB  : (run (P++oldLeaf3At a b c A B A' B' z z'++R) [] s).basis B = false)
    (topB' : (run (P++oldLeaf3At a b c A B A' B' z z'++R) [] s).basis B' = false) :
    Ready3 a b c A B A' B' (run P m s).basis := by
  have nd' := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd'
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haz,haz'⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbz,hbz'⟩,
          ⟨hcA,hcB,hcA',hcB',hcz,hcz'⟩,
          ⟨hAB,hAA',hAB',hAz,hAz'⟩,
          ⟨hBA',hBB',hBz,hBz'⟩,
          ⟨hA'B',hA'z,hA'z'⟩,
          ⟨hB'z,hB'z'⟩,hzz'⟩ := nd'
  have tz  : (run P [] s).basis z  = false := (run_preserves_outside P [] s z hzP).trans cz
  have tz' : (run P [] s).basis z' = false := (run_preserves_outside P [] s z' hz'P).trans cz'
  have hB0 : (run (oldLeaf3At a b c A B A' B' z z') [] (run P [] s)).basis B = false := by
    have h := topB
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B hBR] at h
    exact h
  have hB'0 : (run (oldLeaf3At a b c A B A' B' z z') [] (run P [] s)).basis B' = false := by
    have h := topB'
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B' hB'R] at h
    exact h
  rw [old3_run a b c A B A' B' z z' nd (run P [] s) [] tz tz'] at hB0 hB'0
  simp only [writeBit, Function.update] at hB0 hB'0
  simp only [hbB, hBz', hBB', hbB', hB'z', eq_self_iff_true, if_true, if_false,
    Ne.symm hbB, Ne.symm hBz', Ne.symm hBB', Ne.symm hbB', Ne.symm hB'z'] at hB0 hB'0
  have pb : (run P m s).basis = (run P [] s).basis := run_basis_records P s s m [] rfl
  constructor
  · rw [pb]; rw [Bool.xor_comm ((run P [] s).basis A) ((run P [] s).basis B)]; exact hB0
  · rw [pb]; rw [Bool.xor_comm ((run P [] s).basis A') ((run P [] s).basis B')]; exact hB'0

/-- Whole-program zero-top replacement for the THREE-bit leaf: two Toffolis removed. -/
theorem whole_zero3 (P R : Program) (a b c A B A' B' z z' : Wire)
    (nd : [a,b,c,A,B,A',B',z,z'].Nodup) (s : State) (m : List Bool)
    (cz : s.basis z=false) (cz' : s.basis z'=false)
    (hzP : z∉wires P) (hz'P : z'∉wires P) (hBR : B∉wires R) (hB'R : B'∉wires R)
    (topB  : (run (P++oldLeaf3At a b c A B A' B' z z'++R) [] s).basis B = false)
    (topB' : (run (P++oldLeaf3At a b c A B A' B' z z'++R) [] s).basis B' = false) :
    run (P++oldLeaf3At a b c A B A' B' z z'++R) m s
      = run (P++newLeaf3At a b c A B A' B'++R) m s := by
  have tz  : (run P m s).basis z  = false := (run_preserves_outside P m s z hzP).trans cz
  have tz' : (run P m s).basis z' = false := (run_preserves_outside P m s z' hz'P).trans cz'
  have ready := prefix_leaf3_high P R a b c A B A' B' z z' nd s m cz cz' hzP hz'P hBR hB'R topB topB'
  have eqn := full_state3 a b c A B A' B' z z' nd (run P m s)
    (m.drop (measurementCount P)) (m.drop (measurementCount P)) tz tz' ready
  simpa only [run_cat, measurementCount_append,
    (old3_counts a b c A B A' B' z z').2, (new3_counts a b c A B A' B').2,
    List.drop_drop, Nat.add_comm] using
    congrArg (run R ((m.drop (measurementCount P)).drop 2)) eqn

#print axioms prefix_leaf3_high
#print axioms whole_zero3

/-! ### Instantiation at the KAdd indices -/
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

/-- Mirror of `add_split`, peeling THREE bits. -/
theorem add_split3 (xs ys cs : List Wire) (cin a A A' b B B' z z' : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    addInPlace (xs++[a,A,A']) (ys++[b,B,B']) (cs++[z,z']) cin=
      adderPrefix xs ys cs cin
        ++ oldLeaf3At a b (lastCarry cs cin) A B A' B' z z'
        ++ adderSuffix xs ys cs cin := by
  induction xs generalizing ys cs cin with
  | nil =>
    have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
    have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
    subst ys; subst cs; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have hy' : xs.length=ys.length := by simpa using hy
        have hc' : xs.length=cs.length := by simpa using hc
        have step : addInPlace ((x::xs)++[a,A,A']) ((y::ys)++[b,B,B']) ((c::cs)++[z,z']) cin=
            majority x y cin c++addInPlace (xs++[a,A,A']) (ys++[b,B,B']) (cs++[z,z']) c++
              eraseCarry x y cin c++[.CX x y,.CX cin y] := by
          cases xs <;> cases ys <;> rfl
        rw [step,ih ys cs c hy' hc']
        simp only [adderPrefix,adderSuffix,lastCarry,List.append_assoc]

def P3 (w : Nat→Wire) : Program :=
  adderPrefix (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255) (w 1797)
def R3 (w : Nat→Wire) : Program :=
  adderSuffix (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255) (w 1797)

private theorem lastCarry_cat3 (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs ++ ys) cin = lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => exact ih x

/-- Peel the top THREE bits of the real KAdd adder. -/
theorem literal_split3 (w : Nat→Wire) :
    literalKAdd w = P3 w
      ++ oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796)
      ++ R3 w := by
  have hx : wireBlock w 0 258=wireBlock w 0 255++[w 255,w 256,w 257] := by
    rw [←wireBlock_append w 0 255 3]; rfl
  have hy : wireBlock w 770 258=wireBlock w 770 255++[w 1025,w 1026,w 1027] := by
    rw [←wireBlock_append w 770 255 3]; rfl
  have hc : wireBlock w 1540 257=wireBlock w 1540 255++[w 1795,w 1796] := by
    rw [←wireBlock_append w 1540 255 2]; rfl
  have lastBlock : wireBlock w 1540 255 = wireBlock w 1540 254 ++ [w 1794] := by
    rw [←wireBlock_append w 1540 254 1]; rfl
  have last : lastCarry (wireBlock w 1540 255) (w 1797)=w 1794 := by
    rw [lastBlock,lastCarry_cat3]; rfl
  rw [literalKAdd,read_add,hx,hy,hc]
  simpa only [P3,R3,last] using add_split3
    (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255)
    (w 1797) (w 255) (w 256) (w 257) (w 1025) (w 1026) (w 1027) (w 1795) (w 1796)
    (by simp [wireBlock_length]) (by simp [wireBlock_length])

/-- The three-bit zero replacement of the whole KAdd adder: 255 Toffolis. -/
def zero3KAdd (w : Nat→Wire) : Program :=
  P3 w ++ newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) ++ R3 w


/-- Counts: the three-bit zero replacement costs 255 Toffolis, two fewer than the literal. -/
theorem zero3_counts (w : Nat→Wire)
    (hlit : toffoliCount (literalKAdd w)=257 ∧ measurementCount (literalKAdd w)=257) :
    toffoliCount (zero3KAdd w)=255 ∧ measurementCount (zero3KAdd w)=257 := by
  have hs := literal_split3 w
  have ho := old3_counts (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796)
  have hn := new3_counts (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
  rw [hs] at hlit
  simp only [toffoliCount_append, measurementCount_append, ho.1, ho.2] at hlit
  simp only [zero3KAdd, toffoliCount_append, measurementCount_append, hn.1, hn.2]
  omega

#print axioms zero3_counts


/-! ### Side conditions for `whole_zero3` at the KAdd indices -/

theorem low_avoid3 (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) :
    w i ∉ spinePorts (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255) (w 1797) := by
  intro h
  simp only [spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e:=hinj h; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega

attribute [local irreducible] ECDSAAdd.wires in
theorem P3_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) : w i∉wires (P3 w) := by
  intro h
  exact low_avoid3 w hinj i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section R3SupportOpaque
attribute [local irreducible] ECDSAAdd.wires
theorem R3_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) : w i∉wires (R3 w) := by
  intro h
  have support := suffix_support (wireBlock w 0 255) (wireBlock w 770 255)
    (wireBlock w 1540 255) (w 1797)
  exact low_avoid3 w hinj i hi (List.mem_toFinset.mp (support h))
end R3SupportOpaque

theorem tail3_nd (w : Nat→Wire) (hinj : Function.Injective w) :
    [w 255,w 1025,w 1794,w 256,w 1026,w 257,w 1027,w 1795,w 1796].Nodup :=
  List.Nodup.map hinj (by decide : [255,1025,1794,256,1026,257,1027,1795,1796].Nodup)

#print axioms P3_avoid
#print axioms R3_avoid
#print axioms tail3_nd


/-! ### Extracting the two zero output bits from the word value (mirrors `top_from_div`) -/

theorem bit256_from_div (w : Nat→Wire) (s : BasisState) (W : Nat) (flag : Bool)
    (postWord : regValue (wireBlock w 770 258) s=W) (hdiv : W/2^256%2=flag.toNat) :
    s (w 1026)=flag := by
  have h:=regValue_bit (wireBlock w 770 258) 256 0 s (by simp [wireBlock_length])
  have port : (wireBlock w 770 258).getD 256 0=w 1026 := by rfl
  rw [port,postWord,hdiv] at h
  cases hs : s (w 1026) <;> cases flag <;> simp [hs] at h ⊢

theorem bit257_from_div (w : Nat→Wire) (s : BasisState) (W : Nat) (flag : Bool)
    (postWord : regValue (wireBlock w 770 258) s=W) (hdiv : W/2^257%2=flag.toNat) :
    s (w 1027)=flag := by
  have h:=regValue_bit (wireBlock w 770 258) 257 0 s (by simp [wireBlock_length])
  have port : (wireBlock w 770 258).getD 257 0=w 1027 := by rfl
  rw [port,postWord,hdiv] at h
  cases hs : s (w 1027) <;> cases flag <;> simp [hs] at h ⊢

/-- For the exit caller the word is `Y/2 < 2^255`, so BOTH high bits vanish. -/
theorem exit_two_zero (w : Nat→Wire) (s : BasisState) (W : Nat) (hW : W<2^255)
    (postWord : regValue (wireBlock w 770 258) s=W) :
    s (w 1026)=false ∧ s (w 1027)=false := by
  have l6 : (2:Nat)^255 ≤ 2^256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have l7 : (2:Nat)^255 ≤ 2^257 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have d6 : W/2^256=0 := Nat.div_eq_of_lt (lt_of_lt_of_le hW l6)
  have d7 : W/2^257=0 := Nat.div_eq_of_lt (lt_of_lt_of_le hW l7)
  have h256 : W/2^256%2=(false : Bool).toNat := by rw [d6]; rfl
  have h257 : W/2^257%2=(false : Bool).toNat := by rw [d7]; rfl
  exact ⟨bit256_from_div w s W false postWord h256, bit257_from_div w s W false postWord h257⟩

#print axioms bit256_from_div
#print axioms bit257_from_div
#print axioms exit_two_zero


end Verifier.Leaf3
end


-- Consolidated source module: AffineCarry3B
section

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 400

namespace Verifier.Leaf3
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

section Exit3Opaque
attribute [local irreducible] ECDSAAdd.wires
set_option maxHeartbeats 16000000 in
theorem exit3_run_eq_split (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean5 : s.basis (w 1795)=false) (clean6 : s.basis (w 1796)=false)
    (topB  : (run (P3 w++oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
                (w 1795) (w 1796)++R3 w) [] s).basis (w 1026)=false)
    (topB' : (run (P3 w++oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
                (w 1795) (w 1796)++R3 w) [] s).basis (w 1027)=false) :
    run (P3 w++oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
          (w 1795) (w 1796)++R3 w) m s
      = run (P3 w++newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)++R3 w) m s := by
  exact whole_zero3 (P3 w) (R3 w) (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
    (w 1795) (w 1796) (tail3_nd w hinj) s m clean5 clean6
    (P3_avoid w hinj 1795 (Or.inl rfl)) (P3_avoid w hinj 1796 (Or.inr (Or.inl rfl)))
    (R3_avoid w hinj 1026 (Or.inr (Or.inr (Or.inl rfl))))
    (R3_avoid w hinj 1027 (Or.inr (Or.inr (Or.inr rfl)))) topB topB'
end Exit3Opaque

/-- Same bridge, stated on the literal adder. The module boundary keeps `P3`/`R3` opaque. -/
theorem exit3_run_eq (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean5 : s.basis (w 1795)=false) (clean6 : s.basis (w 1796)=false)
    (topB  : (run (literalKAdd w) [] s).basis (w 1026)=false)
    (topB' : (run (literalKAdd w) [] s).basis (w 1027)=false) :
    run (literalKAdd w) m s=run (zero3KAdd w) m s := by
  rw [literal_split3] at topB topB'
  rw [literal_split3, zero3KAdd]
  exact exit3_run_eq_split w hinj s m clean5 clean6 topB topB'

#print axioms exit3_run_eq
end Verifier.Leaf3
end


-- Consolidated source module: AffineCarry3C
section

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
end


-- Consolidated source module: AffineCarry4A
section

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 400

namespace Verifier.Leaf4
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
open Verifier.Leaf3 (cval oldLeaf3At old3_run old3_counts)

/-- The four-bit terminal suffix: three retired clean carries `z`, `z'`, `z''`. -/
def oldLeaf4At (a b c A B A' B' A'' B'' z z' z'' : Wire) : Program :=
  addInPlace [a,A,A',A''] [b,B,B',B''] [z,z',z''] c

/-- Zero-Toffoli replacement. `B''`, `B'`, `B` are measured strictly top-down:
each correction list names a wire that is still live. -/
def newLeaf4At (a b c A B A' B' A'' B'' : Wire) : Program :=
  [.measureX B'' [] [.Z A', .Z B', .Z A'', .CZ A' B'],
   .measureX B'  [] [.Z A,  .Z B,  .Z A',  .CZ A  B],
   .measureX B   [] [.Z A, .CZ a b, .CZ a c, .CZ b c],
   .CX a b, .CX c b]

/-- Output bits 255, 256 and 257 of the sum are zero. -/
def Ready4 (a b c A B A' B' A'' B'' : Wire) (s : BasisState) : Prop :=
  ((s A ^^ s B) ^^ carryBit (s a) (s b) (s c)) = false ∧
  ((s A' ^^ s B') ^^ carryBit (s A) (s B) (carryBit (s a) (s b) (s c))) = false ∧
  ((s A'' ^^ s B'') ^^
     carryBit (s A') (s B') (carryBit (s A) (s B) (carryBit (s a) (s b) (s c)))) = false

/-! ### Structural checks -/

theorem old4_unfold (a b c A B A' B' A'' B'' z z' z'' : Wire) :
    oldLeaf4At a b c A B A' B' A'' B'' z z' z''
      = majority a b c z ++ oldLeaf3At A B z A' B' A'' B'' z' z''
          ++ eraseCarry a b c z ++ [.CX a b, .CX c b] := rfl

theorem old4_counts (a b c A B A' B' A'' B'' z z' z'' : Wire) :
    toffoliCount (oldLeaf4At a b c A B A' B' A'' B'' z z' z'')=3
      ∧ measurementCount (oldLeaf4At a b c A B A' B' A'' B'' z z' z'')=3 := by
  constructor <;> rfl

theorem new4_counts (a b c A B A' B' A'' B'' : Wire) :
    toffoliCount (newLeaf4At a b c A B A' B' A'' B'')=0
      ∧ measurementCount (newLeaf4At a b c A B A' B' A'' B'')=3 := by
  constructor <;> rfl

/-! ### Boolean content of the three correction lists.

Each is a pure `Bool` identity on the nine leaf values, closed by `decide`
over the 512-point cube.  The point of the construction is that all three stay
degree two: on the restricted domain the degree-three majority collapses. -/

private theorem corr_top : ∀ (va vb vc vA vB vA' vB' vA'' vB'' : Bool),
    ((vA' ^^ vB') ^^ carryBit vA vB (carryBit va vb vc)) = false →
    ((vA'' ^^ vB'') ^^
      carryBit vA' vB' (carryBit vA vB (carryBit va vb vc))) = false →
    vB'' = (vA' ^^ (vB' ^^ (vA'' ^^ (vA' && vB')))) := by decide

private theorem corr_mid : ∀ (va vb vc vA vB vA' vB' : Bool),
    ((vA ^^ vB) ^^ carryBit va vb vc) = false →
    ((vA' ^^ vB') ^^ carryBit vA vB (carryBit va vb vc)) = false →
    vB' = (vA ^^ (vB ^^ (vA' ^^ (vA && vB)))) := by decide

private theorem corr_low : ∀ (va vb vc vA vB : Bool),
    ((vA ^^ vB) ^^ carryBit va vb vc) = false →
    vB = (vA ^^ ((va && vb) ^^ ((va && vc) ^^ (vb && vc)))) := by decide

/-! ### Reusable run-level helpers (mirrors of the three-bit module's privates). -/

private theorem correct_eq (cs : List Correction) (s : State) :
    correct cs s = ⟨s.phase ^^ cval cs s.basis, s.basis⟩ := by
  induction cs generalizing s with
  | nil => simp [correct,cval]
  | cons d cs ih =>
    cases d <;>
      simp [correct,cval,ih,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

private theorem meas_clean (t : Wire) (cs : List Correction) (s : State) (m : List Bool)
    (h : s.basis t = cval cs (writeBit s.basis t false)) :
    run [.measureX t [] cs] m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases hm : m.headD false
  · simp [correct,cval]
  · simp only [Bool.true_and,if_true,correct_eq,←h]
    simp [Bool.xor_assoc]

private theorem st_eq {p q : Bool} {f g : BasisState}
    (hp : p = q) (hf : ∀ w, f w = g w) : (⟨p,f⟩ : State) = ⟨q,g⟩ := by
  subst hp; exact congrArg _ (funext hf)

private theorem run_cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s = run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

private theorem cx2 (x y t : Wire) (hx : x≠t) (hy : y≠t) (s : State) (m : List Bool) :
    run [.CX x t,.CX y t] m s =
      ⟨s.phase,writeBit s.basis t ((s.basis t ^^ s.basis x) ^^ s.basis y)⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=t <;> simp_all [writeBit,Function.update]

/-- Common final state: `b` holds the low sum, all three high outputs are zeroed,
phase is untouched. -/
private def post4 (a b c B B' B'' : Wire) (s : State) : State :=
  ⟨s.phase,
   writeBit (writeBit (writeBit (writeBit s.basis B'' false) B' false) B false) b
     (sumBit (s.basis a) (s.basis b) (s.basis c))⟩

theorem new4_run (a b c A B A' B' A'' B'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B''].Nodup)
    (s : State) (m : List Bool) (ready : Ready4 a b c A B A' B' A'' B'' s.basis) :
    run (newLeaf4At a b c A B A' B' A'' B'') m s = post4 a b c B B' B'' s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB''⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB''⟩,
          ⟨hcA,hcB,hcA',hcB',hcA'',hcB''⟩,
          ⟨hAB,hAA',hAB',hAA'',hAB''⟩,
          ⟨hBA',hBB',hBA'',hBB''⟩,
          ⟨hA'B',hA'A'',hA'B''⟩,
          ⟨hB'A'',hB'B''⟩,hA''B''⟩ := nd
  obtain ⟨r1,r2,r3⟩ := ready
  -- top measurement: B''
  have h1 : s.basis B''
      = cval [.Z A',.Z B',.Z A'',.CZ A' B'] (writeBit s.basis B'' false) := by
    simp only [cval,writeBit,Function.update_of_ne hA'B'',Function.update_of_ne hB'B'',
      Function.update_of_ne hA''B'',Bool.xor_false]
    exact corr_top _ _ _ _ _ _ _ _ _ r2 r3
  have e1 := meas_clean B'' [.Z A',.Z B',.Z A'',.CZ A' B'] s m h1
  -- middle measurement: B'
  have h2 : (⟨s.phase,writeBit s.basis B'' false⟩ : State).basis B'
      = cval [.Z A,.Z B,.Z A',.CZ A B]
          (writeBit (⟨s.phase,writeBit s.basis B'' false⟩ : State).basis B' false) := by
    simp only [cval,writeBit,
      Function.update_of_ne hAB',Function.update_of_ne hAB'',
      Function.update_of_ne hBB',Function.update_of_ne hBB'',
      Function.update_of_ne hA'B',Function.update_of_ne hA'B'',
      Function.update_of_ne hB'B'',Bool.xor_false]
    exact corr_mid _ _ _ _ _ _ _ r1 r2
  have e2 := meas_clean B' [.Z A,.Z B,.Z A',.CZ A B]
    ⟨s.phase,writeBit s.basis B'' false⟩
    (m.drop (measurementCount [Instr.measureX B'' [] [.Z A',.Z B',.Z A'',.CZ A' B']])) h2
  -- low measurement: B
  have h3 : (⟨s.phase,writeBit (writeBit s.basis B'' false) B' false⟩ : State).basis B
      = cval [.Z A,.CZ a b,.CZ a c,.CZ b c]
          (writeBit (⟨s.phase,writeBit (writeBit s.basis B'' false) B' false⟩ : State).basis
            B false) := by
    simp only [cval,writeBit,
      Function.update_of_ne hAB,Function.update_of_ne hAB',Function.update_of_ne hAB'',
      Function.update_of_ne haB,Function.update_of_ne haB',Function.update_of_ne haB'',
      Function.update_of_ne hbB,Function.update_of_ne hbB',Function.update_of_ne hbB'',
      Function.update_of_ne hcB,Function.update_of_ne hcB',Function.update_of_ne hcB'',
      Function.update_of_ne hBB',Function.update_of_ne hBB'',Bool.xor_false]
    exact corr_low _ _ _ _ _ r1
  have e3 := meas_clean B [.Z A,.CZ a b,.CZ a c,.CZ b c]
    ⟨s.phase,writeBit (writeBit s.basis B'' false) B' false⟩
    ((m.drop (measurementCount [Instr.measureX B'' [] [.Z A',.Z B',.Z A'',.CZ A' B']])).drop
      (measurementCount [Instr.measureX B' [] [.Z A,.Z B,.Z A',.CZ A B]])) h3
  show run ([Instr.measureX B'' [] [.Z A',.Z B',.Z A'',.CZ A' B']]
      ++ ([Instr.measureX B' [] [.Z A,.Z B,.Z A',.CZ A B]]
      ++ ([Instr.measureX B [] [.Z A,.CZ a b,.CZ a c,.CZ b c]]
      ++ [.CX a b,.CX c b]))) m s = post4 a b c B B' B'' s
  rw [run_cat,e1,run_cat,e2,run_cat,e3,cx2 a c b hab (Ne.symm hbc)]
  refine st_eq rfl (fun w => ?_)
  simp only [post4,writeBit,
    Function.update_of_ne haB,Function.update_of_ne haB',Function.update_of_ne haB'',
    Function.update_of_ne hbB,Function.update_of_ne hbB',Function.update_of_ne hbB'',
    Function.update_of_ne hcB,Function.update_of_ne hcB',Function.update_of_ne hcB'',sumBit]
  by_cases hw : w = b
  · subst w
    simp only [Function.update_self]
    exact Bool.xor_comm _ _ ▸ (by
      cases s.basis a <;> cases s.basis b <;> cases s.basis c <;> decide)
  · simp only [Function.update_of_ne hw]

#print axioms new4_run

/-- Closed form of the four-bit in-place adder leaf, reusing the three-bit result
for the inner suffix.  `z` is written and erased invisibly. -/
theorem old4_run (a b c A B A' B' A'' B'' z z' z'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B'',z,z',z''].Nodup)
    (s : State) (m : List Bool)
    (cz : s.basis z = false) (cz' : s.basis z' = false) (cz'' : s.basis z'' = false) :
    run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') m s =
      ⟨s.phase,
       writeBit (writeBit (writeBit (writeBit (writeBit (writeBit s.basis
         z'' (carryBit (s.basis A') (s.basis B')
               (carryBit (s.basis A) (s.basis B)
                 (carryBit (s.basis a) (s.basis b) (s.basis c)))))
         B'' ((s.basis B'' ^^ s.basis A'') ^^
               carryBit (s.basis A') (s.basis B')
                 (carryBit (s.basis A) (s.basis B)
                   (carryBit (s.basis a) (s.basis b) (s.basis c)))))
         z'' false)
         B' ((s.basis B' ^^ s.basis A') ^^
               carryBit (s.basis A) (s.basis B)
                 (carryBit (s.basis a) (s.basis b) (s.basis c))))
         B (sumBit (s.basis A) (s.basis B)
               (carryBit (s.basis a) (s.basis b) (s.basis c))))
         b (sumBit (s.basis a) (s.basis b) (s.basis c))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB'',haz,haz',haz''⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB'',hbz,hbz',hbz''⟩,
          ⟨hcA,hcB,hcA',hcB',hcA'',hcB'',hcz,hcz',hcz''⟩,
          ⟨hAB,hAA',hAB',hAA'',hAB'',hAz,hAz',hAz''⟩,
          ⟨hBA',hBB',hBA'',hBB'',hBz,hBz',hBz''⟩,
          ⟨hA'B',hA'A'',hA'B'',hA'z,hA'z',hA'z''⟩,
          ⟨hB'A'',hB'B'',hB'z,hB'z',hB'z''⟩,
          ⟨hA''B'',hA''z,hA''z',hA''z''⟩,
          ⟨hB''z,hB''z',hB''z''⟩,
          ⟨hzz',hzz''⟩,
          hz'z''⟩ := nd
  set K1 := carryBit (s.basis a) (s.basis b) (s.basis c) with hK1
  set K2 := carryBit (s.basis A) (s.basis B) K1 with hK2
  set K3 := carryBit (s.basis A') (s.basis B') K2 with hK3
  have n1 : [a,b,c,z].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]; exact ⟨⟨hab,hac,haz⟩,⟨hbc,hbz⟩,hcz⟩
  have nd9 : [A,B,z,A',B',A'',B'',z',z''].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨hAB,hAz,hAA',hAB',hAA'',hAB'',hAz',hAz''⟩,
           ⟨hBz,hBA',hBB',hBA'',hBB'',hBz',hBz''⟩,
           ⟨Ne.symm hA'z,Ne.symm hB'z,Ne.symm hA''z,Ne.symm hB''z,hzz',hzz''⟩,
           ⟨hA'B',hA'A'',hA'B'',hA'z',hA'z''⟩,
           ⟨hB'A'',hB'B'',hB'z',hB'z''⟩,
           ⟨hA''B'',hA''z',hA''z''⟩,
           ⟨hB''z',hB''z''⟩,hz'z''⟩
  have pz' : (⟨s.phase,writeBit s.basis z K1⟩ : State).basis z' = false := by
    simp only [writeBit,Function.update_of_ne (Ne.symm hzz')]; exact cz'
  have pz'' : (⟨s.phase,writeBit s.basis z K1⟩ : State).basis z'' = false := by
    simp only [writeBit,Function.update_of_ne (Ne.symm hzz'')]; exact cz''
  show run (majority a b c z ++ (oldLeaf3At A B z A' B' A'' B'' z' z''
      ++ (eraseCarry a b c z ++ [Instr.CX a b,.CX c b]))) m s = _
  rw [run_cat,majority_correct a b c z n1]
  simp only [cz,Bool.false_xor,←hK1]
  rw [run_cat,old3_run A B z A' B' A'' B'' z' z'' nd9 ⟨s.phase,writeBit s.basis z K1⟩ _ pz' pz'']
  simp only [writeBit,
    Function.update_of_ne (Ne.symm hAz),Function.update_of_ne (Ne.symm hBz),
    Function.update_of_ne (Ne.symm hA'z),Function.update_of_ne (Ne.symm hB'z),
    Function.update_of_ne (Ne.symm hA''z),Function.update_of_ne (Ne.symm hB''z),
    Function.update_self,←hK2,←hK3]
  rw [run_cat,eraseCarry_correct a b c z haz hbz hcz _ (by
    simp only [writeBit,
      Function.update_of_ne (Ne.symm hBz),Function.update_of_ne (Ne.symm hB'z),
      Function.update_of_ne (Ne.symm hB''z),Function.update_of_ne hzz'',
      Function.update_self,
      Function.update_of_ne haB,Function.update_of_ne haB',Function.update_of_ne haB'',
      Function.update_of_ne haz'',Function.update_of_ne haz,
      Function.update_of_ne hbB,Function.update_of_ne hbB',Function.update_of_ne hbB'',
      Function.update_of_ne hbz'',Function.update_of_ne hbz,
      Function.update_of_ne hcB,Function.update_of_ne hcB',Function.update_of_ne hcB'',
      Function.update_of_ne hcz'',Function.update_of_ne hcz,←hK1])]
  rw [cx2 a c b hab (Ne.symm hbc)]
  have q1 := Ne.symm hzz'; have q2 := Ne.symm hzz''; have q3 := Ne.symm hz'z''
  have q4 := Ne.symm hbz; have q5 := Ne.symm hbz'; have q6 := Ne.symm hbz''
  have q7 := Ne.symm hbB; have q8 := Ne.symm hbB'; have q9 := Ne.symm hbB''
  have q10 := Ne.symm hBz; have q11 := Ne.symm hBz'; have q12 := Ne.symm hBz''
  have q13 := Ne.symm hB'z; have q14 := Ne.symm hB'z'; have q15 := Ne.symm hB'z''
  have q16 := Ne.symm hB''z; have q17 := Ne.symm hB''z'; have q18 := Ne.symm hB''z''
  have q19 := Ne.symm hAz; have q20 := Ne.symm hAz'; have q21 := Ne.symm hAz''
  have q22 := Ne.symm hA'z; have q23 := Ne.symm hA'z'; have q24 := Ne.symm hA'z''
  have q25 := Ne.symm hA''z; have q26 := Ne.symm hA''z'; have q27 := Ne.symm hA''z''
  have q28 := Ne.symm haz; have q29 := Ne.symm hcz; have q30 := Ne.symm haB
  have q31 := Ne.symm haB'; have q32 := Ne.symm haB''; have q33 := Ne.symm hcB
  have q34 := Ne.symm hcB'; have q35 := Ne.symm hcB''; have q36 := Ne.symm hAB
  have q37 := Ne.symm hAB'; have q38 := Ne.symm hAB''; have q39 := Ne.symm hA'B'
  have q40 := Ne.symm hA'B''; have q41 := Ne.symm hA''B''; have q42 := Ne.symm hBB'
  have q43 := Ne.symm hBB''; have q44 := Ne.symm hB'B''; have q45 := Ne.symm hBA'
  have q46 := Ne.symm hBA''; have q47 := Ne.symm hB'A''; have q48 := Ne.symm hAA'
  have q49 := Ne.symm hAA''; have q50 := Ne.symm hA'A''
  refine st_eq rfl (fun w => ?_)
  by_cases hwz : w = z <;> by_cases hwz'' : w = z'' <;>
    by_cases hwb : w = b <;> by_cases hwB : w = B <;>
    by_cases hwB' : w = B' <;> by_cases hwB'' : w = B'' <;>
    subst_vars <;>
    simp_all [writeBit,Function.update,sumBit,
      Bool.xor_comm,Bool.xor_assoc,Bool.xor_left_comm]

#print axioms old4_run

/-- Erasing a scratch wire that was clean on entry leaves no trace, even across an
intervening write to a different wire. -/
private theorem drop_scratch (f : BasisState) (u v : Wire) (huv : u ≠ v) {k x : Bool}
    (hf : f u = false) :
    writeBit (writeBit (writeBit f u k) v x) u false = writeBit f v x := by
  funext w
  by_cases h1 : w = u <;> by_cases h2 : w = v <;>
    simp_all [writeBit,Function.update]

/-- **Main result.** On the restriction that output bits 255, 256 and 257 are zero,
the three-Toffoli four-bit leaf and the zero-Toffoli replacement agree as complete
States -- phase included -- for arbitrary and independent measurement records. -/
theorem full_state4 (a b c A B A' B' A'' B'' z z' z'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B'',z,z',z''].Nodup) (s : State) (m n : List Bool)
    (cz : s.basis z = false) (cz' : s.basis z' = false) (cz'' : s.basis z'' = false)
    (ready : Ready4 a b c A B A' B' A'' B'' s.basis) :
    run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') m s
      = run (newLeaf4At a b c A B A' B' A'' B'') n s := by
  have nd' := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd'
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB'',haz,haz',haz''⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB'',hbz,hbz',hbz''⟩,
          ⟨hcA,hcB,hcA',hcB',hcA'',hcB'',hcz,hcz',hcz''⟩,
          ⟨hAB,hAA',hAB',hAA'',hAB'',hAz,hAz',hAz''⟩,
          ⟨hBA',hBB',hBA'',hBB'',hBz,hBz',hBz''⟩,
          ⟨hA'B',hA'A'',hA'B'',hA'z,hA'z',hA'z''⟩,
          ⟨hB'A'',hB'B'',hB'z,hB'z',hB'z''⟩,
          ⟨hA''B'',hA''z,hA''z',hA''z''⟩,
          ⟨hB''z,hB''z',hB''z''⟩,
          ⟨hzz',hzz''⟩,
          hz'z''⟩ := nd'
  have nd9 : [a,b,c,A,B,A',B',A'',B''].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB''⟩,
           ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB''⟩,
           ⟨hcA,hcB,hcA',hcB',hcA'',hcB''⟩,
           ⟨hAB,hAA',hAB',hAA'',hAB''⟩,
           ⟨hBA',hBB',hBA'',hBB''⟩,
           ⟨hA'B',hA'A'',hA'B''⟩,
           ⟨hB'A'',hB'B''⟩,hA''B''⟩
  obtain ⟨r1,r2,r3⟩ := ready
  have v1 : (s.basis B'' ^^ s.basis A'' ^^
      carryBit (s.basis A') (s.basis B')
        (carryBit (s.basis A) (s.basis B)
          (carryBit (s.basis a) (s.basis b) (s.basis c)))) = false := by
    simpa [Bool.xor_comm] using r3
  have v2 : (s.basis B' ^^ s.basis A' ^^
      carryBit (s.basis A) (s.basis B)
        (carryBit (s.basis a) (s.basis b) (s.basis c))) = false := by
    simpa [Bool.xor_comm] using r2
  have v3 : sumBit (s.basis A) (s.basis B)
      (carryBit (s.basis a) (s.basis b) (s.basis c)) = false := r1
  rw [old4_run a b c A B A' B' A'' B'' z z' z'' nd s m cz cz' cz'',
      new4_run a b c A B A' B' A'' B'' nd9 s n ⟨r1,r2,r3⟩]
  simp only [post4]
  rw [v1]
  rw [v2]
  rw [v3]
  rw [drop_scratch s.basis z'' B'' (Ne.symm hB''z'') cz'']

#print axioms full_state4

/-! ### Wrapper: substitution inside a surrounding program. -/

/-- The three high output bits of the whole program determine `Ready4` at the leaf boundary. -/
theorem prefix_leaf4_high (P R : Program) (a b c A B A' B' A'' B'' z z' z'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B'',z,z',z''].Nodup) (s : State) (m : List Bool)
    (cz : s.basis z=false) (cz' : s.basis z'=false) (cz'' : s.basis z''=false)
    (hzP : z∉wires P) (hz'P : z'∉wires P) (hz''P : z''∉wires P)
    (hBR : B∉wires R) (hB'R : B'∉wires R) (hB''R : B''∉wires R)
    (topB   : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B = false)
    (topB'  : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B' = false)
    (topB'' : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B'' = false) :
    Ready4 a b c A B A' B' A'' B'' (run P m s).basis := by
  have nd' := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd'
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB'',haz,haz',haz''⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB'',hbz,hbz',hbz''⟩,
          ⟨hcA,hcB,hcA',hcB',hcA'',hcB'',hcz,hcz',hcz''⟩,
          ⟨hAB,hAA',hAB',hAA'',hAB'',hAz,hAz',hAz''⟩,
          ⟨hBA',hBB',hBA'',hBB'',hBz,hBz',hBz''⟩,
          ⟨hA'B',hA'A'',hA'B'',hA'z,hA'z',hA'z''⟩,
          ⟨hB'A'',hB'B'',hB'z,hB'z',hB'z''⟩,
          ⟨hA''B'',hA''z,hA''z',hA''z''⟩,
          ⟨hB''z,hB''z',hB''z''⟩,
          ⟨hzz',hzz''⟩,
          hz'z''⟩ := nd'
  have tz   : (run P [] s).basis z   = false := (run_preserves_outside P [] s z hzP).trans cz
  have tz'  : (run P [] s).basis z'  = false := (run_preserves_outside P [] s z' hz'P).trans cz'
  have tz'' : (run P [] s).basis z'' = false := (run_preserves_outside P [] s z'' hz''P).trans cz''
  have hB0 : (run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') []
      (run P [] s)).basis B = false := by
    have h := topB
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B hBR] at h
    exact h
  have hB'0 : (run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') []
      (run P [] s)).basis B' = false := by
    have h := topB'
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B' hB'R] at h
    exact h
  have hB''0 : (run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') []
      (run P [] s)).basis B'' = false := by
    have h := topB''
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B'' hB''R] at h
    exact h
  rw [old4_run a b c A B A' B' A'' B'' z z' z'' nd (run P [] s) [] tz tz' tz''] at hB0 hB'0 hB''0
  simp only [writeBit, Function.update] at hB0 hB'0 hB''0
  simp only [hbB, hBz'', hBB', hBB'', hbB', hbB'', hB'z'', hB''z'', hB'B'',
    eq_self_iff_true, if_true, if_false,
    Ne.symm hbB, Ne.symm hBz'', Ne.symm hBB', Ne.symm hBB'', Ne.symm hbB',
    Ne.symm hbB'', Ne.symm hB'z'', Ne.symm hB''z'', Ne.symm hB'B''] at hB0 hB'0 hB''0
  have pb : (run P m s).basis = (run P [] s).basis := run_basis_records P s s m [] rfl
  refine ⟨?_,?_,?_⟩
  · rw [pb]
    simpa only [sumBit] using hB0
  · rw [pb]; rw [Bool.xor_comm ((run P [] s).basis A') ((run P [] s).basis B')]; exact hB'0
  · rw [pb]; rw [Bool.xor_comm ((run P [] s).basis A'') ((run P [] s).basis B'')]; exact hB''0

/-- Whole-program zero-top replacement for the FOUR-bit leaf: three Toffolis removed. -/
theorem whole_zero4 (P R : Program) (a b c A B A' B' A'' B'' z z' z'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B'',z,z',z''].Nodup) (s : State) (m : List Bool)
    (cz : s.basis z=false) (cz' : s.basis z'=false) (cz'' : s.basis z''=false)
    (hzP : z∉wires P) (hz'P : z'∉wires P) (hz''P : z''∉wires P)
    (hBR : B∉wires R) (hB'R : B'∉wires R) (hB''R : B''∉wires R)
    (topB   : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B = false)
    (topB'  : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B' = false)
    (topB'' : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B'' = false) :
    run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) m s
      = run (P++newLeaf4At a b c A B A' B' A'' B''++R) m s := by
  have tz   : (run P m s).basis z   = false := (run_preserves_outside P m s z hzP).trans cz
  have tz'  : (run P m s).basis z'  = false := (run_preserves_outside P m s z' hz'P).trans cz'
  have tz'' : (run P m s).basis z'' = false := (run_preserves_outside P m s z'' hz''P).trans cz''
  have ready := prefix_leaf4_high P R a b c A B A' B' A'' B'' z z' z'' nd s m
    cz cz' cz'' hzP hz'P hz''P hBR hB'R hB''R topB topB' topB''
  have eqn := full_state4 a b c A B A' B' A'' B'' z z' z'' nd (run P m s)
    (m.drop (measurementCount P)) (m.drop (measurementCount P)) tz tz' tz'' ready
  simpa only [run_cat, measurementCount_append,
    (old4_counts a b c A B A' B' A'' B'' z z' z'').2, (new4_counts a b c A B A' B' A'' B'').2,
    List.drop_drop, Nat.add_comm] using
    congrArg (run R ((m.drop (measurementCount P)).drop 3)) eqn

#print axioms prefix_leaf4_high
#print axioms whole_zero4

/-! ### Instantiation at the KAdd indices -/
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

/-- Mirror of `add_split`, peeling FOUR bits. -/
theorem add_split4 (xs ys cs : List Wire) (cin a A A' A'' b B B' B'' z z' z'' : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    addInPlace (xs++[a,A,A',A'']) (ys++[b,B,B',B'']) (cs++[z,z',z'']) cin=
      adderPrefix xs ys cs cin
        ++ oldLeaf4At a b (lastCarry cs cin) A B A' B' A'' B'' z z' z''
        ++ adderSuffix xs ys cs cin := by
  induction xs generalizing ys cs cin with
  | nil =>
    have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
    have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
    subst ys; subst cs; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have hy' : xs.length=ys.length := by simpa using hy
        have hc' : xs.length=cs.length := by simpa using hc
        have step : addInPlace ((x::xs)++[a,A,A',A'']) ((y::ys)++[b,B,B',B''])
            ((c::cs)++[z,z',z'']) cin=
            majority x y cin c++addInPlace (xs++[a,A,A',A'']) (ys++[b,B,B',B'']) (cs++[z,z',z'']) c++
              eraseCarry x y cin c++[.CX x y,.CX cin y] := by
          cases xs <;> cases ys <;> rfl
        rw [step,ih ys cs c hy' hc']
        simp only [adderPrefix,adderSuffix,lastCarry,List.append_assoc]

def P4 (w : Nat→Wire) : Program :=
  adderPrefix (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)
def R4 (w : Nat→Wire) : Program :=
  adderSuffix (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)

private theorem lastCarry_cat4 (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs ++ ys) cin = lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append,lastCarry] using ih x

theorem literal_split4 (w : Nat→Wire) :
    literalKAdd w = P4 w
      ++ oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
           (w 257) (w 1027) (w 1794) (w 1795) (w 1796)
      ++ R4 w := by
  have hx : wireBlock w 0 258=wireBlock w 0 254++[w 254,w 255,w 256,w 257] := by
    rw [←wireBlock_append w 0 254 4]; rfl
  have hy : wireBlock w 770 258=wireBlock w 770 254++[w 1024,w 1025,w 1026,w 1027] := by
    rw [←wireBlock_append w 770 254 4]; rfl
  have hc : wireBlock w 1540 257=wireBlock w 1540 254++[w 1794,w 1795,w 1796] := by
    rw [←wireBlock_append w 1540 254 3]; rfl
  have lastBlock : wireBlock w 1540 254 = wireBlock w 1540 253 ++ [w 1793] := by
    rw [←wireBlock_append w 1540 253 1]; rfl
  have last : lastCarry (wireBlock w 1540 254) (w 1797)=w 1793 := by
    rw [lastBlock,lastCarry_cat4]; rfl
  rw [literalKAdd,read_add,hx,hy,hc]
  simpa only [P4,R4,last] using add_split4
    (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254)
    (w 1797) (w 254) (w 255) (w 256) (w 257) (w 1024) (w 1025) (w 1026) (w 1027)
    (w 1794) (w 1795) (w 1796)
    (by simp [wireBlock_length]) (by simp [wireBlock_length])

def zero4KAdd (w : Nat→Wire) : Program :=
  P4 w ++ newLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027)
    ++ R4 w

/-- Counts: the four-bit zero replacement costs 254 Toffolis, three fewer than the literal. -/
theorem zero4_counts (w : Nat→Wire)
    (hlit : toffoliCount (literalKAdd w)=257 ∧ measurementCount (literalKAdd w)=257) :
    toffoliCount (zero4KAdd w)=254 ∧ measurementCount (zero4KAdd w)=257 := by
  have hs := literal_split4 w
  have ho := old4_counts (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
    (w 257) (w 1027) (w 1794) (w 1795) (w 1796)
  have hn := new4_counts (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027)
  rw [hs] at hlit
  simp only [toffoliCount_append, measurementCount_append, ho.1, ho.2] at hlit
  simp only [zero4KAdd, toffoliCount_append, measurementCount_append, hn.1, hn.2]
  omega

#print axioms zero4_counts

/-! ### Side conditions for `whole_zero4` at the KAdd indices -/

theorem low_avoid4 (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) :
    w i ∉ spinePorts (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797) := by
  intro h
  simp only [spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e:=hinj h; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega

attribute [local irreducible] ECDSAAdd.wires in
theorem P4_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) : w i∉wires (P4 w) := by
  intro h
  exact low_avoid4 w hinj i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section R4SupportOpaque
attribute [local irreducible] ECDSAAdd.wires
theorem R4_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) : w i∉wires (R4 w) := by
  intro h
  have support := suffix_support (wireBlock w 0 254) (wireBlock w 770 254)
    (wireBlock w 1540 254) (w 1797)
  exact low_avoid4 w hinj i hi (List.mem_toFinset.mp (support h))
end R4SupportOpaque

theorem tail4_nd (w : Nat→Wire) (hinj : Function.Injective w) :
    [w 254,w 1024,w 1793,w 255,w 1025,w 256,w 1026,w 257,w 1027,w 1794,w 1795,w 1796].Nodup :=
  List.Nodup.map hinj
    (by decide : [254,1024,1793,255,1025,256,1026,257,1027,1794,1795,1796].Nodup)

#print axioms P4_avoid
#print axioms R4_avoid
#print axioms tail4_nd

/-! ### Extracting the three zero output bits from the word value -/

theorem bit255_from_div (w : Nat→Wire) (s : BasisState) (W : Nat) (flag : Bool)
    (postWord : regValue (wireBlock w 770 258) s=W) (hdiv : W/2^255%2=flag.toNat) :
    s (w 1025)=flag := by
  have h:=regValue_bit (wireBlock w 770 258) 255 0 s (by simp [wireBlock_length])
  have port : (wireBlock w 770 258).getD 255 0=w 1025 := by rfl
  rw [port,postWord,hdiv] at h
  cases hs : s (w 1025) <;> cases flag <;> simp [hs] at h ⊢

/-- For the exit caller the word is `Y/2 < 2^255`, so ALL THREE high bits vanish. -/
theorem exit_three_zero (w : Nat→Wire) (s : BasisState) (W : Nat) (hW : W<2^255)
    (postWord : regValue (wireBlock w 770 258) s=W) :
    s (w 1025)=false ∧ s (w 1026)=false ∧ s (w 1027)=false := by
  have d5 : W/2^255=0 := Nat.div_eq_of_lt hW
  have h255 : W/2^255%2=(false : Bool).toNat := by rw [d5]; rfl
  exact ⟨bit255_from_div w s W false postWord h255,
    (Verifier.Leaf3.exit_two_zero w s W hW postWord).1,
    (Verifier.Leaf3.exit_two_zero w s W hW postWord).2⟩

#print axioms bit255_from_div
#print axioms exit_three_zero

end Verifier.Leaf4
end


-- Consolidated source module: AffineCarry4B
section

set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 400

namespace Verifier.Leaf4
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

section Exit4Opaque
attribute [local irreducible] ECDSAAdd.wires
set_option maxHeartbeats 16000000 in
theorem exit4_run_eq_split (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean4 : s.basis (w 1794)=false) (clean5 : s.basis (w 1795)=false)
    (clean6 : s.basis (w 1796)=false)
    (topB   : (run (P4 w++oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
                (w 257) (w 1027) (w 1794) (w 1795) (w 1796)++R4 w) [] s).basis (w 1025)=false)
    (topB'  : (run (P4 w++oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
                (w 257) (w 1027) (w 1794) (w 1795) (w 1796)++R4 w) [] s).basis (w 1026)=false)
    (topB'' : (run (P4 w++oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
                (w 257) (w 1027) (w 1794) (w 1795) (w 1796)++R4 w) [] s).basis (w 1027)=false) :
    run (P4 w++oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
          (w 257) (w 1027) (w 1794) (w 1795) (w 1796)++R4 w) m s
      = run (P4 w++newLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
          (w 257) (w 1027)++R4 w) m s := by
  exact whole_zero4 (P4 w) (R4 w) (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
    (w 257) (w 1027) (w 1794) (w 1795) (w 1796) (tail4_nd w hinj) s m clean4 clean5 clean6
    (P4_avoid w hinj 1794 (Or.inl rfl))
    (P4_avoid w hinj 1795 (Or.inr (Or.inl rfl)))
    (P4_avoid w hinj 1796 (Or.inr (Or.inr (Or.inl rfl))))
    (R4_avoid w hinj 1025 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (R4_avoid w hinj 1026 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (R4_avoid w hinj 1027 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    topB topB' topB''
end Exit4Opaque

/-- Same bridge, stated on the literal adder. The module boundary keeps `P4`/`R4` opaque. -/
theorem exit4_run_eq (w : Nat→Wire) (hinj : Function.Injective w) (s : State) (m : List Bool)
    (clean4 : s.basis (w 1794)=false) (clean5 : s.basis (w 1795)=false)
    (clean6 : s.basis (w 1796)=false)
    (topB   : (run (literalKAdd w) [] s).basis (w 1025)=false)
    (topB'  : (run (literalKAdd w) [] s).basis (w 1026)=false)
    (topB'' : (run (literalKAdd w) [] s).basis (w 1027)=false) :
    run (literalKAdd w) m s=run (zero4KAdd w) m s := by
  rw [literal_split4] at topB topB' topB''
  rw [literal_split4, zero4KAdd]
  exact exit4_run_eq_split w hinj s m clean4 clean5 clean6 topB topB' topB''

#print axioms exit4_run_eq
end Verifier.Leaf4
end


-- Consolidated source module: AffineCarry4C
section

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
end


-- Consolidated source module: ExitMerge
section

-- ===== ECDSAAdd.Submission.Entrant.E1Merge =====
section
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectValues
-- consolidated import: import ECDSAAdd.Arithmetic.Compare
-- consolidated import: import ECDSAAdd.Arithmetic.ComparePhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MaskedConstant
-- consolidated import: import ECDSAAdd.Arithmetic.MappedSources
-- consolidated import: import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.Copy
-- consolidated import: import ECDSAAdd.Arithmetic.Rotate
-- consolidated import: import ECDSAAdd.Arithmetic.Reduction
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredGateSupport
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
-- consolidated import: import ECDSAAdd.Baselines.SlotAlgebra
-- consolidated import: import ECDSAAdd.Baselines.SlotMapped
-- consolidated import: import ECDSAAdd.Baselines.SlotNativeFirst

set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1Merge
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum

/-! ### Arithmetic of the merged first tick -/

theorem p_val : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [ECDSAAdd.p]

/-- bit 0 of the selected constant `g·k − f·p`. -/
def ksel0 (k : Nat) (G f : Bool) : Bool := (G && decide (k%2=1)) ^^ f
/-- low bit of the input implied by `(g,f,par)`. -/
def x0 (k : Nat) (G f par : Bool) : Bool := par ^^ ksel0 k G f

/-- Constant added to `x>>1` to obtain the first-tick `K` word directly. -/
def tk (k : Nat) (G f par : Bool) : Nat :=
  if f then (if G then (kConstant false par+2^258-(p+par.toNat-(x0 k G f par).toNat-k)/2)%2^258 else 0)
  else if G then (kConstant false par+((x0 k G f par).toNat+k-par.toNat)/2)%2^258
  else kConstant false par

def delta (par : Bool) : Nat := if par then p else 2^257-p

def thr (k : Nat) (G par : Bool) : Nat := if G then (if par then (k+p+1)/2 else (k+1)/2) else 0

theorem hC_val : hConstant = 57896044618658097711785492504343953926634992332820282019728792003954417335832 := by
  norm_num [hConstant, ECDSAAdd.p]
theorem kC_val (par : Bool) : kConstant false par =
    if par then 405272312330606683982498447530407677486444946329741974138101544027698101223913
    else 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  cases par <;> norm_num [kConstant, ECDSAAdd.p]


theorem arith (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    decide (X%2=1)=x0 k G f par ∧
    (X/2+tk k G f par)%2^258=K ∧
    H=dx/2+(if par then hConstant else 0) ∧
    f=decide (H<thr k G par) ∧
    tk k G f par<2^258 := by
  intro f dx par K H
  rw [p_val] at hk hX
  simp only [f,dx,par,K,H,tk,delta,thr,x0,ksel0,kC_val,hC_val,p_val,Nat.reducePow]
  clear H K par dx f
  cases G
  · have e1 : (X+0)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X := Nat.mod_eq_of_lt (by omega)
    have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-0<X)=false := by
      simp only [decide_eq_false_iff_not]; omega
    simp only [if_false,Bool.false_eq_true,e1,e2,Bool.false_and,Bool.false_xor,Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one X with h|h <;>
    simp only [h,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
      Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true] <;>
    exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
  · simp only [if_true,Bool.true_and]
    by_cases hf : 115792089237316195423570985008687907853269984665640564039457584007908834671663≤X+k
    · have e1 : (X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X+k-115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
        rw [Nat.mod_eq_sub_mod hf,Nat.mod_eq_of_lt (by omega)]
      have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-(115792089237316195423570985008687907853269984665640564039457584007913129639936-115792089237316195423570985008687907853269984665640564039457584007908834671663+k)<X)=true := by
        simp only [decide_eq_true_iff]; omega
      simp only [e1,e2,Bool.xor_true]
      clear e1 e2
      rcases Nat.mod_two_eq_zero_or_one (X+k-115792089237316195423570985008687907853269984665640564039457584007908834671663) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
    · have e1 : (X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X+k := Nat.mod_eq_of_lt (by omega)
      have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-(115792089237316195423570985008687907853269984665640564039457584007913129639936-115792089237316195423570985008687907853269984665640564039457584007908834671663+k)<X)=false := by
        simp only [decide_eq_false_iff_not]; omega
      simp only [e1,e2,Bool.xor_false]
      clear e1 e2
      rcases Nat.mod_two_eq_zero_or_one (X+k) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩

/-! ### Circuit -/

def cmpC : Nat := 2^256-p

def srcR (w : Nat → Wire) : List Wire := wireBlock w 0 256
def xR (w : Nat → Wire) : List Wire := wireBlock w 770 256
def cR (w : Nat → Wire) : List Wire := wireBlock w 256 256
def hR (w : Nat → Wire) : List Wire := wireBlock w 0 258
def kR (w : Nat → Wire) : List Wire := wireBlock w 770 258
def tR (w : Nat → Wire) : List Wire := wireBlock w 1029 256
def hpR (w : Nat → Wire) : List Wire := wireBlock w 1 257
def aC (w : Nat → Wire) : List Wire := wireBlock w 1540 257
def hC2 (w : Nat → Wire) : List Wire := wireBlock w 1540 256
def hp8 (w : Nat → Wire) : List Wire := wireBlock w 1 256
def hC3 (w : Nat → Wire) : List Wire := wireBlock w 1540 255

def comparePart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (srcR w) (cmpC+k)++notRegister (srcR w)++
  compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)++
  notRegister (srcR w)++maskedConstant g (srcR w) (cmpC+k)

def parGates (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]++
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]

def prodPart (w : Nat → Wire) (g : Wire) : Program :=
  [.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)]

def c1 (k : Nat) : Nat := tk k false false false
def cg (k : Nat) : Nat := tk k true false false ^^^ tk k false false false
def cf (k : Nat) : Nat := tk k true true false ^^^ tk k true false false
def cp (k : Nat) : Nat := tk k false false true ^^^ tk k false false false
def cgp (k : Nat) : Nat :=
  tk k true false true ^^^ tk k true false false ^^^ tk k false false true ^^^ tk k false false false
def cfp (k : Nat) : Nat :=
  tk k true true true ^^^ tk k true true false ^^^ tk k true false true ^^^ tk k true false false

def loadK (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1 k)++maskedConstant g (hR w) (cg k)++maskedConstant (w 514) (hR w) (cf k)++
  maskedConstant (w 1028) (hR w) (cp k)++maskedConstant (w 721) (hR w) (cgp k)++
  maskedConstant (w 722) (hR w) (cfp k)

def kAddM (w : Nat → Wire) : Program := mappedAdd (mappedRead (hR w) false) (kR w) (aC w) (w 1797)

def dBits (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := (2^257-p).testBit j
  let b := p.testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def hAddM (w : Nat → Wire) : Program := mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)

/-- `hAddM` with its first carry trimmed. The first mapped bit is the literal `1`
(`2^257-p` and `p` are both odd) and the carry-in `w 1797` is clean, so the first
majority's Toffoli `CCX (w 1) (w 1797) (w 1540)` never fires; it is dropped. -/
def hPost (w : Nat → Wire) : Program :=
  mappedAdd (dBits w).tail (hpR w).tail (hC2 w).tail (w 1540) ++
    mappedEraseCarry {wire:=none,flip:=true} (w 1) (w 1797) (w 1540) ++
    mappedSum {wire:=none,flip:=true} (w 1) (w 1797)

def hAddT1 (w : Nat → Wire) : Program := [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ hPost w

/-- `hAddT1` with its last carry trimmed as well (see `MappedTopZero`). -/
def hAddT (w : Nat → Wire) : Program := MappedTopZero.topT (dBits w) w (w 1028)


def thrA (k : Nat) : Nat := (k+1)/2
def thrB (k : Nat) : Nat := (k+1)/2 ^^^ (k+p+1)/2

def loadT (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrA k)++maskedConstant (w 721) (tR w) (thrB k)

/-- Compare-first constant addition `x ↦ x + g·k mod p` merged into the direct first tick. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w))++prodPart w g++loadK w g k++KAddCallerBridgeResearch.flagKAdd w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-! ### Layout facts -/

section Layout
variable (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
include hn

theorem mem_blk (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) :
    w i ∈ wireBlock w a n ↔ a ≤ i ∧ i < a + n := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := skywalkPool_index_inj w hn i j hi (by omega) he.symm
    omega
  · intro h
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem w_ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
  index_ne w hn i j hi hj h

omit hn in
theorem blk_sub (a n b m : Nat) (h1 : b≤a) (h2 : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem blk_nd (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := block_nodup w hn a n ha

theorem blk_dis (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798) (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := block_disjoint w hn a n b m ha hb sep

theorem g_out (g : Wire) (hg : g∉skywalkPoolWires w) (a n : Nat) (ha : a+n≤1798) : g∉wireBlock w a n :=
  fun h => hg (blk_sub w a n 0 1798 (by omega) (by omega) g h)

theorem g_ne (g : Wire) (hg : g∉skywalkPoolWires w) (i : Nat) (hi : i<1798) : g≠w i := by
  intro e; apply hg; rw [e]
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

end Layout


/-! ### Frame -/

def mutL (w : Nat → Wire) : List Wire := hR w++kR w++tR w++[w 1028,w 514,w 721,w 722]

def MF (w : Nat → Wire) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState) : Prop :=
  regValue (hR w) s=H ∧ regValue (kR w) s=X ∧ regValue (tR w) s=T ∧
  s (w 1028)=par ∧ s (w 514)=f ∧ s (w 721)=gp ∧ s (w 722)=fp ∧ ∀q,q∉mutL w → s q=b0 q

theorem keep (R : List Wire) (s t : BasisState) (hf : ∀q,q∉R → t q=s q) (C : List Wire)
    (hC : ∀q∈C,q∉R) : regValue C t=regValue C s :=
  regValue_congr C t s (fun q hq => hf q (hC q hq))

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem hR_nd : (hR w).Nodup := blk_nd w hn 0 258 (by omega)
theorem kR_nd : (kR w).Nodup := blk_nd w hn 770 258 (by omega)
theorem tR_nd : (tR w).Nodup := blk_nd w hn 1029 256 (by omega)

theorem hR_kR : ∀q∈kR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 770 258 (by omega) (by omega) (by omega)) h hq
theorem hR_tR : ∀q∈tR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem kR_hR : ∀q∈hR w,q∉kR w := fun q hq h => hR_kR w hn q h hq
theorem kR_tR : ∀q∈tR w,q∉kR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 770 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem tR_hR : ∀q∈hR w,q∉tR w := fun q hq h => hR_tR w hn q h hq
theorem tR_kR : ∀q∈kR w,q∉tR w := fun q hq h => kR_tR w hn q h hq

theorem nb (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n :=
  block_not_mem w hn i a n hi ha sep

theorem out_of_mut (R : List Wire) (hR' : ∀q∈R,q∈mutL w) (q : Wire) (hq : q∉mutL w) : q∉R :=
  fun h => hq (hR' q h)

theorem hR_mut : ∀q∈hR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem kR_mut : ∀q∈kR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem tR_mut : ∀q∈tR w,q∈mutL w := fun q hq => by simp [mutL,hq]

/-- An operation that changes only the `H` block. -/
theorem stepH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉hR w → t.basis q=s.basis q) (H' : Nat)
    (hv : regValue (hR w) t.basis=H') : MF w b0 H' X T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨hv,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (hR_kR w hn)]; exact h2
  · rw [keep _ _ _ hf _ (hR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 0 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 0 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 0 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 0 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (hR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the `K` block. -/
theorem stepK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉kR w → t.basis q=s.basis q) (X' : Nat)
    (hv : regValue (kR w) t.basis=X') : MF w b0 H X' T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,hv,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (kR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (kR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 770 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 770 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 770 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (kR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the threshold block. -/
theorem stepT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉tR w → t.basis q=s.basis q) (T' : Nat)
    (hv : regValue (tR w) t.basis=T') : MF w b0 H X T' par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (tR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (tR_kR w hn)]; exact h2
  · rw [hf _ (nb w hn 1028 1029 256 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 1029 256 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 1029 256 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 1029 256 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (tR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes one scalar wire `w j` of the frame. -/
theorem stepBit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State) (j : Nat)
    (hj : j=1028 ∨ j=514 ∨ j=721 ∨ j=722)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q≠w j → t.basis q=s.basis q) :
    MF w b0 H X T (if j=1028 then t.basis (w j) else par) (if j=514 then t.basis (w j) else f)
      (if j=721 then t.basis (w j) else gp) (if j=722 then t.basis (w j) else fp) t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have hjr : j<1798 := by omega
  have nh : w j∉hR w := nb w hn j 0 258 hjr (by omega) (by omega)
  have nk : w j∉kR w := nb w hn j 770 258 hjr (by omega) (by omega)
  have nt : w j∉tR w := nb w hn j 1029 256 hjr (by omega) (by omega)
  have ne (i : Nat) (hi : i<1798) (hij : i≠j) : w i≠w j := w_ne w hn i j hi hjr hij
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nh (e ▸ hq)))]; exact h1
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nk (e ▸ hq)))]; exact h2
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nt (e ▸ hq)))]; exact h3
  · by_cases e : j=1028
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 1028 (by omega) (Ne.symm e))]; exact h4
  · by_cases e : j=514
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 514 (by omega) (Ne.symm e))]; exact h5
  · by_cases e : j=721
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 721 (by omega) (Ne.symm e))]; exact h6
  · by_cases e : j=722
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 722 (by omega) (Ne.symm e))]; exact h7
  · intro q hq
    have : q≠w j := by
      intro e; apply hq; rw [e]
      rcases hj with rfl|rfl|rfl|rfl <;> simp [mutL]
    rw [hf q this]; exact h8 q hq

end Steps


/-! ### Concrete steps -/

theorem run_cx (a b : Wire) (m : List Bool) (s : State) :
    run [.CX a b] m s=⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis a)⟩ := rfl
theorem run_ccx (a b c : Wire) (m : List Bool) (s : State) :
    run [.CCX a b c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ (s.basis a && s.basis b))⟩ := rfl
theorem run_x (a : Wire) (m : List Bool) (s : State) :
    run [.X a] m s=⟨s.phase,writeBit s.basis a (!s.basis a)⟩ := rfl

theorem run_meas_and (t a b : Wire) (m : List Bool) (s : State) (ha : a≠t) (hb : b≠t)
    (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases m.headD false <;> simp [correct,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,ht]

section Concrete
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem kR_split (s : BasisState) :
    regValue (kR w) s=(s (w 770)).toNat+2*regValue (wireBlock w 771 257) s := by
  have e : kR w=w 770::wireBlock w 771 257 := by
    simp [kR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 770) <;> simp [regValue,h]

theorem hR_split (s : BasisState) :
    regValue (hR w) s=(s (w 0)).toNat+2*regValue (hpR w) s := by
  have e : hR w=w 0::hpR w := by
    simp [hR,hpR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 0) <;> simp [regValue,h]

theorem hR_src (s : BasisState) :
    regValue (hR w) s=regValue (srcR w) s+2^256*regValue (wireBlock w 256 2) s := by
  have e : hR w=srcR w++wireBlock w 256 2 := by
    rw [hR,srcR,wireBlock_append]
  rw [e,regValue_append,srcR,wireBlock_length]

theorem kR_x (s : BasisState) :
    regValue (kR w) s=regValue (xR w) s+2^256*regValue (wireBlock w 1026 2) s := by
  have e : kR w=xR w++wireBlock w 1026 2 := by
    rw [kR,xR,wireBlock_append]
  rw [e,regValue_append,xR,wireBlock_length]

theorem kR_low (s : BasisState) :
    regValue (kR w) s=regValue (wireBlock w 770 257) s+2^257*regValue (wireBlock w 1027 1) s := by
  have e : kR w=wireBlock w 770 257++wireBlock w 1027 1 := by
    rw [kR,wireBlock_append]
  rw [e,regValue_append,wireBlock_length]

/-- A CX targeting the parity wire. -/
theorem stepParCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 1028) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 1028)] (MF w b0 H X T (par ^^ cv) f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 1028)
    (s.basis (w 1028) ^^ s.basis c)⟩ 1028 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.1,hcv s.basis h] using this

/-- A CX targeting bit 0 of the K block. -/
theorem stepLowCX (b0 : BasisState) (H Y T : Nat) (b par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 770) (hcv : ∀s : BasisState,MF w b0 H (2*Y+b.toNat) T par f gp fp s → s c=cv) :
    Triple (MF w b0 H (2*Y+b.toNat) T par f gp fp) [.CX c (w 770)]
      (MF w b0 H (2*Y+(b ^^ cv).toNat) T par f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have m770 : w 770∈kR w := (mem_blk w hn 770 770 258 (by omega) (by omega)).mpr (by omega)
  have rest : ∀q∈wireBlock w 771 257,q≠w 770 := fun q hq e =>
    nb w hn 770 771 257 (by omega) (by omega) (by omega) (e ▸ hq)
  apply stepK w hn b0 H _ T par f gp fp s _ h
  · intro q hq; have : q≠w 770 := fun e => hq (e ▸ m770)
    simp [writeBit,Function.update_of_ne this]
  · have sp := kR_split w hn s.basis
    have sp2 := kR_split w hn (writeBit s.basis (w 770) (s.basis (w 770) ^^ s.basis c))
    rw [h.2.1] at sp
    rw [sp2,regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,Function.update_of_ne (rest q hq)])]
    rw [hcv s.basis h]
    simp only [writeBit,Function.update_self]
    cases hb : s.basis (w 770) <;> cases b <;> cases cv <;> simp [hb] at sp ⊢ <;> omega

end Concrete


section Concrete2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepXorH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (xorConstant (hR w) v) (MF w b0 (H^^^v) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := xorConstant_correct (hR w) (hR_nd w hn) v (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1])⟩

theorem stepMaskH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉hR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (hR w) v)
      (MF w b0 (H^^^(if cv then v else 0)) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (hR w) v (hR_nd w hn) hc
    (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1,hcv s.basis h])⟩

theorem stepMaskT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉tR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^256) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (tR w) v)
      (MF w b0 H X (T^^^(if cv then v else 0)) par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (tR w) v (tR_nd w hn) hc
    (by simpa [tR,wireBlock_length] using hv) s m
  exact ⟨hp,stepT w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.2.2.1,hcv s.basis h])⟩

theorem stepCCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (a b : Wire) (j : Nat)
    (hj : j=721 ∨ j=722) (av bv : Bool) (ha : a≠w j) (hb : b≠w j)
    (hav : ∀s : BasisState,MF w b0 H X T par f gp fp s → s a=av)
    (hbv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s b=bv) :
    Triple (MF w b0 H X T par f gp fp) [.CCX a b (w j)]
      (MF w b0 H X T par f (if j=721 then gp ^^ (av && bv) else gp)
        (if j=722 then fp ^^ (av && bv) else fp)) := by
  intro s m h
  rw [run_ccx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w j)
    (s.basis (w j) ^^ (s.basis a && s.basis b))⟩ j (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  rcases hj with rfl|rfl
  · simpa [writeBit,h.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this
  · simpa [writeBit,h.2.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this

theorem stepKAdd (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 H X T par f gp fp) (kAddM w) (MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m h
  have caway : ∀q∈aC w,q∉mutL w := by
    intro q hq hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
    · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
    all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm
  have m1797 : w 1797∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have nd : (w 1797::(kR w++aC w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),
      blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
  have src : ∀q∈mappedWires (mappedRead (hR w) false),q∉w 1797::(kR w++aC w) := by
    rw [mappedRead_wires]
    intro q hq hm
    simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with e|e|e
    · exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq)
    · exact hR_kR w hn q e hq
    · exact List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq e
  have cl : ∀q∈aC w,s.basis q=false := fun q hq => (h.2.2.2.2.2.2.2 q (caway q hq)).trans (hc q hq)
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (mappedRead (hR w) false) (kR w) (aC w) (w 1797) nd src
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length]) s m cl
  refine ⟨hp,stepK w hn b0 H X T par f gp fp s _ h he _ ?_⟩
  rw [hval,mappedRead_value,h.1,h.2.1,(h.2.2.2.2.2.2.2 _ m1797).trans hcin]
  simp [kR,wireBlock_length]

end Concrete2


/-! Checked actual-MF flag/zero step wrappers, migrated without an import cycle. -/

theorem kAdd_literal (w : Nat → Wire) : E1Merge.kAddM w = KAddCallerBridgeResearch.literalKAdd w := rfl

/-- Derive the actual carry cleanliness from the real MF frame and original carry-bank premise. -/
theorem carry_clean (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (s : BasisState)
    (hs : E1Merge.MF w b0 H X T par f gp fp s) : s (w 1796)=false := by
  have away : w 1796∉E1Merge.mutL w := by
    simp only [E1Merge.mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨E1Merge.nb w hn 1796 0 258 (by omega) (by omega) (by omega),
      E1Merge.nb w hn 1796 770 258 (by omega) (by omega) (by omega)⟩,
      E1Merge.nb w hn 1796 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact E1Merge.w_ne w hn _ _ (by omega) (by omega) (by omega)
  have member : w 1796∈E1Merge.aC w := by
    apply List.mem_map.mpr
    refine ⟨1796,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  exact (hs.2.2.2.2.2.2.2 _ away).trans (hc _ member)

theorem carry_clean5 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (s : BasisState)
    (hs : E1Merge.MF w b0 H X T par f gp fp s) : s (w 1795)=false := by
  have away : w 1795∉E1Merge.mutL w := by
    simp only [E1Merge.mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨E1Merge.nb w hn 1795 0 258 (by omega) (by omega) (by omega),
      E1Merge.nb w hn 1795 770 258 (by omega) (by omega) (by omega)⟩,
      E1Merge.nb w hn 1795 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact E1Merge.w_ne w hn _ _ (by omega) (by omega) (by omega)
  have member : w 1795∈E1Merge.aC w := by
    apply List.mem_map.mpr
    refine ⟨1795,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  exact (hs.2.2.2.2.2.2.2 _ away).trans (hc _ member)

theorem carry_clean4 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (s : BasisState)
    (hs : E1Merge.MF w b0 H X T par f gp fp s) : s (w 1794)=false := by
  have away : w 1794∉E1Merge.mutL w := by
    simp only [E1Merge.mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨E1Merge.nb w hn 1794 0 258 (by omega) (by omega) (by omega),
      E1Merge.nb w hn 1794 770 258 (by omega) (by omega) (by omega)⟩,
      E1Merge.nb w hn 1794 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact E1Merge.w_ne w hn _ _ (by omega) (by omega) (by omega)
  have member : w 1794∈E1Merge.aC w := by
    apply List.mem_map.mpr
    refine ⟨1794,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  exact (hs.2.2.2.2.2.2.2 _ away).trans (hc _ member)


/-- Actual-MF flag substitution: postWord comes from the original stepKAdd at the empty record. -/
theorem stepKAddFlag (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (D : Nat) (hD : D<ECDSAAdd.p) (hp : par=decide (D%2=1))
    (hWord : (H+X)%2^258=E1CallerValueFactsResearch.Kword D par) :
    Triple (E1Merge.MF w b0 H X T par f gp fp) (KAddCallerBridgeResearch.flagKAdd w)
      (E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Merge.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (KAddCallerBridgeResearch.literalKAdd w) [] s).basis =
      E1CallerValueFactsResearch.Kword D par := oldEmpty.2.2.1.trans hWord
  have clean := carry_clean w hn b0 H X T par f gp fp hc s.basis hs
  have equal := KAddCallerBridgeResearch.forward_run_eq_pool w hn s m clean D hD par hp hs.2.2.2.1 postWord
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mp (old s m hs)

/-- Actual-MF zero substitution, including the ExitMerge caller that opens E1Merge. -/
theorem stepKAddZero (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (Y : Nat) (hY : Y<ECDSAAdd.p) (hWord : (H+X)%2^258=Y/2) :
    Triple (E1Merge.MF w b0 H X T par f gp fp) (KAddCallerBridgeResearch.zeroKAdd w)
      (E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Merge.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (KAddCallerBridgeResearch.literalKAdd w) [] s).basis = Y/2 :=
    oldEmpty.2.2.1.trans hWord
  have clean := carry_clean w hn b0 H X T par f gp fp hc s.basis hs
  have equal := KAddCallerBridgeResearch.exit_run_eq_pool w hn s m clean Y hY postWord
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mp (old s m hs)



/-- Actual-MF zero substitution, including the ExitMerge caller that opens E1Merge. -/
theorem stepKAddZero3 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (Y : Nat) (hY : Y<ECDSAAdd.p) (hWord : (H+X)%2^258=Y/2) :
    Triple (E1Merge.MF w b0 H X T par f gp fp) (Verifier.Leaf3.zero3KAdd w)
      (E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Merge.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (KAddCallerBridgeResearch.literalKAdd w) [] s).basis = Y/2 :=
    oldEmpty.2.2.1.trans hWord
  have clean6 := carry_clean w hn b0 H X T par f gp fp hc s.basis hs
  have clean5 := carry_clean5 w hn b0 H X T par f gp fp hc s.basis hs
  have hlt : Y/2<2^255 := ECDSAAdd.Entrant.E1CallerValueFactsResearch.exit_half_bound Y hY
  have tops := Verifier.Leaf3.exit_two_zero w
    (run (KAddCallerBridgeResearch.literalKAdd w) [] s).basis (Y/2) hlt postWord
  have equal := Verifier.Leaf3.exit3_run_eq_pool w hn s m clean5 clean6 tops.1 tops.2
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mp (old s m hs)



theorem stepKAddZero4 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (Y : Nat) (hY : Y<ECDSAAdd.p) (hWord : (H+X)%2^258=Y/2) :
    Triple (E1Merge.MF w b0 H X T par f gp fp) (Verifier.Leaf4.zero4KAdd w)
      (E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Merge.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (KAddCallerBridgeResearch.literalKAdd w) [] s).basis = Y/2 :=
    oldEmpty.2.2.1.trans hWord
  have clean6 := carry_clean w hn b0 H X T par f gp fp hc s.basis hs
  have clean5 := carry_clean5 w hn b0 H X T par f gp fp hc s.basis hs
  have clean4 := carry_clean4 w hn b0 H X T par f gp fp hc s.basis hs
  have hlt : Y/2<2^255 := ECDSAAdd.Entrant.E1CallerValueFactsResearch.exit_half_bound Y hY
  have tops := Verifier.Leaf4.exit_three_zero w
    (run (KAddCallerBridgeResearch.literalKAdd w) [] s).basis (Y/2) hlt postWord
  have equal := Verifier.Leaf4.exit4_run_eq_pool w hn s m clean4 clean5 clean6
    tops.1 tops.2.1 tops.2.2
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mp (old s m hs)




def CF (w : Nat → Wire) (b0 : BasisState) (S : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue (srcR w) s=S ∧ s (w 514)=F ∧ ∀q,q∉srcR w → q≠w 514 → s q=b0 q

section Compare
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem src_nd : (srcR w).Nodup := blk_nd w hn 0 256 (by omega)
theorem w514_src : w 514∉srcR w := nb w hn 514 0 256 (by omega) (by omega) (by omega)

theorem cfMask (b0 : BasisState) (S : Nat) (F : Bool) (c : Wire) (hc : c∉srcR w) (hc' : c≠w 514)
    (v : Nat) (hv : v<2^256) :
    Triple (CF w b0 S F) (maskedConstant c (srcR w) v) (CF w b0 (S^^^(if b0 c then v else 0)) F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (srcR w) v (src_nd w hn) hc
    (by simpa [srcR,wireBlock_length] using hv) s m
  refine ⟨hp,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2 c hc hc']
  · rw [he _ (w514_src w hn)]; exact h.2.1
  · intro q h1 h2; rw [he q h1]; exact h.2.2 q h1 h2

theorem cfNot (b0 : BasisState) (S : Nat) (F : Bool) :
    Triple (CF w b0 S F) (notRegister (srcR w)) (CF w b0 (2^256-1-S) F) := by
  intro s m h
  rw [notRegister_correct (srcR w) (src_nd w hn)]
  refine ⟨rfl,?_,?_,?_⟩
  · change regValue (srcR w) (fun q => if q∈srcR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (srcR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.1]
    simp [srcR,wireBlock_length]
  · change (if w 514∈srcR w then !s.basis (w 514) else s.basis (w 514))=_
    simp [w514_src w hn,h.2.1]
  · intro q h1 h2
    change (if q∈srcR w then !s.basis q else s.basis q)=_
    simp [h1,h.2.2 q h1 h2]

theorem cfCmp (b0 : BasisState) (S : Nat) (F : Bool) (X : Nat) (hx : regValue (xR w) b0=X)
    (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false) :
    Triple (CF w b0 S F) (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))
      (CF w b0 S (F ^^ decide (S<X))) := by
  intro s m h
  have xs : ∀q∈xR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)) h' hq
  have x514 : ∀q∈xR w,q≠w 514 := fun q hq e => nb w hn 514 770 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have cs : ∀q∈cR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)) h' hq
  have c514 : ∀q∈cR w,q≠w 514 := fun q hq e => nb w hn 514 256 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have n513 : w 513∉srcR w := nb w hn 513 0 256 (by omega) (by omega) (by omega)
  have e513 : w 513≠w 514 := w_ne w hn 513 514 (by omega) (by omega) (by omega)
  have nd : (w 514::w 513::(srcR w++xR w++cR w)).Nodup := by
    have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
    have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (srcR w++xR w++cR w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨e513.symm,⟨w514_src w hn,nb w hn 514 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨n513,nb w hn 513 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (srcR w) (xR w) (cR w) (w 513) (w 514) nd (by simp)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length]) s m
    ((h.2.2 _ n513 e513).trans hcin) (fun q hq => (h.2.2 q (cs q hq) (c514 q hq)).trans (hc q hq))
  refine ⟨hp,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => he q (fun e => w514_src w hn (e ▸ hq)))]; exact h.1
  · rw [hv,h.2.1,h.1,regValue_congr _ _ b0 (fun q hq => h.2.2 q (xs q hq) (x514 q hq)),hx]
    simp [controlValue]
  · intro q h1 h2; rw [he q h2]; exact h.2.2 q h1 h2

theorem cfCompare (b0 : BasisState) (F : Bool) (k X : Nat) (hk : cmpC+k<2^256)
    (hx : regValue (xR w) b0=X) (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) :
    Triple (CF w b0 0 F) (comparePart w g k)
      (CF w b0 0 (F ^^ decide (2^256-1-(if b0 g then cmpC+k else 0)<X))) := by
  have t := ((((cfMask w hn b0 0 F g gs g514 (cmpC+k) hk).seq
    (cfNot w hn b0 _ F)).seq (cfCmp w hn b0 _ F X hx hc hcin)).seq
    (cfNot w hn b0 _ _)).seq (cfMask w hn b0 _ _ g gs g514 (cmpC+k) hk)
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have lt : (if b0 g then cmpC+k else 0)<2^256 := by split <;> omega
  refine ⟨?_,?_,h.2.2⟩
  · rw [h.1]
    have e : 2^256-1-(2^256-1-(0^^^(if b0 g then cmpC+k else 0)))=(if b0 g then cmpC+k else 0) := by
      simp only [Nat.zero_xor]; omega
    rw [e,Nat.xor_self]
  · rw [h.2.1]; simp only [Nat.zero_xor]

end Compare


def dScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0

theorem dScalar_value (par : Bool) : dScalar par=delta par := by
  cases par <;> decide

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem d_list_value (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (2^257-p).testBit j
      let b := p.testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem dBits_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBits w) s=delta (s (w 1028)) := by
  rw [dBits,d_list_value]
  exact dScalar_value (s (w 1028))

theorem dBits_length (w : Nat → Wire) : (dBits w).length=257 := by simp [dBits]

theorem dBits_cons (w : Nat → Wire) :
    ∃ b' bs, dBits w = {wire:=none,flip:=true} :: b' :: bs := by
  have e : List.range 257 = 0 :: 1 :: List.range' 2 255 := by
    rw [List.range_eq_range']; rfl
  have t1 : (2^257-p).testBit 0 = true := by rw [p_val]; decide
  have t2 : p.testBit 0 = true := by rw [p_val]; decide
  rw [dBits, e, List.map_cons, List.map_cons]
  simp only [t1, t2, ite_true]
  exact ⟨_, _, rfl⟩

theorem hpR_cons (w : Nat → Wire) : ∃ y' ys, hpR w = w 1 :: y' :: ys :=
  ⟨w 2, (List.range' 3 255).map w, by
    rw [hpR, wireBlock, show (257:Nat) = 255+1+1 from rfl, List.range'_succ, List.range'_succ]; rfl⟩

theorem hC2_cons (w : Nat → Wire) : ∃ cs, hC2 w = w 1540 :: cs :=
  ⟨(List.range' 1541 255).map w, by
    rw [hC2, wireBlock, show (256:Nat) = 255+1 from rfl, List.range'_succ]; rfl⟩

theorem hAddM_split (w : Nat → Wire) :
    hAddM w = [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ [.CCX (w 1) (w 1797) (w 1540)] ++ hPost w := by
  obtain ⟨b', bs, hD⟩ := dBits_cons w
  obtain ⟨y', ys, hY⟩ := hpR_cons w
  obtain ⟨cs, hC⟩ := hC2_cons w
  simp only [hAddM, hPost, hD, hY, hC, List.tail_cons, mappedAdd, mappedMajority, List.append_assoc,
    List.cons_append, List.nil_append, if_true]

/-- Dropping a Toffoli whose second control is false after a measurement-free prefix. -/
theorem run_drop_ccx (P Q : Program) (a b t : Wire) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hb : (run P [] s).basis b = false) :
    run (P ++ [.CCX a b t] ++ Q) m s = run (P ++ Q) m s := by
  rw [List.append_assoc, run_append, run_append P Q, hP]
  simp only [List.take_zero, List.drop_zero, List.cons_append, List.nil_append, run, hb,
    Bool.and_false, Bool.xor_false, writeBit, Function.update_eq_self]

theorem hAddT1_run (w : Nat → Wire) (h17 : w 1797 ≠ w 1540) (m : List Bool) (s : State)
    (hc : s.basis (w 1797) = false) : run (hAddT1 w) m s = run (hAddM w) m s := by
  rw [hAddM_split, hAddT1, run_drop_ccx]
  · rfl
  · simp only [run, writeBit, Function.update_of_ne h17, hc]

theorem hAddT1_counts (w : Nat → Wire) :
    toffoliCount (hAddT1 w) + 1 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT1 w) = measurementCount (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [toffoliCount_append, measurementCount_append]
  constructor
  · simp [toffoliCount]; omega
  · simp [measurementCount]

theorem hAddT1_wires (w : Nat → Wire) : wires (hAddT1 w) ⊆ wires (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.subset_union_left) (Finset.Subset.refl _)

theorem hAddT1_physical (w : Nat → Wire) (h : GatePhysical (hAddM w)) : GatePhysical (hAddT1 w) := by
  rw [hAddM_split] at h
  rw [hAddT1]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem hAddT1_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT1 w) + 1 = Challenge.gateSlots (hAddM w) := by
  rw [hAddM_split, hAddT1]
  simp only [Challenge.gateSlots_append]
  simp [Challenge.gateSlots, Challenge.instructionSlots]
  omega


theorem dBits_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBits w)) : q=w 1028 := by
  simp only [dBits,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all


/-! ### Last-carry trim of `hAddT1`: the output `H < p < 2^256`, so its top bit is zero -/

theorem hAddT1_eq (w : Nat → Wire) : hAddT1 w = MappedTopZero.oldT (dBits w) w := rfl

theorem hAddT_eq (w : Nat → Wire) : hAddT w = MappedTopZero.topT (dBits w) w (w 1028) := rfl

theorem dBits_drop (w : Nat → Wire) :
    (dBits w).drop 255 = [MappedTopZero.lowBit (w 1028), MappedTopZero.highBit (w 1028)] := by
  have e : (List.range 257).drop 255 = [255,256] := by decide
  have t1 : (2^257-p).testBit 255 = false := by rw [p_val]; decide
  have t2 : p.testBit 255 = true := by rw [p_val]; decide
  have t3 : (2^257-p).testBit 256 = true := by rw [p_val]; decide
  have t4 : p.testBit 256 = false := by rw [p_val]; decide
  rw [dBits, ← List.map_drop, e]
  simp only [List.map_cons, List.map_nil, t1, t2, t3, t4, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, MappedTopZero.lowBit, MappedTopZero.highBit]

theorem hAddT_counts (w : Nat → Wire) :
    toffoliCount (hAddT w) + 2 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT w) = measurementCount (hAddM w) := by
  have a := hAddT1_counts w
  have b : toffoliCount (hAddT w)+1=toffoliCount (hAddT1 w) ∧
      measurementCount (hAddT w)=measurementCount (hAddT1 w) ∧
      Challenge.gateSlots (hAddT w)+7=Challenge.gateSlots (hAddT1 w) :=
    MappedTopZero.topT_counts (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
  exact ⟨by omega, by omega⟩

section HTopWires
-- Keep elaboration from expanding the whole 257-bit adder's wire set.
attribute [local irreducible] ECDSAAdd.wires

theorem hAddT_wires (w : Nat → Wire) : wires (hAddT w) ⊆ wires (hAddM w) := by
  have b : wires (hAddT w) ⊆ wires (hAddT1 w) :=
    MappedTopZero.topT_wires (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
  exact Finset.Subset.trans b (hAddT1_wires w)

end HTopWires

theorem hAddT_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (h : GatePhysical (hAddM w)) : GatePhysical (hAddT w) := by
  have nd : [w 1028,w 256,w 1794,w 257].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨w_ne w hn _ _ (by omega) (by omega) (by omega),w_ne w hn _ _ (by omega) (by omega) (by omega),
      w_ne w hn _ _ (by omega) (by omega) (by omega)⟩,
      ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),w_ne w hn _ _ (by omega) (by omega) (by omega)⟩,
      w_ne w hn _ _ (by omega) (by omega) (by omega)⟩
  have b : GatePhysical (hAddT1 w) → GatePhysical (hAddT w) :=
    MappedTopZero.topT_physical (dBits w) w (w 1028) (dBits_length w) (dBits_drop w) nd
  exact b (hAddT1_physical w h)

theorem hAddT_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT w) + 8 = Challenge.gateSlots (hAddM w) := by
  have a := hAddT1_slots w
  have b : Challenge.gateSlots (hAddT w)+7=Challenge.gateSlots (hAddT1 w) :=
    (MappedTopZero.topT_counts (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)).2.2
  omega

section Rest
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCompareMF (b0 : BasisState) (k X : Nat) (hk : cmpC+k<2^256) (hX : X<2^256)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) (gm : g∉mutL w) :
    Triple (MF w b0 0 X 0 false false false false) (comparePart w g k)
      (MF w b0 0 X 0 false (decide (2^256-1-(if b0 g then cmpC+k else 0)<X)) false false) := by
  intro s m h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have sp := hR_src w hn s.basis
  have kx := kR_x w hn s.basis
  have xl := regValue_lt (xR w) s.basis
  have sl := regValue_lt (srcR w) s.basis
  simp only [xR,srcR,wireBlock_length] at xl sl
  rw [h1] at sp; rw [h2] at kx
  have hx : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    omega
  have src0 : regValue (srcR w) s.basis=0 := by omega
  have top0 : regValue (wireBlock w 256 2) s.basis=0 := by
    by_contra hne; have : 1≤regValue (wireBlock w 256 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
    have : 2^256≤2^256*regValue (wireBlock w 256 2) s.basis := Nat.le_mul_of_pos_right _ this
    omega
  have hzero := (regValue_zero _ _).mp h1
  have cc : ∀q∈cR w,s.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    by_cases hi2 : i<258
    · exact hzero _ ((mem_blk w hn i 0 258 (by omega) (by omega)).mpr (by omega))
    · rw [h8 _ ?_]; exact hc i (by omega) (by omega)
      simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨⟨⟨nb w hn i 0 258 (by omega) (by omega) (by omega),nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
        nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
        exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have m513 : w 513∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 513 0 258 (by omega) (by omega) (by omega),nb w hn 513 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 513 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have cfr := cfCompare w g hn s.basis false k X hk hx cc ((h8 _ m513).trans hcin) gs g514 s m
    ⟨src0,h5,fun _ _ _ => rfl⟩
  obtain ⟨tp,c1',c2',c3'⟩ := cfr
  refine ⟨tp,?_⟩
  simp only [Bool.false_xor] at c2'
  have gv : s.basis g=b0 g := h8 g gm
  rw [gv] at c2'
  have same : ∀q,q∉srcR w → q≠w 514 → (run (comparePart w g k) m s).basis q=s.basis q := c3'
  have srcm : ∀q∈srcR w,q∈mutL w := fun q hq => hR_mut w hn q (blk_sub w 0 256 0 258 (by omega) (by omega) q hq)
  have m514 : w 514∈mutL w := by simp [mutL]
  refine ⟨?_,?_,?_,?_,c2',?_,?_,?_⟩
  · rw [hR_src w hn,c1',regValue_congr _ _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 256 2 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 256 2 (by omega) (by omega) (by omega) (e ▸ hq))),top0]; simp
  · rw [regValue_congr (kR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 770 258 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 770 258 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h2
  · rw [regValue_congr (tR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 1029 256 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 1029 256 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h3
  · rw [same _ (nb w hn 1028 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h4
  · rw [same _ (nb w hn 721 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h6
  · rw [same _ (nb w hn 722 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h7
  · intro q hq
    rw [same q (fun h' => hq (srcm q h')) (fun e => hq (e ▸ m514))]; exact h8 q hq

theorem stepMeasFp (b0 : BasisState) (H X T : Nat) (par f gp : Bool) :
    Triple (MF w b0 H X T par f gp (f && par)) [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]
      (MF w b0 H X T par f gp false) := by
  intro s m h
  rw [run_meas_and (w 722) (w 514) (w 1028) m s (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.1])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp (f && par) s ⟨s.phase,writeBit s.basis (w 722) false⟩ 722
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepMeasGp (b0 : BasisState) (H X T : Nat) (par f fp : Bool) (gm : g∉mutL w)
    (g515 : g≠w 721) :
    Triple (MF w b0 H X T par f (b0 g && par) fp) [.measureX (w 721) [] [.CZ g (w 1028)]]
      (MF w b0 H X T par f false fp) := by
  intro s m h
  rw [run_meas_and (w 721) g (w 1028) m s g515
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2 g gm])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f (b0 g && par) fp s ⟨s.phase,writeBit s.basis (w 721) false⟩ 721
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepCopy (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 0 X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have e0 : regValue (hpR w) s.basis=0 := by omega
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    rw [e0,b0',Nat.zero_xor]
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [this]; simp

end Rest


section Rest2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem aC_out : ∀q∈aC w,q∉mutL w := by
  intro q hq hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
  · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
  all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm

theorem w1797_out : w 1797∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
    nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
    exact w_ne w hn _ _ (by omega) (by omega) (by omega)

theorem stepHAdd (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddM w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  rw [hAddM]
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBits w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBits_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (dBits w) (hpR w) (hC2 w) (w 1797) nd srcw
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length]) s m cl
  refine ⟨hp,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)) m s).basis
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=Y := by rw [b0'] at sp; simp at sp; omega
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,dBits_value,e0,
      h.2.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin]
    simp [hpR,wireBlock_length]

theorem stepHAddT (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : (delta par+Y)%2^257<2^256) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddT w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  have h17 : w 1797 ≠ w 1540 := w_ne w hn 1797 1540 (by omega) (by omega) (by omega)
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  have m95 : w 1795∈aC w := (mem_blk w hn 1795 1540 257 (by omega) (by omega)).mpr (by omega)
  have c95 : s.basis (w 1795)=false := (h.2.2.2.2.2.2.2 _ (aC_out w hn _ m95)).trans (hc _ m95)
  have post := (stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s [] h).2
  have top : (run (MappedTopZero.oldT (dBits w) w) [] s).basis (w 257)=false := by
    rw [← hAddT1_eq, hAddT1_run w h17 [] s c17]
    have bit := regValue_bit (hR w) 257 0 (run (hAddM w) [] s).basis (by simp [hR,wireBlock_length])
    have port : (hR w).getD 257 0=w 257 := rfl
    rw [port,post.1] at bit
    have lt : 2*((delta par+Y)%2^257)<2^257 := by
      rw [show (2:Nat)^257=2*2^256 by norm_num]; omega
    rw [Nat.div_eq_of_lt lt] at bit
    cases hb : (run (hAddM w) [] s).basis (w 257) <;> simp_all
  have inj : ∀ i j,i<1798 → j<1798 → w i=w j → i=j :=
    fun i j hi hj e => skywalkPool_index_inj w hn i j hi hj e
  have eq := MappedTopZero.topT_run (dBits w) w (w 1028) (dBits_length w) (dBits_drop w)
    (fun q hq => dBits_wire w q hq) inj rfl s m c95 top
  rw [hAddT_eq,eq,← hAddT1_eq,hAddT1_run w h17 m s c17]
  exact stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s m h

theorem stepW0 (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,b0',h.2.2.2.1]
    rw [b0'] at sp
    simp [writeBit] at sp ⊢
    omega

theorem stepErase (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : H<2^257) (hf : f=decide (H/2<T)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC3 w)).Nodup := by
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H/2 := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      cases hb : s.basis (w 0) <;> simp [hb] at sp <;> omega
    cases hb : s.basis (w 0) <;> simp [hb] at sp <;> simp only [hp8] at * <;> omega
  have r := eraseLtChain_correct (hp8 w) (tR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hpv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

end Rest2


section Compose
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem g_mut (hg : g∉skywalkPoolWires w) : g∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨g_out w hn g hg 0 258 (by omega),g_out w hn g hg 770 258 (by omega)⟩,g_out w hn g hg 1029 256 (by omega)⟩,
    g_ne w hn g hg 1028 (by omega),g_ne w hn g hg 514 (by omega),g_ne w hn g hg 721 (by omega),g_ne w hn g hg 722 (by omega)⟩

theorem low_bit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState)
    (h : MF w b0 H X T par f gp fp s) : s (w 770)=decide (X%2=1) := by
  have sp := kR_split w hn s
  rw [h.2.1] at sp
  cases hb : s (w 770) <;> simp [hb] at sp ⊢ <;> omega

omit hn in
theorem xor_clear (a b c : Bool) : (((a ^^ (((false ^^ a) ^^ b) ^^ c)) ^^ b) ^^ c)=false := by
  cases a <;> cases b <;> cases c <;> rfl
omit hn in
theorem xor_clear2 (a c : Bool) : ((a ^^ ((false ^^ a) ^^ c)) ^^ c)=false := by
  cases a <;> cases c <;> rfl

theorem stepPar (b0 : BasisState) (k X : Nat) (f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 X 0 false f false false) (parGates w g k)
      (MF w b0 0 (2*(X/2)) 0 (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f) f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have xs : X=2*(X/2)+(decide (X%2=1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;> simp [hx] <;> omega
  apply Triple.conseq (fun s h => by rw [xs] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parGates,if_pos hk,if_pos hk]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 _ _ f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear] at h
    simpa [hk] using h
  · rw [parGates,if_neg hk,if_neg hk]
    try simp only [List.nil_append]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear2] at h
    simpa [hk] using h

theorem stepRot (b0 : BasisState) (X : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 (2*(X/2)) 0 par f gp fp) (rotateRight (kR w)) (MF w b0 0 (X/2) 0 par f gp fp) := by
  intro s m h
  have r := rotateRight_spec (kR w) (kR_nd w hn) (2*(X/2)) (by omega) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 0 _ 0 par f gp fp s _ h fr.2.1 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  rw [this]; omega

end Compose


theorem kC_lt (par : Bool) : kConstant false par<2^258 := by
  cases par <;> norm_num [kConstant,ECDSAAdd.p]

theorem tk_lt (k : Nat) (G f par : Bool) : tk k G f par<2^258 := by
  unfold tk
  split_ifs
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num
  · exact Nat.mod_lt _ (by norm_num)
  · exact kC_lt par

theorem xlt (a b : Nat) (ha : a<2^258) (hb : b<2^258) : a^^^b<2^258 := Nat.xor_lt_two_pow ha hb

theorem c1_lt (k : Nat) : c1 k<2^258 := tk_lt k _ _ _
theorem cg_lt (k : Nat) : cg k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cf_lt (k : Nat) : cf k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cp_lt (k : Nat) : cp k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cgp_lt (k : Nat) : cgp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)
theorem cfp_lt (k : Nat) : cfp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)

def lkv (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1 k ^^^ (if G then cg k else 0) ^^^ (if f then cf k else 0) ^^^ (if par then cp k else 0) ^^^
    (if gp then cgp k else 0) ^^^ (if fp then cfp k else 0)

theorem lkv_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkv k G f par (G && par) (f && par)=tk k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkv,c1,cg,cf,cp,cgp,cfp,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltv (k : Nat) (G gp : Bool) : Nat := (if G then thrA k else 0) ^^^ (if gp then thrB k else 0)

theorem ltv_eq (k : Nat) (G par : Bool) : ltv k G (G && par)=thr k G par := by
  cases G <;> cases par <;> simp [ltv,thr,thrA,thrB,Nat.xor_assoc,Nat.xor_self]

section Compose2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepLoadK (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadK w g k)
      (MF w b0 (H^^^lkv k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1 k) (c1_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cg k) (cg_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cf k) (cf_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cp k) (cp_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgp k) (cgp_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfp k) (cfp_lt k))))))
  unfold loadK
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1 k^^^(if b0 g then cg k else 0)^^^(if f then cf k else 0)^^^(if par then cp k else 0)^^^
      (if gp then cgp k else 0)^^^(if fp then cfp k else 0)=H^^^lkv k (b0 g) f par gp fp := by
    simp only [lkv,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadT (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadT w g k)
      (MF w b0 H X (T^^^ltv k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrA k<2^256 := by unfold thrA; omega
  have lb : thrB k<2^256 := Nat.xor_lt_two_pow la (by rw [p_val]; omega)
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrB k) lb)
  unfold loadT
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltv,Nat.xor_assoc] using h

end Compose2


section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=x0 k G f par at a1
  change (X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=x0 k G f par := a1
    rw [e]; unfold x0 ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (2^256-1-(if b0 g then cmpC+k else 0)<X)=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by unfold cmpC; rw [p_val] at hk ⊢; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s4a := stepCCX w hn b0 0 (X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have kWord : (tk k G f par+X/2)%2^258=K := by rw [Nat.add_comm]; exact a2
  have s6 := stepKAddFlag w hn b0 (tk k G f par) (X/2) 0 par f (G && par) (f && par) hac h1797
    dx (Nat.mod_lt _ (by rw [p_val]; norm_num)) rfl (by exact kWord)
  rw [kWord] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;> simp [hC_val] <;> omega
  have hH10 : (delta par+K%2^257)%2^257<2^256 := by
    rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]]
    have h2 := hHlt
    have h3 := Bool.toNat_le (!par)
    rw [show (2:Nat)^257=2*2^256 by norm_num] at h2
    omega
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by norm_num)) hac h1797 hH10
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp <;> omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq (s3.seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main


section Final
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- The merged circuit leaves exactly the state of the old compare-first constant addition
followed by the direct first tick, on every measurement record. -/
theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
  generalize hpar : decide (dx%2=1)=par at tri a1 a2 a3 a4 a5
  generalize hK : (dx/2+kConstant false par)%2^258=K at tri a1 a2 a3 a4 a5
  generalize hH : (K%2^257+delta par)%2^257=H at tri a1 a2 a3 a4 a5
  obtain ⟨lp,l1,l2,l3,l4,l5,l6,l7,l8⟩ := tri
  have dxlt : dx<p := by rw [←hdx]; exact Nat.mod_lt _ (by rw [p_val]; norm_num)
  have kh : ∀q∈hR w,q∉kR w := kR_hR w hn
  have kt : ∀q∈tR w,q∉kR w := kR_tR w hn
  have hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 dx u.basis := by
    constructor
    · change regValue (wireBlock w 0 258) u.basis=0
      rw [show wireBlock w 0 258=hR w from rfl,regValue_congr _ _ t.basis (fun q hq => hu2 q (kh q hq)),th0]
    · change regValue (wireBlock w 770 258) u.basis=dx
      exact hu3
    · change regValue (wireBlock w 1540 257) u.basis=0
      apply (regValue_zero _ _).mpr
      intro q hq
      rw [hu2 q (fun h' => List.disjoint_left.mp (blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)) h' hq)]
      exact hac q hq
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
    · change u.basis (w 1028)=false
      rw [hu2 _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact t1028
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn dx dxlt u m' hin
  have e770 : u.basis (w 770)=par := by
    have sp := kR_split w hn u.basis
    rw [hu3] at sp
    rw [←hpar]
    cases hb : u.basis (w 770) <;> simp [hb] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  rw [hK] at zk
  have hv : 2*(dx/2+(if par then hConstant else 0))+(!par).toNat=2*H+(!par).toNat := by rw [a3]
  rw [hv] at zh
  apply State.extensionality
  · rw [lp,zp,hu]
  · funext q
    by_cases qh : q∈hR w
    · exact (regValue_eq_iff (hR w) _ _).mp (l1.trans zh.symm) q qh
    by_cases qk : q∈kR w
    · exact (regValue_eq_iff (kR w) _ _).mp (l2.trans zk.symm) q qk
    by_cases q1 : q=w 1028
    · rw [q1,l4,z1028]
    have nmut : q∉NativeFirstDirect.mutable w := by
      simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
      exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),qk⟩,q1⟩
    rw [zrest q nmut,hu2 q qk]
    by_cases qt : q∈tR w
    · rw [(regValue_zero _ _).mp l3 q qt,(regValue_zero _ _).mp tt0 q qt]
    by_cases q4 : q=w 514
    · rw [q4,l5,t514]
    by_cases q5 : q=w 721
    · rw [q5,l6,t515]
    by_cases q6 : q=w 722
    · rw [q6,l7,t516]
    apply l8
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,qk⟩,qt⟩,q1,q4,q5,q6⟩

end Final


/-! ### Resources -/

def mSites (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 515++wireBlock w 770 515++wireBlock w 1540 258++[w 721,w 722,g]

theorem in_mSites (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) : w i∈mSites w g := by
  simp only [mSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hi with h|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩))
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))

theorem blk_mSites (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 515 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀q∈wireBlock w a n,q∈mSites w g := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_mSites w g i (by omega)

theorem g_mSites (w : Nat → Wire) (g : Wire) : g∈mSites w g := by simp [mSites]

theorem dBits_wires_sub (w : Nat → Wire) : ∀q∈mappedWires (dBits w),q=w 1028 := dBits_wire w

theorem lsub (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀q∈l,q∈mSites w g) :
    l.toFinset⊆(mSites w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀q∈i.wires,q∈mSites w g) :
    wires [i]⊆(mSites w g).toFinset := by
  intro q hq
  simp only [wires,Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

theorem merged_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (srcR w) (xR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 0 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskS _,notS⟩,cmp⟩,notS⟩,mskS _⟩
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mSites w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mSites w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mSites w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hKOld : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (KAddCallerBridgeResearch.flagKAdd w)⊆(mSites w g).toFinset := by
    apply (KAddResourceBridgeResearch.flag_support w).trans
    simp only [Finset.union_subset_iff]
    constructor
    · simpa only [←kAdd_literal] using hKOld
    · intro q hq
      have eq : q=w 1028 := Finset.mem_singleton.mp hq
      rw [eq]
      exact List.mem_toFinset.mpr (I 1028 (by omega))
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mSites w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mSites w g).toFinset := (hAddT_wires w).trans hH
  simp only [merged,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC,hP,hR'⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩


theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1023 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (srcR w)
  have c1' := compareLt_counts none (srcR w) (xR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have h1 := mappedAdd_counts (dBits w) (hpR w) (hC2 w) (w 1797)
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pg : toffoliCount (parGates w g k)=0 ∧ measurementCount (parGates w g k)=0 := by
    unfold parGates; split_ifs <;> simp [toffoliCount,measurementCount]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  have kOld : toffoliCount (KAddCallerBridgeResearch.literalKAdd w)=257 ∧
      measurementCount (KAddCallerBridgeResearch.literalKAdd w)=257 := k1
  have kDelta := KAddCallerBridgeResearch.flag_counts w
  have kNew : toffoliCount (KAddCallerBridgeResearch.flagKAdd w)=256 ∧
      measurementCount (KAddCallerBridgeResearch.flagKAdd w)=257 := by omega
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=254 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,comparePart,prodPart,loadK,kNew.1,kNew.2,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_physical (k : Nat) : GatePhysical (merged w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have mp (c : Wire) (c' : Wire) : GatePhysical [.measureX c [] [.CZ c' c]] ∧
      GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by
    simp [GatePhysical,PhysicalInstr]
  have gS : g∉srcR w := g_out w hn g hg 0 256 (by omega)
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
      have l2 : (srcR w++xR w++cR w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 0 256 (by omega) (by omega) (by omega),
          nb w hn 514 770 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 0 256 (by omega) (by omega) (by omega),nb w hn 513 770 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
  have kPOld : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have kP : GatePhysical (KAddCallerBridgeResearch.flagKAdd w) :=
    KAddResourceBridgeResearch.flag_gatePhysical w hn (by simpa only [←kAdd_literal] using kPOld)
  have hP : GatePhysical (hAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBits w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBits_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have eP : GatePhysical (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parGates w g k) := by
    unfold parGates
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).1
  have prodP : GatePhysical (prodPart w g) := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,gatePhysical_append]
    exact ⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h1286 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h1287 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t1286 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadK w g k) := by
    simp only [loadK,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h1286⟩,maskedConstant_physical _ _ _ h1287⟩
  have ltP : GatePhysical (loadT w g k) := by
    simp only [loadT,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t1286⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have cP : GatePhysical (comparePart w g k) := by
    simp only [comparePart,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gS,notRegister_physical _⟩,cmpP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hn hP
  simp only [merged,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cP,parP,rotP⟩,prodP⟩,lkP⟩,kP⟩,lkP⟩,m1⟩,cpP⟩,hPT⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩

end Phys

theorem gs1 (i : Instr) : Challenge.gateSlots [i]=Challenge.instructionSlots i := by
  simp [Challenge.gateSlots]

theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (srcR w) (xR w) (cR w) (w 513) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).1
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.mappedAdd_gateSlots_le (dBits w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
  have pg : Challenge.gateSlots (parGates w g k)≤6 := by
    unfold parGates; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have pr : Challenge.gateSlots (prodPart w g)=2 := by simp [prodPart,Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q2 : Challenge.gateSlots [.measureX (w 721) [] [.CZ g (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadK w g k)≤6*258 := by
    simp only [loadK,Challenge.gateSlots_append]
    have := x1 (hR w) (c1 k); have := m1 g (hR w) (cg k); have := m1 (w 514) (hR w) (cf k)
    have := m1 (w 1028) (hR w) (cp k); have := m1 (w 721) (hR w) (cgp k); have := m1 (w 722) (hR w) (cfp k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadT w g k)≤2*256 := by
    simp only [loadT,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrA k); have := m1 (w 721) (tR w) (thrB k)
    simp only [tR,wireBlock_length] at *
    omega
  have cP : Challenge.gateSlots (comparePart w g k)≤4*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) (cmpC+k)
    simp only [srcR,xR,wireBlock_length] at *
    omega
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  have kOld : Challenge.gateSlots (KAddCallerBridgeResearch.literalKAdd w)≤17*258 := k1
  have kNew : Challenge.gateSlots (KAddCallerBridgeResearch.flagKAdd w)+5≤17*258 := by
    rw [←(KAddCallerBridgeResearch.flag_counts w).2.2]
    exact kOld
  rw [dBits_length] at h1
  rw [lh] at e1
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,Challenge.gateSlots_append,pr,w0,q1,q2,cp]
  omega

end ECDSAAdd.Entrant.E1Merge

end -- original module boundary


/-! Exit-side merged tick.  On the image of the direct first tick it performs the last
reverse integer tick followed by the controlled constant negation
`x ↦ g ? (k - x mod p) : x` as one circuit: the threshold compare of the negation is read
from the tick word `H`, `H` is erased against `K` by a known-output adder, and one mapped
addition takes the complemented `K` word straight to `y/2`. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 1024

namespace ECDSAAdd.Entrant.ExitMerge
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum E1Merge

/-! ### Arithmetic -/

/-- For `G`, `x > k` iff `¬ H < thrX`, where `H` is the tick word of `x`. -/
def thrX (k : Nat) (G par : Bool) : Nat :=
  if G then (if par then (k+1)/2+hConstant else (k+2)/2) else 0

/-- Constant added to the (complemented) `K` word to reach `y/2`. -/
def tkX (k : Nat) (G f par : Bool) : Nat :=
  if G then (kConstant false par+1+(k+(if f then p else 0)-par.toNat)/2)%2^258
  else (2^258-kConstant false par)%2^258

/-- Addend that takes the tick word `H` back to the low bits of `K`. -/
def dInv (par : Bool) : Nat := if par then 2^257-p else p

theorem pfacts : p%2=1 ∧ 2^255<p ∧ p<2^256 ∧ 2*hConstant=p+1 ∧ kConstant false false=p ∧
    kConstant false true+(p-1)/2=2^258 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · norm_num [p_val]
  · norm_num [p_val]
  · norm_num [p_val]
  · norm_num [hC_val,p_val]
  · norm_num [kC_val,p_val]
  · norm_num [kC_val,p_val]

theorem ymod (k X : Nat) (hk : k<p) (hX : X<p) : (k+p-X)%p=if k<X then k+p-X else k-X := by
  by_cases h : k<X
  · rw [if_pos h]; exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg h,Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega

set_option maxHeartbeats 1000000 in
theorem archX (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let f := G && decide (k<X)
    let Y := if G then (k+p-X)%p else X
    H<2^256 ∧ (dInv par+H)%2^257=K%2^257 ∧ f=(decide (H<thrX k G par) ^^ G) ∧
    ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 ∧ Y<p ∧
    decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) ∧
    f=decide ((if G then k else 2^256-1)<Y) := by
  intro par H K f Y
  obtain ⟨po,pg,pl,hc2,k0,k1⟩ := pfacts
  simp only [par,H,K,f,Y,thrX,tkX,dInv]
  simp only [ymod k X hk hX]
  rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;>
  rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
  cases G <;>
  by_cases hkx : k<X <;>
  simp only [hx,h2,hkx,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
    Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
    Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor,Bool.true_and,Bool.false_and,
    Bool.and_true,Bool.and_false,k0] <;>
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
  first
    | exact True.intro
    | omega
    | (simp only [decide_eq_true_iff,decide_eq_false_iff_not]; omega)
    | (apply Eq.symm; simp only [Bool.not_eq_eq_eq_not,Bool.not_true,Bool.not_false,
        decide_eq_true_iff,decide_eq_false_iff_not]; omega)

/-! ### Circuit -/

def thrXA (k : Nat) : Nat := (k+2)/2
def thrXB (k : Nat) : Nat := (k+2)/2 ^^^ ((k+1)/2+hConstant)

def loadTX (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrXA k)++maskedConstant (w 721) (tR w) (thrXB k)

def fPart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CCX g (w 1028) (w 721)]++loadTX w g k++
  compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)++[.CX g (w 514)]++loadTX w g k++
  [.CCX (w 514) (w 1028) (w 722)]

def dBitsX (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := p.testBit j
  let b := (2^257-p).testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def desiredX (w : Nat → Wire) : List MappedBit := mappedRead (wireBlock w 770 257) false

def knownH (w : Nat → Wire) : Program :=
  KnownOutputAdder.program (dBitsX w) (hpR w) (desiredX w) (hC2 w) (w 1797)

def eraseH (w : Nat → Wire) : Program :=
  [.CX (w 1028) (w 0),.X (w 0)]++knownH w++copyRegister none (wireBlock w 770 257) (hpR w)

def c1X (k : Nat) : Nat := tkX k false false false
def cgX (k : Nat) : Nat := tkX k true false false ^^^ tkX k false false false
def cfX (k : Nat) : Nat := tkX k true true false ^^^ tkX k true false false
def cpX (k : Nat) : Nat := tkX k false false true ^^^ tkX k false false false
def cgpX (k : Nat) : Nat :=
  tkX k true false true ^^^ tkX k true false false ^^^ tkX k false false true ^^^ tkX k false false false
def cfpX (k : Nat) : Nat :=
  tkX k true true true ^^^ tkX k true true false ^^^ tkX k true false true ^^^ tkX k true false false

def loadKX (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1X k)++maskedConstant g (hR w) (cgX k)++maskedConstant (w 514) (hR w) (cfX k)++
  maskedConstant (w 1028) (hR w) (cpX k)++maskedConstant (w 721) (hR w) (cgpX k)++
  maskedConstant (w 722) (hR w) (cfpX k)

def addPart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  FastConst.maskedNot g (kR w)++loadKX w g k++Verifier.Leaf4.zero4KAdd w++loadKX w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]]

def parBack (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]++
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]

def eraseF (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (2^256-1-k)++notRegister (tR w)++
  eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514)++
  notRegister (tR w)++maskedConstant g (tR w) (2^256-1-k)

/-- Last reverse tick and controlled negation `x ↦ g ? (k - x mod p) : x`, merged. -/
def program (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  fPart w g k++eraseH w++addPart w g k++rotateLeft (kR w)++parBack w g k++eraseF w g k

/-! ### Mapped constants -/

theorem selX (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

theorem dX_list (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := p.testBit j
      let b := (2^257-p).testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then (2^257-p).testBit j else p.testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selX]

def dXScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then (2^257-p).testBit j else p.testBit j).toNat+2*acc) 0

theorem dXScalar_value (par : Bool) : dXScalar par=dInv par := by
  cases par <;> decide

theorem dBitsX_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBitsX w) s=dInv (s (w 1028)) := by
  rw [dBitsX,dX_list]
  exact dXScalar_value (s (w 1028))

theorem dBitsX_length (w : Nat → Wire) : (dBitsX w).length=257 := by simp [dBitsX]

theorem dBitsX_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBitsX w)) : q=w 1028 := by
  simp only [dBitsX,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all

theorem desiredX_value (w : Nat → Wire) (s : BasisState) :
    mappedValue (desiredX w) s=regValue (wireBlock w 770 257) s := by
  rw [desiredX,mappedRead_value]

theorem desiredX_length (w : Nat → Wire) : (desiredX w).length=257 := by
  simp [desiredX,mappedRead_length,wireBlock_length]

theorem tkX_lt (k : Nat) (G f par : Bool) : tkX k G f par<2^258 := by
  unfold tkX
  split_ifs <;> exact Nat.mod_lt _ (by norm_num)

theorem c1X_lt (k : Nat) : c1X k<2^258 := tkX_lt k _ _ _
theorem cgX_lt (k : Nat) : cgX k<2^258 := xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)
theorem cfX_lt (k : Nat) : cfX k<2^258 := xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)
theorem cpX_lt (k : Nat) : cpX k<2^258 := xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)
theorem cgpX_lt (k : Nat) : cgpX k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)) (tkX_lt k _ _ _)) (tkX_lt k _ _ _)
theorem cfpX_lt (k : Nat) : cfpX k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)) (tkX_lt k _ _ _)) (tkX_lt k _ _ _)

def lkvX (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1X k ^^^ (if G then cgX k else 0) ^^^ (if f then cfX k else 0) ^^^ (if par then cpX k else 0) ^^^
    (if gp then cgpX k else 0) ^^^ (if fp then cfpX k else 0)

theorem lkvX_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkvX k G f par (G && par) (f && par)=tkX k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkvX,c1X,cgX,cfX,cpX,cgpX,cfpX,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltvX (k : Nat) (G gp : Bool) : Nat := (if G then thrXA k else 0) ^^^ (if gp then thrXB k else 0)

theorem ltvX_eq (k : Nat) (G par : Bool) : ltvX k G (G && par)=thrX k G par := by
  cases G <;> cases par <;> simp [ltvX,thrX,thrXA,thrXB,Nat.xor_assoc,Nat.xor_self]

/-! ### Steps -/

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCmpH (b0 : BasisState) (H b X T : Nat) (par gp fp : Bool) (hH : H<2^256) (hb : b<2)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*H+b) X T par false gp fp) (compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514))
      (MF w b0 (2*H+b) X T par (decide (H<T)) gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC2 w)).Nodup := by
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 256 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC2 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have hpv0 : regValue (hpR w) s.basis=H := by
    cases hb0 : s.basis (w 0) <;> simp [hb0] at sp <;> omega
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    show regValue (wireBlock w 1 256) s.basis=H
    omega
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514) nd (by simp)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC2,tR,wireBlock_length]) s m c17 cl
  refine ⟨hp,?_⟩
  have := stepBit w hn b0 (2*H+b) X T par false gp fp s _ 514 (by omega) h he
  rw [hv,h.2.2.2.2.1,hpv,h.2.2.1] at this
  simpa [controlValue] using this

theorem stepFlagCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 514) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 514)] (MF w b0 H X T par (f ^^ cv) gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514)
    (s.basis (w 514) ^^ s.basis c)⟩ 514 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.2.1,hcv s.basis h] using this

theorem stepW0Back (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=
      ⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 _ X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,h.2.2.2.1]
    cases hb : s.basis (w 0) <;> cases par <;> simp [hb,writeBit] at sp ⊢ <;> omega

theorem stepKnownH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (hH : H<2^257)
    (hsum : (dInv par+H)%2^257=X%2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*H) X T par f gp fp) (knownH w) (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  unfold knownH
  intro s m h
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBitsX w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBitsX_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have dw : ∀q∈mappedWires (desiredX w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [desiredX,mappedRead_wires] at hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn i 1 257 (by omega) (by omega) (by omega),
      nb w hn i 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have b0' : s.basis (w 0)=false := by
    cases hb : s.basis (w 0)
    · rfl
    · simp [hb] at sp; omega
  have e0 : regValue (hpR w) s.basis=H := by rw [b0'] at sp; simp at sp; omega
  have kl := kR_low w hn s.basis
  rw [h.2.1] at kl
  have ll := regValue_lt (wireBlock w 770 257) s.basis
  simp only [wireBlock_length] at ll
  have klow : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
  have lhp : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  obtain ⟨hp,he,hval⟩ := KnownOutputAdder.program_correct (dBitsX w) (desiredX w) (hpR w) (hC2 w) (w 1797)
    nd srcw dw (by rw [dBitsX_length,lhp]) (by rw [desiredX_length,lhp]) (by simp [hC2,hpR,wireBlock_length])
    s m cl (by rw [desiredX_value,dBitsX_value,h.2.2.2.1,e0,c17,klow,lhp]; simpa using hsum.symm)
  refine ⟨hp,stepH w hn b0 (2*H) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp2 := hR_split w hn (run (KnownOutputAdder.program (dBitsX w) (hpR w) (desiredX w) (hC2 w) (w 1797)) m s).basis
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,desiredX_value,klow]
    simp

theorem stepCopyBack (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*(X%2^257)) X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 0 X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 _ X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=X%2^257 := by rw [b0'] at sp; simp at sp; omega
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [e0,this,b0',Nat.xor_self]; simp

theorem stepNegK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (hX : X<2^258)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (FastConst.maskedNot g (kR w))
      (MF w b0 H (if b0 g then 2^258-1-X else X) T par f gp fp) := by
  intro s m h
  have gk : g∉kR w := g_out w hn g hg 770 258 (by omega)
  have gv : s.basis g=b0 g := h.2.2.2.2.2.2.2 g (g_mut w g hn hg)
  rw [FastConst.maskedNot_run g (kR w) gk s m,gv]
  cases hb : b0 g
  · simp only [Bool.false_eq_true,if_false]
    exact ⟨by trivial,h⟩
  · simp only [if_true,eq_self_iff_true]
    rw [notRegister_correct (kR w) (kR_nd w hn)]
    refine ⟨rfl,stepK w hn b0 H X T par f gp fp s _ h ?_ _ ?_⟩
    · intro q hq
      show (if q∈kR w then _ else _)=_
      simp [hq]
    · change regValue (kR w) (fun q => if q∈kR w then !s.basis q else s.basis q)=_
      rw [regValue_congr (kR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
        regValue_complement,h.2.1]
      simp [kR,wireBlock_length]

theorem stepNotT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 H X T par f gp fp) (notRegister (tR w)) (MF w b0 H X (2^256-1-T) par f gp fp) := by
  intro s m h
  rw [notRegister_correct (tR w) (tR_nd w hn)]
  refine ⟨rfl,stepT w hn b0 H X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    show (if q∈tR w then _ else _)=_
    simp [hq]
  · change regValue (tR w) (fun q => if q∈tR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (tR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.2.2.1]
    simp [tR,wireBlock_length]

theorem stepRotL (b0 : BasisState) (H V T : Nat) (par f gp fp : Bool) (hV : 2*V<2^258) :
    Triple (MF w b0 H V T par f gp fp) (rotateLeft (kR w)) (MF w b0 H (2*V) T par f gp fp) := by
  intro s m h
  have r := rotateLeft_spec (kR w) (kR_nd w hn) V (by simpa [kR,wireBlock_length] using hV) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 H V T par f gp fp s _ h fr.2.2.2 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  exact this

theorem stepEraseF (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hX : X<2^256) (hf : f=decide (T<X)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(tR w++xR w++hC3 w)).Nodup := by
    have a1 := blk_dis w hn 1029 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (tR w++xR w).Nodup := List.nodup_append'.mpr ⟨tR_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (tR w++xR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1029 256 (by omega) (by omega) (by omega),
        nb w hn 514 770 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1029 256 (by omega) (by omega) (by omega),nb w hn 1797 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have kx := kR_x w hn s.basis
  rw [h.2.1] at kx
  have xl := regValue_lt (xR w) s.basis
  simp only [xR,wireBlock_length] at xl
  have hxv : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      simp only [xR] at kx; omega
    simp only [xR] at kx ⊢; omega
  have r := eraseLtChain_correct (tR w) (xR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [xR,tR,wireBlock_length]) (by simp [hC3,xR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hxv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepLoadKX (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadKX w g k)
      (MF w b0 (H^^^lkvX k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1X k) (c1X_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cgX k) (cgX_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cfX k) (cfX_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cpX k) (cpX_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgpX k) (cgpX_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfpX k) (cfpX_lt k))))))
  unfold loadKX
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1X k^^^(if b0 g then cgX k else 0)^^^(if f then cfX k else 0)^^^(if par then cpX k else 0)^^^
      (if gp then cgpX k else 0)^^^(if fp then cfpX k else 0)=H^^^lkvX k (b0 g) f par gp fp := by
    simp only [lkvX,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadTX (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadTX w g k)
      (MF w b0 H X (T^^^ltvX k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrXA k<2^256 := by unfold thrXA; omega
  have lb' : (k+1)/2+hConstant<2^256 := by rw [hC_val]; omega
  have lb : thrXB k<2^256 := Nat.xor_lt_two_pow la lb'
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrXA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrXB k) lb)
  unfold loadTX
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltvX,Nat.xor_assoc] using h

theorem stepParBack (b0 : BasisState) (k V : Nat) (par f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 (2*V) 0 par f false false) (parBack w g k)
      (MF w b0 0 (2*V+(par ^^ (b0 g && decide (k%2=1)) ^^ f).toNat) 0 false f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have lb (b par' : Bool) : ∀s : BasisState,MF w b0 0 (2*V+b.toNat) 0 par' f false false s → s (w 770)=b := by
    intro s h; have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; cases b <;> simp <;> omega
  apply Triple.conseq (fun s h => by rw [show 2*V=2*V+(false).toNat by simp] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parBack,if_pos hk,if_pos hk]
    have t := (stepLowCX w hn b0 0 V 0 false par f false false (w 1028) par e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f false false (w 514) f e4 (fun s h => h.2.2.2.2.1)).seq
      ((stepParCX w hn b0 0 _ 0 par f false false (w 770) _ e1 (lb _ par)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      (stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    have e : (((par ^^ (((false ^^ par) ^^ b0 g) ^^ f)) ^^ b0 g) ^^ f)=false := by
      cases par <;> cases b0 g <;> cases f <;> rfl
    rw [e] at h
    have e' : (((false ^^ par) ^^ b0 g) ^^ f)=(par ^^ (b0 g && decide (k%2=1)) ^^ f) := by
      simp [hk]
    rw [e'] at h
    exact h
  · rw [parBack,if_neg hk,if_neg hk]
    try simp only [List.nil_append,List.append_nil]
    have t := (stepLowCX w hn b0 0 V 0 false par f false false (w 1028) par e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f false false (w 514) f e4 (fun s h => h.2.2.2.2.1)).seq
      ((stepParCX w hn b0 0 _ 0 par f false false (w 770) _ e1 (lb _ par)).seq
      (stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    have e : ((par ^^ ((false ^^ par) ^^ f)) ^^ f)=false := by
      cases par <;> cases f <;> rfl
    rw [e] at h
    have e' : ((false ^^ par) ^^ f)=(par ^^ (b0 g && decide (k%2=1)) ^^ f) := by
      simp [hk]
    rw [e'] at h
    exact h

end Steps

/-! ### Composition -/

section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem program_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF w b0 (2*H+(!par).toNat) K 0 par false false false) (program w g k)
      (MF w b0 0 Y 0 false false false false) := by
  intro G par H K Y
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  change f=decide ((if G then k else 2^256-1)<Y) at a8
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by norm_num)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  -- threshold compare
  have s1 := stepCCX w hn b0 (2*H+(!par).toNat) K 0 par false false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX w g hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH w hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX w hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false g G (g_ne w hn g hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 g gm)
  rw [←a3] at s4
  have s5 := stepLoadTX w g hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 g=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX w hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  -- erase the tick word
  have s7 := stepW0Back w hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH w hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack w hn b0 K 0 par f (G && par) (f && par)
  -- one mapped addition to `y/2`
  have s10 := stepNegK w g hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX w g hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkvX_eq k G f par hfg] at s11
  have kWord : (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 := by
    rw [Nat.add_comm]; exact a5
  have s12 := stepKAddZero4 w hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par)
    hac h1797 Y a6 kWord
  rw [kWord] at s12
  have s13 := stepLoadKX w g hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp w hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepMeasGp w g hn b0 0 (Y/2) 0 par f false gm (g_ne w hn g hg 721 (by omega))
  -- rotate and parity
  have s16 := stepRotL w hn b0 0 (Y/2) 0 par f false false (by rw [p_val] at a6; omega)
  have s17 := stepParBack w g hn b0 k (Y/2) par f hg
  rw [show b0 g=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  -- erase the flag
  have s18 := stepMaskT w hn b0 0 Y 0 false f false false g G gT (fun s h => h.2.2.2.2.2.2.2 g gm)
    (2^256-1-k) (by omega)
  have s19 := stepNotT w hn b0 0 Y (0^^^(if G then 2^256-1-k else 0)) false f false false
  have hT (G' : Bool) : 2^256-1-(0^^^(if G' then 2^256-1-k else 0))=(if G' then k else 2^256-1) := by
    rw [p_val] at hk; cases G' <;> simp <;> omega
  rw [hT G] at s19
  have s20 := stepEraseF w hn b0 0 Y (if G then k else 2^256-1) false f false false hac h1797
    (by rw [p_val] at a6; omega) a8
  have s21 := stepNotT w hn b0 0 Y (if G then k else 2^256-1) false false false false
  have s22 := stepMaskT w hn b0 0 Y (2^256-1-(if G then k else 2^256-1)) false false false false g G gT
    (fun s h => h.2.2.2.2.2.2.2 g gm) (2^256-1-k) (by omega)
  have hT2 (G' : Bool) : (2^256-1-(if G' then k else 2^256-1))^^^(if G' then 2^256-1-k else 0)=0 := by
    cases G' <;> simp [Nat.xor_self]
  rw [hT2 G] at s22
  have t := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq (s18.seq (s19.seq (s20.seq (s21.seq
    s22))))))))))))))))))))
  unfold program fPart eraseH addPart eraseF
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main

/-! ### Run on the image of the direct first tick -/

theorem mutL_pool (w : Nat → Wire) : ∀ q∈mutL w,q∈skywalkPoolWires w := by
  intro q hq
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with ((h|h)|h)|h|h|h|h
  · exact blk_sub w 0 258 0 1798 (by omega) (by omega) q h
  · exact blk_sub w 770 258 0 1798 (by omega) (by omega) q h
  · exact blk_sub w 1029 256 0 1798 (by omega) (by omega) q h
  all_goals (subst h; exact List.mem_map.mpr ⟨_,by simp only [List.mem_range'_1]; omega,rfl⟩)

section Run
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- On the forward image of a clean seed holding `X`, the merged exit circuit restores the seed
except that the `K` block holds `g ? (k - X mod p) : X`; wires outside the pool are untouched. -/
theorem program_run (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (initial field : State) (mF m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 X initial.basis)
    (ht : regValue (tR w) initial.basis=0) (h514 : initial.basis (w 514)=false)
    (h721 : initial.basis (w 721)=false) (h722 : initial.basis (w 722)=false)
    (hphase : field.phase=(run (NativeFirstDirect.forward w) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires w,
      field.basis q=(run (NativeFirstDirect.forward w) mF initial).basis q) :
    (run (program w g k) m field).phase=initial.phase ∧
    regValue (kR w) (run (program w g k) m field).basis=(if field.basis g then (k+p-X)%p else X) ∧
    (∀q∈skywalkPoolWires w,q∉kR w → (run (program w g k) m field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w → (run (program w g k) m field).basis q=field.basis q) := by
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn X hX initial mF hin
  have e770 : initial.basis (w 770)=decide (X%2=1) := by
    have sp := kR_split w hn initial.basis
    have hb : regValue (kR w) initial.basis=X := hin.b
    rw [hb] at sp
    cases h : initial.basis (w 770) <;> simp [h] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  have inPool (a n : Nat) (ha : a+n≤1798) : ∀q∈wireBlock w a n,q∈skywalkPoolWires w :=
    blk_sub w a n 0 1798 (by omega) ha
  have wPool (i : Nat) (hi : i<1798) : w i∈skywalkPoolWires w :=
    List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have keepI (i : Nat) (hi : i < 1798) (h1 : 257 ≤ i) (h2 : i < 770 ∨ 1028 < i) :
      field.basis (w i)=initial.basis (w i) := by
    rw [hpool _ (wPool i hi)]
    apply zrest
    simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨nb w hn i 0 257 hi (by omega) (by omega),nb w hn i 770 258 hi (by omega) (by omega)⟩,
      w_ne w hn i 1028 hi (by omega) (by omega)⟩
  have hR0 : regValue (hR w) field.basis=
      2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat := by
    rw [regValue_congr (hR w) field.basis _ (fun q hq => hpool q (inPool 0 258 (by omega) q hq))]
    exact zh
  have kR0 : regValue (kR w) field.basis=(X/2+kConstant false (decide (X%2=1)))%2^258 := by
    rw [regValue_congr (kR w) field.basis _ (fun q hq => hpool q (inPool 770 258 (by omega) q hq))]
    exact zk
  have tR0 : regValue (tR w) field.basis=0 := by
    rw [regValue_congr (tR w) field.basis initial.basis (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact keepI i (by omega) (by omega) (by omega))]
    exact ht
  have f1028 : field.basis (w 1028)=decide (X%2=1) := (hpool _ (wPool 1028 (by omega))).trans z1028
  have f514 : field.basis (w 514)=false := (keepI 514 (by omega) (by omega) (by omega)).trans h514
  have f721 : field.basis (w 721)=false := (keepI 721 (by omega) (by omega) (by omega)).trans h721
  have f722 : field.basis (w 722)=false := (keepI 722 (by omega) (by omega) (by omega)).trans h722
  have hac : ∀q∈aC w,field.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [keepI i (by omega) (by omega) (by omega)]
    exact (regValue_zero _ _).mp hin.carry _ hq
  have h1797 : field.basis (w 1797)=false := (keepI 1797 (by omega) (by omega) (by omega)).trans hin.cin
  have mf0 : MF w field.basis (2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat)
      ((X/2+kConstant false (decide (X%2=1)))%2^258) 0 (decide (X%2=1)) false false false field.basis :=
    ⟨hR0,kR0,tR0,f1028,f514,f721,f722,fun _ _ => rfl⟩
  obtain ⟨tp,o1,o2,o3,o4,o5,o6,o7,o8⟩ := program_triple w g hn hg k hk field.basis X hX hac h1797 field m mf0
  have outMut (q : Wire) (hq : q∉skywalkPoolWires w) : q∉mutL w := fun h => hq (mutL_pool w q h)
  refine ⟨tp.trans (hphase.trans zp),o2,?_,fun q hq => o8 q (outMut q hq)⟩
  intro q hq hk'
  by_cases qh : q∈hR w
  · rw [(regValue_zero _ _).mp o1 q qh]
    exact ((regValue_zero _ _).mp hin.a q qh).symm
  by_cases qt : q∈tR w
  · rw [(regValue_zero _ _).mp o3 q qt]
    exact ((regValue_zero _ _).mp ht q qt).symm
  by_cases q1 : q=w 1028
  · rw [q1,o4]; exact hin.one.symm
  by_cases q2 : q=w 514
  · rw [q2,o5]; exact h514.symm
  by_cases q3 : q=w 721
  · rw [q3,o6]; exact h721.symm
  by_cases q4 : q=w 722
  · rw [q4,o7]; exact h722.symm
  have nm : q∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,hk'⟩,qt⟩,q1,q2,q3,q4⟩
  rw [o8 q nm,hpool q hq]
  apply zrest
  simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
  exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),hk'⟩,q1⟩

end Run

/-! ### Resources -/

theorem program_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (program w g k)=767 ∧ measurementCount (program w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (tR w)
  have c1' := compareLt_counts none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC2,tR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have kh := KnownOutputAdder.program_counts (dBitsX w) (desiredX w) (hpR w) (hC2 w) (w 1797)
    (by rw [dBitsX_length]; simp [hpR,wireBlock_length]) (by rw [desiredX_length]; simp [hpR,wireBlock_length])
    (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (tR w) (xR w) (hC3 w) (w 1797) (w 514)
    (by simp [xR,tR,wireBlock_length]) (by simp [hC3,xR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pb : toffoliCount (parBack w g k)=0 ∧ measurementCount (parBack w g k)=0 := by
    unfold parBack; split_ifs <;> simp [toffoliCount,measurementCount]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  rw [lt] at c1'
  rw [lk] at k1
  have kOld : toffoliCount (KAddCallerBridgeResearch.literalKAdd w)=257 ∧
      measurementCount (KAddCallerBridgeResearch.literalKAdd w)=257 := k1
  have kNew : toffoliCount (Verifier.Leaf4.zero4KAdd w)=254 ∧
      measurementCount (Verifier.Leaf4.zero4KAdd w)=257 :=
    Verifier.Leaf4.zero4_counts w kOld
  rw [lh] at kh
  rw [lx] at e1
  simp only [program,fPart,eraseH,addPart,eraseF,loadTX,loadKX,knownH,kNew.1,kNew.2,FastConst.maskedNot,
    toffoliCount_append,measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,
    n1.1,n1.2,c1'.1,c1'.2.1,r1.2.2.1,r1.2.2.2,kh.1,kh.2,e1.1,e1.2,cp1.1,cp1.2,pb.1,pb.2]
  simp [toffoliCount,measurementCount]

theorem program_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (program w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have notT : wires (notRegister (tR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 1029 256 (by omega))
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have ccx1 : wires [.CCX g (w 1028) (w 721)]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl
    · exact G
    · exact I _ (by omega)
    · exact I _ (by omega)
  have ccx2 : wires [.CCX (w 514) (w 1028) (w 722)]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hT : wires (loadTX w g k)⊆(mSites w g).toFinset := by
    simp only [loadTX,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have cmp : wires (compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514) (by simp [hp8,tR,wireBlock_length])
      (by simp [hC2,tR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 1797 (by omega)
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
  have hF : wires (fPart w g k)⊆(mSites w g).toFinset := by
    simp only [fPart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨ccx1,hT⟩,cmp⟩,cxg 514 (by omega)⟩,hT⟩,ccx2⟩
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hKn : wires (knownH w)⊆(mSites w g).toFinset := by
    apply (KnownOutputAdder.program_support _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with (((hq|hq)|hq)|hq)|rfl
    · rw [dBitsX_wire w q hq]; exact I 1028 (by omega)
    · rw [desiredX,mappedRead_wires] at hq; exact B 770 257 (by omega) q hq
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hE : wires (eraseH w)⊆(mSites w g).toFinset := by
    simp only [eraseH,wires_append,Finset.union_subset_iff]
    exact ⟨⟨hW,hKn⟩,hCp⟩
  have hNeg : wires (FastConst.maskedNot g (kR w))⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (kR w) _).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 770 258 (by omega) q hq))
  have hL : wires (loadKX w g k)⊆(mSites w g).toFinset := by
    simp only [loadKX,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hKOld : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (Verifier.Leaf4.zero4KAdd w)⊆(mSites w g).toFinset := by
    apply (Verifier.Leaf4.zero4_support w).trans
    simpa only [←kAdd_literal] using hKOld
  have hM : wires ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] : Program)⊆
      (mSites w g).toFinset := by
    rw [show ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] : Program)=
      [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++[.measureX (w 721) [] [.CZ g (w 1028)]] from rfl,
      wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
        Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hA : wires (addPart w g k)⊆(mSites w g).toFinset := by
    simp only [addPart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨hNeg,hL⟩,hK⟩,hL⟩,hM⟩
  have hRot : wires (rotateLeft (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).2]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hP : wires (parBack w g k)⊆(mSites w g).toFinset := by
    unfold parBack
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hEr : wires (eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1029 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hEF : wires (eraseF w g k)⊆(mSites w g).toFinset := by
    simp only [eraseF,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskT g G _,notT⟩,hEr⟩,notT⟩,mskT g G _⟩
  simp only [program,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨hF,hE⟩,hA⟩,hRot⟩,hP⟩,hEF⟩

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem program_physical (k : Nat) : GatePhysical (program w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gK : g∉kR w := g_out w hn g hg 770 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 1 256 1540 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 1029 256 1540 256 (by omega) (by omega) (by omega)
      have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
      have l2 : (hp8 w++tR w++hC2 w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 1540 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 1797 (by omega) (by omega) (by omega),nb w hn 514 1 256 (by omega) (by omega) (by omega),
          nb w hn 514 1029 256 (by omega) (by omega) (by omega),nb w hn 514 1540 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega),
          nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · simp
  have khP : GatePhysical (knownH w) := by
    unfold knownH
    apply KnownOutputAdder.program_physical
    · rw [dBitsX_length]; simp [hpR,wireBlock_length]
    · rw [desiredX_length]; simp [hpR,wireBlock_length]
    · simp [hC2,hpR,wireBlock_length]
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBitsX w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBitsX_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [desiredX,mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq'
      simp only [List.mem_range'_1] at hi
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne i 1797 (by omega) (by omega) (by omega),nb w hn i 1 257 (by omega) (by omega) (by omega),
        nb w hn i 1540 256 (by omega) (by omega) (by omega)⟩
  have kPOld : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have kP : GatePhysical (Verifier.Leaf4.zero4KAdd w) :=
    Verifier.Leaf4.zero4_gatePhysical_pool w hn (by simpa only [←kAdd_literal] using kPOld)
  have eP : GatePhysical (eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1029 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (tR w++xR w).Nodup := List.nodup_append'.mpr ⟨tR_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (tR w++xR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1029 256 (by omega) (by omega) (by omega),nb w hn 1797 770 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parBack w g k) := by
    unfold parBack
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).2
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h721 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h722 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t721 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadKX w g k) := by
    simp only [loadKX,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h721⟩,maskedConstant_physical _ _ _ h722⟩
  have ltP : GatePhysical (loadTX w g k) := by
    simp only [loadTX,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t721⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have mP : GatePhysical ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] :
      Program) := by
    simp [GatePhysical,PhysicalInstr]
  have fP : GatePhysical (fPart w g k) := by
    simp only [fPart,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),ltP⟩,cmpP⟩,
      cxp _ _ (gn _ (by omega))⟩,ltP⟩,
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have eHP : GatePhysical (eraseH w) := by
    simp only [eraseH,gatePhysical_append]
    exact ⟨⟨w0P,khP⟩,cpP⟩
  have aP : GatePhysical (addPart w g k) := by
    simp only [addPart,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gK,lkP⟩,kP⟩,lkP⟩,mP⟩
  have eFP : GatePhysical (eraseF w g k) := by
    simp only [eraseF,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gT,notRegister_physical _⟩,eP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gT⟩
  simp only [program,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨fP,eHP⟩,aP⟩,rotP⟩,parP⟩,eFP⟩

end Phys

theorem program_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (program w g k)≤22000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).2
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.knownAdder_gateSlots_le (dBitsX w) (desiredX w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (tR w) (xR w) (hC3 w) (w 1797) (w 514)
  have pb : Challenge.gateSlots (parBack w g k)≤6 := by
    unfold parBack; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g1 : Challenge.gateSlots [.CCX g (w 1028) (w 721)]=1 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g2 : Challenge.gateSlots [.CCX (w 514) (w 1028) (w 722)]=1 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g3 : Challenge.gateSlots [.CX g (w 514)]=1 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],
      .measureX (w 721) [] [.CZ g (w 1028)]] : Program)=4 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadKX w g k)≤6*258 := by
    simp only [loadKX,Challenge.gateSlots_append]
    have := x1 (hR w) (c1X k); have := m1 g (hR w) (cgX k); have := m1 (w 514) (hR w) (cfX k)
    have := m1 (w 1028) (hR w) (cpX k); have := m1 (w 721) (hR w) (cgpX k); have := m1 (w 722) (hR w) (cfpX k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadTX w g k)≤2*256 := by
    simp only [loadTX,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrXA k); have := m1 (w 721) (tR w) (thrXB k)
    simp only [tR,wireBlock_length] at *
    omega
  have nT : Challenge.gateSlots (notRegister (tR w))=256 := by
    simp [Baselines.notRegister_gateSlots,tR,wireBlock_length]
  have mT : Challenge.gateSlots (maskedConstant g (tR w) (2^256-1-k))≤256 := by
    have := m1 g (tR w) (2^256-1-k); simpa [tR,wireBlock_length] using this
  have mK : Challenge.gateSlots (FastConst.maskedNot g (kR w))≤258 := by
    have := m1 g (kR w) (2^(kR w).length-1); simpa [FastConst.maskedNot,kR,wireBlock_length] using this
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lp : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  have kOld : Challenge.gateSlots (KAddCallerBridgeResearch.literalKAdd w)≤17*258 := k1
  have kNew : Challenge.gateSlots (Verifier.Leaf4.zero4KAdd w)+21≤17*258 := by
    rw [Verifier.Leaf4.zero4_slots w]
    exact kOld
  rw [dBitsX_length] at h1
  rw [lt] at e1
  rw [lp,lt] at c1'
  simp only [program,fPart,eraseH,addPart,eraseF,knownH,Challenge.gateSlots_append,g1,g2,g3,w0,q1,cp,nT]
  omega

end ECDSAAdd.Entrant.ExitMerge
end
