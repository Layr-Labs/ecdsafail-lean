import ECDSAAdd.Submission.Entrant.TerminalFiveSample
import ECDSAAdd.Submission.Entrant.TerminalFiveLiveSupport

namespace ECDSAAdd.Entrant.InverseFive23
open ECDSAAdd Arithmetic MappedCompressed Challenge History5 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward regularForward

def candidate15 : Program := TerminalFiveBridge.physical

def reverseTail15 (isA : Bool) : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15) ++
    Rolling1588.reverse isA 1 505

def stackReverse15 (isA : Bool) : Program := renameProgram (sig 511) tickR ++ reverseTail15 isA

theorem resources : toffoliCount candidate15=23 ∧ measurementCount candidate15=16 ∧
    Challenge.gateSlots candidate15=1633 := by
  have h:=TerminalInverse23.counts
  simpa only [candidate15,TerminalFiveBridge.physical,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots] using h

theorem old_resources : toffoliCount TerminalFivePlacement.old=24 ∧
    measurementCount TerminalFivePlacement.old=16 ∧ Challenge.gateSlots TerminalFivePlacement.old=1482 := by
  have a:=Inverse14Width.resources
  have b : toffoliCount (W.ReverseCarry.compactReceiverTick base 506)=10 ∧
      measurementCount (W.ReverseCarry.compactReceiverTick base 506)=5 ∧
      Challenge.gateSlots (W.ReverseCarry.compactReceiverTick base 506)=109 := by decide +kernel
  simp only [TerminalFivePlacement.old,TerminalFivePlacement.shiftedReceiver,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

theorem candidate_physical : GatePhysical candidate15 :=
  gatePhysical_rename TerminalFiveBridge.perm TerminalFiveBridge.perm.injective _ TerminalInverse23.physical

theorem pack506 (isA : Bool) : Rolling1588.Integer.packAfter base isA 506=[] := by
  simp only [Rolling1588.Integer.packAfter,show History5.packDue 506=false from by decide,Bool.false_eq_true,if_false]

theorem pack_inverse15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 506 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510) mD
      (run (Rolling1588.Integer.packAfter base isA 510) mE (run TerminalFiveBridge.forward [] a))=
        run TerminalFiveBridge.forward [] a := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32≤2^256 := by norm_num [p]
  let b:=run (W.repairedTick base 506) [] a
  have stage507 : Stage base isA x p 507 b.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 506
      hp0 hx0 hpo hp gap hx cop (by omega) a [] stage).2
    simpa only [pack506,List.append_nil,b] using h
  have same : run TerminalFiveBridge.forward [] a=run (MorningFour.tick507++tripF) [] b := by
    rw [TerminalFiveBridge.forward,run_append]
    simp only [List.take_nil,List.drop_nil,b]
  rw [same]
  exact InverseFour15.pack_inverse15 isA x hx0 hx b stage507 mE mD

theorem decoded_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 506 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ candidate15) mD
      (run (Rolling1588.Integer.packAfter base isA 510) mE (run TerminalFiveBridge.forward [] a))=
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ TerminalFivePlacement.old) mD
      (run (Rolling1588.Integer.packAfter base isA 510) mE (run TerminalFiveBridge.forward [] a)) := by
  rw [run_append (Rolling1588.Integer.decodeBefore base isA 510) candidate15,
    run_append (Rolling1588.Integer.decodeBefore base isA 510) TerminalFivePlacement.old,
    pack_inverse15 isA x hx0 hx a stage mE]
  exact TerminalFiveSample.stage_replace isA x hx0 hx a _ stage _ _ (fun _ _=>rfl)

theorem sites_pool15 : TerminalFiveDomain.sites.toFinset ⊆ (skywalkPoolWires base).toFinset := by
  let indices : List Nat := [505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 1534, 1535, 1536, 1537, 1538, 1540, 1541, 1542, 1543, 1544]
  have layout : TerminalFiveDomain.sites=indices.map base := by decide +kernel
  have bounds : indices.all (fun i=>Nat.blt i 1798)=true := by decide +kernel
  intro q hq
  have member := List.mem_toFinset.mp hq
  rw [layout] at member
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
  have small:=List.all_eq_true.mp bounds i hi
  exact List.mem_toFinset.mpr (OB5.base_pool i (Nat.blt_eq.mp small))

theorem decoded_replace_pool15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 506 a.basis) (mE mD : List Bool)
    (agree : ∀q∈skywalkPoolWires base,
      u.basis q=(run (TerminalFiveBridge.forward++Rolling1588.Integer.packAfter base isA 510) mE a).basis q) :
    run (Rolling1588.Integer.decodeBefore base isA 510++candidate15) mD u=
      run (Rolling1588.Integer.decodeBefore base isA 510++TerminalFivePlacement.old) mD u := by
  let f:=TerminalFiveBridge.forward
  let codec:=Rolling1588.Integer.decodeBefore base isA 510
  let ref:=run (Rolling1588.Integer.packAfter base isA 510) mE (run f [] a)
  have dec : wires codec⊆(skywalkPoolWires base).toFinset := by
    have h:=(History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←decodeBefore_support_eq base isA 510] at h
    exact h
  have sc : wires (codec++candidate15)⊆(skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,TerminalFiveSample.physical_support.trans sites_pool15⟩
  have so : wires (codec++TerminalFivePlacement.old)⊆(skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,TerminalFiveSample.old_support.trans sites_pool15⟩
  apply Stack5.local_replace _ _ _ sc so u ref mD mD
  · intro q hq
    have e1:=congrFun (run_basis_records (f++Rolling1588.Integer.packAfter base isA 510) a a mE [] rfl) q
    have e2:=congrFun (run_basis_records (Rolling1588.Integer.packAfter base isA 510) (run f [] a) (run f [] a) [] mE rfl) q
    have e3 : (run (f++Rolling1588.Integer.packAfter base isA 510) [] a).basis q=
        (run (Rolling1588.Integer.packAfter base isA 510) [] (run f [] a)).basis q := by
      rw [run_append]; simp only [List.take_nil,List.drop_nil]
    exact (agree q (List.mem_toFinset.mp hq)).trans (e1.trans (e3.trans e2))
  · exact decoded_replace15 isA x hx0 hx a stage mE mD

theorem tail_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 506 a.basis) (mE mD : List Bool)
    (agree : ∀q∈skywalkPoolWires base,
      u.basis q=(run (TerminalFiveBridge.forward++Rolling1588.Integer.packAfter base isA 510) mE a).basis q) :
    run (reverseTail15 isA) mD (pullState (sig 510) u)=
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++TerminalFivePlacement.old)++
      Rolling1588.reverse isA 1 505) mD (pullState (sig 510) u) := by
  have count : measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++candidate15))=
      measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++TerminalFivePlacement.old)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,
      measurementCount_append,measurementCount_append,resources.2.1,old_resources.2.1]
  rw [reverseTail15,
    run_append (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++candidate15))
      (Rolling1588.reverse isA 1 505),
    run_append (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++TerminalFivePlacement.old))
      (Rolling1588.reverse isA 1 505),count]
  rw [InverseFour15.unpack51015,OB5.run_rename 510 (by omega),OB5.run_rename 510 (by omega),
    decoded_replace_pool15 isA x hx0 hx a u stage mE _ agree]

theorem tail_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (u : State) (hu : ∀q∈skywalkPoolWires base,
      u.basis q=(run (regularForward base isA 1 510) mE s1).basis q) (mD : List Bool) :
    run (reverseTail15 isA) mD (pullState (sig 510) u)=
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++TerminalFivePlacement.old)++
      Rolling1588.reverse isA 1 505) mD (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32≤2^256 := by norm_num [p]
  let k:=measurementCount (regularForward base isA 1 505)
  have stage0 : Stage base isA x p 506
      (run (regularForward base isA 1 505)
        (mE.take (measurementCount (regularForward base isA 1 505))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 505
      hp0 hx0 hpo hp gap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  change Stage base isA x p 506 (run (regularForward base isA 1 505) (mE.take k) s1).basis at stage0
  obtain ⟨a,ha⟩ : ∃a : State,run (regularForward base isA 1 505) (mE.take k) s1=a := ⟨_,rfl⟩
  rw [ha] at stage0
  have fwdP : regularForward base isA 1 510=regularForward base isA 1 505 ++
      (TerminalFiveBridge.forward++Rolling1588.Integer.packAfter base isA 510) := by
    rw [regularForward_snoc base isA 1 509,show (1:Nat)+509=510 by rfl,
      regularForward_snoc base isA 1 508,show (1:Nat)+508=509 by rfl,
      regularForward_snoc base isA 1 507,show (1:Nat)+507=508 by rfl,
      regularForward_snoc base isA 1 506,show (1:Nat)+506=507 by rfl,
      regularForward_snoc base isA 1 505,show (1:Nat)+505=506 by rfl,
      pack506,MorningPlacement.pack507,pack508,pack509,
      MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
    simp only [TerminalFiveBridge.forward,tripF,List.append_assoc,List.append_nil]
  have agree : ∀q∈skywalkPoolWires base,
      u.basis q=(run (TerminalFiveBridge.forward++Rolling1588.Integer.packAfter base isA 510) (mE.drop k) a).basis q := by
    intro q hq
    rw [hu q hq,fwdP,run_append,←show measurementCount (regularForward base isA 1 505)=k from rfl,ha]
  exact tail_replace15 isA x hx0 hx a u stage0 (mE.drop k) mD agree


theorem reverse_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base isA 1 511) mE s1).basis q) (mD : List Bool) :
    run (stackReverse15 isA) mD (pullState (sig 511) t5)=
      run (InverseFour15.stackReverse15 isA) mD (pullState (sig 511) t5) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base isA x p 511
      (run (regularForward base isA 1 510)
        (mE.take (measurementCount (regularForward base isA 1 510))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  have whole : run (regularForward base isA 1 510)
      (mE.take (measurementCount (regularForward base isA 1 510))) s1=
        run (regularForward base isA 1 510) mE s1 := run_take _ mE s1
  have last : run (regularForward base isA 1 511) mE s1=
      run (W.repairedTick base 511) (mE.drop (measurementCount (regularForward base isA 1 510)))
        (run (regularForward base isA 1 510)
          (mE.take (measurementCount (regularForward base isA 1 510))) s1) := by
    rw [regularForward_snoc base isA 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base isA 1 510)
    (mE.take (measurementCount (regularForward base isA 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits isA x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero isA x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have cn : measurementCount (renameProgram (sig 511) tickR)=0 :=
    (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
  rw [stackReverse15,TerminalFivePlacement.reverse_shape,run_append,run_append,cn]
  simp only [List.take_zero,List.drop_zero]
  rw [OB5.run_rename 511 (by omega),tickR_run,move]
  exact tail_actual15 isA x hx0 hx s1 mE first _
    (fun q hq => (uAgree q hq).trans (congrArg (fun st : State => st.basis q) whole)) mD

theorem stack_roundtrip15 (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackReverse15 isA) mD (run (Rolling1588TickGap.stackForward isA) mE s)=s := by
  have fwd : run (Rolling1588TickGap.stackForward isA) mE s =
      pullState (sig 511) (run (regularForward base isA 1 511) mE s) := by
    rw [Rolling1588TickGap.stackForward_run_eq isA x hx0 hx s mE first,
      ←Rolling1588.Integer.stackForward_eq_packets,Rolling1588.Integer.stackForwardT_run isA hn hlo x hx0 hx s mE first,
      Rolling1588.Integer.forward_run isA x hx0 hx s mE first]
  rw [fwd, reverse_actual15 isA x hx0 hx s mE first _ (fun _ _ => rfl) mD,←fwd]
  exact InverseFour15.stack_roundtrip15 isA hn hlo x hx0 hx s mE mD first


attribute [local irreducible] candidate15 TerminalFivePlacement.old stackReverse15 reverseTail15
  InverseFour15.stackReverse15

theorem stack_delta (isA : Bool) :
    toffoliCount (stackReverse15 isA)+1=toffoliCount (InverseFour15.stackReverse15 isA) ∧
    measurementCount (stackReverse15 isA)=measurementCount (InverseFour15.stackReverse15 isA) ∧
    Challenge.gateSlots (stackReverse15 isA)=Challenge.gateSlots (InverseFour15.stackReverse15 isA)+151 := by
  have fresh:=resources
  have old:=old_resources
  rw [TerminalFivePlacement.reverse_shape]
  simp only [stackReverse15,reverseTail15,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    Baselines.rename_gateSlots]
  omega

theorem stack_subset (isA : Bool) : wires (stackReverse15 isA)⊆wires (InverseFour15.stackReverse15 isA) := by
  have ren (P Q : Program) : renameProgram (sig 510) (P++Q)=
      renameProgram (sig 510) P++renameProgram (sig 510) Q := by
    simp only [renameProgram,List.map_append]
  have oldPlace : wires (renameProgram (sig 510) TerminalFivePlacement.old)=
      wires (renameProgram (sig 510) Inverse14Width.candidate) ∪
        wires (renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506)) := by
    rw [TerminalFivePlacement.old_placed,wires_append]
  have block : wires (renameProgram (sig 510) candidate15)⊆
      wires (renameProgram (sig 510) TerminalFivePlacement.old) ∪
        wires (Rolling1588.reverse isA 1 505) := by
    have sub:=TerminalFiveLiveSupport.placed_local
    rw [←oldPlace] at sub
    intro q hq
    have used:=sub (by simpa only [candidate15] using hq)
    rcases Finset.mem_union.mp used with oldsite | borrowed
    · exact Finset.mem_union_left _ oldsite
    · exact Finset.mem_union_right _ (TerminalBorrowB.reverse_sites isA borrowed)
  intro q hq
  have move : q∈wires (renameProgram (sig 510) candidate15) →
      q∈wires (renameProgram (sig 510) TerminalFivePlacement.old) ∨
        q∈wires (Rolling1588.reverse isA 1 505) := fun used=>Finset.mem_union.mp (block used)
  rw [stackReverse15,reverseTail15] at hq
  rw [TerminalFivePlacement.reverse_shape]
  simp only [ren,wires_append,Finset.mem_union] at hq ⊢
  tauto

open Arithmetic.DirectSkywalk

def lastPhase15 (isA : Bool) : Program :=
  skywalkArithmeticClear base ++ stackReverse15 isA ++ FrontierEntry1591NativeH.inverse base

theorem last_subset (isA : Bool) : wires (lastPhase15 isA)⊆wires (InverseFour15.lastPhase15 isA) := by
  intro q hq
  have sub:=stack_subset isA
  simp only [lastPhase15,InverseFour15.lastPhase15,wires_append,Finset.mem_union] at hq ⊢
  have move : q∈wires (stackReverse15 isA) → q∈wires (InverseFour15.stackReverse15 isA) := fun used=>sub used
  tauto

theorem last_pool15 (isA : Bool) : wires (lastPhase15 isA)⊆(skywalkPoolWires base).toFinset :=
  (last_subset isA).trans (InverseFour15.last_pool15 isA)

theorem last_hosts_free15 (isA : Bool) (q : Wire) (hq : q∈Rolling1588Lifetime.phaseHosts) : q∉wires (lastPhase15 isA) :=
  fun used=>InverseFour15.last_hosts_free15 isA q hq (last_subset isA used)

theorem last_extra15 (isA : Bool) : wires (lastPhase15 isA)⊆wires (Rolling1588.lastPhase isA)∪{530} :=
  (last_subset isA).trans (InverseFour15.last_extra15 isA)

theorem stack_physical (isA : Bool) : GatePhysical (stackReverse15 isA) := by
  have old:=InverseFour15.last_physical15 isA
  simp only [InverseFour15.lastPhase15,gatePhysical_append] at old
  have stack : GatePhysical (InverseFour15.stackReverse15 isA) := by tauto
  rw [TerminalFivePlacement.reverse_shape] at stack
  have ren (P Q : Program) : renameProgram (sig 510) (P++Q)=
      renameProgram (sig 510) P++renameProgram (sig 510) Q := by
    simp only [renameProgram,List.map_append]
  have inj : Function.Injective (sig 510) := by
    intro a b equal
    have e:=congrArg (sig 510) equal
    simpa only [sig_invol 510 (by omega)] using e
  have fresh:=gatePhysical_rename (sig 510) inj candidate15 candidate_physical
  simp only [ren,gatePhysical_append] at stack
  simp only [stackReverse15,reverseTail15,ren,gatePhysical_append]
  tauto

theorem last_physical15 (isA : Bool) : GatePhysical (lastPhase15 isA) := by
  have old:=InverseFour15.last_physical15 isA
  have stack:=stack_physical isA
  simp only [InverseFour15.lastPhase15,gatePhysical_append] at old
  simp only [lastPhase15,gatePhysical_append]
  tauto

theorem reverse_metrics_new (isA : Bool) :
    toffoliCount (stackReverse15 isA)+3=toffoliCount (Rolling1588.stackReverse isA) ∧
    measurementCount (stackReverse15 isA)=measurementCount (Rolling1588.stackReverse isA) ∧
    Challenge.gateSlots (stackReverse15 isA)=Challenge.gateSlots (Rolling1588.stackReverse isA)+1235 := by
  have fresh:=stack_delta isA
  have old:=InverseFour15.reverse_metrics_new isA
  omega

end ECDSAAdd.Entrant.InverseFive23
