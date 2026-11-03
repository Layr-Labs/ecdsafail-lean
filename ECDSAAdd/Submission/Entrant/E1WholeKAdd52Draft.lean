import ECDSAAdd.Submission.Entrant.E1CarrySplice52Draft

/-! Private SOURCE-ONLY whole258-bit affine tail bridge.
Only high carry254/255/256 (physical1794/1795/1796) start clean. The real
old literal program supplies the high-output promise; no MF/postWord,
all257-carry clean premise, or global wire-map injectivity is assumed. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1WholeKAdd52Research
open Arithmetic RecordedQuantum Challenge AdderSpineBridgeResearch
open KAddCallerBridgeResearch AffineCarryTail52Research E1CarrySplice52Research

/-- Low prefix is exactly254 bits0..253; its final carry is1793. -/
def flagKAdd52 (w : Nat → Wire) : Program :=
  lowPrefix52 w++forwardTail (actualPorts w) (w 1028)++lowSuffix52 w

def zeroKAdd52 (w : Nat → Wire) : Program :=
  lowPrefix52 w++exitTail (actualPorts w)++lowSuffix52 w

def highCarryClean52 (w : Nat → Wire) (b : BasisState) : Prop :=
  b (w 1794)=false ∧ b (w 1795)=false ∧ b (w 1796)=false

/-- A promise about the actual OLD full literal258 run, with an empty tape. -/
def ForwardOldOutputs52 (w : Nat → Wire) (par : Bool) (s : State) : Prop :=
  (run (literalKAdd w) [] s).basis (w 1027)=par ∧
  ((run (literalKAdd w) [] s).basis (w 1026) ^^
    (run (literalKAdd w) [] s).basis (w 1025))=!par

def ExitOldOutputs52 (w : Nat → Wire) (s : State) : Prop :=
  (run (literalKAdd w) [] s).basis (w 1025)=false ∧
  (run (literalKAdd w) [] s).basis (w 1026)=false ∧
  (run (literalKAdd w) [] s).basis (w 1027)=false

private def prefixState52 (w : Nat → Wire) (s : State) : State :=
  run (lowPrefix52 w) [] s

private theorem run_cat52 (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s=run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

private theorem zero_records52 (p : Program) (h : measurementCount p=0)
    (s : State) (m : List Bool) : run p m s=run p [] s := by
  simpa only [h,List.take_zero] using (run_take p m s).symm

/- Explicit interpreter lemmas are used below; never delta-reduce258 gates
while matching an output bit or rewriting one of the three splice states. -/
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.toffoliCount
  ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots

private theorem run_splice52 (p t r : Program) (hp : measurementCount p=0)
    (ht : measurementCount t=3) (s : State) (m : List Bool) :
    run (p++t++r) m s=run r (m.drop 3) (run t m (run p [] s)) := by
  have pre := zero_records52 p hp s m
  simp only [List.append_assoc,run_cat52,hp,List.drop_zero,ht,pre]

private theorem old_normal_form52 (w : Nat → Wire) (s : State) (m : List Bool) :
    run (literalKAdd w) m s=run (lowSuffix52 w) (m.drop 3)
      (run (oldTail (actualPorts w)) m (prefixState52 w s)) := by
  rw [literal_split_four52]
  exact run_splice52 (lowPrefix52 w) (oldTail (actualPorts w)) (lowSuffix52 w)
    (lowPrefix_records52 w) (old_costs (actualPorts w)).2.1 s m

private theorem flag_normal_form52 (w : Nat → Wire) (s : State) (m : List Bool) :
    run (flagKAdd52 w) m s=run (lowSuffix52 w) (m.drop 3)
      (run (forwardTail (actualPorts w) (w 1028)) m (prefixState52 w s)) := by
  exact run_splice52 (lowPrefix52 w) (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w)
    (lowPrefix_records52 w) (forward_costs (actualPorts w) (w 1028)).2.1 s m

private theorem zero_normal_form52 (w : Nat → Wire) (s : State) (m : List Bool) :
    run (zeroKAdd52 w) m s=run (lowSuffix52 w) (m.drop 3)
      (run (exitTail (actualPorts w)) m (prefixState52 w s)) := by
  exact run_splice52 (lowPrefix52 w) (exitTail (actualPorts w)) (lowSuffix52 w)
    (lowPrefix_records52 w) (exit_costs (actualPorts w)).2.1 s m

/-- Only bounded pool injectivity is used, at these13 exact indices. -/
private theorem tail_nd13_pool52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    ((w 1028)::wireList (actualPorts w)).Nodup := by
  have neq (i j : Nat) (hi : i < 1798) (hj : j < 1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [wireList,actualPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    List.nodup_nil,not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

private theorem prefix_high_clean52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (clean : highCarryClean52 w s.basis) :
    Clean (actualPorts w) (prefixState52 w s).basis := by
  have h0 := lowPrefix_keeps_pool52 w hn 1794 (Or.inr (Or.inr ⟨by decide,by decide⟩)) s []
  have h1 := lowPrefix_keeps_pool52 w hn 1795 (Or.inr (Or.inr ⟨by decide,by decide⟩)) s []
  have h2 := lowPrefix_keeps_pool52 w hn 1796 (Or.inr (Or.inr ⟨by decide,by decide⟩)) s []
  change (prefixState52 w s).basis (w 1794)=false ∧
    (prefixState52 w s).basis (w 1795)=false ∧ (prefixState52 w s).basis (w 1796)=false
  exact ⟨h0.trans clean.1,h1.trans clean.2.1,h2.trans clean.2.2⟩

private theorem prefix_flag52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (par : Bool) (flagIn : s.basis (w 1028)=par) :
    (prefixState52 w s).basis (w 1028)=par := by
  exact (lowPrefix_keeps_pool52 w hn 1028 (Or.inr (Or.inl ⟨by decide,by decide⟩)) s []).trans flagIn

/-- The measured low unwind has no high-b support, so OLD full output at[]
is exactly the old four-bit tail output after the actual low prefix. -/
private theorem literal_high_output52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (j : Nat) (hj : 255 ≤ j ∧ j < 258) :
    (run (literalKAdd w) [] s).basis (w (770+j))=
      (run (oldTail (actualPorts w)) [] (prefixState52 w s)).basis (w (770+j)) := by
  rw [old_normal_form52 w s []]
  simpa only [List.drop_nil] using lowSuffix_keeps_high_sum52 w hn j hj
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) []

/-- Normalize an index with abstract State variables, not a concrete258 run. -/
private theorem bit_index52 (w : Nat → Wire) (u v : State) (j k : Nat)
    (hk : 770+j=k)
    (h : u.basis (w (770+j))=v.basis (w (770+j))) :
    u.basis (w k)=v.basis (w k) := by
  simpa only [hk] using h

private theorem forward_code52 (u v : State) (p : Ports) (q1 q2 q3 : Wire) (par : Bool)
    (p1 : p.b1=q1) (p2 : p.b2=q2) (p3 : p.b3=q3)
    (b1 : u.basis q1=v.basis q1) (b2 : u.basis q2=v.basis q2) (b3 : u.basis q3=v.basis q3)
    (promise : u.basis q3=par ∧ ((u.basis q2 ^^ u.basis q1)=!par)) :
    v.basis p.b3=par ∧ ((v.basis p.b2 ^^ v.basis p.b1)=!par) := by
  rw [p1,p2,p3]
  exact ⟨b3.symm.trans promise.1,
    (congrArg₂ (fun a b : Bool => a^^b) b2.symm b1.symm).trans promise.2⟩

private theorem exit_code52 (u v : State) (p : Ports) (q1 q2 q3 : Wire)
    (p1 : p.b1=q1) (p2 : p.b2=q2) (p3 : p.b3=q3)
    (b1 : u.basis q1=v.basis q1) (b2 : u.basis q2=v.basis q2) (b3 : u.basis q3=v.basis q3)
    (promise : u.basis q1=false ∧ u.basis q2=false ∧ u.basis q3=false) :
    v.basis p.b1=false ∧ v.basis p.b2=false ∧ v.basis p.b3=false := by
  rw [p1,p2,p3]
  exact ⟨b1.symm.trans promise.1,b2.symm.trans promise.2.1,b3.symm.trans promise.2.2⟩

private theorem forward_promise_after_prefix52 (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (par : Bool)
    (promise : ForwardOldOutputs52 w par s) :
    ForwardPromise (actualPorts w) par (prefixState52 w s) := by
  have b1 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 255 1025 rfl
    (literal_high_output52 w hn s 255 ⟨by decide,by decide⟩)
  have b2 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 256 1026 rfl
    (literal_high_output52 w hn s 256 ⟨by decide,by decide⟩)
  have b3 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 257 1027 rfl
    (literal_high_output52 w hn s 257 ⟨by decide,by decide⟩)
  exact forward_code52 (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s))
    (actualPorts w) (w 1025) (w 1026) (w 1027) par rfl rfl rfl b1 b2 b3 promise

private theorem exit_promise_after_prefix52 (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (promise : ExitOldOutputs52 w s) :
    ExitPromise (actualPorts w) (prefixState52 w s) := by
  have b1 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 255 1025 rfl
    (literal_high_output52 w hn s 255 ⟨by decide,by decide⟩)
  have b2 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 256 1026 rfl
    (literal_high_output52 w hn s 256 ⟨by decide,by decide⟩)
  have b3 := bit_index52 w (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s)) 257 1027 rfl
    (literal_high_output52 w hn s 257 ⟨by decide,by decide⟩)
  exact exit_code52 (run (literalKAdd w) [] s)
    (run (oldTail (actualPorts w)) [] (prefixState52 w s))
    (actualPorts w) (w 1025) (w 1026) (w 1027) rfl rfl rfl b1 b2 b3 promise

/-- Complete actual258 program State equality, for every full/short/empty tape.
Only the high three initially-clean carry bits and the actual OLD output code
are required; every low carry may have an arbitrary initial value. -/
theorem flag_run_eq52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (clean : highCarryClean52 w s.basis)
    (par : Bool) (flagIn : s.basis (w 1028)=par) (promise : ForwardOldOutputs52 w par s) :
    run (flagKAdd52 w) m s=run (literalKAdd w) m s := by
  have localEq := forward_tail_eq_old (actualPorts w) (w 1028) (tail_nd13_pool52 w hn)
    (prefixState52 w s) (prefix_high_clean52 w hn s clean) par
    (prefix_flag52 w hn s par flagIn) (forward_promise_after_prefix52 w hn s par promise) m
  rw [flag_normal_form52 w s m,old_normal_form52 w s m]
  exact congrArg (fun t => run (lowSuffix52 w) (m.drop 3) t) localEq

theorem zero_run_eq52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (clean : highCarryClean52 w s.basis)
    (promise : ExitOldOutputs52 w s) :
    run (zeroKAdd52 w) m s=run (literalKAdd w) m s := by
  have nd12 := (List.nodup_cons.mp (tail_nd13_pool52 w hn)).2
  have localEq := exit_tail_eq_old (actualPorts w) nd12 (prefixState52 w s)
    (prefix_high_clean52 w hn s clean) (exit_promise_after_prefix52 w hn s promise) m
  rw [zero_normal_form52 w s m,old_normal_form52 w s m]
  exact congrArg (fun t => run (lowSuffix52 w) (m.drop 3) t) localEq

private theorem splice_counts52 (p old new r : Program) (dt ds : Nat)
    (ht : toffoliCount new+dt=toffoliCount old)
    (hm : measurementCount new=measurementCount old)
    (hs : gateSlots new+ds=gateSlots old) :
    toffoliCount (p++new++r)+dt=toffoliCount (p++old++r) ∧
    measurementCount (p++new++r)=measurementCount (p++old++r) ∧
    gateSlots (p++new++r)+ds=gateSlots (p++old++r) := by
  refine ⟨?_,?_,?_⟩
  · simp only [toffoliCount_append]
    omega
  · simp only [measurementCount_append]
    omega
  · simp only [gateSlots_append]
    omega

private theorem flag_tail_deltas52 (p : Ports) (flag : Wire) :
    toffoliCount (forwardTail p flag)+2=toffoliCount (oldTail p) ∧
    measurementCount (forwardTail p flag)=measurementCount (oldTail p) ∧
    gateSlots (forwardTail p flag)+2=gateSlots (oldTail p) := by
  have old := old_costs p
  have new := forward_costs p flag
  refine ⟨?_,?_,?_⟩
  · rw [new.1,old.1]
  · exact new.2.1.trans old.2.1.symm
  · rw [new.2.2,old.2.2]

private theorem zero_tail_deltas52 (p : Ports) :
    toffoliCount (exitTail p)+3=toffoliCount (oldTail p) ∧
    measurementCount (exitTail p)=measurementCount (oldTail p) ∧
    gateSlots (exitTail p)+12=gateSlots (oldTail p) := by
  have old := old_costs p
  have new := exit_costs p
  refine ⟨?_,?_,?_⟩
  · rw [new.1,old.1]
  · exact new.2.1.trans old.2.1.symm
  · rw [new.2.2,old.2.2]

/-- Exact whole-adder syntax deltas; these do not assert a caller/candidate score. -/
theorem flag_counts52 (w : Nat → Wire) :
    toffoliCount (flagKAdd52 w)+2=toffoliCount (literalKAdd w) ∧
    measurementCount (flagKAdd52 w)=measurementCount (literalKAdd w) ∧
    gateSlots (flagKAdd52 w)+2=gateSlots (literalKAdd w) := by
  have delta := flag_tail_deltas52 (actualPorts w) (w 1028)
  have h := splice_counts52 (lowPrefix52 w) (oldTail (actualPorts w))
    (forwardTail (actualPorts w) (w 1028)) (lowSuffix52 w) 2 2 delta.1 delta.2.1 delta.2.2
  exact ⟨h.1.trans (congrArg toffoliCount (literal_split_four52 w)).symm,
    h.2.1.trans (congrArg measurementCount (literal_split_four52 w)).symm,
    h.2.2.trans (congrArg gateSlots (literal_split_four52 w)).symm⟩

theorem zero_counts52 (w : Nat → Wire) :
    toffoliCount (zeroKAdd52 w)+3=toffoliCount (literalKAdd w) ∧
    measurementCount (zeroKAdd52 w)=measurementCount (literalKAdd w) ∧
    gateSlots (zeroKAdd52 w)+12=gateSlots (literalKAdd w) := by
  have delta := zero_tail_deltas52 (actualPorts w)
  have h := splice_counts52 (lowPrefix52 w) (oldTail (actualPorts w))
    (exitTail (actualPorts w)) (lowSuffix52 w) 3 12 delta.1 delta.2.1 delta.2.2
  exact ⟨h.1.trans (congrArg toffoliCount (literal_split_four52 w)).symm,
    h.2.1.trans (congrArg measurementCount (literal_split_four52 w)).symm,
    h.2.2.trans (congrArg gateSlots (literal_split_four52 w)).symm⟩

#print axioms flag_run_eq52
#print axioms zero_run_eq52
#print axioms flag_counts52
#print axioms zero_counts52
end ECDSAAdd.Entrant.E1WholeKAdd52Research
