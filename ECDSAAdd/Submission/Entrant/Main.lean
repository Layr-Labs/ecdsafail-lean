import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ExactBorrowErase
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.DisjointPrograms
import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Submission.Entrant.Prelude
import ECDSAAdd.Submission.Entrant.MainPart07


-- Consolidated source module: ParityCarry
section

namespace ECDSAAdd.Entrant.ParityCarry
open ECDSAAdd Arithmetic Challenge
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem majority_one_one (a b cin carry : Wire) (hn : [a,b,cin,carry].Nodup)
    (s : State) (m : List Bool) (ha : s.basis a=true) (hc : s.basis cin=true) :
    run (majority a b cin carry) m s=run [.X carry] m s := by
  rw [majority_correct a b cin carry hn]
  simp [carryBit,ha,hc,run]

theorem borrow_zero_zero (a b cin carry : Wire) (hn : [a,b,cin,carry].Nodup)
    (s : State) (m : List Bool) (hb : s.basis b=false) (hc : s.basis cin=false) :
    run (borrowMajority a b cin carry) m s=s := by
  rw [borrowMajority_correct a b cin carry hn]
  simp [carryBit,hb,hc,writeBit]

def compareChainHeadOne (x y carry : List Wire) (cin target : Wire) : Program :=
  match x,y,carry with
  | a::as,b::bs,c::cs => [.X c]++compareChain none as bs cs c target++eraseCarry a b cin c
  | _,_,_ => compareChain none x y carry cin target

def compareLtHeadOne (x y carry : List Wire) (cin target : Wire) : Program :=
  notRegister (cin::y)++compareChainHeadOne x y carry cin target++notRegister (cin::y)

def eraseLtHeadZero (x y carry : List Wire) (cin target : Wire) : Program :=
  match x,y,carry with
  | a::a'::as,b::b'::bs,c::cs =>
      eraseLtChain (a'::as) (b'::bs) cs c target++eraseBorrow a b cin c
  | _,_,_ => eraseLtChain x y carry cin target

theorem compareChainHeadOne_eq (a b c : Wire) (as bs cs : List Wire) (cin target : Wire)
    (hn : [a,b,cin,c].Nodup) (s : State) (m : List Bool)
    (ha : s.basis a=true) (hc : s.basis cin=true) :
    run (compareChainHeadOne (a::as) (b::bs) (c::cs) cin target) m s=
      run (compareChain none (a::as) (b::bs) (c::cs) cin target) m s := by
  simp only [compareChainHeadOne,compareChain,List.append_assoc,run_append,
    measurementCount_append]
  rw [majority_one_one a b cin c hn s _ ha hc]
  rfl

theorem eraseLtHeadZero_eq (a a' b b' c : Wire) (as bs cs : List Wire) (cin target : Wire)
    (hn : [a,b,cin,c].Nodup) (s : State) (m : List Bool)
    (hb : s.basis b=false) (hc : s.basis cin=false) :
    run (eraseLtHeadZero (a::a'::as) (b::b'::bs) (c::cs) cin target) m s=
      run (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) m s := by
  simp only [eraseLtHeadZero,eraseLtChain,List.append_assoc,run_append]
  rw [borrow_zero_zero a b cin c hn s _ hb hc]
  rfl

theorem compareChainHeadOne_counts (a b c : Wire) (as bs cs : List Wire) (cin target : Wire) :
    toffoliCount (compareChainHeadOne (a::as) (b::bs) (c::cs) cin target)+1=
      toffoliCount (compareChain none (a::as) (b::bs) (c::cs) cin target) ∧
    measurementCount (compareChainHeadOne (a::as) (b::bs) (c::cs) cin target)=
      measurementCount (compareChain none (a::as) (b::bs) (c::cs) cin target) ∧
    gateSlots (compareChainHeadOne (a::as) (b::bs) (c::cs) cin target)+5=
      gateSlots (compareChain none (a::as) (b::bs) (c::cs) cin target) := by
  simp [compareChainHeadOne,compareChain,majority,toffoliCount_append,measurementCount_append,
    gateSlots_append,toffoliCount,measurementCount,gateSlots,instructionSlots]
  omega

theorem eraseLtHeadZero_counts (a a' b b' c : Wire) (as bs cs : List Wire) (cin target : Wire) :
    toffoliCount (eraseLtHeadZero (a::a'::as) (b::b'::bs) (c::cs) cin target)+1=
      toffoliCount (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) ∧
    measurementCount (eraseLtHeadZero (a::a'::as) (b::b'::bs) (c::cs) cin target)=
      measurementCount (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) ∧
    gateSlots (eraseLtHeadZero (a::a'::as) (b::b'::bs) (c::cs) cin target)+8=
      gateSlots (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) := by
  simp [eraseLtHeadZero,eraseLtChain,borrowMajority,majority,toffoliCount_append,
    measurementCount_append,gateSlots_append,toffoliCount,measurementCount,gateSlots,instructionSlots]
  omega

theorem compareLtHeadOne_eq (a b c : Wire) (as bs cs : List Wire) (cin target : Wire)
    (hn : [a,b,cin,c].Nodup) (hy : (cin::b::bs).Nodup) (hao : a∉cin::b::bs)
    (s : State) (m : List Bool) (ha : s.basis a=true) (hc : s.basis cin=false) :
    run (compareLtHeadOne (a::as) (b::bs) (c::cs) cin target) m s=
      run (compareLt none (a::as) (b::bs) (c::cs) cin target) m s := by
  let P:=notRegister (cin::b::bs)
  let t:=run P m s
  have tr:=notRegister_correct (cin::b::bs) hy s m
  have ta : t.basis a=true := by
    change (run (notRegister (cin::b::bs)) m s).basis a=true
    rw [tr]
    change (if a∈cin::b::bs then !s.basis a else s.basis a)=true
    rw [if_neg hao]
    exact ha
  have tc : t.basis cin=true := by simp [t,P,tr,hc]
  have eqn:=compareChainHeadOne_eq a b c as bs cs cin target hn t m ta tc
  have cnt:measurementCount (compareChainHeadOne (a::as) (b::bs) (c::cs) cin target)=
      measurementCount (compareChain none (a::as) (b::bs) (c::cs) cin target):=
    (compareChainHeadOne_counts a b c as bs cs cin target).2.1
  have pc:measurementCount P=0 := (notRegister_counts _).2
  simp only [compareLtHeadOne,compareLt,List.append_assoc,run_append,run_take]
  change run P _ (run (compareChainHeadOne _ _ _ cin target) _ (run P _ s))=
    run P _ (run (compareChain none _ _ _ cin target) _ (run P _ s))
  simp only [(notRegister_counts (cin::b::bs)).2,List.drop_zero]
  rw [show run P m s=t from rfl,eqn,cnt]

theorem borrow_one_zero (a b cin carry : Wire) (hn : [a,b,cin,carry].Nodup)
    (s : State) (m : List Bool) (ha : s.basis a=true) (hc : s.basis cin=false) :
    run (borrowMajority a b cin carry) m s=s := by
  rw [borrowMajority_correct a b cin carry hn]
  simp [carryBit,ha,hc,writeBit]

theorem eraseLtHeadOne_eq (a a' b b' c : Wire) (as bs cs : List Wire) (cin target : Wire)
    (hn : [a,b,cin,c].Nodup) (s : State) (m : List Bool)
    (ha : s.basis a=true) (hc : s.basis cin=false) :
    run (eraseLtHeadZero (a::a'::as) (b::b'::bs) (c::cs) cin target) m s=
      run (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) m s := by
  simp only [eraseLtHeadZero,eraseLtChain,List.append_assoc,run_append]
  rw [borrow_one_zero a b cin c hn s _ ha hc]
  rfl

theorem heads_nodup (a b c cin : Wire) (as bs cs : List Wire)
    (hn : (cin::((a::as)++(b::bs)++(c::cs))).Nodup) : [a,b,cin,c].Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h:=List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem right_nodup (a b c cin : Wire) (as bs cs : List Wire)
    (hn : (cin::((a::as)++(b::bs)++(c::cs))).Nodup) : (cin::b::bs).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h:=List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem left_outside (a b c cin : Wire) (as bs cs : List Wire)
    (hn : (cin::((a::as)++(b::bs)++(c::cs))).Nodup) : a∉cin::b::bs := by
  intro mem
  have hp:=List.count_pos_iff.mpr mem
  have h:=List.nodup_iff_count.mp hn a
  simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h hp
  omega

theorem reg_head_mod (a : Wire) (as : List Wire) (s : BasisState) :
    regValue (a::as) s%2=if s a then 1 else 0 := by
  cases ha:s a <;> simp [regValue,ha,Nat.add_mod,Nat.mul_mod]

theorem reg_head_one (a : Wire) (as : List Wire) (s : BasisState) (N : Nat)
    (hv : regValue (a::as) s=N) (ho : N%2=1) : s a=true := by
  have h:=reg_head_mod a as s
  rw [hv,ho] at h
  cases hs:s a
  · simp only [hs,Bool.false_eq_true,ite_false] at h
    contradiction
  · rfl

theorem compareLtHeadOne_counts (a b c : Wire) (as bs cs : List Wire) (cin target : Wire) :
    toffoliCount (compareLtHeadOne (a::as) (b::bs) (c::cs) cin target)+1=
      toffoliCount (compareLt none (a::as) (b::bs) (c::cs) cin target) ∧
    measurementCount (compareLtHeadOne (a::as) (b::bs) (c::cs) cin target)=
      measurementCount (compareLt none (a::as) (b::bs) (c::cs) cin target) ∧
    gateSlots (compareLtHeadOne (a::as) (b::bs) (c::cs) cin target)+5=
      gateSlots (compareLt none (a::as) (b::bs) (c::cs) cin target) := by
  have h:=compareChainHeadOne_counts a b c as bs cs cin target
  simp only [compareLtHeadOne,compareLt,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem compareChainHeadOne_wires (a b c : Wire) (as bs cs : List Wire) (cin target : Wire) :
    wires (compareChainHeadOne (a::as) (b::bs) (c::cs) cin target)⊆
      wires (compareChain none (a::as) (b::bs) (c::cs) cin target) := by
  have h : wires ([.X c]:Program)⊆wires (majority a b cin c) := by
    simp [majority,wires,Instr.wires]
  simp only [compareChainHeadOne,compareChain,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union h (Finset.Subset.refl _))
    (Finset.Subset.refl _)

theorem compareLtHeadOne_wires (a b c : Wire) (as bs cs : List Wire) (cin target : Wire) :
    wires (compareLtHeadOne (a::as) (b::bs) (c::cs) cin target)⊆
      wires (compareLt none (a::as) (b::bs) (c::cs) cin target) := by
  have h:=compareChainHeadOne_wires a b c as bs cs cin target
  simp only [compareLtHeadOne,compareLt,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h)
    (Finset.Subset.refl _)

theorem eraseLtHeadZero_wires (a a' b b' c : Wire) (as bs cs : List Wire) (cin target : Wire) :
    wires (eraseLtHeadZero (a::a'::as) (b::b'::bs) (c::cs) cin target)⊆
      wires (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) := by
  change wires (eraseLtChain (a'::as) (b'::bs) cs c target++eraseBorrow a b cin c)⊆
    wires (borrowMajority a b cin c++eraseLtChain (a'::as) (b'::bs) cs c target++eraseBorrow a b cin c)
  simp only [wires_append]
  exact Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl _)

theorem compareChainHeadOne_physical (a b c : Wire) (as bs cs : List Wire) (cin target : Wire)
    (h : GatePhysical (compareChain none (a::as) (b::bs) (c::cs) cin target)) :
    GatePhysical (compareChainHeadOne (a::as) (b::bs) (c::cs) cin target) := by
  simp only [compareChain,gatePhysical_append] at h
  simp only [compareChainHeadOne,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate],h.1.2⟩,h.2⟩

theorem compareLtHeadOne_physical (a b c : Wire) (as bs cs : List Wire) (cin target : Wire)
    (h : GatePhysical (compareLt none (a::as) (b::bs) (c::cs) cin target)) :
    GatePhysical (compareLtHeadOne (a::as) (b::bs) (c::cs) cin target) := by
  simp only [compareLt,gatePhysical_append] at h
  simp only [compareLtHeadOne,gatePhysical_append]
  exact ⟨⟨h.1.1,compareChainHeadOne_physical a b c as bs cs cin target h.1.2⟩,h.2⟩

theorem eraseLtHeadZero_physical (a a' b b' c : Wire) (as bs cs : List Wire) (cin target : Wire)
    (h : GatePhysical (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target)) :
    GatePhysical (eraseLtHeadZero (a::a'::as) (b::b'::bs) (c::cs) cin target) := by
  change GatePhysical (borrowMajority a b cin c++
    eraseLtChain (a'::as) (b'::bs) cs c target++eraseBorrow a b cin c) at h
  change GatePhysical (eraseLtChain (a'::as) (b'::bs) cs c target++eraseBorrow a b cin c)
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.2,h.2⟩

theorem middle_eq (P A B Q : Program) (s : State) (m : List Bool)
    (hc : measurementCount A=measurementCount B)
    (he : ∀ n,run A n (run P m s)=run B n (run P m s)) :
    run (P++A++Q) m s=run (P++B++Q) m s := by
  simp only [List.append_assoc,run_append,run_take]
  rw [he _,hc]

theorem masked_even_head (g a : Wire) (as : List Wire) (v : Nat) (he : v%2=0)
    (ha : a∉as) (hag : a≠g) (s : State) (m : List Bool) :
    (run (maskedConstant g (a::as) v) m s).basis a=s.basis a := by
  have hne : ¬v%2=1 := by omega
  simp only [maskedConstant,hne,if_false,List.nil_append]
  apply run_preserves_outside
  intro hm
  have hs:=maskedConstant_wires_subset g as (v/2) hm
  simp only [List.mem_toFinset,List.mem_cons] at hs
  exact hs.elim hag ha

theorem load_even_not (g a cin : Wire) (as : List Wire) (v : Nat) (he : v%2=0)
    (hn : (a::as).Nodup) (hag : a≠g) (hcg : cin≠g) (hcs : cin∉a::as)
    (s : State) (m : List Bool) (ha : s.basis a=false) (hc : s.basis cin=false) :
    let P:=maskedConstant g (a::as) v++notRegister (a::as)
    (run P m s).basis a=true ∧ (run P m s).basis cin=false := by
  have hao:=List.nodup_cons.mp hn
  let u:=run (maskedConstant g (a::as) v) m s
  have ua:u.basis a=false := (masked_even_head g a as v he hao.1 hag s m).trans ha
  have uc:u.basis cin=false := by
    apply Eq.trans (run_preserves_outside _ m s cin ?_) hc
    intro hm
    have hs:=maskedConstant_wires_subset g (a::as) v hm
    simp only [List.mem_toFinset,List.mem_cons] at hs
    exact hs.elim hcg (fun h=>hcs (List.mem_cons.mpr h))
  have tr:=notRegister_correct (a::as) hn u m
  dsimp only
  simp only [run_append,run_take]
  simp only [(maskedConstant_counts _ _ _).2,List.drop_zero]
  change (run (notRegister (a::as)) m u).basis a=true ∧
    (run (notRegister (a::as)) m u).basis cin=false
  rw [tr]
  constructor
  · simp [ua]
  · change (if cin∈a::as then !u.basis cin else u.basis cin)=false
    rw [if_neg hcs]
    exact uc

def loadNot (g : Wire) (src : List Wire) (v : Nat) : Program :=
  maskedConstant g src v++notRegister src

def unloadNot (g : Wire) (src : List Wire) (v : Nat) : Program :=
  notRegister src++maskedConstant g src v

def comparePrefixOld (g : Wire) (src out carry : List Wire) (cin flag : Wire) (v : Nat) : Program :=
  loadNot g src v++compareLt none src out carry cin flag++unloadNot g src v

def comparePrefixNew (g : Wire) (src out carry : List Wire) (cin flag : Wire) (v : Nat) : Program :=
  loadNot g src v++compareLtHeadOne src out carry cin flag++unloadNot g src v

def erasePrefixOld (g : Wire) (src out carry : List Wire) (cin flag : Wire) (v : Nat) : Program :=
  loadNot g src v++eraseLtChain src out carry cin flag++unloadNot g src v

def erasePrefixNew (g : Wire) (src out carry : List Wire) (cin flag : Wire) (v : Nat) : Program :=
  loadNot g src v++eraseLtHeadZero src out carry cin flag++unloadNot g src v

theorem comparePrefixNew_eq (g a b c cin flag : Wire) (as bs cs : List Wire) (v : Nat)
    (he : v%2=0) (hn : (a::as).Nodup) (hag : a≠g) (hcg : cin≠g) (hcs : cin∉a::as)
    (hport : [a,b,cin,c].Nodup) (hy : (cin::b::bs).Nodup) (hao : a∉cin::b::bs)
    (s : State) (m : List Bool) (ha : s.basis a=false) (hc : s.basis cin=false) :
    run (comparePrefixNew g (a::as) (b::bs) (c::cs) cin flag v) m s=
      run (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v) m s := by
  apply middle_eq _ _ _ _ s m (compareLtHeadOne_counts a b c as bs cs cin flag).2.1
  intro n
  have ready:=load_even_not g a cin as v he hn hag hcg hcs s m ha hc
  exact compareLtHeadOne_eq a b c as bs cs cin flag hport hy hao _ n ready.1 ready.2

theorem erasePrefixNew_eq (g a a' b b' c cin flag : Wire) (as bs cs : List Wire) (v : Nat)
    (he : v%2=0) (hn : (a::a'::as).Nodup) (hag : a≠g) (hcg : cin≠g) (hcs : cin∉a::a'::as)
    (hport : [a,b,cin,c].Nodup) (s : State) (m : List Bool)
    (ha : s.basis a=false) (hc : s.basis cin=false) :
    run (erasePrefixNew g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) m s=
      run (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) m s := by
  apply middle_eq _ _ _ _ s m (eraseLtHeadZero_counts a a' b b' c as bs cs cin flag).2.1
  intro n
  have ready:=load_even_not g a cin (a'::as) v he hn hag hcg hcs s m ha hc
  exact eraseLtHeadOne_eq a a' b b' c as bs cs cin flag hport _ n ready.1 ready.2

theorem comparePrefixNew_counts (g a b c cin flag : Wire) (as bs cs : List Wire) (v : Nat) :
    toffoliCount (comparePrefixNew g (a::as) (b::bs) (c::cs) cin flag v)+1=
      toffoliCount (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v) ∧
    measurementCount (comparePrefixNew g (a::as) (b::bs) (c::cs) cin flag v)=
      measurementCount (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v) ∧
    gateSlots (comparePrefixNew g (a::as) (b::bs) (c::cs) cin flag v)+5=
      gateSlots (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v) := by
  have h:=compareLtHeadOne_counts a b c as bs cs cin flag
  simp only [comparePrefixNew,comparePrefixOld,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem erasePrefixNew_counts (g a a' b b' c cin flag : Wire) (as bs cs : List Wire) (v : Nat) :
    toffoliCount (erasePrefixNew g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)+1=
      toffoliCount (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) ∧
    measurementCount (erasePrefixNew g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)=
      measurementCount (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) ∧
    gateSlots (erasePrefixNew g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)+8=
      gateSlots (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) := by
  have h:=eraseLtHeadZero_counts a a' b b' c as bs cs cin flag
  simp only [erasePrefixNew,erasePrefixOld,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

def oddSavings (k : Nat) : Nat := if k%2=1 then 1 else 0

theorem odd_neg_sum (y : Fp) (hy : y≠0) :
    oddSavings y.val+oddSavings (-y).val=1 := by
  haveI : NeZero p:=⟨by norm_num [p]⟩
  have hv : y.val≠0 := by intro h; exact hy ((ZMod.val_eq_zero y).mp h)
  have hlt : y.val<p := ZMod.val_lt y
  have hp : p%2=1 := by norm_num [p]
  have hn : (-y).val=p-y.val := by
    rw [ZMod.neg_val',Nat.mod_eq_of_lt (by omega)]
  rw [hn]
  unfold oddSavings
  split_ifs <;> omega

theorem list_head (xs : List Wire) (h : 0<xs.length) : ∃ a as,xs=a::as := by
  cases xs with
  | nil => simp at h
  | cons a as => exact ⟨a,as,rfl⟩

theorem list_two (xs : List Wire) (h : 2≤xs.length) : ∃ a b bs,xs=a::b::bs := by
  cases xs with
  | nil => simp at h
  | cons a as =>
    cases as with
    | nil => simp at h
    | cons b bs => exact ⟨a,b,bs,rfl⟩

theorem layout_core_nodup (K : MeasuredCanonicalModLayout) (g : Wire)
    (hn : (g::K.wires).Nodup) : (K.cin::(K.src++K.out++K.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h:=List.nodup_iff_count.mp hn q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem layout_core_take_nodup (K : MeasuredCanonicalModLayout) (g : Wire) (j : Nat)
    (hn : (g::K.wires).Nodup) : (K.cin::(K.src++K.out++K.carry.take j)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h:=List.nodup_iff_count.mp hn q
  have ht:=(List.take_sublist j K.carry).count_le q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem layout_control_src (K : MeasuredCanonicalModLayout) (g : Wire)
    (hn : (g::K.wires).Nodup) : g∉K.src := by
  intro hg
  have h:=List.nodup_cons.mp hn
  exact h.1 (by simp [MeasuredCanonicalModLayout.wires,hg])

theorem layout_control_cin (K : MeasuredCanonicalModLayout) (g : Wire)
    (hn : (g::K.wires).Nodup) : K.cin≠g := by
  intro eq
  have h:=List.nodup_cons.mp hn
  apply h.1
  simp [MeasuredCanonicalModLayout.wires,←eq]

theorem compare_layout_eq (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256)
    (hn : (g::K.wires).Nodup) (v : Nat) (he : v%2=0)
    (s : State) (m : List Bool) (hs0 : regValue K.src s.basis=0) (hc0 : s.basis K.cin=false) :
    run (comparePrefixNew g K.src K.out K.carry K.cin K.flag v) m s=
      run (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) m s := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have H:=layout_core_nodup K g hn
  rw [hs,ho,hc] at H
  have srcND : (a::as).Nodup:=H.of_cons.of_append_left.of_append_left
  have outside:K.cin∉a::as := by
    intro h
    exact (List.nodup_cons.mp H).1 (List.mem_append_left _ (List.mem_append_left _ h))
  have ag:a≠g := by
    intro e
    exact layout_control_src K g hn (by rw [hs];simp [e])
  have sa:s.basis a=false:=(regValue_zero K.src s.basis).mp hs0 a (by rw [hs];simp)
  rw [hs,ho,hc]
  exact comparePrefixNew_eq g a b c K.cin K.flag as bs cs v he srcND ag
    (layout_control_cin K g hn) outside (heads_nodup a b c K.cin as bs cs H)
    (right_nodup a b c K.cin as bs cs H) (left_outside a b c K.cin as bs cs H) s m sa hc0

theorem erase_layout_eq (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256)
    (hn : (g::K.wires).Nodup) (v : Nat) (he : v%2=0)
    (s : State) (m : List Bool) (hs0 : regValue K.src s.basis=0) (hc0 : s.basis K.cin=false) :
    run (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v) m s=
      run (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) m s := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  have H:=layout_core_take_nodup K g 255 hn
  rw [hs,ho,hc] at H
  have srcND : (a::a'::as).Nodup:=H.of_cons.of_append_left.of_append_left
  have outside:K.cin∉a::a'::as := by
    intro h
    exact (List.nodup_cons.mp H).1 (List.mem_append_left _ (List.mem_append_left _ h))
  have ag:a≠g := by
    intro e
    exact layout_control_src K g hn (by rw [hs];simp [e])
  have sa:s.basis a=false:=(regValue_zero K.src s.basis).mp hs0 a (by rw [hs];simp)
  rw [hs,ho,hc]
  exact erasePrefixNew_eq g a a' b b' c K.cin K.flag as bs cs v he srcND ag
    (layout_control_cin K g hn) outside (heads_nodup a b c K.cin (a'::as) (b'::bs) cs H)
    s m sa hc0

end ECDSAAdd.Entrant.ParityCarry
end


-- Consolidated source module: ParityConvert
section

namespace ECDSAAdd.Entrant.ParityConvert
open ECDSAAdd Arithmetic Challenge ParityCarry EntryFuseArithmetic
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem prefix_eq (A B Q : Program) (s : State) (m : List Bool)
    (hc : measurementCount A=measurementCount B) (he : run A m s=run B m s) :
    run (A++Q) m s=run (B++Q) m s := by
  simp only [run_append,run_take]
  rw [he,hc]

theorem compare_layout_counts (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat) :
    toffoliCount (comparePrefixNew g K.src K.out K.carry K.cin K.flag v)+1=
      toffoliCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) ∧
    measurementCount (comparePrefixNew g K.src K.out K.carry K.cin K.flag v)=
      measurementCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) ∧
    gateSlots (comparePrefixNew g K.src K.out K.carry K.cin K.flag v)+5=
      gateSlots (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  rw [hs,ho,hc]
  exact comparePrefixNew_counts g a b c K.cin K.flag as bs cs v

theorem old_entry_split (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (k : Nat) :
    EntryFuse.entry K g complement k=
      comparePrefixOld g K.src K.out K.carry K.cin K.flag (complement+k)++
        EntryFuse.entryBody K g k K.out.tail := by
  have hout:K.out=EntryFuse.lowBit K::K.out.tail := by
    obtain ⟨a,as,hs⟩:=list_head K.out (by rw [hw.out];decide)
    simp [EntryFuse.lowBit,hs]
  have h:=EntryFuse.entry_decompose K g complement k K.out.tail hout
  simpa only [comparePrefixOld,loadNot,unloadNot,EntryFuse.entryCompare,EntryFuse.entryBody,
    EntryFuse.entryMiddle,List.append_assoc] using h

def entryOpt (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  if k%2=1 then
    comparePrefixNew g K.src K.out K.carry K.cin K.flag (complement+k)++
      EntryFuse.entryBody K g k K.out.tail
  else EntryFuse.entry K g complement k

theorem entryOpt_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) (hn : (g::K.wires).Nodup) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hi : s.basis K.cin=false) :
    run (entryOpt K g k) m s=run (EntryFuse.entry K g complement k) m s := by
  unfold entryOpt
  split_ifs with hk
  · have he:(complement+k)%2=0 := by norm_num [complement,Nat.add_mod,hk]
    rw [old_entry_split K g hw k]
    exact prefix_eq _ _ _ s m (compare_layout_counts K g hw (complement+k)).2.1
      (compare_layout_eq K g hw hn (complement+k) he s m hs hi)
  · rfl

theorem entryOpt_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    toffoliCount (entryOpt K g k)+oddSavings k=766 ∧ measurementCount (entryOpt K g k)=767 ∧
    gateSlots (entryOpt K g k)≤gateSlots (EntryFuse.entry K g complement k) := by
  have old:=EntryFuse.entry_counts K g complement k hw
  have delta:=compare_layout_counts K g hw (complement+k)
  have split:=old_entry_split K g hw k
  have ct:=congrArg toffoliCount split
  have cm:=congrArg measurementCount split
  have cg:=congrArg gateSlots split
  unfold entryOpt oddSavings
  split_ifs <;> simp only [toffoliCount_append,measurementCount_append,gateSlots_append] at * <;> omega


open EntryFuse ExitFusionProof Secp256k1 BalancedField

theorem erase_layout_counts (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat) :
    toffoliCount (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v)+1=
      toffoliCount (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) ∧
    measurementCount (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v)=
      measurementCount (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) ∧
    gateSlots (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v)+8=
      gateSlots (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  rw [hs,ho,hc]
  exact erasePrefixNew_counts g a a' b b' c K.cin K.flag as bs cs v

def eraseInputOpt (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  if k%2=1 then erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)
  else ExitFusionResearch.eraseInputWrap K g complement k

theorem old_erase_split (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    ExitFusionResearch.eraseInputWrap K g complement k=
      erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k) := by
  simp only [ExitFusionResearch.eraseInputWrap,erasePrefixOld,loadNot,unloadNot,List.append_assoc]

theorem eraseInputOpt_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) (hn : (g::K.wires).Nodup) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hi : s.basis K.cin=false) :
    run (eraseInputOpt K g k) m s=run (ExitFusionResearch.eraseInputWrap K g complement k) m s := by
  unfold eraseInputOpt
  split_ifs with hk
  · have he:(complement+k)%2=0 := by norm_num [complement,Nat.add_mod,hk]
    rw [old_erase_split]
    exact erase_layout_eq K g hw hn (complement+k) he s m hs hi
  · rfl

theorem eraseInputOpt_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    toffoliCount (eraseInputOpt K g k)+oddSavings k=toffoliCount (ExitFusionResearch.eraseInputWrap K g complement k) ∧
    measurementCount (eraseInputOpt K g k)=measurementCount (ExitFusionResearch.eraseInputWrap K g complement k) ∧
    gateSlots (eraseInputOpt K g k)≤gateSlots (ExitFusionResearch.eraseInputWrap K g complement k) := by
  have delta:=erase_layout_counts K g hw (complement+k)
  rw [old_erase_split]
  unfold eraseInputOpt oddSavings
  split_ifs with hk
  · omega
  · rw [old_erase_split]
    omega

def exitOpt (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  ExitFusionResearch.recoverWrap K g complement k++ExitFusionResearch.undoMiddle K g complement k++
    (ExitFusionResearch.signStage K g k).reverse++eraseInputOpt K g k

theorem exitOpt_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    toffoliCount (exitOpt K g k)+oddSavings k=766 ∧ measurementCount (exitOpt K g k)=766 ∧
    gateSlots (exitOpt K g k)≤gateSlots (ExitFusionResearch.exit K g complement k) := by
  have old:=ExitFusionResearch.exit_counts K g complement k hw
  have delta:=eraseInputOpt_counts K g k hw
  simp only [exitOpt,ExitFusionResearch.exit,toffoliCount_append,measurementCount_append,gateSlots_append] at *
  omega

private theorem run_four (A B C D : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 m4 : List Bool,run (A++B++C++D) m s=run D m4 (run C m3 (run B m2 (run A m1 s))) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    ((m.drop (measurementCount A)).drop (measurementCount B)).take (measurementCount C),
    ((m.drop (measurementCount A)).drop (measurementCount B)).drop (measurementCount C),
    by simp only [List.append_assoc,run_append]⟩
theorem exitOpt_entry_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n : List Bool) (hY : regValue K.out s.basis=Y)
    (hy : Y<prime) (hk : k<prime) (hsrc : regValue K.src s.basis=0)
    (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    run (exitOpt K g k) n (run (EntryFuse.entry K g complement k) m s)=s := by
  obtain ⟨rest,hout⟩ := out_shape K hw
  have pc : prime+complement=2^256 := by norm_num [prime,modulus,complement]
  let m1 := m.take (measurementCount (entryCompare K g complement k))
  let m2 := m.drop (measurementCount (entryCompare K g complement k))
  let t := run (entryCompare K g complement k) m1 s
  have initial : FastConst.Frame K s.basis 0 Y false s.basis := ⟨hsrc,hY,hf,by intro q hq; rfl⟩
  have pre := comparePrefix_correct hn 256 hw s.basis hcarry hcin complement prime k Y pc hk hy s m1 initial
  change t.phase=s.phase ∧ FastConst.Frame K s.basis 0 Y
    (if s.basis g then decide (prime≤Y+k) else false) t.basis at pre
  have tg : t.basis g=s.basis g := pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th : t.basis K.high=false := (pre.2.2.2.2 K.high
    (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have tcin : t.basis K.cin=false := (pre.2.2.2.2 K.cin
    (FastConst.fixed_not_mutable hn K.cin (by simp))).trans hcin
  have tcarry : ∀q∈K.carry,t.basis q=false := by
    intro q hq
    exact (pre.2.2.2.2 q (FastConst.fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have tflag : t.basis K.flag=decide (prime≤Y+(if t.basis g then k else 0)) := by
    rw [tg]
    have h := pre.2.2.2.1
    cases hg : s.basis g <;> simp [hg,show ¬prime≤Y by omega] at h ⊢ <;> exact h
  let A := ExitFusionResearch.recoverWrap K g complement k
  let B := ExitFusionResearch.undoMiddle K g complement k
  let C := (ExitFusionResearch.signStage K g k).reverse
  let D := eraseInputOpt K g k
  obtain ⟨n1,n2,n3,n4,parts⟩ := run_four A B C D n (run (entryBody K g k rest) m2 t)
  have recover : run A n1 (run (entryBody K g k rest) m2 t)=
      run (entryMiddle K g k rest) (m2.take (measurementCount (entryMiddle K g k rest))) t :=
    recover_entryBody K g k Y hn hw rest hout t m2 n1 pre.2.2.1 hy hk pre.2.1 th tcin tcarry tflag
  have undo : run C n3 (run B n2
      (run (entryMiddle K g k rest) (m2.take (measurementCount (entryMiddle K g k rest))) t))=t :=
    undo_entryMiddle_inverse K g k hn hw rest hout t _ n2 n3 pre.2.1 th tcin tcarry
  have erase : run D n4 t=s := by
    change run (eraseInputOpt K g k) n4 t=s
    rw [eraseInputOpt_eq K g k hw hn t n4 pre.2.1 tcin]
    exact eraseInput_entryCompare_inverse K g k Y hn hw s m1 n4 hY hy hk hsrc hf hcin hcarry
  have decomp : EntryFuse.entry K g complement k=entryCompare K g complement k++entryBody K g k rest := by
    rw [entry_decompose K g complement k rest hout]
    simp only [entryBody,entryMiddle,List.append_assoc]
  rw [decomp,run_append]
  change run (A++B++C++D) n (run (entryBody K g k rest) m2 t)=s
  rw [parts,recover,undo,erase]

theorem exitOpt_field_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hH : regValue K.out s.basis=centerWord H)
    (hsrc : regValue K.src s.basis=0) (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    let v := run (exitOpt K g k.val) m s
    v.phase=s.phase ∧ regValue K.out v.basis=(2*H-(if s.basis g then k else 0)).val ∧
      ∀q,q∉K.out → v.basis q=s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let Y : Fp := 2*H-(if s.basis g then k else 0)
  let b := run (xorConstant K.out (regValue K.out s.basis)) [] s
  have clear := xorConstant_correct K.out (FastConst.out_nodup hn) (regValue K.out s.basis)
    (regValue_lt K.out s.basis) s []
  have yBound : Y.val<2^K.out.length := by
    rw [hw.out]
    exact Y.isLt.trans (by norm_num [p])
  let a := run (xorConstant K.out Y.val) [] b
  have load := xorConstant_correct K.out (FastConst.out_nodup hn) Y.val yBound b []
  have av : regValue K.out a.basis=Y.val := by rw [load.2.2,clear.2.2]; simp
  have ap : a.phase=s.phase := load.1.trans clear.1
  have outside (q : Wire) (hq : q∉K.out) : a.basis q=s.basis q :=
    (load.2.1 q hq).trans (clear.2.1 q hq)
  have aSrc : regValue K.src a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq => outside q (src_fullOut K g hn q hq)),hsrc]
  have fixedOutside (q : Wire) (hq : q∈K.carry++[K.high,K.cin]) : q∉K.out := by
    intro bad
    exact FastConst.fixed_not_mutable hn q hq (by simp [FastConst.mutable,bad])
  have af : a.basis K.flag=false := (outside _ (FastConst.flag_not_out hn)).trans hf
  have ah : a.basis K.high=false := (outside _ (fixedOutside _ (by simp))).trans hh
  have ac : a.basis K.cin=false := (outside _ (fixedOutside _ (by simp))).trans hcin
  have aCarry : ∀q∈K.carry,a.basis q=false := by
    intro q hq
    exact (outside q (fixedOutside q (by simp [hq]))).trans (hcarry q hq)
  have ag : a.basis g=s.basis g := outside g (FastConst.g_not_out hn)
  have fwd := entry_field_correct K g k Y hn hw a [] av aSrc af ah ac aCarry
  have math : (Y+(if a.basis g then k else 0))/2=H := by
    rw [ag]
    dsimp only [Y]
    rw [sub_add_cancel]
    have two : (2:Fp)≠0 := by decide
    field_simp
  have preimage : run (EntryFuse.entry K g complement k.val) [] a=s := by
    apply State.extensionality
    · exact fwd.1.trans ap
    · funext q
      by_cases hq : q∈K.out
      · have val : regValue K.out (run (EntryFuse.entry K g complement k.val) [] a).basis=regValue K.out s.basis := by
          rw [fwd.2.1,math,hH]
        exact (regValue_eq_iff _ _ _).mp val q hq
      · exact (fwd.2.2 q hq).trans (outside q hq)
  have hy : Y.val<prime := by rw [prime_eq_secp]; exact Y.isLt
  have hk : k.val<prime := by rw [prime_eq_secp]; exact k.isLt
  have inv := exitOpt_entry_inverse K g k.val Y.val hn hw a [] m av hy hk aSrc af ah ac aCarry
  rw [preimage] at inv
  dsimp only
  rw [inv]
  exact ⟨ap,av,outside⟩


theorem exitOpt_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (s : State) (m n : List Bool)
    (hH : regValue K.out s.basis=centerWord H) (hsrc : regValue K.src s.basis=0)
    (hf : s.basis K.flag=false) (hh : s.basis K.high=false) (hcin : s.basis K.cin=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) :
    run (exitOpt K g k.val) m s=run (ExitFusionResearch.exit K g complement k.val) n s := by
  have a:=exitOpt_field_correct K g k H hn hw s m hH hsrc hf hh hcin hcarry
  have b:=ExitFusionProof.exit_field_correct K g k H hn hw s n hH hsrc hf hh hcin hcarry
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases hq:q∈K.out
    · exact (regValue_eq_iff K.out _ _).mp (a.2.1.trans b.2.1.symm) q hq
    · exact (a.2.2 q hq).trans (b.2.2 q hq).symm


theorem cmp_prefix_wires (g a b c cin flag : Wire) (as bs cs : List Wire) (v : Nat) :
    wires (comparePrefixNew g (a::as) (b::bs) (c::cs) cin flag v)⊆
      wires (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v) := by
  have h:=compareLtHeadOne_wires a b c as bs cs cin flag
  simp only [comparePrefixNew,comparePrefixOld,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)

theorem cmp_prefix_physical (g a b c cin flag : Wire) (as bs cs : List Wire) (v : Nat)
    (h : GatePhysical (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v)) :
    GatePhysical (comparePrefixNew g (a::as) (b::bs) (c::cs) cin flag v) := by
  simp only [comparePrefixOld,gatePhysical_append] at h
  simp only [comparePrefixNew,gatePhysical_append]
  exact ⟨⟨h.1.1,compareLtHeadOne_physical a b c as bs cs cin flag h.1.2⟩,h.2⟩

theorem era_prefix_wires (g a a' b b' c cin flag : Wire) (as bs cs : List Wire) (v : Nat) :
    wires (erasePrefixNew g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)⊆
      wires (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) := by
  have h:=eraseLtHeadZero_wires a a' b b' c as bs cs cin flag
  simp only [erasePrefixNew,erasePrefixOld,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)

theorem era_prefix_physical (g a a' b b' c cin flag : Wire) (as bs cs : List Wire) (v : Nat)
    (h : GatePhysical (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)) :
    GatePhysical (erasePrefixNew g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) := by
  simp only [erasePrefixOld,gatePhysical_append] at h
  simp only [erasePrefixNew,gatePhysical_append]
  exact ⟨⟨h.1.1,eraseLtHeadZero_physical a a' b b' c as bs cs cin flag h.1.2⟩,h.2⟩

theorem compare_layout_wires (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat) :
    wires (comparePrefixNew g K.src K.out K.carry K.cin K.flag v)⊆
      wires (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  rw [hs,ho,hc]
  exact cmp_prefix_wires g a b c K.cin K.flag as bs cs v

theorem compare_layout_physical (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat)
    (h : GatePhysical (comparePrefixOld g K.src K.out K.carry K.cin K.flag v)) :
    GatePhysical (comparePrefixNew g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  rw [hs,ho,hc] at h ⊢
  exact cmp_prefix_physical g a b c K.cin K.flag as bs cs v h

theorem erase_layout_wires (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat) :
    wires (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v)⊆
      wires (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  rw [hs,ho,hc]
  exact era_prefix_wires g a a' b b' c K.cin K.flag as bs cs v

theorem erase_layout_physical (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat)
    (h : GatePhysical (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v)) :
    GatePhysical (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  rw [hs,ho,hc] at h ⊢
  exact era_prefix_physical g a a' b b' c K.cin K.flag as bs cs v h

theorem entryOpt_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    wires (entryOpt K g k)⊆wires (EntryFuse.entry K g complement k) := by
  unfold entryOpt
  split_ifs
  · rw [old_entry_split K g hw k]
    simp only [wires_append]
    exact Finset.union_subset_union (compare_layout_wires K g hw (complement+k)) (Finset.Subset.refl _)
  · exact Finset.Subset.refl _

theorem entryOpt_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (entryOpt K g k) := by
  have old:=EntryFuse.entry_physical K g complement k hn hw
  unfold entryOpt
  split_ifs
  · rw [old_entry_split K g hw k] at old
    simp only [gatePhysical_append] at old ⊢
    exact ⟨compare_layout_physical K g hw (complement+k) old.1,old.2⟩
  · exact old

theorem eraseInputOpt_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    wires (eraseInputOpt K g k)⊆wires (ExitFusionResearch.eraseInputWrap K g complement k) := by
  unfold eraseInputOpt
  split_ifs
  · rw [old_erase_split]
    exact erase_layout_wires K g hw (complement+k)
  · exact Finset.Subset.refl _

theorem eraseInputOpt_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256)
    (h : GatePhysical (ExitFusionResearch.eraseInputWrap K g complement k)) : GatePhysical (eraseInputOpt K g k) := by
  unfold eraseInputOpt
  split_ifs
  · rw [old_erase_split] at h
    exact erase_layout_physical K g hw (complement+k) h
  · exact h

theorem exitOpt_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    wires (exitOpt K g k)⊆wires (ExitFusionResearch.exit K g complement k) := by
  have h:=eraseInputOpt_wires K g k hw
  simp only [exitOpt,ExitFusionResearch.exit,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) h

theorem exitOpt_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (exitOpt K g k) := by
  have old:=ExitFusionResearch.exit_physical K g complement k hn hw
  simp only [ExitFusionResearch.exit,gatePhysical_append] at old
  simp only [exitOpt,gatePhysical_append]
  exact ⟨old.1,eraseInputOpt_physical K g k hw old.2⟩


def yLayout (L : ControlledPointLayout) : MeasuredCanonicalModLayout := L.recoveryConstant L.point.y

def entryYOpt (L : ControlledPointLayout) (k : Fp) : Program := entryOpt (yLayout L) L.core.generic k.val

def exitYOpt (L : ControlledPointLayout) (k : Fp) : Program := exitOpt (yLayout L) L.core.generic k.val

theorem y_aux_clean (L : ControlledPointLayout) (hw : L.Widths) (s : State)
    (hc : regValue L.dialogPool s.basis=0) (q : Wire)
    (hq : q∈(yLayout L).src++(yLayout L).carry++[(yLayout L).high,(yLayout L).cin,(yLayout L).flag]) :
    s.basis q=false := by
  change q∈(L.recoveryConstant L.point.y).src++(L.recoveryConstant L.point.y).carry++
    [(L.recoveryConstant L.point.y).high,(L.recoveryConstant L.point.y).cin,(L.recoveryConstant L.point.y).flag] at hq
  rw [L.recoveryConstant_pool hw L.point.y] at hq
  exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)

theorem entryYOpt_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (s : State) (m : List Bool) (hc : regValue L.dialogPool s.basis=0) :
    run (entryYOpt L k) m s=run (EntryFuse.fusedY L k) m s := by
  let K:=yLayout L
  have aux:=y_aux_clean L hw s hc
  have sz:regValue K.src s.basis=0 := (regValue_zero _ _).mpr (fun q hq=>aux q (by simp [K,hq]))
  have ci:s.basis K.cin=false:=aux _ (by simp [K])
  have h:=entryOpt_eq K L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) s m sz ci
  simpa only [entryYOpt,EntryFuse.fusedY,K,yLayout] using h

theorem exitYOpt_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (s : State) (m n : List Bool)
    (hy : regValue L.point.y s.basis=centerWord Y) (hc : regValue L.dialogPool s.basis=0) :
    run (exitYOpt L k) m s=run (ExitFusionResearch.exitY L k) n s := by
  let K:=yLayout L
  have aux:=y_aux_clean L hw s hc
  have sz:regValue K.src s.basis=0 := (regValue_zero _ _).mpr (fun q hq=>aux q (by simp [K,hq]))
  have h:=exitOpt_eq K L.core.generic k Y
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl))
    (L.recoveryConstant_widths hw L.point.y hw.inputY) s m n hy sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq=>aux q (by simp [K,hq]))
  simpa only [exitYOpt,ExitFusionResearch.exitY,K,yLayout] using h

theorem entryYOpt_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (s : State) (m : List Bool) (hy : regValue L.point.y s.basis=Y.val)
    (hc : regValue L.dialogPool s.basis=0) :
    let v:=run (entryYOpt L k) m s
    v.phase=s.phase ∧ regValue L.point.y v.basis=centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
      ∀q,q∉L.point.y → v.basis q=s.basis q := by
  dsimp only
  rw [entryYOpt_eq L hw hn k s m hc]
  exact EntryFuse.fusedY_correct L hw hn Y k s m hy hc

theorem exitYOpt_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (s : State) (m : List Bool) (hy : regValue L.point.y s.basis=centerWord Y)
    (hc : regValue L.dialogPool s.basis=0) :
    let v:=run (exitYOpt L k) m s
    v.phase=s.phase ∧ regValue L.point.y v.basis=(2*Y-(if s.basis L.core.generic then k else 0)).val ∧
      ∀q,q∉L.point.y → v.basis q=s.basis q := by
  dsimp only
  rw [exitYOpt_eq L hw hn Y k s m m hy hc]
  exact ExitFusionResearch.exitY_correct L hw hn Y k s m hy hc

theorem entryYOpt_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryYOpt L k)+oddSavings k.val=766 ∧ measurementCount (entryYOpt L k)=767 ∧
    gateSlots (entryYOpt L k)≤gateSlots (EntryFuse.fusedY L k) := by
  exact entryOpt_counts (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYOpt_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (exitYOpt L k)+oddSavings k.val=766 ∧ measurementCount (exitYOpt L k)=766 ∧
    gateSlots (exitYOpt L k)≤gateSlots (ExitFusionResearch.exitY L k) := by
  exact exitOpt_counts (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

attribute [local irreducible] wires GatePhysical

theorem entryYOpt_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryYOpt L k)⊆wires (EntryFuse.fusedY L k) :=
  entryOpt_wires (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYOpt_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (exitYOpt L k)⊆wires (ExitFusionResearch.exitY L k) :=
  exitOpt_wires (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem entryYOpt_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (entryYOpt L k) :=
  entryOpt_physical (yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYOpt_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (exitYOpt L k) :=
  exitOpt_physical (yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) (L.recoveryConstant_widths hw L.point.y hw.inputY)

end ECDSAAdd.Entrant.ParityConvert
end


-- Consolidated source module: ParityStage
section

namespace ECDSAAdd.Entrant.ParityStage
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap OB5 Rolling1588Lifetime ParityCarry ParityConvert
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  InverseFour15.lastPhase15 InverseFour15.stackReverse15 InverseFour15.reverseTail15 Rolling1588TickGap.tailPhase
def restEntry (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true) ++
      (Rolling1588.entryFieldHosted ++ renameProgram phaseHost (InverseFour15.lastPhase15 false)))

def entryRef (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky ++ E1QubitPlacement.entryM L kx ++ restEntry L

theorem entry_split_ref (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry InverseFour15.entryKernel15 L = E1QubitPlacement.tickF L ++ restEntry L := by
  have tick := E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base)) = E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,InverseFour15.entryKernel15,InverseFour15.kernel15,
    Rolling1588TickGap.firstPhase,restEntry,renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem entryRef_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryRef L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX L hw hn X Y G origin kx
  have divide := division_step InverseFour15.entryKernel15 InverseFour15.entry_support530
    InverseFour15.entry_correct15 L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior := add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky ++ E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx ++ fusedY L ky ++ E1QubitPlacement.tickF L)
    (R:=restEntry L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryRef,division,entry_split_ref,List.append_assoc] using prior


def entryStageOpt (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  entryYOpt L ky++E1QubitPlacement.entryM L kx++restEntry L

theorem entryStageOpt_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (kx ky : Fp) (s : State) (m : List Bool) (hc : regValue L.dialogPool s.basis=0) :
    run (entryStageOpt L kx ky) m s=run (entryRef L kx ky) m s := by
  have cm:(measurementCount (entryYOpt L ky))=measurementCount (fusedY L ky) :=
    (entryYOpt_counts L hw ky).2.1.trans (fusedY_counts L hw ky).2.symm
  simpa only [entryStageOpt,entryRef,List.append_assoc] using
    prefix_eq (entryYOpt L ky) (fusedY L ky) (E1QubitPlacement.entryM L kx++restEntry L) s m cm
      (entryYOpt_eq L hw hn ky s m hc)

theorem entryStageOpt_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState) (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStageOpt L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  intro s m hs
  rw [entryStageOpt_eq L hw hn kx ky s m hs.clean]
  exact entryRef_step L hw hn X Y kx ky G origin hx s m hs

theorem multiplyExitOpt_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ExitMergeKernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (P++exitYOpt L k) m s=run (P++ExitFusionResearch.exitY L k) m s := by
  let n:=measurementCount P
  let a:=run P (m.take n) s
  have hp:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have half:=correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have ac:regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq=>half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av:regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  rw [run_append,run_append]
  exact exitYOpt_eq L hw hn ((Y*X)/2) k a (m.drop n) (m.drop n) av ac

theorem multiplyExitOpt_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ExitMergeKernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++exitYOpt L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m hs
  rw [multiplyExitOpt_eq L hw hn P cx correct X Y k G origin hX s m hs]
  exact ExitMergeKernel.fusedMultiplyX_step L hw hn P cx correct X Y k G origin hX s m hs

def secondStageOpt (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  ReflectionE1TickGapLow48.squareEntry L k++ExitMergeKernel.restXX L cx.val++exitYOpt L cy

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
open ReflectionE1TickGapLow48
theorem secondStageOpt_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageOpt L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=multiplyExitOpt_step L hw hn
    (FrontierEntry1591Callers.exit (ExitMergeKernel.kernelX cx.val) L) cx
    (ExitMergeKernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageOpt,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ExitMergeKernel.restXX L cx.val++exitYOpt L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ExitMergeKernel.exit_splitX,List.append_assoc,Z] using prior

end

def genericOpt (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStageOpt L (-cx) (-cy)++secondStageOpt L (ReflectionE1.correction cx) cy cx

def genericRef (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryRef L (-cx) (-cy)++ReflectionE1TickGapLow48.secondStageX L (ReflectionE1.correction cx) cy cx

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (genericOpt L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageOpt_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageOpt_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (genericOpt L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStageOpt_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageOpt_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second



end


theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericOpt L cx cy)+oddSavings (-cy).val+oddSavings cy.val=toffoliCount (genericRef L cx cy) ∧
    measurementCount (genericOpt L cx cy)=measurementCount (genericRef L cx cy) ∧
    gateSlots (genericOpt L cx cy)≤gateSlots (genericRef L cx cy) := by
  have a:=entryYOpt_counts L hw (-cy)
  have aa:=fusedY_counts L hw (-cy)
  have b:=exitYOpt_counts L hw cy
  have bb:=ExitFusionResearch.exitY_counts L hw cy
  simp only [genericOpt,genericRef,entryStageOpt,entryRef,secondStageOpt,
    ReflectionE1TickGapLow48.secondStageX,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem generic_toffoli (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) (hy : cy≠0) :
    toffoliCount (genericOpt L cx cy)+1=toffoliCount (genericRef L cx cy) := by
  have h:=generic_counts L hw cx cy
  have p:=odd_neg_sum cy hy
  omega

theorem generic_wires (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (genericOpt L cx cy)⊆wires (genericRef L cx cy) := by
  have a:=entryYOpt_wires L hw (-cy)
  have b:=exitYOpt_wires L hw cy
  simp only [genericOpt,genericRef,entryStageOpt,entryRef,secondStageOpt,
    ReflectionE1TickGapLow48.secondStageX,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union a (Finset.Subset.refl _)) (Finset.Subset.refl _))
    (Finset.union_subset_union (Finset.Subset.refl _) b)

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp)
    (h : GatePhysical (genericRef L cx cy)) : GatePhysical (genericOpt L cx cy) := by
  simp only [genericRef,entryRef,ReflectionE1TickGapLow48.secondStageX,gatePhysical_append] at h
  simp only [genericOpt,entryStageOpt,secondStageOpt,gatePhysical_append]
  exact ⟨⟨⟨entryYOpt_physical L hw hn (-cy),h.1.1.2⟩,h.1.2⟩,
    ⟨h.2.1,exitYOpt_physical L hw hn cy⟩⟩

end ECDSAAdd.Entrant.ParityStage
end


-- Consolidated source module: ParityEven
section
namespace ECDSAAdd.Entrant.ParityEven
open Arithmetic Secp256k1 Challenge ParityCarry
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem cached_majority (a b cin carry h : Wire) (hn : [a,b,cin,carry].Nodup)
    (hh : carry≠h) (s : State) (m : List Bool)
    (hc : s.basis cin=true) (hp : s.basis h=(!s.basis a && !s.basis b)) :
    run (majority a b cin carry) m s=run [.X carry,.CX h carry] m s := by
  rw [majority_correct a b cin carry hn]
  apply State.extensionality
  · rfl
  funext q
  by_cases hq:q=carry
  · subst q
    simp only [run,writeBit,Function.update_self,Function.update_of_ne hh.symm]
    rw [hc,hp]
    cases s.basis a <;> cases s.basis b <;> cases s.basis carry <;> rfl
  · simp [run,writeBit,Function.update,hq]

theorem even_shared_product (y k : Nat) (g : Bool)
    (hy : y<EntryFuseArithmetic.prime) (hk : k<EntryFuseArithmetic.prime) (he : k%2=0) :
    (g && decide (((y+(if g then k else 0))%EntryFuseArithmetic.prime)%2=1)) =
      ((g && decide (y%2=1)) ^^ decide (EntryFuseArithmetic.prime≤y+(if g then k else 0))) := by
  rw [EntryFuseArithmetic.output_sign_controlled y k g hy hk]
  have w:=EntryFuseArithmetic.wrap_implies_control y k g hy
  simp only [he,show ¬(0:Nat)=1 by decide,decide_false,Bool.and_false,Bool.xor_false]
  cases g <;> simp_all

def put (s : State) (q : Wire) (v : Bool) : State:=⟨s.phase,writeBit s.basis q v⟩

theorem run_put (P : Program) (m : List Bool) (s : State) (q : Wire) (v : Bool)
    (hq : q∉wires P) : run P m (put s q v)=put (run P m s) q v := by
  have agree:=pool_run_agrees P (wires P) (Finset.Subset.refl _) m (put s q v) s
    (by rfl) (by
      intro w hw
      have ne:w≠q:=fun e=>hq (e ▸ hw)
      simp [put,writeBit,ne])
  apply State.extensionality
  · exact agree.1
  funext w
  by_cases he:w=q
  · subst w
    rw [run_preserves_outside P m (put s q v) q hq]
    simp [put,writeBit]
  · by_cases hw:w∈wires P
    · simpa [put,writeBit,he] using agree.2 w hw
    · rw [run_preserves_outside P m (put s q v) w hw]
      simp [put,writeBit,he,run_preserves_outside P m s w hw]

def compareChainCached (x y carry : List Wire) (cin target h : Wire) : Program :=
  match x,y,carry with
  | a::as,b::bs,c::cs => [.X c,.CX h c]++compareChain none as bs cs c target++eraseCarry a b cin c
  | _,_,_ => compareChain none x y carry cin target

theorem compareChainCached_eq (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire)
    (hn : [a,b,cin,c].Nodup) (hh : c≠h) (s : State) (m : List Bool)
    (hc : s.basis cin=true) (hp : s.basis h=(!s.basis a && !s.basis b)) :
    run (compareChainCached (a::as) (b::bs) (c::cs) cin target h) m s=
      run (compareChain none (a::as) (b::bs) (c::cs) cin target) m s := by
  simp only [compareChainCached,compareChain,List.append_assoc,run_append,measurementCount_append]
  rw [cached_majority a b cin c h hn hh s _ hc hp]
  rfl

theorem compareChainCached_counts (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire) :
    toffoliCount (compareChainCached (a::as) (b::bs) (c::cs) cin target h)+1=
      toffoliCount (compareChain none (a::as) (b::bs) (c::cs) cin target) ∧
    measurementCount (compareChainCached (a::as) (b::bs) (c::cs) cin target h)=
      measurementCount (compareChain none (a::as) (b::bs) (c::cs) cin target) := by
  simp [compareChainCached,compareChain,majority,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount]
  omega

def compareLtCached (x y carry : List Wire) (cin target h : Wire) : Program :=
  notRegister (cin::y)++compareChainCached x y carry cin target h++notRegister (cin::y)

theorem compareLtCached_eq (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire)
    (hn : [a,b,cin,c].Nodup) (hy : (cin::b::bs).Nodup) (hao : a∉cin::b::bs)
    (hho : h∉cin::b::bs) (hhc : c≠h) (s : State) (m : List Bool)
    (hc : s.basis cin=false) (hp : s.basis h=(!s.basis a && s.basis b)) :
    run (compareLtCached (a::as) (b::bs) (c::cs) cin target h) m s=
      run (compareLt none (a::as) (b::bs) (c::cs) cin target) m s := by
  let P:=notRegister (cin::b::bs)
  let t:=run P m s
  have tr:=notRegister_correct (cin::b::bs) hy s m
  have ta:t.basis a=s.basis a := by
    change (run (notRegister (cin::b::bs)) m s).basis a=s.basis a
    rw [tr]
    change (if a∈cin::b::bs then !s.basis a else s.basis a)=s.basis a
    rw [if_neg hao]
  have th:t.basis h=s.basis h := by
    change (run (notRegister (cin::b::bs)) m s).basis h=s.basis h
    rw [tr]
    change (if h∈cin::b::bs then !s.basis h else s.basis h)=s.basis h
    rw [if_neg hho]
  have tb:t.basis b= !s.basis b := by simp [t,P,tr]
  have tc:t.basis cin=true := by simp [t,P,tr,hc]
  have eqn:=compareChainCached_eq a b c as bs cs cin target h hn hhc t m tc
    (by rw [th,ta,tb,Bool.not_not];exact hp)
  have cnt:measurementCount (compareChainCached (a::as) (b::bs) (c::cs) cin target h)=
      measurementCount (compareChain none (a::as) (b::bs) (c::cs) cin target):=
    (compareChainCached_counts a b c as bs cs cin target h).2
  simp only [compareLtCached,compareLt,List.append_assoc,run_append,run_take]
  change run P _ (run (compareChainCached _ _ _ cin target h) _ (run P _ s))=
    run P _ (run (compareChain none _ _ _ cin target) _ (run P _ s))
  simp only [(notRegister_counts (cin::b::bs)).2,List.drop_zero]
  rw [show run P m s=t from rfl,eqn,cnt]

theorem cached_flag_eq (g b f a : Wire) (hfa : f≠a) (s : State) (m : List Bool)
    (A : Bool) (ha : s.basis a=false) (hprod : (s.basis g && s.basis b)=(A ^^ s.basis f)) :
    run [.CX f a] m (put s a A)=run [.CCX g b a] m s := by
  apply State.extensionality
  · rfl
  funext q
  by_cases hq:q=a
  · subst q
    simp [run,put,writeBit,Function.update,hfa,ha,hprod]
  · simp [run,put,writeBit,Function.update,hq]

theorem masked_odd_head (g a : Wire) (as : List Wire) (v : Nat) (he : v%2=1)
    (ha : a∉as) (hag : a≠g) (s : State) (m : List Bool) :
    (run (maskedConstant g (a::as) v) m s).basis a=(s.basis a ^^ s.basis g) := by
  simp only [maskedConstant,he,if_true]
  rw [run_append,run_preserves_outside]
  · simp [run,writeBit]
  · intro hm
    have hs:=maskedConstant_wires_subset g as (v/2) hm
    simp only [List.mem_toFinset,List.mem_cons] at hs
    exact hs.elim hag ha

theorem load_odd_not (g a : Wire) (as : List Wire) (v : Nat) (he : v%2=1)
    (hn : (a::as).Nodup) (hag : a≠g) (s : State) (m : List Bool) (ha : s.basis a=false) :
    (run (loadNot g (a::as) v) m s).basis a= !s.basis g := by
  let u:=run (maskedConstant g (a::as) v) m s
  have ua:u.basis a=s.basis g := by
    rw [masked_odd_head g a as v he (List.nodup_cons.mp hn).1 hag s m,ha]
    simp
  have tr:=notRegister_correct (a::as) hn u m
  simp only [loadNot,run_append]
  simp only [run_take]
  simp only [(maskedConstant_counts _ _ _).2,List.drop_zero]
  change (run (notRegister (a::as)) m u).basis a= !s.basis g
  rw [tr]
  simp [ua]

theorem loadNot_outside (g q : Wire) (src : List Wire) (v : Nat) (s : State) (m : List Bool)
    (hqg:q≠g) (hqs:q∉src) : (run (loadNot g src v) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro h
  simp only [loadNot,wires_append,Finset.mem_union,notRegister_wires,List.mem_toFinset] at h
  rcases h with h|h
  · have H:=maskedConstant_wires_subset g src v h
    simp only [List.mem_toFinset,List.mem_cons] at H
    exact H.elim hqg hqs
  · exact hqs h

def comparePrefixCached (g h : Wire) (src out carry : List Wire) (cin flag : Wire) (v : Nat) : Program :=
  loadNot g src v++compareLtCached src out carry cin flag h++unloadNot g src v

theorem compareLtCached_counts (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire) :
    toffoliCount (compareLtCached (a::as) (b::bs) (c::cs) cin target h)+1=
      toffoliCount (compareLt none (a::as) (b::bs) (c::cs) cin target) ∧
    measurementCount (compareLtCached (a::as) (b::bs) (c::cs) cin target h)=
      measurementCount (compareLt none (a::as) (b::bs) (c::cs) cin target) := by
  have H:=compareChainCached_counts a b c as bs cs cin target h
  simp only [compareLtCached,compareLt,toffoliCount_append,measurementCount_append]
  omega

theorem comparePrefixCached_eq (g a b c cin flag h : Wire) (as bs cs : List Wire) (v : Nat)
    (he : v%2=1) (hn : (a::as).Nodup) (hag : a≠g)
    (hcg : cin≠g) (hcs : cin∉a::as) (hbg : b≠g) (hbs : b∉a::as)
    (hhg : h≠g) (hhs : h∉a::as) (hhc : c≠h)
    (hport : [a,b,cin,c].Nodup) (hy : (cin::b::bs).Nodup)
    (hao : a∉cin::b::bs) (hho : h∉cin::b::bs)
    (s : State) (m : List Bool) (ha : s.basis a=false) (hc : s.basis cin=false)
    (hp : s.basis h=(s.basis g && s.basis b)) :
    run (comparePrefixCached g h (a::as) (b::bs) (c::cs) cin flag v) m s=
      run (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v) m s := by
  apply middle_eq _ _ _ _ s m (compareLtCached_counts a b c as bs cs cin flag h).2
  intro n
  apply compareLtCached_eq a b c as bs cs cin flag h hport hy hao hho hhc
  · rw [loadNot_outside g cin (a::as) v s m hcg hcs,hc]
  · rw [loadNot_outside g h (a::as) v s m hhg hhs,
      load_odd_not g a as v he hn hag s m ha,
      loadNot_outside g b (a::as) v s m hbg hbs,Bool.not_not]
    exact hp

theorem cached_layout_eq (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256)
    (hn : (g::K.wires).Nodup) (v : Nat) (he : v%2=1)
    (s : State) (m : List Bool) (hs0 : regValue K.src s.basis=0) (hc0 : s.basis K.cin=false)
    (hp : s.basis K.high=(s.basis g && s.basis (EntryFuse.lowBit K))) :
    run (comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v) m s=
      run (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) m s := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have H:=layout_core_nodup K g hn
  rw [hs,ho,hc] at H
  have N:(g::K.high::K.cin::(K.src++K.out++K.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have C:=List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at C ⊢
    omega
  rw [hs,ho,hc] at N
  obtain ⟨gf,N⟩:=List.nodup_cons.mp N
  obtain ⟨hf,N⟩:=List.nodup_cons.mp N
  have csFree:= (List.nodup_cons.mp H).1
  have srcND:(a::as).Nodup:=H.of_cons.of_append_left.of_append_left
  have ag:a≠g:=by intro e;exact gf (by simp [←e])
  have bg:b≠g:=by intro e;exact gf (by simp [←e])
  have hg:K.high≠g:=by intro e;exact gf (by simp [←e])
  have ciSrc:K.cin∉a::as:=by
    intro h;exact csFree (List.mem_append_left _ (List.mem_append_left _ h))
  have hiSrc:K.high∉a::as:=by
    intro h;exact hf (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h)))
  have hiOut:K.high∉K.cin::b::bs:=by
    intro h
    rcases List.mem_cons.mp h with h|h
    · exact hf (List.mem_cons.mpr (Or.inl h))
    · exact hf (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ h)))
  have chi:c≠K.high:=by intro e;exact hf (by simp [←e])
  have bSrc:b∉a::as:=by
    intro h
    exact (List.nodup_append.mp H.of_cons.of_append_left).2.2 b h b (by simp) rfl
  have sa:s.basis a=false:=(regValue_zero K.src s.basis).mp hs0 a (by rw [hs];simp)
  have ph:s.basis K.high=(s.basis g && s.basis b):=by simpa [EntryFuse.lowBit,ho] using hp
  rw [hs,ho,hc]
  exact comparePrefixCached_eq g a b c K.cin K.flag K.high as bs cs v he srcND ag
    (layout_control_cin K g hn) ciSrc bg bSrc hg hiSrc chi
    (heads_nodup a b c K.cin as bs cs H) (right_nodup a b c K.cin as bs cs H)
    (left_outside a b c K.cin as bs cs H) hiOut s m sa hc0 ph

theorem comparePrefixOld_support (g cin flag : Wire) (src out carry : List Wire) (v : Nat)
    (hso : src.length=out.length) (hco : carry.length=out.length) :
    wires (comparePrefixOld g src out carry cin flag v)⊆(g::flag::cin::(src++out++carry)).toFinset := by
  let T:=(g::flag::cin::(src++out++carry)).toFinset
  have hs:src.toFinset⊆T:=by
    intro q h
    simp only [List.mem_toFinset] at h
    simp only [T,List.mem_toFinset,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
  have hm:wires (maskedConstant g src v)⊆T:=by
    intro q h
    have H:=maskedConstant_wires_subset g src v h
    simp only [List.mem_toFinset,List.mem_cons] at H
    rcases H with H|H
    · simp [T,H]
    · exact hs (List.mem_toFinset.mpr H)
  have hc:wires (compareLt none src out carry cin flag)⊆T:=by
    rw [(compareLt_wires none src out carry cin flag hso hco).1]
    intro q h
    simp only [T,Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    exact Or.inr h
  simp only [comparePrefixOld,loadNot,unloadNot,wires_append,notRegister_wires]
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset hm hs) hc) (Finset.union_subset hs hm)

theorem put_reg (r : List Wire) (s : State) (q : Wire) (v : Bool) (hq:q∉r) :
    regValue r (put s q v).basis=regValue r s.basis := by
  apply regValue_congr
  intro w hw
  have ne:w≠q:=by intro e;exact hq (e ▸ hw)
  simp [put,writeBit,ne]

theorem cachedPrefix_after_compute (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256)
    (hn : (g::K.wires).Nodup) (v : Nat) (he:v%2=1) (s : State) (m : List Bool)
    (hs0:regValue K.src s.basis=0) (hc0:s.basis K.cin=false) (hh0:s.basis K.high=false) :
    run ([.CCX g (EntryFuse.lowBit K) K.high]++
      comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v) m s=
      put (run (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) m s)
        K.high (s.basis g && s.basis (EntryFuse.lowBit K)) := by
  have free:K.high∉g::K.flag::K.cin::(K.src++K.out++K.carry):=by
    intro h
    have P:=List.count_pos_iff.mpr h
    have C:=List.nodup_iff_count.mp hn K.high
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil,
      beq_self_eq_true,if_true] at C P
    omega
  have hg:K.high≠g:=by intro e;exact free (by simp [e])
  have hci:K.cin≠K.high:=by intro e;exact free (by simp [e])
  have hsrc:K.high∉K.src:=by
    intro h;exact free (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h)))))
  have hout:K.high∉K.out:=by
    intro h;exact free (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ h)))))
  have hlb':EntryFuse.lowBit K≠K.high:=by
    intro e
    apply hout
    obtain ⟨b,bs,h⟩:=list_head K.out (by rw [hw.out];decide)
    rw [←e]
    simp [EntryFuse.lowBit,h]
  have outside:K.high∉wires (comparePrefixOld g K.src K.out K.carry K.cin K.flag v):=by
    intro h
    exact free (List.mem_toFinset.mp (comparePrefixOld_support g K.cin K.flag K.src K.out K.carry v
      (hw.src.trans hw.out.symm) (hw.carry.trans hw.out.symm) h))
  let A:=s.basis g && s.basis (EntryFuse.lowBit K)
  have pre:run [.CCX g (EntryFuse.lowBit K) K.high] m s=put s K.high A:=by
    simp [run,put,A,hh0]
  rw [run_append,run_take]
  simp only [measurementCount,List.drop_zero]
  rw [pre,cached_layout_eq K g hw hn v he (put s K.high A) m
    ((put_reg K.src s K.high A hsrc).trans hs0)
    (by simp [put,writeBit,hci,hc0])
    (by simp [put,writeBit,hg.symm,hlb',A])]
  exact run_put _ m s K.high A outside

def moveCached (h a : Wire) : Program := [.CX h a,.CX a h,.CX h a]

theorem moveCached_eq (h a : Wire) (hne:a≠h) (s : State) (m : List Bool) (A : Bool)
    (hh:s.basis h=false) (ha:s.basis a=false) :
    run (moveCached h a) m (put s h A)=put s a A := by
  apply State.extensionality
  · rfl
  funext q
  by_cases hq:q=h
  · subst q;cases A <;> simp [moveCached,run,put,writeBit,Function.update,hne,hne.symm,hh,ha]
  · by_cases hqa:q=a
    · subst q;cases A <;> simp [moveCached,run,put,writeBit,Function.update,hne,hne.symm,hh,ha]
    · simp [moveCached,run,put,writeBit,Function.update,hq,hqa]

theorem signStage_outside (K : MeasuredCanonicalModLayout) (g q : Wire) (k : Nat)
    (hw:K.Widths 256) (qo:q∉K.out) (qg:q≠g) (qf:q≠K.flag) (qh:q≠K.high) :
    q∉wires (ExitFusionResearch.signStage K g k) := by
  have lb:EntryFuse.lowBit K∈K.out:=by
    obtain ⟨b,bs,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [EntryFuse.lowBit,h]
  have sb:EntryFuse.sign K∈K.out:=by
    rw [show K.out=EntryFuse.lowOut K++[EntryFuse.sign K] from (EntryFuse.word_split K.out hw.out).symm]
    simp
  have ql:q≠EntryFuse.lowBit K:=fun e=>qo (e ▸ lb)
  have qs:q≠EntryFuse.sign K:=fun e=>qo (e ▸ sb)
  have ql':q≠ExitFusionResearch.lowBit K:=ql
  have qs':q≠ExitFusionResearch.sign K:=qs
  simp only [ExitFusionResearch.signStage,wires_append]
  rw [(rotate_wires K.out).1]
  unfold ExitFusionResearch.parityControl
  split_ifs <;> simp [wires,Instr.wires,hw.out,qo,qg,qf,qh,ql',qs']

theorem append_eq_states (P R Q : Program) (s t : State) (m : List Bool)
    (count:measurementCount P=measurementCount R) (equal:run P m s=run R m t) :
    run (P++Q) m s=run (R++Q) m t := by
  simp only [run_append,run_take]
  rw [count,equal]

theorem cached_stage_eq (S Q : Program) (h a g b f : Wire) (hne:a≠h) (hfa:f≠a)
    (s : State) (m : List Bool) (A : Bool) (hh:s.basis h=false) (ha:s.basis a=false)
    (outside:a∉wires S)
    (product:((run S m s).basis g && (run S m s).basis b)=(A ^^ (run S m s).basis f)) :
    run (moveCached h a++S++[.CX f a]++Q) m (put s h A)=
      run (S++[.CCX g b a]++Q) m s := by
  have kept:(run S m s).basis a=false:=(run_preserves_outside S m s a outside).trans ha
  have e:run (moveCached h a++S++[.CX f a]) m (put s h A)=run (S++[.CCX g b a]) m s:=by
    simp only [List.append_assoc,run_append,run_take]
    have z:measurementCount (moveCached h a)=0:=rfl
    simp only [z,List.drop_zero]
    rw [moveCached_eq h a hne s m A hh ha,run_put S m s a A outside]
    exact cached_flag_eq g b f a hfa (run S m s) _ A kept product
  apply append_eq_states _ _ Q (put s h A) s m
  · simp [measurementCount_append,moveCached,measurementCount]
  · exact e

def evenBody (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  moveCached K.high (EntryFuse.alpha K)++ExitFusionResearch.signStage K g k++
    [.CX K.flag (EntryFuse.alpha K),.CCX K.flag (EntryFuse.sign K) K.high]++
    EntryFuse.addClearBeta K g EntryFuseArithmetic.complement k++
    EntryFuse.clearWrap K g EntryFuseArithmetic.complement k

theorem evenBody_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (he:k%2=0) (rest:List Wire) (hout:K.out=EntryFuse.lowBit K::rest)
    (s:State) (m:List Bool) (hh:s.basis K.high=false) (ha:regValue K.src s.basis=0)
    (wrap:s.basis K.flag=true→s.basis g=true) :
    run (evenBody K g k) m
      (put s K.high (s.basis g && s.basis (EntryFuse.lowBit K)))=
      run (EntryFuse.entryBody K g k rest) m s := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩:=
    EntryFuse.controls_distinct K g hn hw
  have go:g∉K.out:=EntryFuse.controls_fullOut K g hn hw g (by simp [EntryFuse.controls]) hgS
  have fo:K.flag∉K.out:=EntryFuse.controls_fullOut K g hn hw K.flag (by simp [EntryFuse.controls]) hfS
  have ao:EntryFuse.alpha K∉K.out:=EntryFuse.controls_fullOut K g hn hw (EntryFuse.alpha K)
    (by simp [EntryFuse.controls]) haS
  have ho:K.high∉K.out:=EntryFuse.controls_fullOut K g hn hw K.high (by simp [EntryFuse.controls]) hhS
  have ac:EntryFuse.alpha K∈K.src:=by
    rw [show K.src=EntryFuse.lowSrc K++[EntryFuse.alpha K] from (EntryFuse.word_split K.src hw.src).symm]
    simp
  have a0:s.basis (EntryFuse.alpha K)=false:=(regValue_zero K.src s.basis).mp ha _ ac
  have outND:K.out.Nodup:=EntryFuse.out_nodup K g hn
  have sign:=EntryFuse.signStage_correct (EntryFuse.lowBit K) g K.flag K.high rest k
    (by rw [←hout];exact hw.out) (by rw [←hout];exact outND)
    (by rw [←hout];exact ho) (by rw [←hout];exact go) (by rw [←hout];exact fo)
    hgH hfH s m hh
  let S:=ExitFusionResearch.signStage K g k
  have eqS:=ExitFusionProof.signStage_eq K g k rest hout
  have tg:(run S m s).basis g=s.basis g:=by
    simpa only [S,eqS,←hout] using sign.2.2.2.2 g (by rw [←hout];exact go) hgH
  have tf:(run S m s).basis K.flag=s.basis K.flag:=by
    simpa only [S,eqS,←hout] using sign.2.2.2.2 K.flag (by rw [←hout];exact fo) hfH
  have ts:(run S m s).basis (EntryFuse.sign K)=
      (s.basis (EntryFuse.lowBit K) ^^ s.basis K.flag):=by
    have ne:¬k%2=1:=by omega
    simpa only [S,eqS,←hout,EntryFuse.sign,ne,if_false,Bool.xor_false] using sign.2.2.1
  have product:((run S m s).basis g && (run S m s).basis (EntryFuse.sign K))=
      ((s.basis g && s.basis (EntryFuse.lowBit K)) ^^ (run S m s).basis K.flag):=by
    rw [tg,tf,ts]
    cases hg:s.basis g <;> cases hb:s.basis (EntryFuse.lowBit K) <;>
      cases hf:s.basis K.flag <;> simp_all
  have outA:EntryFuse.alpha K∉wires S:=signStage_outside K g (EntryFuse.alpha K) k hw ao hgA.symm hfA.symm hhA.symm
  have E:=cached_stage_eq S
    ([.CCX K.flag (EntryFuse.sign K) K.high]++EntryFuse.addClearBeta K g EntryFuseArithmetic.complement k++
      EntryFuse.clearWrap K g EntryFuseArithmetic.complement k)
    K.high (EntryFuse.alpha K) g (EntryFuse.sign K) K.flag hhA.symm hfA s m
    (s.basis g && s.basis (EntryFuse.lowBit K)) hh a0 outA product
  simpa only [evenBody,EntryFuse.entryBody,EntryFuse.entryMiddle,EntryFuse.middle,EntryFuse.makeFlags,
    S,eqS,List.append_assoc,List.cons_append,List.nil_append] using E

theorem cached_prefix_measurements (K : MeasuredCanonicalModLayout) (g : Wire) (hw:K.Widths 256) (v:Nat) :
    measurementCount ([.CCX g (EntryFuse.lowBit K) K.high]++
      comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v)=
      measurementCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have H:=(compareLtCached_counts a b c as bs cs K.cin K.flag K.high).2
  simp only [hs,ho,hc,comparePrefixCached,comparePrefixOld,measurementCount_append,measurementCount]
  rw [H]
  omega

def entryEven (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  [.CCX g (EntryFuse.lowBit K) K.high]++
    comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag (EntryFuseArithmetic.complement+k)++
    evenBody K g k

theorem entryEven_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (he:k%2=0) (hy:Y<EntryFuseArithmetic.prime) (hk:k<EntryFuseArithmetic.prime)
    (s:State) (m:List Bool) (hY:regValue K.out s.basis=Y) (hs:regValue K.src s.basis=0)
    (hf:s.basis K.flag=false) (hh:s.basis K.high=false) (hc:s.basis K.cin=false)
    (carry:∀q∈K.carry,s.basis q=false) :
    run (entryEven K g k) m s=run (EntryFuse.entry K g EntryFuseArithmetic.complement k) m s := by
  let c:=EntryFuseArithmetic.complement
  let P:=[Instr.CCX g (EntryFuse.lowBit K) K.high]++
    comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag (c+k)
  let O:=comparePrefixOld g K.src K.out K.carry K.cin K.flag (c+k)
  let n:=measurementCount O
  let t:=run O (m.take n) s
  have cmp:measurementCount P=measurementCount O:=cached_prefix_measurements K g hw (c+k)
  have cp:(c+k)%2=1:=by
    have cmod:c%2=1:=by norm_num [c,EntryFuseArithmetic.complement]
    omega
  have cachedRun:run P (m.take n) s=put t K.high (s.basis g && s.basis (EntryFuse.lowBit K)):=
    cachedPrefix_after_compute K g hw hn (c+k) cp s (m.take n) hs hc hh
  have pc:EntryFuseArithmetic.prime+c=2^256:=by norm_num [c,EntryFuseArithmetic.prime,
    EntryFuseArithmetic.modulus,EntryFuseArithmetic.complement]
  have initial:FastConst.Frame K s.basis 0 Y false s.basis:=⟨hs,hY,hf,by intro q hq;rfl⟩
  have pre:=EntryFuse.comparePrefix_correct hn 256 hw s.basis carry hc c EntryFuseArithmetic.prime k Y
    pc hk hy s (m.take n) initial
  have oe:O=EntryFuse.comparePrefix K g c k:=by
    simp only [O,comparePrefixOld,loadNot,unloadNot,EntryFuse.comparePrefix,List.append_assoc]
  rw [←oe] at pre
  change t.phase=s.phase ∧ FastConst.Frame K s.basis 0 Y
    (if s.basis g then decide (EntryFuseArithmetic.prime≤Y+k) else false) t.basis at pre
  have tg:t.basis g=s.basis g:=pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th:t.basis K.high=false:=(pre.2.2.2.2 K.high
    (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have wrap:t.basis K.flag=true→t.basis g=true:=by
    intro hf'
    rw [tg]
    have f:=pre.2.2.2.1
    cases hg:s.basis g <;> simp_all
  have lb:EntryFuse.lowBit K∈K.out:=by
    obtain ⟨b,bs,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [EntryFuse.lowBit,h]
  have tv:t.basis (EntryFuse.lowBit K)=s.basis (EntryFuse.lowBit K):=
    (regValue_eq_iff K.out t.basis s.basis).mp (pre.2.2.1.trans hY.symm) _ lb
  rw [←tg,←tv] at cachedRun
  obtain ⟨rest,hout⟩:=EntryFuse.out_shape K hw
  have decomp:=ParityConvert.old_entry_split K g hw k
  rw [decomp]
  change run (P++evenBody K g k) m s=run (O++EntryFuse.entryBody K g k K.out.tail) m s
  simp only [run_append,cmp]
  change run (evenBody K g k) (m.drop n) (run P (m.take n) s)=
    run (EntryFuse.entryBody K g k K.out.tail) (m.drop n) t
  rw [cachedRun]
  exact evenBody_eq K g k hw hn he K.out.tail
    (by rw [hout];rfl) t (m.drop n) th pre.2.1 wrap

theorem evenBody_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (rest:List Wire) (hout:K.out=EntryFuse.lowBit K::rest) :
    toffoliCount (evenBody K g k)+1=toffoliCount (EntryFuse.entryBody K g k rest) ∧
    measurementCount (evenBody K g k)=measurementCount (EntryFuse.entryBody K g k rest) ∧
    gateSlots (evenBody K g k)=gateSlots (EntryFuse.entryBody K g k rest)+3 := by
  have e:=ExitFusionProof.signStage_eq K g k rest hout
  simp only [evenBody,EntryFuse.entryBody,EntryFuse.entryMiddle,EntryFuse.middle,EntryFuse.makeFlags,
    toffoliCount_append,measurementCount_append,gateSlots_append,e]
  simp only [moveCached,toffoliCount,measurementCount,gateSlots,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,instructionSlots]
  omega

theorem retain_product (g b f a h : Wire) (ga:g≠a) (ba:b≠a) (_fa:f≠a) (ha:h≠a)
    (s:State) (m n:List Bool) (hh:s.basis h=false) (known:s.basis a=(s.basis g && s.basis b)) :
    run [.CX f a,.measureX h [] []] m s=
      put (run [.measureX a [] [.CZ g b]] n s) a
        ((s.basis g && s.basis b) ^^ s.basis f) := by
  rw [EntryFuse.erase_and g b a ga ba s n known]
  apply State.extensionality
  · simp [run,measureAndCorrect,correct,put,writeBit,ha,hh]
  funext q
  by_cases qa:q=a
  · subst q
    simp [run,measureAndCorrect,correct,put,writeBit,Function.update,ha,ha.symm,known]
  · by_cases qh:q=h
    · subst q
      simp [run,measureAndCorrect,correct,put,writeBit,Function.update,ha,hh]
    · simp [run,measureAndCorrect,correct,put,writeBit,Function.update,qa,qh]

theorem compareChainCached_slots (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire) :
    gateSlots (compareChainCached (a::as) (b::bs) (c::cs) cin target h)+4=
      gateSlots (compareChain none (a::as) (b::bs) (c::cs) cin target) := by
  simp [compareChainCached,compareChain,majority,gateSlots_append,
    gateSlots,instructionSlots]
  omega

theorem cached_layout_counts (K : MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (v:Nat) :
    let P:=[Instr.CCX g (EntryFuse.lowBit K) K.high]++
      comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v
    toffoliCount P=toffoliCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) ∧
    measurementCount P=measurementCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) ∧
    gateSlots P+3=gateSlots (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have H:=compareChainCached_slots a b c as bs cs K.cin K.flag K.high
  have C:=compareChainCached_counts a b c as bs cs K.cin K.flag K.high
  simp only [hs,ho,hc,comparePrefixCached,comparePrefixOld,compareLtCached,compareLt,
    toffoliCount_append,measurementCount_append,gateSlots_append]
  simp only [toffoliCount,measurementCount,gateSlots,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,instructionSlots] at *
  omega

theorem entryEven_counts (K : MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (k:Nat) :
    toffoliCount (entryEven K g k)+1=766 ∧ measurementCount (entryEven K g k)=767 ∧
    gateSlots (entryEven K g k)=gateSlots (EntryFuse.entry K g EntryFuseArithmetic.complement k) := by
  obtain ⟨rest,hout⟩:=EntryFuse.out_shape K hw
  have C:=cached_layout_counts K g hw (EntryFuseArithmetic.complement+k)
  have B:=evenBody_counts K g k rest hout
  have O:=EntryFuse.entry_counts K g EntryFuseArithmetic.complement k hw
  have split:=ParityConvert.old_entry_split K g hw k
  have tail:K.out.tail=rest:=by rw [hout];rfl
  rw [tail] at split
  have t:=congrArg toffoliCount split
  have m:=congrArg measurementCount split
  have slots:=congrArg gateSlots split
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append] at t m slots
  unfold entryEven
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append]
  dsimp only at C
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append] at C
  omega

theorem move_borrow (a b cin c h : Wire) (hn:[a,b,cin,c].Nodup) (ch:c≠h)
    (s:State) (m:List Bool) (hc:s.basis cin=false) (cz:s.basis c=false) (hz:s.basis h=false) :
    run [.CX h c,.CX c h] m (put s h (!s.basis a && s.basis b))=
      run (borrowMajority a b cin c) m s := by
  rw [borrowMajority_correct a b cin c hn]
  apply State.extensionality
  · rfl
  funext q
  by_cases qc:q=c
  · subst q
    cases aa:s.basis a <;> cases bb:s.basis b <;>
      simp [run,put,writeBit,Function.update,ch,ch.symm,carryBit,hc,cz,aa,bb]
  · by_cases qh:q=h
    · subst q
      cases aa:s.basis a <;> cases bb:s.basis b <;>
        simp [run,put,writeBit,Function.update,ch,ch.symm,carryBit,hc,cz,hz,aa,bb]
    · simp [run,put,writeBit,Function.update,qc,qh]

def eraseLtMoved (x y carry : List Wire) (cin target h : Wire) : Program :=
  match x,y,carry with
  | a::a'::as,b::b'::bs,c::cs =>
      [.CX h c,.CX c h]++eraseLtChain (a'::as) (b'::bs) cs c target++eraseBorrow a b cin c
  | _,_,_ => eraseLtChain x y carry cin target

theorem eraseLtMoved_eq (a a' b b' c : Wire) (as bs cs:List Wire) (cin target h:Wire)
    (hn:[a,b,cin,c].Nodup) (ch:c≠h) (s:State) (m:List Bool)
    (hc:s.basis cin=false) (cz:s.basis c=false) (hz:s.basis h=false) :
    run (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h) m
      (put s h (!s.basis a && s.basis b))=
      run (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) m s := by
  apply append_eq_states _ _ (eraseBorrow a b cin c) _ s m
  · simp [measurementCount_append,measurementCount,borrowMajority,majority]
  · apply append_eq_states _ _ (eraseLtChain (a'::as) (b'::bs) cs c target)
    · simp [measurementCount,borrowMajority,majority,measurementCount_append]
    · exact move_borrow a b cin c h hn ch s m hc cz hz

theorem cleanup_keep_product (K:MeasuredCanonicalModLayout) (g:Wire)
    (hgA:g≠EntryFuse.alpha K) (hsA:EntryFuse.sign K≠EntryFuse.alpha K) (hfA:K.flag≠EntryFuse.alpha K)
    (hgH:g≠K.high) (hsH:EntryFuse.sign K≠K.high) (hfH:K.flag≠K.high)
    (haH:EntryFuse.alpha K≠K.high) (s:State) (m n l:List Bool)
    (ha:s.basis (EntryFuse.alpha K)=false) (hh:s.basis K.high=false) :
    run [.CX K.flag (EntryFuse.alpha K),.measureX K.high [] []] l
      (run [.measureX K.high [] [.CZ K.flag (EntryFuse.sign K)]] n
        (run (EntryFuse.makeFlags K g) m s))=
      put s (EntryFuse.alpha K) ((s.basis g && s.basis (EntryFuse.sign K)) ^^ s.basis K.flag) := by
  let t:=run (EntryFuse.makeFlags K g) m s
  have mf:=EntryFuse.makeFlags_correct K g hgA hsA hfA haH s m ha hh
  have tg:t.basis g=s.basis g:=mf.2.2.2 g hgA hgH
  have tf:t.basis K.flag=s.basis K.flag:=mf.2.2.2 _ hfA hfH
  have ts:t.basis (EntryFuse.sign K)=s.basis (EntryFuse.sign K):=mf.2.2.2 _ hsA hsH
  have beta:t.basis K.high=(t.basis K.flag && t.basis (EntryFuse.sign K)):=by rw [mf.2.2.1,tf,ts]
  have erB:=EntryFuse.erase_and K.flag (EntryFuse.sign K) K.high hfH hsH t n beta
  let u:State:=⟨t.phase,writeBit t.basis K.high false⟩
  have keep (q:Wire) (hq:q≠K.high):u.basis q=t.basis q:=by simp [u,writeBit,hq]
  have alphaKnown:u.basis (EntryFuse.alpha K)=(u.basis g && u.basis (EntryFuse.sign K)):=by
    rw [keep _ haH,keep _ hgH,keep _ hsH,mf.2.1,tg,ts]
  have highZero:u.basis K.high=false:=by simp [u,writeBit]
  have eraseAll:=ExitFusionProof.cleanup_makeFlags_inverse K g hgA hsA hfA hgH hsH hfH haH s m n l ha hh
  change run _ l (run _ n t)=_ at eraseAll ⊢
  rw [erB] at eraseAll ⊢
  have retain:=retain_product g (EntryFuse.sign K) K.flag (EntryFuse.alpha K) K.high
    hgA hsA hfA haH.symm u l l highZero alphaKnown
  change run _ l u=_ at eraseAll ⊢
  rw [retain,eraseAll]
  rw [keep _ hgH,keep _ hsH,keep _ hfH,tg,ts,tf]

open EntryFuse ExitFusionProof EntryFuseArithmetic

def undoMiddleKeep (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat) : Program :=
  [.CCX K.flag (EntryFuse.sign K) K.high]++ExitFusionResearch.table K g c k++
    mappedSub (mappedRead (EntryFuse.lowSrc K) false) (EntryFuse.lowOut K) (K.carry.take 254) K.cin++
    ExitFusionResearch.untabled K g c k++[.measureX K.high [] [.CZ K.flag (EntryFuse.sign K)],
      .CX K.flag (EntryFuse.alpha K),.measureX K.high [] []]

private theorem run_three (A B C : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 : List Bool, run (A++B++C) m s=run C m3 (run B m2 (run A m1 s)) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    (m.drop (measurementCount A)).drop (measurementCount B),by simp only [List.append_assoc,run_append]⟩
private theorem run_four (A B C D : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 m4 : List Bool, run (A++B++C++D) m s=run D m4 (run C m3 (run B m2 (run A m1 s))) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    ((m.drop (measurementCount A)).drop (measurementCount B)).take (measurementCount C),
    ((m.drop (measurementCount A)).drop (measurementCount B)).drop (measurementCount C),
    by simp only [List.append_assoc,run_append]⟩

theorem undoMiddleKeep_middle_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n : List Bool)
    (ha0 : s.basis (alpha K)=false) (hh0 : s.basis K.high=false)
    (hcarry : ∀q∈K.carry.take 254,s.basis q=false) (hcin : s.basis K.cin=false) :
    run (undoMiddleKeep K g c k) n (run (middle K g c k) m s)=put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis K.flag) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q∈controls K g) : q∉lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q∈controls K g) : q∉lowOut K := controls_out K g hn hw q h
  have cc (q : Wire) (h : q∈controls K g) : q∉K.carry.take 254 := carry_away K g hn hw q h
  have hctrlSrc : ∀e∈entryMasks K g c k,e.1∉lowSrc K := by
    intro e he; exact cs _ ((mask_controls K g c k).1 e he)
  have hctrlOut : ∀e∈entryMasks K g c k,e.1∉lowOut K := by
    intro e he; exact co _ ((mask_controls K g c k).1 e he)
  have haway : ∀q∈mappedWires (mappedRead (lowSrc K) false),q∉K.cin::(lowOut K++K.carry.take 254) := by
    simpa only [mappedRead_wires] using src_away K g hn hw
  let M := makeFlags K g
  let T := tableAdd K g c k
  let E : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  obtain ⟨m1,m2,m3,forward⟩ := run_three M T E m s
  have mf := makeFlags_correct K g hgA (Ne.symm haS) hfA (Ne.symm hhA) s m1 ha0 hh0
  let s1 := run M m1 s
  let s2 := run T m2 s1
  let s3 := run E m3 s2
  have frame (q : Wire) (hqa : q≠alpha K) (hqh : q≠K.high) : s1.basis q=s.basis q := mf.2.2.2 q hqa hqh
  have clean : ∀q∈K.carry.take 254,s1.basis q=false := by
    intro q hq
    have qa : q≠alpha K := fun e => cc (alpha K) (by simp [controls]) (e ▸ hq)
    have qh : q≠K.high := fun e => cc K.high (by simp [controls]) (e ▸ hq)
    exact (frame q qa qh).trans (hcarry q hq)
  have ci : s1.basis K.cin=false := (frame _ hcA (Ne.symm hhC)).trans hcin
  have ad := tableAdd_correct K g c k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1,low.2.1]) (by rw [low.2.2,low.2.1]) hctrlSrc hctrlOut s1 m2 clean ci
  have f2 : s2.basis K.flag=s.basis K.flag :=
    (ad.2.2 _ (co _ (by simp [controls]))).trans (frame _ hfA hfH)
  have sg2 : s2.basis (sign K)=s.basis (sign K) :=
    (ad.2.2 _ (co _ (by simp [controls]))).trans (frame _ (Ne.symm haS) (Ne.symm hhS))
  have beta : s2.basis K.high=(s2.basis K.flag && s2.basis (sign K)) := by
    rw [ad.2.2 _ (co _ (by simp [controls])),mf.2.2.1,f2,sg2]
  let A : Program := [.CCX K.flag (sign K) K.high]
  let B := tableSub K g c k
  let C : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  let D : Program := [.CX K.flag (alpha K),.measureX K.high [] []]
  obtain ⟨n1,n2,n3,n4,inverse⟩ := run_four A B C D n s3
  have restore : run A n1 s3=s2 := recompute_measured_and K.flag (sign K) K.high hfH
    (Ne.symm hhS) s2 m3 n1 beta
  have sub := tableSub_tableAdd_inverse K g c k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1,low.2.1]) (by rw [low.2.2,low.2.1]) hctrlSrc s1 m2 n2 clean ci
  have goal : run (A++B++C++D) n (run (M++T++E) m s)=put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis K.flag) := by
    rw [forward]
    change run (A++B++C++D) n s3=put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis K.flag)
    rw [inverse,restore,sub]
    exact cleanup_keep_product K g hgA (Ne.symm haS) hfA hgH (Ne.symm hhS) hfH
      (Ne.symm hhA) s m1 n3 n4 ha0 hh0
  simpa only [middle,addClearBeta,undoMiddleKeep,tableSub,
    M,T,E,A,B,C,D,List.append_assoc] using goal


theorem undo_entryMiddleKeep_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (he:k%2=0)
    (rest : List Wire) (hout : K.out=lowBit K::rest)
    (s : State) (m n r : List Bool) (hsrc : regValue K.src s.basis=0)
    (hh : s.basis K.high=false) (hcin : s.basis K.cin=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) (wrap:s.basis K.flag=true→s.basis g=true) :
    run (ExitFusionResearch.signStage K g k).reverse r
      (run (undoMiddleKeep K g complement k) n
        (run (entryMiddle K g k rest) m s))=put s (alpha K) (s.basis g && s.basis (lowBit K)) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have cio : K.cin∉K.out := controls_fullOut K g hn hw K.cin (by simp [controls]) hcS
  have ho : K.high∉K.out := controls_fullOut K g hn hw K.high (by simp [controls]) hhS
  have go : g∉K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have fo : K.flag∉K.out := controls_fullOut K g hn hw K.flag (by simp [controls]) hfS
  have am : alpha K∈K.src := by
    rw [show K.src=lowSrc K++[alpha K] from (word_split K.src hw.src).symm]; simp
  have ao : alpha K∉K.out := src_fullOut K g hn _ am
  have a0 : s.basis (alpha K)=false := (regValue_zero K.src s.basis).mp hsrc _ am
  let P := ExitFusionResearch.signStage K g k
  have proper := ExitFusionResearch.signStage_proper K g k hn hw
  have eqP := signStage_eq K g k rest hout
  have zero : measurementCount P=0 := properProgram_measurementCount P proper
  let t := run P [] s
  have first := signStage_correct (lowBit K) g K.flag K.high rest k
    (by rw [←hout]; exact hw.out) (by rw [←hout]; exact FastConst.out_nodup hn)
    (by rw [←hout]; exact ho) (by rw [←hout]; exact go) (by rw [←hout]; exact fo)
    hgH hfH s [] hh
  rw [←eqP] at first
  rw [←hout] at first
  have high : t.basis K.high=false := first.2.2.2.1
  have alphaClean : t.basis (alpha K)=false :=
    (first.2.2.2.2 _ ao (Ne.symm hhA)).trans a0
  have carry : ∀q∈K.carry.take 254,t.basis q=false := by
    intro q hq
    have mem := List.mem_of_mem_take hq
    have qo := carry_fullOut K g hn q mem
    have qh : q≠K.high := by
      intro e
      have bad := carry_away K g hn hw K.high (by simp [controls])
      exact bad (e ▸ hq)
    exact (first.2.2.2.2 q qo qh).trans (hcarry q mem)
  have ci : t.basis K.cin=false := (first.2.2.2.2 _ cio (Ne.symm hhC)).trans hcin
  have middle := undoMiddleKeep_middle_inverse K g complement k hn hw t m n alphaClean high carry ci
  rw [entryMiddle,←eqP,run_append,zero,List.take_zero,List.drop_zero]
  rw [middle]
  have outA:alpha K∉wires P.reverse:=by
    rw [wires_reverse]
    exact signStage_outside K g (alpha K) k hw ao hgA.symm hfA.symm hhA.symm
  rw [run_put P.reverse r t (alpha K) _ outA,run_reverse_proper P proper s [] r]
  have tg:t.basis g=s.basis g:=first.2.2.2.2 g go hgH
  have tf:t.basis K.flag=s.basis K.flag:=first.2.2.2.2 K.flag fo hfH
  have ts:t.basis (sign K)=(s.basis (lowBit K) ^^ s.basis K.flag):=by
    have ne:¬k%2=1:=by omega
    simpa only [ne,if_false,Bool.xor_false] using first.2.2.1
  rw [tg,tf,ts]
  congr 1
  cases hg:s.basis g <;> cases hb:s.basis (lowBit K) <;>
    cases hf:s.basis K.flag <;> simp_all


theorem eraseLtMoved_measurements (a a' b b' c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    measurementCount (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)=
      measurementCount (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) := by
  simp [eraseLtMoved,eraseLtChain,measurementCount_append,borrowMajority,majority,measurementCount]

def erasePrefixMoved (g h:Wire) (src out carry:List Wire) (cin flag:Wire) (v:Nat) : Program :=
  loadNot g src v++eraseLtMoved src out carry cin flag h++unloadNot g src v

theorem erasePrefixMoved_eq (g a a' b b' c cin flag h:Wire) (as bs cs:List Wire) (v:Nat)
    (he:v%2=1) (hn:(a::a'::as).Nodup) (hag:a≠g)
    (hcg:cin≠g) (hcs:cin∉a::a'::as) (hbg:b≠g) (hbs:b∉a::a'::as)
    (hhg:h≠g) (hhs:h∉a::a'::as) (ch:c≠h) (ccg:c≠g) (ccs:c∉a::a'::as)
    (hport:[a,b,cin,c].Nodup) (s:State) (m:List Bool)
    (ha:s.basis a=false) (hc:s.basis cin=false) (cz:s.basis c=false) (hz:s.basis h=false) :
    run (erasePrefixMoved g h (a::a'::as) (b::b'::bs) (c::cs) cin flag v) m
      (put s h (s.basis g && s.basis b))=
      run (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) m s := by
  let P:=loadNot g (a::a'::as) v
  let t:=run P m s
  have outP:h∉wires P:=by
    intro H
    simp only [P,loadNot,wires_append,notRegister_wires,Finset.mem_union,List.mem_toFinset] at H
    rcases H with H|H
    · have R:=maskedConstant_wires_subset g (a::a'::as) v H
      simp only [List.mem_toFinset,List.mem_cons] at R
      exact R.elim hhg (fun r=>hhs (by simpa only [List.mem_cons] using r))
    · exact hhs H
  have ac:t.basis a= !s.basis g:=load_odd_not g a (a'::as) v he hn hag s m ha
  have cb:t.basis b=s.basis b:=loadNot_outside g b _ v s m hbg hbs
  have ci:t.basis cin=false:=(loadNot_outside g cin _ v s m hcg hcs).trans hc
  have ca:t.basis c=false:=(loadNot_outside g c _ v s m ccg ccs).trans cz
  have hi:t.basis h=false:=(loadNot_outside g h _ v s m hhg hhs).trans hz
  have product:(!t.basis a && t.basis b)=(s.basis g && s.basis b):=by rw [ac,cb,Bool.not_not]
  apply append_eq_states _ _ (unloadNot g (a::a'::as) v) _ s m
  · simp only [measurementCount_append]
    rw [eraseLtMoved_measurements]
  · simp only [run_append,run_take]
    have zero:measurementCount P=0:=by simp [P,loadNot,measurementCount_append,
      (maskedConstant_counts _ _ _).2,(notRegister_counts _).2]
    change run (eraseLtMoved _ _ _ cin flag h) (m.drop (measurementCount P)) (run P m _)=
      run (eraseLtChain _ _ _ cin flag) (m.drop (measurementCount P)) (run P m s)
    rw [zero,List.drop_zero,run_put P m s h _ outP,←product]
    exact eraseLtMoved_eq a a' b b' c as bs cs cin flag h hport ch t m ci ca hi

theorem eraseMoved_layout_eq (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (v:Nat) (he:v%2=1) (s:State) (m:List Bool)
    (hs0:regValue K.src s.basis=0) (hc0:s.basis K.cin=false) (hh0:s.basis K.high=false)
    (hcarry:∀q∈K.carry,s.basis q=false) :
    run (erasePrefixMoved g K.high K.src K.out (K.carry.take 255) K.cin K.flag v) m
      (put s K.high (s.basis g && s.basis (lowBit K)))=
      run (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) m s := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  have H:=layout_core_take_nodup K g 255 hn
  rw [hs,ho,hc] at H
  have N:(g::K.high::K.cin::(K.src++K.out++K.carry.take 255)).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have C:=List.nodup_iff_count.mp hn q
    have T:=(List.take_sublist 255 K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at C ⊢
    omega
  rw [hs,ho,hc] at N
  obtain ⟨gf,N⟩:=List.nodup_cons.mp N
  obtain ⟨hf,N⟩:=List.nodup_cons.mp N
  have csFree:=(List.nodup_cons.mp H).1
  have srcND:(a::a'::as).Nodup:=H.of_cons.of_append_left.of_append_left
  have ag:a≠g:=by intro e;exact gf (by simp [←e])
  have bg:b≠g:=by intro e;exact gf (by simp [←e])
  have hg:K.high≠g:=by intro e;exact gf (by simp [←e])
  have cg:c≠g:=by intro e;exact gf (by simp [←e])
  have ciSrc:K.cin∉a::a'::as:=by
    intro h;exact csFree (List.mem_append_left _ (List.mem_append_left _ h))
  have hiSrc:K.high∉a::a'::as:=by
    intro h;exact hf (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h)))
  have chi:c≠K.high:=by intro e;exact hf (by simp [←e])
  have bSrc:b∉a::a'::as:=by
    intro h
    exact (List.nodup_append.mp H.of_cons.of_append_left).2.2 b h b (by simp) rfl
  have cSrc:c∉a::a'::as:=by
    intro h
    exact (List.nodup_append.mp H.of_cons).2.2 c (List.mem_append_left _ h) c (by simp) rfl
  have sa:s.basis a=false:=(regValue_zero K.src s.basis).mp hs0 a (by rw [hs];simp)
  have cz:s.basis c=false:=hcarry c (List.mem_of_mem_take (by rw [hc];simp))
  have lb:lowBit K=b:=by simp [lowBit,ho]
  rw [lb,hs,ho,hc]
  exact erasePrefixMoved_eq g a a' b b' c K.cin K.flag K.high as bs cs v he srcND ag
    (layout_control_cin K g hn) ciSrc bg bSrc hg hiSrc chi cg cSrc
    (heads_nodup a b c K.cin (a'::as) (b'::bs) cs H) s m sa hc0 cz hh0

def eraseInputMoved (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) : Program :=
  moveCached (alpha K) K.high++
    erasePrefixMoved g K.high K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)

theorem eraseInputMoved_eq (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (k:Nat) (he:k%2=0) (s:State) (m:List Bool)
    (hs0:regValue K.src s.basis=0) (hc0:s.basis K.cin=false) (hh0:s.basis K.high=false)
    (hcarry:∀q∈K.carry,s.basis q=false) :
    run (eraseInputMoved K g k) m (put s (alpha K) (s.basis g && s.basis (lowBit K)))=
      run (ExitFusionResearch.eraseInputWrap K g complement k) m s := by
  have pc:(complement+k)%2=1:=by
    have C:complement%2=1:=by norm_num [complement]
    omega
  have hhA:K.high≠alpha K:=(EntryFuse.controls_distinct K g hn hw).2.2.2.2.2.2.2.2.2.2.1
  have am:alpha K∈K.src:=by
    rw [show K.src=lowSrc K++[alpha K] from (word_split K.src hw.src).symm];simp
  have az:s.basis (alpha K)=false:=(regValue_zero K.src s.basis).mp hs0 _ am
  have old:erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)=
      ExitFusionResearch.eraseInputWrap K g complement k:=by
    simp only [erasePrefixOld,loadNot,unloadNot,ExitFusionResearch.eraseInputWrap,List.append_assoc]
  rw [←old]
  unfold eraseInputMoved
  rw [run_append,run_take]
  have z:measurementCount (moveCached (alpha K) K.high)=0:=rfl
  rw [z,List.drop_zero,moveCached_eq (alpha K) K.high hhA s m _ az hh0]
  exact eraseMoved_layout_eq K g hw hn (complement+k) pc s m hs0 hc0 hh0 hcarry

def exitEven (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) : Program :=
  ExitFusionResearch.recoverWrap K g complement k++undoMiddleKeep K g complement k++
    (ExitFusionResearch.signStage K g k).reverse++eraseInputMoved K g k

theorem exitEven_entry_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (he:k%2=0)
    (s : State) (m n : List Bool) (hY : regValue K.out s.basis=Y)
    (hy : Y<prime) (hk : k<prime) (hsrc : regValue K.src s.basis=0)
    (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    run (exitEven K g k) n (run (EntryFuse.entry K g complement k) m s)=s := by
  obtain ⟨rest,hout⟩ := out_shape K hw
  have pc : prime+complement=2^256 := by norm_num [prime,modulus,complement]
  let m1 := m.take (measurementCount (entryCompare K g complement k))
  let m2 := m.drop (measurementCount (entryCompare K g complement k))
  let t := run (entryCompare K g complement k) m1 s
  have initial : FastConst.Frame K s.basis 0 Y false s.basis := ⟨hsrc,hY,hf,by intro q hq; rfl⟩
  have pre := comparePrefix_correct hn 256 hw s.basis hcarry hcin complement prime k Y pc hk hy s m1 initial
  change t.phase=s.phase ∧ FastConst.Frame K s.basis 0 Y
    (if s.basis g then decide (prime≤Y+k) else false) t.basis at pre
  have tg : t.basis g=s.basis g := pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th : t.basis K.high=false := (pre.2.2.2.2 K.high
    (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have tcin : t.basis K.cin=false := (pre.2.2.2.2 K.cin
    (FastConst.fixed_not_mutable hn K.cin (by simp))).trans hcin
  have tcarry : ∀q∈K.carry,t.basis q=false := by
    intro q hq
    exact (pre.2.2.2.2 q (FastConst.fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have tflag : t.basis K.flag=decide (prime≤Y+(if t.basis g then k else 0)) := by
    rw [tg]
    have h := pre.2.2.2.1
    cases hg : s.basis g <;> simp [hg,show ¬prime≤Y by omega] at h ⊢ <;> exact h
  let A := ExitFusionResearch.recoverWrap K g complement k
  let B := undoMiddleKeep K g complement k
  let C := (ExitFusionResearch.signStage K g k).reverse
  let D := eraseInputMoved K g k
  obtain ⟨n1,n2,n3,n4,parts⟩ := run_four A B C D n (run (entryBody K g k rest) m2 t)
  have recover : run A n1 (run (entryBody K g k rest) m2 t)=
      run (entryMiddle K g k rest) (m2.take (measurementCount (entryMiddle K g k rest))) t :=
    recover_entryBody K g k Y hn hw rest hout t m2 n1 pre.2.2.1 hy hk pre.2.1 th tcin tcarry tflag
  have wrap:t.basis K.flag=true→t.basis g=true:=by
    intro f
    rw [tg]
    have tf:=pre.2.2.2.1
    cases G:s.basis g <;> simp_all
  have undo : run C n3 (run B n2
      (run (entryMiddle K g k rest) (m2.take (measurementCount (entryMiddle K g k rest))) t))=put t (alpha K) (t.basis g && t.basis (lowBit K)) :=
    undo_entryMiddleKeep_inverse K g k hn hw he rest hout t _ n2 n3 pre.2.1 th tcin tcarry wrap
  have erase : run D n4 (put t (alpha K) (t.basis g && t.basis (lowBit K)))=s :=
    (eraseInputMoved_eq K g hw hn k he t n4 pre.2.1 tcin th tcarry).trans
      (eraseInput_entryCompare_inverse K g k Y hn hw s m1 n4 hY hy hk hsrc hf hcin hcarry)
  have decomp : EntryFuse.entry K g complement k=entryCompare K g complement k++entryBody K g k rest := by
    rw [entry_decompose K g complement k rest hout]
    simp only [entryBody,entryMiddle,List.append_assoc]
  rw [decomp,run_append]
  change run (A++B++C++D) n (run (entryBody K g k rest) m2 t)=s
  rw [parts,recover,undo,erase]


open Secp256k1 BalancedField
theorem exitEven_field_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (he:k.val%2=0)
    (s : State) (m : List Bool) (hH : regValue K.out s.basis=centerWord H)
    (hsrc : regValue K.src s.basis=0) (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    let v := run (exitEven K g k.val) m s
    v.phase=s.phase ∧ regValue K.out v.basis=(2*H-(if s.basis g then k else 0)).val ∧
      ∀q,q∉K.out → v.basis q=s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let Y : Fp := 2*H-(if s.basis g then k else 0)
  let b := run (xorConstant K.out (regValue K.out s.basis)) [] s
  have clear := xorConstant_correct K.out (FastConst.out_nodup hn) (regValue K.out s.basis)
    (regValue_lt K.out s.basis) s []
  have yBound : Y.val<2^K.out.length := by
    rw [hw.out]
    exact Y.isLt.trans (by norm_num [p])
  let a := run (xorConstant K.out Y.val) [] b
  have load := xorConstant_correct K.out (FastConst.out_nodup hn) Y.val yBound b []
  have av : regValue K.out a.basis=Y.val := by rw [load.2.2,clear.2.2]; simp
  have ap : a.phase=s.phase := load.1.trans clear.1
  have outside (q : Wire) (hq : q∉K.out) : a.basis q=s.basis q :=
    (load.2.1 q hq).trans (clear.2.1 q hq)
  have aSrc : regValue K.src a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq => outside q (src_fullOut K g hn q hq)),hsrc]
  have fixedOutside (q : Wire) (hq : q∈K.carry++[K.high,K.cin]) : q∉K.out := by
    intro bad
    exact FastConst.fixed_not_mutable hn q hq (by simp [FastConst.mutable,bad])
  have af : a.basis K.flag=false := (outside _ (FastConst.flag_not_out hn)).trans hf
  have ah : a.basis K.high=false := (outside _ (fixedOutside _ (by simp))).trans hh
  have ac : a.basis K.cin=false := (outside _ (fixedOutside _ (by simp))).trans hcin
  have aCarry : ∀q∈K.carry,a.basis q=false := by
    intro q hq
    exact (outside q (fixedOutside q (by simp [hq]))).trans (hcarry q hq)
  have ag : a.basis g=s.basis g := outside g (FastConst.g_not_out hn)
  have fwd := entry_field_correct K g k Y hn hw a [] av aSrc af ah ac aCarry
  have math : (Y+(if a.basis g then k else 0))/2=H := by
    rw [ag]
    dsimp only [Y]
    rw [sub_add_cancel]
    have two : (2:Fp)≠0 := by decide
    field_simp
  have preimage : run (EntryFuse.entry K g complement k.val) [] a=s := by
    apply State.extensionality
    · exact fwd.1.trans ap
    · funext q
      by_cases hq : q∈K.out
      · have val : regValue K.out (run (EntryFuse.entry K g complement k.val) [] a).basis=regValue K.out s.basis := by
          rw [fwd.2.1,math,hH]
        exact (regValue_eq_iff _ _ _).mp val q hq
      · exact (fwd.2.2 q hq).trans (outside q hq)
  have hy : Y.val<prime := by rw [prime_eq_secp]; exact Y.isLt
  have hk : k.val<prime := by rw [prime_eq_secp]; exact k.isLt
  have inv := exitEven_entry_inverse K g k.val Y.val hn hw he a [] m av hy hk aSrc af ah ac aCarry
  rw [preimage] at inv
  dsimp only
  rw [inv]
  exact ⟨ap,av,outside⟩


theorem exitEven_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (he:k.val%2=0) (s : State) (m n : List Bool)
    (hH : regValue K.out s.basis=centerWord H) (hsrc : regValue K.src s.basis=0)
    (hf : s.basis K.flag=false) (hh : s.basis K.high=false) (hcin : s.basis K.cin=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) :
    run (exitEven K g k.val) m s=run (ExitFusionResearch.exit K g complement k.val) n s := by
  have a:=exitEven_field_correct K g k H hn hw he s m hH hsrc hf hh hcin hcarry
  have b:=ExitFusionProof.exit_field_correct K g k H hn hw s n hH hsrc hf hh hcin hcarry
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases hq:q∈K.out
    · exact (regValue_eq_iff K.out _ _).mp (a.2.1.trans b.2.1.symm) q hq
    · exact (a.2.2 q hq).trans (b.2.2 q hq).symm



theorem eraseLtMoved_counts (a a' b b' c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    toffoliCount (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)+1=
      toffoliCount (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) ∧
    measurementCount (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)=
      measurementCount (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) ∧
    gateSlots (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)+6=
      gateSlots (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) := by
  simp [eraseLtMoved,eraseLtChain,borrowMajority,majority,toffoliCount_append,measurementCount_append,
    gateSlots_append,toffoliCount,measurementCount,gateSlots,instructionSlots]
  omega

theorem eraseMoved_layout_counts (K:MeasuredCanonicalModLayout) (g h:Wire) (hw:K.Widths 256) (v:Nat) :
    toffoliCount (erasePrefixMoved g h K.src K.out (K.carry.take 255) K.cin K.flag v)+1=
      toffoliCount (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) ∧
    measurementCount (erasePrefixMoved g h K.src K.out (K.carry.take 255) K.cin K.flag v)=
      measurementCount (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) ∧
    gateSlots (erasePrefixMoved g h K.src K.out (K.carry.take 255) K.cin K.flag v)+6=
      gateSlots (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  have H:=eraseLtMoved_counts a a' b b' c as bs cs K.cin K.flag h
  simp only [hs,ho,hc,erasePrefixMoved,erasePrefixOld,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem eraseInputMoved_counts (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (k:Nat) :
    toffoliCount (eraseInputMoved K g k)+1=toffoliCount (ExitFusionResearch.eraseInputWrap K g complement k) ∧
    measurementCount (eraseInputMoved K g k)=measurementCount (ExitFusionResearch.eraseInputWrap K g complement k) ∧
    gateSlots (eraseInputMoved K g k)+3=gateSlots (ExitFusionResearch.eraseInputWrap K g complement k) := by
  have H:=eraseMoved_layout_counts K g K.high hw (complement+k)
  have old:erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)=
      ExitFusionResearch.eraseInputWrap K g complement k:=by
    simp only [erasePrefixOld,loadNot,unloadNot,ExitFusionResearch.eraseInputWrap,List.append_assoc]
  rw [old] at H
  simp only [eraseInputMoved,toffoliCount_append,measurementCount_append,gateSlots_append]
  simp only [moveCached,toffoliCount,measurementCount,gateSlots,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,instructionSlots] at H ⊢
  omega

theorem undoMiddleKeep_counts (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat) :
    toffoliCount (undoMiddleKeep K g c k)=toffoliCount (ExitFusionResearch.undoMiddle K g c k) ∧
    measurementCount (undoMiddleKeep K g c k)=measurementCount (ExitFusionResearch.undoMiddle K g c k) ∧
    gateSlots (undoMiddleKeep K g c k)=gateSlots (ExitFusionResearch.undoMiddle K g c k) := by
  simp only [undoMiddleKeep,ExitFusionResearch.undoMiddle,toffoliCount_append,measurementCount_append,gateSlots_append]
  simp [toffoliCount,measurementCount,gateSlots,instructionSlots,
    ExitFusionResearch.lowSrc,ExitFusionResearch.lowOut,EntryFuse.lowSrc,EntryFuse.lowOut]

theorem exitEven_counts (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (k:Nat) :
    toffoliCount (exitEven K g k)+1=766 ∧ measurementCount (exitEven K g k)=766 ∧
    gateSlots (exitEven K g k)+3=gateSlots (ExitFusionResearch.exit K g complement k) := by
  have D:=eraseInputMoved_counts K g hw k
  have B:=undoMiddleKeep_counts K g complement k
  have old:=ExitFusionResearch.exit_counts K g complement k hw
  have split:ExitFusionResearch.exit K g complement k=ExitFusionResearch.recoverWrap K g complement k++
      ExitFusionResearch.undoMiddle K g complement k++(ExitFusionResearch.signStage K g k).reverse++
      ExitFusionResearch.eraseInputWrap K g complement k:=rfl
  have slots:=congrArg gateSlots split
  rw [split] at old
  simp only [exitEven,toffoliCount_append,measurementCount_append,gateSlots_append] at old slots ⊢
  omega

attribute [local irreducible] run wires GatePhysical toffoliCount measurementCount gateSlots

theorem compareChainCached_physical (a b c:Wire) (as bs cs:List Wire) (cin target h:Wire) (ch:c≠h)
    (old:GatePhysical (compareChain none (a::as) (b::bs) (c::cs) cin target)) :
    GatePhysical (compareChainCached (a::as) (b::bs) (c::cs) cin target h) := by
  simp only [compareChain,gatePhysical_append] at old
  simp only [compareChainCached,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ch,ch.symm],old.1.2⟩,old.2⟩

theorem compareLtCached_physical (a b c:Wire) (as bs cs:List Wire) (cin target h:Wire) (ch:c≠h)
    (old:GatePhysical (compareLt none (a::as) (b::bs) (c::cs) cin target)) :
    GatePhysical (compareLtCached (a::as) (b::bs) (c::cs) cin target h) := by
  simp only [compareLt,gatePhysical_append] at old
  simp only [compareLtCached,gatePhysical_append]
  exact ⟨⟨old.1.1,compareChainCached_physical a b c as bs cs cin target h ch old.1.2⟩,old.2⟩

theorem eraseLtMoved_physical (a a' b b' c:Wire) (as bs cs:List Wire) (cin target h:Wire) (ch:c≠h)
    (old:GatePhysical (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target)) :
    GatePhysical (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h) := by
  simp only [eraseLtChain,gatePhysical_append] at old
  simp only [eraseLtMoved,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ch,ch.symm],old.1.2⟩,old.2⟩

theorem comparePrefixCached_physical (g a b c cin flag h:Wire) (as bs cs:List Wire) (v:Nat) (ch:c≠h)
    (old:GatePhysical (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v)) :
    GatePhysical (comparePrefixCached g h (a::as) (b::bs) (c::cs) cin flag v) := by
  simp only [comparePrefixOld,gatePhysical_append] at old
  simp only [comparePrefixCached,gatePhysical_append]
  exact ⟨⟨old.1.1,compareLtCached_physical a b c as bs cs cin flag h ch old.1.2⟩,old.2⟩

theorem erasePrefixMoved_physical (g a a' b b' c cin flag h:Wire) (as bs cs:List Wire) (v:Nat) (ch:c≠h)
    (old:GatePhysical (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)) :
    GatePhysical (erasePrefixMoved g h (a::a'::as) (b::b'::bs) (c::cs) cin flag v) := by
  simp only [erasePrefixOld,gatePhysical_append] at old
  simp only [erasePrefixMoved,gatePhysical_append]
  exact ⟨⟨old.1.1,eraseLtMoved_physical a a' b b' c as bs cs cin flag h ch old.1.2⟩,old.2⟩

theorem carry_high_ne (K:MeasuredCanonicalModLayout) (g q:Wire) (hn:(g::K.wires).Nodup)
    (hq:q∈K.carry) : q≠K.high := by
  intro e
  have C:=List.nodup_iff_count.mp hn K.high
  have H:=List.count_pos_iff.mpr (e ▸ hq)
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil,
    beq_self_eq_true,if_true] at C
  omega

theorem compareCached_layout_physical (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (v:Nat)
    (old:GatePhysical (comparePrefixOld g K.src K.out K.carry K.cin K.flag v)) :
    GatePhysical (comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have ch:=carry_high_ne K g c hn (by rw [hc];simp)
  rw [hs,ho,hc] at old ⊢
  exact comparePrefixCached_physical g a b c K.cin K.flag K.high as bs cs v ch old

theorem eraseMoved_layout_physical (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (v:Nat)
    (old:GatePhysical (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v)) :
    GatePhysical (erasePrefixMoved g K.high K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  have ch:=carry_high_ne K g c hn (List.mem_of_mem_take (by rw [hc];simp))
  rw [hs,ho,hc] at old ⊢
  exact erasePrefixMoved_physical g a a' b b' c K.cin K.flag K.high as bs cs v ch old

theorem evenBody_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (rest:List Wire) (hout:K.out=lowBit K::rest)
    (old:GatePhysical (entryBody K g k rest)) : GatePhysical (evenBody K g k) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩:=controls_distinct K g hn hw
  have move:GatePhysical (moveCached K.high (alpha K)):=by
    simp [moveCached,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hhA,hhA.symm]
  have flags:GatePhysical [.CX K.flag (alpha K),.CCX K.flag (sign K) K.high]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hfA,hfS,hfH,hhS.symm]
  simp only [entryBody,entryMiddle,middle,gatePhysical_append] at old
  simp only [evenBody,gatePhysical_append,ExitFusionProof.signStage_eq K g k rest hout]
  exact ⟨⟨⟨⟨move,old.1.1⟩,flags⟩,old.1.2.2⟩,old.2⟩

theorem entryEven_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) : GatePhysical (entryEven K g k) := by
  have old:=EntryFuse.entry_physical K g complement k hn hw
  rw [ParityConvert.old_entry_split K g hw k] at old
  simp only [gatePhysical_append] at old
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩:=controls_distinct K g hn hw
  have go:g∉K.out:=controls_fullOut K g hn hw g (by simp [controls]) hgS
  have ho:K.high∉K.out:=controls_fullOut K g hn hw K.high (by simp [controls]) hhS
  have lb:lowBit K∈K.out:=by
    obtain ⟨a,as,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [lowBit,h]
  have gl:g≠lowBit K:=by intro e;exact go (e ▸ lb)
  have lh:lowBit K≠K.high:=by intro e;exact ho (e ▸ lb)
  have pre:GatePhysical [.CCX g (lowBit K) K.high]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,gl,hgH,lh]
  have hout:K.out=lowBit K::K.out.tail:=by
    obtain ⟨a,as,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [lowBit,h]
  simp only [entryEven,gatePhysical_append]
  exact ⟨⟨pre,compareCached_layout_physical K g hw hn (complement+k) old.1⟩,
    evenBody_physical K g k hw hn K.out.tail hout old.2⟩

theorem undoMiddleKeep_physical (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256)
    (old:GatePhysical (ExitFusionResearch.undoMiddle K g c k)) :
    GatePhysical (undoMiddleKeep K g c k) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩:=controls_distinct K g hn hw
  have tail:GatePhysical [.measureX K.high [] [.CZ K.flag (sign K)],
      .CX K.flag (alpha K),.measureX K.high [] []]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hfH,hfH.symm,hfS,hfS.symm,
      hhS,hhS.symm,hfA]
  simp only [undoMiddleKeep,ExitFusionResearch.undoMiddle,gatePhysical_append,
    ExitFusionResearch.lowSrc,ExitFusionResearch.lowOut,EntryFuse.lowSrc,EntryFuse.lowOut] at old ⊢
  exact ⟨old.1,tail⟩

theorem eraseInputMoved_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256)
    (old:GatePhysical (ExitFusionResearch.eraseInputWrap K g complement k)) :
    GatePhysical (eraseInputMoved K g k) := by
  have hhA:K.high≠alpha K:=(controls_distinct K g hn hw).2.2.2.2.2.2.2.2.2.2.1
  have move:GatePhysical (moveCached (alpha K) K.high):=by
    simp [moveCached,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hhA,hhA.symm]
  have eqOld:erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)=
      ExitFusionResearch.eraseInputWrap K g complement k:=by
    simp only [erasePrefixOld,loadNot,unloadNot,ExitFusionResearch.eraseInputWrap,List.append_assoc]
  rw [←eqOld] at old
  simp only [eraseInputMoved,gatePhysical_append]
  exact ⟨move,eraseMoved_layout_physical K g hw hn (complement+k) old⟩

theorem exitEven_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) : GatePhysical (exitEven K g k) := by
  have old:=ExitFusionResearch.exit_physical K g complement k hn hw
  simp only [ExitFusionResearch.exit,gatePhysical_append] at old
  simp only [exitEven,gatePhysical_append]
  exact ⟨⟨⟨old.1.1.1,undoMiddleKeep_physical K g complement k hn hw old.1.1.2⟩,old.1.2⟩,
    eraseInputMoved_physical K g k hn hw old.2⟩

theorem compareChainCached_wires (a b c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    wires (compareChainCached (a::as) (b::bs) (c::cs) cin target h)⊆
      wires (compareChain none (a::as) (b::bs) (c::cs) cin target)∪{h} := by
  have head:wires [.X c,.CX h c]⊆wires (majority a b cin c)∪{h}:=by
    simp [majority,wires,Instr.wires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  simp only [compareChainCached,compareChain,wires_append]
  intro q H
  have S:=head (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem compareLtCached_wires (a b c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    wires (compareLtCached (a::as) (b::bs) (c::cs) cin target h)⊆
      wires (compareLt none (a::as) (b::bs) (c::cs) cin target)∪{h} := by
  have core:=compareChainCached_wires a b c as bs cs cin target h
  simp only [compareLtCached,compareLt,wires_append]
  intro q H
  have S:=core (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem eraseLtMoved_wires (a a' b b' c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    wires (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)⊆
      wires (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target)∪{h} := by
  have head:wires [.CX h c,.CX c h]⊆wires (borrowMajority a b cin c)∪{h}:=by
    simp [borrowMajority,majority,wires,Instr.wires]
  simp only [eraseLtMoved,eraseLtChain,wires_append]
  intro q H
  have S:=head (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem comparePrefixCached_wires (g a b c cin flag h:Wire) (as bs cs:List Wire) (v:Nat) :
    wires (comparePrefixCached g h (a::as) (b::bs) (c::cs) cin flag v)⊆
      wires (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v)∪{h} := by
  have core:=compareLtCached_wires a b c as bs cs cin flag h
  simp only [comparePrefixCached,comparePrefixOld,wires_append]
  intro q H
  have S:=core (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem erasePrefixMoved_wires (g a a' b b' c cin flag h:Wire) (as bs cs:List Wire) (v:Nat) :
    wires (erasePrefixMoved g h (a::a'::as) (b::b'::bs) (c::cs) cin flag v)⊆
      wires (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)∪{h} := by
  have core:=eraseLtMoved_wires a a' b b' c as bs cs cin flag h
  simp only [erasePrefixMoved,erasePrefixOld,wires_append]
  intro q H
  have S:=core (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem compareCached_layout_wires (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (v:Nat) :
    wires (comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v)⊆
      wires (comparePrefixOld g K.src K.out K.carry K.cin K.flag v)∪{K.high} := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  rw [hs,ho,hc]
  exact comparePrefixCached_wires g a b c K.cin K.flag K.high as bs cs v

theorem eraseMoved_layout_wires (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (v:Nat) :
    wires (erasePrefixMoved g K.high K.src K.out (K.carry.take 255) K.cin K.flag v)⊆
      wires (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v)∪{K.high} := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  rw [hs,ho,hc]
  exact erasePrefixMoved_wires g a a' b b' c K.cin K.flag K.high as bs cs v

theorem evenBody_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (rest:List Wire) (hout:K.out=lowBit K::rest) :
    wires (evenBody K g k)⊆wires (entryBody K g k rest) := by
  have move:wires (moveCached K.high (alpha K))⊆wires (makeFlags K g):=by
    simp [moveCached,makeFlags,wires,Instr.wires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  have flags:wires [.CX K.flag (alpha K),.CCX K.flag (sign K) K.high]⊆wires (makeFlags K g):=by
    simp [makeFlags,wires,Instr.wires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  simp only [evenBody,entryBody,entryMiddle,middle,wires_append,ExitFusionProof.signStage_eq K g k rest hout]
  intro q H
  have M:=move (a:=q)
  have F:=flags (a:=q)
  simp only [Finset.mem_union] at H M F ⊢
  tauto

theorem body_control_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (rest:List Wire) :
    ({g,lowBit K,K.high}:Finset Wire)⊆wires (entryBody K g k rest) := by
  simp only [entryBody,entryMiddle,middle,EntryFuse.signStage,moveStage,makeFlags,wires_append]
  intro q H
  simp only [Finset.mem_insert,Finset.mem_singleton] at H
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,or_false]
  tauto

theorem entryEven_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (entryEven K g k)⊆wires (EntryFuse.entry K g complement k) := by
  have hwrd:K.out=lowBit K::K.out.tail:=by
    obtain ⟨a,as,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [lowBit,h]
  have B:=evenBody_wires K g k K.out.tail hwrd
  have C:=body_control_wires K g k K.out.tail
  have P:=compareCached_layout_wires K g hw (complement+k)
  have pre:wires [.CCX g (lowBit K) K.high]⊆wires (entryBody K g k K.out.tail):=by
    simpa only [wires,Instr.wires,Finset.union_empty] using C
  rw [ParityConvert.old_entry_split K g hw k]
  simp only [entryEven,wires_append]
  intro q H
  have bb:=B (a:=q)
  have pp:=P (a:=q)
  have pr:=pre (a:=q)
  have hi:q=K.high→q∈wires (entryBody K g k K.out.tail):=by
    intro e;apply C; simp [e]
  simp only [Finset.mem_union,Finset.mem_singleton] at H bb pp pr ⊢
  tauto

theorem undoMiddleKeep_wires (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat) :
    wires (undoMiddleKeep K g c k)⊆wires (ExitFusionResearch.undoMiddle K g c k) := by
  have tail:wires [.measureX K.high [] [.CZ K.flag (sign K)],
      .CX K.flag (alpha K),.measureX K.high [] []]⊆
      wires [.measureX K.high [] [.CZ K.flag (sign K)],.measureX (alpha K) [] [.CZ g (sign K)]]:=by
    simp [wires,Instr.wires,correctionWires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  simp only [undoMiddleKeep,ExitFusionResearch.undoMiddle,wires_append,
    ExitFusionResearch.lowSrc,ExitFusionResearch.lowOut,EntryFuse.lowSrc,EntryFuse.lowOut]
  exact Finset.union_subset_union (Finset.Subset.refl _) tail

theorem undoMiddle_control_wires (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat) :
    ({alpha K,K.high}:Finset Wire)⊆wires (ExitFusionResearch.undoMiddle K g c k) := by
  simp only [ExitFusionResearch.undoMiddle,wires_append]
  intro q H
  simp only [Finset.mem_insert,Finset.mem_singleton] at H
  simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,or_false]
  tauto

theorem eraseInputMoved_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (eraseInputMoved K g k)⊆wires (ExitFusionResearch.eraseInputWrap K g complement k)∪{alpha K,K.high} := by
  have core:=eraseMoved_layout_wires K g hw (complement+k)
  have old:erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)=
      ExitFusionResearch.eraseInputWrap K g complement k:=by
    simp only [erasePrefixOld,loadNot,unloadNot,ExitFusionResearch.eraseInputWrap,List.append_assoc]
  rw [old] at core
  have move:wires (moveCached (alpha K) K.high)⊆({alpha K,K.high}:Finset Wire):=by
    simp [moveCached,wires,Instr.wires]
  simp only [eraseInputMoved,wires_append]
  intro q H
  have M:=move (a:=q)
  have C:=core (a:=q)
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at H M C ⊢
  tauto

theorem exitEven_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (exitEven K g k)⊆wires (ExitFusionResearch.exit K g complement k) := by
  have B:=undoMiddleKeep_wires K g complement k
  have D:=eraseInputMoved_wires K g k hw
  have E:=undoMiddle_control_wires K g complement k
  simp only [exitEven,ExitFusionResearch.exit,wires_append]
  intro q H
  have b:=B (a:=q)
  have d:=D (a:=q)
  have e:=E (a:=q)
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at H b d e ⊢
  tauto

end ECDSAAdd.Entrant.ParityEven
end


-- Consolidated source module: ParityUniform
section
namespace ECDSAAdd.Entrant.ParityUniform
open Arithmetic Challenge Secp256k1 ControlledPointLayout BalancedField ParityCarry ParityConvert ParityEven EntryFuseArithmetic
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires GatePhysical toffoliCount measurementCount gateSlots

def entryAll (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) : Program :=
  if k%2=1 then ParityConvert.entryOpt K g k else entryEven K g k

def exitAll (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) : Program :=
  if k%2=1 then ParityConvert.exitOpt K g k else exitEven K g k

theorem entryAll_eq (K:MeasuredCanonicalModLayout) (g:Wire) (k Y:Nat) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (hy:Y<prime) (hk:k<prime)
    (s:State) (m:List Bool) (hY:regValue K.out s.basis=Y) (hs:regValue K.src s.basis=0)
    (hf:s.basis K.flag=false) (hh:s.basis K.high=false) (hc:s.basis K.cin=false)
    (carry:∀q∈K.carry,s.basis q=false) :
    run (entryAll K g k) m s=run (EntryFuse.entry K g complement k) m s := by
  unfold entryAll
  split_ifs with he
  · exact ParityConvert.entryOpt_eq K g k hw hn s m hs hc
  · exact entryEven_eq K g k Y hw hn (by omega) hy hk s m hY hs hf hh hc carry

theorem exitAll_eq (K:MeasuredCanonicalModLayout) (g:Wire) (k H:Fp)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) (s:State) (m n:List Bool)
    (hH:regValue K.out s.basis=centerWord H) (hs:regValue K.src s.basis=0)
    (hf:s.basis K.flag=false) (hh:s.basis K.high=false) (hc:s.basis K.cin=false)
    (carry:∀q∈K.carry,s.basis q=false) :
    run (exitAll K g k.val) m s=run (ExitFusionResearch.exit K g complement k.val) n s := by
  unfold exitAll
  split_ifs with he
  · exact ParityConvert.exitOpt_eq K g k H hn hw s m n hH hs hf hh hc carry
  · exact exitEven_eq K g k H hn hw (by omega) s m n hH hs hf hh hc carry

theorem entryAll_counts (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    toffoliCount (entryAll K g k)+1=766 ∧ measurementCount (entryAll K g k)=767 ∧
    gateSlots (entryAll K g k)≤gateSlots (EntryFuse.entry K g complement k) := by
  unfold entryAll
  split_ifs with he
  · have H:=ParityConvert.entryOpt_counts K g k hw
    simpa only [oddSavings,he,if_true] using H
  · have H:=entryEven_counts K g hw k
    exact ⟨H.1,H.2.1,H.2.2.le⟩

theorem exitAll_counts (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    toffoliCount (exitAll K g k)+1=766 ∧ measurementCount (exitAll K g k)=766 ∧
    gateSlots (exitAll K g k)≤gateSlots (ExitFusionResearch.exit K g complement k) := by
  unfold exitAll
  split_ifs with he
  · have H:=ParityConvert.exitOpt_counts K g k hw
    simpa only [oddSavings,he,if_true] using H
  · have H:=exitEven_counts K g hw k
    exact ⟨H.1,H.2.1,by omega⟩

theorem entryAll_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (entryAll K g k)⊆wires (EntryFuse.entry K g complement k) := by
  unfold entryAll
  split_ifs
  · exact ParityConvert.entryOpt_wires K g k hw
  · exact entryEven_wires K g k hw

theorem exitAll_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (exitAll K g k)⊆wires (ExitFusionResearch.exit K g complement k) := by
  unfold exitAll
  split_ifs
  · exact ParityConvert.exitOpt_wires K g k hw
  · exact exitEven_wires K g k hw

theorem entryAll_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) : GatePhysical (entryAll K g k) := by
  unfold entryAll
  split_ifs
  · exact ParityConvert.entryOpt_physical K g k hn hw
  · exact entryEven_physical K g k hn hw

theorem exitAll_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) : GatePhysical (exitAll K g k) := by
  unfold exitAll
  split_ifs
  · exact ParityConvert.exitOpt_physical K g k hn hw
  · exact exitEven_physical K g k hn hw

def entryYAll (L:ControlledPointLayout) (k:Fp) : Program := entryAll (yLayout L) L.core.generic k.val

def exitYAll (L:ControlledPointLayout) (k:Fp) : Program := exitAll (yLayout L) L.core.generic k.val

theorem entryYAll_eq (L:ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (Y k:Fp) (s:State) (m:List Bool) (hY:regValue L.point.y s.basis=Y.val)
    (hc:regValue L.dialogPool s.basis=0) :
    run (entryYAll L k) m s=run (EntryFuse.fusedY L k) m s := by
  let K:=yLayout L
  have aux:=y_aux_clean L hw s hc
  have sz:regValue K.src s.basis=0:=(regValue_zero _ _).mpr (fun q hq=>aux q (by simp [K,hq]))
  have hy:Y.val<prime:=by rw [EntryFuse.prime_eq_secp];exact Y.isLt
  have hk:k.val<prime:=by rw [EntryFuse.prime_eq_secp];exact k.isLt
  have H:=entryAll_eq K L.core.generic k.val Y.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) hy hk s m hY sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq=>aux q (by simp [K,hq]))
  simpa only [entryYAll,EntryFuse.fusedY,K,yLayout] using H

theorem exitYAll_eq (L:ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (Y k:Fp) (s:State) (m n:List Bool) (hY:regValue L.point.y s.basis=centerWord Y)
    (hc:regValue L.dialogPool s.basis=0) :
    run (exitYAll L k) m s=run (ExitFusionResearch.exitY L k) n s := by
  let K:=yLayout L
  have aux:=y_aux_clean L hw s hc
  have sz:regValue K.src s.basis=0:=(regValue_zero _ _).mpr (fun q hq=>aux q (by simp [K,hq]))
  have H:=exitAll_eq K L.core.generic k Y
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl))
    (L.recoveryConstant_widths hw L.point.y hw.inputY) s m n hY sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq=>aux q (by simp [K,hq]))
  simpa only [exitYAll,ExitFusionResearch.exitY,K,yLayout] using H

theorem entryYAll_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryYAll L k)+1=766 ∧ measurementCount (entryYAll L k)=767 ∧
    gateSlots (entryYAll L k)≤gateSlots (EntryFuse.fusedY L k) := by
  exact entryAll_counts (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAll_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (exitYAll L k)+1=766 ∧ measurementCount (exitYAll L k)=766 ∧
    gateSlots (exitYAll L k)≤gateSlots (ExitFusionResearch.exitY L k) := by
  exact exitAll_counts (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)


theorem entryYAll_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryYAll L k)⊆wires (EntryFuse.fusedY L k) :=
  entryAll_wires (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAll_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (exitYAll L k)⊆wires (ExitFusionResearch.exitY L k) :=
  exitAll_wires (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem entryYAll_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (entryYAll L k) :=
  entryAll_physical (yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYAll_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (exitYAll L k) :=
  exitAll_physical (yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) (L.recoveryConstant_widths hw L.point.y hw.inputY)


end ECDSAAdd.Entrant.ParityUniform
end


-- Consolidated source module: ParityStageUniform
section

namespace ECDSAAdd.Entrant.ParityStageUniform
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap OB5 Rolling1588Lifetime ParityCarry ParityConvert ParityUniform
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  InverseFour15.lastPhase15 InverseFour15.stackReverse15 InverseFour15.reverseTail15 Rolling1588TickGap.tailPhase
def restEntry (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true) ++
      (Rolling1588.entryFieldHosted ++ renameProgram phaseHost (InverseFour15.lastPhase15 false)))

def entryRef (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky ++ E1QubitPlacement.entryM L kx ++ restEntry L

theorem entry_split_ref (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry InverseFour15.entryKernel15 L = E1QubitPlacement.tickF L ++ restEntry L := by
  have tick := E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base)) = E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,InverseFour15.entryKernel15,InverseFour15.kernel15,
    Rolling1588TickGap.firstPhase,restEntry,renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem entryRef_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryRef L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX L hw hn X Y G origin kx
  have divide := division_step InverseFour15.entryKernel15 InverseFour15.entry_support530
    InverseFour15.entry_correct15 L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior := add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky ++ E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx ++ fusedY L ky ++ E1QubitPlacement.tickF L)
    (R:=restEntry L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryRef,division,entry_split_ref,List.append_assoc] using prior


def entryStageAll (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  entryYAll L ky++E1QubitPlacement.entryM L kx++restEntry L

theorem entryStageAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y kx ky : Fp) (s : State) (m : List Bool) (hY:regValue L.point.y s.basis=Y.val)
    (hc : regValue L.dialogPool s.basis=0) :
    run (entryStageAll L kx ky) m s=run (entryRef L kx ky) m s := by
  have cm:(measurementCount (entryYAll L ky))=measurementCount (fusedY L ky) :=
    (entryYAll_counts L hw ky).2.1.trans (fusedY_counts L hw ky).2.symm
  simpa only [entryStageAll,entryRef,List.append_assoc] using
    prefix_eq (entryYAll L ky) (fusedY L ky) (E1QubitPlacement.entryM L kx++restEntry L) s m cm
      (entryYAll_eq L hw hn Y ky s m hY hc)

theorem entryStageAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState) (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStageAll L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  intro s m hs
  rw [entryStageAll_eq L hw hn Y kx ky s m hs.y hs.clean]
  exact entryRef_step L hw hn X Y kx ky G origin hx s m hs

theorem multiplyExitAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ExitMergeKernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (P++exitYAll L k) m s=run (P++ExitFusionResearch.exitY L k) m s := by
  let n:=measurementCount P
  let a:=run P (m.take n) s
  have hp:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have half:=correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have ac:regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq=>half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av:regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  rw [run_append,run_append]
  exact exitYAll_eq L hw hn ((Y*X)/2) k a (m.drop n) (m.drop n) av ac

theorem multiplyExitAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ExitMergeKernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++exitYAll L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m hs
  rw [multiplyExitAll_eq L hw hn P cx correct X Y k G origin hX s m hs]
  exact ExitMergeKernel.fusedMultiplyX_step L hw hn P cx correct X Y k G origin hX s m hs

def secondStageAll (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  ReflectionE1TickGapLow48.squareEntry L k++ExitMergeKernel.restXX L cx.val++exitYAll L cy

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
open ReflectionE1TickGapLow48
theorem secondStageAll_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageAll L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=multiplyExitAll_step L hw hn
    (FrontierEntry1591Callers.exit (ExitMergeKernel.kernelX cx.val) L) cx
    (ExitMergeKernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageAll,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ExitMergeKernel.restXX L cx.val++exitYAll L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ExitMergeKernel.exit_splitX,List.append_assoc,Z] using prior

end

def genericAll (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStageAll L (-cx) (-cy)++secondStageAll L (ReflectionE1.correction cx) cy cx

def genericRef (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryRef L (-cx) (-cy)++ReflectionE1TickGapLow48.secondStageX L (ReflectionE1.correction cx) cy cx

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (genericAll L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageAll_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (genericAll L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageAll_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second



end


theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+2=toffoliCount (genericRef L cx cy) ∧
    measurementCount (genericAll L cx cy)=measurementCount (genericRef L cx cy) ∧
    gateSlots (genericAll L cx cy)≤gateSlots (genericRef L cx cy) := by
  have a:=entryYAll_counts L hw (-cy)
  have aa:=fusedY_counts L hw (-cy)
  have b:=exitYAll_counts L hw cy
  have bb:=ExitFusionResearch.exitY_counts L hw cy
  simp only [genericAll,genericRef,entryStageAll,entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem generic_toffoli (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+2=toffoliCount (genericRef L cx cy) := by
  have h:=generic_counts L hw cx cy
  omega

theorem generic_wires (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (genericAll L cx cy)⊆wires (genericRef L cx cy) := by
  have a:=entryYAll_wires L hw (-cy)
  have b:=exitYAll_wires L hw cy
  simp only [genericAll,genericRef,entryStageAll,entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union a (Finset.Subset.refl _)) (Finset.Subset.refl _))
    (Finset.union_subset_union (Finset.Subset.refl _) b)

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp)
    (h : GatePhysical (genericRef L cx cy)) : GatePhysical (genericAll L cx cy) := by
  simp only [genericRef,entryRef,ReflectionE1TickGapLow48.secondStageX,gatePhysical_append] at h
  simp only [genericAll,entryStageAll,secondStageAll,gatePhysical_append]
  exact ⟨⟨⟨entryYAll_physical L hw hn (-cy),h.1.1.2⟩,h.1.2⟩,
    ⟨h.2.1,exitYAll_physical L hw hn cy⟩⟩

end ECDSAAdd.Entrant.ParityStageUniform
end


-- Consolidated source module: ParityXEntry
section
namespace ECDSAAdd.Entrant.ParityXEntry
open Arithmetic Challenge RecordedQuantum NativeFirstDirect MappedCompressed
  E1Merge ParityCarry ParityConvert ParityEven EntryFuseArithmetic E1WholeKAdd52Research
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires GatePhysical toffoliCount measurementCount gateSlots
  E1Merge.comparePart E1Merge.parGates E1Merge.prodPart E1Merge.loadK E1Merge.loadT E1Merge.hAddT flagKAdd52

def postX (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  loadK w g k++[.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

def tailX (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  (parGates w g k++rotateRight (kR w))++prodPart w g++loadK w g k++flagKAdd52 w++postX w g k

theorem merged_split (w:Nat→Wire) (g:Wire) (k:Nat) :
    E1AffineEndpoints52Research.Forward.merged w g k=comparePart w g k++tailX w g k := by
  unfold E1AffineEndpoints52Research.Forward.merged
  change ((comparePart w g k++(parGates w g k++rotateRight (kR w)))++prodPart w g++loadK w g k)++
    flagKAdd52 w++postX w g k=comparePart w g k++tailX w g k
  simp only [tailX,List.append_assoc]

def compareLayout (w:Nat→Wire) : MeasuredCanonicalModLayout where
  src:=srcR w
  out:=xR w
  carry:=cR w
  high:=w 721
  cin:=w 513
  flag:=w 514

theorem compareLayout_widths (w:Nat→Wire) : (compareLayout w).Widths 256 := by
  constructor <;> simp [compareLayout,srcR,xR,cR,wireBlock]

theorem compareLayout_nodup : (base 2400::(compareLayout base).wires).Nodup := by
  have numeric:(2400::((List.range' 0 256)++(List.range' 770 256)++(List.range' 256 256)++[721,513,514])).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    simp only [List.count_cons,List.count_append,List.count_nil,List.count_range_1',beq_iff_eq]
    split_ifs <;> omega
  simpa only [compareLayout,MeasuredCanonicalModLayout.wires,srcR,xR,cR,wireBlock,
    List.map_cons,List.map_nil,List.map_append] using numeric.map base_injective

theorem comparePart_eq (w:Nat→Wire) (g:Wire) (k:Nat) :
    comparePart w g k=comparePrefixOld g (compareLayout w).src (compareLayout w).out
      (compareLayout w).carry (compareLayout w).cin (compareLayout w).flag (complement+k) := by
  have hc:E1Merge.cmpC=complement:=by norm_num [E1Merge.cmpC,ECDSAAdd.p,complement]
  simp only [comparePart,comparePrefixOld,loadNot,unloadNot,compareLayout,hc,List.append_assoc]

def compareOdd (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  comparePrefixNew g (compareLayout w).src (compareLayout w).out (compareLayout w).carry
    (compareLayout w).cin (compareLayout w).flag (complement+k)

def mergedOdd (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  if k%2=1 then compareOdd w g k++tailX w g k else E1AffineEndpoints52Research.Forward.merged w g k

theorem mergedOdd_eq (k:Nat) (s:State) (m:List Bool)
    (hs:regValue (srcR base) s.basis=0) (hc:s.basis (base 513)=false) :
    run (mergedOdd base (base 2400) k) m s=
      run (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) m s := by
  unfold mergedOdd
  split_ifs with he
  · have even:(complement+k)%2=0:=by norm_num [complement,Nat.add_mod,he]
    rw [merged_split,comparePart_eq]
    exact prefix_eq _ _ _ s m
      (ParityConvert.compare_layout_counts (compareLayout base) (base 2400) (compareLayout_widths base) (complement+k)).2.1
      (compare_layout_eq (compareLayout base) (base 2400) (compareLayout_widths base)
        compareLayout_nodup (complement+k) even s m hs hc)
  · rfl

theorem mergedOdd_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (mergedOdd w g k)+oddSavings k=toffoliCount (E1AffineEndpoints52Research.Forward.merged w g k) ∧
    measurementCount (mergedOdd w g k)=measurementCount (E1AffineEndpoints52Research.Forward.merged w g k) ∧
    gateSlots (mergedOdd w g k)≤gateSlots (E1AffineEndpoints52Research.Forward.merged w g k) := by
  by_cases he:k%2=1
  · have delta:=ParityConvert.compare_layout_counts (compareLayout w) g (compareLayout_widths w) (complement+k)
    simp only [mergedOdd,oddSavings,he,if_true]
    rw [merged_split,comparePart_eq]
    simp only [compareOdd,toffoliCount_append,measurementCount_append,gateSlots_append]
    omega
  · simp [mergedOdd,oddSavings,he]


theorem mergedOdd_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (mergedOdd w g k)⊆wires (E1AffineEndpoints52Research.Forward.merged w g k) := by
  unfold mergedOdd
  split_ifs
  · rw [merged_split,comparePart_eq]
    simp only [compareOdd,wires_append]
    exact Finset.union_subset_union
      (ParityConvert.compare_layout_wires (compareLayout w) g (compareLayout_widths w) (complement+k))
      (Finset.Subset.refl _)
  · exact Finset.Subset.refl _

theorem mergedOdd_physical (k:Nat)
    (old:GatePhysical (E1AffineEndpoints52Research.Forward.merged base (base 2400) k)) :
    GatePhysical (mergedOdd base (base 2400) k) := by
  unfold mergedOdd
  split_ifs
  · rw [merged_split,comparePart_eq] at old
    simp only [gatePhysical_append] at old ⊢
    exact ⟨ParityConvert.compare_layout_physical (compareLayout base) (base 2400)
      (compareLayout_widths base) (complement+k) old.1,old.2⟩
  · exact old

def parStage (k:Nat) : Program := parGates base (base 2400) k++rotateRight (kR base)

theorem rotate_outside (i:Nat) (hi : i < 770 ∨ 1028 ≤ i) : base i∉wires (rotateRight (kR base)) := by
  rw [(rotate_wires (kR base)).1]
  simp only [kR,wireBlock,List.length_map,List.length_range',show ¬(258:Nat)<2 by decide,
    if_false,List.mem_toFinset,List.mem_map]
  intro H
  obtain ⟨j,hj,e⟩:=H
  have E:=base_injective e
  simp only [List.mem_range'_1] at hj
  omega

theorem parStage_alpha_free (k:Nat) : base 721∉wires (parStage k) := by
  have R:=rotate_outside 721 (Or.inl (by decide))
  simp only [parStage,wires_append,Finset.mem_union,not_or]
  constructor
  · unfold parGates
    split_ifs <;> simp [wires_append,wires,Instr.wires,base]
  · exact R

theorem parStage_values (k:Nat) (he:k%2=0) (s:State) (m:List Bool)
    (hp:s.basis (base 1028)=false) :
    let t:=run (parStage k) m s
    t.basis (base 2400)=s.basis (base 2400) ∧ t.basis (base 514)=s.basis (base 514) ∧
    t.basis (base 1028)=(s.basis (base 770) ^^ s.basis (base 514)) := by
  have ne:¬k%2=1:=by omega
  let u:=run (parGates base (base 2400) k) m s
  have ug:u.basis (base 2400)=s.basis (base 2400):=by
    simp [u,parGates,ne,run,writeBit,Function.update,base]
  have uf:u.basis (base 514)=s.basis (base 514):=by
    simp [u,parGates,ne,run,writeBit,Function.update,base]
  have up:u.basis (base 1028)=(s.basis (base 770) ^^ s.basis (base 514)):=by
    have hp':s.basis 1044=false:=hp
    simp [u,parGates,ne,run,writeBit,Function.update,base,hp']
  dsimp only
  simp only [parStage,run_append,run_take]
  have z:measurementCount (parGates base (base 2400) k)=0:=by
    simp [parGates,ne,measurementCount_append,measurementCount]
  rw [z,List.drop_zero]
  exact ⟨(run_preserves_outside _ m u _ (rotate_outside 2400 (Or.inr (by decide)))).trans ug,
    (run_preserves_outside _ m u _ (rotate_outside 514 (Or.inl (by decide)))).trans uf,
    (run_preserves_outside _ m u _ (rotate_outside 1028 (Or.inr (by decide)))).trans up⟩

def evenTail (k:Nat) : Program :=
  parStage k++[.CX (base 514) (base 721),.CCX (base 514) (base 1028) (base 722)]++
    loadK base (base 2400) k++flagKAdd52 base++postX base (base 2400) k

theorem evenTail_eq (k:Nat) (he:k%2=0) (s:State) (m:List Bool)
    (ha:s.basis (base 721)=false) (hp:s.basis (base 1028)=false)
    (wrap:s.basis (base 514)=true→s.basis (base 2400)=true) :
    run (evenTail k) m (put s (base 721) (s.basis (base 2400) && s.basis (base 770)))=
      run (tailX base (base 2400) k) m s := by
  let S:=parStage k
  let A:=s.basis (base 2400) && s.basis (base 770)
  have vals:=parStage_values k he s m hp
  have product:((run S m s).basis (base 2400) && (run S m s).basis (base 1028))=
      (A ^^ (run S m s).basis (base 514)):=by
    rw [vals.1,vals.2.1,vals.2.2]
    dsimp only [A]
    cases hg:s.basis (base 2400) <;> cases hx:s.basis (base 770) <;>
      cases hf:s.basis (base 514) <;> simp_all
  have ac:(run S m s).basis (base 721)=false:=
    (run_preserves_outside S m s _ (parStage_alpha_free k)).trans ha
  have e:run (S++[.CX (base 514) (base 721)]) m (put s (base 721) A)=
      run (S++[.CCX (base 2400) (base 1028) (base 721)]) m s:=by
    simp only [run_append,run_take]
    rw [run_put S m s (base 721) A (parStage_alpha_free k)]
    exact cached_flag_eq (base 2400) (base 1028) (base 514) (base 721) (by decide) (run S m s) _ A ac product
  have E:=append_eq_states _ _
    ([Instr.CCX (base 514) (base 1028) (base 722)]++loadK base (base 2400) k++flagKAdd52 base++postX base (base 2400) k)
    (put s (base 721) A) s m (by simp [measurementCount_append,measurementCount]) e
  simpa only [evenTail,tailX,prodPart,parStage,S,A,List.append_assoc,List.cons_append,List.nil_append] using E

def mergedEven (k:Nat) : Program :=
  [.CCX (base 2400) (base 770) (base 721)]++
    comparePrefixCached (base 2400) (base 721) (srcR base) (xR base) (cR base)
      (base 513) (base 514) (complement+k)++evenTail k

theorem mergedEven_eq (k X:Nat) (hk:k<ECDSAAdd.p) (hX:X<ECDSAAdd.p)
    (s:State) (m:List Bool) (he:k%2=0) (hx:regValue (xR base) s.basis=X)
    (hs:regValue (srcR base) s.basis=0) (hf:s.basis (base 514)=false)
    (ha:s.basis (base 721)=false) (hp:s.basis (base 1028)=false) (hc:s.basis (base 513)=false)
    (hcarry:∀q∈cR base,s.basis q=false) :
    run (mergedEven k) m s=run (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) m s := by
  let K:=compareLayout base
  let g:=base 2400
  let c:=complement
  let P:=[Instr.CCX g (base 770) (base 721)]++
    comparePrefixCached g (base 721) (srcR base) (xR base) (cR base) (base 513) (base 514) (c+k)
  let O:=comparePrefixOld g K.src K.out K.carry K.cin K.flag (c+k)
  let n:=measurementCount O
  let t:=run O (m.take n) s
  have hw:=compareLayout_widths base
  have hn:=compareLayout_nodup
  have lb:EntryFuse.lowBit K=base 770:=rfl
  have count:measurementCount P=measurementCount O:=(cached_layout_counts K g hw (c+k)).2.1
  have odd:(c+k)%2=1:=by
    have C:c%2=1:=by norm_num [c,complement]
    omega
  have cachedRun:run P (m.take n) s=put t (base 721) (s.basis g && s.basis (base 770)):=by
    simpa only [K,compareLayout,lb] using cachedPrefix_after_compute K g hw hn (c+k) odd s (m.take n) hs hc ha
  have primeBound:X<prime:=by rw [EntryFuse.prime_eq_secp];exact hX
  have kBound:k<prime:=by rw [EntryFuse.prime_eq_secp];exact hk
  have pc:prime+c=2^256:=by norm_num [prime,c,modulus,complement]
  have initial:FastConst.Frame K s.basis 0 X false s.basis:=⟨hs,hx,hf,by intro q hq;rfl⟩
  have pre:=EntryFuse.comparePrefix_correct hn 256 hw s.basis hcarry hc c prime k X pc kBound primeBound
    s (m.take n) initial
  have oe:O=EntryFuse.comparePrefix K g c k:=by
    simp only [O,comparePrefixOld,loadNot,unloadNot,EntryFuse.comparePrefix,List.append_assoc]
  rw [←oe] at pre
  change t.phase=s.phase ∧ FastConst.Frame K s.basis 0 X
    (if s.basis g then decide (prime≤X+k) else false) t.basis at pre
  have tg:t.basis g=s.basis g:=pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have ta:t.basis (base 721)=false:=(pre.2.2.2.2 K.high
    (FastConst.fixed_not_mutable hn K.high (by simp [K]))).trans ha
  have po:base 1028∉FastConst.mutable K:=by decide +kernel
  have tp:t.basis (base 1028)=false:=(pre.2.2.2.2 _ po).trans hp
  have tv:t.basis (base 770)=s.basis (base 770):=
    (regValue_eq_iff K.out t.basis s.basis).mp (pre.2.2.1.trans hx.symm) _ (by decide +kernel)
  have wrap:t.basis (base 514)=true→t.basis g=true:=by
    intro F
    change t.basis K.flag=true at F
    rw [tg]
    have f:=pre.2.2.2.1
    cases G:s.basis g <;> simp_all
  rw [←tg,←tv] at cachedRun
  rw [merged_split,comparePart_eq]
  change run (P++evenTail k) m s=run (O++tailX base g k) m s
  simp only [run_append,count]
  change run (evenTail k) (m.drop n) (run P (m.take n) s)=run (tailX base g k) (m.drop n) t
  rw [cachedRun]
  exact evenTail_eq k he t (m.drop n) ta tp wrap

theorem evenTail_counts (k:Nat) :
    toffoliCount (evenTail k)+1=toffoliCount (tailX base (base 2400) k) ∧
    measurementCount (evenTail k)=measurementCount (tailX base (base 2400) k) ∧
    gateSlots (evenTail k)=gateSlots (tailX base (base 2400) k) := by
  simp only [evenTail,tailX,parStage,prodPart,toffoliCount_append,measurementCount_append,gateSlots_append]
  simp only [toffoliCount,measurementCount,gateSlots,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,instructionSlots]
  constructor
  · omega
  · exact ⟨trivial,trivial⟩

theorem mergedEven_counts (k:Nat) :
    toffoliCount (mergedEven k)+1=toffoliCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) ∧
    measurementCount (mergedEven k)=measurementCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) ∧
    gateSlots (mergedEven k)+3=gateSlots (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) := by
  let K:=compareLayout base
  let P:=[Instr.CCX (base 2400) (base 770) (base 721)]++
    comparePrefixCached (base 2400) (base 721) (srcR base) (xR base) (cR base)
      (base 513) (base 514) (complement+k)
  have C:toffoliCount P=toffoliCount (comparePrefixOld (base 2400) K.src K.out K.carry K.cin K.flag (complement+k)) ∧
      measurementCount P=measurementCount (comparePrefixOld (base 2400) K.src K.out K.carry K.cin K.flag (complement+k)) ∧
      gateSlots P+3=gateSlots (comparePrefixOld (base 2400) K.src K.out K.carry K.cin K.flag (complement+k)):=
    cached_layout_counts K (base 2400) (compareLayout_widths base) (complement+k)
  have B:=evenTail_counts k
  have E:mergedEven k=P++evenTail k:=rfl
  rw [E,merged_split,comparePart_eq]
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append]
  dsimp only [K] at C ⊢
  omega

theorem evenTail_wires (k:Nat) : wires (evenTail k)⊆wires (tailX base (base 2400) k) := by
  have flags:wires [.CX (base 514) (base 721),.CCX (base 514) (base 1028) (base 722)]⊆
      wires (prodPart base (base 2400)):=by
    simp [prodPart,wires,Instr.wires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  simp only [evenTail,tailX,parStage,wires_append]
  intro q H
  have F:=flags (a:=q)
  simp only [Finset.mem_union] at H F ⊢
  tauto

theorem tail_control_wires (k:Nat) : ({base 2400,base 770,base 721}:Finset Wire)⊆
    wires (tailX base (base 2400) k) := by
  simp only [tailX,parGates,prodPart,wires_append]
  intro q H
  simp only [Finset.mem_insert,Finset.mem_singleton] at H
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,or_false]
  tauto

theorem mergedEven_wires (k:Nat) : wires (mergedEven k)⊆
    wires (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) := by
  let K:=compareLayout base
  have C:wires (comparePrefixCached (base 2400) (base 721) (srcR base) (xR base) (cR base)
      (base 513) (base 514) (complement+k))⊆
      wires (comparePrefixOld (base 2400) K.src K.out K.carry K.cin K.flag (complement+k))∪{base 721}:=
    compareCached_layout_wires K (base 2400) (compareLayout_widths base) (complement+k)
  have B:=evenTail_wires k
  have E:=tail_control_wires k
  have pre:wires [.CCX (base 2400) (base 770) (base 721)]⊆wires (tailX base (base 2400) k):=by
    simpa only [wires,Instr.wires,Finset.union_empty] using E
  rw [merged_split,comparePart_eq]
  simp only [mergedEven,wires_append]
  intro q H
  have c:=C (a:=q)
  have b:=B (a:=q)
  have e:=pre (a:=q)
  have a:q=base 721→q∈wires (tailX base (base 2400) k):=by intro e;apply E;simp [e]
  simp only [Finset.mem_union,Finset.mem_singleton] at H c b e ⊢
  tauto

theorem evenTail_physical (k:Nat) (old:GatePhysical (tailX base (base 2400) k)) :
    GatePhysical (evenTail k) := by
  have flags:GatePhysical [.CX (base 514) (base 721),.CCX (base 514) (base 1028) (base 722)]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,base]
  simp only [tailX,gatePhysical_append] at old
  simp only [evenTail,parStage,gatePhysical_append]
  exact ⟨⟨⟨⟨old.1.1.1.1,flags⟩,old.1.1.2⟩,old.1.2⟩,old.2⟩

theorem mergedEven_physical (k:Nat)
    (old:GatePhysical (E1AffineEndpoints52Research.Forward.merged base (base 2400) k)) :
    GatePhysical (mergedEven k) := by
  rw [merged_split,comparePart_eq] at old
  simp only [gatePhysical_append] at old
  have pre:GatePhysical [.CCX (base 2400) (base 770) (base 721)]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,base]
  simp only [mergedEven,gatePhysical_append]
  exact ⟨⟨pre,compareCached_layout_physical (compareLayout base) (base 2400) (compareLayout_widths base)
    compareLayout_nodup (complement+k) old.1⟩,evenTail_physical k old.2⟩

def mergedAll (k:Nat) : Program :=
  if k%2=1 then mergedOdd base (base 2400) k else mergedEven k

theorem mergedAll_eq (k X:Nat) (hk:k<ECDSAAdd.p) (hX:X<ECDSAAdd.p)
    (s:State) (m:List Bool) (hx:regValue (xR base) s.basis=X)
    (hs:regValue (srcR base) s.basis=0) (hf:s.basis (base 514)=false)
    (ha:s.basis (base 721)=false) (hp:s.basis (base 1028)=false) (hc:s.basis (base 513)=false)
    (hcarry:∀q∈cR base,s.basis q=false) :
    run (mergedAll k) m s=run (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) m s := by
  unfold mergedAll
  split_ifs with he
  · exact mergedOdd_eq k s m hs hc
  · exact mergedEven_eq k X hk hX s m (by omega) hx hs hf ha hp hc hcarry

theorem mergedAll_counts (k:Nat) :
    toffoliCount (mergedAll k)+1=toffoliCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) ∧
    measurementCount (mergedAll k)=measurementCount (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) ∧
    gateSlots (mergedAll k)≤gateSlots (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) := by
  unfold mergedAll
  split_ifs with he
  · have H:=mergedOdd_counts base (base 2400) k
    simpa only [oddSavings,he,if_true] using H
  · have H:=mergedEven_counts k
    exact ⟨H.1,H.2.1,by omega⟩

theorem mergedAll_wires (k:Nat) : wires (mergedAll k)⊆
    wires (E1AffineEndpoints52Research.Forward.merged base (base 2400) k) := by
  unfold mergedAll
  split_ifs
  · exact mergedOdd_wires base (base 2400) k
  · exact mergedEven_wires k

theorem mergedAll_physical (k:Nat) : GatePhysical (mergedAll k) := by
  have old:=E1AffineEndpoints52Research.Forward.merged_physical base (base 2400)
    base_pool_nodup E1QubitPlacement.g2400 k
  unfold mergedAll
  split_ifs
  · exact mergedOdd_physical k old
  · exact mergedEven_physical k old

theorem rename_run_equal (f:Wire→Wire) (S:Finset Wire)
    (inj:∀a∈S,∀b∈S,f a=f b→a=b) (P Q:Program) (hP:wires P⊆S) (hQ:wires Q⊆S)
    (s:State) (m:List Bool) (eq:run P m (pullState f s)=run Q m (pullState f s)) :
    run (renameProgram f P) m s=run (renameProgram f Q) m s := by
  have A:=run_rename_pool f S inj P hP m (pullState f s) s (by rfl) (by intro q hq;rfl)
  have B:=run_rename_pool f S inj Q hQ m (pullState f s) s (by rfl) (by intro q hq;rfl)
  rw [eq] at A
  apply State.extensionality
  · exact A.1.trans B.1.symm
  funext q
  by_cases im:q∈S.image f
  · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp im
    exact (A.2 a ha).trans (B.2 a ha).symm
  · rw [run_rename_pool_outside f S P hP m s q im,run_rename_pool_outside f S Q hQ m s q im]

def entryXAll (L:ControlledPointLayout) (k:Fp) : Program :=
  renameProgram (E1QubitPlacement.pmapR L) (mergedAll k.val)

theorem entryXAll_eq (L:ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (X k:Fp) (s:State) (m:List Bool) (hx:regValue L.point.x s.basis=X.val)
    (hc:regValue L.dialogPool s.basis=0) :
    run (entryXAll L k) m s=run (E1QubitPlacement.entryM L k) m s := by
  have inj:=E1QubitPlacement.pmap_inj L hw hn
  have pool:=E1QubitPlacement.pmap_pool L hw hn
  have hzero:=(regValue_zero _ _).mp hc
  let F:=E1QubitPlacement.pmapR L
  let t:=pullState F s
  have clean (q:Wire) (hq:q∈E1QubitPlacement.S) (notx:q∉wireBlock base 770 256) (notg:q≠base 2400) :
      t.basis q=false:=hzero _ (pool q hq notx notg)
  have inS (i:Nat) (hi : i < 515 ∨ i = 721 ∨ i = 1028) : base i∈E1QubitPlacement.S:=
    List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i (by omega))
  have notx (i:Nat) (hi : i < 770 ∨ 1026 ≤ i) : base i∉wireBlock base 770 256:=by
    intro H
    obtain ⟨j,hj,e⟩:=List.mem_map.mp H
    have E:=base_injective e
    simp only [List.mem_range'_1] at hj
    omega
  have cl (i:Nat) (hi : i < 515 ∨ i = 721 ∨ i = 1028) : t.basis (base i)=false:=
    clean _ (inS i hi) (notx i (by omega)) (fun E=>by have e:=base_injective E;omega)
  have src:regValue (srcR base) t.basis=0:=by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (Or.inl (by omega))
  have carry:∀q∈cR base,t.basis q=false:=by
    intro q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (Or.inl (by omega))
  have xval:regValue (xR base) t.basis=X.val:=by
    change regValue (wireBlock base 770 256) (fun q=>s.basis (F q))=X.val
    rw [E1QubitPlacement.regValue_pull,E1QubitPlacement.pmap_x L hw hn,hx]
  have old:=E1QubitPlacement.merged_S k.val
  have new:=(mergedAll_wires k.val).trans old
  unfold entryXAll E1QubitPlacement.entryM
  apply rename_run_equal F E1QubitPlacement.S inj _ _ new old s m
  exact mergedAll_eq k.val X.val k.isLt X.isLt t m xval src (cl 514 (by omega))
    (cl 721 (by simp)) (cl 1028 (by simp)) (cl 513 (by omega)) carry

theorem entryXAll_counts (L:ControlledPointLayout) (k:Fp) :
    toffoliCount (entryXAll L k)+1=toffoliCount (E1QubitPlacement.entryM L k) ∧
    measurementCount (entryXAll L k)=measurementCount (E1QubitPlacement.entryM L k) ∧
    gateSlots (entryXAll L k)≤gateSlots (E1QubitPlacement.entryM L k) := by
  simpa only [entryXAll,E1QubitPlacement.entryM,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots] using mergedAll_counts k.val

theorem entryXAll_wires (L:ControlledPointLayout) (k:Fp) :
    wires (entryXAll L k)⊆wires (E1QubitPlacement.entryM L k) := by
  simp only [entryXAll,E1QubitPlacement.entryM,renameProgram_support]
  exact Finset.image_subset_image (mergedAll_wires k.val)

theorem entryXAll_physical (L:ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (k:Fp) :
    GatePhysical (entryXAll L k) := by
  have support:=(mergedAll_wires k.val).trans (E1QubitPlacement.merged_S k.val)
  exact gatePhysical_rename_support (E1QubitPlacement.pmapR L) (mergedAll k.val)
    (fun a ha b hb e=>E1QubitPlacement.pmap_inj L hw hn a (support ha) b (support hb) e)
    (mergedAll_physical k.val)

end ECDSAAdd.Entrant.ParityXEntry
end


-- Consolidated source module: ParityStageX
section

namespace ECDSAAdd.Entrant.ParityStageX
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap OB5 Rolling1588Lifetime ParityCarry ParityConvert ParityUniform ParityXEntry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  InverseFour15.lastPhase15 InverseFour15.stackReverse15 InverseFour15.reverseTail15 Rolling1588TickGap.tailPhase
def restEntry (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true) ++
      (Rolling1588.entryFieldHosted ++ renameProgram phaseHost (InverseFour15.lastPhase15 false)))

def entryRef (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky ++ E1QubitPlacement.entryM L kx ++ restEntry L

theorem entry_split_ref (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry InverseFour15.entryKernel15 L = E1QubitPlacement.tickF L ++ restEntry L := by
  have tick := E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base)) = E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,InverseFour15.entryKernel15,InverseFour15.kernel15,
    Rolling1588TickGap.firstPhase,restEntry,renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem entryRef_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryRef L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX L hw hn X Y G origin kx
  have divide := division_step InverseFour15.entryKernel15 InverseFour15.entry_support530
    InverseFour15.entry_correct15 L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior := add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky ++ E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx ++ fusedY L ky ++ E1QubitPlacement.tickF L)
    (R:=restEntry L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryRef,division,entry_split_ref,List.append_assoc] using prior


def entryStageAll (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  entryYAll L ky++entryXAll L kx++restEntry L

theorem entryStageAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (s : State) (m : List Bool) (hX:regValue L.point.x s.basis=X.val)
    (hY:regValue L.point.y s.basis=Y.val) (hc : regValue L.dialogPool s.basis=0) :
    run (entryStageAll L kx ky) m s=run (entryRef L kx ky) m s := by
  have cm:measurementCount (entryYAll L ky)=measurementCount (fusedY L ky) :=
    (entryYAll_counts L hw ky).2.1.trans (fusedY_counts L hw ky).2.symm
  have first:=prefix_eq (entryYAll L ky) (fusedY L ky) (entryXAll L kx++restEntry L) s m cm
      (entryYAll_eq L hw hn Y ky s m hY hc)
  have fy:=fusedY_correct L hw hn Y ky s (m.take (measurementCount (fusedY L ky))) hY hc
  let t:=run (fusedY L ky) (m.take (measurementCount (fusedY L ky))) s
  have tx:regValue L.point.x t.basis=X.val:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)),hX]
  have tc:regValue L.dialogPool t.basis=0:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)),hc]
  have second:=prefix_eq (entryXAll L kx) (E1QubitPlacement.entryM L kx) (restEntry L)
    t (m.drop (measurementCount (fusedY L ky))) (entryXAll_counts L kx).2.1
    (entryXAll_eq L hw hn X kx t _ tx tc)
  change run ((entryYAll L ky++entryXAll L kx)++restEntry L) m s=_
  rw [List.append_assoc,first]
  simpa only [entryRef,List.append_assoc,run_append,t] using second

theorem entryStageAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState) (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStageAll L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  intro s m hs
  rw [entryStageAll_eq L hw hn X Y kx ky s m hs.x hs.y hs.clean]
  exact entryRef_step L hw hn X Y kx ky G origin hx s m hs

theorem multiplyExitAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ExitMergeKernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (P++exitYAll L k) m s=run (P++ExitFusionResearch.exitY L k) m s := by
  let n:=measurementCount P
  let a:=run P (m.take n) s
  have hp:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have half:=correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have ac:regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq=>half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av:regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  rw [run_append,run_append]
  exact exitYAll_eq L hw hn ((Y*X)/2) k a (m.drop n) (m.drop n) av ac

theorem multiplyExitAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ExitMergeKernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++exitYAll L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m hs
  rw [multiplyExitAll_eq L hw hn P cx correct X Y k G origin hX s m hs]
  exact ExitMergeKernel.fusedMultiplyX_step L hw hn P cx correct X Y k G origin hX s m hs

def secondStageAll (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  ReflectionE1TickGapLow48.squareEntry L k++ExitMergeKernel.restXX L cx.val++exitYAll L cy

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
open ReflectionE1TickGapLow48
theorem secondStageAll_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageAll L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=multiplyExitAll_step L hw hn
    (FrontierEntry1591Callers.exit (ExitMergeKernel.kernelX cx.val) L) cx
    (ExitMergeKernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageAll,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ExitMergeKernel.restXX L cx.val++exitYAll L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ExitMergeKernel.exit_splitX,List.append_assoc,Z] using prior

end

def genericAll (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStageAll L (-cx) (-cy)++secondStageAll L (ReflectionE1.correction cx) cy cx

def genericRef (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryRef L (-cx) (-cy)++ReflectionE1TickGapLow48.secondStageX L (ReflectionE1.correction cx) cy cx

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (genericAll L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageAll_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (genericAll L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageAll_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second



end


theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+3=toffoliCount (genericRef L cx cy) ∧
    measurementCount (genericAll L cx cy)=measurementCount (genericRef L cx cy) ∧
    gateSlots (genericAll L cx cy)≤gateSlots (genericRef L cx cy) := by
  have x:=entryXAll_counts L (-cx)
  have a:=entryYAll_counts L hw (-cy)
  have aa:=fusedY_counts L hw (-cy)
  have b:=exitYAll_counts L hw cy
  have bb:=ExitFusionResearch.exitY_counts L hw cy
  simp only [genericAll,genericRef,entryStageAll,entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem generic_toffoli (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+3=toffoliCount (genericRef L cx cy) := by
  have h:=generic_counts L hw cx cy
  omega

theorem generic_wires (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (genericAll L cx cy)⊆wires (genericRef L cx cy) := by
  have a:=entryYAll_wires L hw (-cy)
  have b:=exitYAll_wires L hw cy
  simp only [genericAll,genericRef,entryStageAll,entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union a (entryXAll_wires L (-cx))) (Finset.Subset.refl _))
    (Finset.union_subset_union (Finset.Subset.refl _) b)

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp)
    (h : GatePhysical (genericRef L cx cy)) : GatePhysical (genericAll L cx cy) := by
  simp only [genericRef,entryRef,ReflectionE1TickGapLow48.secondStageX,gatePhysical_append] at h
  simp only [genericAll,entryStageAll,secondStageAll,gatePhysical_append]
  exact ⟨⟨⟨entryYAll_physical L hw hn (-cy),entryXAll_physical L hw hn (-cx)⟩,h.1.2⟩,
    ⟨h.2.1,exitYAll_physical L hw hn cy⟩⟩

end ECDSAAdd.Entrant.ParityStageX
end


-- Consolidated source module: ParityXExit
section
namespace ECDSAAdd.Entrant.ParityXExit
open Arithmetic Challenge RecordedQuantum NativeFirstDirect MappedCompressed E1Merge ExitMerge ParityCarry ParityConvert ParityEven
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires GatePhysical toffoliCount measurementCount gateSlots
  ExitMerge.fPart ExitMerge.eraseH ExitMerge.addPart ExitMerge.parBack ExitMerge.eraseF
  FastConst.maskedNot ExitMerge.loadKX Verifier.Leaf4.zero4KAdd rotateLeft

def eraseLayout (w:Nat→Wire) : MeasuredCanonicalModLayout where
  src:=tR w
  out:=xR w
  carry:=hC2 w
  high:=w 721
  cin:=w 1797
  flag:=w 514

theorem eraseLayout_widths (w:Nat→Wire) : (eraseLayout w).Widths 256 := by
  constructor <;> simp [eraseLayout,tR,xR,hC2,wireBlock]

theorem eraseLayout_nodup : (base 2400::(eraseLayout base).wires).Nodup := by
  have numeric:(2400::((List.range' 1029 256)++(List.range' 770 256)++(List.range' 1540 256)++[721,1797,514])).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    simp only [List.count_cons,List.count_append,List.count_nil,List.count_range_1',beq_iff_eq]
    split_ifs <;> omega
  simpa only [eraseLayout,MeasuredCanonicalModLayout.wires,tR,xR,hC2,wireBlock,
    List.map_cons,List.map_nil,List.map_append] using numeric.map base_injective

theorem eraseF_eq (w:Nat→Wire) (g:Wire) (k:Nat) :
    eraseF w g k=erasePrefixOld g (eraseLayout w).src (eraseLayout w).out
      ((eraseLayout w).carry.take 255) (eraseLayout w).cin (eraseLayout w).flag (2^256-1-k) := by
  simp only [eraseF,erasePrefixOld,loadNot,unloadNot,eraseLayout,hC2,hC3,wireBlock,
    ←List.map_take,List.take_range'_of_length_ge (by decide : 256 ≥ 255),List.append_assoc]

def eraseOdd (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  erasePrefixNew g (eraseLayout w).src (eraseLayout w).out ((eraseLayout w).carry.take 255)
    (eraseLayout w).cin (eraseLayout w).flag (2^256-1-k)

theorem eraseOdd_eq (k:Nat) (hk:k<2^256) (he:k%2=1) (s:State) (m:List Bool)
    (ht:regValue (tR base) s.basis=0) (hc:s.basis (base 1797)=false) :
    run (eraseOdd base (base 2400) k) m s=run (eraseF base (base 2400) k) m s := by
  have even:(2^256-1-k)%2=0:=by omega
  rw [eraseF_eq]
  exact erase_layout_eq (eraseLayout base) (base 2400) (eraseLayout_widths base)
    eraseLayout_nodup (2^256-1-k) even s m ht hc

theorem eraseOdd_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (eraseOdd w g k)+1=toffoliCount (eraseF w g k) ∧
    measurementCount (eraseOdd w g k)=measurementCount (eraseF w g k) ∧
    gateSlots (eraseOdd w g k)+8=gateSlots (eraseF w g k) := by
  rw [eraseF_eq]
  exact erase_layout_counts (eraseLayout w) g (eraseLayout_widths w) (2^256-1-k)

def programOdd (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  ExitMerge.fPart w g k++ExitMerge.eraseH w++ExitMerge.addPart w g k++
    rotateLeft (kR w)++ExitMerge.parBack w g k++eraseOdd w g k

theorem programOdd_triple (k : Nat) (hk : k<p) (he:k%2=1) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC base,b0 q=false) (h1797 : b0 (base 1797)=false) :
    let G := b0 (base 2400)
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF base b0 (2*H+(!par).toNat) K 0 par false false false) (programOdd base (base 2400) k)
      (MF base b0 0 Y 0 false false false false) := by
  intro G par H K Y
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  change f=decide ((if G then k else 2^256-1)<Y) at a8
  have gm := g_mut base (base 2400) hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by norm_num)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have gT : (base 2400)∉tR base := g_out base hn (base 2400) hg 1029 256 (by omega)
  -- threshold compare
  have s1 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par false false false (base 2400) (base 1028) 721 (by omega) G par
    (g_ne base hn (base 2400) hg 721 (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH base hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX base hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false (base 2400) G (g_ne base hn (base 2400) hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
  rw [←a3] at s4
  have s5 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 (base 2400)=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (base 514) (base 1028) 722 (by omega) f par
    (w_ne base hn _ _ (by omega) (by omega) (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  -- erase the tick word
  have s7 := stepW0Back base hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH base hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack base hn b0 K 0 par f (G && par) (f && par)
  -- one mapped addition to `y/2`
  have s10 := stepNegK base (base 2400) hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX base (base 2400) hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg] at s11
  have kWord : (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 := by
    rw [Nat.add_comm]; exact a5
  have s12 := stepKAddZero4 base hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par)
    hac h1797 Y a6 kWord
  rw [kWord] at s12
  have s13 := stepLoadKX base (base 2400) hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp base hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepMeasGp base (base 2400) hn b0 0 (Y/2) 0 par f false gm (g_ne base hn (base 2400) hg 721 (by omega))
  -- rotate and parity
  have s16 := stepRotL base hn b0 0 (Y/2) 0 par f false false (by rw [p_val] at a6; omega)
  have s17 := stepParBack base (base 2400) hn b0 k (Y/2) par f hg
  rw [show b0 (base 2400)=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  -- erase the flag
  have s18 := stepMaskT base hn b0 0 Y 0 false f false false (base 2400) G gT (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
    (2^256-1-k) (by omega)
  have s19 := stepNotT base hn b0 0 Y (0^^^(if G then 2^256-1-k else 0)) false f false false
  have hT (G' : Bool) : 2^256-1-(0^^^(if G' then 2^256-1-k else 0))=(if G' then k else 2^256-1) := by
    rw [p_val] at hk
    cases G'
    · simp
    · simp only [if_true, Nat.zero_xor]
      omega
  rw [hT G] at s19
  have s20 := stepEraseF base hn b0 0 Y (if G then k else 2^256-1) false f false false hac h1797
    (by rw [p_val] at a6; omega) a8
  have s21 := stepNotT base hn b0 0 Y (if G then k else 2^256-1) false false false false
  have s22 := stepMaskT base hn b0 0 Y (2^256-1-(if G then k else 2^256-1)) false false false false (base 2400) G gT
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (2^256-1-k) (by omega)
  have hT2 (G' : Bool) : (2^256-1-(if G' then k else 2^256-1))^^^(if G' then 2^256-1-k else 0)=0 := by
    cases G' <;> simp [Nat.xor_self]
  rw [hT2 G] at s22
  have oldErase:=s18.seq (s19.seq (s20.seq (s21.seq s22)))
  have ncin:base 1797∉E1Merge.mutL base:=by decide +kernel
  have erase : Triple (MF base b0 0 Y 0 false f false false) (eraseOdd base (base 2400) k)
      (MF base b0 0 Y 0 false false false false) := by
    intro s m hs
    rw [eraseOdd_eq k (by rw [p_val] at hk;omega) he s m hs.2.2.1
      ((hs.2.2.2.2.2.2.2 _ ncin).trans h1797)]
    simpa only [ExitMerge.eraseF,List.append_assoc] using oldErase s m hs
  have t:=s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq erase))))))))))))))))
  unfold programOdd ExitMerge.fPart ExitMerge.eraseH ExitMerge.addPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem MF_unique (w:Nat→Wire) (b:BasisState) (H X T:Nat) (par f gp fp:Bool)
    (s t:BasisState) (hs:MF w b H X T par f gp fp s) (ht:MF w b H X T par f gp fp t) : s=t := by
  have hH:∀q∈hR w,s q=t q:=(regValue_eq_iff _ _ _).mp (hs.1.trans ht.1.symm)
  have hX:∀q∈kR w,s q=t q:=(regValue_eq_iff _ _ _).mp (hs.2.1.trans ht.2.1.symm)
  have hT:∀q∈tR w,s q=t q:=(regValue_eq_iff _ _ _).mp (hs.2.2.1.trans ht.2.2.1.symm)
  funext q
  by_cases A:q∈hR w
  · exact hH q A
  by_cases B:q∈kR w
  · exact hX q B
  by_cases C:q∈tR w
  · exact hT q C
  by_cases D:q=w 1028
  · subst q;exact hs.2.2.2.1.trans ht.2.2.2.1.symm
  by_cases E:q=w 514
  · subst q;exact hs.2.2.2.2.1.trans ht.2.2.2.2.1.symm
  by_cases F:q=w 721
  · subst q;exact hs.2.2.2.2.2.1.trans ht.2.2.2.2.2.1.symm
  by_cases G:q=w 722
  · subst q;exact hs.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.2.1.symm
  have off:q∉mutL w:=by simp [mutL,A,B,C,D,E,F,G]
  exact (hs.2.2.2.2.2.2.2 q off).trans (ht.2.2.2.2.2.2.2 q off).symm

section Keep
variable (w:Nat→Wire) (g:Wire) (hn:(skywalkPoolWires w).Nodup)
include hn
theorem stepParBackKeep (b0 : BasisState) (k V : Nat) (par f gp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 (2*V) 0 par f gp false) (parBack w g k)
      (MF w b0 0 (2*V+(par ^^ (b0 g && decide (k%2=1)) ^^ f).toNat) 0 false f gp false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have lb (b par' : Bool) : ∀s : BasisState,MF w b0 0 (2*V+b.toNat) 0 par' f gp false s → s (w 770)=b := by
    intro s h; have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; cases b <;> simp
  apply Triple.conseq (fun s h => by rw [show 2*V=2*V+(false).toNat by simp] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parBack,if_pos hk,if_pos hk]
    have t := (stepLowCX w hn b0 0 V 0 false par f gp false (w 1028) par e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f gp false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f gp false (w 514) f e4 (fun s h => h.2.2.2.2.1)).seq
      ((stepParCX w hn b0 0 _ 0 par f gp false (w 770) _ e1 (lb _ par)).seq
      ((stepParCX w hn b0 0 _ 0 _ f gp false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      (stepParCX w hn b0 0 _ 0 _ f gp false (w 514) f e2 (fun s h => h.2.2.2.2.1))))))
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
    have t := (stepLowCX w hn b0 0 V 0 false par f gp false (w 1028) par e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f gp false (w 514) f e4 (fun s h => h.2.2.2.2.1)).seq
      ((stepParCX w hn b0 0 _ 0 par f gp false (w 770) _ e1 (lb _ par)).seq
      (stepParCX w hn b0 0 _ 0 _ f gp false (w 514) f e2 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    have e : ((par ^^ ((false ^^ par) ^^ f)) ^^ f)=false := by
      cases par <;> cases f <;> rfl
    rw [e] at h
    have e' : ((false ^^ par) ^^ f)=(par ^^ (b0 g && decide (k%2=1)) ^^ f) := by
      simp [hk]
    rw [e'] at h
    exact h


theorem MF_put_alpha (b:BasisState) (H X T:Nat) (par f gp fp v:Bool) (s:State)
    (hs:MF w b H X T par f gp fp s.basis) :
    MF w b H X T par f v fp (put s (w 721) v).basis := by
  have h:=stepBit w hn b H X T par f gp fp s (put s (w 721) v) 721 (by omega) hs
    (fun q hq=>by simp [put,writeBit,hq])
  simpa [put,writeBit] using h

theorem stepRetainGp (b:BasisState) (H X T:Nat) (par f:Bool) (hg:g∉skywalkPoolWires w) :
    Triple (MF w b H X T par f (b g && par) false)
      [.CX (w 514) (w 721),.measureX (w 722) [] []]
      (MF w b H X T par f ((b g && par) ^^ f) false) := by
  intro s m hs
  have gm:=g_mut w g hn hg
  have known:s.basis (w 721)=(s.basis g && s.basis (w 1028)):=by
    rw [hs.2.2.2.2.2.1,hs.2.2.2.1,hs.2.2.2.2.2.2.2 g gm]
  have eq:=retain_product g (w 1028) (w 514) (w 721) (w 722)
    (g_ne w hn g hg 721 (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) s m m hs.2.2.2.2.2.2.1 known
  rw [eq]
  have old:=stepMeasGp w g hn b H X T par f false gm (g_ne w hn g hg 721 (by omega)) s m hs
  have frame:=MF_put_alpha w hn b H X T par f false false ((b g && par) ^^ f) _ old.2
  rw [hs.2.2.2.2.2.2.2 g gm,hs.2.2.2.1,hs.2.2.2.2.1]
  exact ⟨old.1,frame⟩

end Keep

theorem eraseF_step (k Y:Nat) (hk:k<p) (a6:Y<p) (b0:BasisState) (f:Bool)
    (hac:∀q∈aC base,b0 q=false) (h1797:b0 (base 1797)=false)
    (a8:f=decide ((if b0 (base 2400) then k else 2^256-1)<Y)) :
    Triple (MF base b0 0 Y 0 false f false false) (eraseF base (base 2400) k)
      (MF base b0 0 Y 0 false false false false) := by
  let G:=b0 (base 2400)
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  have gm:=g_mut base (base 2400) hn hg
  have gT:=g_out base hn (base 2400) hg 1029 256 (by omega)
  have s18 := stepMaskT base hn b0 0 Y 0 false f false false (base 2400) G gT (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
    (2^256-1-k) (by omega)
  have s19 := stepNotT base hn b0 0 Y (0^^^(if G then 2^256-1-k else 0)) false f false false
  have hT (G' : Bool) : 2^256-1-(0^^^(if G' then 2^256-1-k else 0))=(if G' then k else 2^256-1) := by
    rw [p_val] at hk
    cases G'
    · simp
    · simp only [if_true, Nat.zero_xor]
      omega
  rw [hT G] at s19
  have s20 := stepEraseF base hn b0 0 Y (if G then k else 2^256-1) false f false false hac h1797
    (by rw [p_val] at a6; omega) a8
  have s21 := stepNotT base hn b0 0 Y (if G then k else 2^256-1) false false false false
  have s22 := stepMaskT base hn b0 0 Y (2^256-1-(if G then k else 2^256-1)) false false false false (base 2400) G gT
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (2^256-1-k) (by omega)
  have hT2 (G' : Bool) : (2^256-1-(if G' then k else 2^256-1))^^^(if G' then 2^256-1-k else 0)=0 := by
    cases G' <;> simp [Nat.xor_self]
  rw [hT2 G] at s22

  simpa only [eraseF,List.append_assoc] using s18.seq (s19.seq (s20.seq (s21.seq s22)))

def eraseEven (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  erasePrefixMoved g (w 721) (eraseLayout w).src (eraseLayout w).out ((eraseLayout w).carry.take 255)
    (eraseLayout w).cin (eraseLayout w).flag (2^256-1-k)

theorem eraseEven_step (k Y:Nat) (hk:k<p) (he:k%2=0) (hY:Y<p) (b:BasisState) (f:Bool)
    (hac:∀q∈aC base,b q=false) (h1797:b (base 1797)=false)
    (hf:f=decide ((if b (base 2400) then k else 2^256-1)<Y)) :
    Triple (MF base b 0 Y 0 false f (b (base 2400) && decide (Y%2=1)) false)
      (eraseEven base (base 2400) k) (MF base b 0 Y 0 false false false false) := by
  intro s m hs
  let z:=put s (base 721) false
  have hz:MF base b 0 Y 0 false f false false z.basis:=
    MF_put_alpha base base_pool_nodup b 0 Y 0 false f _ false false s hs
  have old:=eraseF_step k Y hk hY b f hac h1797 hf z m hz
  have pc:(2^256-1-k)%2=1:=by rw [p_val] at hk;omega
  have outcin:base 1797∉mutL base:=by decide +kernel
  have outcarry:∀q∈hC2 base,q∉mutL base:=by
    intro q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb base base_pool_nodup i 0 258 (by omega) (by omega) (by omega),
      nb base base_pool_nodup i 770 258 (by omega) (by omega) (by omega)⟩,
      nb base base_pool_nodup i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact w_ne base base_pool_nodup _ _ (by omega) (by omega) (by omega)
  have carry:∀q∈(eraseLayout base).carry,z.basis q=false:=by
    intro q hq
    exact (hz.2.2.2.2.2.2.2 q (outcarry q hq)).trans
      (hac q (blk_sub base 1540 256 1540 257 (by omega) (by omega) q hq))
  have ci:z.basis (base 1797)=false:=(hz.2.2.2.2.2.2.2 _ outcin).trans h1797
  have e:=eraseMoved_layout_eq (eraseLayout base) (base 2400) (eraseLayout_widths base)
    eraseLayout_nodup (2^256-1-k) pc z m hz.2.2.1 ci hz.2.2.2.2.2.1 carry
  have prod:(z.basis (base 2400) && z.basis (EntryFuse.lowBit (eraseLayout base)))=
      (b (base 2400) && decide (Y%2=1)):=by
    have lb:EntryFuse.lowBit (eraseLayout base)=base 770:=by rfl
    rw [lb,low_bit base base_pool_nodup b 0 Y 0 false f false false z.basis hz,
      hz.2.2.2.2.2.2.2 _ (g_mut base (base 2400) base_pool_nodup E1QubitPlacement.g2400)]
  have restore:put z (base 721) (b (base 2400) && decide (Y%2=1))=s:=by
    apply State.extensionality
    · rfl
    funext q
    by_cases h:q=base 721
    · subst q;simp [z,put,writeBit,hs.2.2.2.2.2.1]
    · simp [z,put,writeBit,h]
  rw [prod,←eraseF_eq] at e
  change run (eraseEven base (base 2400) k) m
    (put z (base 721) (b (base 2400) && decide (Y%2=1)))=run (eraseF base (base 2400) k) m z at e
  rw [restore] at e
  rw [e]
  exact old

def addPartKeep (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  FastConst.maskedNot g (kR w)++loadKX w g k++Verifier.Leaf4.zero4KAdd w++loadKX w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  [.CX (w 514) (w 721),.measureX (w 722) [] []]

def programEven (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  ExitMerge.fPart w g k++ExitMerge.eraseH w++addPartKeep w g k++
    rotateLeft (kR w)++ExitMerge.parBack w g k++eraseEven w g k

theorem programEven_triple (k : Nat) (hk : k<p) (he:k%2=0) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC base,b0 q=false) (h1797 : b0 (base 1797)=false) :
    let G := b0 (base 2400)
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF base b0 (2*H+(!par).toNat) K 0 par false false false) (programEven base (base 2400) k)
      (MF base b0 0 Y 0 false false false false) := by
  intro G par H K Y
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  change f=decide ((if G then k else 2^256-1)<Y) at a8
  have gm := g_mut base (base 2400) hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by norm_num)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have gT : (base 2400)∉tR base := g_out base hn (base 2400) hg 1029 256 (by omega)
  -- threshold compare
  have s1 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par false false false (base 2400) (base 1028) 721 (by omega) G par
    (g_ne base hn (base 2400) hg 721 (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH base hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX base hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false (base 2400) G (g_ne base hn (base 2400) hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 (base 2400) gm)
  rw [←a3] at s4
  have s5 := stepLoadTX base (base 2400) hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 (base 2400)=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX base hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (base 514) (base 1028) 722 (by omega) f par
    (w_ne base hn _ _ (by omega) (by omega) (by omega)) (w_ne base hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  -- erase the tick word
  have s7 := stepW0Back base hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH base hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack base hn b0 K 0 par f (G && par) (f && par)
  -- one mapped addition to `y/2`
  have s10 := stepNegK base (base 2400) hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX base (base 2400) hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg] at s11
  have kWord : (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 := by
    rw [Nat.add_comm]; exact a5
  have s12 := stepKAddZero4 base hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par)
    hac h1797 Y a6 kWord
  rw [kWord] at s12
  have s13 := stepLoadKX base (base 2400) hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 (base 2400)=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp base hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepRetainGp base (base 2400) hn b0 0 (Y/2) 0 par f hg
  -- rotate and parity
  have s16 := stepRotL base hn b0 0 (Y/2) 0 par f ((G && par) ^^ f) false (by rw [p_val] at a6; omega)
  have s17 := stepParBackKeep base (base 2400) hn b0 k (Y/2) par f ((G && par) ^^ f) hg
  rw [show b0 (base 2400)=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  have aprod:((G && par) ^^ f)=(G && decide (Y%2=1)):=by
    rw [a7]
    simp only [he,show ¬(0:Nat)=1 by decide,decide_false,Bool.and_false,Bool.xor_false]
    cases hG:G <;> cases hp:par <;> cases hf:f <;> simp [hG,hp,hf] at hfg ⊢
  have erase:=eraseEven_step k Y hk he a6 b0 f hac h1797 a8
  change Triple (MF base b0 0 Y 0 false f (G && decide (Y%2=1)) false) _ _ at erase
  rw [←aprod] at erase
  have t:=s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq erase))))))))))))))))
  unfold programEven ExitMerge.fPart ExitMerge.eraseH addPartKeep
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

theorem eraseEven_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (eraseEven w g k)+1=toffoliCount (eraseF w g k) ∧
    measurementCount (eraseEven w g k)=measurementCount (eraseF w g k) ∧
    gateSlots (eraseEven w g k)+6=gateSlots (eraseF w g k) := by
  rw [eraseF_eq]
  exact eraseMoved_layout_counts (eraseLayout w) g (w 721) (eraseLayout_widths w) (2^256-1-k)

theorem addPartKeep_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (addPartKeep w g k)=toffoliCount (addPart w g k) ∧
    measurementCount (addPartKeep w g k)=measurementCount (addPart w g k) ∧
    gateSlots (addPartKeep w g k)=gateSlots (addPart w g k) := by
  simp only [addPartKeep,addPart,toffoliCount_append,measurementCount_append,gateSlots_append]
  simp [toffoliCount,measurementCount,gateSlots,instructionSlots]

theorem programOdd_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (programOdd w g k)+1=toffoliCount (ExitMerge.program w g k) ∧
    measurementCount (programOdd w g k)=measurementCount (ExitMerge.program w g k) ∧
    gateSlots (programOdd w g k)+8=gateSlots (ExitMerge.program w g k) := by
  have h:=eraseOdd_counts w g k
  simp only [programOdd,ExitMerge.program,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem programEven_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (programEven w g k)+1=toffoliCount (ExitMerge.program w g k) ∧
    measurementCount (programEven w g k)=measurementCount (ExitMerge.program w g k) ∧
    gateSlots (programEven w g k)+6=gateSlots (ExitMerge.program w g k) := by
  have h:=eraseEven_counts w g k
  have a:=addPartKeep_counts w g k
  simp only [programEven,ExitMerge.program,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

def programAll (w:Nat→Wire) (g:Wire) (k:Nat) : Program :=
  if k%2=1 then programOdd w g k else programEven w g k

theorem programAll_counts (w:Nat→Wire) (g:Wire) (k:Nat) :
    toffoliCount (programAll w g k)+1=toffoliCount (ExitMerge.program w g k) ∧
    measurementCount (programAll w g k)=measurementCount (ExitMerge.program w g k) ∧
    gateSlots (programAll w g k)≤gateSlots (ExitMerge.program w g k) := by
  unfold programAll
  split_ifs
  · have h:=programOdd_counts w g k;omega
  · have h:=programEven_counts w g k;omega

theorem programAll_triple (k:Nat) (hk:k<p) (b:BasisState) (X:Nat) (hX:X<p)
    (hac:∀q∈aC base,b q=false) (hc:b (base 1797)=false) :
    let G:=b (base 2400)
    let par:=decide (X%2=1)
    let H:=X/2+(if par then hConstant else 0)
    let K:=(X/2+kConstant false par)%2^258
    let Y:=if G then (k+p-X)%p else X
    Triple (MF base b (2*H+(!par).toNat) K 0 par false false false)
      (programAll base (base 2400) k) (MF base b 0 Y 0 false false false false) := by
  unfold programAll
  split_ifs with he
  · exact programOdd_triple k hk he b X hX hac hc
  · exact programEven_triple k hk (by omega) b X hX hac hc

theorem programAll_run (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (initial field : State) (mF m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 X initial.basis)
    (ht : regValue (tR base) initial.basis=0) (h514 : initial.basis (base 514)=false)
    (h721 : initial.basis (base 721)=false) (h722 : initial.basis (base 722)=false)
    (hphase : field.phase=(run (NativeFirstDirect.forward base) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires base,
      field.basis q=(run (NativeFirstDirect.forward base) mF initial).basis q) :
    (run (programAll base (base 2400) k) m field).phase=initial.phase ∧
    regValue (kR base) (run (programAll base (base 2400) k) m field).basis=(if field.basis (base 2400) then (k+p-X)%p else X) ∧
    (∀q∈skywalkPoolWires base,q∉kR base → (run (programAll base (base 2400) k) m field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires base → (run (programAll base (base 2400) k) m field).basis q=field.basis q) := by
  have hn:=base_pool_nodup
  have hg:=E1QubitPlacement.g2400
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec base hn X hX initial mF hin
  have e770 : initial.basis (base 770)=decide (X%2=1) := by
    have sp := kR_split base hn initial.basis
    have hb : regValue (kR base) initial.basis=X := hin.b
    rw [hb] at sp
    cases h : initial.basis (base 770) <;> simp [h] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  have inPool (a n : Nat) (ha : a+n≤1798) : ∀q∈wireBlock base a n,q∈skywalkPoolWires base :=
    blk_sub base a n 0 1798 (by omega) ha
  have wPool (i : Nat) (hi : i<1798) : base i∈skywalkPoolWires base :=
    List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have keepI (i : Nat) (hi : i < 1798) (h1 : 257 ≤ i) (h2 : i < 770 ∨ 1028 < i) :
      field.basis (base i)=initial.basis (base i) := by
    rw [hpool _ (wPool i hi)]
    apply zrest
    simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨nb base hn i 0 257 hi (by omega) (by omega),nb base hn i 770 258 hi (by omega) (by omega)⟩,
      w_ne base hn i 1028 hi (by omega) (by omega)⟩
  have hR0 : regValue (hR base) field.basis=
      2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat := by
    rw [regValue_congr (hR base) field.basis _ (fun q hq => hpool q (inPool 0 258 (by omega) q hq))]
    exact zh
  have kR0 : regValue (kR base) field.basis=(X/2+kConstant false (decide (X%2=1)))%2^258 := by
    rw [regValue_congr (kR base) field.basis _ (fun q hq => hpool q (inPool 770 258 (by omega) q hq))]
    exact zk
  have tR0 : regValue (tR base) field.basis=0 := by
    rw [regValue_congr (tR base) field.basis initial.basis (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact keepI i (by omega) (by omega) (by omega))]
    exact ht
  have f1028 : field.basis (base 1028)=decide (X%2=1) := (hpool _ (wPool 1028 (by omega))).trans z1028
  have f514 : field.basis (base 514)=false := (keepI 514 (by omega) (by omega) (by omega)).trans h514
  have f721 : field.basis (base 721)=false := (keepI 721 (by omega) (by omega) (by omega)).trans h721
  have f722 : field.basis (base 722)=false := (keepI 722 (by omega) (by omega) (by omega)).trans h722
  have hac : ∀q∈aC base,field.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [keepI i (by omega) (by omega) (by omega)]
    exact (regValue_zero _ _).mp hin.carry _ hq
  have h1797 : field.basis (base 1797)=false := (keepI 1797 (by omega) (by omega) (by omega)).trans hin.cin
  have mf0 : MF base field.basis (2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat)
      ((X/2+kConstant false (decide (X%2=1)))%2^258) 0 (decide (X%2=1)) false false false field.basis :=
    ⟨hR0,kR0,tR0,f1028,f514,f721,f722,fun _ _ => rfl⟩
  obtain ⟨tp,o1,o2,o3,o4,o5,o6,o7,o8⟩ := programAll_triple k hk field.basis X hX hac h1797 field m mf0
  have outMut (q : Wire) (hq : q∉skywalkPoolWires base) : q∉mutL base := fun h => hq (mutL_pool base q h)
  refine ⟨tp.trans (hphase.trans zp),o2,?_,fun q hq => o8 q (outMut q hq)⟩
  intro q hq hk'
  by_cases qh : q∈hR base
  · rw [(regValue_zero _ _).mp o1 q qh]
    exact ((regValue_zero _ _).mp hin.a q qh).symm
  by_cases qt : q∈tR base
  · rw [(regValue_zero _ _).mp o3 q qt]
    exact ((regValue_zero _ _).mp ht q qt).symm
  by_cases q1 : q=base 1028
  · rw [q1,o4]; exact hin.one.symm
  by_cases q2 : q=base 514
  · rw [q2,o5]; exact h514.symm
  by_cases q3 : q=base 721
  · rw [q3,o6]; exact h721.symm
  by_cases q4 : q=base 722
  · rw [q4,o7]; exact h722.symm
  have nm : q∉mutL base := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,hk'⟩,qt⟩,q1,q2,q3,q4⟩
  rw [o8 q nm,hpool q hq]
  apply zrest
  simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
  exact ⟨⟨fun h' => qh (blk_sub base 0 257 0 258 (by omega) (by omega) q h'),hk'⟩,q1⟩

theorem eraseOdd_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (eraseOdd w g k)⊆wires (eraseF w g k) := by
  rw [eraseF_eq]
  exact erase_layout_wires (eraseLayout w) g (eraseLayout_widths w) (2^256-1-k)

theorem eraseEven_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (eraseEven w g k)⊆wires (eraseF w g k)∪{w 721} := by
  rw [eraseF_eq]
  exact eraseMoved_layout_wires (eraseLayout w) g (eraseLayout_widths w) (2^256-1-k)

theorem addPartKeep_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (addPartKeep w g k)⊆wires (addPart w g k) := by
  let P:=FastConst.maskedNot g (kR w)++loadKX w g k++Verifier.Leaf4.zero4KAdd w++loadKX w g k
  let A:Program:=[.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
    [.CX (w 514) (w 721),.measureX (w 722) [] []]
  let B:Program:=[.measureX (w 722) [] [.CZ (w 514) (w 1028)],
    .measureX (w 721) [] [.CZ g (w 1028)]]
  have tail:wires A⊆wires B:=by
    intro a H
    simp [A,B,wires,Instr.wires,correctionWires] at H ⊢
    tauto
  have whole:wires (P++A)⊆wires (P++B):=by
    rw [show wires (P++A)=wires P∪wires A from wires_append P A,
      show wires (P++B)=wires P∪wires B from wires_append P B]
    exact Finset.union_subset_union (Finset.Subset.refl _) tail
  simpa only [P,A,B,addPartKeep,addPart,List.append_assoc] using whole

theorem programAll_wires (w:Nat→Wire) (g:Wire) (k:Nat) :
    wires (programAll w g k)⊆wires (ExitMerge.program w g k) := by
  have odd:=eraseOdd_wires w g k
  have even:=eraseEven_wires w g k
  have add:=addPartKeep_wires w g k
  have alpha:w 721∈wires (addPart w g k):=by
    simp only [addPart,wires_append,Finset.mem_union]
    right
    simp [wires,Instr.wires,correctionWires]
  unfold programAll
  split_ifs
  · simp only [programOdd,ExitMerge.program,wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) odd
  · simp only [programEven,ExitMerge.program,wires_append]
    intro q h
    have C:=add (a:=q)
    have E:=even (a:=q)
    simp only [Finset.mem_union,Finset.mem_singleton] at h C E ⊢
    by_cases e:q=w 721
    · subst q;tauto
    · tauto

theorem eraseOdd_physical (k:Nat) (h:GatePhysical (eraseF base (base 2400) k)) :
    GatePhysical (eraseOdd base (base 2400) k) := by
  rw [eraseF_eq] at h
  exact erase_layout_physical (eraseLayout base) (base 2400) (eraseLayout_widths base) (2^256-1-k) h

theorem eraseEven_physical (k:Nat) (h:GatePhysical (eraseF base (base 2400) k)) :
    GatePhysical (eraseEven base (base 2400) k) := by
  rw [eraseF_eq] at h
  exact eraseMoved_layout_physical (eraseLayout base) (base 2400) (eraseLayout_widths base)
    eraseLayout_nodup (2^256-1-k) h

theorem addPartKeep_physical (k:Nat) (old:GatePhysical (addPart base (base 2400) k)) :
    GatePhysical (addPartKeep base (base 2400) k) := by
  have tail:GatePhysical ([Instr.measureX (base 722) [] [Correction.CZ (base 514) (base 1028)]]++
      [Instr.CX (base 514) (base 721),Instr.measureX (base 722) [] []]):=by
    simp [GatePhysical,PhysicalInstr,ProperGate,base]
  simp only [addPart,gatePhysical_append] at old
  simp only [addPartKeep,gatePhysical_append] at tail ⊢
  tauto

theorem programAll_physical (k:Nat) : GatePhysical (programAll base (base 2400) k) := by
  have old:=ExitMerge.program_physical base (base 2400) base_pool_nodup E1QubitPlacement.g2400 k
  simp only [ExitMerge.program,gatePhysical_append] at old
  have erase:GatePhysical (eraseF base (base 2400) k):=old.2
  have add:GatePhysical (addPart base (base 2400) k):=old.1.1.1.2
  have oddP:=eraseOdd_physical k erase
  have evenP:=eraseEven_physical k erase
  have addP:=addPartKeep_physical k add
  unfold programAll
  split_ifs
  · simp only [programOdd,gatePhysical_append]
    tauto
  · simp only [programEven,gatePhysical_append]
    tauto

end ECDSAAdd.Entrant.ParityXExit
end


-- Consolidated source module: ParityXExitKernel
section
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ParityXExitKernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog
attribute [local irreducible] run wires

/-! ### Placement of the merged exit circuit in the unhosted phase coordinates -/

def pi : Equiv.Perm Wire := E1QubitPlacement.rho.trans E1QubitPlacement.nativeSwap

def piN (i : Nat) : Nat :=
  if E1QubitPlacement.rhoN i=1797 then 511 else if E1QubitPlacement.rhoN i=511 then 1797
  else E1QubitPlacement.rhoN i

theorem pi_base (i : Nat) : pi (base i)=base (piN i) := by
  change E1QubitPlacement.nativeSwap (E1QubitPlacement.rho (base i))=_
  rw [E1QubitPlacement.rho_base]
  unfold E1QubitPlacement.nativeSwap
  rw [E1QubitPlacement.swap_base]
  unfold piN
  rfl

/-- The merged exit circuit, placed like the direct first tick. -/
def x1 (k : Nat) : Program := renameProgram pi (ParityXExit.programAll base (base 2400) k)

/-- The exit last phase with the inverse tick and the controlled negation merged. -/
def lastX (k : Nat) : Program :=
  skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true ++ x1 k

theorem x1_has530x (k:Nat) : (530:Wire)∈wires (x1 k) := by
  rw [x1,renameProgram_support]
  apply Finset.mem_image.mpr
  refine ⟨base 514,?_,?_⟩
  · have F:base 514∈wires (ExitMerge.fPart base (base 2400) k):=by
      simp only [ExitMerge.fPart,wires_append,Finset.mem_union]
      right
      simp [wires,Instr.wires]
    unfold ParityXExit.programAll
    split_ifs <;> simp only [ParityXExit.programOdd,ParityXExit.programEven,wires_append,Finset.mem_union] <;> tauto
  · rw [pi_base]
    decide +kernel


def negDiv (k x : Nat) (G : Bool) : Nat := if G then (k+p-x)%p else x

theorem forward_placed :
    FrontierEntry1591Native.forward base=renameProgram pi (NativeFirstDirect.forward base) := by
  have e := E1QubitPlacement.rho_fix E1QubitPlacement.nativeSwap
  change renameProgram (fun q => E1QubitPlacement.nativeSwap (E1QubitPlacement.rho q))
    (NativeFirstDirect.forward base)=renameProgram E1QubitPlacement.nativeSwap
      (NativeFirstDirect.forward base) at e
  rw [show renameProgram pi (NativeFirstDirect.forward base)=renameProgram
    (fun q => E1QubitPlacement.nativeSwap (E1QubitPlacement.rho q)) (NativeFirstDirect.forward base) from rfl,e]
  rfl

theorem mem_pool_iff (q : Wire) : q∈skywalkPoolWires base ↔ ∃ i, i < 1798 ∧ q=base i := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hi
    exact ⟨i,by omega,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem piN_lt (i : Nat) (hi : i < 1798) : piN i < 1798 := by
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

theorem pi_pool (q : Wire) (hq : q∈skywalkPoolWires base) : pi q∈skywalkPoolWires base := by
  obtain ⟨i,hi,rfl⟩ := (mem_pool_iff q).mp hq
  rw [pi_base]
  exact (mem_pool_iff _).mpr ⟨_,piN_lt i hi,rfl⟩

theorem pi_out (r : Wire) (h : r∉skywalkPoolWires base) : pi r=r := by
  have ne (i : Nat) (hi : i < 1798) : r≠base i := fun e => h ((mem_pool_iff r).mpr ⟨i,hi,e⟩)
  simp only [pi,Equiv.trans_apply,E1QubitPlacement.rho,E1QubitPlacement.nativeSwap,
    Equiv.swap_apply_of_ne_of_ne (ne 511 (by omega)) (ne 725 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 721 (by omega)) (ne 723 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 722 (by omega)) (ne 724 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (ne 1797 (by omega)) (ne 511 (by omega))]

theorem pi_symm_pool (q : Wire) (hq : q∈skywalkPoolWires base) : pi.symm q∈skywalkPoolWires base := by
  by_contra h
  have e := pi_out (pi.symm q) h
  rw [Equiv.apply_symm_apply] at e
  rw [←e] at h
  exact h hq

theorem piN_kR (i : Nat) (hi : 770 ≤ i ∧ i < 1028) : piN i=i := by
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

theorem pi_kR (q : Wire) (hq : q∈wireBlock base 770 258) : pi q=q := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [pi_base,piN_kR i (by omega)]

theorem pi_symm_kR (q : Wire) (hq : q∈wireBlock base 770 258) : pi.symm q=q := by
  have := pi_kR q hq
  rw [←this,Equiv.symm_apply_apply,this]

theorem pi_fix (i : Nat) (hi : i < 258 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1797) ∨ i=2400) :
    pi (base i)=base i := by
  rw [pi_base]; congr 1
  unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega

/-! ### The merged exit circuit on the image of the placed first tick

Every state comparison below goes through `pull_basis`/`pull_phase` rewrites, so the kernel never
has to evaluate a concrete program to see through `pullState`. -/

theorem pull_basis (f : Wire → Wire) (t : State) (q : Wire) : (pullState f t).basis q=t.basis (f q) := rfl
theorem pull_phase (f : Wire → Wire) (t : State) : (pullState f t).phase=t.phase := rfl
theorem x1_eq (k : Nat) : x1 k=renameProgram pi (ParityXExit.programAll base (base 2400) k) := rfl

theorem x1_run (k : Nat) (hk : k < p) (x y : Nat) (hx : x < p) (s v : State) (mn r : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis)
    (hphase : v.phase=(run (FrontierEntry1591Native.forward base) mn s).phase)
    (hpool : ∀q∈skywalkPoolWires base,v.basis q=(run (FrontierEntry1591Native.forward base) mn s).basis q) :
    (run (x1 k) r v).phase=s.phase ∧
    regValue (wireBlock base 770 258) (run (x1 k) r v).basis=negDiv k x (v.basis (base 2400)) ∧
    (∀q∈skywalkPoolWires base,q∉wireBlock base 770 258 → (run (x1 k) r v).basis q=s.basis q) ∧
    (∀q,q∉skywalkPoolWires base → (run (x1 k) r v).basis q=v.basis q) := by
  rw [x1_eq]
  have rr := run_rename pi pi.injective (ParityXExit.programAll base (base 2400) k) r v
  have fr := run_rename pi pi.injective (NativeFirstDirect.forward base) mn s
  rw [←forward_placed] at fr
  have sh : (i : Nat) → (hi : i < 2314) → (hdx : ¬(770 ≤ i ∧ i < 1026)) → (hdy : ¬(2056 ≤ i ∧ i < 2312)) →
      s.basis (base i)=false := by
    intro i hi hdx hdy
    apply input.2.2
    · exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
    · intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
      simp only [List.mem_range'_1] at hj
      have := base_injective e; omega
    · intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
      simp only [List.mem_range'_1] at hj
      have := base_injective e; omega
  have izero (i : Nat) (hi : i < 1798) (hx' : ¬(770 ≤ i ∧ i < 1026)) : (pullState pi s).basis (base i)=false := by
    rw [pull_basis,pi_base]
    have h1 := piN_lt i hi
    apply sh _ (by omega) _ (by omega)
    unfold piN E1QubitPlacement.rhoN; split_ifs <;> omega
  have blk0 (a n : Nat) (h : a+n ≤ 1798) (hd : a+n ≤ 770 ∨ 1026 ≤ a) :
      regValue (wireBlock base a n) (pullState pi s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact izero i (by omega) (by omega)
  have hxr : regValue (wireBlock base 770 256) (pullState pi s).basis=x := by
    rw [regValue_congr _ _ s.basis (fun q hq => by
      rw [pull_basis,pi_kR q (E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) q hq)])]
    exact input.1
  have seed : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 x (pullState pi s).basis := by
    refine ⟨blk0 0 258 (by omega) (by omega),?_,blk0 1540 257 (by omega) (by omega),
      izero 1797 (by omega) (by omega),izero 1028 (by omega) (by omega),izero 1797 (by omega) (by omega)⟩
    change regValue (E1Merge.kR base) (pullState pi s).basis=x
    rw [E1Merge.kR_x base base_pool_nodup,show E1Merge.xR base=wireBlock base 770 256 from rfl,hxr,
      blk0 1026 2 (by omega) (by omega)]
    simp
  have fpool : ∀q∈skywalkPoolWires base,
      (pullState pi v).basis q=(run (NativeFirstDirect.forward base) mn (pullState pi s)).basis q := by
    intro q hq
    rw [←fr,pull_basis,pull_basis]
    exact hpool _ (pi_pool q hq)
  have fphase : (pullState pi v).phase=(run (NativeFirstDirect.forward base) mn (pullState pi s)).phase := by
    rw [←fr,pull_phase,pull_phase]; exact hphase
  have pr := ParityXExit.programAll_run k hk x hx
    (pullState pi s) (pullState pi v) mn r seed (blk0 1029 256 (by omega) (by omega))
    (izero 514 (by omega) (by omega)) (izero 721 (by omega) (by omega)) (izero 722 (by omega) (by omega))
    fphase fpool
  rw [←rr] at pr
  obtain ⟨p1,p2,p3,p4⟩ := pr
  rw [pull_phase,pull_phase] at p1
  rw [pull_basis,pi_fix 2400 (by omega)] at p2
  refine ⟨p1,?_,?_,?_⟩
  · rw [regValue_congr _ _ (pullState pi (run (renameProgram pi (ParityXExit.programAll base (base 2400) k)) r v)).basis
      (fun q hq => by rw [pull_basis,pi_kR q hq])]
    exact p2
  · intro q hq hk'
    have hs : pi.symm q∉E1Merge.kR base := fun h => hk' (by
      have e := pi_kR _ h; rw [Equiv.apply_symm_apply] at e; rw [e]; exact h)
    have h3 := p3 _ (pi_symm_pool q hq) hs
    rw [pull_basis,pull_basis,Equiv.apply_symm_apply] at h3
    exact h3
  · intro q hq
    have hs : pi.symm q∉skywalkPoolWires base := fun h => hq (by
      have := pi_pool _ h; rwa [Equiv.apply_symm_apply] at this)
    have h4 := p4 _ hs
    rw [pull_basis,pull_basis,Equiv.apply_symm_apply] at h4
    exact h4

/-! ### Kernel with the merged exit: unhosted form -/

private theorem compose_half (N F C R : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀mn mf md,run R md (run F mf (run N mn s))=run N mn s) :
    run (C++R) mr (run (N++(F++C)) mp s)=run N (mp.take (measurementCount N)) s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]

theorem prefix_roundtrip (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true) mr
        (run (Rolling1588.firstPhase true) mp s)=
      run (FrontierEntry1591Native.forward base)
        (mp.take (measurementCount (FrontierEntry1591Native.forward base))) s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run (InverseFour15.stackReverse15 true) md (run (Rolling1588.stackForward true) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s := by
    have first := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input
    rw [← Rolling1588TickGap.stackForward_run_eq true x hx0 hx _ mf first]
    exact InverseFour15.stack_roundtrip15 true hn hlo x hx0 hx _ mf md first
  simpa only [Rolling1588.firstPhase,List.append_assoc] using
    compose_half (FrontierEntry1591Native.forward base) (Rolling1588.stackForward true)
      (skywalkArithmeticClear base) (InverseFour15.stackReverse15 true) s mp mr clearM twice stack

theorem prefix_pool :
    wires (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)⊆(skywalkPoolWires base).toFinset := by
  intro q hq
  apply InverseFour15.last_pool15 true
  simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union] at hq ⊢
  exact Or.inl hq

theorem first_pool (isA : Bool) : wires (Rolling1588.firstPhase isA)⊆(skywalkPoolWires base).toFinset := by
  have h := first_support_eq isA
  simp only [Rolling1588Lifetime.firstPhase] at h
  rw [h]; exact FrontierEntry1591Kernel.first_pool

theorem g_not_pool : base 2400∉skywalkPoolWires base := E1QubitPlacement.g2400

theorem num_not_pool (q : Wire) (hq : q∈skywalkPoolWires base) : q∉wireBlock base 2056 256 := by
  obtain ⟨i,hi,rfl⟩ := (mem_pool_iff q).mp hq
  intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj; have := base_injective e; omega

theorem kR_pool (q : Wire) (hq : q∈wireBlock base 770 258) : q∈skywalkPoolWires base := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact (mem_pool_iff _).mpr ⟨i,by omega,rfl⟩

theorem rawX (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      regValue (wireBlock base 770 258) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉wireBlock base 2056 256 → q∉wireBlock base 770 258 → out.basis q=s.basis q := by
  intro out
  obtain ⟨mp,mf,mr,eqOut⟩ : ∃ mp mf mr,
      out=run (lastX k) mr (run F mf (run (Rolling1588.firstPhase false) mp s)) :=
    ⟨_,_,_,by
      show run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s=_
      rw [FrontierEntry1591Native.kernel,run_append,run_append]⟩
  obtain ⟨r1,r2,r3⟩ := fieldResult mp mf
  generalize hAfter : run F mf (run (Rolling1588.firstPhase false) mp s)=after at eqOut r1 r2 r3
  generalize hBefore : run (Rolling1588.firstPhase true) mp s=beforeB at r1 r2 r3
  have eqOut2 : out=run (x1 k)
      (mr.drop (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)))
      (run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
        (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after) := by
    rw [eqOut,show lastX k=(skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)++x1 k from rfl,
      run_append]
  have agree := pool_run_agrees (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
    (skywalkPoolWires base).toFinset prefix_pool
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after beforeB r1
    (fun q hq => r3 q (num_not_pool q (List.mem_toFinset.mp hq)))
  generalize hv : run (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true)
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) after=v
    at eqOut2 agree
  have vB := prefix_roundtrip hn hlo x y hx0 hx s mp
    (mr.take (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) input
  rw [hBefore] at vB
  rw [vB] at agree
  have xr := x1_run k hk x y hx s v _
    (mr.drop (measurementCount (skywalkArithmeticClear base ++ InverseFour15.stackReverse15 true))) input agree.1
    (fun q hq => agree.2 q (List.mem_toFinset.mpr hq))
  rw [←eqOut2] at xr
  obtain ⟨o1,o2,o3,o4⟩ := xr
  have offA (q : Wire) (hq : q∉skywalkPoolWires base) : v.basis q=after.basis q := by
    rw [←hv]
    exact run_preserves_outside _ _ after q (fun h => hq (List.mem_toFinset.mp (prefix_pool h)))
  have offB (q : Wire) (hq : q∉skywalkPoolWires base) : beforeB.basis q=s.basis q := by
    rw [←hBefore]
    exact run_preserves_outside _ _ s q (fun h => hq (List.mem_toFinset.mp (first_pool true h)))
  have g2056 : base 2400∉wireBlock base 2056 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have gv : v.basis (base 2400)=s.basis (base 2400) := by
    rw [offA _ g_not_pool,r3 _ g2056,offB _ g_not_pool]
  have numOut (q : Wire) (hq : q∈wireBlock base 2056 256) : out.basis q=after.basis q := by
    have np : q∉skywalkPoolWires base := fun h => num_not_pool q h hq
    rw [o4 q np,offA q np]
  refine ⟨o1,?_,?_,?_⟩
  · rw [regValue_congr _ _ after.basis numOut]; exact r2
  · rw [o2,gv]
  · intro q h1 h2
    by_cases hp : q∈skywalkPoolWires base
    · exact o3 q hp h2
    · rw [o4 q hp,offA q hp,r3 q h1,offB q hp]

/-! ### Kernel with the merged exit: hosted form -/

private theorem phase_sites_split' : phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem rebind (P F Q : Program) (s : State) (m : List Bool)
    (input : ∀q∈phaseSites,s.basis q=false)
    (firstFree : ∀q∈phaseHosts,q∉wires P)
    (firstClean : ∀records,∀q∈FrontierEntry1591Native.workSites,
      (run P records s).basis q=false)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (lastFree : ∀q∈phaseHosts,q∉wires Q)
    (output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel P F Q) m s).basis q=false) :
    run (renameProgram phaseHost P++(F++renameProgram phaseHost Q)) m s=
      run (FrontierEntry1591Native.kernel P F Q) m s := by
  let mp := m.take (measurementCount P)
  let rest := m.drop (measurementCount P)
  let mf := rest.take (measurementCount F)
  let mr := rest.drop (measurementCount F)
  let before := run P mp s
  let after := run F mf before
  have finalClean : ∀q∈phaseSites,(run Q mr after).basis q=false := by
    simpa only [FrontierEntry1591Native.kernel,run_append] using output
  have lastInput : ∀q∈phaseSites,after.basis q=false := by
    intro q hq
    rw [phase_sites_split'] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_split'];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_split'] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_split'];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last

theorem x1_hosts_free (k : Nat) (q : Wire) (hq : q∈phaseHosts) : q∉wires (x1 k) := by
  intro h
  rw [x1_eq,renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
  obtain ⟨i,rfl,hi⟩ := E1QubitPlacement.S_cases _ (ExitMerge.program_support base (base 2400) k (ParityXExit.programAll_wires base (base 2400) k ha))
  rw [pi_base] at hq
  simp only [phaseHosts,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with e|e|e <;> have := base_injective e <;> unfold piN E1QubitPlacement.rhoN at this <;>
    split_ifs at this <;> omega

theorem lastX_hosts_free (k : Nat) (q : Wire) (hq : q∈phaseHosts) : q∉wires (lastX k) := by
  have old := InverseFour15.last_hosts_free15 true q hq
  simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union,not_or] at old
  simp only [lastX,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨old.1.1,old.1.2⟩,x1_hosts_free k q hq⟩

theorem top_zero (t : BasisState) (h : regValue (wireBlock base 770 258) t < 2^256) :
    ∀q∈wireBlock base 1026 2,t q=false := by
  have sp := E1Merge.kR_x base base_pool_nodup t
  change regValue (wireBlock base 770 258) t=_ at sp
  apply (regValue_zero _ _).mp
  by_contra hne
  have : 1 ≤ regValue (wireBlock base 1026 2) t := Nat.one_le_iff_ne_zero.mpr hne
  have : 2^256 ≤ 2^256*regValue (wireBlock base 1026 2) t := Nat.le_mul_of_pos_right _ this
  omega

theorem negDiv_lt (k x : Nat) (G : Bool) (hx : x < p) : negDiv k x G < p := by
  unfold negDiv; split
  · exact Nat.mod_lt _ (by norm_num [p])
  · exact hx

theorem p_lt : p < 2^256 := by norm_num [p]

theorem sites_not_num (q : Wire) (hq : q∈phaseSites) : q∉wireBlock base 2056 256 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  intro h; obtain ⟨j,hj,e'⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  rcases hq with e|e|e|e|e|e <;> rw [e] at e' <;> have := base_injective e' <;> omega

theorem sites_not_kR (q : Wire) (hq : q∈phaseSites) (h26 : q≠base 1026) : q∉wireBlock base 770 258 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  intro h; obtain ⟨j,hj,e'⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  rcases hq with e|e|e|e|e|e
  · exact h26 e
  all_goals (rw [e] at e'; have := base_injective e'; omega)

theorem hostedX (F : Program) (k : Nat) (hk : k < p) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (value : Nat) (input : SkywalkArithmeticInput base x y s.basis)
    (integerBoundary : ∀mn mf,
      run (Rolling1588.stackForward false) mf (run (FrontierEntry1591Native.forward base) mn s)=
        pullState (OB5.sig 511) (run (Rolling1588.allEncode base false 102) []
          (run (W.compactSkywalkForward base 1 511) []
            (run (FrontierEntry1591Native.forward base) mn s))))
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (fieldResult : ∀mp mf,
      let beforeA := run (Rolling1588.firstPhase false) mp s
      let beforeB := run (Rolling1588.firstPhase true) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (renameProgram phaseHost (Rolling1588.firstPhase false)++
      (F++renameProgram phaseHost (lastX k))) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      regValue (wireBlock base 770 258) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉wireBlock base 2056 256 → q∉wireBlock base 770 258 → out.basis q=s.basis q := by
  have raw := rawX F k hk hn hlo x y hx0 hx s m value input fieldResult
  have clean := caller_phase_clean x y s input
  obtain ⟨o1,o2,o3,o4⟩ := raw
  have output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (Rolling1588.firstPhase false) F (lastX k)) m s).basis q=false := by
    intro q hq
    have hq' := hq
    simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq'
    by_cases h26 : q=base 1026
    · subst h26
      apply top_zero _ (by rw [o3]; exact (negDiv_lt k x _ hx).trans p_lt)
      exact List.mem_map.mpr ⟨1026,by simp only [List.mem_range'_1]; omega,rfl⟩
    · rw [o4 q (sites_not_num q hq) (sites_not_kR q hq h26)]
      exact clean q hq
  have same := rebind (Rolling1588.firstPhase false) F (lastX k) s m clean (first_hosts_free false)
    (fun records => first_clean_of_boundary false hn x y hx0 hx s records input integerBoundary)
    fieldFree (lastX_hosts_free k) output
  dsimp only
  rw [same]
  exact ⟨o1,o2,o3,o4⟩

/-! ### The TickGap exit kernel with the merged exit -/

def kernelX (k : Nat) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase false)++
    (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k))

set_option linter.unusedVariables false in
def ExitNegCorrect (K : Program) (k : Nat) : Prop := ∀
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false),
    let out := run K m s
    out.phase=s.phase ∧ regValue (skywalkArithmeticNumerator base) out.basis=centerWord (Y*(x:Fp)/2) ∧
      regValue (skywalkArithmeticDivisor base) out.basis=negDiv k x (s.basis (base 2400)) ∧
      ∀q,q∉skywalkArithmeticNumerator base → q∉skywalkArithmeticDivisor base → out.basis q=s.basis q

private theorem append_run_eq' (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernelX_correct (k : Nat) (hk : k < p) : ExitNegCorrect (kernelX k) k := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase false))=
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase false)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics false).2.1]
  have eq := append_run_eq' _ _ (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k)) s m records
    (fun r => Rolling1588TickGap.first_hosted_run_eq false hn x Y.val hx0 hx s r input)
  have res := hostedX Rolling1588.exitFieldHosted k hk hn hlo x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input
    (fun mn mf => Rolling1588.stackForward_boundary false hn hlo x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x Y.val hx0 hx s mn input))
    Rolling1588.exitFieldHosted_work_free
    (fun mp mf => Rolling1588.exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  dsimp only at res ⊢
  rw [kernelX,eq]
  obtain ⟨o1,o2,o3,o4⟩ := res
  have tz := top_zero _ (by rw [o3]; exact (negDiv_lt k x _ hx).trans p_lt)
  have sp := E1Merge.kR_x base base_pool_nodup
    (run (renameProgram phaseHost (Rolling1588.firstPhase false)++
      (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k))) m s).basis
  change regValue (wireBlock base 770 258) _=regValue (wireBlock base 770 256) _+_ at sp
  rw [o3,(regValue_zero _ _).mpr tz] at sp
  refine ⟨o1,o2,by simp only [skywalkArithmeticDivisor]; omega,?_⟩
  intro q h1 h2
  by_cases hk' : q∈wireBlock base 770 258
  · have top : q∈wireBlock base 1026 2 := by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk'
      simp only [List.mem_range'_1] at hi
      refine List.mem_map.mpr ⟨i,?_,rfl⟩
      simp only [List.mem_range'_1]
      by_contra hc
      exact h2 (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)
    rw [tz q top]
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp top
    simp only [List.mem_range'_1] at hi
    exact (input.2.2 _ (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩) h2 h1).symm
  · exact o4 q h1 hk'

/-! ### Point-layout transfer -/

theorem wordTransferX (L : ControlledPointLayout) (f : Wire → Wire) (k : Nat)
    (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (gSite : base 2400∈domain)
    (X : Nat) (Y : Fp) (R : Nat)
    (s : State) (m : List Bool)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (P : Program) (programSites : wires P⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      t.basis (base 2409)=false → t.basis (base 2410)=false →
      (run P records t).phase=t.phase ∧
      regValue (skywalkArithmeticNumerator base) (run P records t).basis=R ∧
      regValue (skywalkArithmeticDivisor base) (run P records t).basis=negDiv k X (t.basis (base 2400)) ∧
      ∀ q,q∉skywalkArithmeticNumerator base → q∉skywalkArithmeticDivisor base →
        (run P records t).basis q=t.basis q) :
    (run (renameProgram f P) m s).phase=s.phase ∧
    regValue L.point.y (run (renameProgram f P) m s).basis=R ∧
    regValue L.point.x (run (renameProgram f P) m s).basis=negDiv k X (s.basis L.core.generic) ∧
      ∀q,q∉L.point.y → q∉L.point.x → (run (renameProgram f P) m s).basis q=s.basis q := by
  let t := ECDSAAdd.Entrant.selInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,ECDSAAdd.Entrant.selInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [ECDSAAdd.Entrant.selRegMap f _ t.basis s.basis
        (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,ECDSAAdd.Entrant.selInput,if_neg used]
  have strong := P_spec t m input (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective P programSites m t s rfl inputBits
  have tg : t.basis (base 2400)=s.basis L.core.generic := by rw [inputBits _ gSite,controlMap]
  refine ⟨transfer.1.trans strong.1,?_,?_,?_⟩
  · rw [←numeratorMap]
    exact (ECDSAAdd.Entrant.selRegMap f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · rw [←divisorMap,←tg]
    exact (ECDSAAdd.Entrant.selRegMap f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dxSites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.2.1
  · intro q outY outX
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      have awayY : a∉skywalkArithmeticNumerator base := by
        intro mem; apply outY; rw [←numeratorMap]; exact List.mem_map.mpr ⟨a,mem,rfl⟩
      have awayX : a∉skywalkArithmeticDivisor base := by
        intro mem; apply outX; rw [←divisorMap]; exact List.mem_map.mpr ⟨a,mem,rfl⟩
      exact (transfer.2 a ha).trans ((strong.2.2.2 a awayY awayX).trans (inputBits a ha))
    · exact run_rename_pool_outside f domain P programSites m s q image

theorem lx_support (k : Nat) : wires (lastX k) ⊆ wires (Rolling1588.lastPhase true) ∪ wires (x1 k) := by
  intro q hq
  simp only [lastX,wires_append,Finset.mem_union] at hq
  rcases hq with (hc | hs) | hx
  · have h : q ∈ wires (InverseFour15.lastPhase15 true) := by
      simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union]
      exact Or.inl (Or.inl hc)
    rcases Finset.mem_union.mp (InverseFour15.last_extra15 true h) with old | extra
    · exact Finset.mem_union_left _ old
    · simp only [Finset.mem_singleton] at extra
      subst q
      exact Finset.mem_union_right _ (x1_has530x k)
  · have h : q ∈ wires (InverseFour15.lastPhase15 true) := by
      simp only [InverseFour15.lastPhase15,wires_append,Finset.mem_union]
      exact Or.inl (Or.inr hs)
    rcases Finset.mem_union.mp (InverseFour15.last_extra15 true h) with old | extra
    · exact Finset.mem_union_left _ old
    · simp only [Finset.mem_singleton] at extra
      subst q
      exact Finset.mem_union_right _ (x1_has530x k)
  · exact Finset.mem_union_right _ hx

theorem x1_logical (k : Nat) : wires (x1 k)⊆(E1QubitPlacement.S).image pi := by
  rw [x1_eq,renameProgram_support]
  exact Finset.image_subset_image ((ParityXExit.programAll_wires base (base 2400) k).trans
    (ExitMerge.program_support base (base 2400) k))

theorem host_pi (q : Wire) : phaseHost (pi q)=E1QubitPlacement.sig (E1QubitPlacement.rho q) := rfl

theorem hostedX1_logical (k : Nat) :
    wires (renameProgram phaseHost (x1 k))⊆OB5Support.logicalSites := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (x1_logical k ha)
  obtain ⟨i,rfl,hi⟩ := E1QubitPlacement.S_cases b hb
  rw [host_pi,E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range i hi)

theorem kernelX_support (k : Nat) : wires (kernelX k)⊆OB5Support.logicalSites := by
  have old := Rolling1588TickGap.exitKernel_support
  intro q hq
  simp only [kernelX,wires_append,Finset.mem_union,renameProgram_support] at hq
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,wires_append,
    renameProgram_support] at old
  rcases hq with h|h|h
  · exact old (Finset.mem_union_left _ h)
  · exact old (Finset.mem_union_right _ (Finset.mem_union_left _ h))
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rcases Finset.mem_union.mp (lx_support k ha) with h1|h1
    · exact old (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,h1,rfl⟩)))
    · exact hostedX1_logical k (by rw [renameProgram_support]; exact Finset.mem_image.mpr ⟨a,h1,rfl⟩)

def HalfMultiplyNegCorrect (L : ControlledPointLayout) (P : Program) (k : Nat) : Prop :=
  ∀(X Y : Nat),X < p → 0 < X → Y < p → ∀(s : State)(m : List Bool),
    regValue L.point.x s.basis=X → regValue L.point.y s.basis=Y → regValue L.dialogPool s.basis=0 →
    (run P m s).phase=s.phase ∧
    regValue L.point.y (run P m s).basis=centerWord (((Y:Fp)*(X:Fp))/2) ∧
    regValue L.point.x (run P m s).basis=negDiv k X (s.basis L.core.generic) ∧
    ∀q,q∉L.point.y → q∉L.point.x → (run P m s).basis q=s.basis q

theorem exitX_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k < p) :
    HalfMultiplyNegCorrect L (FrontierEntry1591Callers.exit (kernelX k) L) k := by
  intro X Y hX hX0 hY s m hx hy hc
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,
    selectorG,selectorS,zeroFlag⟩
  have dx : (wireBlock base 770 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have dy : (wireBlock base 2056 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have gSite : base 2400∈OB5Support.logicalSites := by
    have := E1QubitPlacement.sw_logical 2400 (by unfold E1QubitPlacement.Rng; omega)
    simpa [E1QubitPlacement.sw] using this
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have result := wordTransferX L (wireFn2 L) k OB5Support.logicalSites
    (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
      (ArithmeticOB5.logical_sub_old hb) eq)
    divisorMap numeratorMap controlMap
    (fun q hq used hx hy => sharedWork q hq (ArithmeticOB5.logical_sub_old used) hx hy)
    selectorG selectorS dx dy gSite X (Y:Fp) (centerWord (((Y:Fp)*(X:Fp))/2))
    s m hx (hy.trans yValue.symm) hc
    (kernelX k) (kernelX_support k)
    (fun t records input hg hs => kernelX_correct k hk
      config.1 above config.2.1 config.2.2 X (Y:Fp) hX0 hX t records input hg hs)
  simpa only [FrontierEntry1591Callers.exit] using result

private theorem sub_val'' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

/-! ### Point step: the multiplication kernel with the merged negation, then `exitY` -/

theorem fusedMultiplyX_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++ExitFusionResearch.exitY L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m v
  let n := measurementCount P
  let a := run P (m.take n) s
  have hp : 0 < X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have half := correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h => finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h => finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have genY : L.core.generic∉L.point.y :=
    fun h => finGeneric_not_xy L hn (List.mem_append_right _ h)
  have genX : L.core.generic∉L.point.x :=
    fun h => finGeneric_not_xy L hn (List.mem_append_left _ h)
  have ag : a.basis L.core.generic=G := (half.2.2.2 _ genY genX).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq => half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av : regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  have out := ExitFusionResearch.exitY_correct L hw hn ((Y*X)/2) k a (m.drop n) av ac
  let b := run (ExitFusionResearch.exitY L k) (m.drop n) a
  have phase : b.phase=s.phase := out.1.trans half.1
  have xy (q : Wire) (hq : q∈L.point.x) : q∉L.point.y := by
    intro h
    have nd := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have p1 := List.count_pos_iff.mpr hq
    have p2 := List.count_pos_iff.mpr h
    simp only [ControlledPointLayout.dialogUsedWires,PointAddLayout.pointWires,List.count_append,
      List.count_cons] at nd
    omega
  have frame (q : Wire) (hy : q∉L.point.y) (hx : q∉L.point.x) : b.basis q=s.basis q :=
    (out.2.2 q hy).trans (half.2.2.2 q hy hx)
  have twice : 2*((Y*X)/2)=Y*X := by
    have two : (2:Fp)≠0 := by decide
    field_simp
  have bv : regValue L.point.y b.basis=(Y*X-(if G then k else 0)).val := by
    rw [out.2.1,ag,twice]
  have bx : regValue L.point.x b.basis=(if G then cx-X else X).val := by
    rw [regValue_congr _ _ a.basis (fun q hq => out.2.2 q (xy q hq)),half.2.2.1,v.generic]
    cases G
    · rfl
    · simp only [negDiv,if_true]; rw [sub_val'']
  rw [run_append]
  change b.phase=s.phase ∧ PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin b.basis
  refine ⟨phase,bx,bv,?_,?_,?_⟩
  · exact (frame _ genY genX).trans v.generic
  · rw [←v.clean]
    exact regValue_congr _ _ _ (fun q hq => frame q (poolY q hq) (poolX q hq))
  · intro q hq
    exact (frame q (fun h => hq (List.mem_append_right _ h)) (fun h => hq (List.mem_append_left _ h))).trans
      (v.rest q hq)

def restXX (L : ControlledPointLayout) (k : Nat) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++renameProgram phaseHost (lastX k)))

theorem exit_splitX (L : ControlledPointLayout) (k : Nat) :
    FrontierEntry1591Callers.exit (kernelX k) L=E1QubitPlacement.tickF L++restXX L k := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,kernelX,Rolling1588TickGap.firstPhase,restXX,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

/-! ### Resources of the merged exit inside the stage -/

theorem x1_counts (k : Nat) : toffoliCount (x1 k)=766 ∧ measurementCount (x1 k)=1027 := by
  rw [x1_eq,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  have h:=ParityXExit.programAll_counts base (base 2400) k
  have old:=ExitMerge.program_counts base (base 2400) k
  omega

theorem x1_slots (k : Nat) : Challenge.gateSlots (x1 k) ≤ 22000 := by
  rw [x1_eq,Baselines.rename_gateSlots]
  exact (ParityXExit.programAll_counts base (base 2400) k).2.2.trans
    (ExitMerge.program_slots base (base 2400) k)

theorem x1_physical (k : Nat) : GatePhysical (x1 k) := by
  rw [x1_eq]
  exact gatePhysical_rename pi pi.injective _
    (ParityXExit.programAll_physical k)

theorem restXX_metrics (L : ControlledPointLayout) (k : Nat) :
    toffoliCount (restXX L k)+255=toffoliCount (ReflectionE1TickGap.restX L)+768 ∧
    measurementCount (restXX L k)+508=measurementCount (ReflectionE1TickGap.restX L)+1027 ∧
    Challenge.gateSlots (restXX L k) ≤ Challenge.gateSlots (ReflectionE1TickGap.restX L)+23084 := by
  have c := x1_counts k
  have rev := InverseFour15.reverse_metrics_new true
  have sl := x1_slots k
  have i := FrontierEntry1591NativeH.counts base
  simp only [restXX,ReflectionE1TickGap.restX,lastX,Rolling1588.lastPhase,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

theorem restXX_support (L : ControlledPointLayout) (k : Nat) :
    wires (restXX L k)⊆wires (ReflectionE1TickGap.restX L)∪
      wires (renameProgram (wireFn2 L) (renameProgram phaseHost (x1 k))) := by
  have sub := Finset.image_subset_image (f := wireFn2 L) (Finset.image_subset_image (f := phaseHost) (lx_support k))
  simp only [Finset.image_union] at sub
  intro q hq
  simp only [restXX,ReflectionE1TickGap.restX,renameProgram_support,
    wires_append,Finset.image_union,Finset.mem_union] at hq ⊢
  have imp : q ∈ ((wires (lastX k)).image phaseHost |>.image (wireFn2 L)) →
      q ∈ ((wires (Rolling1588.lastPhase true)).image phaseHost |>.image (wireFn2 L)) ∨
        q ∈ ((wires (x1 k)).image phaseHost |>.image (wireFn2 L)) := by
    intro h
    exact Finset.mem_union.mp (sub h)
  tauto
theorem placedX1_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Nat) :
    wires (renameProgram (wireFn2 L) (renameProgram phaseHost (x1 k)))⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ (hostedX1_logical k)

theorem hostedX1_labels (k : Nat) (q : Wire) (hq : q∈wires (renameProgram phaseHost (x1 k))) :
    ∃ j, q=base (E1QubitPlacement.sw (E1QubitPlacement.rhoN j)) ∧
      (j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j=721 ∨ j=722 ∨ j=2400) := by
  rw [renameProgram_support] at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (x1_logical k ha)
  obtain ⟨j,rfl,hj⟩ := E1QubitPlacement.S_cases b hb
  exact ⟨j,by rw [host_pi,E1QubitPlacement.rho_base,E1QubitPlacement.sig_base],hj⟩

theorem kernelX_physical (k : Nat) : GatePhysical (kernelX k) := by
  have old := Rolling1588TickGap.exitKernel_physical
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,gatePhysical_append] at old
  have last := InverseFour15.last_physical15 true
  simp only [InverseFour15.lastPhase15,gatePhysical_append] at last
  have lx : GatePhysical (lastX k) := by
    simp only [lastX,gatePhysical_append]; exact ⟨last.1,x1_physical k⟩
  simp only [kernelX,gatePhysical_append]
  exact ⟨old.1,old.2.1,gatePhysical_rename phaseHost phaseHost.injective _ lx⟩

theorem restXX_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Nat) :
    GatePhysical (restXX L k) := by
  have physical := FrontierEntry1591Native.placed_physical L hw hn (kernelX k) (kernelX_support k)
    (kernelX_physical k)
  have e : GatePhysical (FrontierEntry1591Callers.exit (kernelX k) L) := by
    unfold FrontierEntry1591Callers.exit; exact physical
  rw [exit_splitX,gatePhysical_append] at e
  exact e.2

theorem sw760 (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j=721 ∨ j=722 ∨ j=2400) :
    E1QubitPlacement.sw (E1QubitPlacement.rhoN j)≠760 := by
  have range:=E1QubitPlacement.rhoN_range j hj
  generalize E1QubitPlacement.rhoN j=i at range ⊢
  unfold E1QubitPlacement.Rng at range
  unfold E1QubitPlacement.sw
  split_ifs <;> omega

theorem kernelX_760_free (k : Nat) : base 760∉wires (kernelX k) := by
  have old := Rolling1588TickGap.exitKernel_760_free
  simp only [Rolling1588TickGap.exitKernel,Rolling1588TickGap.kernel,wires_append,
    renameProgram_support,Finset.mem_union,not_or] at old
  simp only [kernelX,wires_append,renameProgram_support,Finset.mem_union,not_or]
  refine ⟨old.1,old.2.1,?_⟩
  intro h
  obtain ⟨a,ha,e⟩ := Finset.mem_image.mp h
  rcases Finset.mem_union.mp (lx_support k ha) with h1|h1
  · exact old.2.2 (Finset.mem_image.mpr ⟨a,h1,e⟩)
  · obtain ⟨j,e',hj⟩ := hostedX1_labels k (phaseHost a) (by
      rw [renameProgram_support]; exact Finset.mem_image.mpr ⟨a,h1,rfl⟩)
    rw [e] at e'
    exact sw760 j hj (base_injective e').symm


theorem restXX_delta (L:ControlledPointLayout) (k:Nat) :
    toffoliCount (restXX L k)+1=toffoliCount (ExitMergeKernel.restXX L k) ∧
    measurementCount (restXX L k)=measurementCount (ExitMergeKernel.restXX L k) ∧
    Challenge.gateSlots (restXX L k)≤Challenge.gateSlots (ExitMergeKernel.restXX L k) := by
  have h:=ParityXExit.programAll_counts base (base 2400) k
  simp only [restXX,ExitMergeKernel.restXX,lastX,ExitMergeKernel.lastX,x1,ExitMergeKernel.x1,
    toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

theorem restXX_subset (L:ControlledPointLayout) (k:Nat) :
    wires (restXX L k)⊆wires (ExitMergeKernel.restXX L k) := by
  have x1sub:wires (x1 k)⊆wires (ExitMergeKernel.x1 k):=by
    simp only [x1,ExitMergeKernel.x1,renameProgram_support]
    exact Finset.image_subset_image (ParityXExit.programAll_wires base (base 2400) k)
  have last:wires (lastX k)⊆wires (ExitMergeKernel.lastX k):=by
    simp only [lastX,ExitMergeKernel.lastX,wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) x1sub
  have host:wires (renameProgram phaseHost (lastX k))⊆
      wires (renameProgram phaseHost (ExitMergeKernel.lastX k)):=by
    simp only [renameProgram_support]
    exact Finset.image_subset_image last
  have inner:=Finset.union_subset_union
    (Finset.Subset.refl (wires (renameProgram phaseHost (Rolling1588TickGap.tailPhase false))))
    (Finset.union_subset_union (Finset.Subset.refl (wires Rolling1588.exitFieldHosted)) host)
  simpa only [restXX,ExitMergeKernel.restXX,renameProgram_support,wires_append] using
    Finset.image_subset_image (f:=wireFn2 L) inner

end ECDSAAdd.Entrant.ParityXExitKernel
end


-- Consolidated source module: ParityStageXY
section

namespace ECDSAAdd.Entrant.ParityStageXY
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap OB5 Rolling1588Lifetime ParityCarry ParityConvert ParityUniform ParityXEntry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  InverseFour15.lastPhase15 InverseFour15.stackReverse15 InverseFour15.reverseTail15 Rolling1588TickGap.tailPhase
def restEntry (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true) ++
      (Rolling1588.entryFieldHosted ++ renameProgram phaseHost (InverseFour15.lastPhase15 false)))

def entryRef (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky ++ E1QubitPlacement.entryM L kx ++ restEntry L

theorem entry_split_ref (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry InverseFour15.entryKernel15 L = E1QubitPlacement.tickF L ++ restEntry L := by
  have tick := E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base)) = E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,InverseFour15.entryKernel15,InverseFour15.kernel15,
    Rolling1588TickGap.firstPhase,restEntry,renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem entryRef_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryRef L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX L hw hn X Y G origin kx
  have divide := division_step InverseFour15.entryKernel15 InverseFour15.entry_support530
    InverseFour15.entry_correct15 L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior := add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky ++ E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx ++ fusedY L ky ++ E1QubitPlacement.tickF L)
    (R:=restEntry L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryRef,division,entry_split_ref,List.append_assoc] using prior


def entryStageAll (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  entryYAll L ky++entryXAll L kx++restEntry L

theorem entryStageAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (s : State) (m : List Bool) (hX:regValue L.point.x s.basis=X.val)
    (hY:regValue L.point.y s.basis=Y.val) (hc : regValue L.dialogPool s.basis=0) :
    run (entryStageAll L kx ky) m s=run (entryRef L kx ky) m s := by
  have cm:measurementCount (entryYAll L ky)=measurementCount (fusedY L ky) :=
    (entryYAll_counts L hw ky).2.1.trans (fusedY_counts L hw ky).2.symm
  have first:=prefix_eq (entryYAll L ky) (fusedY L ky) (entryXAll L kx++restEntry L) s m cm
      (entryYAll_eq L hw hn Y ky s m hY hc)
  have fy:=fusedY_correct L hw hn Y ky s (m.take (measurementCount (fusedY L ky))) hY hc
  let t:=run (fusedY L ky) (m.take (measurementCount (fusedY L ky))) s
  have tx:regValue L.point.x t.basis=X.val:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)),hX]
  have tc:regValue L.dialogPool t.basis=0:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)),hc]
  have second:=prefix_eq (entryXAll L kx) (E1QubitPlacement.entryM L kx) (restEntry L)
    t (m.drop (measurementCount (fusedY L ky))) (entryXAll_counts L kx).2.1
    (entryXAll_eq L hw hn X kx t _ tx tc)
  change run ((entryYAll L ky++entryXAll L kx)++restEntry L) m s=_
  rw [List.append_assoc,first]
  simpa only [entryRef,List.append_assoc,run_append,t] using second

theorem entryStageAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState) (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStageAll L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  intro s m hs
  rw [entryStageAll_eq L hw hn X Y kx ky s m hs.x hs.y hs.clean]
  exact entryRef_step L hw hn X Y kx ky G origin hx s m hs

theorem multiplyExitAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ParityXExitKernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (P++exitYAll L k) m s=run (P++ExitFusionResearch.exitY L k) m s := by
  let n:=measurementCount P
  let a:=run P (m.take n) s
  have hp:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have half:=correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have ac:regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq=>half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av:regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  rw [run_append,run_append]
  exact exitYAll_eq L hw hn ((Y*X)/2) k a (m.drop n) (m.drop n) av ac

theorem multiplyExitAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ParityXExitKernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++exitYAll L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m hs
  rw [multiplyExitAll_eq L hw hn P cx correct X Y k G origin hX s m hs]
  exact ParityXExitKernel.fusedMultiplyX_step L hw hn P cx correct X Y k G origin hX s m hs

def secondStageAll (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  ReflectionE1TickGapLow48.squareEntry L k++ParityXExitKernel.restXX L cx.val++exitYAll L cy

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
open ReflectionE1TickGapLow48
theorem secondStageAll_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageAll L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=multiplyExitAll_step L hw hn
    (FrontierEntry1591Callers.exit (ParityXExitKernel.kernelX cx.val) L) cx
    (ParityXExitKernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageAll,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ParityXExitKernel.restXX L cx.val++exitYAll L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ParityXExitKernel.exit_splitX,List.append_assoc,Z] using prior

end

def genericAll (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStageAll L (-cx) (-cy)++secondStageAll L (ReflectionE1.correction cx) cy cx

def genericRef (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryRef L (-cx) (-cy)++ReflectionE1TickGapLow48.secondStageX L (ReflectionE1.correction cx) cy cx

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (genericAll L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageAll_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (genericAll L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageAll_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second



end


theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+4=toffoliCount (genericRef L cx cy) ∧
    measurementCount (genericAll L cx cy)=measurementCount (genericRef L cx cy) ∧
    gateSlots (genericAll L cx cy)≤gateSlots (genericRef L cx cy) := by
  have r:=ParityXExitKernel.restXX_delta L cx.val
  have x:=entryXAll_counts L (-cx)
  have a:=entryYAll_counts L hw (-cy)
  have aa:=fusedY_counts L hw (-cy)
  have b:=exitYAll_counts L hw cy
  have bb:=ExitFusionResearch.exitY_counts L hw cy
  simp only [genericAll,genericRef,entryStageAll,entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem generic_toffoli (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+4=toffoliCount (genericRef L cx cy) := by
  have h:=generic_counts L hw cx cy
  omega

theorem generic_wires (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (genericAll L cx cy)⊆wires (genericRef L cx cy) := by
  have r:=ParityXExitKernel.restXX_subset L cx.val
  have a:=entryYAll_wires L hw (-cy)
  have b:=exitYAll_wires L hw cy
  simp only [genericAll,genericRef,entryStageAll,entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union a (entryXAll_wires L (-cx))) (Finset.Subset.refl _))
    (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) r) b)

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp)
    (h : GatePhysical (genericRef L cx cy)) : GatePhysical (genericAll L cx cy) := by
  simp only [genericRef,entryRef,ReflectionE1TickGapLow48.secondStageX,gatePhysical_append] at h
  simp only [genericAll,entryStageAll,secondStageAll,gatePhysical_append]
  exact ⟨⟨⟨entryYAll_physical L hw hn (-cy),entryXAll_physical L hw hn (-cx)⟩,h.1.2⟩,
    ⟨⟨h.2.1.1,ParityXExitKernel.restXX_physical L hw hn cx.val⟩,exitYAll_physical L hw hn cy⟩⟩

end ECDSAAdd.Entrant.ParityStageXY
end


-- Consolidated source module: Main
section

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.

-- ===== merged module ECDSAAdd.Submission.Entrant.InputSentinel =====
namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- First bit below 256 where two words differ (0 when none). -/
def firstDiff (a b : Nat) : Nat :=
  ((List.range 256).find? (fun i => a.testBit i != b.testBit i)).getD 0

theorem firstDiff_spec (a b : Nat) (ha : a < 2^256) (hb : b < 2^256) (hne : a ≠ b) :
    firstDiff a b < 256 ∧ a.testBit (firstDiff a b) ≠ b.testBit (firstDiff a b) := by
  have ex : ∃ i ∈ List.range 256, (a.testBit i != b.testBit i) = true := by
    by_contra h
    push_neg at h
    apply hne
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 256
    · have := h i (List.mem_range.mpr hi)
      simpa using this
    · have h1 : a.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h2 : b.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [h1, h2]
  obtain ⟨j, hj, hjp⟩ := ex
  have hs : ((List.range 256).find? (fun i => a.testBit i != b.testBit i)).isSome := by
    rw [List.find?_isSome]; exact ⟨j, hj, hjp⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  have hkm := List.mem_of_find?_eq_some hk
  have hkp := List.find?_some hk
  have hfd : firstDiff a b = k := by simp [firstDiff, hk]
  rw [hfd]
  exact ⟨List.mem_range.mp hkm, by simpa using hkp⟩

/-- The three words the input stage compares `x` with: `C.x`, `(-2C).x` and the sentinel. -/
structure Tri where
  A : Nat
  B : Nat
  S : Nat

namespace Tri
variable (t : Tri)

/-- First pivot: a bit separating `B` from `S`. -/
def r1 : Nat := firstDiff t.B t.S
/-- Role 1: `A` agrees with `S` at the first pivot (otherwise it agrees with `B`). -/
def role1 : Bool := t.A.testBit t.r1 == t.S.testBit t.r1
/-- Second pivot: separates `A` from the word it agrees with at `r1`. -/
def r2 : Nat := if t.role1 then firstDiff t.A t.S else firstDiff t.A t.B

def pat (K : Nat) : Bool × Bool := (K.testBit t.r1, K.testBit t.r2)

/-- Target bit `i` at pivot pattern `p`: the matching word's bit, else the affine completion. -/
def tgt (i : Nat) (p : Bool × Bool) : Bool :=
  if p = t.pat t.A then t.A.testBit i
  else if p = t.pat t.B then t.B.testBit i
  else if p = t.pat t.S then t.S.testBit i
  else t.A.testBit i ^^ t.B.testBit i ^^ t.S.testBit i

structure Valid : Prop where
  hA : t.A < 2^256
  hB : t.B < 2^256
  hS : t.S < 2^256
  AB : t.A ≠ t.B
  AS : t.A ≠ t.S
  BS : t.B ≠ t.S

variable {t}

theorem pivots (v : t.Valid) :
    t.r1 < 256 ∧ t.r2 < 256 ∧ t.r1 ≠ t.r2 ∧
      t.pat t.A ≠ t.pat t.B ∧ t.pat t.A ≠ t.pat t.S ∧ t.pat t.B ≠ t.pat t.S := by
  have h1 := firstDiff_spec t.B t.S v.hB v.hS v.BS
  have hAS := firstDiff_spec t.A t.S v.hA v.hS v.AS
  have hAB := firstDiff_spec t.A t.B v.hA v.hB v.AB
  have er1 : t.r1 = firstDiff t.B t.S := rfl
  by_cases ro : t.role1 = true
  · have er2 : t.r2 = firstDiff t.A t.S := by simp [r2, ro]
    have eq1 : t.A.testBit t.r1 = t.S.testBit t.r1 := by simpa [role1] using ro
    have ne : t.r1 ≠ t.r2 := by
      intro e; rw [er2] at e; rw [e] at eq1; exact hAS.2 eq1
    refine ⟨h1.1, er2 ▸ hAS.1, ne, ?_, ?_, ?_⟩
    · intro e; have := congrArg Prod.fst e; simp only [pat] at this
      exact h1.2 (by rw [← er1, ← this, eq1])
    · intro e; have := congrArg Prod.snd e; simp only [pat] at this
      exact hAS.2 (by rw [er2] at this; exact this)
    · intro e; have := congrArg Prod.fst e; simp only [pat] at this
      exact h1.2 (by rw [← er1]; exact this)
  · have er2 : t.r2 = firstDiff t.A t.B := by simp [r2, ro]
    have ne1 : t.A.testBit t.r1 ≠ t.S.testBit t.r1 := by simpa [role1] using ro
    have eq1 : t.A.testBit t.r1 = t.B.testBit t.r1 := by
      have hb := h1.2; rw [← er1] at hb
      cases hA : t.A.testBit t.r1 <;> cases hB' : t.B.testBit t.r1 <;> cases hS' : t.S.testBit t.r1 <;>
        simp_all
    have ne : t.r1 ≠ t.r2 := by
      intro e; rw [er2] at e; rw [e] at eq1; exact hAB.2 eq1
    refine ⟨h1.1, er2 ▸ hAB.1, ne, ?_, ?_, ?_⟩
    · intro e; have := congrArg Prod.snd e; simp only [pat] at this
      exact hAB.2 (by rw [er2] at this; exact this)
    · intro e; have := congrArg Prod.fst e; simp only [pat] at this
      exact ne1 this
    · intro e; have := congrArg Prod.fst e; simp only [pat] at this
      exact h1.2 (by rw [← er1]; exact this)

private theorem affine4 : ∀ (pA pB pS : Bool × Bool) (a b c : Bool),
    pA ≠ pB → pA ≠ pS → pB ≠ pS →
    let f := fun p : Bool × Bool => if p = pA then a else if p = pB then b else if p = pS then c
      else a ^^ b ^^ c
    f (true, true) = (f (true, false) ^^ f (false, true) ^^ f (false, false)) := by
  decide

theorem tgt_affine (v : t.Valid) (i : Nat) :
    t.tgt i (true, true) = (t.tgt i (true, false) ^^ t.tgt i (false, true) ^^ t.tgt i (false, false)) := by
  have pv := pivots v
  exact affine4 _ _ _ _ _ _ pv.2.2.2.1 pv.2.2.2.2.1 pv.2.2.2.2.2

theorem tgt_A (i : Nat) : t.tgt i (t.pat t.A) = t.A.testBit i := by simp [tgt]
theorem tgt_B (v : t.Valid) (i : Nat) : t.tgt i (t.pat t.B) = t.B.testBit i := by
  have pv := pivots v; simp [tgt, Ne.symm pv.2.2.2.1]
theorem tgt_S (v : t.Valid) (i : Nat) : t.tgt i (t.pat t.S) = t.S.testBit i := by
  have pv := pivots v; simp [tgt, Ne.symm pv.2.2.2.2.1, Ne.symm pv.2.2.2.2.2]

/-- Bits other than the two pivots. -/
def idx : List Nat := (List.range 256).filter (fun i => i ≠ t.r1 ∧ i ≠ t.r2)

/-- A zero test on the remapped non-pivot bits plus a pivot pattern identifies the word. -/
theorem match_iff (v : t.Valid) (X K : Nat) (hX : X < 2^256) (hK : K < 2^256)
    (hKt : ∀ i, t.tgt i (t.pat K) = K.testBit i) :
    ((∀ i ∈ t.idx, X.testBit i = t.tgt i (t.pat X)) ∧ t.pat X = t.pat K) ↔ X = K := by
  have pv := pivots v
  constructor
  · rintro ⟨hall, hp⟩
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 256
    · by_cases h1 : i = t.r1
      · subst h1; exact congrArg Prod.fst hp
      by_cases h2 : i = t.r2
      · subst h2; exact congrArg Prod.snd hp
      have hm : i ∈ t.idx := by simp [idx, hi, h1, h2]
      rw [hall i hm, hp, hKt]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · rintro rfl
    exact ⟨fun i _ => (hKt i).symm, rfl⟩

end Tri

namespace Tri
variable (t : Tri)

/-- Per-bit remap: XOR the target bit of the current pivot pattern into wire `w`. -/
def remapBit (xr1 xr2 w : Wire) (i : Nat) : Program :=
  (if t.tgt i (false, false) then [.X w] else []) ++
  ((if (t.tgt i (true, false) ^^ t.tgt i (false, false)) then [.CX xr1 w] else []) ++
  (if (t.tgt i (false, true) ^^ t.tgt i (false, false)) then [.CX xr2 w] else []))

def remapList (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) : Program :=
  l.flatMap (fun i => t.remapBit xr1 xr2 (w i) i)

variable {t}

theorem remapBit_run (v : t.Valid) (xr1 xr2 w : Wire) (i : Nat) (h1 : w ≠ xr1) (h2 : w ≠ xr2)
    (m : List Bool) (s : State) :
    run (t.remapBit xr1 xr2 w i) m s =
      ⟨s.phase, writeBit s.basis w (s.basis w ^^ t.tgt i (s.basis xr1, s.basis xr2))⟩ := by
  have aff := tgt_affine v i
  have key : t.tgt i (s.basis xr1, s.basis xr2) =
      (t.tgt i (false, false) ^^ (s.basis xr1 && (t.tgt i (true, false) ^^ t.tgt i (false, false))) ^^
        (s.basis xr2 && (t.tgt i (false, true) ^^ t.tgt i (false, false)))) := by
    have gen : ∀ x1 x2 : Bool, t.tgt i (x1, x2) =
        (t.tgt i (false, false) ^^ (x1 && (t.tgt i (true, false) ^^ t.tgt i (false, false))) ^^
          (x2 && (t.tgt i (false, true) ^^ t.tgt i (false, false)))) := by
      intro x1 x2
      cases x1 <;> cases x2 <;>
      (revert aff
       generalize t.tgt i (true, true) = d
       generalize t.tgt i (false, false) = a
       generalize t.tgt i (true, false) = b
       generalize t.tgt i (false, true) = c
       intro aff; subst aff
       cases a <;> cases b <;> cases c <;> rfl)
    exact gen _ _
  rw [key]
  clear key aff
  unfold remapBit
  generalize t.tgt i (false, false) = a
  generalize t.tgt i (true, false) = b
  generalize t.tgt i (false, true) = c
  obtain ⟨ph, bs⟩ := s
  have w1 : xr1 ≠ w := Ne.symm h1
  have w2 : xr2 ≠ w := Ne.symm h2
  cases a <;> cases b <;> cases c <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true,
      if_false, List.nil_append, List.append_nil, List.cons_append, List.singleton_append] <;>
    simp only [run] <;> congr 1 <;> funext q <;> by_cases hq : q = w <;>
    simp [writeBit, Function.update, hq, w1, w2, Bool.and_false, Bool.and_true, Bool.xor_false,
      Bool.false_xor, Bool.xor_true, Bool.true_xor]

theorem remapList_run (v : t.Valid) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat)
    (hnd : (l.map w).Nodup) (h1 : xr1 ∉ l.map w) (h2 : xr2 ∉ l.map w) (m : List Bool) (s : State) :
    (run (t.remapList xr1 xr2 w l) m s).phase = s.phase ∧
    (∀ q, q ∉ l.map w → (run (t.remapList xr1 xr2 w l) m s).basis q = s.basis q) ∧
    (∀ i ∈ l, (run (t.remapList xr1 xr2 w l) m s).basis (w i) =
      (s.basis (w i) ^^ t.tgt i (s.basis xr1, s.basis xr2))) := by
  induction l generalizing s m with
  | nil => simp [remapList, run]
  | cons i l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd h1 h2
    have hw1 : w i ≠ xr1 := fun e => h1.1 e.symm
    have hw2 : w i ≠ xr2 := fun e => h2.1 e.symm
    have e : t.remapList xr1 xr2 w (i :: l) = t.remapBit xr1 xr2 (w i) i ++ t.remapList xr1 xr2 w l := by
      simp [remapList]
    rw [e, run_append, remapBit_run v xr1 xr2 (w i) i hw1 hw2]
    set s1 : State := ⟨s.phase, writeBit s.basis (w i) (s.basis (w i) ^^ t.tgt i (s.basis xr1, s.basis xr2))⟩
    have ih1 := ih hnd.2 h1.2 h2.2 (m.drop (measurementCount (t.remapBit xr1 xr2 (w i) i))) s1
    have k1 : s1.basis xr1 = s.basis xr1 := by simp [s1, writeBit, Function.update, Ne.symm hw1]
    have k2 : s1.basis xr2 = s.basis xr2 := by simp [s1, writeBit, Function.update, Ne.symm hw2]
    refine ⟨ih1.1, ?_, ?_⟩
    · intro q hq
      simp only [List.map_cons, List.mem_cons, not_or] at hq
      rw [ih1.2.1 q hq.2]
      simp [s1, writeBit, Function.update, hq.1]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [ih1.2.1 (w j) hnd.1]
        simp [s1, writeBit]
      · rw [ih1.2.2 j hj, k1, k2]
        have hne : w j ≠ w i := fun e => hnd.1 (e ▸ List.mem_map_of_mem hj)
        simp [s1, writeBit, Function.update, hne]

end Tri



/-- `[q = v]` frame: flip `q` when the tested value is `false`. -/
def lit (q : Wire) (v : Bool) : Program := if v then [] else [.X q]

/-! Decode tail on local wires: 0 `h` (zero-test result), 1 `x_r1`, 2 `x_r2`, 3 `y0`, 4 control,
5 finite flag, 6 generic select, 7–9 clean scratch. -/

def decodeCore : Program :=
  [.CX 1 0,
   .CX 2 0,
   .CX 3 0,
   .CX 5 0,
   .CCX 0 4 7,
   .CX 5 0,
   .CX 3 0,
   .CX 4 0,
   .CX 5 0,
   .CX 7 0,
   .CX 7 1,
   .CCX 0 1 8,
   .CX 7 1,
   .CX 7 0,
   .CX 5 0,
   .CX 4 0,
   .CX 2 0,
   .CX 1 0,
   .CX 8 7,
   .CX 7 0,
   .CCX 7 0 9,
   .CX 7 0,
   .CX 8 7,
   .CX 4 6,
   .CX 7 6,
   .CX 8 6,
   .CX 9 6,
   .measureX 7 [] [.Z 4, .Z 6, .Z 8, .Z 9],
   .CX 5 8,
   .CX 5 9,
   .measureX 5 [] [.CZ 0 9],
   .CX 8 9,
   .measureX 8 [] [.Z 1, .Z 4, .Z 6, .CZ 0 1, .CZ 0 4, .CZ 1 2, .CZ 1 9, .CZ 2 6, .CZ 3 6, .CZ 3 9],
   .measureX 9 [] [.CZ 0 4, .CZ 1 6, .CZ 2 6, .CZ 3 4]]

/-- Map the two pivot bits to the affine indicators of {A,S} and {B,S}. -/
def decode1 (a1 a2 b2 yb : Bool) : Program :=
  let frame := lit 1 a1 ++ lit 2 b2 ++ (if a2 == b2 then [.CX 1 2] else []) ++ lit 3 yb
  frame ++ [.X 5] ++ decodeCore ++ frame.reverse

def decode2 (b1 a2 s2 yb : Bool) : Program :=
  let frame := lit 1 b1 ++ lit 2 s2 ++ (if a2 == s2 then [.CX 1 2] else []) ++ [.CX 2 1] ++ lit 3 yb
  frame ++ [.X 5] ++ decodeCore ++ frame.reverse

/-- The generic flag produced by role 1 from the zero-test bit and the pivot bits. -/
def gen1 (a1 b2 yb : Bool) (x : Nat) : Bool :=
  x.testBit 4 && !((x.testBit 0 && (x.testBit 1 == a1)) ||
    (x.testBit 0 && (x.testBit 1 != a1) && (x.testBit 2 == b2) && (x.testBit 3 == yb)))

def gen2 (b1 a2 yb : Bool) (x : Nat) : Bool :=
  let g1 := x.testBit 0 && (x.testBit 1 == b1)
  x.testBit 4 && (x.testBit 5 ^^ (g1 && (x.testBit 2 == a2)) ^^
    (g1 && (x.testBit 2 != a2) && (x.testBit 3 == yb)))

/-- Output word: finite flag cleared, generic select toggled by `gv`. -/
def out (x : Nat) (gv : Bool) : Nat :=
  x ^^^ (if x.testBit 5 then 32 else 0) ^^^ (if gv then 64 else 0)

def pre1 (a1 a2 : Bool) (x : Nat) : Bool :=
  x.testBit 5 == !(x.testBit 0 && (x.testBit 1 == a1) && (x.testBit 2 == !a2))

def pre2 (b1 s2 : Bool) (x : Nat) : Bool :=
  x.testBit 5 == !(x.testBit 0 && (x.testBit 1 != b1) && (x.testBit 2 == s2))

theorem decode1_ok : ∀ a1 a2 b2 yb : Bool, ∀ x : Fin 128, pre1 a1 a2 x.val = true → x.val.testBit 6 = false →
    safe (decode1 a1 a2 b2 yb) x.val = true ∧
      bitRun (decode1 a1 a2 b2 yb) x.val = out x.val (gen1 a1 b2 yb x.val) := by
  decide +kernel

theorem decode2_ok : ∀ b1 a2 s2 yb : Bool, ∀ x : Fin 128, pre2 b1 s2 x.val = true → x.val.testBit 6 = false →
    safe (decode2 b1 a2 s2 yb) x.val = true ∧
      bitRun (decode2 b1 a2 s2 yb) x.val = out x.val (gen2 b1 a2 yb x.val) := by
  decide +kernel

theorem decode_counts (a1 a2 b2 yb : Bool) :
    toffoliCount (decode1 a1 a2 b2 yb) = 3 ∧ measurementCount (decode1 a1 a2 b2 yb) = 4 ∧
    toffoliCount (decode2 a1 a2 b2 yb) = 3 ∧ measurementCount (decode2 a1 a2 b2 yb) = 4 := by
  cases a1 <;> cases a2 <;> cases b2 <;> cases yb <;> decide


/-- A safe local program on wires `0..n-1` lifts through an injective port map: the ports end
with the bits of its classical simulation, every other wire is untouched, and the phase is kept. -/
theorem lift_local (n : Nat) (p : Fin n → Wire) (hp : Function.Injective p) (D : Program)
    (hD : wires D ⊆ Finset.range n) (s : State) (m : List Bool) (x : Nat)
    (hx : ∀ q (h : q < n), s.basis (p ⟨q, h⟩) = x.testBit q) (hsafe : safe D x = true) :
    (run (renameProgram (LocalWireModel.label p) D) m s).phase = s.phase ∧
    (∀ q (h : q < n), (run (renameProgram (LocalWireModel.label p) D) m s).basis (p ⟨q, h⟩) =
      (bitRun D x).testBit q) ∧
    (∀ w, (∀ q (h : q < n), w ≠ p ⟨q, h⟩) →
      (run (renameProgram (LocalWireModel.label p) D) m s).basis w = s.basis w) := by
  let t : State := ⟨s.phase, fun q => s.basis (LocalWireModel.label p q)⟩
  have rr := run_rename_pool (LocalWireModel.label p) (Finset.range n)
    (LocalWireModel.label_injective p hp) D hD m t s rfl (fun _ _ => rfl)
  have lab (q : Nat) (h : q < n) : LocalWireModel.label p q = p ⟨q, h⟩ := by
    simp [LocalWireModel.label, h]
  have agree := pool_run_agrees D (Finset.range n) hD m t ⟨s.phase, bitsOf x⟩ rfl (by
    intro q hq
    have h := Finset.mem_range.mp hq
    change s.basis (LocalWireModel.label p q) = x.testBit q
    rw [lab q h, hx q h])
  have sim := run_sim D m s.phase x
  rw [sim_safe D x hsafe m s.phase] at sim
  refine ⟨?_, ?_, ?_⟩
  · rw [rr.1, agree.1, sim]
  · intro q h
    have e := rr.2 q (Finset.mem_range.mpr h)
    rw [lab q h] at e
    rw [e, agree.2 q (Finset.mem_range.mpr h), sim]
    rfl
  · intro w hw
    apply run_rename_pool_outside _ _ D hD m s w
    intro hm
    obtain ⟨q, hq, eq⟩ := Finset.mem_image.mp hm
    have h := Finset.mem_range.mp hq
    exact hw q h (by rw [← lab q h]; exact eq.symm)

theorem out_bit (x : Nat) (gv : Bool) (q : Nat) :
    (out x gv).testBit q = (if q = 5 then false else if q = 6 then (x.testBit 6 ^^ gv) else x.testBit q) := by
  unfold out
  rw [Nat.testBit_xor, Nat.testBit_xor]
  have e1 : Nat.testBit 32 5 = true := by decide
  have e2 : Nat.testBit 64 5 = false := by decide
  have e3 : Nat.testBit 32 6 = false := by decide
  have e4 : Nat.testBit 64 6 = true := by decide
  by_cases h5 : q = 5
  · subst h5; cases hx : x.testBit 5 <;> cases gv <;> simp [hx, e1, e2]
  · by_cases h6 : q = 6
    · subst h6; cases hx : x.testBit 5 <;> cases gv <;> cases x.testBit 6 <;> simp [hx, e3, e4]
    · have a : (if x.testBit 5 then 32 else 0 : Nat).testBit q = false := by
        split_ifs
        · rw [show (32:Nat) = 2^5 by norm_num, Nat.testBit_two_pow]; simp [Ne.symm h5]
        · simp
      have b : (if gv then 64 else 0 : Nat).testBit q = false := by
        split_ifs
        · rw [show (64:Nat) = 2^6 by norm_num, Nat.testBit_two_pow]; simp [Ne.symm h6]
        · simp
      rw [a, b]; simp [h5, h6]

/-- The decode tail for the word triple's pivot role. -/
def decodeT (tr : Tri) (yb : Bool) : Program :=
  if tr.role1 then decode1 (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) (tr.B.testBit tr.r2) yb
  else decode2 (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) (tr.S.testBit tr.r2) yb

/-- Generic flag toggle produced by the tail from the zero-test bit and the read bits. -/
def genOut (tr : Tri) (yb v x1 x2 y c f : Bool) : Bool :=
  if tr.role1 then
    c && !((v && (x1 == tr.A.testBit tr.r1)) ||
      (v && (x1 != tr.A.testBit tr.r1) && (x2 == tr.B.testBit tr.r2) && (y == yb)))
  else
    c && (f ^^ ((v && (x1 == tr.A.testBit tr.r1)) && (x2 == tr.A.testBit tr.r2)) ^^
      ((v && (x1 == tr.A.testBit tr.r1)) && (x2 != tr.A.testBit tr.r2) && (y == yb)))

theorem decodeT_support (tr : Tri) (yb : Bool) : wires (decodeT tr yb) ⊆ Finset.range 10 := by
  unfold decodeT
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.A.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c; generalize tr.S.testBit tr.r2 = d
    cases a <;> cases b <;> cases c <;> cases d <;> cases yb <;> decide

theorem tail_run (tr : Tri) (v : tr.Valid) (yb : Bool) (h xr1 xr2 y0 c f g g1 wB t : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, g1, wB, t].Nodup) (s : State) (m : List Bool)
    (hg : s.basis g = false)
    (hz : s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(s.basis h && decide ((s.basis xr1, s.basis xr2) = tr.pat tr.S))) :
    run (renameProgram (LocalWireModel.label
        (fun q : Fin 10 => [h, xr1, xr2, y0, c, f, g, g1, wB, t].getD q.val 0)) (decodeT tr yb)) m s =
      ⟨s.phase, writeBit (writeBit s.basis f false) g (s.basis g ^^
        genOut tr yb (s.basis h) (s.basis xr1) (s.basis xr2) (s.basis y0) (s.basis c) (s.basis f))⟩ := by
  have hfg : f ≠ g := by intro e; subst e; simp at hnd
  set r : List Wire := [h, xr1, xr2, y0, c, f, g, g1, wB, t] with hr
  have pv := Tri.pivots v
  let x : Nat := regValue r s.basis
  have hx : ∀ q (hq : q < 10), s.basis (r.getD q 0) = x.testBit q := by
    intro q hq
    exact (LocalWireModel.reg_bit r s.basis q (by simpa [hr] using hq)).symm
  have hb (q : Nat) (hq : q < 10) : x.testBit q = s.basis (r.getD q 0) := (hx q hq).symm
  have x7 : x < 2^7 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases h10 : i < 10
    · interval_cases i
      · rw [hb 7 (by decide)]; simpa [hr] using hz.1
      · rw [hb 8 (by decide)]; simpa [hr] using hz.2.1
      · rw [hb 9 (by decide)]; simpa [hr] using hz.2.2
    · have hl : x < 2^10 := by simpa [x, hr] using regValue_lt r s.basis
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hl (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have bits : x.testBit 0 = s.basis h ∧ x.testBit 1 = s.basis xr1 ∧ x.testBit 2 = s.basis xr2 ∧
      x.testBit 3 = s.basis y0 ∧ x.testBit 4 = s.basis c ∧ x.testBit 5 = s.basis f ∧
      x.testBit 6 = s.basis g := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (rw [hb 0 (by decide)]; simp [hr]) | (rw [hb 1 (by decide)]; simp [hr])
      | (rw [hb 2 (by decide)]; simp [hr]) | (rw [hb 3 (by decide)]; simp [hr])
      | (rw [hb 4 (by decide)]; simp [hr]) | (rw [hb 5 (by decide)]; simp [hr])
      | (rw [hb 6 (by decide)]; simp [hr])
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := bits
  have inj := LocalWireModel.listPorts_injective r hnd (n := 10) (by simp [hr])
  -- the classical check for this role
  have core : safe (decodeT tr yb) x = true ∧ bitRun (decodeT tr yb) x =
      out x (genOut tr yb (s.basis h) (s.basis xr1) (s.basis xr2) (s.basis y0) (s.basis c) (s.basis f)) := by
    unfold decodeT genOut
    by_cases ro : tr.role1 = true
    · have eq1 : tr.A.testBit tr.r1 = tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
      have neS : tr.S.testBit tr.r2 = !tr.A.testBit tr.r2 := by
        have er2 : tr.r2 = firstDiff tr.A tr.S := by simp [Tri.r2, ro]
        have d := (firstDiff_spec tr.A tr.S v.hA v.hS v.AS).2
        rw [← er2] at d
        cases hA : tr.A.testBit tr.r2 <;> cases hS : tr.S.testBit tr.r2 <;> simp_all
      have pre : pre1 (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) x = true := by
        simp only [pre1, b0, b1, b2, b5, hf, Tri.pat, eq1, neS, Prod.mk.injEq]
        cases s.basis h <;> cases s.basis xr1 <;> cases s.basis xr2 <;>
          cases tr.S.testBit tr.r1 <;> cases tr.A.testBit tr.r2 <;> decide
      have k := decode1_ok (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) (tr.B.testBit tr.r2) yb ⟨x, x7⟩ pre (b6.trans hg)
      simp only [ro, if_true]
      refine ⟨k.1, ?_⟩
      rw [k.2]
      congr 1
      simp only [gen1, b0, b1, b2, b3, b4]
    · have ro' : tr.role1 = false := by simpa using ro
      have ne1 : tr.S.testBit tr.r1 = !tr.A.testBit tr.r1 := by
        have : tr.A.testBit tr.r1 ≠ tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
        cases hA : tr.A.testBit tr.r1 <;> cases hS : tr.S.testBit tr.r1 <;> simp_all
      have pre : pre2 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) x = true := by
        simp only [pre2, b0, b1, b2, b5, hf, Tri.pat, ne1, Prod.mk.injEq]
        cases s.basis h <;> cases s.basis xr1 <;> cases s.basis xr2 <;>
          cases tr.A.testBit tr.r1 <;> cases tr.S.testBit tr.r2 <;> decide
      have k := decode2_ok (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) (tr.S.testBit tr.r2) yb ⟨x, x7⟩ pre (b6.trans hg)
      simp only [ro', Bool.false_eq_true, if_false]
      refine ⟨k.1, ?_⟩
      rw [k.2]
      congr 1
      simp only [gen2, b0, b1, b2, b3, b4, b5]
  have L := lift_local 10 _ inj (decodeT tr yb) (decodeT_support tr yb) s m x hx core.1
  rw [core.2] at L
  apply State.extensionality
  · exact L.1
  · funext w
    have port (q : Nat) (hq : q < 10) := L.2.1 q hq
    simp only [out_bit] at port
    by_cases wf : w = f
    · subst wf
      have := port 5 (by decide)
      simpa [hr, writeBit, Function.update, hfg] using this
    by_cases wg : w = g
    · subst wg
      have e6 : w = r.getD 6 0 := by simp [hr]
      conv_lhs => rw [e6]
      rw [port 6 (by decide)]
      simp [writeBit, Function.update, b6, ← e6]
    by_cases wr : w ∈ r
    · obtain ⟨q, hq, hqw⟩ : ∃ q, q < 10 ∧ r.getD q 0 = w := by
        obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem wr
        exact ⟨i, by simpa [hr] using hi, by rw [List.getD_eq_getElem _ _ hi]; exact hiw⟩
      have pq := port q hq
      have q5 : q ≠ 5 := by intro e; subst e; apply wf; rw [← hqw]; simp [hr]
      have q6 : q ≠ 6 := by intro e; subst e; apply wg; rw [← hqw]; simp [hr]
      simp only [q5, q6, if_false] at pq
      change (run _ m s).basis (r.getD q 0) = _ at pq
      rw [hqw] at pq
      rw [pq, hb q hq, hqw]
      simp [writeBit, Function.update, wf, wg]
    · rw [L.2.2 w (by
        intro q hq e
        apply wr
        rw [e]
        have hq' : q < r.length := by simpa [hr] using hq
        rw [List.getD_eq_getElem _ _ hq']
        exact List.getElem_mem hq')]
      simp [writeBit, Function.update, wf, wg]

/-- The tail on the chain's last work wire `h`. -/
def tail (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t : Wire) (h : Wire) : Program :=
  renameProgram (LocalWireModel.label
    (fun q : Fin 10 => [h, xr1, xr2, y0, c, f, g, g1, wB, t].getD q.val 0)) (decodeT tr yb)

/-- Tail precondition: clean scratch and the finite flag is the negated sentinel match. -/
def tailPre (tr : Tri) (xr1 xr2 f g g1 wB t : Wire) (u : Bool) (st : BasisState) : Prop :=
  st g1 = false ∧ st wB = false ∧ st t = false ∧
    st g = false ∧ st f = !(u && decide ((st xr1, st xr2) = tr.pat tr.S))

/-- Tail effect: the finite flag is cleared and the generic select is toggled. -/
def tailEff (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g : Wire) (u : Bool) (st : BasisState) : BasisState :=
  writeBit (writeBit st f false) g
    (st g ^^ genOut tr yb u (st xr1) (st xr2) (st y0) (st c) (st f))

theorem chain_run (tr : Tri) (v : tr.Valid) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t : Wire)
    (hused : [xr1, xr2, y0, c, f, g, g1, wB, t].Nodup)
    (c0 : Wire) (bs : List ZeroBit) (hcu : c0 ∉ [xr1, xr2, y0, c, f, g, g1, wB, t])
    (hnd : (c0 :: bs.flatMap ZeroBit.wires).Nodup)
    (hdis : ∀ b ∈ bs, b.input ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, g1, wB, t])
    (s : State) (m : List Bool)
    (hs : tailPre tr xr1 xr2 f g g1 wB t (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis)
    (hz : ∀ b ∈ bs, s.basis b.work = false) :
    run (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) c0 bs) m s =
      ⟨s.phase, tailEff tr yb xr1 xr2 y0 c f g (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis⟩ := by
  set used : List Wire := [xr1, xr2, y0, c, f, g, g1, wB, t] with hu
  apply zeroWith_effect_runQ used (tailPre tr xr1 xr2 f g g1 wB t) (tailEff tr yb xr1 xr2 y0 c f g)
  · intro w hw u st z
    have h1 : w ≠ g1 := fun e => hw (by simp [hu, e])
    have h2 : w ≠ wB := fun e => hw (by simp [hu, e])
    have h3 : w ≠ t := fun e => hw (by simp [hu, e])
    have h4 : w ≠ f := fun e => hw (by simp [hu, e])
    have h5 : w ≠ xr1 := fun e => hw (by simp [hu, e])
    have h6 : w ≠ xr2 := fun e => hw (by simp [hu, e])
    have h7 : w ≠ g := fun e => hw (by simp [hu, e])
    simp [tailPre, Ne.symm h7, writeBit, Function.update, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
      Ne.symm h5, Ne.symm h6]
  · intro u st w hw
    have h4 : w ≠ f := fun e => hw (by simp [hu, e])
    have h7 : w ≠ g := fun e => hw (by simp [hu, e])
    simp [tailEff, writeBit, Function.update, h4, h7]
  · intro u st w z hw
    have hs' : ∀ q ∈ used, q ≠ w := fun q hq e => hw (e ▸ hq)
    have h4 : f ≠ w := hs' f (by simp [hu])
    have h7 : g ≠ w := hs' g (by simp [hu])
    have r1 : xr1 ≠ w := hs' xr1 (by simp [hu])
    have r2 : xr2 ≠ w := hs' xr2 (by simp [hu])
    have r3 : y0 ≠ w := hs' y0 (by simp [hu])
    have r4 : c ≠ w := hs' c (by simp [hu])
    unfold tailEff
    simp only [writeBit, Function.update_apply, r1, r2, r3, r4, h4, h7, if_false]
    funext q
    by_cases qg : q = g
    · subst qg; simp [Function.update, h7]
    · by_cases qf : q = f
      · subst qf; simp [Function.update, h4, qg]
      · by_cases qw : q = w
        · subst qw; simp [Function.update, qg, qf]
        · simp [Function.update, qg, qf, qw]
  · intro c' hc' st m' hp
    have hnd' : [c', xr1, xr2, y0, c, f, g, g1, wB, t].Nodup := List.nodup_cons.mpr ⟨hc', hused⟩
    exact tail_run tr v yb c' xr1 xr2 y0 c f g g1 wB t hnd' st m' hp.2.2.2.1 ⟨hp.1, hp.2.1, hp.2.2.1⟩ hp.2.2.2.2
  · exact hcu
  · exact hnd
  · exact hdis
  · exact hs
  · exact hz

namespace Tri
variable {t : Tri}

theorem idx_facts (v : t.Valid) :
    t.idx.Nodup ∧ t.idx.length = 254 ∧ t.r1 ∉ t.idx ∧ t.r2 ∉ t.idx ∧ ∀ i ∈ t.idx, i < 256 := by
  have pv := pivots v
  have hnd : t.idx.Nodup := (List.nodup_range).filter _
  refine ⟨hnd, ?_, by simp [idx], by simp [idx], fun i hi => by
    simp only [idx, List.mem_filter, List.mem_range] at hi; exact hi.1⟩
  have e : t.idx.toFinset = Finset.range 256 \ {t.r1, t.r2} := by
    ext i; simp only [idx, List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_sdiff,
      Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, decide_eq_true_eq]; tauto
  rw [← List.toFinset_card_of_nodup hnd, e, Finset.card_sdiff]
  have hsub : ({t.r1, t.r2} : Finset Nat) ∩ Finset.range 256 = {t.r1, t.r2} := by
    apply Finset.inter_eq_left.mpr
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_range.mpr pv.1
    · exact Finset.mem_range.mpr pv.2.1
  rw [hsub, Finset.card_range, Finset.card_pair pv.2.2.1]

end Tri

theorem remapList_mc (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) :
    measurementCount (tr.remapList xr1 xr2 w l) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, measurementCount_append] at ih ⊢
    rw [ih]
    simp only [Tri.remapBit, measurementCount_append]
    split_ifs <;> rfl

theorem tailEff_apply (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g : Wire) (hfg : f ≠ g) (u : Bool)
    (st : BasisState) (q : Wire) :
    tailEff tr yb xr1 xr2 y0 c f g u st q =
      if q = g then (st g ^^ genOut tr yb u (st xr1) (st xr2) (st y0) (st c) (st f))
      else if q = f then false else st q := by
  unfold tailEff
  by_cases hg : q = g
  · subst hg; simp [writeBit]
  · by_cases hf : q = f
    · subst hf; simp [writeBit, Function.update, hg]
    · simp [writeBit, Function.update, hg, hf]

theorem shape_run (tr : Tri) (v : tr.Valid) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t : Wire)
    (w : Nat → Wire) (i0 : Nat) (it : List Nat) (work : List Wire)
    (hPn : ((i0 :: it).map w).Nodup) (x1P : xr1 ∉ (i0 :: it).map w) (x2P : xr2 ∉ (i0 :: it).map w)
    (hused : [xr1, xr2, y0, c, f, g, g1, wB, t].Nodup)
    (hextP : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w)
    (hwl : (it.map w).length = work.length) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, g1, wB, t])
    (s : State) (m : List Bool)
    (hg : s.basis g = false)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) &&
      decide ((s.basis xr1, s.basis xr2) = tr.pat tr.S))) :
    run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s =
      ⟨s.phase, tailEff tr yb xr1 xr2 y0 c f g
        ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis⟩ := by
  have hlw : (i0 :: it).map w = w i0 :: it.map w := rfl
  have p0l : w i0 ∈ (i0 :: it).map w := by simp
  have usedNotP : ∀ q ∈ [xr1, xr2, y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | hq
    · exact x1P
    · exact x2P
    · exact hextP q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have itNe : ∀ i ∈ it, w i ≠ w i0 := by
    intro i hi e
    rw [hlw] at hPn
    exact (List.nodup_cons.mp hPn).1 (e ▸ List.mem_map_of_mem hi)
  -- step 1: remap
  have R1 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P m s
  rw [LocalWireModel.run_concat, remapList_mc, List.drop_zero, LocalWireModel.run_concat]
  generalize hs1 : run (tr.remapList xr1 xr2 w (i0 :: it)) m s = s1 at R1 ⊢
  -- step 2: X p0
  have e2 : run [Instr.X (w i0)] m s1 = ⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ := by
    simp [run]
  rw [e2]
  generalize hs2 : (⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ : State) = s2
  have s2ph : s2.phase = s.phase := by rw [← hs2]; exact R1.1
  have s2out : ∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q := by
    intro q hq
    have hq0 : q ≠ w i0 := fun e => hq (e ▸ p0l)
    rw [← hs2]; simp [writeBit, Function.update, hq0, R1.2.1 q hq]
  have s2p0 : s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) := by
    rw [← hs2]; simp only [writeBit, Function.update_self]
    rw [R1.2.2 i0 (by simp)]
    cases s.basis (w i0) <;> cases tr.tgt i0 (s.basis xr1, s.basis xr2) <;> rfl
  have s2it : ∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2)) := by
    intro i hi
    rw [← hs2]; simp only [writeBit]
    rw [Function.update_of_ne (itNe i hi), R1.2.2 i (by simp [hi])]
  have k1 : s2.basis xr1 = s.basis xr1 := s2out xr1 x1P
  have k2 : s2.basis xr2 = s.basis xr2 := s2out xr2 x2P
  -- the zero-test value equals the match bit
  have zp := zeroPorts_maps (it.map w) work hwl
  have huV : (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    have hall : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
        it.all (fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
      have : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
          ((zeroPorts (it.map w) work).map ZeroBit.input).all (fun q => !s2.basis q) := by
        rw [List.all_map]; rfl
      rw [this, zp.1, List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      apply forall₂_congr
      intro i hi
      simp only [Function.comp_apply, s2it i hi]
      cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> simp
    rw [hall, s2p0]
    simp [List.all_cons]
  -- step 3: the zero-test chain with the decode tail
  have hcu : w i0 ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := fun h => usedNotP _ h p0l
  have hperm := zeroPorts_perm (it.map w) work hwl
  have hnd : (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp (hperm.mem_iff.mp hm) with h | h
      · obtain ⟨i, hi, e⟩ := List.mem_map.mp h
        exact itNe i hi e
      · exact (hdisj _ h).1 p0l
    · apply hperm.symm.nodup_iff.mp
      apply List.nodup_append.mpr
      refine ⟨(List.nodup_cons.mp (hlw ▸ hPn)).2, hwn, ?_⟩
      intro a ha b hb e
      subst e
      exact (hdisj a hb).1 (by rw [hlw]; exact List.mem_cons_of_mem _ ha)
  have hfg : f ≠ g := by
    intro e; rw [e] at hused; simp at hused
  have hdis' : ∀ b ∈ zeroPorts (it.map w) work, b.input ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := by
    intro b hb
    have hin : b.input ∈ it.map w := by
      have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    exact ⟨fun h => usedNotP _ h (by rw [hlw]; exact List.mem_cons_of_mem _ hin), (hdisj _ hwk).2⟩
  have hs3 : tailPre tr xr1 xr2 f g g1 wB t
      (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) s2.basis := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [s2out g1 (usedNotP g1 (by simp))]; exact hz.2.1
    · rw [s2out wB (usedNotP wB (by simp))]; exact hz.2.2.1
    · rw [s2out t (usedNotP t (by simp))]; exact hz.2.2.2
    · rw [s2out g (usedNotP g (by simp))]; exact hg
    · rw [s2out f (usedNotP f (by simp)), huV, k1, k2]; exact hf
  have hz3 : ∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false := by
    intro b hb
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    rw [s2out _ (hdisj _ hwk).1]; exact hz.1 _ hwk
  rw [LocalWireModel.run_concat, chain_run tr v yb xr1 xr2 y0 c f g g1 wB t hused (w i0) _ hcu hnd hdis'
    s2 _ hs3 hz3, huV, LocalWireModel.run_concat]
  set V := (i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2) with hV
  set T3 := tailEff tr yb xr1 xr2 y0 c f g V s2.basis with hT3
  have e4 : ∀ mm, run [Instr.X (w i0)] mm ⟨s2.phase, T3⟩ = ⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ := by
    intro mm; simp [run]
  rw [e4]
  generalize hs4 : (⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ : State) = s4
  have T3out : ∀ q, q ∉ (i0 :: it).map w → T3 q = tailEff tr yb xr1 xr2 y0 c f g V s.basis q := by
    intro q hq
    rw [hT3, tailEff_apply tr yb xr1 xr2 y0 c f g hfg, tailEff_apply tr yb xr1 xr2 y0 c f g hfg]
    rw [s2out g (usedNotP g (by simp)), k1, k2, s2out y0 (usedNotP y0 (by simp)),
      s2out c (usedNotP c (by simp)), s2out f (usedNotP f (by simp)), s2out q hq]
  have T3in : ∀ q, q ≠ f → q ≠ g → T3 q = s2.basis q := by
    intro q h1 h2; rw [hT3, tailEff_apply tr yb xr1 xr2 y0 c f g hfg]; simp [h1, h2]
  have s4x1 : s4.basis xr1 = s.basis xr1 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun e => hcu (by simp [e])), T3in xr1
      (fun e => by rw [e] at hused; simp at hused) (fun e => by rw [e] at hused; simp at hused), k1]
  have s4x2 : s4.basis xr2 = s.basis xr2 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun e => hcu (by simp [e])), T3in xr2
      (fun e => by rw [e] at hused; simp at hused) (fun e => by rw [e] at hused; simp at hused), k2]
  -- step 5: remap again
  suffices key : ∀ mm, run (tr.remapList xr1 xr2 w (i0 :: it)) mm s4 =
      ⟨s.phase, tailEff tr yb xr1 xr2 y0 c f g V s.basis⟩ from key _
  intro mm
  have R5 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P mm s4
  apply State.extensionality
  · rw [R5.1, ← hs4]; exact s2ph
  · funext q
    by_cases hq : q ∈ (i0 :: it).map w
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      rw [R5.2.2 i hi, s4x1, s4x2]
      have rhs : tailEff tr yb xr1 xr2 y0 c f g V s.basis (w i) = s.basis (w i) := by
        rw [tailEff_apply tr yb xr1 xr2 y0 c f g hfg]
        have h1 : w i ≠ g := fun e => usedNotP g (by simp) (e ▸ hq)
        have h2 : w i ≠ f := fun e => usedNotP f (by simp) (e ▸ hq)
        simp [h1, h2]
      change (s4.basis (w i) ^^ _) = tailEff tr yb xr1 xr2 y0 c f g V s.basis (w i)
      rw [rhs]
      have h1 : w i ≠ g := fun e => usedNotP g (by simp) (e ▸ hq)
      have h2 : w i ≠ f := fun e => usedNotP f (by simp) (e ▸ hq)
      rw [← hs4]; simp only [writeBit]
      rcases List.mem_cons.mp hi with rfl | hit
      · rw [Function.update_self, T3in _ h2 h1, s2p0]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
      · rw [Function.update_of_ne (itNe i hit), T3in _ h2 h1, s2it i hit]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
    · rw [R5.2.1 q hq, ← hs4]
      change writeBit T3 (w i0) (!T3 (w i0)) q = tailEff tr yb xr1 xr2 y0 c f g V s.basis q
      simp only [writeBit]
      rw [Function.update_of_ne (fun e : q = w i0 => hq (e ▸ p0l)), T3out q hq]



/-- The merged classifier on the abscissa `xs`: remap, zero-test the non-pivot bits, decode, undo. -/
def classifier (tr : Tri) (yb : Bool) (xs work : List Wire) (y0 c f g g1 wB t : Wire) : Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

/-- Zero-test value of the merged classifier. -/
def matchBit (tr : Tri) (xs : List Wire) (st : BasisState) : Bool :=
  tr.idx.all (fun i => st (xs.getD i 0) == tr.tgt i (st (xs.getD tr.r1 0), st (xs.getD tr.r2 0)))

theorem classifier_run (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, g1, wB, t].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ xs ∧ q ∉ work)
    (s : State) (m : List Bool)
    (hg : s.basis g = false)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis g1 = false ∧ s.basis wB = false ∧ s.basis t = false)
    (hf : s.basis f = !(matchBit tr xs s.basis &&
      decide ((s.basis (xs.getD tr.r1 0), s.basis (xs.getD tr.r2 0)) = tr.pat tr.S))) :
    run (classifier tr yb xs work y0 c f g g1 wB t) m s =
      ⟨s.phase, tailEff tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g
        (matchBit tr xs s.basis) s.basis⟩ := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  set w : Nat → Wire := fun i => xs.getD i 0 with hw
  set xr1 := w tr.r1 with hx1
  set xr2 := w tr.r2 with hx2
  set P := tr.idx.map w with hP
  have winj : ∀ i j, i < 256 → j < 256 → w i = w j → i = j := by
    intro i j hi hj e
    simp only [hw] at e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact hxs.getElem_inj_iff.mp e
  have wmem : ∀ i, i < 256 → w i ∈ xs := by
    intro i hi; simp only [hw]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hPn : P.Nodup := by
    apply List.Nodup.map_on _ ix.1
    intro i hi j hj e; exact winj i j (ix.2.2.2.2 i hi) (ix.2.2.2.2 j hj) e
  have memP : ∀ q, q ∈ P ↔ ∃ i ∈ tr.idx, w i = q := by intro q; simp [hP]
  have x1P : xr1 ∉ P := by
    rw [memP]; rintro ⟨i, hi, e⟩
    exact ix.2.2.1 (winj i tr.r1 (ix.2.2.2.2 i hi) pv.1 e ▸ hi)
  have x2P : xr2 ∉ P := by
    rw [memP]; rintro ⟨i, hi, e⟩
    exact ix.2.2.2.1 (winj i tr.r2 (ix.2.2.2.2 i hi) pv.2.1 e ▸ hi)
  have x12 : xr1 ≠ xr2 := fun e => pv.2.2.1 (winj _ _ pv.1 pv.2.1 e)
  have Psub : ∀ q ∈ P, q ∈ xs := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := (memP q).mp hq; exact wmem i (ix.2.2.2.2 i hi)
  have hPl : P.length = 254 := by simp [hP, ix.2.1]
  obtain ⟨i0, it, hidx⟩ : ∃ i0 it, tr.idx = i0 :: it := by
    have hl := ix.2.1
    cases h : tr.idx with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  have hP0 : P = w i0 :: it.map w := by simp [hP, hidx]
  set p0 := w i0 with hp0
  have hPt : P.tail = it.map w := by rw [hP0]; rfl
  have hPh : P.headD 0 = p0 := by rw [hP0]; rfl
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have zp := zeroPorts_maps (it.map w) work (by rw [hitl, hwl])
  -- membership facts for the outside wires
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, g1, wB, t]) : q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    refine ⟨fun hp => h.1 (Psub q hp), h.2, fun e => h.1 (e ▸ wmem _ pv.1), fun e => h.1 (e ▸ wmem _ pv.2.1)⟩
  have p0P : p0 ∈ P := by rw [hP0]; simp
  have hused : [xr1, xr2, y0, c, f, g, g1, wB, t].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨x12, ?_⟩
      have := fun q hq => (extx q hq).2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      exact ⟨fun e => this y0 (Or.inl rfl) e.symm, fun e => this c (by tauto) e.symm,
        fun e => this f (by tauto) e.symm, fun e => this g (by tauto) e.symm,
        fun e => this g1 (by tauto) e.symm, fun e => this wB (by tauto) e.symm,
        fun e => this t (by tauto) e.symm⟩
    · intro hm
      exact (extx xr2 hm).2.2.2 rfl
  have hlP : (i0 :: it).map w = P := by rw [hP0]; rfl
  have hPn' : ((i0 :: it).map w).Nodup := by rw [hlP]; exact hPn
  have x1P' : xr1 ∉ (i0 :: it).map w := by rw [hlP]; exact x1P
  have x2P' : xr2 ∉ (i0 :: it).map w := by rw [hlP]; exact x2P
  have hextP : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ (i0 :: it).map w := by
    intro q hq; rw [hlP]; exact (extx q hq).1
  have hdisj' : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, g1, wB, t] := by
    intro q hq
    refine ⟨fun hm => hdisj q hq (Psub q (by rw [← hlP]; exact hm)), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (e | e | e)
    · exact hdisj q hq (e ▸ wmem _ pv.1)
    · exact hdisj q hq (e ▸ wmem _ pv.2.1)
    · exact (hextx q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)).2 hq
  have hmb : matchBit tr xs s.basis =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    simp only [matchBit, hidx]; rfl
  have hf' : s.basis f = !(((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) &&
      decide ((s.basis xr1, s.basis xr2) = tr.pat tr.S)) := by rw [← hmb]; exact hf
  have run_eq := shape_run tr v yb xr1 xr2 y0 c f g g1 wB t w i0 it work hPn' x1P' x2P' hused hextP
    (by rw [hitl, hwl]) hwn hdisj' s m hg hz hf'
  rw [hmb]
  have hprog : classifier tr yb xs work y0 c f g g1 wB t =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (tail tr yb xr1 xr2 y0 c f g g1 wB t) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [classifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hprog]
  exact run_eq

section Glue
open Secp256k1

/-- The three compared words for the classical point `C`. -/
def triOf (C : Point) : Tri := ⟨pairCode C, pairCode (dialogExceptionPoint C), FiniteFlagInterval.sentinel⟩

theorem exception_code {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    pairCode (dialogExceptionPoint (.some hc : Point)) =
      (doubleX cx cy).val := by
  have hy : cy ≠ -cy := of_decide_eq_true (cy_ne_neg hc)
  unfold dialogExceptionPoint
  rw [pairCode_neg, ← doublePoint_correct hc hy]
  rfl

theorem triOf_valid {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : (triOf (.some hc)).Valid := by
  have hy : cy ≠ -cy := of_decide_eq_true (cy_ne_neg hc)
  have hd := double_nonsingular hc hy
  have hB := exception_code hc
  have hA : pairCode (.some hc : Point) = cx.val := rfl
  have p256 : p < 2^256 := by norm_num [p]
  refine ⟨pairCode_lt _, pairCode_lt _, lt_trans FiniteFlagInterval.sentinel_lt p256, ?_, ?_, ?_⟩
  · show pairCode (.some hc : Point) ≠ pairCode (dialogExceptionPoint (.some hc : Point))
    rw [hA, hB]; intro e
    exact NoThreeTorsion.double_x_ne hc (ZMod.val_injective _ e.symm)
  · show pairCode (.some hc : Point) ≠ FiniteFlagInterval.sentinel
    rw [hA]; intro e
    exact FiniteFlagInterval.curve_x_not_interval hc (Or.inr (Or.inr (by rw [e]; rfl)))
  · show pairCode (dialogExceptionPoint (.some hc : Point)) ≠ FiniteFlagInterval.sentinel
    rw [hB]; intro e
    exact FiniteFlagInterval.curve_x_not_interval hd (Or.inr (Or.inr (by rw [e]; rfl)))

/-- The decoded flags agree with the dialog classification once `x` carries the sentinel for `O`. -/
theorem glue [DecidableEq Point] {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    let tr := triOf (.some hc)
    let X := if pointFinite R then pointX R else FiniteFlagInterval.sentinel
    let V := tr.idx.all (fun i => X.testBit i == tr.tgt i (X.testBit tr.r1, X.testBit tr.r2))
    pointFinite R = !(V && decide ((X.testBit tr.r1, X.testBit tr.r2) = tr.pat tr.S)) ∧
    genOut tr (yBit (dialogExceptionPoint (.some hc))) V (X.testBit tr.r1) (X.testBit tr.r2)
      (yBit R) b (pointFinite R) = dialogOrdinary b R (.some hc) := by
  intro tr X V
  have v : tr.Valid := triOf_valid hc
  have pv := Tri.pivots v
  have p256 : p < 2^256 := by norm_num [p]
  have hX : X < 2^256 := by
    simp only [X]; split_ifs
    · exact pairCode_lt R
    · exact lt_trans FiniteFlagInterval.sentinel_lt p256
  have hV : V = true ↔ ∀ i ∈ tr.idx, X.testBit i = tr.tgt i (tr.pat X) := by
    simp only [V, List.all_eq_true, beq_iff_eq, Tri.pat]
  have mK : ∀ K, K < 2^256 → (∀ i, tr.tgt i (tr.pat K) = K.testBit i) →
      ((V = true ∧ tr.pat X = tr.pat K) ↔ X = K) := by
    intro K hK hKt
    rw [hV]; exact Tri.match_iff v X K hX hK hKt
  have mA := mK tr.A v.hA (fun i => Tri.tgt_A i)
  have mB := mK tr.B v.hB (Tri.tgt_B v)
  have mS := mK tr.S v.hS (Tri.tgt_S v)
  have epat : tr.pat X = (X.testBit tr.r1, X.testBit tr.r2) := rfl
  -- pattern bits of the three words
  have ePA : tr.pat tr.A = (tr.A.testBit tr.r1, tr.A.testBit tr.r2) := rfl
  have ePB : tr.pat tr.B = (tr.B.testBit tr.r1, tr.B.testBit tr.r2) := rfl
  have ePS : tr.pat tr.S = (tr.S.testBit tr.r1, tr.S.testBit tr.r2) := rfl
  have hBS1 : tr.B.testBit tr.r1 ≠ tr.S.testBit tr.r1 := (firstDiff_spec tr.B tr.S v.hB v.hS v.BS).2
  set x1 := X.testBit tr.r1 with hx1
  set x2 := X.testBit tr.r2 with hx2
  set a1 := tr.A.testBit tr.r1
  set a2 := tr.A.testBit tr.r2
  set b1 := tr.B.testBit tr.r1
  set b2 := tr.B.testBit tr.r2
  set s1 := tr.S.testBit tr.r1
  set s2 := tr.S.testBit tr.r2
  rw [epat] at mA mB mS
  rw [ePA] at mA; rw [ePB] at mB; rw [ePS] at mS
  have eS : (V && decide ((x1, x2) = (s1, s2))) = decide (X = tr.S) := by
    apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact mS
  have dAB : X = tr.A → X ≠ tr.B := fun h e => v.AB (h.symm.trans e)
  have dAS : X = tr.A → X ≠ tr.S := fun h e => v.AS (h.symm.trans e)
  have dBS : X = tr.B → X ≠ tr.S := fun h e => v.BS (h.symm.trans e)
  -- the decoded flag in terms of the three matches
  have key : genOut tr (yBit (dialogExceptionPoint (.some hc))) V x1 x2 (yBit R) b
      (!(decide (X = tr.S))) =
      (b && !(decide (X = tr.A) || decide (X = tr.S) ||
        (decide (X = tr.B) && (yBit R == yBit (dialogExceptionPoint (.some hc)))))) := by
    unfold genOut
    by_cases ro : tr.role1 = true
    · have e1 : a1 = s1 := by simpa [Tri.role1] using ro
      have er2 : tr.r2 = firstDiff tr.A tr.S := by simp [Tri.r2, ro]
      have n2 : a2 ≠ s2 := by
        have d := (firstDiff_spec tr.A tr.S v.hA v.hS v.AS).2; rw [← er2] at d; exact d
      have k1 : (V && (x1 == a1)) = (decide (X = tr.A) || decide (X = tr.S)) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hv, h1⟩
          by_cases h2 : x2 = a2
          · exact Or.inl (mA.mp ⟨hv, by rw [h1, h2]⟩)
          · have h2' : x2 = s2 := by
              cases hx : x2 <;> cases ha : a2 <;> cases hs : s2 <;> simp_all
            exact Or.inr (mS.mp ⟨hv, by rw [h1, h2', e1]⟩)
        · rintro (h | h)
          · obtain ⟨hv, hp⟩ := mA.mpr h; exact ⟨hv, (Prod.mk.inj hp).1⟩
          · obtain ⟨hv, hp⟩ := mS.mpr h; exact ⟨hv, (Prod.mk.inj hp).1.trans e1.symm⟩
      have k2 : (V && (x1 != a1) && (x2 == b2)) = decide (X = tr.B) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hv, h1⟩, h2⟩
          have h1' : x1 = b1 := by
            have : b1 ≠ a1 := by rw [e1]; exact hBS1
            cases hx : x1 <;> cases ha : a1 <;> cases hb : b1 <;> simp_all
          exact mB.mp ⟨hv, by rw [h1', h2]⟩
        · intro h
          obtain ⟨hv, hp⟩ := mB.mpr h
          have hb1 : b1 ≠ a1 := by rw [e1]; exact hBS1
          refine ⟨⟨hv, ?_⟩, (Prod.mk.inj hp).2⟩
          rw [(Prod.mk.inj hp).1]; exact hb1
      simp only [ro, if_true]
      rw [k1, show (V && (x1 != a1) && (x2 == b2) &&
          (yBit R == yBit (dialogExceptionPoint (.some hc)))) =
        ((V && (x1 != a1) && (x2 == b2)) && (yBit R == yBit (dialogExceptionPoint (.some hc)))) from rfl, k2]
    · have ro' : tr.role1 = false := by simpa using ro
      have ne1 : a1 ≠ s1 := by simpa [Tri.role1] using ro
      have e1 : a1 = b1 := by
        cases ha : a1 <;> cases hb : b1 <;> cases hs : s1 <;> simp_all
      have er2 : tr.r2 = firstDiff tr.A tr.B := by simp [Tri.r2, ro']
      have n2 : a2 ≠ b2 := by
        have d := (firstDiff_spec tr.A tr.B v.hA v.hB v.AB).2; rw [← er2] at d; exact d
      have k1 : (V && (x1 == a1) && (x2 == a2)) = decide (X = tr.A) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hv, h1⟩, h2⟩; exact mA.mp ⟨hv, by rw [h1, h2]⟩
        · intro h; obtain ⟨hv, hp⟩ := mA.mpr h; exact ⟨⟨hv, (Prod.mk.inj hp).1⟩, (Prod.mk.inj hp).2⟩
      have k2 : (V && (x1 == a1) && (x2 != a2)) = decide (X = tr.B) := by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨hv, h1⟩, h2⟩
          have h2' : x2 = b2 := by
            cases hx : x2 <;> cases ha : a2 <;> cases hb : b2 <;> simp_all
          exact mB.mp ⟨hv, by rw [h1, h2', e1]⟩
        · intro h
          obtain ⟨hv, hp⟩ := mB.mpr h
          refine ⟨⟨hv, (Prod.mk.inj hp).1.trans e1.symm⟩, ?_⟩
          rw [(Prod.mk.inj hp).2]; exact Ne.symm n2
      simp only [ro', Bool.false_eq_true, if_false]
      rw [show (V && (x1 == a1) && (x2 != a2) && (yBit R == yBit (dialogExceptionPoint (.some hc)))) =
        ((V && (x1 == a1) && (x2 != a2)) && (yBit R == yBit (dialogExceptionPoint (.some hc)))) from rfl,
        k1, k2]
      by_cases hA : X = tr.A
      · have := dAB hA; have := dAS hA; simp_all
      · by_cases hB : X = tr.B
        · have := dBS hB; simp_all
        · cases decide (X = tr.S) <;> simp_all
  have hC0 : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have fin_iff : pointFinite R = !(decide (X = tr.S)) := by
    cases R with
    | zero =>
      have pf0 : pointFinite (WeierstrassCurve.Affine.Point.zero : Point) = false := rfl
      have hX0 : X = FiniteFlagInterval.sentinel := by simp only [X, pf0, Bool.false_eq_true, if_false]
      rw [pf0, hX0]; simp [tr, triOf]
    | @some rx ry hr =>
      have pf1 : pointFinite (.some hr : Point) = true := rfl
      have hX1 : X = rx.val := by simp only [X, pf1, if_true]; rfl
      have hne : rx.val ≠ FiniteFlagInterval.sentinel := by
        intro e; exact FiniteFlagInterval.curve_x_not_interval hr (Or.inr (Or.inr (by rw [e]; rfl)))
      rw [pf1, hX1]; simp [tr, triOf, hne]
  refine ⟨?_, ?_⟩
  · rw [fin_iff, ePS, ← eS]
  · rw [fin_iff, key]
    apply Bool.eq_iff_iff.mpr
    rw [dialogOrdinary_true b R _ hC0]
    cases R with
    | zero =>
      have pf0 : pointFinite (WeierstrassCurve.Affine.Point.zero : Point) = false := rfl
      have hX0 : X = tr.S := by simp only [X, pf0, Bool.false_eq_true, if_false]; rfl
      rw [hX0]
      constructor
      · intro h; simp at h
      · rintro ⟨_, h, _⟩; exact absurd rfl h
    | @some rx ry hr =>
      have pf1 : pointFinite (.some hr : Point) = true := rfl
      have hX1 : X = pairCode (.some hr : Point) := by simp only [X, pf1, if_true]; rfl
      have hR0 : (.some hr : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hr
      have hne : X ≠ tr.S := by
        rw [hX1]; intro e
        exact FiniteFlagInterval.curve_x_not_interval hr (Or.inr (Or.inr (by
          rw [show rx.val = pairCode (.some hr : Point) from rfl, e]; rfl)))
      have hAeq : X = tr.A ↔ ((.some hr : Point) = .some hc ∨ (.some hr : Point) = -(.some hc : Point)) := by
        rw [hX1, ← sameX_iff_eq_or_neg hr hc]
        constructor
        · intro e; exact ZMod.val_injective _ e
        · intro e; show rx.val = cx.val; rw [e]
      have hBeq : (decide (X = tr.B) && (yBit (.some hr : Point) == yBit (dialogExceptionPoint (.some hc)))) =
          decide ((.some hr : Point) = dialogExceptionPoint (.some hc)) := by
        rw [hX1]
        have := pair_value_eq (.some hr : Point) (dialogExceptionPoint (.some hc))
        rw [show tr.B = pairCode (dialogExceptionPoint (.some hc : Point)) from rfl, this]
        apply Bool.eq_iff_iff.mpr
        rw [pointEqual_true_iff]; simp
      rw [hBeq]
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
        hne, not_false_eq_true, and_true, ne_eq]
      constructor
      · rintro ⟨hb, hA, hE⟩
        refine ⟨hb, hR0, ?_, ?_, hE⟩
        · intro e; exact hA (hAeq.mpr (Or.inl e))
        · intro e; exact hA (hAeq.mpr (Or.inr e))
      · rintro ⟨hb, -, h1, h2, hE⟩
        refine ⟨hb, ?_, hE⟩
        intro hA; rcases hAeq.mp hA with e | e
        · exact h1 e
        · exact h2 e

end Glue

theorem corrections_fix (f : Wire → Wire) (cs : List Correction)
    (h : ∀ w ∈ correctionWires cs, f w = w) : cs.map (renameCorrection f) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z t =>
      simp only [correctionWires, Finset.mem_union, Finset.mem_singleton] at h
      simp [renameCorrection, h t (Or.inl rfl), ih (fun w hw => h w (Or.inr hw))]
    | CZ a b =>
      simp only [correctionWires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
      simp [renameCorrection, h a (Or.inl (Or.inl rfl)), h b (Or.inl (Or.inr rfl)),
        ih (fun w hw => h w (Or.inr hw))]

/-- A relabelling that fixes every wire of a program leaves it unchanged. -/
theorem rename_fix (f : Wire → Wire) (P : Program) (h : ∀ w ∈ wires P, f w = w) :
    renameProgram f P = P := by
  induction P with
  | nil => rfl
  | cons i P ih =>
    have hi : ∀ w ∈ i.wires, f w = w := fun w hw => h w (by simp [wires, hw])
    have hP : ∀ w ∈ wires P, f w = w := fun w hw => h w (by simp [wires, hw])
    have e := ih hP
    simp only [renameProgram, List.map_cons] at e ⊢
    rw [e]
    congr 1
    cases i with
    | X t => simp only [Instr.wires, Finset.mem_singleton] at hi; simp [renameInstr, hi t rfl]
    | CX c t =>
      simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hi
      simp [renameInstr, hi c (Or.inl rfl), hi t (Or.inr rfl)]
    | CCX a b t =>
      simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hi
      simp [renameInstr, hi a (Or.inl rfl), hi b (Or.inr (Or.inl rfl)), hi t (Or.inr (Or.inr rfl))]
    | measureX t c0 c1 =>
      simp only [Instr.wires, Finset.mem_union, Finset.mem_singleton] at hi
      simp [renameInstr, hi t (Or.inl (Or.inl rfl)),
        corrections_fix f c0 (fun w hw => hi w (Or.inl (Or.inr hw))),
        corrections_fix f c1 (fun w hw => hi w (Or.inr hw))]

section Stage
open Secp256k1 ControlledPointLayout

/-- The merged input stage: sentinel-code `x`, then the three-word classifier. -/
def stage (L : ControlledPointLayout) (C : Point) : Program :=
  FiniteFlagInterval.zrep L ++
  classifier (triOf C) (yBit (dialogExceptionPoint C)) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0)

/-- Sentinel-coded abscissa: `x` for a finite point, the sentinel for `O`. -/
def codeX (R : Point) : Nat := if pointFinite R then pointX R else FiniteFlagInterval.sentinel

/-- State after the input stage: `x` sentinel-coded, the finite flag cleared, the generic select set. -/
def Mid (L : ControlledPointLayout) (R : Point) (G : Bool) (s t : State) : Prop :=
  t.phase = s.phase ∧ regValue L.point.x t.basis = codeX R ∧ t.basis L.point.finite = false ∧
    t.basis L.genericSelect = G ∧
    ∀ q, q ∉ L.point.x → q ≠ L.point.finite → q ≠ L.genericSelect → t.basis q = s.basis q

theorem Mid.unique {L : ControlledPointLayout} {R : Point} {G : Bool} {s t u : State}
    (ht : Mid L R G s t) (hu : Mid L R G s u) : t = u := by
  apply State.extensionality
  · exact ht.1.trans hu.1.symm
  · funext q
    by_cases hx : q ∈ L.point.x
    · exact (regValue_eq_iff _ _ _).mp (ht.2.1.trans hu.2.1.symm) q hx
    by_cases hf : q = L.point.finite
    · subst hf; exact ht.2.2.1.trans hu.2.2.1.symm
    by_cases hg : q = L.genericSelect
    · subst hg; exact ht.2.2.2.1.trans hu.2.2.2.1.symm
    exact (ht.2.2.2.2 q hx hf hg).trans (hu.2.2.2.2 q hx hf hg).symm

/-- Wire facts of the dialog layout used by the merged stage. -/
theorem stage_layout (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.point.x.Nodup ∧ L.point.x.length = 256 ∧ (L.dialogPool.take 253).length = 253 ∧
    (L.dialogPool.take 253).Nodup ∧ (∀ q ∈ L.dialogPool.take 253, q ∉ L.point.x) ∧
    [yLow L, L.control, L.point.finite, L.genericSelect,
      L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0].Nodup ∧
    (∀ q ∈ [yLow L, L.control, L.point.finite, L.genericSelect,
      L.dialogPool.getD 253 0, L.dialogPool.getD 254 0, L.dialogPool.getD 255 0],
      q ∉ L.point.x ∧ q ∉ L.dialogPool.take 253) := by
  have hD := L.dialogUsed_nodup hn
  have hxl : L.point.x.length = 256 := hw.inputX
  have hyl : L.point.y.length = 256 := hw.inputY
  have hpl := dialogPool_length L hw
  have C : ∀ q, (if q = L.point.finite then 1 else 0) + L.point.x.count q + L.point.y.count q +
      (if q = L.control then 1 else 0) + L.inPlaceFlags.count q + L.dialogPool.count q ≤ 1 := by
    intro q
    have h := List.nodup_iff_count_le_one.mp hD q
    simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons,
      List.count_singleton', List.count_nil] at h
    split_ifs at h ⊢ <;> simp_all <;> omega
  have pos (l : List Wire) (q : Wire) (h : q ∈ l) : 1 ≤ l.count q := List.count_pos_iff.mpr h
  have hpn : L.dialogPool.Nodup := List.nodup_iff_count_le_one.mpr (fun q => by have := C q; omega)
  have hxn : L.point.x.Nodup := List.nodup_iff_count_le_one.mpr (fun q => by have := C q; omega)
  have xp : ∀ q, q ∈ L.dialogPool → q ∉ L.point.x := by
    intro q h1 h2; have := C q; have := pos _ _ h1; have := pos _ _ h2; omega
  have pget (i : Nat) (hi : i < 2613) : L.dialogPool.getD i 0 ∈ L.dialogPool := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have takeMem : ∀ q ∈ L.dialogPool.take 253, q ∈ L.dialogPool := fun q h => List.mem_of_mem_take h
  have pnot (i : Nat) (hi : 253 ≤ i) (hi2 : i < 2613) : L.dialogPool.getD i 0 ∉ L.dialogPool.take 253 := by
    intro h
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem h
    rw [List.getElem_take] at e
    rw [List.getD_eq_getElem _ _ (by omega)] at e
    have hj' : j < 253 := by simpa [List.length_take, hpl] using hj
    have := (hpn.getElem_inj_iff).mp e
    omega
  have pne (i j : Nat) (hi : i < 2613) (hj : j < 2613) (hij : i ≠ j) :
      L.dialogPool.getD i 0 ≠ L.dialogPool.getD j 0 := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    intro e; exact hij ((hpn.getElem_inj_iff).mp e)
  have yl : yLow L ∈ L.point.y := by
    unfold yLow
    rw [show L.point.y.headD L.control = L.point.y.getD 0 L.control by
      cases L.point.y <;> rfl]
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have gf : L.genericSelect ∈ L.inPlaceFlags := by simp [inPlaceFlags]
  -- region separation from the counts
  have Cq (q : Wire) := C q
  have yx : ∀ q ∈ L.point.y, q ∉ L.point.x := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have yfl : ∀ q ∈ L.point.y, q ∉ L.inPlaceFlags := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have yp : ∀ q ∈ L.point.y, q ∉ L.dialogPool := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have flx : ∀ q ∈ L.inPlaceFlags, q ∉ L.point.x := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have flp : ∀ q ∈ L.inPlaceFlags, q ∉ L.dialogPool := by
    intro q h1 h2; have := Cq q; have := pos _ _ h1; have := pos _ _ h2; omega
  have yc : ∀ q ∈ L.point.y, q ≠ L.control := by
    intro q h1 e; subst e; have c := Cq L.control; have hp := pos _ _ h1
    simp only [eq_self_iff_true, if_true] at c; omega
  have yf : ∀ q ∈ L.point.y, q ≠ L.point.finite := by
    intro q h1 e; subst e; have c := Cq L.point.finite; have hp := pos _ _ h1
    simp only [eq_self_iff_true, if_true] at c; omega
  have cx : L.control ∉ L.point.x := by
    intro h; have c := Cq L.control; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have cfl : L.control ∉ L.inPlaceFlags := by
    intro h; have c := Cq L.control; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have cp : L.control ∉ L.dialogPool := by
    intro h; have c := Cq L.control; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have fx : L.point.finite ∉ L.point.x := by
    intro h; have c := Cq L.point.finite; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have ffl : L.point.finite ∉ L.inPlaceFlags := by
    intro h; have c := Cq L.point.finite; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have fp : L.point.finite ∉ L.dialogPool := by
    intro h; have c := Cq L.point.finite; have := pos _ _ h; simp only [eq_self_iff_true, if_true] at c; omega
  have cf : L.control ≠ L.point.finite := by
    intro e; have c := Cq L.control; rw [← e] at c; simp only [eq_self_iff_true, if_true] at c; omega
  have p3 := pget 253 (by decide); have p4 := pget 254 (by decide); have p5 := pget 255 (by decide)
  refine ⟨hxn, hxl, by simp [hpl], hpn.sublist (List.take_sublist _ _), fun q h => xp q (takeMem q h),
    ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true]
    refine ⟨⟨yc _ yl, yf _ yl, fun e => yfl _ yl (e ▸ gf), fun e => yp _ yl (e ▸ p3),
        fun e => yp _ yl (e ▸ p4), fun e => yp _ yl (e ▸ p5)⟩,
      ⟨cf, fun e => cfl (e ▸ gf), fun e => cp (e ▸ p3), fun e => cp (e ▸ p4), fun e => cp (e ▸ p5)⟩,
      ⟨fun e => ffl (e ▸ gf), fun e => fp (e ▸ p3), fun e => fp (e ▸ p4), fun e => fp (e ▸ p5)⟩,
      ⟨fun e => flp _ gf (e ▸ p3), fun e => flp _ gf (e ▸ p4), fun e => flp _ gf (e ▸ p5)⟩,
      ⟨pne 253 254 (by decide) (by decide) (by decide), pne 253 255 (by decide) (by decide) (by decide)⟩,
      ⟨pne 254 255 (by decide) (by decide) (by decide), not_false⟩⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨yx _ yl, fun h => yp _ yl (takeMem _ h)⟩
    · exact ⟨cx, fun h => cp (takeMem _ h)⟩
    · exact ⟨fx, fun h => fp (takeMem _ h)⟩
    · exact ⟨flx _ gf, fun h => flp _ gf (takeMem _ h)⟩
    · exact ⟨xp _ p3, pnot 253 le_rfl (by decide)⟩
    · exact ⟨xp _ p4, pnot 254 (by decide) (by decide)⟩
    · exact ⟨xp _ p5, pnot 255 (by decide) (by decide)⟩

theorem y_not_x (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    ∀ q ∈ L.point.y, q ∉ L.point.x := by
  have hD := L.dialogUsed_nodup hn
  intro q h1 h2
  have h := List.nodup_iff_count_le_one.mp hD q
  simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons,
    List.count_singleton', List.count_nil] at h
  have c1 : 1 ≤ L.point.y.count q := List.count_pos_iff.mpr h1
  have c2 : 1 ≤ L.point.x.count q := List.count_pos_iff.mpr h2
  split_ifs at h <;> omega

theorem stage_mid [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary L R b (fun _ => false) s.basis) :
    Mid L R (dialogOrdinary b R (.some hc)) s (run (stage L (.some hc)) m s) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout L hw hn
  have hp := (point_holds _ _ _).mp hs.point
  have v := triOf_valid hc
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have hpl := dialogPool_length L hw
  have Z := FiniteFlagInterval.zrep_run L hw hn s m
  unfold stage
  rw [LocalWireModel.run_concat]
  generalize hs1 : run (FiniteFlagInterval.zrep L) m s = s1 at Z ⊢
  have fx : L.point.finite ∉ L.point.x := (hextx _ (by simp)).1
  have gx : L.genericSelect ∉ L.point.x := (hextx _ (by simp)).1
  have yx : yLow L ∉ L.point.x := (hextx _ (by simp)).1
  have cx' : L.control ∉ L.point.x := (hextx _ (by simp)).1
  have fg : L.point.finite ≠ L.genericSelect := by
    intro e; rw [e] at hext; simp at hext
  have hX : regValue L.point.x s1.basis = codeX R := by
    rw [Z.2.2, hp.2.1, hp.1]
    unfold codeX
    cases hf : pointFinite R
    · have hx0 : pointX R = 0 := by
        cases R with
        | zero => rfl
        | some h => simp [pointFinite] at hf
      simp [hx0]
    · simp
  have xbit : ∀ i, i < 256 → s1.basis (L.point.x.getD i 0) = (codeX R).testBit i := by
    intro i hi
    rw [← hX]; exact (LocalWireModel.reg_bit L.point.x s1.basis i (by rw [hxl]; exact hi)).symm
  have s1f : s1.basis L.point.finite = pointFinite R := (Z.2.1 _ fx).trans hp.1
  have s1g : s1.basis L.genericSelect = false := (Z.2.1 _ gx).trans
    (hs.flags _ (by simp [ControlledPointLayout.inPlaceFlags]))
  have s1c : s1.basis L.control = b := (Z.2.1 _ cx').trans hs.control
  have s1y : s1.basis (yLow L) = yBit R := by
    rw [Z.2.1 _ yx]
    have hyl : L.point.y.length = 256 := hw.inputY
    have e : yLow L = L.point.y.getD 0 0 := by
      unfold yLow
      cases hy : L.point.y with
      | nil => rw [hy] at hyl; simp at hyl
      | cons a l => rfl
    rw [e, ← LocalWireModel.reg_bit L.point.y s.basis 0 (by rw [hyl]; decide), hp.2.2]
    unfold yBit
    rw [Nat.testBit_zero]
  have s1p : ∀ q, q ∈ L.dialogPool → q ∉ L.point.x → s1.basis q = false := by
    intro q hq hx; rw [Z.2.1 _ hx]; exact (regValue_zero _ _).mp hs.clean q hq
  have pget (i : Nat) (hi : i < 2613) : L.dialogPool.getD i 0 ∈ L.dialogPool := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hz : (∀ q ∈ L.dialogPool.take 253, s1.basis q = false) ∧
      s1.basis (L.dialogPool.getD 253 0) = false ∧ s1.basis (L.dialogPool.getD 254 0) = false ∧
      s1.basis (L.dialogPool.getD 255 0) = false :=
    ⟨fun q hq => s1p q (List.mem_of_mem_take hq) (hdisj q hq),
      s1p _ (pget 253 (by decide)) (hextx _ (by simp)).1,
      s1p _ (pget 254 (by decide)) (hextx _ (by simp)).1,
      s1p _ (pget 255 (by decide)) (hextx _ (by simp)).1⟩
  have G := glue hc b R
  have hmb : matchBit (triOf (.some hc)) L.point.x s1.basis =
      (triOf (.some hc)).idx.all (fun i => (codeX R).testBit i ==
        (triOf (.some hc)).tgt i ((codeX R).testBit (triOf (.some hc)).r1,
          (codeX R).testBit (triOf (.some hc)).r2)) := by
    unfold matchBit
    rw [xbit _ pv.1, xbit _ pv.2.1, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    apply forall₂_congr
    intro i hi
    rw [xbit i (ix.2.2.2.2 i hi)]
  have hf' : s1.basis L.point.finite = !(matchBit (triOf (.some hc)) L.point.x s1.basis &&
      decide ((s1.basis (L.point.x.getD (triOf (.some hc)).r1 0),
        s1.basis (L.point.x.getD (triOf (.some hc)).r2 0)) = (triOf (.some hc)).pat (triOf (.some hc)).S)) := by
    rw [s1f, hmb, xbit _ pv.1, xbit _ pv.2.1]
    exact G.1
  have CR := classifier_run (triOf (.some hc)) v (yBit (dialogExceptionPoint (.some hc))) L.point.x
    (L.dialogPool.take 253) (yLow L) L.control L.point.finite L.genericSelect
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0)
    hxn hxl hwl hwn hdisj hext hextx s1 (List.drop (measurementCount (FiniteFlagInterval.zrep L)) m) s1g hz hf'
  rw [CR]
  refine ⟨Z.1, ?_, ?_, ?_, ?_⟩
  · rw [← hX]
    apply regValue_congr
    intro q hq
    dsimp only
    rw [tailEff_apply _ _ _ _ _ _ _ _ fg]
    have hqg : q ≠ L.genericSelect := fun e => gx (e ▸ hq)
    have hqf : q ≠ L.point.finite := fun e => fx (e ▸ hq)
    simp [hqg, hqf]
  · show tailEff _ _ _ _ _ _ _ _ _ s1.basis L.point.finite = false
    rw [tailEff_apply _ _ _ _ _ _ _ _ fg]
    simp [fg]
  · show tailEff _ _ _ _ _ _ _ _ _ s1.basis L.genericSelect = _
    rw [tailEff_apply _ _ _ _ _ _ _ _ fg, if_pos rfl, s1g, xbit _ pv.1, xbit _ pv.2.1, s1y, s1c, s1f, hmb,
      Bool.false_xor]
    exact G.2
  · intro q hx hf hg
    show tailEff _ _ _ _ _ _ _ _ _ s1.basis q = _
    rw [tailEff_apply _ _ _ _ _ _ _ _ fg]
    simp only [hg, hf, if_false]
    exact Z.2.1 q hx

/-- The record's input classification and flag merge leave only the generic select set. -/
theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C = decide (R = C) := by
  simp only [pointEqual, pointCode_injective.eq_iff]

open Classical in
theorem oldPrefix_triple (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _ => false))
      (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc))
      (PointDialogBoundary L R b
        (dialogFlagState L false false (dialogOrdinary b R (.some hc)) false false false false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simp,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simp]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simp]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simp]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simp]
  have hfin (P : Point) : (b && pointFinite P) = (b ^^ (b && pointEqual P 0)) := by
    rw [pointEqual_zero]; cases b <;> cases pointFinite P <;> rfl
  have hGv : ((((false ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) = G := by
    rw [hfin, hO]; simp only [G, dialogOrdinary, O, D, I, H, Bool.false_xor]
  have hgen := (dialogOrdinary_true b R C hC)
  have covered : G=true → b=true ∧ pointFinite R=true := by
    intro hg
    obtain ⟨hb,h0,-⟩ := hgen.mp hg
    refine ⟨hb,?_⟩
    cases R with
    | zero => exact False.elim (h0 rfl)
    | some hr => rfl
  have hG1 : (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) = G := by
    rw [← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have h3 := inputClass_flag L hw hn R C cy b false false false false false false false
  rw [hD,hI,hH,Bool.false_xor,Bool.false_xor,Bool.false_xor] at h3
  have h6 := genFlagN_flag L hn R b false D I false false H false
  rw [hG1] at h6
  have hHx : H = true → b = true ∧ D = false := by
    intro h
    dsimp only [H, D, dialogException, dialogDouble] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, _, hne, _⟩, hR⟩ := h
    refine ⟨hb, ?_⟩
    simp [hR, hne]
  have hDx : D = true → b = true := by
    intro h
    dsimp only [D, dialogDouble] at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have cls := DHClass.classify hc b R
  dsimp only at cls
  have hKC : decide (cy≠-cy) = decide (C≠-C) := by
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact doubling_enabled_iff hc
  have clrD : false = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))) := by
    rw [hKC]; simp only [D, G, C]; rw [← cls.1, Bool.xor_self]
  have clrH : false = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C))) := by
    rw [hE]; simp only [H, G, C]; rw [← cls.2, Bool.xor_self]
  have hf1 := clrDH_flag L hw hn C cy R b D G H false false clrD clrH

  have hf1' := FusedFlags.boundary_step L hw hn hc true R b D G H false false covered
    (fun _ => ⟨rfl, rfl⟩) (by simp) hf1
  have h0 : dialogFlagState L false false false false false false false = (fun _ => false) := by
    funext q; simp [dialogFlagState, writeBit, Function.update]
  have trip := Triple.seq h3 (Triple.seq h6 hf1')
  rw [h0] at trip
  intro s m hs
  have e := FusedFlags.same_context (genFlagN L ++ FusedFlags.adapterProgram L (.some hc) true)
    (FusedFlags.prefixProgram L (.some hc)) (inputClass L (.some hc) cy) []
    (FusedFlags.prefix_measurements L (.some hc)) (FusedFlags.prefix_run L hw hn (.some hc)) s m
  simp only [List.append_nil] at e
  rw [← e]
  have t := trip s m hs
  simpa only [List.append_assoc] using t

theorem poolWire_mem (L : ControlledPointLayout) (hw : L.Widths) (i : Nat) (hi : i < 2613) :
    L.core.poolWire i ∈ L.dialogPool := by
  have hpl := dialogPool_length L hw
  have hcore : 2613 ≤ L.core.pool.length := by
    have := hpl; simp only [ControlledPointLayout.dialogPool, List.length_take] at this; omega
  simp only [PointAddLayout.poolWire, ControlledPointLayout.dialogPool]
  rw [List.getD_eq_getElem _ _ (by omega)]
  apply List.mem_iff_getElem.mpr
  refine ⟨i, by simp only [List.length_take]; omega, ?_⟩
  simp [List.getElem_take]

theorem yLow_mem (L : ControlledPointLayout) (hw : L.Widths) : yLow L ∈ L.point.y := by
  have hyl : L.point.y.length = 256 := hw.inputY
  unfold yLow
  cases hy : L.point.y with
  | nil => rw [hy] at hyl; simp at hyl
  | cons a l => simp

theorem sitesN_used (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q ∈ sitesN L, q ∈ L.dialogUsedWires := by
  have hpl := dialogPool_length L hw
  have hcore : 2613 ≤ L.core.pool.length := by
    have := hpl; simp only [ControlledPointLayout.dialogPool, List.length_take] at this; omega
  have pool (i : Nat) (hi : i < 2613) : L.core.poolWire i ∈ L.dialogPool := by
    simp only [PointAddLayout.poolWire, ControlledPointLayout.dialogPool]
    rw [List.getD_eq_getElem _ _ (by omega)]
    apply List.mem_iff_getElem.mpr
    refine ⟨i, by simp only [List.length_take]; omega, ?_⟩
    simp [List.getElem_take]
  intro q hq
  simp only [sitesN, List.mem_append, List.mem_singleton] at hq
  simp only [ControlledPointLayout.dialogUsedWires, List.mem_append, List.mem_singleton]
  rcases hq with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · left; right
    simp only [flagsN, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [ControlledPointLayout.inPlaceFlags, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · right
    simp only [sharedPoolF, wireBlock, List.mem_append, List.mem_map, List.mem_range'_1] at h
    rcases h with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩ <;> exact pool i (by omega)

/-- The record's input stage in its un-relabelled form. -/
def oldStage (L : ControlledPointLayout) (C : Point) (cy : Fp) : Program :=
  inputClass L C cy ++ FusedFlags.prefixProgram L C ++ FiniteFlagInterval.zrep L ++
    CodexYParityProbe.clearF L

theorem dialogFlagState_other (L : ControlledPointLayout) (G : Bool) (q : Wire) (hq : q ≠ L.genericSelect) :
    dialogFlagState L false false G false false false false q = false := by
  simp only [dialogFlagState, writeBit, Function.update]
  split_ifs <;> simp_all

open Classical in
theorem oldStage_mid (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary L R b (fun _ => false) s.basis) :
    Mid L R (dialogOrdinary b R (.some hc)) s (run (oldStage L (.some hc) cy) m s) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout L hw hn
  have hD := L.dialogUsed_nodup hn
  have hpl := dialogPool_length L hw
  have used_mem : ∀ q, q ∈ L.dialogUsedWires ↔ q ∈ PointAddLayout.pointWires L.point ∨ q = L.control ∨
      q ∈ L.inPlaceFlags ∨ q ∈ L.dialogPool := by
    intro q; simp only [ControlledPointLayout.dialogUsedWires, List.mem_append, List.mem_singleton]; tauto
  -- support of the record prefix
  have supp : ∀ q, q ∉ L.dialogUsedWires →
      q ∉ wires (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc)) := by
    intro q hq hm
    rw [wires_append, Finset.mem_union] at hm
    rcases hm with h | h
    · have h1 := List.mem_toFinset.mp (inputClass_wires L hw (.some hc) cy h)
      apply hq
      have yl := yLow_mem L hw
      have p514 := poolWire_mem L hw 514 (by decide)
      simp only [List.mem_cons, List.mem_append] at h1
      simp only [ControlledPointLayout.dialogUsedWires, PointAddLayout.pointWires, List.mem_append,
        List.mem_cons, List.mem_singleton, ControlledPointLayout.inPlaceFlags, List.not_mem_nil, or_false]
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | h1 | h1
      · tauto
      · tauto
      · tauto
      · tauto
      · tauto
      · tauto
      · have : q ∈ L.point.x := h1
        tauto
      · have : q ∈ L.dialogPool := List.mem_of_mem_take h1
        tauto
    · have h2 := (FusedFlags.part_support L hc).1 h
      rw [wires_append, Finset.mem_union] at h2
      rcases h2 with h3 | h3
      · exact hq (sitesN_used L hw q (List.mem_toFinset.mp (genFlagN_support L h3)))
      · exact hq (sitesN_used L hw q (List.mem_toFinset.mp (clrDH_sitesN L hw _ _ h3)))
  have hp := (point_holds _ _ _).mp hs.point
  -- step 1: the record prefix
  have T := oldPrefix_triple L hw hn R hc b s m hs
  unfold oldStage
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc)) m s = t1 at T supp ⊢
  have hp1 := (point_holds _ _ _).mp T.2.point
  have t1out : ∀ q, q ∉ L.dialogUsedWires → t1.basis q = s.basis q := by
    intro q hq; rw [← ht1]; exact run_preserves_outside _ m s q (supp q hq)
  have fx : L.point.finite ∉ L.point.x := (hextx _ (by simp)).1
  have gx : L.genericSelect ∉ L.point.x := (hextx _ (by simp)).1
  have fg : L.point.finite ≠ L.genericSelect := by intro e; rw [e] at hext; simp at hext
  -- step 2: the sentinel coding
  have Z := FiniteFlagInterval.zrep_run L hw hn t1 (List.drop (measurementCount
    (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc))) m)
  generalize ht2 : run (FiniteFlagInterval.zrep L) (List.drop (measurementCount
    (inputClass L (.some hc) cy ++ FusedFlags.prefixProgram L (.some hc))) m) t1 = t2 at Z ⊢
  have hX : regValue L.point.x t2.basis = codeX R := by
    rw [Z.2.2, hp1.2.1, hp1.1]
    unfold codeX
    cases hf : pointFinite R
    · have hx0 : pointX R = 0 := by
        cases R with
        | zero => rfl
        | some h => simp [pointFinite] at hf
      simp [hx0]
    · simp
  have t2f : t2.basis L.point.finite = pointFinite R := (Z.2.1 _ fx).trans hp1.1
  -- step 3: the finite-flag clear
  have hz : regValue (CodexYParityProbe.work L) t2.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have hq' : q ∈ L.dialogPool.take 245 := hq
    have hqx : q ∉ L.point.x := fun h => (stage_layout L hw hn).2.2.2.2.1 q
      (List.mem_take_iff_getElem.mpr (by
        obtain ⟨i, hi, e⟩ := List.mem_take_iff_getElem.mp hq'
        exact ⟨i, by omega, e⟩)) h
    rw [Z.2.1 _ hqx]
    exact (regValue_zero _ _).mp T.2.clean q (List.mem_of_mem_take hq')
  have hY : regValue L.point.y t2.basis = pointY R := by
    rw [← hp1.2.2]; apply regValue_congr; intro q hq
    exact Z.2.1 q (y_not_x L hn q hq)
  have fb : (pointFinite R ^^ CodexYParityProbe.finiteBit (codeX R) (pointY R)) = false := by
    unfold codeX
    cases R with
    | zero =>
      have h0 : pointFinite (WeierstrassCurve.Affine.Point.zero : Point) = false := rfl
      have hy0 : pointY (WeierstrassCurve.Affine.Point.zero : Point) = 0 := rfl
      have eq : FiniteFlagInterval.sentinel = p-1 := by norm_num [FiniteFlagInterval.sentinel, p]
      simp [h0, hy0, CodexYParityProbe.finiteBit, eq, CodexYParityMath.sentinel_matches]
    | @some rx ry hr =>
      have h1 : pointFinite (.some hr : Point) = true := rfl
      have hne : CodexYParityProbe.finiteBit rx.val ry.val = true :=
        decide_eq_true (CodexYParityMath.curve_not_matches hr)
      have e : pointX (.some hr : Point) = rx.val := rfl
      have e' : pointY (.some hr : Point) = ry.val := rfl
      simp [h1, e, e', hne]
  have zero : ∀ mm, (run (CodexYParityProbe.clrF L) mm t2).basis L.point.finite = false := by
    intro mm
    rw [CodexYParityProbe.clrF_run L hw hn _ _ hz, hX, hY, t2f]
    simp only [writeBit, Function.update_self]
    exact fb
  rw [CodexYParityProbe.clearF_eq L hw hn _ _ hz (zero _), CodexYParityProbe.clrF_run L hw hn _ _ hz]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show t2.phase = s.phase
    rw [Z.1]; exact T.1
  · show regValue L.point.x (writeBit t2.basis L.point.finite _) = codeX R
    rw [← hX]; apply regValue_congr; intro q hq
    have hqf : q ≠ L.point.finite := fun e => fx (e ▸ hq)
    simp [writeBit, Function.update, hqf]
  · show writeBit t2.basis L.point.finite _ L.point.finite = false
    simp only [writeBit, Function.update_self]
    rw [hX, hY, t2f]; exact fb
  · show writeBit t2.basis L.point.finite _ L.genericSelect = _
    simp only [writeBit, Function.update_of_ne (Ne.symm fg)]
    rw [Z.2.1 _ gx, T.2.flags _ (by simp [ControlledPointLayout.inPlaceFlags])]
    exact (dialogFlagState_read L hn false false (dialogOrdinary b R (.some hc)) false false false false).2.2.1
  · intro q hx hf hg
    show writeBit t2.basis L.point.finite _ q = s.basis q
    simp only [writeBit, Function.update_of_ne hf]
    rw [Z.2.1 _ hx]
    by_cases hu : q ∈ L.dialogUsedWires
    · rw [used_mem] at hu
      rcases hu with hu | hu | hu | hu
      · simp only [PointAddLayout.pointWires, List.mem_cons, List.mem_append] at hu
        rcases hu with (hu | hu) | hu
        · exact absurd hu hf
        · exact absurd hu hx
        · exact (regValue_eq_iff _ _ _).mp (hp1.2.2.trans hp.2.2.symm) q hu
      · subst hu; exact T.2.control.trans hs.control.symm
      · rw [T.2.flags q hu, hs.flags q hu, dialogFlagState_other L _ q hg]
      · exact (regValue_eq_iff _ _ _).mp (T.2.clean.trans hs.clean.symm) q hu
    · exact t1out q hu

open Classical in
/-- The merged stage and the record stage agree on every dialog boundary state, whatever the
measurement records. -/
theorem stage_run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m m' : List Bool) (hs : PointDialogBoundary L R b (fun _ => false) s.basis) :
    run (stage L (.some hc)) m' s = run (oldStage L (.some hc) cy) m s :=
  Mid.unique (stage_mid L hw hn hc b R s m' hs) (oldStage_mid L hw hn hc b R s m hs)

end Stage


end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinelAux
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- A wire of one instruction of a program is a wire of the program. -/
theorem mem_wires_of_instr {P : Program} {i : Instr} {q : Wire} (hi : i ∈ P) (hq : q ∈ i.wires) :
    q ∈ wires P := by
  induction P with
  | nil => cases hi
  | cons j P ih =>
    simp only [wires, Finset.mem_union]
    rcases List.mem_cons.mp hi with rfl | h
    · exact Or.inl hq
    · exact Or.inr (ih h)

theorem chainAnd_target (c a t : Wire) : t ∈ wires (chainAnd c a t) :=
  mem_wires_of_instr (i := .CCX c a t) (by simp [chainAnd]) (by simp [Instr.wires])

/-- Every work wire of a zero chain is written by the chain. -/
theorem zeroWith_work_mem (T : Wire → Program) (c : Wire) (bs : List ZeroBit) :
    ∀ b ∈ bs, b.work ∈ wires (zeroWith T c bs) := by
  induction bs generalizing c with
  | nil => intro b hb; cases hb
  | cons b bs ih =>
    intro b' hb'
    simp only [zeroWith, wires_append, Finset.mem_union]
    rcases List.mem_cons.mp hb' with rfl | h
    · exact Or.inl (Or.inl (chainAnd_target _ _ _))
    · exact Or.inl (Or.inr (ih b.work b' h))

/-- A wire the innermost step always touches is a wire of the zero chain. -/
theorem zeroWith_tail_mem (T : Wire → Program) (w : Wire) (hT : ∀ h, w ∈ wires (T h)) (c : Wire)
    (bs : List ZeroBit) : w ∈ wires (zeroWith T c bs) := by
  induction bs generalizing c with
  | nil => simpa [zeroWith] using hT c
  | cons b bs ih =>
    simp only [zeroWith, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (ih b.work))

theorem affineClassTail_wa_mem (r y t₁ t₂ t₃ wa wb : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) (h : Wire) :
    wa ∈ wires (affineClassTail r y t₁ t₂ t₃ wa wb e₁ a₁ e₂ a₂ a₃ h) := by
  simp only [affineClassTail, wires_append, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (chainAnd_target _ _ _)))))

/-- Every port's work wire is written by the affine input classifier. -/
theorem affineInputWith_work_mem (y t₁ t₂ t₃ wb : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) :
    ∀ (bs : List ZeroBit) (c : Wire) (a b : Nat), ∀ p ∈ bs,
      p.work ∈ wires (affineInputWith y t₁ t₂ t₃ wb e₁ a₁ e₂ a₂ a₃ c bs a b) := by
  intro bs
  induction bs with
  | nil => intro c a b p hp; cases hp
  | cons q qs ih =>
    intro c a b p hp
    simp only [affineInputWith, wires_append, Finset.mem_union]
    left; right
    split_ifs with hab
    · simp only [wires_append, Finset.mem_union]
      rcases List.mem_cons.mp hp with rfl | h
      · exact Or.inl (Or.inl (chainAnd_target _ _ _))
      · exact Or.inl (Or.inr (ih q.work (a/2) (b/2) p h))
    · simp only [affineInputSuffix, wires_append, Finset.mem_union]
      left; right
      rcases List.mem_cons.mp hp with rfl | h
      · exact zeroWith_tail_mem _ _ (fun h => affineClassTail_wa_mem _ _ _ _ _ _ _ _ _ _ _ _ h) _ _
      · exact zeroWith_work_mem _ _ _ p h

theorem inputClass_pool_mem (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp) :
    ∀ q ∈ L.dialogPool.take 256, q ∈ wires (inputClass L C cy) := by
  intro q hq
  have hmap := (pairPorts_maps L hw).2
  rw [← hmap] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  unfold inputClass
  split_ifs
  · exact affineInputWith_work_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp
  · simp only [pairEqual, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (zeroWith_work_mem _ _ _ p hp))

theorem prefix_generic_mem (L : ControlledPointLayout) (C : Point) :
    L.genericSelect ∈ wires (FusedFlags.prefixProgram L C) := by
  unfold FusedFlags.prefixProgram
  rw [renameProgram_support]
  refine Finset.mem_image.mpr ⟨5, ?_, ?_⟩
  · simp only [FusedFlags.clearPrefix, List.cons_append, wires, Finset.mem_union]
    exact Or.inl (by simp [Instr.wires])
  · rfl

theorem inputClass_counts_ge (L : ControlledPointLayout) (hw : L.Widths) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    258 ≤ toffoliCount (inputClass L (.some hc) cy) ∧
      measurementCount (inputClass L (.some hc) cy) = 256 := by
  have tc : tailCost (decide (cy≠-cy)) (yBit (.some hc)) true (yBit (-(.some hc : Point))) = 1 := by
    rw [cy_ne_neg hc,yBit_neg hc]
    cases yBit (.some hc) <;> decide
  unfold inputClass
  split_ifs with enabled
  · have hh := affineInputWith_counts (yLow L) L.doubleSelect L.genericSelect L.core.equalNegY
      (L.core.poolWire 514) (decide (cy≠-cy)) (yBit (.some hc)) true (yBit (-(.some hc : Point)))
      (yBit (dialogExceptionPoint (.some hc))) L.control (pairPorts L) (pairCode (.some hc))
      (pairCode (dialogExceptionPoint (.some hc)))
    rw [pairPorts_length L hw,tc] at hh
    omega
  · exact False.elim (enabled (NoThreeTorsion.enabled hc))


end ECDSAAdd.Entrant.InputSentinelAux

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section ClassifierFacts
open Challenge
/-! ### Static facts of the merged classifier: wire support, physical gates, counts and slots -/

/-- Bool form of `PhysicalInstr` on gates (the record's `ProperGate`; measurements admitted). -/
def physB : Instr → Bool
  | .X _ => true
  | .CX c t => decide (c ≠ t)
  | .CCX a b t => decide (a ≠ t ∧ b ≠ t)
  | .measureX _ _ _ => true

theorem gatePhysical_of_all (p : Program) (h : p.all physB = true) : GatePhysical p := by
  intro i hi
  have hb := List.all_eq_true.mp h i hi
  cases i <;> simp_all [physB, RecordedQuantum.PhysicalInstr, ProperGate]

theorem decode_physical (a1 a2 b2 yb : Bool) :
    GatePhysical (decode1 a1 a2 b2 yb) ∧ GatePhysical (decode2 a1 a2 b2 yb) := by
  constructor <;> apply gatePhysical_of_all <;>
    cases a1 <;> cases a2 <;> cases b2 <;> cases yb <;> decide

theorem decodeT_physical (tr : Tri) (yb : Bool) : GatePhysical (decodeT tr yb) := by
  unfold decodeT
  split_ifs
  · exact (decode_physical _ _ _ _).1
  · exact (decode_physical _ _ _ _).2

theorem decode_slots (a1 a2 b2 yb : Bool) :
    gateSlots (decode1 a1 a2 b2 yb) ≤ 64 ∧ gateSlots (decode2 a1 a2 b2 yb) ≤ 64 := by
  cases a1 <;> cases a2 <;> cases b2 <;> cases yb <;> decide

theorem decodeT_slots (tr : Tri) (yb : Bool) : gateSlots (decodeT tr yb) ≤ 64 := by
  unfold decodeT
  split_ifs
  · exact (decode_slots _ _ _ _).1
  · exact (decode_slots _ _ _ _).2

theorem tail_support (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire) :
    wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) ⊆ {h, xr1, xr2, y0, c, f, g, g1, wB, t} := by
  unfold tail
  rw [renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have ha10 : a < 10 := Finset.mem_range.mp (decodeT_support tr yb ha)
  simp only [LocalWireModel.label, dif_pos ha10]
  interval_cases a <;> simp

theorem tail_physical (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, g1, wB, t].Nodup) :
    GatePhysical (tail tr yb xr1 xr2 y0 c f g g1 wB t h) := by
  have inj := LocalWireModel.listPorts_injective [h, xr1, xr2, y0, c, f, g, g1, wB, t] hnd
    (n := 10) (by simp)
  unfold tail
  exact gatePhysical_rename_support _ _ (fun a ha b hb e =>
    LocalWireModel.label_injective _ inj a (decodeT_support tr yb ha) b (decodeT_support tr yb hb) e)
    (decodeT_physical tr yb)

theorem tail_counts (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire) :
    toffoliCount (tail tr yb xr1 xr2 y0 c f g g1 wB t h) = 3 ∧
    measurementCount (tail tr yb xr1 xr2 y0 c f g g1 wB t h) = 4 := by
  unfold tail
  rw [(renameProgram_counts _ _).1, (renameProgram_counts _ _).2]
  unfold decodeT
  split_ifs
  · exact ⟨(decode_counts _ _ _ _).1, (decode_counts _ _ _ _).2.1⟩
  · exact ⟨(decode_counts _ _ _ _).2.2.1, (decode_counts _ _ _ _).2.2.2⟩

theorem tail_slots (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire) :
    gateSlots (tail tr yb xr1 xr2 y0 c f g g1 wB t h) = gateSlots (decodeT tr yb) := by
  unfold tail
  exact rename_gateSlots _ _

theorem zeroPorts_mem : ∀ (xs ws : List Wire) (b : ZeroBit), b ∈ zeroPorts xs ws →
    b.input ∈ xs ∧ b.work ∈ ws
  | x :: xs, w :: ws, b, hb => by
    simp only [zeroPorts, List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp
    · have h := zeroPorts_mem xs ws b hb
      exact ⟨List.mem_cons_of_mem _ h.1, List.mem_cons_of_mem _ h.2⟩
  | [], _, b, hb => by simp [zeroPorts] at hb
  | _ :: _, [], b, hb => by simp [zeroPorts] at hb

theorem gateSlots_app (p q : Program) : gateSlots (p ++ q) = gateSlots p + gateSlots q := by
  simp [gateSlots, List.map_append, List.sum_append]

theorem remapBit_sub (tr : Tri) (xr1 xr2 w : Wire) (i : Nat) (U : Finset Wire)
    (h1 : xr1 ∈ U) (h2 : xr2 ∈ U) (hw : w ∈ U) : wires (tr.remapBit xr1 xr2 w i) ⊆ U := by
  unfold Tri.remapBit
  split_ifs <;> simp [wires, Instr.wires, Finset.insert_subset_iff, h1, h2, hw]

theorem remapList_sub (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) (U : Finset Wire)
    (h1 : xr1 ∈ U) (h2 : xr2 ∈ U) (hw : ∀ i ∈ l, w i ∈ U) :
    wires (tr.remapList xr1 xr2 w l) ⊆ U := by
  induction l with
  | nil => simp [Tri.remapList, wires]
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, wires_append] at ih ⊢
    exact Finset.union_subset (remapBit_sub tr xr1 xr2 (w i) i U h1 h2 (hw i (by simp)))
      (ih (fun j hj => hw j (by simp [hj])))

theorem remapBit_physical (tr : Tri) (xr1 xr2 w : Wire) (i : Nat) (h1 : xr1 ≠ w) (h2 : xr2 ≠ w) :
    GatePhysical (tr.remapBit xr1 xr2 w i) := by
  unfold Tri.remapBit
  split_ifs <;> simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, h1, h2]

theorem remapList_physical (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat)
    (h : ∀ i ∈ l, xr1 ≠ w i ∧ xr2 ≠ w i) : GatePhysical (tr.remapList xr1 xr2 w l) := by
  induction l with
  | nil => simp [Tri.remapList, GatePhysical]
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, gatePhysical_append] at ih ⊢
    exact ⟨remapBit_physical tr xr1 xr2 (w i) i (h i (by simp)).1 (h i (by simp)).2,
      ih (fun j hj => h j (by simp [hj]))⟩

theorem remapList_tc (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) :
    toffoliCount (tr.remapList xr1 xr2 w l) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, toffoliCount_append] at ih ⊢
    rw [ih]
    simp only [Tri.remapBit, toffoliCount_append]
    split_ifs <;> rfl

theorem remapBit_slots (tr : Tri) (xr1 xr2 w : Wire) (i : Nat) :
    gateSlots (tr.remapBit xr1 xr2 w i) ≤ 3 := by
  unfold Tri.remapBit
  split_ifs <;> simp [gateSlots, instructionSlots]

theorem remapList_slots (tr : Tri) (xr1 xr2 : Wire) (w : Nat → Wire) (l : List Nat) :
    gateSlots (tr.remapList xr1 xr2 w l) ≤ 3 * l.length := by
  induction l with
  | nil => simp [Tri.remapList, gateSlots]
  | cons i l ih =>
    simp only [Tri.remapList, List.flatMap_cons, gateSlots_app, List.length_cons] at ih ⊢
    have := remapBit_slots tr xr1 xr2 (w i) i
    omega

/-- A zero chain stays inside any wire set that holds its control, ports and every innermost step. -/
theorem zeroWith_sub (T : Wire → Program) (U : Finset Wire) (hT : ∀ h ∈ U, wires (T h) ⊆ U) :
    ∀ (c : Wire) (bs : List ZeroBit), c ∈ U → (∀ b ∈ bs, b.input ∈ U ∧ b.work ∈ U) →
      wires (zeroWith T c bs) ⊆ U := by
  intro c bs
  induction bs generalizing c with
  | nil => intro hc _; simpa [zeroWith] using hT c hc
  | cons b bs ih =>
    intro hc hb
    have hb0 := hb b (by simp)
    simp only [zeroWith, wires_append]
    refine Finset.union_subset (Finset.union_subset ?_ (ih b.work hb0.2 (fun b' h => hb b' (by simp [h])))) ?_
    · simp [chainAnd, wires, Instr.wires, Finset.insert_subset_iff, hc, hb0.1, hb0.2]
    · simp [chainErase, wires, Instr.wires, correctionWires, Finset.insert_subset_iff, hc, hb0.1, hb0.2]

/-- A zero chain is physical when its chain wires are distinct, each input differs from its work
wire, and every innermost step it can reach is physical. -/
theorem zeroWith_physical (T : Wire → Program) :
    ∀ (c : Wire) (bs : List ZeroBit), (c :: bs.map ZeroBit.work).Nodup → (∀ b ∈ bs, b.input ≠ b.work) →
      (∀ h ∈ c :: bs.map ZeroBit.work, GatePhysical (T h)) → GatePhysical (zeroWith T c bs) := by
  intro c bs
  induction bs generalizing c with
  | nil => intro _ _ hT; simpa [zeroWith] using hT c (by simp)
  | cons b bs ih =>
    intro hn hio hT
    simp only [List.map_cons] at hn hT
    have hcw : c ≠ b.work := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
    have hn' : (b.work :: bs.map ZeroBit.work).Nodup := (List.nodup_cons.mp hn).2
    have hiw := hio b (by simp)
    simp only [zeroWith, gatePhysical_append]
    refine ⟨⟨?_, ih b.work hn' (fun b' h => hio b' (by simp [h]))
      (fun h hh => hT h (List.mem_cons_of_mem _ hh))⟩, ?_⟩
    · simp [chainAnd, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hcw, hiw]
    · simp [chainErase, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]

theorem zeroWith_slots (T : Wire → Program) (n : Nat) (hT : ∀ h, gateSlots (T h) = n) :
    ∀ (c : Wire) (bs : List ZeroBit), gateSlots (zeroWith T c bs) = 7 * bs.length + n := by
  intro c bs
  induction bs generalizing c with
  | nil => simp [zeroWith, hT]
  | cons b bs ih =>
    simp only [zeroWith, gateSlots_app, ih, List.length_cons]
    simp [chainAnd, chainErase, gateSlots, instructionSlots]
    omega

/-- The classifier's index list starts with a non-pivot bit and has 253 more. -/
theorem idx_split (tr : Tri) (v : tr.Valid) : ∃ i0 it, tr.idx = i0 :: it ∧ it.length = 253 := by
  have hl := (Tri.idx_facts v).2.1
  cases h : tr.idx with
  | nil => rw [h] at hl; simp at hl
  | cons a l => rw [h] at hl; exact ⟨a, l, rfl, by simpa using hl⟩

theorem classifier_support (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire) (hxl : xs.length = 256) (_hwl : work.length = 253) :
    wires (classifier tr yb xs work y0 c f g g1 wB t) ⊆
      xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, g1, wB, t} := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  let U : Finset Wire := xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, g1, wB, t}
  have xsU : ∀ i, i < 256 → xs.getD i 0 ∈ U := by
    intro i hi
    have hm : xs.getD i 0 ∈ xs := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    simp only [U, Finset.mem_union, List.mem_toFinset]
    exact Or.inl (Or.inl hm)
  have workU : ∀ q ∈ work, q ∈ U := fun q hq => by simp [U, hq]
  have r1U := xsU _ pv.1
  have r2U := xsU _ pv.2.1
  have idxU : ∀ i ∈ tr.idx, xs.getD i 0 ∈ U := fun i hi => xsU i (ix.2.2.2.2 i hi)
  have PU : ∀ q ∈ tr.idx.map (fun i => xs.getD i 0), q ∈ U := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; exact idxU i hi
  have h0U : (tr.idx.map (fun i => xs.getD i 0)).headD 0 ∈ U := by
    rw [hidx]; exact idxU i0 (by rw [hidx]; simp)
  have portsU : ∀ b ∈ zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work,
      b.input ∈ U ∧ b.work ∈ U := by
    intro b hb
    have hm := zeroPorts_mem _ _ b hb
    exact ⟨PU _ (List.mem_of_mem_tail hm.1), workU _ hm.2⟩
  have extU : ∀ q ∈ ({y0, c, f, g, g1, wB, t} : Finset Wire), q ∈ U := by
    intro q hq; simp only [U, Finset.mem_union]; exact Or.inr hq
  have tailU : ∀ h ∈ U,
      wires (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t h) ⊆ U := by
    intro h hh
    refine (tail_support tr yb _ _ y0 c f g g1 wB t h).trans ?_
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hh, r1U, r2U, extU y0 (by simp), extU c (by simp), extU f (by simp), extU g (by simp),
      extU g1 (by simp), extU wB (by simp), extU t (by simp)⟩
  have remapU := remapList_sub tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx U
    r1U r2U idxU
  have zU := zeroWith_sub _ U tailU _ _ h0U portsU
  have xU : wires [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ⊆ U := by
    generalize (tr.idx.map (fun i => xs.getD i 0)).headD 0 = h0 at h0U ⊢
    intro q hq
    simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton] at hq
    rcases hq with rfl | hq
    · exact h0U
    · simp at hq
  intro q hq
  simp only [classifier, wires_append, Finset.mem_union] at hq
  rcases hq with h | h | h | h | h
  · exact remapU h
  · exact xU h
  · exact zU h
  · exact xU h
  · exact remapU h

theorem classifier_physical (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire) (hxl : xs.length = 256) (hwl : work.length = 253)
    (hxn : xs.Nodup) (hwn : work.Nodup) (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, g1, wB, t].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, g1, wB, t], q ∉ xs ∧ q ∉ work) :
    GatePhysical (classifier tr yb xs work y0 c f g g1 wB t) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have winj : ∀ i j, i < 256 → j < 256 → xs.getD i 0 = xs.getD j 0 → i = j := by
    intro i j hi hj e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact hxn.getElem_inj_iff.mp e
  have wmem : ∀ i, i < 256 → xs.getD i 0 ∈ xs := by
    intro i hi; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hi0 : i0 ∈ tr.idx := by rw [hidx]; simp
  have i0lt := ix.2.2.2.2 i0 hi0
  have i0r1 : i0 ≠ tr.r1 := fun e => ix.2.2.1 (e ▸ hi0)
  have i0r2 : i0 ≠ tr.r2 := fun e => ix.2.2.2.1 (e ▸ hi0)
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  -- the remap's CX controls are the pivot wires, never a remapped wire
  have remapP : GatePhysical (tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx) := by
    apply remapList_physical
    intro i hi
    have hi256 := ix.2.2.2.2 i hi
    refine ⟨fun e => ix.2.2.1 ((winj _ _ pv.1 hi256 e) ▸ hi), fun e => ix.2.2.2.1 ((winj _ _ pv.2.1 hi256 e) ▸ hi)⟩
  -- the zero chain: control `xs[i0]`, inputs the other non-pivot bits, works the pool wires
  have hP0 : (tr.idx.map (fun i => xs.getD i 0)).headD 0 = xs.getD i0 0 := by rw [hidx]; rfl
  have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by rw [hidx]; rfl
  have x0x : xs.getD i0 0 ∈ xs := wmem i0 i0lt
  have hused : [xs.getD tr.r1 0, xs.getD tr.r2 0, y0, c, f, g, g1, wB, t].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, not_or]
      refine ⟨fun e => pv.2.2.1 (winj _ _ pv.1 pv.2.1 e), ?_⟩
      have hx1 := wmem _ pv.1
      refine ⟨fun e => (hextx y0 (by simp)).1 (e ▸ hx1), fun e => (hextx c (by simp)).1 (e ▸ hx1),
        fun e => (hextx f (by simp)).1 (e ▸ hx1), fun e => (hextx g (by simp)).1 (e ▸ hx1),
        fun e => (hextx g1 (by simp)).1 (e ▸ hx1), fun e => (hextx wB (by simp)).1 (e ▸ hx1),
        fun e => (hextx t (by simp)).1 (e ▸ hx1), by simp⟩
    · simp only [List.mem_cons, not_or]
      have hx2 := wmem _ pv.2.1
      exact ⟨fun e => (hextx y0 (by simp)).1 (e ▸ hx2), fun e => (hextx c (by simp)).1 (e ▸ hx2),
        fun e => (hextx f (by simp)).1 (e ▸ hx2), fun e => (hextx g (by simp)).1 (e ▸ hx2),
        fun e => (hextx g1 (by simp)).1 (e ▸ hx2), fun e => (hextx wB (by simp)).1 (e ▸ hx2),
        fun e => (hextx t (by simp)).1 (e ▸ hx2), by simp⟩
  -- any chain wire (the control `xs[i0]` or a pool wire) is off the tail's other nine wires
  have hout : ∀ h, (h = xs.getD i0 0 ∨ h ∈ work) → h ∉ [xs.getD tr.r1 0, xs.getD tr.r2 0, y0, c, f, g, g1, wB, t] := by
    intro h hh hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hh with rfl | hw
    · rcases hm with e | e | e | e | e | e | e | e | e
      · exact i0r1 (winj _ _ i0lt pv.1 e)
      · exact i0r2 (winj _ _ i0lt pv.2.1 e)
      all_goals first
        | exact (hextx y0 (by simp)).1 (e ▸ x0x) | exact (hextx c (by simp)).1 (e ▸ x0x)
        | exact (hextx f (by simp)).1 (e ▸ x0x) | exact (hextx g (by simp)).1 (e ▸ x0x)
        | exact (hextx g1 (by simp)).1 (e ▸ x0x) | exact (hextx wB (by simp)).1 (e ▸ x0x)
        | exact (hextx t (by simp)).1 (e ▸ x0x)
    · rcases hm with e | e | e | e | e | e | e | e | e
      · exact hdisj h hw (e ▸ wmem _ pv.1)
      · exact hdisj h hw (e ▸ wmem _ pv.2.1)
      all_goals first
        | exact (hextx y0 (by simp)).2 (e ▸ hw) | exact (hextx c (by simp)).2 (e ▸ hw)
        | exact (hextx f (by simp)).2 (e ▸ hw) | exact (hextx g (by simp)).2 (e ▸ hw)
        | exact (hextx g1 (by simp)).2 (e ▸ hw) | exact (hextx wB (by simp)).2 (e ▸ hw)
        | exact (hextx t (by simp)).2 (e ▸ hw)
  have zP : GatePhysical (zeroWith (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)) := by
    rw [hP0, hPt]
    apply zeroWith_physical
    · rw [zp.2]
      exact List.nodup_cons.mpr ⟨fun hm => hdisj _ hm x0x, hwn⟩
    · intro b hb e
      have hm := zeroPorts_mem _ _ b hb
      obtain ⟨i, hi, hie⟩ := List.mem_map.mp hm.1
      have hit : i ∈ tr.idx := by rw [hidx]; simp [hi]
      exact hdisj _ hm.2 (e ▸ hie ▸ wmem i (ix.2.2.2.2 i hit))
    · intro h hh
      rw [zp.2] at hh
      apply tail_physical
      exact List.nodup_cons.mpr ⟨hout h (by simpa using hh), hused⟩
  have xP : GatePhysical [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] := by
    simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]
  unfold classifier
  simp only [gatePhysical_append]
  exact ⟨remapP, xP, zP, xP, remapP⟩

theorem classifier_counts (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire) (hwl : work.length = 253) :
    toffoliCount (classifier tr yb xs work y0 c f g g1 wB t) = 256 ∧
    measurementCount (classifier tr yb xs work y0 c f g g1 wB t) = 257 ∧
    gateSlots (classifier tr yb xs work y0 c f g g1 wB t) ≤ 4000 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zc := zeroWith_counts_general (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t) 3 4
    (fun h => tail_counts tr yb _ _ y0 c f g g1 wB t h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc
  have zs := zeroWith_slots (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t)
    (gateSlots (decodeT tr yb)) (fun h => tail_slots tr yb _ _ y0 c f g g1 wB t h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := decodeT_slots tr yb
  have rt := remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold classifier
  simp only [toffoliCount_append, measurementCount_append, gateSlots_app, rt, rm, zc.1, zc.2, zs]
  refine ⟨by simp [toffoliCount], by simp [measurementCount], ?_⟩
  simp only [gateSlots, instructionSlots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at rs ds ⊢
  omega

/-- The tightest uniform slot bound: 3 slots a remapped bit twice, the two flips, 7 a chain rung,
and the 64-slot worst decode tail. -/
theorem classifier_slots (tr : Tri) (v : tr.Valid) (yb : Bool) (xs work : List Wire)
    (y0 c f g g1 wB t : Wire) (hwl : work.length = 253) :
    gateSlots (classifier tr yb xs work y0 c f g g1 wB t) ≤ 3361 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zs := zeroWith_slots (tail tr yb (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g g1 wB t)
    (gateSlots (decodeT tr yb)) (fun h => tail_slots tr yb _ _ y0 c f g g1 wB t h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := decodeT_slots tr yb
  unfold classifier
  simp only [gateSlots_app, zs]
  simp only [gateSlots, instructionSlots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at rs ds ⊢
  omega


end ClassifierFacts


end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section Splice
open Secp256k1 ControlledPointLayout

/-- The record generic block after its input clear. -/
def tailGen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (swapF L) (CodexYParityProbe.generic L cx cy) ++ CodexYParityProbe.clrF L ++
    FiniteFlagInterval.zrep L

/-- The part of the finite program after the input stage. -/
def shared (L : ControlledPointLayout) (C : Point) (Gen : Program) : Program :=
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ++
    FusedFlags.suffixProgram L C ++
  renameProgram (sigP L) (corners2 L C ++ Edges.sharedM L C) ++
  chainErase L.control L.point.finite L.genericSelect

/-- Finite program with the merged input stage. -/
def finiteProgram' (L : ControlledPointLayout) (C : Point) (Gen : Program) : Program :=
  stage L C ++ shared L C Gen

def wrapper' (L : ControlledPointLayout) (C : Point) (Gen : Program) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram' L C (renameProgram (Wrapper5.U L) Gen))

theorem gen_split (L : ControlledPointLayout) (cx cy : Fp) :
    CodexYParityProbe.gen L cx cy =
      FiniteFlagInterval.zrep L ++ CodexYParityProbe.clearF L ++ tailGen L cx cy := by
  simp only [CodexYParityProbe.gen, CodexYParityProbe.mid, tailGen, List.append_assoc]

/-- Wire numbers of the relabelled sites in the concrete layout. -/
theorem special_wires :
    (layout.core.poolWire 684 : Nat) = 4799 ∧ (layout.core.poolWire 717 : Nat) = 4832 ∧
    (spareD layout : Nat) = 5655 ∧ (layout.core.generic : Nat) = 4113 ∧
    (layout.genericSelect : Nat) = 9814 ∧ (layout.core.equalNegY : Nat) = 4112 ∧
    (layout.doubleSelect : Nat) = 9815 := by
  decide +kernel

/-- The finite flag, both coordinates and the first 255 pool sites avoid the relabelled sites. -/
theorem fix_range : ∀ w ∈ layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255 ++
    layout.point.y), (w : Nat) < 514 ∨ (4115 ≤ (w : Nat) ∧ (w : Nat) < 4370) := by
  decide +kernel

theorem wire_ne {w k : Nat} (r : w < 514 ∨ (4115 ≤ w ∧ w < 4370))
    (hk : (514 ≤ k ∧ k < 4115) ∨ 4370 ≤ k) : w ≠ k := by
  omega

/-- The four relabellings fix the finite flag, both coordinates and the first 255 pool sites. -/
theorem fix_maps : ∀ w ∈ layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255 ++
    layout.point.y), Wrapper5.U layout w = w ∧ tauM layout w = w ∧ swapE layout w = w ∧
      swapD layout w = w := by
  intro w hw
  have r := fix_range w hw
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := special_wires
  have n1 : w ≠ layout.core.poolWire 684 := wire_ne r (by rw [p1]; decide)
  have n2 : w ≠ layout.core.poolWire 717 := wire_ne r (by rw [p2]; decide)
  have n3 : w ≠ spareD layout := wire_ne r (by rw [p3]; decide)
  have n4 : w ≠ layout.core.generic := wire_ne r (by rw [p4]; decide)
  have n5 : w ≠ layout.genericSelect := wire_ne r (by rw [p5]; decide)
  have n6 : w ≠ layout.core.equalNegY := wire_ne r (by rw [p6]; decide)
  have n7 : w ≠ layout.doubleSelect := wire_ne r (by rw [p7]; decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Wrapper5.U, Equiv.swap_apply_of_ne_of_ne n1 n2]
  · unfold tauM
    rw [if_neg n4, if_neg n5]
  · unfold swapE spareWire
    rw [if_neg n6, if_neg n1]
  · unfold swapD
    rw [if_neg n7, if_neg n3]

theorem fix_sub (P : Program)
    (h : wires P ⊆ (layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255)).toFinset ∪
      layout.point.y.toFinset) :
    renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) P))) = P := by
  have mem : ∀ w ∈ wires P, w ∈ layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255 ++
      layout.point.y) := by
    intro w hw
    rcases Finset.mem_union.mp (h hw) with a | a
    · simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at a ⊢; tauto
    · simp only [List.mem_toFinset] at a
      simp only [List.mem_cons, List.mem_append]; tauto
  have hU : renameProgram (Wrapper5.U layout) P = P :=
    rename_fix _ P (fun w hw => (fix_maps w (mem w hw)).1)
  have hM : renameProgram (tauM layout) P = P :=
    rename_fix _ P (fun w hw => (fix_maps w (mem w hw)).2.1)
  have hE : renameProgram (swapE layout) P = P :=
    rename_fix _ P (fun w hw => (fix_maps w (mem w hw)).2.2.1)
  have hD : renameProgram (swapD layout) P = P :=
    rename_fix _ P (fun w hw => (fix_maps w (mem w hw)).2.2.2)
  rw [hU, hM, hE, hD]

theorem zrep_fixed :
    renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (FiniteFlagInterval.zrep layout)))) =
      FiniteFlagInterval.zrep layout := by
  apply fix_sub
  rw [← FiniteFlagInterval.old_clrF_support layout layout_widths]
  exact (FiniteFlagInterval.zrep_support_old layout layout_widths).trans Finset.subset_union_left

theorem clearF_fixed :
    renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (CodexYParityProbe.clearF layout)))) =
      CodexYParityProbe.clearF layout := by
  apply fix_sub
  rw [← FiniteFlagInterval.old_clrF_support layout layout_widths]
  exact CodexYParityProbe.clearF_support_old layout layout_widths

theorem old_split {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    FusedFlags.finiteProgram layout (.some hc) cy
      (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy)) =
      oldStage layout (.some hc) cy ++
        shared layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy)) := by
  have hz := zrep_fixed
  have hf := clearF_fixed
  simp only [FusedFlags.rename_append] at hz hf
  rw [gen_split]
  simp only [FusedFlags.finiteProgram, oldStage, shared, FusedFlags.rename_append, hz, hf,
    List.append_assoc]

theorem new_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m' : List Bool)
    (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    run (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) m' s =
      run (FusedFlags.finiteProgram layout (.some hc) cy
        (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy)))
        (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
          m'.drop (measurementCount (stage layout (.some hc)))) s := by
  have hd : (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
      m'.drop (measurementCount (stage layout (.some hc)))).drop
        (measurementCount (oldStage layout (.some hc) cy)) =
      m'.drop (measurementCount (stage layout (.some hc))) := List.drop_left' (by simp)
  rw [old_split hc, finiteProgram', LocalWireModel.run_concat, LocalWireModel.run_concat, hd,
    stage_run_eq layout layout_widths layout_nodup hc b R s
      (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
        m'.drop (measurementCount (stage layout (.some hc)))) m' hs]

theorem wrapper'_eq {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m' : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    run (wrapper' layout (.some hc) (tailGen layout cx cy)) m' s =
      run (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy))
        (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
          m'.drop (measurementCount (stage layout (.some hc)))) s := by
  have hGen := CodexYParityProbe.genFFused_ok layout layout_widths layout_nodup hc
  have hsI := Edges.finite_specWith layout layout_widths layout_nodup R hc b
    (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy))
    (Wrapper5.genericOK_relabel layout layout_widths hc _ hGen)
    (FusedFlags.adapterProgram layout (.some hc) true) (FusedFlags.adapterProgram layout (.some hc) false)
    (fun R b D G H cov old => FusedFlags.boundary_step layout layout_widths layout_nodup hc true R b D G H
      false false cov (fun _ => ⟨rfl,rfl⟩) (by simp) old)
    (fun R b G D H cov old => FusedFlags.boundary_step layout layout_widths layout_nodup hc false R b false G
      false D H cov (by simp) (fun _ => ⟨rfl,rfl⟩) old)
  have h := hsI s (List.replicate (measurementCount (oldStage layout (.some hc) cy)) false ++
    m'.drop (measurementCount (stage layout (.some hc)))) hs
  rw [FusedFlags.finite_run layout layout_widths layout_nodup] at h
  have e := new_run hc b R s m' hs
  unfold wrapper' FusedFlags.wrapper
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
      (Wrapper5.U_outside layout layout_widths) (FusedFlags.finiteProgram layout (.some hc) cy
        (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy))) s _ hs.clean h.2.clean,
    Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
      (Wrapper5.U_outside layout layout_widths) (finiteProgram' layout (.some hc)
        (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) s m' hs.clean (by rw [e]; exact h.2.clean)]
  exact e

theorem full_spec' {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapper' layout (.some hc) (tailGen layout cx cy)
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m' hs
  have hz : regValue layout.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi : PointDialogBoundary layout R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  rw [wrapper'_eq hc b R s m' hi]
  exact FusedFlags.full_spec layout layout_widths layout_nodup R hc b _
    (CodexYParityProbe.genFFused_ok layout layout_widths layout_nodup hc)
    (CodexYParityProbe.gen_sites layout layout_widths layout_nodup cx cy) s _ hs

theorem counts_rel {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        toffoliCount (oldStage layout (.some hc) cy) =
      toffoliCount (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) +
        toffoliCount (stage layout (.some hc)) ∧
    measurementCount (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        measurementCount (oldStage layout (.some hc) cy) =
      measurementCount (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) +
        measurementCount (stage layout (.some hc)) ∧
    Challenge.gateSlots (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        Challenge.gateSlots (oldStage layout (.some hc) cy) =
      Challenge.gateSlots (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) +
        Challenge.gateSlots (stage layout (.some hc)) := by
  unfold wrapper' FusedFlags.wrapper
  rw [old_split hc]
  simp only [renameProgram_counts, rename_gateSlots, finiteProgram', toffoliCount_append,
    measurementCount_append, Challenge.gateSlots_append]
  omega

theorem oldStage_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    503 ≤ toffoliCount (oldStage layout (.some hc) cy) ∧
      measurementCount (oldStage layout (.some hc) cy) = 504 := by
  obtain ⟨i1, i2⟩ := InputSentinelAux.inputClass_counts_ge layout layout_widths hc
  have pr := FusedFlags.counts (DHClass.cxk (.some hc)) (yBit (.some hc))
  have pt := renameProgram_counts (LocalWireModel.label (FusedFlags.ports layout (DHClass.kx (.some hc))))
    (FusedFlags.clearPrefix (DHClass.cxk (.some hc)) (yBit (.some hc)))
  have z := FiniteFlagInterval.zrep_counts layout
  have c := CodexYParityProbe.counts layout layout_widths
  simp only [oldStage, FusedFlags.prefixProgram, toffoliCount_append, measurementCount_append, pt.1, pt.2,
    pr.1, pr.2.2.1, z.1, z.2, c.2.2.1, c.2.2.2, i2]
  exact ⟨by omega, trivial⟩

end Splice

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

section Cert
open Secp256k1 Challenge ControlledPointLayout
attribute [local irreducible] wires

theorem pool_take_mem (i : Nat) (hi : i < 256) : layout.dialogPool.getD i 0 ∈ layout.dialogPool.take 256 := by
  have hpl := dialogPool_length layout layout_widths
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩

theorem stage_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (stage layout (.some hc)) ⊆ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset ∪
      ({layout.genericSelect} ∪ (layout.dialogPool.take 256).toFinset) := by
  have hz : wires (FiniteFlagInterval.zrep layout) ⊆
      (layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255)).toFinset := by
    rw [← FiniteFlagInterval.old_clrF_support layout layout_widths]
    exact FiniteFlagInterval.zrep_support_old layout layout_widths
  have hcl := classifier_support (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) layout_widths.inputX (by simp [dialogPool_length layout layout_widths])
  have yl := yLow_mem layout layout_widths
  have hpl := dialogPool_length layout layout_widths
  have tk : ∀ n, n ≤ 256 → ∀ q ∈ layout.dialogPool.take n, q ∈ layout.dialogPool.take 256 := by
    intro n hn q hq
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    rw [← e]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  intro q hq
  unfold stage at hq
  rw [wires_append, Finset.mem_union] at hq
  simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset, List.mem_append,
    PointAddLayout.pointWires, List.mem_cons, List.mem_singleton]
  rcases hq with h | h
  · have h' := hz h
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at h'
    rcases h' with h' | h' | h'
    · exact Or.inl (Or.inl (Or.inl (Or.inl h')))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h')))
    · exact Or.inr (Or.inr (tk 255 (by decide) q h'))
  · have h' := hcl h
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at h'
    rcases h' with (h' | h') | h' | h' | h' | h' | h' | h' | h'
    · exact Or.inl (Or.inl (Or.inl (Or.inr h')))
    · exact Or.inr (Or.inr (tk 253 (by decide) q h'))
    · subst h'; exact Or.inl (Or.inl (Or.inr yl))
    · exact Or.inl (Or.inr (Or.inl h'))
    · exact Or.inl (Or.inl (Or.inl (Or.inl h')))
    · exact Or.inr (Or.inl h')
    · subst h'; exact Or.inr (Or.inr (pool_take_mem 253 (by decide)))
    · subst h'; exact Or.inr (Or.inr (pool_take_mem 254 (by decide)))
    · subst h'; exact Or.inr (Or.inr (pool_take_mem 255 (by decide)))

theorem stage_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (stage layout (.some hc)) = 256 ∧ measurementCount (stage layout (.some hc)) = 257 ∧
      Challenge.gateSlots (stage layout (.some hc)) ≤ 3619 := by
  have c := classifier_counts (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) (by simp [dialogPool_length layout layout_widths])
  have sl := classifier_slots (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
    layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
    layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) (by simp [dialogPool_length layout layout_widths])
  have z := FiniteFlagInterval.zrep_counts layout
  have zs := FiniteFlagInterval.zrep_slots layout layout_widths
  unfold stage
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append, z.1, z.2, c.1, c.2.1]
  exact ⟨trivial, trivial, by omega⟩

theorem stage_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (stage layout (.some hc)) := by
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, hext, hextx⟩ := stage_layout layout layout_widths layout_nodup
  unfold stage
  rw [gatePhysical_append]
  exact ⟨FiniteFlagInterval.zrep_physical layout layout_nodup,
    classifier_physical (triOf (.some hc)) (triOf_valid hc) (yBit (dialogExceptionPoint (.some hc)))
      layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite
      layout.genericSelect (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
      (layout.dialogPool.getD 255 0) hxl hwl hxn hwn hdisj hext hextx⟩

theorem io_mem (w : Wire) (h : w ∈ PointAddLayout.pointWires layout.point ++ [layout.control]) :
    w ∈ ioWires := by
  rcases List.mem_append.mp h with hp | hc
  · rw [Baselines.point_wires] at hp
    exact Finset.mem_range.mpr (List.mem_range'_1.mp hp).2
  · rw [List.mem_singleton] at hc
    subst hc
    exact Finset.mem_range.mpr (by decide)

theorem io_not_pool (w : Wire) (h : w ∈ PointAddLayout.pointWires layout.point ++ [layout.control]) :
    w ∉ layout.dialogPool := by
  have hD := layout.dialogUsed_nodup layout_nodup
  intro hp
  have c := List.nodup_iff_count_le_one.mp hD w
  have c1 : 1 ≤ (PointAddLayout.pointWires layout.point ++ [layout.control]).count w :=
    List.count_pos_iff.mpr h
  have c2 : 1 ≤ layout.dialogPool.count w := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.dialogUsedWires, List.count_append] at c c1
  omega

theorem finite_sub {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) ⊆
      wires (FusedFlags.finiteProgram layout (.some hc) cy
        (renameProgram (Wrapper5.U layout) (CodexYParityProbe.gen layout cx cy))) ∪
        (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
  rw [old_split hc, finiteProgram', wires_append, wires_append]
  apply Finset.union_subset
  · intro w hst
    rcases Finset.mem_union.mp (stage_support hc hst) with ht | hx
    · exact Finset.mem_union_right _ ht
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp only [oldStage, wires_append, Finset.mem_union]
      rcases Finset.mem_union.mp hx with hg | hp
      · rw [Finset.mem_singleton] at hg
        subst hg
        exact Or.inl (Or.inl (Or.inr (InputSentinelAux.prefix_generic_mem layout _)))
      · exact Or.inl (Or.inl (Or.inl
          (InputSentinelAux.inputClass_pool_mem layout layout_widths _ cy w (List.mem_toFinset.mp hp))))
  · exact fun w h => Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem wrapper'_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper' layout (.some hc) (tailGen layout cx cy)) ⊆
      wires (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ∪
        (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
  unfold wrapper' FusedFlags.wrapper
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (finite_sub hc hw) with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  · apply Finset.mem_union_right
    rw [Wrapper5.U_outside layout layout_widths w (io_not_pool w (List.mem_toFinset.mp h))]
    exact h

theorem support_used' {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper' layout (.some hc) (tailGen layout cx cy)) ⊆ layout.dialogUsedWires.toFinset := by
  have sites := CodexYParityProbe.gen_sites layout layout_widths layout_nodup cx cy
  have old := ((FusedFlags.wrapper_support layout hc (CodexYParityProbe.gen layout cx cy)).trans
    (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)).trans
      (WrapperOB5.support_used layout layout_widths)
  intro q hq
  rcases Finset.mem_union.mp (wrapper'_support hc hq) with o | t
  · exact old o
  · have t' := List.mem_toFinset.mp t
    apply List.mem_toFinset.mpr
    unfold ControlledPointLayout.dialogUsedWires
    exact List.mem_append_left _ (List.mem_append_left _ t')

theorem wrapper'_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapper' layout (.some hc) (tailGen layout cx cy)) := by
  have old := FusedFlags.wrapper_physical layout layout_widths layout_nodup (.some hc) cy _
    (CodexYParityProbe.gen_physical layout layout_widths layout_nodup cx cy)
  unfold FusedFlags.wrapper at old
  rw [R2SqEp760.gatePhysical_rename_iff, old_split hc, gatePhysical_append] at old
  unfold wrapper'
  rw [R2SqEp760.gatePhysical_rename_iff, finiteProgram', gatePhysical_append]
  exact ⟨stage_physical hc, old.2⟩

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => wrapper' layout C (tailGen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2150781, 1498614, 1587, 50242569⟩

theorem program_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    exact fixed_correct _ control R _ (full_spec' hc control R) (support_used' hc)

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2150781 := by
  cases C with
  | zero => simp [program, toffoliCount]
  | @some cx cy hc =>
    have r := (counts_rel hc).1
    have o := (oldStage_counts hc).1
    have st := (stage_counts hc).1
    have old := CodexYParityProbe.program_toffoli (.some hc)
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ≤
      2151028 at old
    change toffoliCount (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 2150781
    omega

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1498614 := by
  cases C with
  | zero => simp [program, measurementCount]
  | @some cx cy hc =>
    have r := (counts_rel hc).2.1
    have o := (oldStage_counts hc).2
    have st := (stage_counts hc).2.1
    have old := CodexYParityProbe.program_measurements (.some hc)
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ≤
      1498861 at old
    change measurementCount (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 1498614
    omega

theorem program_qubits (C : Point) : qubits (program C) ≤ 1587 := by
  cases C with
  | zero => change qubits [] ≤ 1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have sub := wrapper'_support hc
    have old := CodexYParityProbe.program_qubits (.some hc)
    change qubits (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ≤ 1587 at old
    change qubits (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 1587
    refine le_trans (Finset.card_le_card ?_) old
    intro q hq
    rcases Finset.mem_union.mp hq with io | used
    · exact Finset.mem_union_left _ io
    · rcases Finset.mem_union.mp (sub used) with o | t
      · exact Finset.mem_union_right _ o
      · apply Finset.mem_union_left
        exact io_mem q (List.mem_toFinset.mp t)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program, GatePhysical]
  | @some cx cy hc => exact wrapper'_physical hc

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50242569 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have r := (counts_rel hc).2.2
    have st := (stage_counts hc).2.2
    have old := CodexYParityProbe.program_gateSlots (.some hc)
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (CodexYParityProbe.gen layout cx cy)) ≤
      50238950 at old
    change gateSlots (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 50242569
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1498614
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50242569
    rw [normalize_slots]; exact program_gateSlots C

end Cert

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section OutputGadgets

/-- Little-endian word of a bit list. -/
def ofBits : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBits bs

/-! Corner flag decode on local wires: 0 generic select (left holding the inverse flag), 1 control,
2 `x_r1`, 3 `x_r2`, 4 `y0`, 5 infinity flag, 6 double flag, 7 exception flag. -/

/-- Role 1: `x_r1` isolates `(-2C).x` (value `b1`), then `x_r2` isolates the sentinel (`s2`). -/
def predec1 (b1 s2 yc : Bool) : Program :=
  [.CX 1 0] ++ lit 2 b1 ++ [.CCX 0 2 7] ++ lit 2 b1 ++ [.CX 7 0] ++
  lit 3 s2 ++ [.CCX 0 3 5] ++ lit 3 s2 ++ [.CX 5 0] ++
  lit 4 yc ++ [.CCX 0 4 6] ++ lit 4 yc ++ [.CX 6 0]

/-- Role 2: `x_r1` isolates the sentinel (value `s1`), then `x_r2` isolates `(-2C).x` (`b2`). -/
def predec2 (s1 b2 yc : Bool) : Program :=
  [.CX 1 0] ++ lit 2 s1 ++ [.CCX 0 2 5] ++ lit 2 s1 ++ [.CX 5 0] ++
  lit 3 b2 ++ [.CCX 0 3 7] ++ lit 3 b2 ++ [.CX 7 0] ++
  lit 4 yc ++ [.CCX 0 4 6] ++ lit 4 yc ++ [.CX 6 0]

def predOut1 (b1 s2 yc : Bool) (x : Nat) : Nat :=
  let n := x.testBit 0 ^^ x.testBit 1
  let pB := x.testBit 2 == b1
  let pS := !pB && (x.testBit 3 == s2)
  let yC := x.testBit 4 == yc
  ofBits [n && !pB && !pS && !yC, x.testBit 1, x.testBit 2, x.testBit 3, x.testBit 4,
    n && pS, n && !pB && !pS && yC, n && pB]

def predOut2 (s1 b2 yc : Bool) (x : Nat) : Nat :=
  let n := x.testBit 0 ^^ x.testBit 1
  let pS := x.testBit 2 == s1
  let pB := !pS && (x.testBit 3 == b2)
  let yC := x.testBit 4 == yc
  ofBits [n && !pS && !pB && !yC, x.testBit 1, x.testBit 2, x.testBit 3, x.testBit 4,
    n && pS, n && !pS && !pB && yC, n && pB]

theorem predec1_ok : ∀ b1 s2 yc : Bool, ∀ x : Fin 32,
    safe (predec1 b1 s2 yc) x.val = true ∧ bitRun (predec1 b1 s2 yc) x.val = predOut1 b1 s2 yc x.val := by
  decide +kernel

theorem predec2_ok : ∀ s1 b2 yc : Bool, ∀ x : Fin 32,
    safe (predec2 s1 b2 yc) x.val = true ∧ bitRun (predec2 s1 b2 yc) x.val = predOut2 s1 b2 yc x.val := by
  decide +kernel

/-! Output tail on local wires: 0 `h` (zero-test bit), 1 `x_r1`, 2 `x_r2`, 3 `y0`, 4 control,
5 finite flag (scratch, then restored), 6 inverse flag, 7 infinity flag, 8 double flag,
9 exception flag, 10–12 clean scratch. -/

/-- Erase the corner flags given `x = C.x` on 10 (via 5) and `x = (-2C).x` on 12.
With the exception flag present (`e`), `O ⊕ H = c ∧ [x = C.x]`, so one `CX` replaces the
Toffoli that computed that product. -/
def leaves (yc y2c e : Bool) : Program :=
  [.measureX 6 [] [.CZ 4 11]] ++
  (if e then
    [.CX 9 7] ++ lit 3 (!yc) ++ [.measureX 9 [] [.CZ 7 3]] ++ lit 3 (!yc) ++
    [.measureX 7 [] [.CZ 4 10]]
  else
    [.CCX 4 10 5] ++ lit 3 yc ++ [.measureX 7 [] [.CZ 5 3]] ++ lit 3 yc ++
    [.measureX 5 [] [.CZ 4 10]]) ++
  [.CCX 4 12 5] ++
  lit 3 y2c ++ [.measureX 8 [] [.CZ 5 3]] ++ lit 3 y2c ++
  [.measureX 5 [] [.CZ 4 12]] ++
  [.X 5, .CX 11 5]

/-- Role 1: `C.x` and the sentinel share `x_r1 = a1`; `x_r2 = s2` isolates the sentinel;
`(-2C).x` has `x_r2 = b2`. -/
def otail1 (a1 s2 b2 yc y2c e : Bool) : Program :=
  lit 1 a1 ++ [.CCX 0 1 10] ++ lit 1 a1 ++ [.CX 10 0] ++
  lit 2 s2 ++ [.CCX 10 2 11] ++ lit 2 s2 ++ [.CX 11 10] ++
  lit 2 b2 ++ [.CCX 0 2 12] ++ lit 2 b2 ++
  leaves yc y2c e ++
  lit 2 b2 ++ [.measureX 12 [] [.CZ 0 2]] ++ lit 2 b2 ++
  [.CX 11 10] ++
  lit 2 s2 ++ [.measureX 11 [] [.CZ 10 2]] ++ lit 2 s2 ++
  [.CX 10 0] ++
  lit 1 a1 ++ [.measureX 10 [] [.CZ 0 1]] ++ lit 1 a1

/-- Role 2: `C.x` and `(-2C).x` share `x_r1 = a1`; `x_r2 = b2` isolates `(-2C).x`;
the sentinel has `x_r2 = s2`. -/
def otail2 (a1 s2 b2 yc y2c e : Bool) : Program :=
  lit 1 a1 ++ [.CCX 0 1 10] ++ lit 1 a1 ++ [.CX 10 0] ++
  lit 2 s2 ++ [.CCX 0 2 11] ++ lit 2 s2 ++
  lit 2 b2 ++ [.CCX 10 2 12] ++ lit 2 b2 ++ [.CX 12 10] ++
  leaves yc y2c e ++
  [.CX 12 10] ++
  lit 2 b2 ++ [.measureX 12 [] [.CZ 10 2]] ++ lit 2 b2 ++
  lit 2 s2 ++ [.measureX 11 [] [.CZ 0 2]] ++ lit 2 s2 ++
  [.CX 10 0] ++
  lit 1 a1 ++ [.measureX 10 [] [.CZ 0 1]] ++ lit 1 a1

/-- Match bits of the three constants from the zero-test bit and the pivots. -/
def oxS1 (a1 s2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 == a1) && (r2 == s2)
def oxA1 (a1 s2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 == a1) && (r2 != s2)
def oxB1 (a1 b2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 != a1) && (r2 == b2)
def oxS2 (a1 s2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 != a1) && (r2 == s2)
def oxA2 (a1 b2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 == a1) && (r2 != b2)
def oxB2 (a1 b2 : Bool) (h r1 r2 : Bool) : Bool := h && (r1 == a1) && (r2 == b2)

/-- Tail input word from the free bits `h, x_r1, x_r2, y0, c` (bits 0–4 of `v`). -/
def oin (xS xA xB : Bool) (yc y2c e : Bool) (v : Nat) : Nat :=
  let c := v.testBit 4
  let y0 := v.testBit 3
  ofBits [v.testBit 0, v.testBit 1, v.testBit 2, y0, c, false,
    c && xS, c && xA && (y0 == yc), c && xB && (y0 == y2c), e && c && xA && (y0 != yc),
    false, false, false]

def oout (xS : Bool) (v : Nat) : Nat :=
  ofBits [v.testBit 0, v.testBit 1, v.testBit 2, v.testBit 3, v.testBit 4, !xS,
    false, false, false, false, false, false, false]

theorem otail1_ok : ∀ a1 s2 b2 yc y2c e : Bool, ∀ v : Fin 32,
    let xS := oxS1 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xA := oxA1 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xB := oxB1 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    safe (otail1 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val) = true ∧
      bitRun (otail1 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val) = oout xS v.val := by
  decide +kernel

theorem otail2_ok : ∀ a1 s2 b2 yc y2c e : Bool, ∀ v : Fin 32,
    let xS := oxS2 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xA := oxA2 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xB := oxB2 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    safe (otail2 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val) = true ∧
      bitRun (otail2 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val) = oout xS v.val := by
  decide +kernel

theorem predec_counts (b1 s2 yc : Bool) :
    toffoliCount (predec1 b1 s2 yc) = 3 ∧ measurementCount (predec1 b1 s2 yc) = 0 ∧
    toffoliCount (predec2 b1 s2 yc) = 3 ∧ measurementCount (predec2 b1 s2 yc) = 0 := by
  cases b1 <;> cases s2 <;> cases yc <;> decide

theorem otail_counts (a1 s2 b2 yc y2c e : Bool) :
    toffoliCount (otail1 a1 s2 b2 yc y2c e) = (if e then 4 else 5) ∧
    toffoliCount (otail2 a1 s2 b2 yc y2c e) = (if e then 4 else 5) ∧
    measurementCount (otail1 a1 s2 b2 yc y2c e) = 8 ∧
    measurementCount (otail2 a1 s2 b2 yc y2c e) = 8 := by
  cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> cases e <;> decide

end OutputGadgets

section OutputStage
open Secp256k1 ControlledPointLayout

/-- Corner decode for the constants of `tr` (role chosen by the pivots). -/
def predecT (tr : Tri) (yc : Bool) : Program :=
  if tr.role1 then predec1 (tr.B.testBit tr.r1) (tr.S.testBit tr.r2) yc
  else predec2 (tr.S.testBit tr.r1) (tr.B.testBit tr.r2) yc

def predecL (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire) : Program :=
  renameProgram (LocalWireModel.label
    (fun q : Fin 8 => [g, c, xr1, xr2, y0, O, D, H].getD q.val 0)) (predecT tr yc)

/-- Output tail for the constants of `tr`. -/
def otail (tr : Tri) (yc y2c e : Bool) : Program :=
  if tr.role1 then otail1 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) (tr.B.testBit tr.r2) yc y2c e
  else otail2 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) (tr.B.testBit tr.r2) yc y2c e

def otailL (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire) (h : Wire) : Program :=
  renameProgram (LocalWireModel.label
    (fun q : Fin 13 => [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].getD q.val 0)) (otail tr yc y2c e)

/-- Output classifier: the input-stage zero test on the output abscissa with the output tail. -/
def oclassifier (tr : Tri) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) : Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))

/-- Sentinel-coded corner outputs: `O ↦ C`, `C ↦ 2C`, `-C ↦ O`, `-2C ↦ -C`. -/
def ocorners (L : ControlledPointLayout) (C : Point) : Program :=
  maskedConstant (parkWire L) L.point.x (FiniteFlagInterval.sentinel ^^^ pairCode C) ++
  maskedConstant (parkWire L) L.point.y (pointY C) ++
  maskedConstant L.doubleSelect L.point.x (pairCode C ^^^ pairCode (dialogExceptionPoint C)) ++
  maskedConstant L.doubleSelect L.point.y (pointY C ^^^ pointY (C + C)) ++
  maskedConstant L.genericSelect L.point.x (pairCode C ^^^ FiniteFlagInterval.sentinel) ++
  maskedConstant L.genericSelect L.point.y (pointY (-C)) ++
  maskedConstant L.core.equalNegY L.point.x (pairCode (dialogExceptionPoint C) ^^^ pairCode C) ++
  maskedConstant L.core.equalNegY L.point.y (pointY (dialogExceptionPoint C) ^^^ pointY (-C))

/-- The merged output stage, run after the relabelled generic block on the sentinel-coded point. -/
def outStage (L : ControlledPointLayout) (C : Point) : Program :=
  predecL (triOf C) (yBit C) L.genericSelect L.control (L.point.x.getD (triOf C).r1 0)
    (L.point.x.getD (triOf C).r2 0) (yLow L) (parkWire L) L.doubleSelect L.core.equalNegY ++
  ocorners L C ++
  oclassifier (triOf C) (yBit C) (yBit (C + C)) (exceptionBit C) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect (parkWire L) L.doubleSelect L.core.equalNegY
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) ++
  FiniteFlagInterval.zrep L

end OutputStage

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

section OutCorners
open Secp256k1 ControlledPointLayout
attribute [local irreducible] wires

/-! ### The fused suffix touches the double flag, the negation flag and the park wire -/

theorem suffix_mem (L : ControlledPointLayout) (C : Point) :
    L.doubleSelect ∈ wires (FusedFlags.suffixProgram L C) ∧
    L.core.equalNegY ∈ wires (FusedFlags.suffixProgram L C) ∧
    parkWire L ∈ wires (FusedFlags.suffixProgram L C) := by
  unfold FusedFlags.suffixProgram
  rw [renameProgram_support]
  have hmem : ∀ q ∈ ({4, 6, 10} : Finset Wire),
      q ∈ wires (FusedFlags.restoreSuffix (DHClass.cxk C) (yBit C)) := by
    intro q hq
    unfold FusedFlags.restoreSuffix
    rw [wires_append]
    apply Finset.mem_union_right
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> simp [wires, Instr.wires]
  exact ⟨Finset.mem_image.mpr ⟨4, hmem 4 (by simp), rfl⟩,
    Finset.mem_image.mpr ⟨6, hmem 6 (by simp), rfl⟩,
    Finset.mem_image.mpr ⟨10, hmem 10 (by simp), rfl⟩⟩

/-! ### The corner constants -/

/-- The abscissa change of the corner block for corner flags `O D I H`. -/
def cornerX (C : Point) (O D I H : Bool) : Nat :=
  (if O then FiniteFlagInterval.sentinel ^^^ pairCode C else 0) ^^^
  (if D then pairCode C ^^^ pairCode (dialogExceptionPoint C) else 0) ^^^
  (if I then pairCode C ^^^ FiniteFlagInterval.sentinel else 0) ^^^
  (if H then pairCode (dialogExceptionPoint C) ^^^ pairCode C else 0)

/-- The ordinate change of the corner block for corner flags `O D I H`. -/
def cornerY (C : Point) (O D I H : Bool) : Nat :=
  (if O then pointY C else 0) ^^^
  (if D then pointY C ^^^ pointY (C + C) else 0) ^^^
  (if I then pointY (-C) else 0) ^^^
  (if H then pointY (dialogExceptionPoint C) ^^^ pointY (-C) else 0)

theorem point_x_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.point.x.Nodup := by
  have h := L.dialogUsed_nodup hn
  simp only [dialogUsedWires, PointAddLayout.pointWires, List.cons_append, List.append_assoc] at h
  exact (List.nodup_cons.mp h).2.sublist (List.sublist_append_left _ _)

theorem point_y_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.point.y.Nodup := by
  have h := L.dialogUsed_nodup hn
  simp only [dialogUsedWires, PointAddLayout.pointWires, List.cons_append, List.append_assoc] at h
  exact ((List.nodup_cons.mp h).2.sublist (List.sublist_append_right _ _)).sublist
    (List.sublist_append_left _ _)

theorem flag_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q ∈ L.inPlaceFlags) : q ∉ L.point.x ∧ q ∉ L.point.y := by
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hf := List.count_pos_iff.mpr hq
  simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons] at h
  constructor
  · intro hx
    have := List.count_pos_iff.mpr hx
    split_ifs at h <;> omega
  · intro hy
    have := List.count_pos_iff.mpr hy
    split_ifs at h <;> omega

theorem park_not_point (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    parkWire L ∉ L.point.x ∧ parkWire L ∉ L.point.y := by
  have pa := (park_away L hw hn).1
  exact ⟨fun h => pa (by simp [PointAddLayout.pointWires, h]),
    fun h => pa (by simp [PointAddLayout.pointWires, h])⟩

/-- One masked constant on `r`, with `r'` a disjoint register and `c` off both. -/
theorem masked_step (r r' : List Wire) (c : Wire) (k : Nat) (hn : r.Nodup) (hcr : c ∉ r)
    (hcr' : c ∉ r') (hk : k < 2^r.length) (hd : ∀ w ∈ r', w ∉ r) (s t : State) (V V' : Nat)
    (m : List Bool)
    (h : t.phase = s.phase ∧ regValue r t.basis = V ∧ regValue r' t.basis = V' ∧
      ∀ w, w ∉ r → w ∉ r' → t.basis w = s.basis w) :
    (run (maskedConstant c r k) m t).phase = s.phase ∧
    regValue r (run (maskedConstant c r k) m t).basis = V ^^^ (if s.basis c then k else 0) ∧
    regValue r' (run (maskedConstant c r k) m t).basis = V' ∧
    ∀ w, w ∉ r → w ∉ r' → (run (maskedConstant c r k) m t).basis w = s.basis w := by
  obtain ⟨hp, hout, hv⟩ := maskedConstant_correct c r k hn hcr hk t m
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc : t.basis c = s.basis c := h4 c hcr hcr'
  refine ⟨hp.trans h1, by rw [hv, h2, hc], ?_, fun w hw hw' => (hout w hw).trans (h4 w hw hw')⟩
  rw [← h3]
  exact regValue_congr _ _ _ (fun w hw => hout w (hd w hw))

theorem run_masked_append (c : Wire) (r : List Wire) (k : Nat) (q : Program) (m : List Bool)
    (s : State) : run (maskedConstant c r k ++ q) m s = run q m (run (maskedConstant c r k) [] s) := by
  rw [run_append, (maskedConstant_counts c r k).2, List.drop_zero, List.take_zero]

theorem ocorners_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    (s : State) (m : List Bool) :
    (run (ocorners L C) m s).phase = s.phase ∧
    regValue L.point.x (run (ocorners L C) m s).basis = regValue L.point.x s.basis ^^^
      cornerX C (s.basis (parkWire L)) (s.basis L.doubleSelect) (s.basis L.genericSelect)
        (s.basis L.core.equalNegY) ∧
    regValue L.point.y (run (ocorners L C) m s).basis = regValue L.point.y s.basis ^^^
      cornerY C (s.basis (parkWire L)) (s.basis L.doubleSelect) (s.basis L.genericSelect)
        (s.basis L.core.equalNegY) ∧
    ∀ q, q ∉ L.point.x → q ∉ L.point.y → (run (ocorners L C) m s).basis q = s.basis q := by
  have hxl : L.point.x.length = 256 := hw.inputX
  have hyl : L.point.y.length = 256 := hw.inputY
  have hxn := point_x_nodup L hn
  have hyn := point_y_nodup L hn
  have hyx : ∀ w ∈ L.point.y, w ∉ L.point.x := y_not_x L hn
  have hxy : ∀ w ∈ L.point.x, w ∉ L.point.y := fun w hx hy => hyx w hy hx
  have hP := park_not_point L hw hn
  have hD := flag_not_point L hn L.doubleSelect (by simp [inPlaceFlags])
  have hG := flag_not_point L hn L.genericSelect (by simp [inPlaceFlags])
  have hH := flag_not_point L hn L.core.equalNegY (by simp [inPlaceFlags])
  have hp256 : p < 2^256 := by norm_num [p]
  have bX : ∀ R : Point, pairCode R < 2^256 := pairCode_lt
  have bY : ∀ R : Point, pointY R < 2^256 := fun R => lt_trans (point_coordinates_lt R).2 hp256
  have bS : FiniteFlagInterval.sentinel < 2^256 := lt_trans FiniteFlagInterval.sentinel_lt hp256
  have kx : ∀ a b : Nat, a < 2^256 → b < 2^256 → a ^^^ b < 2^L.point.x.length := fun a b ha hb => by
    rw [hxl]; exact Nat.xor_lt_two_pow ha hb
  have ky : ∀ a b : Nat, a < 2^256 → b < 2^256 → a ^^^ b < 2^L.point.y.length := fun a b ha hb => by
    rw [hyl]; exact Nat.xor_lt_two_pow ha hb
  have ky1 : ∀ R : Point, pointY R < 2^L.point.y.length := fun R => by rw [hyl]; exact bY R
  have swap : ∀ (t : State), (∀ w, w ∉ L.point.x → w ∉ L.point.y → t.basis w = s.basis w) →
      ∀ w, w ∉ L.point.y → w ∉ L.point.x → t.basis w = s.basis w := fun t h w a b => h w b a
  have swap' : ∀ (t : State), (∀ w, w ∉ L.point.y → w ∉ L.point.x → t.basis w = s.basis w) →
      ∀ w, w ∉ L.point.x → w ∉ L.point.y → t.basis w = s.basis w := fun t h w a b => h w b a
  have h0 : s.phase = s.phase ∧ regValue L.point.x s.basis = regValue L.point.x s.basis ∧
      regValue L.point.y s.basis = regValue L.point.y s.basis ∧
      ∀ w, w ∉ L.point.x → w ∉ L.point.y → s.basis w = s.basis w := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
  have e1 := masked_step L.point.x L.point.y (parkWire L) (FiniteFlagInterval.sentinel ^^^ pairCode C)
    hxn hP.1 hP.2 (kx _ _ bS (bX C)) hyx s s _ _ [] h0
  have e2 := masked_step L.point.y L.point.x (parkWire L) (pointY C) hyn hP.2 hP.1 (ky1 C) hxy s _ _ _ []
    ⟨e1.1, e1.2.2.1, e1.2.1, swap _ e1.2.2.2⟩
  have e3 := masked_step L.point.x L.point.y L.doubleSelect (pairCode C ^^^ pairCode (dialogExceptionPoint C))
    hxn hD.1 hD.2 (kx _ _ (bX C) (bX (dialogExceptionPoint C))) hyx s _ _ _ []
    ⟨e2.1, e2.2.2.1, e2.2.1, swap' _ e2.2.2.2⟩
  have e4 := masked_step L.point.y L.point.x L.doubleSelect (pointY C ^^^ pointY (C + C))
    hyn hD.2 hD.1 (ky _ _ (bY C) (bY (C + C))) hxy s _ _ _ []
    ⟨e3.1, e3.2.2.1, e3.2.1, swap _ e3.2.2.2⟩
  have e5 := masked_step L.point.x L.point.y L.genericSelect (pairCode C ^^^ FiniteFlagInterval.sentinel)
    hxn hG.1 hG.2 (kx _ _ (bX C) bS) hyx s _ _ _ []
    ⟨e4.1, e4.2.2.1, e4.2.1, swap' _ e4.2.2.2⟩
  have e6 := masked_step L.point.y L.point.x L.genericSelect (pointY (-C)) hyn hG.2 hG.1 (ky1 (-C)) hxy s _ _ _ []
    ⟨e5.1, e5.2.2.1, e5.2.1, swap _ e5.2.2.2⟩
  have e7 := masked_step L.point.x L.point.y L.core.equalNegY (pairCode (dialogExceptionPoint C) ^^^ pairCode C)
    hxn hH.1 hH.2 (kx _ _ (bX (dialogExceptionPoint C)) (bX C)) hyx s _ _ _ []
    ⟨e6.1, e6.2.2.1, e6.2.1, swap' _ e6.2.2.2⟩
  have e8 := masked_step L.point.y L.point.x L.core.equalNegY (pointY (dialogExceptionPoint C) ^^^ pointY (-C))
    hyn hH.2 hH.1 (ky _ _ (bY (dialogExceptionPoint C)) (bY (-C))) hxy s _ _ _ m
    ⟨e7.1, e7.2.2.1, e7.2.1, swap _ e7.2.2.2⟩
  have hrun : run (ocorners L C) m s =
      run (maskedConstant L.core.equalNegY L.point.y (pointY (dialogExceptionPoint C) ^^^ pointY (-C))) m
      (run (maskedConstant L.core.equalNegY L.point.x (pairCode (dialogExceptionPoint C) ^^^ pairCode C)) []
      (run (maskedConstant L.genericSelect L.point.y (pointY (-C))) []
      (run (maskedConstant L.genericSelect L.point.x (pairCode C ^^^ FiniteFlagInterval.sentinel)) []
      (run (maskedConstant L.doubleSelect L.point.y (pointY C ^^^ pointY (C + C))) []
      (run (maskedConstant L.doubleSelect L.point.x (pairCode C ^^^ pairCode (dialogExceptionPoint C))) []
      (run (maskedConstant (parkWire L) L.point.y (pointY C)) []
      (run (maskedConstant (parkWire L) L.point.x (FiniteFlagInterval.sentinel ^^^ pairCode C)) [] s))))))) := by
    simp only [ocorners, List.append_assoc, run_masked_append]
  rw [hrun]
  refine ⟨e8.1, ?_, ?_, swap' _ e8.2.2.2⟩
  · rw [e8.2.2.1]
    simp only [cornerX, Nat.xor_assoc]
  · rw [e8.2.1]
    simp only [cornerY, Nat.xor_assoc]

theorem ocorners_counts (L : ControlledPointLayout) (C : Point) :
    toffoliCount (ocorners L C) = 0 ∧ measurementCount (ocorners L C) = 0 := by
  constructor <;> simp [ocorners, toffoliCount_append, measurementCount_append,
    (maskedConstant_counts _ _ _).1, (maskedConstant_counts _ _ _).2]

theorem ocorners_support (L : ControlledPointLayout) (C : Point) :
    wires (ocorners L C) ⊆
      (L.point.x ++ L.point.y ++ [parkWire L, L.doubleSelect, L.genericSelect, L.core.equalNegY]).toFinset := by
  have hs : ∀ (c : Wire) (r : List Wire) (k : Nat),
      c ∈ [parkWire L, L.doubleSelect, L.genericSelect, L.core.equalNegY] →
      (r = L.point.x ∨ r = L.point.y) → wires (maskedConstant c r k) ⊆
        (L.point.x ++ L.point.y ++ [parkWire L, L.doubleSelect, L.genericSelect, L.core.equalNegY]).toFinset := by
    intro c r k hc hr q hq
    have hm := maskedConstant_wires_subset c r k hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm hc ⊢
    rcases hm with rfl | hm
    · exact Or.inr hc
    · rcases hr with rfl | rfl
      · exact Or.inl (Or.inl hm)
      · exact Or.inl (Or.inr hm)
  simp only [ocorners, wires_append]
  repeat' apply Finset.union_subset
  all_goals exact hs _ _ _ (by simp) (by simp)

theorem ocorners_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) :
    GatePhysical (ocorners L C) := by
  have hP := park_not_point L hw hn
  have hD := flag_not_point L hn L.doubleSelect (by simp [inPlaceFlags])
  have hG := flag_not_point L hn L.genericSelect (by simp [inPlaceFlags])
  have hH := flag_not_point L hn L.core.equalNegY (by simp [inPlaceFlags])
  simp only [ocorners, List.append_assoc, gatePhysical_append]
  exact ⟨maskedConstant_physical _ _ _ hP.1, maskedConstant_physical _ _ _ hP.2,
    maskedConstant_physical _ _ _ hD.1, maskedConstant_physical _ _ _ hD.2,
    maskedConstant_physical _ _ _ hG.1, maskedConstant_physical _ _ _ hG.2,
    maskedConstant_physical _ _ _ hH.1, maskedConstant_physical _ _ _ hH.2⟩

end OutCorners

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section OutTail
open Challenge

/-! ### Bits of a little-endian word -/

theorem ofBits_testBit : ∀ (bs : List Bool) (q : Nat), (ofBits bs).testBit q = bs.getD q false
  | [], q => by simp [ofBits]
  | b :: bs, q => by
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    cases q with
    | zero =>
      rw [Nat.testBit_zero]
      cases b <;> simp [ofBits, Nat.add_mul_mod_self_left]
    | succ q =>
      rw [Nat.testBit_succ, show ofBits (b :: bs) / 2 = ofBits bs by simp only [ofBits]; omega]
      simpa using ofBits_testBit bs q

/-! ### The output tail's match bits and its two roles -/

/-- A match bit of the output tail: the zero-test bit `h` and the pivot pattern of `K`. -/
def tX (tr : Tri) (K : Nat) (h a b : Bool) : Bool := h && decide ((a, b) = tr.pat K)

theorem role_facts (tr : Tri) (v : tr.Valid) :
    tr.B.testBit tr.r1 = !tr.S.testBit tr.r1 ∧
    (tr.role1 = true → tr.A.testBit tr.r1 = tr.S.testBit tr.r1 ∧ tr.A.testBit tr.r2 = !tr.S.testBit tr.r2) ∧
    (tr.role1 = false → tr.A.testBit tr.r1 = !tr.S.testBit tr.r1 ∧ tr.A.testBit tr.r2 = !tr.B.testBit tr.r2) := by
  have d1 := (firstDiff_spec tr.B tr.S v.hB v.hS v.BS).2
  have er1 : tr.r1 = firstDiff tr.B tr.S := rfl
  rw [← er1] at d1
  refine ⟨?_, ?_, ?_⟩
  · cases hB : tr.B.testBit tr.r1 <;> cases hS : tr.S.testBit tr.r1 <;> simp_all
  · intro ro
    have eq1 : tr.A.testBit tr.r1 = tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
    have er2 : tr.r2 = firstDiff tr.A tr.S := by simp [Tri.r2, ro]
    have d2 := (firstDiff_spec tr.A tr.S v.hA v.hS v.AS).2
    rw [← er2] at d2
    refine ⟨eq1, ?_⟩
    cases hA : tr.A.testBit tr.r2 <;> cases hS : tr.S.testBit tr.r2 <;> simp_all
  · intro ro
    have ne1 : tr.A.testBit tr.r1 ≠ tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
    have er2 : tr.r2 = firstDiff tr.A tr.B := by simp [Tri.r2, ro]
    have d2 := (firstDiff_spec tr.A tr.B v.hA v.hB v.AB).2
    rw [← er2] at d2
    constructor
    · cases hA : tr.A.testBit tr.r1 <;> cases hS : tr.S.testBit tr.r1 <;> simp_all
    · cases hA : tr.A.testBit tr.r2 <;> cases hB : tr.B.testBit tr.r2 <;> simp_all

theorem tX_bridge (tr : Tri) (v : tr.Valid) (hb r1b r2b : Bool) :
    (tr.role1 = true →
      tX tr tr.S hb r1b r2b = oxS1 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) hb r1b r2b ∧
      tX tr tr.A hb r1b r2b = oxA1 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) hb r1b r2b ∧
      tX tr tr.B hb r1b r2b = oxB1 (tr.A.testBit tr.r1) (tr.B.testBit tr.r2) hb r1b r2b) ∧
    (tr.role1 = false →
      tX tr tr.S hb r1b r2b = oxS2 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) hb r1b r2b ∧
      tX tr tr.A hb r1b r2b = oxA2 (tr.A.testBit tr.r1) (tr.B.testBit tr.r2) hb r1b r2b ∧
      tX tr tr.B hb r1b r2b = oxB2 (tr.A.testBit tr.r1) (tr.B.testBit tr.r2) hb r1b r2b) := by
  obtain ⟨fB, f1, f2⟩ := role_facts tr v
  constructor
  · intro ro
    obtain ⟨e1, e2⟩ := f1 ro
    simp only [tX, Tri.pat, oxS1, oxA1, oxB1, Prod.mk.injEq, e1, e2, fB]
    generalize tr.S.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    revert a b c hb r1b r2b; decide
  · intro ro
    obtain ⟨e1, e2⟩ := f2 ro
    simp only [tX, Tri.pat, oxS2, oxA2, oxB2, Prod.mk.injEq, e1, e2, fB]
    generalize tr.S.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    revert a b c hb r1b r2b; decide

/-- The output gadget's classical check in the triple's own terms (either role). -/
theorem otail_core (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (w : Fin 32) :
    safe (otail tr yc y2c e) (oin (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.A (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.B (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) yc y2c e w.val) = true ∧
    bitRun (otail tr yc y2c e) (oin (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.A (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.B (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) yc y2c e w.val) =
      oout (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) w.val := by
  have br := tX_bridge tr v (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)
  unfold otail
  by_cases ro : tr.role1 = true
  · obtain ⟨hS, hA, hB⟩ := br.1 ro
    rw [if_pos ro, hS, hA, hB]
    exact otail1_ok _ _ _ yc y2c e w
  · have ro' : tr.role1 = false := by simpa using ro
    obtain ⟨hS, hA, hB⟩ := br.2 ro'
    rw [if_neg ro, hS, hA, hB]
    exact otail2_ok _ _ _ yc y2c e w

theorem otail_support (tr : Tri) (yc y2c e : Bool) : wires (otail tr yc y2c e) ⊆ Finset.range 13 := by
  unfold otail
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_physical (tr : Tri) (yc y2c e : Bool) : GatePhysical (otail tr yc y2c e) := by
  unfold otail
  split_ifs <;> apply gatePhysical_of_all <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_slots (tr : Tri) (yc y2c e : Bool) : gateSlots (otail tr yc y2c e) ≤ 45 := by
  unfold otail
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_counts' (tr : Tri) (yc y2c e : Bool) :
    toffoliCount (otail tr yc y2c e) = (if e then 4 else 5) ∧ measurementCount (otail tr yc y2c e) = 8 := by
  unfold otail
  by_cases ro : tr.role1 = true
  · rw [if_pos ro]
    exact ⟨(otail_counts _ _ _ _ _ _).1, (otail_counts _ _ _ _ _ _).2.2.1⟩
  · rw [if_neg ro]
    exact ⟨(otail_counts _ _ _ _ _ _).2.1, (otail_counts _ _ _ _ _ _).2.2.2⟩

/-! ### The output tail on its thirteen wires -/

theorem otailL_support (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    wires (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) ⊆
      {h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u} := by
  unfold otailL
  rw [renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have ha13 : a < 13 := Finset.mem_range.mp (otail_support tr yc y2c e ha)
  simp only [LocalWireModel.label, dif_pos ha13]
  interval_cases a <;> simp

theorem otailL_physical (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup) :
    GatePhysical (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) := by
  have inj := LocalWireModel.listPorts_injective [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] hnd
    (n := 13) (by simp)
  unfold otailL
  exact gatePhysical_rename_support _ _ (fun a ha b hb heq =>
    LocalWireModel.label_injective _ inj a (otail_support tr yc y2c e ha) b (otail_support tr yc y2c e hb) heq)
    (otail_physical tr yc y2c e)

theorem otailL_counts (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    toffoliCount (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = (if e then 4 else 5) ∧
    measurementCount (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = 8 := by
  unfold otailL
  rw [(renameProgram_counts _ _).1, (renameProgram_counts _ _).2]
  exact otail_counts' tr yc y2c e

theorem otailL_slots (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    gateSlots (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = gateSlots (otail tr yc y2c e) := by
  unfold otailL
  exact rename_gateSlots _ _

/-- Tail precondition: clean scratch, and the four corner flags hold their match bits. -/
def otailPre (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire) (uu : Bool)
    (st : BasisState) : Prop :=
  st f = false ∧ st t1 = false ∧ st t2 = false ∧ st u = false ∧
  st g = (st c && tX tr tr.S uu (st xr1) (st xr2)) ∧
  st O = (st c && tX tr tr.A uu (st xr1) (st xr2) && (st y0 == yc)) ∧
  st D = (st c && tX tr tr.B uu (st xr1) (st xr2) && (st y0 == y2c)) ∧
  st H = (e && st c && tX tr tr.A uu (st xr1) (st xr2) && (st y0 != yc))

/-- Tail effect: the finite flag takes the negated sentinel match and the four flags are cleared. -/
def otailEff (tr : Tri) (xr1 xr2 f g O D H : Wire) (uu : Bool) (st : BasisState) : BasisState :=
  writeBit (writeBit (writeBit (writeBit (writeBit st f (!tX tr tr.S uu (st xr1) (st xr2))) g false)
    O false) D false) H false

theorem otailEff_apply (tr : Tri) (xr1 xr2 f g O D H : Wire) (uu : Bool) (st : BasisState) (q : Wire) :
    otailEff tr xr1 xr2 f g O D H uu st q =
      if q = H then false else if q = D then false else if q = O then false else if q = g then false
      else if q = f then !tX tr tr.S uu (st xr1) (st xr2) else st q := by
  unfold otailEff
  simp only [writeBit, Function.update_apply]

theorem otail_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (h xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup) (s : State) (m : List Bool)
    (hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u (s.basis h) s.basis) :
    run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H (s.basis h) s.basis⟩ := by
  unfold otailPre at hp
  obtain ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩ := hp
  set r : List Wire := [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] with hr
  have inj := LocalWireModel.listPorts_injective r hnd (n := 13) (by simp [hr])
  have rne : ∀ i j, i < 13 → j < 13 → i ≠ j → r.getD i 0 ≠ r.getD j 0 := by
    intro i j hi hj hij e
    have hi' : i < r.length := by simp [hr]; omega
    have hj' : j < r.length := by simp [hr]; omega
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at e
    exact hij (hnd.getElem_inj_iff.mp e)
  have n_h_f : h ≠ f := by simpa [hr] using rne 0 5 (by decide) (by decide) (by decide)
  have n_h_g : h ≠ g := by simpa [hr] using rne 0 6 (by decide) (by decide) (by decide)
  have n_h_O : h ≠ O := by simpa [hr] using rne 0 7 (by decide) (by decide) (by decide)
  have n_h_D : h ≠ D := by simpa [hr] using rne 0 8 (by decide) (by decide) (by decide)
  have n_h_H : h ≠ H := by simpa [hr] using rne 0 9 (by decide) (by decide) (by decide)
  have n_xr1_f : xr1 ≠ f := by simpa [hr] using rne 1 5 (by decide) (by decide) (by decide)
  have n_xr1_g : xr1 ≠ g := by simpa [hr] using rne 1 6 (by decide) (by decide) (by decide)
  have n_xr1_O : xr1 ≠ O := by simpa [hr] using rne 1 7 (by decide) (by decide) (by decide)
  have n_xr1_D : xr1 ≠ D := by simpa [hr] using rne 1 8 (by decide) (by decide) (by decide)
  have n_xr1_H : xr1 ≠ H := by simpa [hr] using rne 1 9 (by decide) (by decide) (by decide)
  have n_xr2_f : xr2 ≠ f := by simpa [hr] using rne 2 5 (by decide) (by decide) (by decide)
  have n_xr2_g : xr2 ≠ g := by simpa [hr] using rne 2 6 (by decide) (by decide) (by decide)
  have n_xr2_O : xr2 ≠ O := by simpa [hr] using rne 2 7 (by decide) (by decide) (by decide)
  have n_xr2_D : xr2 ≠ D := by simpa [hr] using rne 2 8 (by decide) (by decide) (by decide)
  have n_xr2_H : xr2 ≠ H := by simpa [hr] using rne 2 9 (by decide) (by decide) (by decide)
  have n_y0_f : y0 ≠ f := by simpa [hr] using rne 3 5 (by decide) (by decide) (by decide)
  have n_y0_g : y0 ≠ g := by simpa [hr] using rne 3 6 (by decide) (by decide) (by decide)
  have n_y0_O : y0 ≠ O := by simpa [hr] using rne 3 7 (by decide) (by decide) (by decide)
  have n_y0_D : y0 ≠ D := by simpa [hr] using rne 3 8 (by decide) (by decide) (by decide)
  have n_y0_H : y0 ≠ H := by simpa [hr] using rne 3 9 (by decide) (by decide) (by decide)
  have n_c_f : c ≠ f := by simpa [hr] using rne 4 5 (by decide) (by decide) (by decide)
  have n_c_g : c ≠ g := by simpa [hr] using rne 4 6 (by decide) (by decide) (by decide)
  have n_c_O : c ≠ O := by simpa [hr] using rne 4 7 (by decide) (by decide) (by decide)
  have n_c_D : c ≠ D := by simpa [hr] using rne 4 8 (by decide) (by decide) (by decide)
  have n_c_H : c ≠ H := by simpa [hr] using rne 4 9 (by decide) (by decide) (by decide)
  have n_f_g : f ≠ g := by simpa [hr] using rne 5 6 (by decide) (by decide) (by decide)
  have n_f_O : f ≠ O := by simpa [hr] using rne 5 7 (by decide) (by decide) (by decide)
  have n_f_D : f ≠ D := by simpa [hr] using rne 5 8 (by decide) (by decide) (by decide)
  have n_f_H : f ≠ H := by simpa [hr] using rne 5 9 (by decide) (by decide) (by decide)
  have n_g_f : g ≠ f := by simpa [hr] using rne 6 5 (by decide) (by decide) (by decide)
  have n_g_O : g ≠ O := by simpa [hr] using rne 6 7 (by decide) (by decide) (by decide)
  have n_g_D : g ≠ D := by simpa [hr] using rne 6 8 (by decide) (by decide) (by decide)
  have n_g_H : g ≠ H := by simpa [hr] using rne 6 9 (by decide) (by decide) (by decide)
  have n_O_f : O ≠ f := by simpa [hr] using rne 7 5 (by decide) (by decide) (by decide)
  have n_O_g : O ≠ g := by simpa [hr] using rne 7 6 (by decide) (by decide) (by decide)
  have n_O_D : O ≠ D := by simpa [hr] using rne 7 8 (by decide) (by decide) (by decide)
  have n_O_H : O ≠ H := by simpa [hr] using rne 7 9 (by decide) (by decide) (by decide)
  have n_D_f : D ≠ f := by simpa [hr] using rne 8 5 (by decide) (by decide) (by decide)
  have n_D_g : D ≠ g := by simpa [hr] using rne 8 6 (by decide) (by decide) (by decide)
  have n_D_O : D ≠ O := by simpa [hr] using rne 8 7 (by decide) (by decide) (by decide)
  have n_D_H : D ≠ H := by simpa [hr] using rne 8 9 (by decide) (by decide) (by decide)
  have n_H_f : H ≠ f := by simpa [hr] using rne 9 5 (by decide) (by decide) (by decide)
  have n_H_g : H ≠ g := by simpa [hr] using rne 9 6 (by decide) (by decide) (by decide)
  have n_H_O : H ≠ O := by simpa [hr] using rne 9 7 (by decide) (by decide) (by decide)
  have n_H_D : H ≠ D := by simpa [hr] using rne 9 8 (by decide) (by decide) (by decide)
  have n_t1_f : t1 ≠ f := by simpa [hr] using rne 10 5 (by decide) (by decide) (by decide)
  have n_t1_g : t1 ≠ g := by simpa [hr] using rne 10 6 (by decide) (by decide) (by decide)
  have n_t1_O : t1 ≠ O := by simpa [hr] using rne 10 7 (by decide) (by decide) (by decide)
  have n_t1_D : t1 ≠ D := by simpa [hr] using rne 10 8 (by decide) (by decide) (by decide)
  have n_t1_H : t1 ≠ H := by simpa [hr] using rne 10 9 (by decide) (by decide) (by decide)
  have n_t2_f : t2 ≠ f := by simpa [hr] using rne 11 5 (by decide) (by decide) (by decide)
  have n_t2_g : t2 ≠ g := by simpa [hr] using rne 11 6 (by decide) (by decide) (by decide)
  have n_t2_O : t2 ≠ O := by simpa [hr] using rne 11 7 (by decide) (by decide) (by decide)
  have n_t2_D : t2 ≠ D := by simpa [hr] using rne 11 8 (by decide) (by decide) (by decide)
  have n_t2_H : t2 ≠ H := by simpa [hr] using rne 11 9 (by decide) (by decide) (by decide)
  have n_u_f : u ≠ f := by simpa [hr] using rne 12 5 (by decide) (by decide) (by decide)
  have n_u_g : u ≠ g := by simpa [hr] using rne 12 6 (by decide) (by decide) (by decide)
  have n_u_O : u ≠ O := by simpa [hr] using rne 12 7 (by decide) (by decide) (by decide)
  have n_u_D : u ≠ D := by simpa [hr] using rne 12 8 (by decide) (by decide) (by decide)
  have n_u_H : u ≠ H := by simpa [hr] using rne 12 9 (by decide) (by decide) (by decide)
  set vv : Nat := ofBits [s.basis h, s.basis xr1, s.basis xr2, s.basis y0, s.basis c] with hvv
  have hv32 : vv < 32 := by
    simp only [hvv, ofBits]
    cases s.basis h <;> cases s.basis xr1 <;> cases s.basis xr2 <;> cases s.basis y0 <;> cases s.basis c <;> simp
  have v0 : vv.testBit 0 = s.basis h := by rw [hvv, ofBits_testBit]; rfl
  have v1 : vv.testBit 1 = s.basis xr1 := by rw [hvv, ofBits_testBit]; rfl
  have v2 : vv.testBit 2 = s.basis xr2 := by rw [hvv, ofBits_testBit]; rfl
  have v3 : vv.testBit 3 = s.basis y0 := by rw [hvv, ofBits_testBit]; rfl
  have v4 : vv.testBit 4 = s.basis c := by rw [hvv, ofBits_testBit]; rfl
  have core := otail_core tr v yc y2c e ⟨vv, hv32⟩
  simp only [v0, v1, v2] at core
  set xS := tX tr tr.S (s.basis h) (s.basis xr1) (s.basis xr2) with hxS
  set xA := tX tr tr.A (s.basis h) (s.basis xr1) (s.basis xr2) with hxA
  set xB := tX tr tr.B (s.basis h) (s.basis xr1) (s.basis xr2) with hxB
  have hx : ∀ q (hq : q < 13), s.basis ((fun q : Fin 13 => r.getD q.val 0) ⟨q, hq⟩) =
      (oin xS xA xB yc y2c e vv).testBit q := by
    intro q hq
    simp only [oin, ofBits_testBit]
    interval_cases q <;> simp [hr, v0, v1, v2, v3, v4, pf, pt1, pt2, pu, pg, pO, pD, pH]
  have L := lift_local 13 _ inj (otail tr yc y2c e) (otail_support tr yc y2c e) s m _ hx core.1
  rw [core.2] at L
  have port : ∀ q (hq : q < 13), (run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s).basis
      (r.getD q 0) = [vv.testBit 0, vv.testBit 1, vv.testBit 2, vv.testBit 3, vv.testBit 4, !xS,
        false, false, false, false, false, false, false].getD q false := by
    intro q hq
    have := L.2.1 q hq
    simp only [oout, ofBits_testBit] at this
    exact this
  apply State.extensionality
  · exact L.1
  · funext w
    show _ = otailEff tr xr1 xr2 f g O D H (s.basis h) s.basis w
    rw [otailEff_apply]
    by_cases wr : w ∈ r
    · obtain ⟨q, hq, hqw⟩ : ∃ q, q < 13 ∧ r.getD q 0 = w := by
        obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem wr
        exact ⟨i, by simpa [hr] using hi, by rw [List.getD_eq_getElem _ _ hi]; exact hiw⟩
      subst hqw
      rw [port q hq]
      interval_cases q <;> simp [hr, hxS, v0, v1, v2, v3, v4, pt1, pt2, pu, n_h_f, n_h_g, n_h_O, n_h_D, n_h_H, n_xr1_f, n_xr1_g, n_xr1_O, n_xr1_D, n_xr1_H, n_xr2_f, n_xr2_g, n_xr2_O, n_xr2_D, n_xr2_H, n_y0_f, n_y0_g, n_y0_O, n_y0_D, n_y0_H, n_c_f, n_c_g, n_c_O, n_c_D, n_c_H, n_f_g, n_f_O, n_f_D, n_f_H, n_g_f, n_g_O, n_g_D, n_g_H, n_O_f, n_O_g, n_O_D, n_O_H, n_D_f, n_D_g, n_D_O, n_D_H, n_H_f, n_H_g, n_H_O, n_H_D, n_t1_f, n_t1_g, n_t1_O, n_t1_D, n_t1_H, n_t2_f, n_t2_g, n_t2_O, n_t2_D, n_t2_H, n_u_f, n_u_g, n_u_O, n_u_D, n_u_H]
    · have nw : ∀ x ∈ r, w ≠ x := fun x hx heq => wr (heq ▸ hx)
      have hout : (run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s).basis w = s.basis w :=
        L.2.2 w (fun q hq heq => wr (by
          rw [heq]
          show r.getD q 0 ∈ r
          rw [List.getD_eq_getElem _ _ (by simpa [hr] using hq)]
          exact List.getElem_mem _))
      rw [hout]
      simp [nw f (by simp [hr]), nw g (by simp [hr]), nw O (by simp [hr]), nw D (by simp [hr]),
        nw H (by simp [hr])]

/-! ### The zero chain with the output tail -/

theorem ochain_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (c0 : Wire) (bs : List ZeroBit) (hcu : c0 ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (hnd : (c0 :: bs.flatMap ZeroBit.wires).Nodup)
    (hdis : ∀ b ∈ bs, b.input ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (s : State) (m : List Bool)
    (hs : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis)
    (hz : ∀ b ∈ bs, s.basis b.work = false) :
    run (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) c0 bs) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis⟩ := by
  set used : List Wire := [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] with hu
  apply zeroWith_effect_runQ used (otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u)
    (otailEff tr xr1 xr2 f g O D H)
  · intro w hw uu st z
    have n : ∀ x ∈ used, x ≠ w := fun x hx heq => hw (heq ▸ hx)
    have p_xr1 : xr1 ≠ w := n xr1 (by simp [hu])
    have p_xr2 : xr2 ≠ w := n xr2 (by simp [hu])
    have p_y0 : y0 ≠ w := n y0 (by simp [hu])
    have p_c : c ≠ w := n c (by simp [hu])
    have p_f : f ≠ w := n f (by simp [hu])
    have p_g : g ≠ w := n g (by simp [hu])
    have p_O : O ≠ w := n O (by simp [hu])
    have p_D : D ≠ w := n D (by simp [hu])
    have p_H : H ≠ w := n H (by simp [hu])
    have p_t1 : t1 ≠ w := n t1 (by simp [hu])
    have p_t2 : t2 ≠ w := n t2 (by simp [hu])
    have p_u : u ≠ w := n u (by simp [hu])
    simp only [otailPre, writeBit, Function.update_apply, p_xr1, p_xr2, p_y0, p_c, p_f, p_g, p_O, p_D, p_H, p_t1, p_t2, p_u, if_false]
  · intro uu st w hw
    have n : ∀ x ∈ used, w ≠ x := fun x hx heq => hw (heq ▸ hx)
    rw [otailEff_apply]
    simp [n f (by simp [hu]), n g (by simp [hu]), n O (by simp [hu]), n D (by simp [hu]), n H (by simp [hu])]
  · intro uu st w z hw
    have n : ∀ x ∈ used, w ≠ x := fun x hx heq => hw (heq ▸ hx)
    have a1 : writeBit st w z xr1 = st xr1 := by
      simp [writeBit, Function.update, Ne.symm (n xr1 (by simp [hu]))]
    have a2 : writeBit st w z xr2 = st xr2 := by
      simp [writeBit, Function.update, Ne.symm (n xr2 (by simp [hu]))]
    funext q
    rw [otailEff_apply, a1, a2]
    by_cases hq : q = w
    · subst hq
      simp [writeBit, otailEff_apply, n f (by simp [hu]), n g (by simp [hu]), n O (by simp [hu]),
        n D (by simp [hu]), n H (by simp [hu])]
    · simp only [writeBit, Function.update_apply, hq, if_false]
      rw [otailEff_apply]
  · intro c' hc' st m' hp
    exact otail_run tr v yc y2c e c' xr1 xr2 y0 c f g O D H t1 t2 u (List.nodup_cons.mpr ⟨hc', hused⟩) st m' hp
  · exact hcu
  · exact hnd
  · exact hdis
  · exact hs
  · exact hz

/-! ### Remap, zero test with the output tail, undo -/

theorem oshape_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (w : Nat → Wire) (i0 : Nat) (it : List Nat) (work : List Wire)
    (hPn : ((i0 :: it).map w).Nodup) (x1P : xr1 ∉ (i0 :: it).map w) (x2P : xr2 ∉ (i0 :: it).map w)
    (hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w)
    (hwl : (it.map w).length = work.length) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (s : State) (m : List Bool)
    (hz : ∀ q ∈ work, s.basis q = false)
    (hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis) :
    run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H
        ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis⟩ := by
  have hlw : (i0 :: it).map w = w i0 :: it.map w := rfl
  have p0l : w i0 ∈ (i0 :: it).map w := by simp
  have usedNotP : ∀ q ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | hq
    · exact x1P
    · exact x2P
    · exact hextP q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have itNe : ∀ i ∈ it, w i ≠ w i0 := by
    intro i hi heq
    rw [hlw] at hPn
    exact (List.nodup_cons.mp hPn).1 (heq ▸ List.mem_map_of_mem hi)
  -- step 1: remap
  have R1 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P m s
  rw [LocalWireModel.run_concat, remapList_mc, List.drop_zero, LocalWireModel.run_concat]
  generalize hs1 : run (tr.remapList xr1 xr2 w (i0 :: it)) m s = s1 at R1 ⊢
  -- step 2: X p0
  have e2 : run [Instr.X (w i0)] m s1 = ⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ := by
    simp [run]
  rw [e2]
  generalize hs2 : (⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ : State) = s2
  have s2ph : s2.phase = s.phase := by rw [← hs2]; exact R1.1
  have s2out : ∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q := by
    intro q hq
    have hq0 : q ≠ w i0 := fun heq => hq (heq ▸ p0l)
    rw [← hs2]; simp [writeBit, Function.update, hq0, R1.2.1 q hq]
  have s2p0 : s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) := by
    rw [← hs2]; simp only [writeBit, Function.update_self]
    rw [R1.2.2 i0 (by simp)]
    cases s.basis (w i0) <;> cases tr.tgt i0 (s.basis xr1, s.basis xr2) <;> rfl
  have s2it : ∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2)) := by
    intro i hi
    rw [← hs2]; simp only [writeBit]
    rw [Function.update_of_ne (itNe i hi), R1.2.2 i (by simp [hi])]
  have k1 : s2.basis xr1 = s.basis xr1 := s2out xr1 x1P
  have k2 : s2.basis xr2 = s.basis xr2 := s2out xr2 x2P
  -- the zero-test value equals the match bit
  have zp := zeroPorts_maps (it.map w) work hwl
  have huV : (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    have hall : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
        it.all (fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
      have : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
          ((zeroPorts (it.map w) work).map ZeroBit.input).all (fun q => !s2.basis q) := by
        rw [List.all_map]; rfl
      rw [this, zp.1, List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      apply forall₂_congr
      intro i hi
      simp only [Function.comp_apply, s2it i hi]
      cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> simp
    rw [hall, s2p0]
    simp [List.all_cons]
  -- step 3: the zero-test chain with the output tail
  have hcu : w i0 ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := fun h => usedNotP _ h p0l
  have hperm := zeroPorts_perm (it.map w) work hwl
  have hnd : (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp (hperm.mem_iff.mp hm) with h | h
      · obtain ⟨i, hi, heq⟩ := List.mem_map.mp h
        exact itNe i hi heq
      · exact (hdisj _ h).1 p0l
    · apply hperm.symm.nodup_iff.mp
      apply List.nodup_append.mpr
      refine ⟨(List.nodup_cons.mp (hlw ▸ hPn)).2, hwn, ?_⟩
      intro a ha b hb heq
      subst heq
      exact (hdisj a hb).1 (by rw [hlw]; exact List.mem_cons_of_mem _ ha)
  have hdis' : ∀ b ∈ zeroPorts (it.map w) work, b.input ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    intro b hb
    have hin : b.input ∈ it.map w := by
      have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    exact ⟨fun h => usedNotP _ h (by rw [hlw]; exact List.mem_cons_of_mem _ hin), (hdisj _ hwk).2⟩
  unfold otailPre at hp
  obtain ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩ := hp
  have qq : ∀ x ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], s2.basis x = s.basis x :=
    fun x hx => s2out x (usedNotP x hx)
  have hs3 : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) s2.basis := by
    rw [huV]
    unfold otailPre
    rw [qq f (by simp), qq t1 (by simp), qq t2 (by simp), qq u (by simp), qq g (by simp), qq c (by simp),
      qq O (by simp), qq D (by simp), qq H (by simp), qq y0 (by simp), k1, k2]
    exact ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩
  have hz3 : ∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false := by
    intro b hb
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    rw [s2out _ (hdisj _ hwk).1]; exact hz _ hwk
  rw [LocalWireModel.run_concat, ochain_run tr v yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u hused (w i0) _ hcu hnd
    hdis' s2 _ hs3 hz3, huV, LocalWireModel.run_concat]
  set V := (i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2) with hV
  set T3 := otailEff tr xr1 xr2 f g O D H V s2.basis with hT3
  have e4 : ∀ mm, run [Instr.X (w i0)] mm ⟨s2.phase, T3⟩ = ⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ := by
    intro mm; simp [run]
  rw [e4]
  generalize hs4 : (⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ : State) = s4
  have T3out : ∀ q, q ∉ (i0 :: it).map w → T3 q = otailEff tr xr1 xr2 f g O D H V s.basis q := by
    intro q hq
    rw [hT3, otailEff_apply, otailEff_apply, k1, k2, s2out q hq]
  have T3in : ∀ q, q ≠ f → q ≠ g → q ≠ O → q ≠ D → q ≠ H → T3 q = s2.basis q := by
    intro q h1 h2 h3 h4 h5
    rw [hT3, otailEff_apply]
    simp [h1, h2, h3, h4, h5]
  have u_xr1_f : xr1 ≠ f := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_g : xr1 ≠ g := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_O : xr1 ≠ O := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_D : xr1 ≠ D := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_H : xr1 ≠ H := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_f : xr2 ≠ f := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_g : xr2 ≠ g := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_O : xr2 ≠ O := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_D : xr2 ≠ D := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_H : xr2 ≠ H := fun heq => by rw [heq] at hused; simp at hused
  have s4x1 : s4.basis xr1 = s.basis xr1 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun heq => hcu (by simp [heq])), T3in xr1 u_xr1_f u_xr1_g u_xr1_O u_xr1_D u_xr1_H, k1]
  have s4x2 : s4.basis xr2 = s.basis xr2 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun heq => hcu (by simp [heq])), T3in xr2 u_xr2_f u_xr2_g u_xr2_O u_xr2_D u_xr2_H, k2]
  -- step 5: remap again
  suffices key : ∀ mm, run (tr.remapList xr1 xr2 w (i0 :: it)) mm s4 =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H V s.basis⟩ from key _
  intro mm
  have R5 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P mm s4
  apply State.extensionality
  · rw [R5.1, ← hs4]; exact s2ph
  · funext q
    by_cases hq : q ∈ (i0 :: it).map w
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      rw [R5.2.2 i hi, s4x1, s4x2]
      have nf : w i ≠ f := fun heq => usedNotP f (by simp) (heq ▸ hq)
      have ng : w i ≠ g := fun heq => usedNotP g (by simp) (heq ▸ hq)
      have nO : w i ≠ O := fun heq => usedNotP O (by simp) (heq ▸ hq)
      have nD : w i ≠ D := fun heq => usedNotP D (by simp) (heq ▸ hq)
      have nH : w i ≠ H := fun heq => usedNotP H (by simp) (heq ▸ hq)
      have rhs : otailEff tr xr1 xr2 f g O D H V s.basis (w i) = s.basis (w i) := by
        rw [otailEff_apply]; simp [nf, ng, nO, nD, nH]
      change (s4.basis (w i) ^^ _) = otailEff tr xr1 xr2 f g O D H V s.basis (w i)
      rw [rhs]
      rw [← hs4]; simp only [writeBit]
      rcases List.mem_cons.mp hi with rfl | hit
      · rw [Function.update_self, T3in _ nf ng nO nD nH, s2p0]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
      · rw [Function.update_of_ne (itNe i hit), T3in _ nf ng nO nD nH, s2it i hit]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
    · rw [R5.2.1 q hq, ← hs4]
      change writeBit T3 (w i0) (!T3 (w i0)) q = otailEff tr xr1 xr2 f g O D H V s.basis q
      simp only [writeBit]
      rw [Function.update_of_ne (fun heq : q = w i0 => hq (heq ▸ p0l)), T3out q hq]

/-! ### The output classifier -/

/-- The output classifier's match bit for constant `K`: the zero test and `K`'s pivot pattern. -/
def oX (tr : Tri) (K : Nat) (xs : List Wire) (st : BasisState) : Bool :=
  matchBit tr xs st && decide ((st (xs.getD tr.r1 0), st (xs.getD tr.r2 0)) = tr.pat K)

theorem oclassifier_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ xs ∧ q ∉ work)
    (s : State) (m : List Bool)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis f = false ∧ s.basis t1 = false ∧
      s.basis t2 = false ∧ s.basis u = false)
    (hfl : s.basis g = (s.basis c && oX tr tr.S xs s.basis) ∧
      s.basis O = (s.basis c && oX tr tr.A xs s.basis && (s.basis y0 == yc)) ∧
      s.basis D = (s.basis c && oX tr tr.B xs s.basis && (s.basis y0 == y2c)) ∧
      s.basis H = (e && s.basis c && oX tr tr.A xs s.basis && (s.basis y0 != yc))) :
    run (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) m s =
      ⟨s.phase, writeBit (writeBit (writeBit (writeBit (writeBit s.basis f (!oX tr tr.S xs s.basis))
        g false) O false) D false) H false⟩ := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  set w : Nat → Wire := fun i => xs.getD i 0 with hw
  set xr1 := w tr.r1 with hx1
  set xr2 := w tr.r2 with hx2
  set P := tr.idx.map w with hP
  have winj : ∀ i j, i < 256 → j < 256 → w i = w j → i = j := by
    intro i j hi hj heq
    simp only [hw] at heq
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
    exact hxs.getElem_inj_iff.mp heq
  have wmem : ∀ i, i < 256 → w i ∈ xs := by
    intro i hi; simp only [hw]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hPn : P.Nodup := by
    apply List.Nodup.map_on _ ix.1
    intro i hi j hj heq; exact winj i j (ix.2.2.2.2 i hi) (ix.2.2.2.2 j hj) heq
  have memP : ∀ q, q ∈ P ↔ ∃ i ∈ tr.idx, w i = q := by intro q; simp [hP]
  have x1P : xr1 ∉ P := by
    rw [memP]; rintro ⟨i, hi, heq⟩
    exact ix.2.2.1 (winj i tr.r1 (ix.2.2.2.2 i hi) pv.1 heq ▸ hi)
  have x2P : xr2 ∉ P := by
    rw [memP]; rintro ⟨i, hi, heq⟩
    exact ix.2.2.2.1 (winj i tr.r2 (ix.2.2.2.2 i hi) pv.2.1 heq ▸ hi)
  have x12 : xr1 ≠ xr2 := fun heq => pv.2.2.1 (winj _ _ pv.1 pv.2.1 heq)
  have Psub : ∀ q ∈ P, q ∈ xs := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := (memP q).mp hq; exact wmem i (ix.2.2.2.2 i hi)
  have hPl : P.length = 254 := by simp [hP, ix.2.1]
  obtain ⟨i0, it, hidx⟩ : ∃ i0 it, tr.idx = i0 :: it := by
    have hl := ix.2.1
    cases h : tr.idx with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  have hP0 : P = w i0 :: it.map w := by simp [hP, hidx]
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, O, D, H, t1, t2, u]) :
      q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    exact ⟨fun hp => h.1 (Psub q hp), h.2, fun heq => h.1 (heq ▸ wmem _ pv.1),
      fun heq => h.1 (heq ▸ wmem _ pv.2.1)⟩
  have hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨x12, ?_⟩
      have := fun q hq => (extx q hq).2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      exact ⟨fun heq => this y0 (Or.inl rfl) heq.symm, fun heq => this c (by tauto) heq.symm,
        fun heq => this f (by tauto) heq.symm, fun heq => this g (by tauto) heq.symm,
        fun heq => this O (by tauto) heq.symm, fun heq => this D (by tauto) heq.symm,
        fun heq => this H (by tauto) heq.symm, fun heq => this t1 (by tauto) heq.symm,
        fun heq => this t2 (by tauto) heq.symm, fun heq => this u (by tauto) heq.symm⟩
    · intro hm
      exact (extx xr2 hm).2.2.2 rfl
  have hlP : (i0 :: it).map w = P := by rw [hP0]; rfl
  have hPn' : ((i0 :: it).map w).Nodup := by rw [hlP]; exact hPn
  have x1P' : xr1 ∉ (i0 :: it).map w := by rw [hlP]; exact x1P
  have x2P' : xr2 ∉ (i0 :: it).map w := by rw [hlP]; exact x2P
  have hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w := by
    intro q hq; rw [hlP]; exact (extx q hq).1
  have hdisj' : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    intro q hq
    refine ⟨fun hm => hdisj q hq (Psub q (by rw [← hlP]; exact hm)), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (heq | heq | heq)
    · exact hdisj q hq (heq ▸ wmem _ pv.1)
    · exact hdisj q hq (heq ▸ wmem _ pv.2.1)
    · exact (hextx q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)).2 hq
  have hmb : matchBit tr xs s.basis =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    simp only [matchBit, hidx]; rfl
  have hoX : ∀ K, oX tr K xs s.basis = tX tr K
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2))
      (s.basis xr1) (s.basis xr2) := by
    intro K; simp only [oX, tX, ← hmb]; rfl
  have hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis := by
    unfold otailPre
    rw [← hoX, ← hoX, ← hoX]
    exact ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2, hfl.1, hfl.2.1, hfl.2.2.1, hfl.2.2.2⟩
  have run_eq := oshape_run tr v yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u w i0 it work hPn' x1P' x2P' hused
    hextP (by rw [hitl, hwl]) hwn hdisj' s m hz.1 hp
  have hprog : oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [oclassifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hprog, run_eq]
  unfold otailEff
  rw [← hoX]

/-! ### Counts, slots, support and physical gates of the output classifier -/

theorem oclassifier_counts (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hwl : work.length = 253) :
    toffoliCount (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) = 253 + (if e then 4 else 5) ∧
    measurementCount (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) = 253 + 8 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zc := zeroWith_counts_general
    (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u) (if e then 4 else 5) 8
    (fun h => otailL_counts tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc
  have rt := remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold oclassifier
  simp only [toffoliCount_append, measurementCount_append, rt, rm, zc.1, zc.2]
  exact ⟨by simp [toffoliCount], by simp [measurementCount]⟩

/-- 3 slots a remapped bit twice, the two flips, 7 a chain rung, and the 45-slot worst output tail. -/
theorem oclassifier_slots (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hwl : work.length = 253) :
    gateSlots (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ≤ 3342 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zs := zeroWith_slots (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
    (gateSlots (otail tr yc y2c e)) (fun h => otailL_slots tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := otail_slots tr yc y2c e
  unfold oclassifier
  simp only [gateSlots_app, zs]
  simp only [gateSlots, instructionSlots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at rs ds ⊢
  omega

theorem oclassifier_support (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hxl : xs.length = 256) (hwl : work.length = 253) :
    wires (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ⊆
      xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, O, D, H, t1, t2, u} := by
  have _ := hwl
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  let U : Finset Wire := xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, O, D, H, t1, t2, u}
  have xsU : ∀ i, i < 256 → xs.getD i 0 ∈ U := by
    intro i hi
    have hm : xs.getD i 0 ∈ xs := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    simp only [U, Finset.mem_union, List.mem_toFinset]
    exact Or.inl (Or.inl hm)
  have workU : ∀ q ∈ work, q ∈ U := fun q hq => by simp [U, hq]
  have r1U := xsU _ pv.1
  have r2U := xsU _ pv.2.1
  have idxU : ∀ i ∈ tr.idx, xs.getD i 0 ∈ U := fun i hi => xsU i (ix.2.2.2.2 i hi)
  have PU : ∀ q ∈ tr.idx.map (fun i => xs.getD i 0), q ∈ U := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; exact idxU i hi
  have h0U : (tr.idx.map (fun i => xs.getD i 0)).headD 0 ∈ U := by
    rw [hidx]; exact idxU i0 (by rw [hidx]; simp)
  have portsU : ∀ b ∈ zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work,
      b.input ∈ U ∧ b.work ∈ U := by
    intro b hb
    have hm := zeroPorts_mem _ _ b hb
    exact ⟨PU _ (List.mem_of_mem_tail hm.1), workU _ hm.2⟩
  have extU : ∀ q ∈ ({y0, c, f, g, O, D, H, t1, t2, u} : Finset Wire), q ∈ U := by
    intro q hq; simp only [U, Finset.mem_union]; exact Or.inr hq
  have tailU : ∀ h ∈ U,
      wires (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h) ⊆ U := by
    intro h hh
    refine (otailL_support tr yc y2c e _ _ y0 c f g O D H t1 t2 u h).trans ?_
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hh, r1U, r2U, extU y0 (by simp), extU c (by simp), extU f (by simp), extU g (by simp),
      extU O (by simp), extU D (by simp), extU H (by simp), extU t1 (by simp), extU t2 (by simp),
      extU u (by simp)⟩
  have remapU := remapList_sub tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx U
    r1U r2U idxU
  have zU := zeroWith_sub _ U tailU _ _ h0U portsU
  have xU : wires [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ⊆ U := by
    generalize (tr.idx.map (fun i => xs.getD i 0)).headD 0 = h0 at h0U ⊢
    intro q hq
    simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton] at hq
    rcases hq with rfl | hq
    · exact h0U
    · simp at hq
  intro q hq
  simp only [oclassifier, wires_append, Finset.mem_union] at hq
  rcases hq with h | h | h | h | h
  · exact remapU h
  · exact xU h
  · exact zU h
  · exact xU h
  · exact remapU h

theorem oclassifier_physical (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hxl : xs.length = 256) (hwl : work.length = 253)
    (hxn : xs.Nodup) (hwn : work.Nodup) (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ xs ∧ q ∉ work) :
    GatePhysical (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have winj : ∀ i j, i < 256 → j < 256 → xs.getD i 0 = xs.getD j 0 → i = j := by
    intro i j hi hj heq
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
    exact hxn.getElem_inj_iff.mp heq
  have wmem : ∀ i, i < 256 → xs.getD i 0 ∈ xs := by
    intro i hi; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hi0 : i0 ∈ tr.idx := by rw [hidx]; simp
  have i0lt := ix.2.2.2.2 i0 hi0
  have i0r1 : i0 ≠ tr.r1 := fun heq => ix.2.2.1 (heq ▸ hi0)
  have i0r2 : i0 ≠ tr.r2 := fun heq => ix.2.2.2.1 (heq ▸ hi0)
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have remapP : GatePhysical (tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx) := by
    apply remapList_physical
    intro i hi
    have hi256 := ix.2.2.2.2 i hi
    refine ⟨fun heq => ix.2.2.1 ((winj _ _ pv.1 hi256 heq) ▸ hi), fun heq => ix.2.2.2.1 ((winj _ _ pv.2.1 hi256 heq) ▸ hi)⟩
  have hP0 : (tr.idx.map (fun i => xs.getD i 0)).headD 0 = xs.getD i0 0 := by rw [hidx]; rfl
  have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by rw [hidx]; rfl
  have x0x : xs.getD i0 0 ∈ xs := wmem i0 i0lt
  have ex : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], ∀ a ∈ xs, a ≠ q :=
    fun q hq a ha heq => (hextx q hq).1 (heq ▸ ha)
  have ew : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], ∀ a ∈ work, a ≠ q :=
    fun q hq a ha heq => (hextx q hq).2 (heq ▸ ha)
  -- any chain wire (the control `xs[i0]` or a pool wire) together with the tail's other twelve wires is nodup
  have hlist : ∀ h, (h = xs.getD i0 0 ∨ h ∈ work) →
      [h, xs.getD tr.r1 0, xs.getD tr.r2 0, y0, c, f, g, O, D, H, t1, t2, u].Nodup := by
    intro h hh
    have hx1 := wmem _ pv.1
    have hx2 := wmem _ pv.2.1
    have hxx : xs.getD tr.r1 0 ≠ xs.getD tr.r2 0 := fun heq => pv.2.2.1 (winj _ _ pv.1 pv.2.1 heq)
    have hh1 : h ≠ xs.getD tr.r1 0 := by
      rcases hh with rfl | hw
      · exact fun heq => i0r1 (winj _ _ i0lt pv.1 heq)
      · exact fun heq => hdisj h hw (heq ▸ hx1)
    have hh2 : h ≠ xs.getD tr.r2 0 := by
      rcases hh with rfl | hw
      · exact fun heq => i0r2 (winj _ _ i0lt pv.2.1 heq)
      · exact fun heq => hdisj h hw (heq ▸ hx2)
    have hhe : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], h ≠ q := by
      intro q hq
      rcases hh with rfl | hw
      · exact ex q hq _ x0x
      · exact ew q hq _ hw
    have r1e : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], xs.getD tr.r1 0 ≠ q := fun q hq => ex q hq _ hx1
    have r2e : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], xs.getD tr.r2 0 ≠ q := fun q hq => ex q hq _ hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hhe r1e r2e
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hh1, hh2, hhe⟩, ⟨hxx, r1e⟩, r2e, ?_⟩
    simpa using hext
  have zP : GatePhysical (zeroWith (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)) := by
    rw [hP0, hPt]
    apply zeroWith_physical
    · rw [zp.2]
      exact List.nodup_cons.mpr ⟨fun hm => hdisj _ hm x0x, hwn⟩
    · intro b hb heq
      have hm := zeroPorts_mem _ _ b hb
      obtain ⟨i, hi, hie⟩ := List.mem_map.mp hm.1
      have hit : i ∈ tr.idx := by rw [hidx]; simp [hi]
      exact hdisj _ hm.2 (heq ▸ hie ▸ wmem i (ix.2.2.2.2 i hit))
    · intro h hh
      rw [zp.2] at hh
      apply otailL_physical
      exact hlist h (by simpa using hh)
  have xP : GatePhysical [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] := by
    simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]
  unfold oclassifier
  simp only [gatePhysical_append]
  exact ⟨remapP, xP, zP, xP, remapP⟩

end OutTail

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section GenBlock
open Secp256k1 ControlledPointLayout
attribute [local irreducible] wires

theorem pull_pull (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (s : State) :
    pullState f (pullState f s) = s := by
  apply State.extensionality
  · rfl
  · funext q; simp only [pullState, hf]

theorem pull_fixed (f : Wire → Wire) (s : State) (h : ∀ q, s.basis (f q) = s.basis q) :
    pullState f s = s := by
  apply State.extensionality
  · rfl
  · funext q; exact h q

/-- A program relabelled by an involution runs as the original on the pulled state, pulled back. -/
theorem run_rename_invol (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (P : Program) (m : List Bool)
    (s : State) : run (renameProgram f P) m s = pullState f (run P m (pullState f s)) := by
  have hinj : Function.Injective f := fun a b h => by rw [← hf a, ← hf b, h]
  have h := ECDSAAdd.run_rename f hinj P m s
  rw [← h, pull_pull f hf]

/-- Relabelling by an involution is invisible when the state before and after is symmetric. -/
theorem run_rename_noop (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (P : Program) (m : List Bool)
    (s : State) (hs : ∀ q, s.basis (f q) = s.basis q)
    (hr : ∀ q, (run P m s).basis (f q) = (run P m s).basis q) :
    run (renameProgram f P) m s = run P m s := by
  rw [run_rename_invol f hf, pull_fixed f s hs, pull_fixed f _ hr]

/-- A swap of two wires holding equal bits leaves the state unchanged. -/
theorem swap_sym (a b : Wire) (sw : Wire → Wire)
    (hsw : ∀ q, sw q = if q = a then b else if q = b then a else q) (st : BasisState)
    (h : st a = st b) : ∀ q, st (sw q) = st q := by
  intro q
  rw [hsw q]
  by_cases ha : q = a
  · subst ha; simp [h]
  · by_cases hb : q = b
    · subst hb; simp [ha, h]
    · simp [ha, hb]

theorem flags_not_point (q : Wire) (hq : q ∈ layout.inPlaceFlags) :
    q ∉ layout.point.x ++ layout.point.y := by
  have hD := layout.dialogUsed_nodup layout_nodup
  intro hp
  have c := List.nodup_iff_count_le_one.mp hD q
  have c1 : 1 ≤ layout.inPlaceFlags.count q := List.count_pos_iff.mpr hq
  have c2 : 1 ≤ (layout.point.x ++ layout.point.y).count q := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.dialogUsedWires, PointAddLayout.pointWires, List.count_append,
    List.count_cons] at c c2
  split_ifs at c <;> omega

theorem pool_not_point (q : Wire) (hq : q ∈ layout.dialogPool) :
    q ∉ layout.point.x ++ layout.point.y := by
  have hD := layout.dialogUsed_nodup layout_nodup
  intro hp
  have c := List.nodup_iff_count_le_one.mp hD q
  have c1 : 1 ≤ layout.dialogPool.count q := List.count_pos_iff.mpr hq
  have c2 : 1 ≤ (layout.point.x ++ layout.point.y).count q := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.dialogUsedWires, PointAddLayout.pointWires, List.count_append,
    List.count_cons] at c c2
  split_ifs at c <;> omega

theorem pool_not_flag (q : Wire) (hq : q ∈ layout.dialogPool) : q ∉ layout.inPlaceFlags := by
  have hD := layout.dialogUsed_nodup layout_nodup
  intro hp
  have c := List.nodup_iff_count_le_one.mp hD q
  have c1 : 1 ≤ layout.dialogPool.count q := List.count_pos_iff.mpr hq
  have c2 : 1 ≤ layout.inPlaceFlags.count q := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.dialogUsedWires, List.count_append] at c
  omega

theorem finite_not_flag : layout.point.finite ∉ layout.inPlaceFlags ∧
    layout.point.finite ∉ layout.point.x ++ layout.point.y := by
  have hD := layout.dialogUsed_nodup layout_nodup
  have c := List.nodup_iff_count_le_one.mp hD layout.point.finite
  simp only [ControlledPointLayout.dialogUsedWires, PointAddLayout.pointWires, List.count_append,
    List.count_cons, beq_self_eq_true, if_true] at c
  constructor
  · intro hp; have := List.count_pos_iff.mpr hp; omega
  · intro hp; have := List.count_pos_iff.mpr hp
    simp only [List.count_append] at this; omega

section GenRun
attribute [local irreducible] run ReflectionE1TickGapLow48.generic

/-- The relabelled generic block on a sentinel-coded state: only the coordinates move. -/
theorem gen_block_run {cx cy : Fp} (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      (ReflectionE1TickGapLow48.generic layout cx cy) (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t).basis q = t.basis q := by
  have hw := layout_widths
  have hn := layout_nodup
  have tinv := tauM_invol layout hn
  have einv := swapE_invol layout hw hn
  have dinv := swapD_invol layout hw hn
  have uinv : ∀ q, Wrapper5.U layout (Wrapper5.U layout q) = q := fun q => Equiv.swap_apply_self _ _ _
  have gflag : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have sflag : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have eflag : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have dflag : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have tauM_def : ∀ q, tauM layout q =
      if q = layout.core.generic then layout.genericSelect else
        if q = layout.genericSelect then layout.core.generic else q := fun q => rfl
  -- tauM fixes everything off the two generic flags
  have tfix : ∀ q, q ≠ layout.core.generic → q ≠ layout.genericSelect → tauM layout q = q := by
    intro q h1 h2; rw [tauM_def q, if_neg h1, if_neg h2]
  have pclean : ∀ q ∈ layout.dialogPool, t.basis q = false :=
    fun q hq => (regValue_zero _ _).mp hclean q hq
  have pne (q : Wire) (hq : q ∈ layout.dialogPool) : q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => pool_not_flag q hq (e ▸ gflag), fun e => pool_not_flag q hq (e ▸ sflag)⟩
  have xyne (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => flags_not_point _ gflag (e ▸ hq), fun e => flags_not_point _ sflag (e ▸ hq)⟩
  have fne : layout.point.finite ≠ layout.core.generic ∧ layout.point.finite ≠ layout.genericSelect :=
    ⟨fun e => finite_not_flag.1 (e ▸ gflag), fun e => finite_not_flag.1 (e ▸ sflag)⟩
  -- the generic block in its own frame
  generalize ht' : pullState (tauM layout) t = t'
  have t'def : ∀ q, t'.basis q = t.basis (tauM layout q) := by intro q; rw [← ht']; rfl
  have t'x : ∀ q ∈ layout.point.x ++ layout.point.y, t'.basis q = t.basis q := by
    intro q hq; rw [t'def, tfix q (xyne q hq).1 (xyne q hq).2]
  have v : PointDialogValues layout X Y G t'.basis t'.basis := by
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [← hx]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_left _ hq)
    · rw [← hy]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_right _ hq)
    · rw [t'def, tauM_def, if_pos rfl]; exact hg
    · apply (regValue_zero _ _).mpr
      intro q hq
      rw [t'def, tfix q (pne q hq).1 (pne q hq).2]; exact pclean q hq
  have hb : t'.basis layout.point.finite = false := by
    rw [t'def, tfix _ fne.1 fne.2]; exact hf
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn (ReflectionE1TickGapLow48.generic layout cx cy)
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) (ReflectionE1TickGapLow48.generic layout cx cy)) m t' = R0
    at ph0 v0
  have R0clean : ∀ q ∈ layout.dialogPool, R0.basis q = false :=
    fun q hq => (regValue_zero _ _).mp v0.clean q hq
  -- U swaps two clean pool sites
  have u684 := Square5Placement.pool_member layout hw 684 (by omega)
  have u717 := Square5Placement.pool_member layout hw 717 (by omega)
  have U_def : ∀ q, Wrapper5.U layout q = if q = layout.core.poolWire 684 then layout.core.poolWire 717
      else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
    intro q
    show (Equiv.swap _ _) q = _
    rw [Equiv.swap_apply_def]
  have R1 : run (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      (ReflectionE1TickGapLow48.generic layout cx cy))) m t' = R0 := by
    rw [run_rename_noop _ uinv]
    · exact hR0
    · apply swap_sym _ _ _ U_def
      have a : t'.basis (layout.core.poolWire 684) = false := by
        rw [t'def, tfix _ (pne _ u684).1 (pne _ u684).2]; exact pclean _ u684
      have b : t'.basis (layout.core.poolWire 717) = false := by
        rw [t'def, tfix _ (pne _ u717).1 (pne _ u717).2]; exact pclean _ u717
      rw [a, b]
    · rw [hR0]
      apply swap_sym _ _ _ U_def
      rw [R0clean _ u684, R0clean _ u717]
  -- tauM is the real swap between the generic flag and the generic select
  have R2 : run (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      (ReflectionE1TickGapLow48.generic layout cx cy)))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_invol _ tinv, ht', R1]
  -- R0 off the point registers equals the pulled start
  have R0rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → R0.basis q = t'.basis q := v0.rest
  have tq_off : ∀ q, q ∉ layout.point.x ++ layout.point.y → tauM layout q ∉ layout.point.x ++ layout.point.y := by
    intro q hq
    rw [tauM_def]
    split_ifs
    · exact flags_not_point _ sflag
    · exact flags_not_point _ gflag
    · exact hq
  have R2rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → (pullState (tauM layout) R0).basis q = t.basis q := by
    intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, R0rest _ (tq_off q hq), t'def, tinv]
  -- swapE and swapD act on clean wires before and after
  have spE := spare_pool layout hw
  have spD := spareD_pool layout hw
  have E_def : ∀ q, swapE layout q = if q = layout.core.equalNegY then spareWire layout
      else if q = spareWire layout then layout.core.equalNegY else q := fun q => rfl
  have D_def : ∀ q, swapD layout q = if q = layout.doubleSelect then spareD layout
      else if q = spareD layout then layout.doubleSelect else q := fun q => rfl
  have R2E : (pullState (tauM layout) R0).basis layout.core.equalNegY = false := by
    rw [R2rest _ (flags_not_point _ eflag)]; exact hE
  have R2Es : (pullState (tauM layout) R0).basis (spareWire layout) = false := by
    rw [R2rest _ (pool_not_point _ spE)]; exact pclean _ spE
  have R2D : (pullState (tauM layout) R0).basis layout.doubleSelect = false := by
    rw [R2rest _ (flags_not_point _ dflag)]; exact hD
  have R2Ds : (pullState (tauM layout) R0).basis (spareD layout) = false := by
    rw [R2rest _ (pool_not_point _ spD)]; exact pclean _ spD
  have R3 : run (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (ReflectionE1TickGapLow48.generic layout cx cy)))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ dinv _ _ _ (swap_sym _ _ _ D_def _ (by rw [hD, pclean _ spD]))
      (by rw [R3]; exact swap_sym _ _ _ D_def _ (by rw [R2D, R2Ds])), R3]
  rw [R4]
  refine ⟨?_, ?_, ?_, R2rest⟩
  · have e1 : (pullState (tauM layout) R0).phase = R0.phase := rfl
    rw [e1, ph0, ← ht']; rfl
  · rw [← v0.x]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_left _ hq)).1 (xyne q (List.mem_append_left _ hq)).2]
  · rw [← v0.y]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_right _ hq)).1 (xyne q (List.mem_append_right _ hq)).2]

end GenRun

end GenBlock

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section PreDecode
open Secp256k1 ControlledPointLayout

theorem ofBits_bit : ∀ (l : List Bool) (q : Nat), (ofBits l).testBit q = l.getD q false
  | [], q => by simp [ofBits]
  | b :: bs, 0 => by
      simp only [ofBits, List.getD_cons_zero]
      cases b <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
  | b :: bs, q + 1 => by
      simp only [ofBits, List.getD_cons_succ]
      rw [← ofBits_bit bs q, Nat.testBit_succ]
      congr 1
      cases b <;> simp <;> omega

/-- A safe local program on the ports `r` lifts to the layout. -/
theorem lift_list (n : Nat) (r : List Wire) (hl : r.length = n) (hnd : r.Nodup) (D : Program)
    (hD : wires D ⊆ Finset.range n) (s : State) (m : List Bool)
    (hsafe : safe D (regValue r s.basis) = true) :
    (run (renameProgram (LocalWireModel.label (fun q : Fin n => r.getD q.val 0)) D) m s).phase = s.phase ∧
    (∀ q (_ : q < n), (run (renameProgram (LocalWireModel.label (fun q : Fin n => r.getD q.val 0)) D) m s).basis
      (r.getD q 0) = (bitRun D (regValue r s.basis)).testBit q) ∧
    (∀ w, w ∉ r →
      (run (renameProgram (LocalWireModel.label (fun q : Fin n => r.getD q.val 0)) D) m s).basis w = s.basis w) := by
  have inj := LocalWireModel.listPorts_injective r hnd hl
  have hx : ∀ q (h : q < n), s.basis ((fun q : Fin n => r.getD q.val 0) ⟨q, h⟩) =
      (regValue r s.basis).testBit q := by
    intro q h
    exact (LocalWireModel.reg_bit r s.basis q (by omega)).symm
  have L := lift_local n _ inj D hD s m (regValue r s.basis) hx hsafe
  refine ⟨L.1, fun q hq => L.2.1 q hq, ?_⟩
  intro w hw
  apply L.2.2 w
  intro q hq e
  apply hw
  rw [e]
  show r.getD q 0 ∈ r
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- Corner flags `(O, D, H, I)` from `n = c ∧ ¬G`, the pivot bits and `y0`. -/
def predFlags (tr : Tri) (yc n r1 r2 y0 : Bool) : Bool × Bool × Bool × Bool :=
  if tr.role1 then
    let pB := r1 == tr.B.testBit tr.r1
    let pS := !pB && (r2 == tr.S.testBit tr.r2)
    let yC := y0 == yc
    (n && pS, n && !pB && !pS && yC, n && pB, n && !pB && !pS && !yC)
  else
    let pS := r1 == tr.S.testBit tr.r1
    let pB := !pS && (r2 == tr.B.testBit tr.r2)
    let yC := y0 == yc
    (n && pS, n && !pS && !pB && yC, n && pB, n && !pS && !pB && !yC)

theorem predecT_support (tr : Tri) (yc : Bool) : wires (predecT tr yc) ⊆ Finset.range 8 := by
  unfold predecT
  split_ifs <;>
  · cases tr.B.testBit tr.r1 <;> cases tr.S.testBit tr.r2 <;> cases tr.S.testBit tr.r1 <;>
      cases tr.B.testBit tr.r2 <;> cases yc <;> decide

section PreRun
attribute [local irreducible] run wires
set_option maxHeartbeats 400000

theorem predecL_run (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire)
    (hnd : [g, c, xr1, xr2, y0, O, D, H].Nodup) (s : State) (m : List Bool)
    (hz : s.basis O = false ∧ s.basis D = false ∧ s.basis H = false) :
    run (predecL tr yc g c xr1 xr2 y0 O D H) m s =
      ⟨s.phase, writeBit (writeBit (writeBit (writeBit s.basis g
        (predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0)).2.2.2) O
        (predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0)).1) D
        (predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0)).2.1) H
        (predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0)).2.2.1⟩ := by
  generalize hpf : predFlags tr yc (s.basis g ^^ s.basis c) (s.basis xr1) (s.basis xr2) (s.basis y0) = pf
  have nd := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or] at nd
  unfold predecL
  set r : List Wire := [g, c, xr1, xr2, y0, O, D, H] with hr
  have hl : r.length = 8 := rfl
  let x := regValue r s.basis
  have hb (q : Nat) (hq : q < 8) : x.testBit q = s.basis (r.getD q 0) :=
    LocalWireModel.reg_bit r s.basis q (by omega)
  have x5 : x < 2^5 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases h8 : i < 8
    · interval_cases i
      · rw [hb 5 (by decide)]; exact hz.1
      · rw [hb 6 (by decide)]; exact hz.2.1
      · rw [hb 7 (by decide)]; exact hz.2.2
    · have hlt : x < 2^8 := by simpa [x, hr] using regValue_lt r s.basis
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have b0 : x.testBit 0 = s.basis g := hb 0 (by decide)
  have b1 : x.testBit 1 = s.basis c := hb 1 (by decide)
  have b2 : x.testBit 2 = s.basis xr1 := hb 2 (by decide)
  have b3 : x.testBit 3 = s.basis xr2 := hb 3 (by decide)
  have b4 : x.testBit 4 = s.basis y0 := hb 4 (by decide)
  have core : safe (predecT tr yc) x = true ∧
      bitRun (predecT tr yc) x = ofBits [pf.2.2.2, s.basis c, s.basis xr1, s.basis xr2, s.basis y0,
        pf.1, pf.2.1, pf.2.2.1] := by
    rw [← hpf]
    unfold predecT
    by_cases ro : tr.role1 = true
    · have k := predec1_ok (tr.B.testBit tr.r1) (tr.S.testBit tr.r2) yc ⟨x, x5⟩
      simp only [ro, if_true]
      refine ⟨k.1, ?_⟩
      rw [k.2]
      simp only [predOut1, b0, b1, b2, b3, b4, predFlags, ro, if_true]
    · have ro' : tr.role1 = false := by simpa using ro
      have k := predec2_ok (tr.S.testBit tr.r1) (tr.B.testBit tr.r2) yc ⟨x, x5⟩
      simp only [ro', Bool.false_eq_true, if_false]
      refine ⟨k.1, ?_⟩
      rw [k.2]
      simp only [predOut2, b0, b1, b2, b3, b4, predFlags, ro', Bool.false_eq_true, if_false]
  have L := lift_list 8 r hl hnd (predecT tr yc) (predecT_support tr yc) s m core.1
  rw [core.2] at L
  generalize hR : run (renameProgram (LocalWireModel.label (fun q : Fin 8 => r.getD q.val 0))
    (predecT tr yc)) m s = R at L ⊢
  apply State.extensionality
  · exact L.1
  · funext w
    have pv (q : Nat) (hq : q < 8) := L.2.1 q hq
    have p0 := pv 0 (by decide)
    have p1 := pv 1 (by decide)
    have p2 := pv 2 (by decide)
    have p3 := pv 3 (by decide)
    have p4 := pv 4 (by decide)
    have p5 := pv 5 (by decide)
    have p6 := pv 6 (by decide)
    have p7 := pv 7 (by decide)
    simp only [ofBits_bit, List.getD_cons_zero, List.getD_cons_succ] at p0 p1 p2 p3 p4 p5 p6 p7
    have e0 : r.getD 0 0 = g := rfl
    have e1 : r.getD 1 0 = c := rfl
    have e2 : r.getD 2 0 = xr1 := rfl
    have e3 : r.getD 3 0 = xr2 := rfl
    have e4 : r.getD 4 0 = y0 := rfl
    have e5 : r.getD 5 0 = O := rfl
    have e6 : r.getD 6 0 = D := rfl
    have e7 : r.getD 7 0 = H := rfl
    rw [e0] at p0; rw [e1] at p1; rw [e2] at p2; rw [e3] at p3; rw [e4] at p4; rw [e5] at p5
    rw [e6] at p6; rw [e7] at p7
    show R.basis w = writeBit (writeBit (writeBit (writeBit s.basis g pf.2.2.2) O pf.1) D pf.2.1) H pf.2.2.1 w
    simp only [writeBit, Function.update_apply]
    by_cases wH : w = H
    · rw [if_pos wH, wH]; exact p7
    by_cases wD : w = D
    · rw [if_neg wH, if_pos wD, wD]; exact p6
    by_cases wO : w = O
    · rw [if_neg wH, if_neg wD, if_pos wO, wO]; exact p5
    by_cases wg : w = g
    · rw [if_neg wH, if_neg wD, if_neg wO, if_pos wg, wg]; exact p0
    rw [if_neg wH, if_neg wD, if_neg wO, if_neg wg]
    by_cases wc : w = c
    · rw [wc]; exact p1
    by_cases w1 : w = xr1
    · rw [w1]; exact p2
    by_cases w2 : w = xr2
    · rw [w2]; exact p3
    by_cases w4 : w = y0
    · rw [w4]; exact p4
    exact L.2.2 w (by simp [hr, wH, wD, wO, wg, wc, w1, w2, w4])

end PreRun

end PreDecode

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

section OutLocal
open Challenge

/-! ### Local-wire facts of the decode and predecode gadgets (checked over every parameter) -/

/-- Every decode variant writes local wires 6 (`.CCX 4 9 6`) and 7, 8, 9 (its CCX scratch targets). -/
theorem c2c_decodeT_mem (tr : Tri) (yb : Bool) : ({6, 7, 8, 9} : Finset Nat) ⊆ wires (decodeT tr yb) := by
  unfold decodeT
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.A.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c; generalize tr.S.testBit tr.r2 = d
    cases a <;> cases b <;> cases c <;> cases d <;> cases yb <;> decide

theorem c2c_predecT_support (tr : Tri) (yc : Bool) : wires (predecT tr yc) ⊆ Finset.range 8 := by
  unfold predecT
  split_ifs <;>
  · generalize tr.B.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.S.testBit tr.r1 = a'; generalize tr.B.testBit tr.r2 = b'
    cases a <;> cases b <;> cases a' <;> cases b' <;> cases yc <;> decide

theorem c2c_predecT_physical (tr : Tri) (yc : Bool) : GatePhysical (predecT tr yc) := by
  unfold predecT
  split_ifs <;> apply gatePhysical_of_all <;>
  · generalize tr.B.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.S.testBit tr.r1 = a'; generalize tr.B.testBit tr.r2 = b'
    cases a <;> cases b <;> cases a' <;> cases b' <;> cases yc <;> decide

theorem c2c_predec_slots (a b yc : Bool) :
    gateSlots (predec1 a b yc) ≤ 13 ∧ gateSlots (predec2 a b yc) ≤ 13 := by
  cases a <;> cases b <;> cases yc <;> decide

end OutLocal

section OutCounts
open Secp256k1 ControlledPointLayout Challenge
attribute [local irreducible] wires

/-! ### Facts of the merged input stage -/

theorem c2c_tail_mem (tr : Tri) (yb : Bool) (xr1 xr2 y0 c f g g1 wB t h : Wire) :
    g ∈ wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) ∧ g1 ∈ wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) ∧
    wB ∈ wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) ∧ t ∈ wires (tail tr yb xr1 xr2 y0 c f g g1 wB t h) := by
  have hm := c2c_decodeT_mem tr yb
  unfold tail
  rw [renameProgram_support]
  exact ⟨Finset.mem_image.mpr ⟨6, hm (by simp), rfl⟩, Finset.mem_image.mpr ⟨7, hm (by simp), rfl⟩,
    Finset.mem_image.mpr ⟨8, hm (by simp), rfl⟩, Finset.mem_image.mpr ⟨9, hm (by simp), rfl⟩⟩

theorem c2c_pool256 (q : Wire) (hq : q ∈ layout.dialogPool.take 256) :
    q ∈ layout.dialogPool.take 253 ∨ q = layout.dialogPool.getD 253 0 ∨ q = layout.dialogPool.getD 254 0 ∨
      q = layout.dialogPool.getD 255 0 := by
  have hpl := dialogPool_length layout layout_widths
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  have hi' : i < 256 := by simp at hi; omega
  have hil : i < layout.dialogPool.length := by simp at hi; omega
  rw [List.getElem_take]
  by_cases h253 : i < 253
  · left
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  · right
    have h3 : i = 253 ∨ i = 254 ∨ i = 255 := by omega
    rcases h3 with rfl | rfl | rfl
    · left; rw [List.getD_eq_getElem _ _ hil]
    · right; left; rw [List.getD_eq_getElem _ _ hil]
    · right; right; rw [List.getD_eq_getElem _ _ hil]

theorem stage_wires_mem {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    (∀ q ∈ layout.dialogPool.take 256, q ∈ wires (stage layout (.some hc))) ∧
    layout.genericSelect ∈ wires (stage layout (.some hc)) := by
  have v := triOf_valid hc
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split (triOf (.some hc)) v
  have hpl := dialogPool_length layout layout_widths
  have hwl : (layout.dialogPool.take 253).length = 253 := by simp; omega
  have hPt : ((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).tail.length = 253 := by
    rw [hidx]; simp [hitl]
  have zp := zeroPorts_maps ((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).tail
    (layout.dialogPool.take 253) (by rw [hPt, hwl])
  have toStage : ∀ q, q ∈ wires (zeroWith (tail (triOf (.some hc)) (yBit (dialogExceptionPoint (.some hc)))
        (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0)
        (yLow layout) layout.control layout.point.finite layout.genericSelect (layout.dialogPool.getD 253 0)
        (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0))
        (((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).headD 0)
        (zeroPorts ((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).tail
          (layout.dialogPool.take 253))) →
      q ∈ wires (stage layout (.some hc)) := by
    intro q hq
    unfold stage classifier
    simp only [wires_append, Finset.mem_union]
    exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
  have tm := fun (w : Wire) (hw : ∀ h, w ∈ wires (tail (triOf (.some hc)) (yBit (dialogExceptionPoint (.some hc)))
        (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0)
        (yLow layout) layout.control layout.point.finite layout.genericSelect (layout.dialogPool.getD 253 0)
        (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) h)) =>
    toStage w (InputSentinelAux.zeroWith_tail_mem _ w hw _ _)
  have ct := fun h => c2c_tail_mem (triOf (.some hc)) (yBit (dialogExceptionPoint (.some hc)))
    (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0)
    (yLow layout) layout.control layout.point.finite layout.genericSelect (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) h
  refine ⟨?_, tm _ (fun h => (ct h).1)⟩
  intro q hq
  rcases c2c_pool256 q hq with hw | rfl | rfl | rfl
  · have hm : q ∈ (zeroPorts ((triOf (.some hc)).idx.map (fun i => layout.point.x.getD i 0)).tail
        (layout.dialogPool.take 253)).map ZeroBit.work := by rw [zp.2]; exact hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    exact toStage _ (InputSentinelAux.zeroWith_work_mem _ _ _ b hb)
  · exact tm _ (fun h => (ct h).2.1)
  · exact tm _ (fun h => (ct h).2.2.1)
  · exact tm _ (fun h => (ct h).2.2.2)

/-! ### The predecode block on its eight wires -/

theorem predecL_support (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire) :
    wires (predecL tr yc g c xr1 xr2 y0 O D H) ⊆ ([g, c, xr1, xr2, y0, O, D, H] : List Wire).toFinset := by
  unfold predecL
  rw [renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have ha8 : a < 8 := Finset.mem_range.mp (c2c_predecT_support tr yc ha)
  simp only [LocalWireModel.label, dif_pos ha8]
  interval_cases a <;> simp

theorem predecL_physical (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire)
    (hnd : [g, c, xr1, xr2, y0, O, D, H].Nodup) : GatePhysical (predecL tr yc g c xr1 xr2 y0 O D H) := by
  have inj := LocalWireModel.listPorts_injective [g, c, xr1, xr2, y0, O, D, H] hnd (n := 8) (by simp)
  unfold predecL
  exact gatePhysical_rename_support _ _ (fun a ha b hb heq =>
    LocalWireModel.label_injective _ inj a (c2c_predecT_support tr yc ha) b (c2c_predecT_support tr yc hb) heq)
    (c2c_predecT_physical tr yc)

/-- Toffolis, measurements and the exact worst slot count (13) over both roles. -/
theorem predecL_counts (tr : Tri) (yc : Bool) (g c xr1 xr2 y0 O D H : Wire) :
    toffoliCount (predecL tr yc g c xr1 xr2 y0 O D H) = 3 ∧
    measurementCount (predecL tr yc g c xr1 xr2 y0 O D H) = 0 ∧
    gateSlots (predecL tr yc g c xr1 xr2 y0 O D H) ≤ 13 := by
  unfold predecL
  rw [(renameProgram_counts _ _).1, (renameProgram_counts _ _).2, rename_gateSlots]
  unfold predecT
  by_cases ro : tr.role1 = true
  · rw [if_pos ro]
    exact ⟨(predec_counts _ _ _).1, (predec_counts _ _ _).2.1, (c2c_predec_slots _ _ _).1⟩
  · rw [if_neg ro]
    exact ⟨(predec_counts _ _ _).2.2.1, (predec_counts _ _ _).2.2.2, (c2c_predec_slots _ _ _).2⟩

/-! ### Counts of the merged output stage -/

theorem c2c_ocorners_slots (L : ControlledPointLayout) (hw : L.Widths) (C : Point) :
    gateSlots (ocorners L C) ≤ 2048 := by
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have a1 := maskedConstant_gateSlots_le (parkWire L) L.point.x (FiniteFlagInterval.sentinel ^^^ pairCode C)
  have a2 := maskedConstant_gateSlots_le (parkWire L) L.point.y (pointY C)
  have a3 := maskedConstant_gateSlots_le L.doubleSelect L.point.x (pairCode C ^^^ pairCode (dialogExceptionPoint C))
  have a4 := maskedConstant_gateSlots_le L.doubleSelect L.point.y (pointY C ^^^ pointY (C + C))
  have a5 := maskedConstant_gateSlots_le L.genericSelect L.point.x (pairCode C ^^^ FiniteFlagInterval.sentinel)
  have a6 := maskedConstant_gateSlots_le L.genericSelect L.point.y (pointY (-C))
  have a7 := maskedConstant_gateSlots_le L.core.equalNegY L.point.x (pairCode (dialogExceptionPoint C) ^^^ pairCode C)
  have a8 := maskedConstant_gateSlots_le L.core.equalNegY L.point.y
    (pointY (dialogExceptionPoint C) ^^^ pointY (-C))
  rw [hx] at a1 a3 a5 a7
  rw [hy] at a2 a4 a6 a8
  simp only [ocorners, gateSlots_append]
  omega

/-- The finite exception enable fact already proved in the imported FusedFlags module. -/
theorem exceptionBit_finite {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    exceptionBit (.some hc : Point) = true := by
  exact NoThreeTorsion.enabled hc

/-- 260 Toffolis, 253 + 8 measurements, and the slot bounds summed:
13 (predecode) + 2048 (corners) + 3342 (output classifier) + 258 (sentinel recode). -/
theorem outStage_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (outStage layout (.some hc)) = 260 ∧
    measurementCount (outStage layout (.some hc)) = 253 + 8 ∧
    gateSlots (outStage layout (.some hc)) ≤ 5661 := by
  have hpl := dialogPool_length layout layout_widths
  have hwl : (layout.dialogPool.take 253).length = 253 := by simp; omega
  have pc := predecL_counts (triOf (.some hc)) (yBit (.some hc)) layout.genericSelect layout.control
    (layout.point.x.getD (triOf (.some hc)).r1 0) (layout.point.x.getD (triOf (.some hc)).r2 0) (yLow layout)
    (parkWire layout) layout.doubleSelect layout.core.equalNegY
  have oc := ocorners_counts layout (.some hc)
  have os := c2c_ocorners_slots layout layout_widths (.some hc)
  have cc := oclassifier_counts (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc : Point) + .some hc)) (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253)
    (yLow layout) layout.control layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect
    layout.core.equalNegY (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) hwl
  have cs := oclassifier_slots (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc : Point) + .some hc)) (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253)
    (yLow layout) layout.control layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect
    layout.core.equalNegY (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) hwl
  have z := FiniteFlagInterval.zrep_counts layout
  have zs := FiniteFlagInterval.zrep_slots layout layout_widths
  unfold outStage
  simp only [exceptionBit_finite hc, ↓reduceIte] at cc cs ⊢
  simp only [toffoliCount_append, measurementCount_append, gateSlots_append, pc.1, pc.2.1, oc.1, oc.2,
    cc.1, cc.2, z.1, z.2]
  have ps := pc.2.2
  refine ⟨by trivial, by trivial, ?_⟩
  omega

end OutCounts

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section OutCompose
open Secp256k1 ControlledPointLayout
attribute [local irreducible] wires run

/-- Pivot bits of the three constants in each role. -/
theorem tri_bits (tr : Tri) (v : tr.Valid) :
    (tr.role1 = true → tr.A.testBit tr.r1 = tr.S.testBit tr.r1 ∧ tr.B.testBit tr.r1 = !tr.S.testBit tr.r1 ∧
      tr.A.testBit tr.r2 = !tr.S.testBit tr.r2) ∧
    (tr.role1 = false → tr.A.testBit tr.r1 = tr.B.testBit tr.r1 ∧ tr.S.testBit tr.r1 = !tr.A.testBit tr.r1 ∧
      tr.A.testBit tr.r2 = !tr.B.testBit tr.r2) := by
  have h1 : tr.B.testBit tr.r1 ≠ tr.S.testBit tr.r1 := (firstDiff_spec tr.B tr.S v.hB v.hS v.BS).2
  constructor
  · intro ro
    have eq1 : tr.A.testBit tr.r1 = tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
    have er2 : tr.r2 = firstDiff tr.A tr.S := by simp [Tri.r2, ro]
    have d2 := (firstDiff_spec tr.A tr.S v.hA v.hS v.AS).2
    rw [← er2] at d2
    refine ⟨eq1, ?_, ?_⟩
    · revert h1; cases tr.B.testBit tr.r1 <;> cases tr.S.testBit tr.r1 <;> simp
    · revert d2; cases tr.A.testBit tr.r2 <;> cases tr.S.testBit tr.r2 <;> simp
  · intro ro
    have ne1 : tr.A.testBit tr.r1 ≠ tr.S.testBit tr.r1 := by simpa [Tri.role1] using ro
    have er2 : tr.r2 = firstDiff tr.A tr.B := by simp [Tri.r2, ro]
    have d2 := (firstDiff_spec tr.A tr.B v.hA v.hB v.AB).2
    rw [← er2] at d2
    refine ⟨?_, ?_, ?_⟩
    · revert h1 ne1; cases tr.A.testBit tr.r1 <;> cases tr.B.testBit tr.r1 <;> cases tr.S.testBit tr.r1 <;> simp
    · revert ne1; cases tr.A.testBit tr.r1 <;> cases tr.S.testBit tr.r1 <;> simp
    · revert d2; cases tr.A.testBit tr.r2 <;> cases tr.B.testBit tr.r2 <;> simp

/-- The corner decode on a constant word gives its one-hot pattern. -/
theorem predFlags_S (tr : Tri) (v : tr.Valid) (yc n y0 : Bool) :
    predFlags tr yc n (tr.S.testBit tr.r1) (tr.S.testBit tr.r2) y0 = (n, false, false, false) := by
  have tb := tri_bits tr v
  unfold predFlags
  cases ro : tr.role1
  · obtain ⟨_, e2, _⟩ := tb.2 ro
    simp only [Bool.false_eq_true, if_false]
    rw [e2]; cases n <;> cases tr.A.testBit tr.r1 <;> cases (tr.S.testBit tr.r2 == tr.B.testBit tr.r2) <;> simp
  · obtain ⟨_, e2, _⟩ := tb.1 ro
    simp only [if_true]
    rw [e2]; cases n <;> cases tr.S.testBit tr.r1 <;> simp

theorem predFlags_B (tr : Tri) (v : tr.Valid) (yc n y0 : Bool) :
    predFlags tr yc n (tr.B.testBit tr.r1) (tr.B.testBit tr.r2) y0 = (false, false, n, false) := by
  have tb := tri_bits tr v
  unfold predFlags
  cases ro : tr.role1
  · obtain ⟨e1, e2, _⟩ := tb.2 ro
    simp only [Bool.false_eq_true, if_false]
    rw [e2, ← e1]; cases n <;> cases tr.A.testBit tr.r1 <;> simp
  · simp only [if_true]
    cases n <;> simp

theorem predFlags_A (tr : Tri) (v : tr.Valid) (yc n y0 : Bool) :
    predFlags tr yc n (tr.A.testBit tr.r1) (tr.A.testBit tr.r2) y0 =
      (false, n && (y0 == yc), false, n && !(y0 == yc)) := by
  have tb := tri_bits tr v
  unfold predFlags
  cases ro : tr.role1
  · obtain ⟨e1, e2, e3⟩ := tb.2 ro
    simp only [Bool.false_eq_true, if_false]
    rw [e2, e3]; cases n <;> cases tr.A.testBit tr.r1 <;> cases tr.B.testBit tr.r2 <;> cases (y0 == yc) <;> simp
  · obtain ⟨e1, e2, e3⟩ := tb.1 ro
    simp only [if_true]
    rw [e1, e2, e3]; cases n <;> cases tr.S.testBit tr.r1 <;> cases tr.S.testBit tr.r2 <;> cases (y0 == yc) <;> simp

theorem predFlags_zero (tr : Tri) (yc r1 r2 y0 : Bool) :
    predFlags tr yc false r1 r2 y0 = (false, false, false, false) := by
  unfold predFlags; split_ifs <;> simp

theorem pointFinite_of_ne {P : Point} (h : P ≠ 0) : pointFinite P = true := by
  cases P with
  | zero => exact absurd rfl h
  | some _ => rfl

theorem codeX_finite {P : Point} (h : P ≠ 0) : codeX P = pointX P := by
  simp [codeX, pointFinite_of_ne h]

open Classical in
/-- On the post-generic state the corner decode yields the four dialog flags. -/
theorem predFlags_dialog {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    predFlags (triOf (.some hc)) (yBit (.some hc)) (dialogOrdinary b R (.some hc) ^^ b)
      ((codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R)).testBit (triOf (.some hc)).r1)
      ((codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R)).testBit (triOf (.some hc)).r2)
      (yBit (if dialogOrdinary b R (.some hc) then R + .some hc else R)) =
    (dialogInfinity b R, dialogDouble b R (.some hc), dialogException b R (.some hc),
      dialogInversePoint b R (.some hc)) := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hnC : -C ≠ 0 := neg_ne_zero.mpr hC
  have hCn : C ≠ -C := (doubling_enabled_iff hc).mp (of_decide_eq_true (cy_ne_neg hc))
  have v := triOf_valid hc
  have eA : (triOf C).A = pointX C := rfl
  have eB : (triOf C).B = pointX (dialogExceptionPoint C) := rfl
  have eS : (triOf C).S = FiniteFlagInterval.sentinel := rfl
  by_cases hg : dialogOrdinary b R C = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R C hC).mp hg
    subst hb
    rw [hg, Bool.xor_self, predFlags_zero]
    simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, h0, h1, h2, h3]
  · have hg' : dialogOrdinary b R C = false := by simpa using hg
    rw [hg']
    simp only [Bool.false_eq_true, if_false, Bool.false_xor]
    cases b with
    | false =>
      rw [predFlags_zero]
      simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint]
    | true =>
      by_cases h0 : R = 0
      · subst h0
        have e : codeX (0 : Point) = (triOf C).S := rfl
        rw [e, predFlags_S _ v]
        simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, Ne.symm hC, Ne.symm hnC]
        intro a _ _ e; exact a e.symm
      by_cases h1 : R = C
      · subst h1
        rw [codeX_finite hC, ← eA, predFlags_A _ v]
        simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, hC, hCn]
        intro _ a _ e; exact a e.symm
      by_cases h2 : R = -C
      · subst h2
        rw [codeX_finite hnC, DHClass.pointX_neg, ← eA, predFlags_A _ v, yBit_neg hc]
        have hn2 : -C ≠ C := fun e => hCn e.symm
        simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, hnC, hn2]
        exact ⟨rfl, fun _ _ a e => a e.symm, rfl⟩
      have h3 : R = dialogExceptionPoint C := by
        by_contra h3
        exact hg ((dialogOrdinary_true true R C hC).mpr ⟨rfl, h0, h1, h2, h3⟩)
      subst h3
      rw [codeX_finite h0, ← eB, predFlags_B _ v]
      simp [dialogInfinity, dialogDouble, dialogException, dialogInversePoint, h0, h1, h2]

theorem xor_cancel (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

open Classical in
/-- The sentinel-coded corner write-back turns `R1` into the output `S`. -/
theorem corners_value {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ^^^
        cornerX (.some hc) (dialogInfinity b R) (dialogDouble b R (.some hc))
          (dialogInversePoint b R (.some hc)) (dialogException b R (.some hc)) =
      codeX (if b then R + .some hc else R) ∧
    pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ^^^
        cornerY (.some hc) (dialogInfinity b R) (dialogDouble b R (.some hc))
          (dialogInversePoint b R (.some hc)) (dialogException b R (.some hc)) =
      pointY (if b then R + .some hc else R) := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hnC : -C ≠ 0 := neg_ne_zero.mpr hC
  have hCn : C ≠ -C := (doubling_enabled_iff hc).mp (of_decide_eq_true (cy_ne_neg hc))
  have h2C : C + C ≠ 0 := fun e => hCn (eq_neg_of_add_eq_zero_left e)
  have z0 : cornerX C false false false false = 0 := by simp [cornerX]
  have z1 : cornerY C false false false false = 0 := by simp [cornerY]
  by_cases hg : dialogOrdinary b R C = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R C hC).mp hg
    subst hb
    have f0 : dialogInfinity true R = false := by simp [dialogInfinity, h0]
    have f1 : dialogDouble true R C = false := by simp [dialogDouble, h1]
    have f2 : dialogInversePoint true R C = false := by simp [dialogInversePoint, h2]
    have f3 : dialogException true R C = false := by simp [dialogException, h3]
    rw [hg, f0, f1, f2, f3, z0, z1]
    simp
  · have hg' : dialogOrdinary b R C = false := by simpa using hg
    rw [hg']
    simp only [Bool.false_eq_true, if_false]
    cases b with
    | false =>
      have f0 : dialogInfinity false R = false := rfl
      have f1 : dialogDouble false R C = false := rfl
      have f2 : dialogInversePoint false R C = false := rfl
      have f3 : dialogException false R C = false := rfl
      rw [f0, f1, f2, f3, z0, z1]
      simp
    | true =>
      simp only [if_true]
      by_cases h0 : R = 0
      · subst h0
        have f0 : dialogInfinity true 0 = true := by simp [dialogInfinity]
        have f1 : dialogDouble true 0 C = false := by simp [dialogDouble, Ne.symm hC]
        have f2 : dialogInversePoint true 0 C = false := by simp [dialogInversePoint, Ne.symm hnC]
        rw [f0, f1, f2, dialogException_zero, zero_add]
        have e : codeX (0 : Point) = FiniteFlagInterval.sentinel := rfl
        simp only [cornerX, cornerY, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, e, xor_cancel]
        exact ⟨(codeX_finite hC).symm, by simp [pointY, coordinates]⟩
      by_cases h1 : R = C
      · subst h1
        have f0 : dialogInfinity true C = false := by simp [dialogInfinity, hC]
        have f1 : dialogDouble true C C = true := by simp [dialogDouble, hCn]
        have f2 : dialogInversePoint true C C = false := by simp [dialogInversePoint, hCn]
        have f3 : dialogException true C C = false := by
          simp [dialogException]
          intro _ a _ e; exact a e.symm
        rw [f0, f1, f2, f3]
        simp only [cornerX, cornerY, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, Nat.zero_xor,
          codeX_finite hC, codeX_finite h2C, pairCode, xor_cancel]
        refine ⟨?_, trivial⟩
        unfold dialogExceptionPoint
        rw [DHClass.pointX_neg]
      by_cases h2 : R = -C
      · subst h2
        have f0 : dialogInfinity true (-C) = false := by simp [dialogInfinity, hnC]
        have f1 : dialogDouble true (-C) C = false := by
          simp only [dialogDouble, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          right; intro e; exact hCn e.symm
        have f2 : dialogInversePoint true (-C) C = true := by simp [dialogInversePoint]
        have f3 : dialogException true (-C) C = false := by
          simp [dialogException]
          intro _ _ a e; exact a e.symm
        rw [f0, f1, f2, f3, neg_add_cancel]
        simp only [cornerX, cornerY, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, Nat.zero_xor,
          codeX_finite hnC, pairCode, DHClass.pointX_neg, xor_cancel]
        refine ⟨rfl, ?_⟩
        rw [Nat.xor_self]; rfl
      have h3 : R = dialogExceptionPoint C := by
        by_contra h3
        exact hg ((dialogOrdinary_true true R C hC).mpr ⟨rfl, h0, h1, h2, h3⟩)
      subst h3
      have f0 : dialogInfinity true (dialogExceptionPoint C) = false := by simp [dialogInfinity, h0]
      have f1 : dialogDouble true (dialogExceptionPoint C) C = false := by simp [dialogDouble, h1]
      have f2 : dialogInversePoint true (dialogExceptionPoint C) C = false := by simp [dialogInversePoint, h2]
      have f3 : dialogException true (dialogExceptionPoint C) C = true := by
        simp [dialogException, h0, h1, h2]
      rw [f0, f1, f2, f3, dialog_exception_add]
      simp only [cornerX, cornerY, if_true, Bool.false_eq_true, if_false, Nat.xor_zero, Nat.zero_xor,
        codeX_finite h0, codeX_finite hnC, pairCode, DHClass.pointX_neg, xor_cancel]
      exact ⟨by trivial, by trivial⟩

theorem eq_of_x_ybit {x₁ y₁ x₂ y₂ : Fp} (h₁ : curve.toAffine.Nonsingular x₁ y₁)
    (h₂ : curve.toAffine.Nonsingular x₂ y₂) (hx : x₁.val = x₂.val)
    (hy : yBit (.some h₁ : Point) = yBit (.some h₂)) : (.some h₁ : Point) = .some h₂ := by
  have hxe : x₁ = x₂ := ZMod.val_injective _ hx
  subst hxe
  by_cases hinv : y₁ = -y₂
  · exfalso
    have e : (.some h₁ : Point) = -(.some h₂ : Point) := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq, negY_eq_neg, hinv, and_self]
    rw [e, yBit_neg h₂] at hy
    cases hb : yBit (.some h₂ : Point) <;> simp [hb] at hy
  · have := y_eq_of_x_eq_of_not_inverse h₁ h₂ rfl hinv
    subst this; rfl

theorem curve_x_ne_sentinel {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    x.val ≠ FiniteFlagInterval.sentinel := by
  intro e
  apply CodexAffineMath.curve_x_not_matches h
  have hs : FiniteFlagInterval.sentinel = p - 1 := by norm_num [FiniteFlagInterval.sentinel, p]
  rw [e, hs]; exact CodexAffineMath.sentinel_matches

/-- A sentinel-coded abscissa and a `y` parity determine a finite point. -/
theorem code_match (S P : Point) (hP : P ≠ 0) :
    (codeX S = pointX P ∧ yBit S = yBit P) ↔ S = P := by
  constructor
  · rintro ⟨hx, hy⟩
    cases P with
    | zero => exact absurd rfl hP
    | @some xp yp hp =>
      cases S with
      | zero =>
        exfalso
        change FiniteFlagInterval.sentinel = xp.val at hx
        exact curve_x_ne_sentinel hp hx.symm
      | @some xs ys hs =>
        change xs.val = xp.val at hx
        exact eq_of_x_ybit hs hp hx hy
  · rintro rfl; exact ⟨codeX_finite hP, rfl⟩

theorem code_sentinel (S : Point) : codeX S = FiniteFlagInterval.sentinel ↔ S = 0 := by
  cases S with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @some xs ys hs =>
    have e1 : codeX (.some hs : Point) = xs.val := rfl
    rw [e1]
    exact ⟨fun h => absurd h (curve_x_ne_sentinel hs),
      fun h => absurd h (WeierstrassCurve.Affine.Point.some_ne_zero hs)⟩

/-- The output classifier's match bits are equality tests with the three constants. -/
theorem oX_eq (tr : Tri) (v : tr.Valid) (xs : List Wire) (hxl : xs.length = 256) (st : BasisState)
    (K : Nat) (hK : K < 2^256) (hKt : ∀ i, tr.tgt i (tr.pat K) = K.testBit i) :
    oX tr K xs st = decide (regValue xs st = K) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  have hXlt : regValue xs st < 2^256 := by have := regValue_lt xs st; rwa [hxl] at this
  have xbit : ∀ i, i < 256 → st (xs.getD i 0) = (regValue xs st).testBit i :=
    fun i hi => (LocalWireModel.reg_bit xs st i (by omega)).symm
  have hm : matchBit tr xs st =
      decide (∀ i ∈ tr.idx, (regValue xs st).testBit i = tr.tgt i (tr.pat (regValue xs st))) := by
    unfold matchBit
    rw [xbit _ pv.1, xbit _ pv.2.1]
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true, decide_eq_true_iff]
    apply forall₂_congr
    intro i hi
    rw [xbit i (ix.2.2.2.2 i hi)]
    simp [Tri.pat]
  unfold oX
  rw [hm, xbit _ pv.1, xbit _ pv.2.1]
  have hp : ((regValue xs st).testBit tr.r1, (regValue xs st).testBit tr.r2) = tr.pat (regValue xs st) := rfl
  rw [hp]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  exact Tri.match_iff v _ K hXlt hK hKt

theorem yLow_bit (st : BasisState) : st (yLow layout) = (regValue layout.point.y st).testBit 0 := by
  have hyl : layout.point.y.length = 256 := layout_widths.inputY
  have e : yLow layout = layout.point.y.getD 0 0 := by
    unfold yLow
    cases hy : layout.point.y with
    | nil => rw [hy] at hyl; simp at hyl
    | cons a l => rfl
  rw [e, LocalWireModel.reg_bit layout.point.y st 0 (by rw [hyl]; decide)]

theorem pointY_bit0 (P : Point) : (pointY P).testBit 0 = yBit P := by
  unfold yBit
  rw [Nat.testBit_zero]

/-- Fixed wires of the output stage in the concrete layout. -/
theorem out_fixed :
    [layout.genericSelect, layout.control, yLow layout, parkWire layout, layout.doubleSelect,
      layout.core.equalNegY].Nodup ∧
    (∀ q ∈ [layout.genericSelect, layout.control, yLow layout, parkWire layout, layout.doubleSelect,
      layout.core.equalNegY], q ∉ layout.point.x) ∧
    [yLow layout, layout.control, layout.point.finite, layout.genericSelect, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY, layout.dialogPool.getD 253 0,
      layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0].Nodup ∧
    (∀ q ∈ [yLow layout, layout.control, layout.point.finite, layout.genericSelect, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY, layout.dialogPool.getD 253 0,
      layout.dialogPool.getD 254 0, layout.dialogPool.getD 255 0],
      q ∉ layout.point.x ∧ q ∉ layout.dialogPool.take 253) ∧
    parkWire layout ∈ layout.dialogPool ∧ parkWire layout ∉ layout.point.y ∧
    layout.dialogPool.getD 253 0 ∈ layout.dialogPool ∧ layout.dialogPool.getD 254 0 ∈ layout.dialogPool ∧
    layout.dialogPool.getD 255 0 ∈ layout.dialogPool := by
  decide +kernel

open Classical in
theorem exc_bit (C : Point) : exceptionBit C = decide (dialogExceptionEnabled C) := by
  simp [exceptionBit, equal_simp, dialogExceptionEnabled, Bool.and_assoc]


/-- Wires the output stage only reads or rewrites, off the point registers in the concrete layout. -/
theorem out_off : ∀ q ∈ [layout.control, layout.infinitySelect, layout.doubleSelect, layout.core.generic,
    layout.core.equalX, layout.core.equalNegY, layout.core.double, parkWire layout],
    q ∉ layout.point.x ∧ q ∉ layout.point.y ∧ q ≠ layout.point.finite ∧ q ≠ layout.genericSelect := by
  decide +kernel

theorem out_pool_off : ∀ q ∈ layout.dialogPool, q ≠ layout.point.finite ∧ q ≠ layout.genericSelect ∧
    q ≠ layout.doubleSelect ∧ q ≠ layout.core.equalNegY ∧ q ≠ layout.control := by
  decide +kernel

theorem flags_list : layout.inPlaceFlags = [layout.infinitySelect, layout.doubleSelect, layout.genericSelect,
    layout.core.generic, layout.core.equalX, layout.core.equalNegY, layout.core.double] := rfl

theorem gsel_off : layout.genericSelect ∉ layout.point.x ∧ layout.genericSelect ∉ layout.point.y ∧
    layout.genericSelect ≠ layout.point.finite := by
  decide +kernel


theorem out_ne : layout.genericSelect ≠ parkWire layout ∧ layout.genericSelect ≠ layout.doubleSelect ∧
    layout.genericSelect ≠ layout.core.equalNegY ∧ parkWire layout ≠ layout.doubleSelect ∧
    parkWire layout ≠ layout.core.equalNegY ∧ layout.doubleSelect ≠ layout.core.equalNegY := by
  decide +kernel

open Classical in
theorem bool_match (S P : Point) (hP : P ≠ 0) :
    (decide (codeX S = pointX P) && (yBit S == yBit P)) = decide (S = P) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact code_match S P hP


open Classical in
theorem finite_dec (S : Point) : pointFinite S = !decide (S = 0) := by
  cases S with
  | zero =>
    have e : (WeierstrassCurve.Affine.Point.zero : Point) = 0 := rfl
    simp [e, pointFinite, coordinates]
  | some h => simp [pointFinite, coordinates]

open Classical in
theorem code_back (S : Point) :
    codeX S ^^^ (if (!decide (S = 0)) = true then 0 else FiniteFlagInterval.sentinel) = pointX S := by
  cases S with
  | zero =>
    have e : (WeierstrassCurve.Affine.Point.zero : Point) = 0 := rfl
    simp [e, codeX, pointFinite, coordinates, pointX]
  | @some x y h =>
    have hne : (WeierstrassCurve.Affine.Point.some h : Point) ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero h
    simp [hne, codeX_finite hne]

open Classical in
/-- The merged output stage takes the post-generic state to the output boundary. -/
theorem outStage_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s0 : State) (hs : PointDialogBoundary layout R b (fun _ => false) s0.basis) (t : State) (m : List Bool)
    (htx : regValue layout.point.x t.basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (hty : regValue layout.point.y t.basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (htf : t.basis layout.point.finite = false)
    (htg : t.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (htr : ∀ q, q ∉ layout.point.x → q ∉ layout.point.y → q ≠ layout.point.finite →
      q ≠ layout.genericSelect → t.basis q = s0.basis q) :
    (run (outStage layout (.some hc)) m t).phase = t.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (outStage layout (.some hc)) m t).basis := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hnC : -C ≠ 0 := neg_ne_zero.mpr hC
  have hCn : C ≠ -C := (doubling_enabled_iff hc).mp (of_decide_eq_true (cy_ne_neg hc))
  have h2C : C + C ≠ 0 := fun e => hCn (eq_neg_of_add_eq_zero_left e)
  have v : (triOf C).Valid := triOf_valid hc
  have pv := Tri.pivots v
  obtain ⟨fx6n, fx6x, fx10n, fx10x, parkP, parkY, p253, p254, p255⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  set xr1 := layout.point.x.getD (triOf C).r1 0 with hxr1
  set xr2 := layout.point.x.getD (triOf C).r2 0 with hxr2
  have x1m : xr1 ∈ layout.point.x := by
    rw [hxr1, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x2m : xr2 ∈ layout.point.x := by
    rw [hxr2, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x12 : xr1 ≠ xr2 := by
    intro e
    rw [hxr1, hxr2, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact pv.2.2.1 ((List.Nodup.getElem_inj_iff hxn).mp e)
  have hnd8 : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY].Nodup := by
    have hperm : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY].Perm
        ([xr1, xr2] ++ [layout.genericSelect, layout.control, yLow layout, parkWire layout,
          layout.doubleSelect, layout.core.equalNegY]) := by
      show (([layout.genericSelect, layout.control] ++ [xr1, xr2]) ++ [yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY]).Perm
        (([xr1, xr2] ++ [layout.genericSelect, layout.control]) ++ [yLow layout, parkWire layout,
          layout.doubleSelect, layout.core.equalNegY])
      exact List.perm_append_comm.append_right _
    apply hperm.nodup_iff.mpr
    rw [List.nodup_append]
    refine ⟨by simp [x12], fx6n, ?_⟩
    intro a ha b hb e
    subst e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact fx6x _ hb x1m
    · exact fx6x _ hb x2m
  -- reads of the post-generic state
  have off (q : Wire) (hq : q ∈ [layout.control, layout.infinitySelect, layout.doubleSelect, layout.core.generic,
      layout.core.equalX, layout.core.equalNegY, layout.core.double, parkWire layout]) :
      t.basis q = s0.basis q := by
    obtain ⟨a, b', c, d⟩ := out_off q hq
    exact htr q a b' c d
  have flag0 (q : Wire) (hq : q ∈ layout.inPlaceFlags) : s0.basis q = false := hs.flags q hq
  have pool0 (q : Wire) (hq : q ∈ layout.dialogPool) : s0.basis q = false :=
    (regValue_zero _ _).mp hs.clean q hq
  have tpool (q : Wire) (hq : q ∈ layout.dialogPool) : t.basis q = false := by
    obtain ⟨a, b', -, -, -⟩ := out_pool_off q hq
    rw [htr q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) a b']
    exact pool0 q hq
  have hb0 : t.basis layout.control = b := by rw [off _ (by simp)]; exact hs.control
  have hz1 : t.basis (parkWire layout) = false ∧ t.basis layout.doubleSelect = false ∧
      t.basis layout.core.equalNegY = false := by
    refine ⟨tpool _ parkP, ?_, ?_⟩
    · rw [off _ (by simp)]; exact flag0 _ (by simp [flags_list])
    · rw [off _ (by simp)]; exact flag0 _ (by simp [flags_list])
  have hx1v : t.basis xr1 = (codeX (if dialogOrdinary b R C then R + C else R)).testBit (triOf C).r1 := by
    rw [← htx, LocalWireModel.reg_bit _ _ _ (by omega)]
  have hx2v : t.basis xr2 = (codeX (if dialogOrdinary b R C then R + C else R)).testBit (triOf C).r2 := by
    rw [← htx, LocalWireModel.reg_bit _ _ _ (by omega)]
  have hy0v : t.basis (yLow layout) = yBit (if dialogOrdinary b R C then R + C else R) := by
    rw [yLow_bit t.basis, hty, pointY_bit0]
  have pfv : predFlags (triOf C) (yBit C) (t.basis layout.genericSelect ^^ t.basis layout.control)
      (t.basis xr1) (t.basis xr2) (t.basis (yLow layout)) =
      (dialogInfinity b R, dialogDouble b R C, dialogException b R C, dialogInversePoint b R C) := by
    rw [htg, hb0, hx1v, hx2v, hy0v]; exact predFlags_dialog hc b R
  unfold outStage
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat, LocalWireModel.run_concat,
    predecL_run (triOf C) (yBit C) _ _ _ _ _ _ _ _ hnd8 t m hz1, pfv]
  -- stage 2: corners
  generalize ht1 : (⟨t.phase, writeBit (writeBit (writeBit (writeBit t.basis layout.genericSelect
    (dialogInversePoint b R C)) (parkWire layout) (dialogInfinity b R)) layout.doubleSelect
    (dialogDouble b R C)) layout.core.equalNegY (dialogException b R C)⟩ : State) = t1
  obtain ⟨gp, gd, gh, pd, ph, dh⟩ := out_ne
  have t1off (q : Wire) (h1 : q ≠ layout.genericSelect) (h2 : q ≠ parkWire layout) (h3 : q ≠ layout.doubleSelect)
      (h4 : q ≠ layout.core.equalNegY) : t1.basis q = t.basis q := by
    rw [← ht1]; simp [writeBit, Function.update, h1, h2, h3, h4]
  have t1g : t1.basis layout.genericSelect = dialogInversePoint b R C := by
    rw [← ht1]; simp [writeBit, Function.update, gp, gd, gh]
  have t1p : t1.basis (parkWire layout) = dialogInfinity b R := by
    rw [← ht1]; simp [writeBit, Function.update, pd, ph]
  have t1d : t1.basis layout.doubleSelect = dialogDouble b R C := by
    rw [← ht1]; simp [writeBit, Function.update, dh]
  have t1h : t1.basis layout.core.equalNegY = dialogException b R C := by
    rw [← ht1]; simp [writeBit, Function.update]
  have t1ph : t1.phase = t.phase := by rw [← ht1]
  have notw (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.genericSelect ∧ q ≠ parkWire layout ∧ q ≠ layout.doubleSelect ∧ q ≠ layout.core.equalNegY := by
    refine ⟨fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq), fun e => pool_not_point _ parkP (e ▸ hq),
      fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq), fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq)⟩
  have t1x : regValue layout.point.x t1.basis = regValue layout.point.x t.basis := by
    apply regValue_congr; intro q hq
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_left _ hq)
    exact t1off q a b' c d
  have t1y : regValue layout.point.y t1.basis = regValue layout.point.y t.basis := by
    apply regValue_congr; intro q hq
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_right _ hq)
    exact t1off q a b' c d
  -- stage 2: corners
  obtain ⟨c1, c2, c3, c4⟩ := ocorners_run layout layout_widths layout_nodup C t1
    (List.drop (measurementCount (predecL (triOf C) (yBit C) layout.genericSelect layout.control xr1 xr2
      (yLow layout) (parkWire layout) layout.doubleSelect layout.core.equalNegY)) m)
  generalize ht2 : run (ocorners layout C) (List.drop (measurementCount (predecL (triOf C) (yBit C)
    layout.genericSelect layout.control xr1 xr2 (yLow layout) (parkWire layout) layout.doubleSelect
    layout.core.equalNegY)) m) t1 = t2 at c1 c2 c3 c4 ⊢
  have cv := corners_value hc b R
  rw [t1x, htx, t1p, t1d, t1g, t1h, cv.1] at c2
  rw [t1y, hty, t1p, t1d, t1g, t1h, cv.2] at c3
  set S := if b then R + C else R with hSdef
  have t2off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) : t2.basis q = t1.basis q := c4 q hx hy
  have offxy (q : Wire) (hq : q ∈ layout.dialogPool) : q ∉ layout.point.x ∧ q ∉ layout.point.y :=
    ⟨fun h => pool_not_point q hq (List.mem_append_left _ h), fun h => pool_not_point q hq (List.mem_append_right _ h)⟩
  have flxy (q : Wire) (hq : q ∈ layout.inPlaceFlags) : q ∉ layout.point.x ∧ q ∉ layout.point.y :=
    ⟨fun h => flags_not_point q hq (List.mem_append_left _ h), fun h => flags_not_point q hq (List.mem_append_right _ h)⟩
  have t2pool (q : Wire) (hq : q ∈ layout.dialogPool) (hp : q ≠ parkWire layout) : t2.basis q = false := by
    obtain ⟨a, b'⟩ := offxy q hq
    obtain ⟨-, g1, d1, h1, -⟩ := out_pool_off q hq
    rw [t2off q a b', t1off q g1 hp d1 h1]; exact tpool q hq
  have t2ctl : t2.basis layout.control = b := by
    obtain ⟨a, b', -, -⟩ := out_off layout.control (by simp)
    rw [t2off _ a b', t1off _ (by decide) (by decide) (by decide) (by decide)]; exact hb0
  have t2f : t2.basis layout.point.finite = false := by
    have hfx := finite_not_flag.2
    rw [t2off _ (fun h => hfx (List.mem_append_left _ h)) (fun h => hfx (List.mem_append_right _ h)),
      t1off _ (by decide) (by decide) (by decide) (by decide)]; exact htf
  have t2y0 : t2.basis (yLow layout) = yBit S := by rw [yLow_bit t2.basis, c3, pointY_bit0]
  have gF := flxy layout.genericSelect (by simp [flags_list])
  have dF := flxy layout.doubleSelect (by simp [flags_list])
  have hF := flxy layout.core.equalNegY (by simp [flags_list])
  have pF := offxy (parkWire layout) parkP
  have t2g : t2.basis layout.genericSelect = dialogInversePoint b R C := by rw [t2off _ gF.1 gF.2, t1g]
  have t2p : t2.basis (parkWire layout) = dialogInfinity b R := by rw [t2off _ pF.1 pF.2, t1p]
  have t2d : t2.basis layout.doubleSelect = dialogDouble b R C := by rw [t2off _ dF.1 dF.2, t1d]
  have t2h : t2.basis layout.core.equalNegY = dialogException b R C := by rw [t2off _ hF.1 hF.2, t1h]
  -- the match bits on the output abscissa
  have oS : oX (triOf C) (triOf C).S layout.point.x t2.basis = decide (S = 0) := by
    rw [oX_eq _ v _ hxl _ _ v.hS (Tri.tgt_S v), c2]
    exact decide_eq_decide.mpr (code_sentinel S)
  have oA : oX (triOf C) (triOf C).A layout.point.x t2.basis = decide (codeX S = pointX C) := by
    rw [oX_eq _ v _ hxl _ _ v.hA (Tri.tgt_A), c2]; rfl
  have oB : oX (triOf C) (triOf C).B layout.point.x t2.basis = decide (codeX S = pointX (C + C)) := by
    rw [oX_eq _ v _ hxl _ _ v.hB (Tri.tgt_B v), c2]
    have e : (triOf C).B = pointX (C + C) := by
      show pointX (dialogExceptionPoint C) = _
      unfold dialogExceptionPoint; exact DHClass.pointX_neg _
    rw [e]
  have fo := dialogFlags_output b R C
  dsimp only at fo
  have hwl' : (layout.dialogPool.take 253).length = 253 := hwl
  have hfl : t2.basis layout.genericSelect = (t2.basis layout.control && oX (triOf C) (triOf C).S layout.point.x t2.basis) ∧
      t2.basis (parkWire layout) = (t2.basis layout.control && oX (triOf C) (triOf C).A layout.point.x t2.basis &&
        (t2.basis (yLow layout) == yBit C)) ∧
      t2.basis layout.doubleSelect = (t2.basis layout.control && oX (triOf C) (triOf C).B layout.point.x t2.basis &&
        (t2.basis (yLow layout) == yBit (C + C))) ∧
      t2.basis layout.core.equalNegY = (exceptionBit C && t2.basis layout.control &&
        oX (triOf C) (triOf C).A layout.point.x t2.basis && (t2.basis (yLow layout) != yBit C)) := by
    rw [t2g, t2p, t2d, t2h, t2ctl, oS, oA, oB, t2y0]
    have bmC := bool_match S C hC
    have bm2 := bool_match S (C + C) h2C
    have bmN := bool_match S (-C) hnC
    have e1 : (yBit S != yBit C) = (yBit S == yBit (-C)) := by
      rw [yBit_neg hc]; cases yBit S <;> cases yBit (.some hc : Point) <;> rfl
    have e2 : pointX C = pointX (-C) := (DHClass.pointX_neg C).symm
    have hdec : decide (C ≠ -C) = true := decide_eq_true hCn
    refine ⟨fo.2.2.1.symm, ?_, ?_, ?_⟩
    · rw [← fo.1, Bool.and_assoc, bmC]
    · rw [← fo.2.1, hdec, Bool.and_true, Bool.and_assoc, bm2]
    · rw [← fo.2.2.2, e1, e2, exc_bit]
      by_cases hen : dialogExceptionEnabled C
      · have h1 : decide (dialogExceptionEnabled C) = true := decide_eq_true hen
        have h2 : decide (dialogExceptionPoint C ≠ 0 ∧ dialogExceptionPoint C ≠ C ∧
            dialogExceptionPoint C ≠ -C) = true := decide_eq_true hen
        rw [h1, h2, Bool.and_true, Bool.true_and, Bool.and_assoc, bmN]
      · have h1 : decide (dialogExceptionEnabled C) = false := decide_eq_false hen
        have h2 : decide (dialogExceptionPoint C ≠ 0 ∧ dialogExceptionPoint C ≠ C ∧
            dialogExceptionPoint C ≠ -C) = false := decide_eq_false hen
        rw [h1, h2]; simp
  rw [oclassifier_run (triOf C) v (yBit C) (yBit (C + C)) (exceptionBit C) layout.point.x
    (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
    (parkWire layout) layout.doubleSelect layout.core.equalNegY (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) hxn hxl hwl' hwn hdisj fx10n fx10x t2 _
    ⟨fun q hq => t2pool q (List.mem_of_mem_take hq) (fun e => (fx10x _ (by simp)).2 (e ▸ hq)), t2f,
      t2pool _ p253 (by decide), t2pool _ p254 (by decide), t2pool _ p255 (by decide)⟩ hfl]
  rw [oS]
  -- stage 4: back to the plain abscissa
  generalize ht3 : (⟨t2.phase, writeBit (writeBit (writeBit (writeBit (writeBit t2.basis layout.point.finite
    (!decide (S = 0))) layout.genericSelect false) (parkWire layout) false) layout.doubleSelect false)
    layout.core.equalNegY false⟩ : State) = t3
  have t3ph : t3.phase = t.phase := by rw [← ht3]; show t2.phase = t.phase; rw [c1, t1ph]
  have t3off (q : Wire) (h0 : q ≠ layout.point.finite) (h1 : q ≠ layout.genericSelect) (h2 : q ≠ parkWire layout)
      (h3 : q ≠ layout.doubleSelect) (h4 : q ≠ layout.core.equalNegY) : t3.basis q = t2.basis q := by
    rw [← ht3]; simp [writeBit, Function.update, h0, h1, h2, h3, h4]
  have fG : layout.point.finite ≠ layout.genericSelect := (gsel_off.2.2).symm
  have fP : layout.point.finite ≠ parkWire layout := fun e => (out_pool_off _ parkP).1 e.symm
  have fD : layout.point.finite ≠ layout.doubleSelect :=
    fun e => finite_not_flag.1 (e ▸ (by simp [flags_list] : layout.doubleSelect ∈ layout.inPlaceFlags))
  have fH : layout.point.finite ≠ layout.core.equalNegY :=
    fun e => finite_not_flag.1 (e ▸ (by simp [flags_list] : layout.core.equalNegY ∈ layout.inPlaceFlags))
  have t3f : t3.basis layout.point.finite = !decide (S = 0) := by
    rw [← ht3]; simp [writeBit, Function.update, fG, fP, fD, fH]
  have t3x : regValue layout.point.x t3.basis = codeX S := by
    rw [← c2]; apply regValue_congr; intro q hq
    have hf : q ≠ layout.point.finite := fun e => finite_not_flag.2 (e ▸ List.mem_append_left _ hq)
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_left _ hq)
    exact t3off q hf a b' c d
  have t3y : regValue layout.point.y t3.basis = pointY S := by
    rw [← c3]; apply regValue_congr; intro q hq
    have hf : q ≠ layout.point.finite := fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_right _ hq)
    exact t3off q hf a b' c d
  suffices key : ∀ mm, (run (FiniteFlagInterval.zrep layout) mm t3).phase = t.phase ∧
      PointDialogBoundary layout S b (fun _ => false) (run (FiniteFlagInterval.zrep layout) mm t3).basis by
    exact key _
  intro mm
  obtain ⟨z1, z2, z3⟩ := FiniteFlagInterval.zrep_run layout layout_widths layout_nodup t3 mm
  generalize run (FiniteFlagInterval.zrep layout) mm t3 = t4 at z1 z2 z3 ⊢
  have fx : layout.point.finite ∉ layout.point.x := fun h => finite_not_flag.2 (List.mem_append_left _ h)
  refine ⟨by rw [z1, t3ph], ?_, ?_, ?_, ?_⟩
  · apply (point_holds _ _ _).mpr
    refine ⟨by rw [z2 _ fx, t3f, finite_dec], by rw [z3, t3x, t3f, code_back], ?_⟩
    rw [← t3y]; apply regValue_congr; intro q hq
    exact z2 q (y_not_x layout layout_nodup q hq)
  · obtain ⟨a, -, c, d⟩ := out_off layout.control (by simp)
    rw [z2 _ a, t3off _ c.symm.symm (by decide) (by decide) (by decide) (by decide)]
    · exact t2ctl
  · intro q hq
    rw [z2 q (flags_not_point q hq ∘ List.mem_append_left _)]
    rw [flags_list] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨a, b', c, d⟩ := out_off layout.infinitySelect (by simp)
      rw [t3off _ c (by decide) (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ (by decide) (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · rw [← ht3]; simp [writeBit, Function.update, dh]
    · rw [← ht3]; simp [writeBit, Function.update, gp, gd, gh]
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.generic (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.equalX (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · rw [← ht3]; simp [writeBit, Function.update]
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.double (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
  · apply (regValue_zero _ _).mpr
    intro q hq
    rw [z2 q (fun h => pool_not_point q hq (List.mem_append_left _ h))]
    by_cases hp : q = parkWire layout
    · subst hp; rw [← ht3]; simp [writeBit, Function.update, pd, ph]
    · obtain ⟨f1, g1, d1, h1, -⟩ := out_pool_off q hq
      rw [t3off q f1 g1 hp d1 h1]
      exact t2pool q hq hp

end OutCompose

end ECDSAAdd.Entrant.InputSentinel

namespace ECDSAAdd.Entrant.InputSentinel
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section OutSplice
open Secp256k1 ControlledPointLayout
attribute [local irreducible] wires

/-- The generic block on its own, before the input relabellings. -/
def genBlock (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ReflectionE1TickGapLow48.generic L cx cy))

/-- Finite program with both merged stages. -/
def finiteProgram2 (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlock L cx cy))) ++
    outStage L C

def wrapper2 (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram2 L C cx cy)

open Classical in
theorem finite2_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgram2 layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgram2 layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgram2
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlock layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlock layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlock layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlock layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlock
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ReflectionE1TickGapLow48.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ReflectionE1TickGapLow48.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run x y x y false
        (fun base' => ReflectionE1TickGapLow48.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper2_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapper2 layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite2_run hc b R s m hs
  unfold wrapper2
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h

/-- Old output parts of the classifier wrapper, in order, and their resource floor. -/
theorem old_out_counts {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    504 ≤ toffoliCount (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (CodexYParityProbe.clrF layout ++ FiniteFlagInterval.zrep layout)))) ++
      FusedFlags.suffixProgram layout (.some hc) ++
      renameProgram (sigP layout) (corners2 layout (.some hc) ++ Edges.sharedM layout (.some hc)) ++
      chainErase layout.control layout.point.finite layout.genericSelect) ∧
    505 ≤ measurementCount (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (CodexYParityProbe.clrF layout ++ FiniteFlagInterval.zrep layout)))) ++
      FusedFlags.suffixProgram layout (.some hc) ++
      renameProgram (sigP layout) (corners2 layout (.some hc) ++ Edges.sharedM layout (.some hc)) ++
      chainErase layout.control layout.point.finite layout.genericSelect) := by
  have c := CodexYParityProbe.counts layout layout_widths
  have z := FiniteFlagInterval.zrep_counts layout
  have sm := Edges.sharedM_counts layout layout_widths hc
  have pr := FusedFlags.counts (DHClass.cxk (.some hc)) (yBit (.some hc))
  have pt := renameProgram_counts (LocalWireModel.label (FusedFlags.ports layout (DHClass.kx (.some hc))))
    (FusedFlags.restoreSuffix (DHClass.cxk (.some hc)) (yBit (.some hc)))
  have ce : measurementCount (chainErase layout.control layout.point.finite layout.genericSelect) = 1 := rfl
  simp only [toffoliCount_append, measurementCount_append, renameProgram_counts, FusedFlags.suffixProgram,
    pt.1, pt.2, c.1, c.2.1, z.1, z.2, sm.1, sm.2, pr.2.1, pr.2.2.2, ce]
  constructor <;> omega

theorem wires_inst {P Q : Program} (h : ∀ i ∈ P, i ∈ Q) : wires P ⊆ wires Q := fun w hw => by
  obtain ⟨i, hi, hq⟩ := (SW.mem_wires_iff _ _).mp hw
  exact (SW.mem_wires_iff _ _).mpr ⟨i, h i hi, hq⟩

/-- Wires of the merged output stage: I/O wires, wires of the merged input stage, or of the fused suffix. -/
theorem outStage_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (outStage layout (.some hc)) ⊆
      (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset ∪
        (wires (stage layout (.some hc)) ∪ wires (FusedFlags.suffixProgram layout (.some hc))) := by
  have sw := stage_wires_mem hc
  have sm := suffix_mem layout (.some hc)
  have hyl := yLow_mem layout layout_widths
  have hxl : layout.point.x.length = 256 := layout_widths.inputX
  have io_x : ∀ q ∈ layout.point.x, q ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
    intro q hq; simp [PointAddLayout.pointWires, hq]
  have io_y : ∀ q ∈ layout.point.y, q ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
    intro q hq; simp [PointAddLayout.pointWires, hq]
  have io_f : layout.point.finite ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
    simp [PointAddLayout.pointWires]
  have io_c : layout.control ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by simp
  have st (q : Wire) (h : q ∈ wires (stage layout (.some hc))) :
      q ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset ∪
        (wires (stage layout (.some hc)) ∪ wires (FusedFlags.suffixProgram layout (.some hc))) :=
    Finset.mem_union_right _ (Finset.mem_union_left _ h)
  have su (q : Wire) (h : q ∈ wires (FusedFlags.suffixProgram layout (.some hc))) :
      q ∈ (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset ∪
        (wires (stage layout (.some hc)) ∪ wires (FusedFlags.suffixProgram layout (.some hc))) :=
    Finset.mem_union_right _ (Finset.mem_union_right _ h)
  have tk (n : Nat) (hn : n ≤ 256) (q : Wire) (hq : q ∈ layout.dialogPool.take n) :
      q ∈ layout.dialogPool.take 256 := by
    have hpl := dialogPool_length layout layout_widths
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    rw [← e]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  intro w hw
  unfold outStage at hw
  simp only [wires_append, Finset.mem_union] at hw
  rcases hw with ((hw | hw) | hw) | hw
  · have h := predecL_support _ _ _ _ _ _ _ _ _ _ hw
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact st _ sw.2
    · exact Finset.mem_union_left _ io_c
    · apply Finset.mem_union_left; apply io_x
      rw [List.getD_eq_getElem _ _ (by have := (Tri.pivots (triOf_valid hc)).1; omega)]
      exact List.getElem_mem _
    · apply Finset.mem_union_left; apply io_x
      rw [List.getD_eq_getElem _ _ (by have := (Tri.pivots (triOf_valid hc)).2.1; omega)]
      exact List.getElem_mem _
    · exact Finset.mem_union_left _ (io_y _ hyl)
    · exact su _ sm.2.2
    · exact su _ sm.1
    · exact su _ sm.2.1
  · have h := ocorners_support layout (.some hc) hw
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (h | h) | h | h | h | h
    · exact Finset.mem_union_left _ (io_x _ h)
    · exact Finset.mem_union_left _ (io_y _ h)
    · subst h; exact su _ sm.2.2
    · subst h; exact su _ sm.1
    · subst h; exact st _ sw.2
    · subst h; exact su _ sm.2.1
  · have h := oclassifier_support _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl
      (by simp [dialogPool_length layout layout_widths]) hw
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with (h | h) | h | h | h | h | h | h | h | h | h | h
    · exact Finset.mem_union_left _ (io_x _ h)
    · exact st _ (sw.1 _ (tk 253 (by decide) _ h))
    · subst h; exact Finset.mem_union_left _ (io_y _ hyl)
    · subst h; exact Finset.mem_union_left _ io_c
    · subst h; exact Finset.mem_union_left _ io_f
    · subst h; exact st _ sw.2
    · subst h; exact su _ sm.2.2
    · subst h; exact su _ sm.1
    · subst h; exact su _ sm.2.1
    · subst h; exact st _ (sw.1 _ (pool_take_mem 253 (by decide)))
    · subst h; exact st _ (sw.1 _ (pool_take_mem 254 (by decide)))
    · subst h; exact st _ (sw.1 _ (pool_take_mem 255 (by decide)))
  · have h : w ∈ (layout.point.finite :: (layout.point.x ++ layout.dialogPool.take 255)).toFinset := by
      rw [← FiniteFlagInterval.old_clrF_support layout layout_widths]
      exact FiniteFlagInterval.zrep_support_old layout layout_widths hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact Finset.mem_union_left _ io_f
    · exact Finset.mem_union_left _ (io_x _ h)
    · exact st _ (sw.1 _ (tk 255 (by decide) _ h))

theorem finite2_sub {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (finiteProgram2 layout (.some hc) cx cy) ⊆
      wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) ∪
        (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
  have hst : wires (stage layout (.some hc)) ⊆
      wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) :=
    wires_inst (fun i hi => by unfold finiteProgram'; exact List.mem_append_left _ hi)
  have hsu : wires (FusedFlags.suffixProgram layout (.some hc)) ⊆
      wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) :=
    wires_inst (fun i hi => by
      unfold finiteProgram' shared
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hi))))
  have hge : wires (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock layout cx cy)))) ⊆
      wires (finiteProgram' layout (.some hc) (renameProgram (Wrapper5.U layout) (tailGen layout cx cy))) :=
    wires_inst (fun i hi => by
      unfold finiteProgram' shared
      apply List.mem_append_right
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      simp only [tailGen, genBlock, FusedFlags.rename_append] at hi ⊢
      exact List.mem_append_left _ (List.mem_append_left _ hi))
  intro w hw
  unfold finiteProgram2 at hw
  simp only [wires_append, Finset.mem_union] at hw
  rcases hw with (hw | hw) | hw
  · exact Finset.mem_union_left _ (hst hw)
  · exact Finset.mem_union_left _ (hge hw)
  · rcases Finset.mem_union.mp (outStage_support hc hw) with h | h
    · exact Finset.mem_union_right _ h
    · rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union_left _ (hst h)
      · exact Finset.mem_union_left _ (hsu h)

theorem wrapper2_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper2 layout (.some hc) cx cy) ⊆
      wires (wrapper' layout (.some hc) (tailGen layout cx cy)) ∪
        (PointAddLayout.pointWires layout.point ++ [layout.control]).toFinset := by
  unfold wrapper2 wrapper'
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (finite2_sub hc hw) with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  · apply Finset.mem_union_right
    rw [Wrapper5.U_outside layout layout_widths w (io_not_pool w (List.mem_toFinset.mp h))]
    exact h

theorem support2_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper2 layout (.some hc) cx cy) ⊆ layout.dialogUsedWires.toFinset := by
  intro q hq
  rcases Finset.mem_union.mp (wrapper2_support hc hq) with o | t
  · exact support_used' hc o
  · have t' := List.mem_toFinset.mp t
    apply List.mem_toFinset.mpr
    unfold ControlledPointLayout.dialogUsedWires
    exact List.mem_append_left _ (List.mem_append_left _ t')

open Classical in
theorem full_spec2 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapper2 layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz : regValue layout.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi : PointDialogBoundary layout R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  have c2 := wrapper2_spec hc b R s m hi
  have a : (run (wrapper' layout (.some hc) (tailGen layout cx cy)) m s).phase = s.phase ∧
      PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
        (run (wrapper' layout (.some hc) (tailGen layout cx cy)) m s).basis := by
    rw [wrapper'_eq hc b R s m hi]
    exact FusedFlags.wrapper_spec layout layout_widths layout_nodup R hc b _
      (CodexYParityProbe.genFFused_ok layout layout_widths layout_nodup hc) s _ hi
  rw [MeasuredDH.boundary_unique layout _ _ (support2_used hc) (support_used' hc) s m _ b c2.2 a.2
    (c2.1.trans a.1.symm)]
  exact full_spec' hc b R s m hs

/-- Old output parts of the classifier wrapper. -/
def oldOut (L : ControlledPointLayout) (C : Point) : Program :=
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L)
    (renameProgram (Wrapper5.U L) (CodexYParityProbe.clrF L ++ FiniteFlagInterval.zrep L)))) ++
  FusedFlags.suffixProgram L C ++
  renameProgram (sigP L) (corners2 L C ++ Edges.sharedM L C) ++
  chainErase L.control L.point.finite L.genericSelect

theorem counts2_rel {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapper2 layout (.some hc) cx cy) + toffoliCount (oldOut layout (.some hc)) =
      toffoliCount (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        toffoliCount (outStage layout (.some hc)) ∧
    measurementCount (wrapper2 layout (.some hc) cx cy) + measurementCount (oldOut layout (.some hc)) =
      measurementCount (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        measurementCount (outStage layout (.some hc)) ∧
    Challenge.gateSlots (wrapper2 layout (.some hc) cx cy) + Challenge.gateSlots (oldOut layout (.some hc)) =
      Challenge.gateSlots (wrapper' layout (.some hc) (tailGen layout cx cy)) +
        Challenge.gateSlots (outStage layout (.some hc)) := by
  unfold wrapper2 wrapper' finiteProgram2 finiteProgram' shared tailGen genBlock oldOut
  simp only [renameProgram_counts, rename_gateSlots, toffoliCount_append, measurementCount_append,
    Challenge.gateSlots_append, CodexYParityProbe.generic]
  omega

theorem nd8 (xr1 xr2 : Wire) (x1m : xr1 ∈ layout.point.x) (x2m : xr2 ∈ layout.point.x) (x12 : xr1 ≠ xr2) :
    [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY].Nodup := by
  obtain ⟨fx6n, fx6x, -, -, -, -, -, -, -⟩ := out_fixed
  have hperm : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY].Perm
      ([xr1, xr2] ++ [layout.genericSelect, layout.control, yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY]) := by
    show (([layout.genericSelect, layout.control] ++ [xr1, xr2]) ++ [yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY]).Perm
      (([xr1, xr2] ++ [layout.genericSelect, layout.control]) ++ [yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY])
    exact List.perm_append_comm.append_right _
  apply hperm.nodup_iff.mpr
  rw [List.nodup_append]
  refine ⟨by simp [x12], fx6n, ?_⟩
  intro a ha b hb e
  subst e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact fx6x _ hb x1m
  · exact fx6x _ hb x2m

theorem outStage_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (outStage layout (.some hc)) := by
  have pv := Tri.pivots (triOf_valid hc)
  obtain ⟨-, -, fx10n, fx10x, -, -, -, -, -⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  have x1m : layout.point.x.getD (triOf (.some hc)).r1 0 ∈ layout.point.x := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x2m : layout.point.x.getD (triOf (.some hc)).r2 0 ∈ layout.point.x := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x12 : layout.point.x.getD (triOf (.some hc)).r1 0 ≠ layout.point.x.getD (triOf (.some hc)).r2 0 := by
    intro e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact pv.2.2.1 ((List.Nodup.getElem_inj_iff hxn).mp e)
  unfold outStage
  simp only [gatePhysical_append]
  exact ⟨⟨⟨predecL_physical _ _ _ _ _ _ _ _ _ _ (nd8 _ _ x1m x2m x12),
    ocorners_physical layout layout_widths layout_nodup _⟩,
    oclassifier_physical _ (triOf_valid hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hxl hwl hxn hwn hdisj fx10n fx10x⟩,
    FiniteFlagInterval.zrep_physical layout layout_nodup⟩

theorem wrapper2_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapper2 layout (.some hc) cx cy) := by
  have old := wrapper'_physical hc
  unfold wrapper' at old
  rw [R2SqEp760.gatePhysical_rename_iff] at old
  unfold wrapper2
  rw [R2SqEp760.gatePhysical_rename_iff]
  intro i hi
  unfold finiteProgram2 at hi
  rcases List.mem_append.mp hi with hi | hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact stage_physical hc i hi
    · apply old i
      unfold finiteProgram' shared
      apply List.mem_append_right
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      simp only [tailGen, genBlock, FusedFlags.rename_append] at hi ⊢
      exact List.mem_append_left _ (List.mem_append_left _ hi)
  · exact outStage_physical hc i hi

end OutSplice


section OutCert
open Secp256k1 Challenge ControlledPointLayout
attribute [local irreducible] wires

def program2 (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => wrapper2 layout C cx cy

def entry2 : Challenge.Entry := fun C => normalizeProgram (program2 C)
def bounds2 : Challenge.Bounds := ⟨2150537, 1498370, 1587, 50248230⟩

theorem program2_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program2 C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program2,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    exact fixed_correct _ control R _ (full_spec2 hc control R) (support2_used hc)

theorem program2_toffoli (C : Point) : toffoliCount (program2 C) ≤ 2150537 := by
  cases C with
  | zero => simp [program2, toffoliCount]
  | @some cx cy hc =>
    have r := (counts2_rel hc).1
    have o : 504 ≤ toffoliCount (oldOut layout (.some hc)) := (old_out_counts hc).1
    have st := (outStage_counts hc).1
    have old := program_toffoli (.some hc)
    change toffoliCount (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 2150781 at old
    change toffoliCount (wrapper2 layout (.some hc) cx cy) ≤ 2150537
    omega

theorem program2_measurements (C : Point) : measurementCount (program2 C) ≤ 1498370 := by
  cases C with
  | zero => simp [program2, measurementCount]
  | @some cx cy hc =>
    have r := (counts2_rel hc).2.1
    have o : 505 ≤ measurementCount (oldOut layout (.some hc)) := (old_out_counts hc).2
    have st := (outStage_counts hc).2.1
    have old := program_measurements (.some hc)
    change measurementCount (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 1498614 at old
    change measurementCount (wrapper2 layout (.some hc) cx cy) ≤ 1498370
    omega

theorem program2_qubits (C : Point) : qubits (program2 C) ≤ 1587 := by
  cases C with
  | zero => change qubits [] ≤ 1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have sub := wrapper2_support hc
    have old := program_qubits (.some hc)
    change qubits (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 1587 at old
    change qubits (wrapper2 layout (.some hc) cx cy) ≤ 1587
    refine le_trans (Finset.card_le_card ?_) old
    intro q hq
    rcases Finset.mem_union.mp hq with io | used
    · exact Finset.mem_union_left _ io
    · rcases Finset.mem_union.mp (sub used) with o | t
      · exact Finset.mem_union_right _ o
      · apply Finset.mem_union_left
        exact io_mem q (List.mem_toFinset.mp t)

theorem program2_physical (C : Point) : GatePhysical (program2 C) := by
  cases C with
  | zero => simp [program2, GatePhysical]
  | @some cx cy hc => exact wrapper2_physical hc

theorem program2_gateSlots (C : Point) : gateSlots (program2 C) ≤ 50248230 := by
  cases C with
  | zero => simp [program2]
  | @some cx cy hc =>
    have r := (counts2_rel hc).2.2
    have st := (outStage_counts hc).2.2
    have old := program_gateSlots (.some hc)
    change gateSlots (wrapper' layout (.some hc) (tailGen layout cx cy)) ≤ 50242569 at old
    change gateSlots (wrapper2 layout (.some hc) cx cy) ≤ 50248230
    omega

theorem certificate2 : Challenge.Certificate entry2 bounds2 where
  correct C control R := (normalize_triple _ _ _).mpr (program2_correct C control R)
  physical C := normalize_physical _ (program2_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program2_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program2 C)) ≤ 1498370
    rw [normalize_measurements]; exact program2_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program2 C)) ≤ 1587
    rw [normalize_qubits]; exact program2_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program2 C)) ≤ 50248230
    rw [normalize_slots]; exact program2_gateSlots C

end OutCert

end ECDSAAdd.Entrant.InputSentinel




namespace ECDSAAdd.Entrant.Entry530
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap OB5 Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  InverseFour15.lastPhase15 InverseFour15.stackReverse15 InverseFour15.reverseTail15 Rolling1588TickGap.tailPhase

def restE530 (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true) ++
      (Rolling1588.entryFieldHosted ++ renameProgram phaseHost (InverseFour15.lastPhase15 false)))

def entryStage530 (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky ++ E1QubitPlacement.entryM L kx ++ restE530 L

theorem entry_split530 (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry InverseFour15.entryKernel15 L = E1QubitPlacement.tickF L ++ restE530 L := by
  have tick := E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base)) = E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,InverseFour15.entryKernel15,InverseFour15.kernel15,
    Rolling1588TickGap.firstPhase,restE530,renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem entryStage_step530 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStage530 L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX L hw hn X Y G origin kx
  have divide := division_step InverseFour15.entryKernel15 InverseFour15.entry_support530
    InverseFour15.entry_correct15 L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior := add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky ++ E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx ++ fusedY L ky ++ E1QubitPlacement.tickF L)
    (R:=restE530 L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryStage530,division,entry_split530,List.append_assoc] using prior

open ReflectionE1TickGapLow48

def generic530 (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage530 L (-cx) (-cy) ++ ReflectionE1TickGapLow48.secondStageX L (ReflectionE1.correction cx) cy cx

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic530 L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStage_step530 L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageX_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic530 L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStage_step530 L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageX_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second



end

end ECDSAAdd.Entrant.Entry530


open ECDSAAdd.Entrant.InverseFour15

set_option Elab.async false

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires Entry530.generic530

theorem gen_block_run530 {cx cy : Fp} (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      (Entry530.generic530 layout cx cy) (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy)))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy)))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy)))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          (Entry530.generic530 layout cx cy)))))) m t).basis q = t.basis q := by
  have hw := layout_widths
  have hn := layout_nodup
  have tinv := tauM_invol layout hn
  have einv := swapE_invol layout hw hn
  have dinv := swapD_invol layout hw hn
  have uinv : ∀ q, Wrapper5.U layout (Wrapper5.U layout q) = q := fun q => Equiv.swap_apply_self _ _ _
  have gflag : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have sflag : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have eflag : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have dflag : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have tauM_def : ∀ q, tauM layout q =
      if q = layout.core.generic then layout.genericSelect else
        if q = layout.genericSelect then layout.core.generic else q := fun q => rfl
  -- tauM fixes everything off the two generic flags
  have tfix : ∀ q, q ≠ layout.core.generic → q ≠ layout.genericSelect → tauM layout q = q := by
    intro q h1 h2; rw [tauM_def q, if_neg h1, if_neg h2]
  have pclean : ∀ q ∈ layout.dialogPool, t.basis q = false :=
    fun q hq => (regValue_zero _ _).mp hclean q hq
  have pne (q : Wire) (hq : q ∈ layout.dialogPool) : q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => pool_not_flag q hq (e ▸ gflag), fun e => pool_not_flag q hq (e ▸ sflag)⟩
  have xyne (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => flags_not_point _ gflag (e ▸ hq), fun e => flags_not_point _ sflag (e ▸ hq)⟩
  have fne : layout.point.finite ≠ layout.core.generic ∧ layout.point.finite ≠ layout.genericSelect :=
    ⟨fun e => finite_not_flag.1 (e ▸ gflag), fun e => finite_not_flag.1 (e ▸ sflag)⟩
  -- the generic block in its own frame
  generalize ht' : pullState (tauM layout) t = t'
  have t'def : ∀ q, t'.basis q = t.basis (tauM layout q) := by intro q; rw [← ht']; rfl
  have t'x : ∀ q ∈ layout.point.x ++ layout.point.y, t'.basis q = t.basis q := by
    intro q hq; rw [t'def, tfix q (xyne q hq).1 (xyne q hq).2]
  have v : PointDialogValues layout X Y G t'.basis t'.basis := by
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [← hx]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_left _ hq)
    · rw [← hy]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_right _ hq)
    · rw [t'def, tauM_def, if_pos rfl]; exact hg
    · apply (regValue_zero _ _).mpr
      intro q hq
      rw [t'def, tfix q (pne q hq).1 (pne q hq).2]; exact pclean q hq
  have hb : t'.basis layout.point.finite = false := by
    rw [t'def, tfix _ fne.1 fne.2]; exact hf
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn (Entry530.generic530 layout cx cy)
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) (Entry530.generic530 layout cx cy)) m t' = R0
    at ph0 v0
  have R0clean : ∀ q ∈ layout.dialogPool, R0.basis q = false :=
    fun q hq => (regValue_zero _ _).mp v0.clean q hq
  -- U swaps two clean pool sites
  have u684 := Square5Placement.pool_member layout hw 684 (by omega)
  have u717 := Square5Placement.pool_member layout hw 717 (by omega)
  have U_def : ∀ q, Wrapper5.U layout q = if q = layout.core.poolWire 684 then layout.core.poolWire 717
      else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
    intro q
    show (Equiv.swap _ _) q = _
    rw [Equiv.swap_apply_def]
  have R1 : run (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      (Entry530.generic530 layout cx cy))) m t' = R0 := by
    rw [run_rename_noop _ uinv]
    · exact hR0
    · apply swap_sym _ _ _ U_def
      have a : t'.basis (layout.core.poolWire 684) = false := by
        rw [t'def, tfix _ (pne _ u684).1 (pne _ u684).2]; exact pclean _ u684
      have b : t'.basis (layout.core.poolWire 717) = false := by
        rw [t'def, tfix _ (pne _ u717).1 (pne _ u717).2]; exact pclean _ u717
      rw [a, b]
    · rw [hR0]
      apply swap_sym _ _ _ U_def
      rw [R0clean _ u684, R0clean _ u717]
  -- tauM is the real swap between the generic flag and the generic select
  have R2 : run (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      (Entry530.generic530 layout cx cy)))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_invol _ tinv, ht', R1]
  -- R0 off the point registers equals the pulled start
  have R0rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → R0.basis q = t'.basis q := v0.rest
  have tq_off : ∀ q, q ∉ layout.point.x ++ layout.point.y → tauM layout q ∉ layout.point.x ++ layout.point.y := by
    intro q hq
    rw [tauM_def]
    split_ifs
    · exact flags_not_point _ sflag
    · exact flags_not_point _ gflag
    · exact hq
  have R2rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → (pullState (tauM layout) R0).basis q = t.basis q := by
    intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, R0rest _ (tq_off q hq), t'def, tinv]
  -- swapE and swapD act on clean wires before and after
  have spE := spare_pool layout hw
  have spD := spareD_pool layout hw
  have E_def : ∀ q, swapE layout q = if q = layout.core.equalNegY then spareWire layout
      else if q = spareWire layout then layout.core.equalNegY else q := fun q => rfl
  have D_def : ∀ q, swapD layout q = if q = layout.doubleSelect then spareD layout
      else if q = spareD layout then layout.doubleSelect else q := fun q => rfl
  have R2E : (pullState (tauM layout) R0).basis layout.core.equalNegY = false := by
    rw [R2rest _ (flags_not_point _ eflag)]; exact hE
  have R2Es : (pullState (tauM layout) R0).basis (spareWire layout) = false := by
    rw [R2rest _ (pool_not_point _ spE)]; exact pclean _ spE
  have R2D : (pullState (tauM layout) R0).basis layout.doubleSelect = false := by
    rw [R2rest _ (flags_not_point _ dflag)]; exact hD
  have R2Ds : (pullState (tauM layout) R0).basis (spareD layout) = false := by
    rw [R2rest _ (pool_not_point _ spD)]; exact pclean _ spD
  have R3 : run (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        (Entry530.generic530 layout cx cy)))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ dinv _ _ _ (swap_sym _ _ _ D_def _ (by rw [hD, pclean _ spD]))
      (by rw [R3]; exact swap_sym _ _ _ D_def _ (by rw [R2D, R2Ds])), R3]
  rw [R4]
  refine ⟨?_, ?_, ?_, R2rest⟩
  · have e1 : (pullState (tauM layout) R0).phase = R0.phase := rfl
    rw [e1, ph0, ← ht']; rfl
  · rw [← v0.x]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_left _ hq)).1 (xyne q (List.mem_append_left _ hq)).2]
  · rw [← v0.y]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_right _ hq)).1 (xyne q (List.mem_append_right _ hq)).2]

end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires Entry530.generic530

def genBlock530 (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (Entry530.generic530 L cx cy))
def finiteProgram530 (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlock530 L cx cy))) ++ InputSentinel.outStage L C
def wrapper530 (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram530 L C cx cy)

open Classical in
theorem finite530_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgram530 layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgram530 layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgram530
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock530 layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlock530 layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlock530 layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlock530 layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlock530 layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlock530 layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlock530
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run530 x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => Entry530.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run530 (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => Entry530.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run530 x y x y false
        (fun base' => Entry530.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper530_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapper530 layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite530_run hc b R s m hs
  unfold wrapper530
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h


end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout InputSentinel
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires

theorem predec_wire530 (tr : Tri) (yc : Bool) (g c x y z O D H : Wire) :
    O ∈ wires (predecL tr yc g c x y z O D H) := by
  have key : (5:Wire) ∈ wires (predecT tr yc) := by
    unfold predecT
    split <;> simp only [predec1,predec2,wires_append,Finset.mem_union] <;>
      simp [wires,Instr.wires]
  unfold predecL
  rw [renameProgram_support]
  apply Finset.mem_image.mpr
  refine ⟨5,key,?_⟩
  simp [LocalWireModel.label]

theorem out_wire530 (C : Point) : parkWire layout ∈ wires (InputSentinel.outStage layout C) := by
  unfold InputSentinel.outStage
  rw [wires_append,wires_append,wires_append]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact predec_wire530 _ _ _ _ _ _ _ _ _ _

theorem wrapper_wire530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    (4629:Wire) ∈ wires (wrapper2 layout (.some hc) cx cy) := by
  unfold wrapper2
  rw [renameProgram_support]
  apply Finset.mem_image.mpr
  refine ⟨parkWire layout,?_,?_⟩
  · unfold finiteProgram2
    rw [wires_append,wires_append]
    exact Finset.mem_union_right _ (out_wire530 (.some hc))
  · decide +kernel

end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.Entry530
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap ReflectionE1TickGapLow48 OB5 Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  InverseFour15.lastPhase15 Rolling1588.lastPhase Rolling1588TickGap.tailPhase

theorem restE_extra530 (L : ControlledPointLayout) :
    wires (restE530 L) ⊆ wires (ReflectionE1TickGap.restE L) ∪ {wireFn2 L 530} := by
  have inner := InverseFour15.hosted_extra530 false
  unfold restE530 ReflectionE1TickGap.restE
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  simp only [wires_append,Finset.mem_union] at hv
  rcases hv with first | field | last
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨v,?_,rfl⟩
    simp only [wires_append,Finset.mem_union]
    exact Or.inl first
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨v,?_,rfl⟩
    simp only [wires_append,Finset.mem_union]
    exact Or.inr (Or.inl field)
  · rcases Finset.mem_union.mp (inner last) with old | extra
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨v,?_,rfl⟩
      simp only [wires_append,Finset.mem_union]
      exact Or.inr (Or.inr old)
    · simp only [Finset.mem_singleton] at extra
      subst v
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

theorem generic_extra530 (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic530 L cx cy) ⊆
      wires (ReflectionE1TickGapLow48.generic L cx cy) ∪ {wireFn2 L 530} := by
  have h := restE_extra530 L
  intro q hq
  simp only [generic530,entryStage530,ReflectionE1TickGapLow48.generic,
    ReflectionE1TickGap.entryStage,wires_append,Finset.mem_union] at hq ⊢
  rcases hq with (((hy | hm) | he) | hs)
  · exact Or.inl (Or.inl (Or.inl (Or.inl hy)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hm)))
  · rcases Finset.mem_union.mp (h he) with old | extra
    · exact Or.inl (Or.inl (Or.inr old))
    · exact Or.inr extra
  · exact Or.inl (Or.inr hs)
end ECDSAAdd.Entrant.Entry530

namespace ECDSAAdd.Entrant.Entry530
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap ReflectionE1TickGapLow48 OB5 Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  Rolling1588.stackReverse Rolling1588.lastPhase InverseFour15.stackReverse15 InverseFour15.reverseTail15 InverseFour15.lastPhase15 candidate15 old15

theorem old_metrics530 : toffoliCount old15 = 16 ∧ measurementCount old15 = 11 ∧ gateSlots old15 = 289 := by decide +kernel

theorem reverse_metrics530 (isA : Bool) :
    toffoliCount (InverseFour15.stackReverse15 isA) + 2 = toffoliCount (Rolling1588.stackReverse isA) ∧
    measurementCount (InverseFour15.stackReverse15 isA) = measurementCount (Rolling1588.stackReverse isA) ∧
    gateSlots (InverseFour15.stackReverse15 isA) = gateSlots (Rolling1588.stackReverse isA) + 1084 := by
  have old := old_metrics530
  have fresh := InverseFour15.resources
  rw [InverseFour15.reverse_shape15]
  simp only [InverseFour15.stackReverse15,InverseFour15.reverseTail15,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots] at *
  omega

theorem last_metrics530 (isA : Bool) :
    toffoliCount (InverseFour15.lastPhase15 isA) + 2 = toffoliCount (Rolling1588.lastPhase isA) ∧
    measurementCount (InverseFour15.lastPhase15 isA) = measurementCount (Rolling1588.lastPhase isA) ∧
    gateSlots (InverseFour15.lastPhase15 isA) = gateSlots (Rolling1588.lastPhase isA) + 1084 := by
  have h := reverse_metrics530 isA
  simp only [InverseFour15.lastPhase15,Rolling1588.lastPhase,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem restE_metrics530 (L : ControlledPointLayout) :
    toffoliCount (restE530 L) + 2 = toffoliCount (ReflectionE1TickGap.restE L) ∧
    measurementCount (restE530 L) = measurementCount (ReflectionE1TickGap.restE L) ∧
    gateSlots (restE530 L) = gateSlots (ReflectionE1TickGap.restE L) + 1084 := by
  have h := last_metrics530 false
  simp only [restE530,ReflectionE1TickGap.restE,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega

theorem generic_metrics530 (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (generic530 L cx cy) + 2 = toffoliCount (ReflectionE1TickGapLow48.generic L cx cy) ∧
    measurementCount (generic530 L cx cy) = measurementCount (ReflectionE1TickGapLow48.generic L cx cy) ∧
    gateSlots (generic530 L cx cy) = gateSlots (ReflectionE1TickGapLow48.generic L cx cy) + 1084 := by
  have h := restE_metrics530 L
  simp only [generic530,entryStage530,ReflectionE1TickGapLow48.generic,
    ReflectionE1TickGap.entryStage,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega
end ECDSAAdd.Entrant.Entry530

namespace ECDSAAdd.Entrant.Entry530
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap ReflectionE1TickGapLow48 OB5 Rolling1588Lifetime
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  InverseFour15.lastPhase15 Rolling1588.lastPhase Rolling1588TickGap.tailPhase

theorem restE_physical530 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restE530 L) := by
  have p := placed_physical InverseFour15.entryKernel15 InverseFour15.entry_support530 InverseFour15.entry_physical15 L hw hn
  have entryP : GatePhysical (FrontierEntry1591Callers.entry InverseFour15.entryKernel15 L) := by
    simpa only [FrontierEntry1591Callers.entry] using p
  rw [entry_split530,gatePhysical_append] at entryP
  exact entryP.2

theorem generic_physical530 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic530 L cx cy) := by
  have old := ReflectionE1TickGapLow48.generic_physical L hw hn cx cy
  simp only [ReflectionE1TickGapLow48.generic,ReflectionE1TickGap.entryStage,gatePhysical_append] at old
  simp only [generic530,entryStage530,gatePhysical_append]
  exact ⟨⟨⟨old.1.1.1,old.1.1.2⟩,restE_physical530 L hw hn⟩,old.2⟩
end ECDSAAdd.Entrant.Entry530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Entry530.generic530 ReflectionE1TickGapLow48.generic

private theorem mapped_extra530 (f : Wire → Wire) (P Q : Program) (e : Wire)
    (h : wires P ⊆ wires Q ∪ {e}) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) ∪ {f e} := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (h hv) with old | extra
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ old)
  · simp only [Finset.mem_singleton] at extra
    subst v
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

private theorem context_extra530 (A P Q B : Program) (e : Wire)
    (h : wires P ⊆ wires Q ∪ {e}) :
    wires (A ++ P ++ B) ⊆ wires (A ++ Q ++ B) ∪ {e} := by
  intro q hq
  simp only [wires_append,Finset.mem_union] at hq ⊢
  rcases hq with (ha | hp) | hb
  · exact Or.inl (Or.inl (Or.inl ha))
  · rcases Finset.mem_union.mp (h hp) with ho | he
    · exact Or.inl (Or.inl (Or.inr ho))
    · exact Or.inr he
  · exact Or.inl (Or.inr hb)

theorem wrapper_extra530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper530 layout (.some hc) cx cy) ⊆
      wires (wrapper2 layout (.some hc) cx cy) ∪ {4629} := by
  have h0 := Entry530.generic_extra530 layout cx cy
  have h1 := mapped_extra530 (swapF layout) _ _ _ h0
  have h2 := mapped_extra530 (Wrapper5.U layout) _ _ _ h1
  have h3 := mapped_extra530 (tauM layout) _ _ _ h2
  have h4 := mapped_extra530 (swapE layout) _ _ _ h3
  have h5 := mapped_extra530 (swapD layout) _ _ _ h4
  have h6 := context_extra530 (InputSentinel.stage layout (.some hc)) _ _
    (InputSentinel.outStage layout (.some hc)) _ h5
  have h7 := mapped_extra530 (Wrapper5.U layout) _ _ _ h6
  have e : Wrapper5.U layout (swapD layout (swapE layout (tauM layout
      (Wrapper5.U layout (swapF layout (wireFn2 layout 530)))))) = 4629 := by decide +kernel
  simpa only [wrapper530,finiteProgram530,genBlock530,wrapper2,finiteProgram2,genBlock,e] using h7

theorem wrapper_support530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper530 layout (.some hc) cx cy) ⊆ wires (wrapper2 layout (.some hc) cx cy) := by
  intro q hq
  rcases Finset.mem_union.mp (wrapper_extra530 hc hq) with old | extra
  · exact old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact wrapper_wire530 hc

theorem support_used530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapper530 layout (.some hc) cx cy) ⊆ layout.dialogUsedWires.toFinset :=
  (wrapper_support530 hc).trans (InputSentinel.support2_used hc)
end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Entry530 Challenge
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  Entry530.generic530 ReflectionE1TickGapLow48.generic

theorem wrapper_metrics530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapper530 layout (.some hc) cx cy) + 2 = toffoliCount (wrapper2 layout (.some hc) cx cy) ∧
    measurementCount (wrapper530 layout (.some hc) cx cy) = measurementCount (wrapper2 layout (.some hc) cx cy) ∧
    gateSlots (wrapper530 layout (.some hc) cx cy) = gateSlots (wrapper2 layout (.some hc) cx cy) + 1084 := by
  have h := Entry530.generic_metrics530 layout cx cy
  simp only [wrapper530,finiteProgram530,genBlock530,wrapper2,finiteProgram2,genBlock,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega
end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Entry530 Challenge
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  Entry530.generic530 ReflectionE1TickGapLow48.generic

theorem wrapper_physical530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapper530 layout (.some hc) cx cy) := by
  have p0 := Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapper530
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgram530,genBlock530,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,InputSentinel.outStage_physical hc⟩
end ECDSAAdd.Entrant.InputSentinel530

namespace ECDSAAdd.Entrant.InputSentinel530
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Entry530 Challenge
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  Entry530.generic530 ReflectionE1TickGapLow48.generic

open Classical in
theorem full_spec530 {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapper530 layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz : regValue layout.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi : PointDialogBoundary layout R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  have c2 := wrapper530_spec hc b R s m hi
  have a : (run (wrapper' layout (.some hc) (tailGen layout cx cy)) m s).phase = s.phase ∧
      PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
        (run (wrapper' layout (.some hc) (tailGen layout cx cy)) m s).basis := by
    rw [wrapper'_eq hc b R s m hi]
    exact FusedFlags.wrapper_spec layout layout_widths layout_nodup R hc b _
      (CodexYParityProbe.genFFused_ok layout layout_widths layout_nodup hc) s _ hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used530 hc) (support_used' hc) s m _ b c2.2 a.2
    (c2.1.trans a.1.symm)]
  exact full_spec' hc b R s m hs


def program530 (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => wrapper530 layout C cx cy

def entry530 : Challenge.Entry := fun C => normalizeProgram (program530 C)
def bounds530 : Challenge.Bounds := ⟨2150535,1498370,1587,50249314⟩

theorem program_correct530 (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program530 C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program530,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    exact fixed_correct _ control R _ (full_spec530 hc control R) (support_used530 hc)

theorem program_toffoli530 (C : Point) : toffoliCount (program530 C) ≤ 2150535 := by
  cases C with
  | zero => simp [program530, toffoliCount]
  | @some cx cy hc =>
    have old := InputSentinel.program2_toffoli (.some hc)
    have delta := (wrapper_metrics530 hc).1
    change toffoliCount (wrapper2 layout (.some hc) cx cy) ≤ 2150537 at old
    change toffoliCount (wrapper530 layout (.some hc) cx cy) ≤ 2150535
    omega

theorem program_measurements530 (C : Point) : measurementCount (program530 C) ≤ 1498370 := by
  cases C with
  | zero => simp [program530, measurementCount]
  | @some cx cy hc =>
    have old := InputSentinel.program2_measurements (.some hc)
    have delta := (wrapper_metrics530 hc).2.1
    change measurementCount (wrapper2 layout (.some hc) cx cy) ≤ 1498370 at old
    change measurementCount (wrapper530 layout (.some hc) cx cy) ≤ 1498370
    omega

theorem program_qubits530 (C : Point) : qubits (program530 C) ≤ 1587 := by
  cases C with
  | zero => change qubits [] ≤ 1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have old := InputSentinel.program2_qubits (.some hc)
    have sub := wrapper_support530 hc
    change qubits (wrapper2 layout (.some hc) cx cy) ≤ 1587 at old
    change qubits (wrapper530 layout (.some hc) cx cy) ≤ 1587
    refine le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) sub

theorem program_physical530 (C : Point) : GatePhysical (program530 C) := by
  cases C with
  | zero => simp [program530,GatePhysical]
  | @some cx cy hc => exact wrapper_physical530 hc

theorem program_slots530 (C : Point) : gateSlots (program530 C) ≤ 50249314 := by
  cases C with
  | zero => simp [program530]
  | @some cx cy hc =>
    have old := InputSentinel.program2_gateSlots (.some hc)
    have delta := (wrapper_metrics530 hc).2.2
    change gateSlots (wrapper2 layout (.some hc) cx cy) ≤ 50248230 at old
    change gateSlots (wrapper530 layout (.some hc) cx cy) ≤ 50249314
    omega

theorem certificate530 : Challenge.Certificate entry530 bounds530 where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct530 C control R)
  physical C := normalize_physical _ (program_physical530 C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli530 C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program530 C)) ≤ 1498370
    rw [normalize_measurements]; exact program_measurements530 C
  qubits_le C := by
    change qubits (normalizeProgram (program530 C)) ≤ 1587
    rw [normalize_qubits]; exact program_qubits530 C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program530 C)) ≤ 50249314
    rw [normalize_slots]; exact program_slots530 C
end ECDSAAdd.Entrant.InputSentinel530



namespace ECDSAAdd.Entrant.ParityFinal
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  ParityStage.genericOpt Entry530.generic530

theorem reference_eq (L : ControlledPointLayout) (cx cy : Fp) :
    ParityStage.genericRef L cx cy=Entry530.generic530 L cx cy := by
  simp only [ParityStage.genericRef,Entry530.generic530,ParityStage.entryRef,Entry530.entryStage530,
    ParityStage.restEntry,Entry530.restE530]

theorem gen_block_run (P : Program) (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      P (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          P))))) m t).basis q = t.basis q := by
  have hw := layout_widths
  have hn := layout_nodup
  have tinv := tauM_invol layout hn
  have einv := swapE_invol layout hw hn
  have dinv := swapD_invol layout hw hn
  have uinv : ∀ q, Wrapper5.U layout (Wrapper5.U layout q) = q := fun q => Equiv.swap_apply_self _ _ _
  have gflag : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have sflag : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have eflag : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have dflag : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have tauM_def : ∀ q, tauM layout q =
      if q = layout.core.generic then layout.genericSelect else
        if q = layout.genericSelect then layout.core.generic else q := fun q => rfl
  -- tauM fixes everything off the two generic flags
  have tfix : ∀ q, q ≠ layout.core.generic → q ≠ layout.genericSelect → tauM layout q = q := by
    intro q h1 h2; rw [tauM_def q, if_neg h1, if_neg h2]
  have pclean : ∀ q ∈ layout.dialogPool, t.basis q = false :=
    fun q hq => (regValue_zero _ _).mp hclean q hq
  have pne (q : Wire) (hq : q ∈ layout.dialogPool) : q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => pool_not_flag q hq (e ▸ gflag), fun e => pool_not_flag q hq (e ▸ sflag)⟩
  have xyne (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => flags_not_point _ gflag (e ▸ hq), fun e => flags_not_point _ sflag (e ▸ hq)⟩
  have fne : layout.point.finite ≠ layout.core.generic ∧ layout.point.finite ≠ layout.genericSelect :=
    ⟨fun e => finite_not_flag.1 (e ▸ gflag), fun e => finite_not_flag.1 (e ▸ sflag)⟩
  -- the generic block in its own frame
  generalize ht' : pullState (tauM layout) t = t'
  have t'def : ∀ q, t'.basis q = t.basis (tauM layout q) := by intro q; rw [← ht']; rfl
  have t'x : ∀ q ∈ layout.point.x ++ layout.point.y, t'.basis q = t.basis q := by
    intro q hq; rw [t'def, tfix q (xyne q hq).1 (xyne q hq).2]
  have v : PointDialogValues layout X Y G t'.basis t'.basis := by
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [← hx]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_left _ hq)
    · rw [← hy]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_right _ hq)
    · rw [t'def, tauM_def, if_pos rfl]; exact hg
    · apply (regValue_zero _ _).mpr
      intro q hq
      rw [t'def, tfix q (pne q hq).1 (pne q hq).2]; exact pclean q hq
  have hb : t'.basis layout.point.finite = false := by
    rw [t'def, tfix _ fne.1 fne.2]; exact hf
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn P
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) P) m t' = R0
    at ph0 v0
  have R0clean : ∀ q ∈ layout.dialogPool, R0.basis q = false :=
    fun q hq => (regValue_zero _ _).mp v0.clean q hq
  -- U swaps two clean pool sites
  have u684 := Square5Placement.pool_member layout hw 684 (by omega)
  have u717 := Square5Placement.pool_member layout hw 717 (by omega)
  have U_def : ∀ q, Wrapper5.U layout q = if q = layout.core.poolWire 684 then layout.core.poolWire 717
      else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
    intro q
    show (Equiv.swap _ _) q = _
    rw [Equiv.swap_apply_def]
  have R1 : run (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P)) m t' = R0 := by
    rw [run_rename_noop _ uinv]
    · exact hR0
    · apply swap_sym _ _ _ U_def
      have a : t'.basis (layout.core.poolWire 684) = false := by
        rw [t'def, tfix _ (pne _ u684).1 (pne _ u684).2]; exact pclean _ u684
      have b : t'.basis (layout.core.poolWire 717) = false := by
        rw [t'def, tfix _ (pne _ u717).1 (pne _ u717).2]; exact pclean _ u717
      rw [a, b]
    · rw [hR0]
      apply swap_sym _ _ _ U_def
      rw [R0clean _ u684, R0clean _ u717]
  -- tauM is the real swap between the generic flag and the generic select
  have R2 : run (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_invol _ tinv, ht', R1]
  -- R0 off the point registers equals the pulled start
  have R0rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → R0.basis q = t'.basis q := v0.rest
  have tq_off : ∀ q, q ∉ layout.point.x ++ layout.point.y → tauM layout q ∉ layout.point.x ++ layout.point.y := by
    intro q hq
    rw [tauM_def]
    split_ifs
    · exact flags_not_point _ sflag
    · exact flags_not_point _ gflag
    · exact hq
  have R2rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → (pullState (tauM layout) R0).basis q = t.basis q := by
    intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, R0rest _ (tq_off q hq), t'def, tinv]
  -- swapE and swapD act on clean wires before and after
  have spE := spare_pool layout hw
  have spD := spareD_pool layout hw
  have E_def : ∀ q, swapE layout q = if q = layout.core.equalNegY then spareWire layout
      else if q = spareWire layout then layout.core.equalNegY else q := fun q => rfl
  have D_def : ∀ q, swapD layout q = if q = layout.doubleSelect then spareD layout
      else if q = spareD layout then layout.doubleSelect else q := fun q => rfl
  have R2E : (pullState (tauM layout) R0).basis layout.core.equalNegY = false := by
    rw [R2rest _ (flags_not_point _ eflag)]; exact hE
  have R2Es : (pullState (tauM layout) R0).basis (spareWire layout) = false := by
    rw [R2rest _ (pool_not_point _ spE)]; exact pclean _ spE
  have R2D : (pullState (tauM layout) R0).basis layout.doubleSelect = false := by
    rw [R2rest _ (flags_not_point _ dflag)]; exact hD
  have R2Ds : (pullState (tauM layout) R0).basis (spareD layout) = false := by
    rw [R2rest _ (pool_not_point _ spD)]; exact pclean _ spD
  have R3 : run (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P)))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ dinv _ _ _ (swap_sym _ _ _ D_def _ (by rw [hD, pclean _ spD]))
      (by rw [R3]; exact swap_sym _ _ _ D_def _ (by rw [R2D, R2Ds])), R3]
  rw [R4]
  refine ⟨?_, ?_, ?_, R2rest⟩
  · have e1 : (pullState (tauM layout) R0).phase = R0.phase := rfl
    rw [e1, ph0, ← ht']; rfl
  · rw [← v0.x]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_left _ hq)).1 (xyne q (List.mem_append_left _ hq)).2]
  · rw [← v0.y]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_right _ hq)).1 (xyne q (List.mem_append_right _ hq)).2]

def genBlockOpt (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ParityStage.genericOpt L cx cy))
def finiteProgramOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlockOpt L cx cy))) ++ InputSentinel.outStage L C
def wrapperOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgramOpt L C cx cy)

open Classical in
theorem finite_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgramOpt layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgramOpt layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgramOpt
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlockOpt layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlockOpt
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run (ParityStage.genericOpt layout cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ParityStage.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (ParityStage.genericOpt layout cx cy) (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ParityStage.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run (ParityStage.genericOpt layout cx cy) x y x y false
        (fun base' => ParityStage.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperOpt layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run hc b R s m hs
  unfold wrapperOpt
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h



theorem rename_wires_sub (f : Wire → Wire) (P Q : Program) (h : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  simp only [renameProgram_support]
  exact Finset.image_subset_image h

theorem wrapper_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆wires (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have h:=ParityStage.generic_wires layout layout_widths cx cy
  rw [reference_eq] at h
  have b:=rename_wires_sub (Wrapper5.U layout) _ _ (rename_wires_sub (swapF layout) _ _ h)
  have m:=rename_wires_sub (swapD layout) _ _ (rename_wires_sub (swapE layout) _ _
    (rename_wires_sub (tauM layout) _ _ b))
  unfold wrapperOpt InputSentinel530.wrapper530
  apply rename_wires_sub
  simp only [finiteProgramOpt,InputSentinel530.finiteProgram530,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) m) (Finset.Subset.refl _)

theorem support_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆layout.dialogUsedWires.toFinset :=
  (wrapper_support hc).trans (InputSentinel530.support_used530 hc)

theorem wrapper_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperOpt layout (.some hc) cx cy)+1=
      toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    measurementCount (wrapperOpt layout (.some hc) cx cy)=
      measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    gateSlots (wrapperOpt layout (.some hc) cx cy)≤
      gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have t:=ParityStage.generic_toffoli layout layout_widths cx cy (curve_y_ne_zero hc)
  have h:=ParityStage.generic_counts layout layout_widths cx cy
  rw [reference_eq] at t h
  simp only [wrapperOpt,finiteProgramOpt,genBlockOpt,InputSentinel530.wrapper530,
    InputSentinel530.finiteProgram530,InputSentinel530.genBlock530,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega
theorem wrapper_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperOpt layout (.some hc) cx cy) := by
  have old:GatePhysical (ParityStage.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0:=ParityStage.generic_physical layout layout_widths layout_nodup cx cy old
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapperOpt
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgramOpt,genBlockOpt,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,InputSentinel.outStage_physical hc⟩

open Classical in
theorem full_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperOpt layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programOpt (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperOpt layout C cx cy

def entryOpt : Challenge.Entry := fun C=>normalizeProgram (programOpt C)
def boundsOpt : Challenge.Bounds := ⟨2150534,1498370,1587,50249314⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150534 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150535 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150534
    omega

theorem program_measurements (C : Point) : measurementCount (programOpt C)≤1498370 := by
  cases C with
  | zero=>simp [programOpt,measurementCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_measurements530 (.some hc)
    have delta:=(wrapper_metrics hc).2.1
    change measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370
    omega

theorem program_qubits (C : Point) : qubits (programOpt C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=InputSentinel530.program_qubits530 (.some hc)
    change qubits (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) (wrapper_support hc)

theorem program_physical (C : Point) : GatePhysical (programOpt C) := by
  cases C with
  | zero=>simp [programOpt,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical hc

theorem program_slots (C : Point) : gateSlots (programOpt C)≤50249314 := by
  cases C with
  | zero=>simp [programOpt]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_slots530 (.some hc)
    have delta:=(wrapper_metrics hc).2.2
    change gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤50249314 at old
    change gateSlots (wrapperOpt layout (.some hc) cx cy)≤50249314
    omega

theorem certificateOpt : Challenge.Certificate entryOpt boundsOpt where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programOpt C))≤1498370
    rw [normalize_measurements];exact program_measurements C
  qubits_le C:=by
    change qubits (normalizeProgram (programOpt C))≤1587
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C:=by
    change gateSlots (normalizeProgram (programOpt C))≤50249314
    rw [normalize_slots];exact program_slots C

end ECDSAAdd.Entrant.ParityFinal


namespace ECDSAAdd.Entrant.ParityFinalUniform
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  ParityStageUniform.genericAll Entry530.generic530

theorem reference_eq (L : ControlledPointLayout) (cx cy : Fp) :
    ParityStageUniform.genericRef L cx cy=Entry530.generic530 L cx cy := by
  simp only [ParityStageUniform.genericRef,Entry530.generic530,ParityStageUniform.entryRef,Entry530.entryStage530,
    ParityStageUniform.restEntry,Entry530.restE530]

theorem gen_block_run (P : Program) (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      P (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          P))))) m t).basis q = t.basis q := by
  have hw := layout_widths
  have hn := layout_nodup
  have tinv := tauM_invol layout hn
  have einv := swapE_invol layout hw hn
  have dinv := swapD_invol layout hw hn
  have uinv : ∀ q, Wrapper5.U layout (Wrapper5.U layout q) = q := fun q => Equiv.swap_apply_self _ _ _
  have gflag : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have sflag : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have eflag : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have dflag : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have tauM_def : ∀ q, tauM layout q =
      if q = layout.core.generic then layout.genericSelect else
        if q = layout.genericSelect then layout.core.generic else q := fun q => rfl
  -- tauM fixes everything off the two generic flags
  have tfix : ∀ q, q ≠ layout.core.generic → q ≠ layout.genericSelect → tauM layout q = q := by
    intro q h1 h2; rw [tauM_def q, if_neg h1, if_neg h2]
  have pclean : ∀ q ∈ layout.dialogPool, t.basis q = false :=
    fun q hq => (regValue_zero _ _).mp hclean q hq
  have pne (q : Wire) (hq : q ∈ layout.dialogPool) : q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => pool_not_flag q hq (e ▸ gflag), fun e => pool_not_flag q hq (e ▸ sflag)⟩
  have xyne (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => flags_not_point _ gflag (e ▸ hq), fun e => flags_not_point _ sflag (e ▸ hq)⟩
  have fne : layout.point.finite ≠ layout.core.generic ∧ layout.point.finite ≠ layout.genericSelect :=
    ⟨fun e => finite_not_flag.1 (e ▸ gflag), fun e => finite_not_flag.1 (e ▸ sflag)⟩
  -- the generic block in its own frame
  generalize ht' : pullState (tauM layout) t = t'
  have t'def : ∀ q, t'.basis q = t.basis (tauM layout q) := by intro q; rw [← ht']; rfl
  have t'x : ∀ q ∈ layout.point.x ++ layout.point.y, t'.basis q = t.basis q := by
    intro q hq; rw [t'def, tfix q (xyne q hq).1 (xyne q hq).2]
  have v : PointDialogValues layout X Y G t'.basis t'.basis := by
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [← hx]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_left _ hq)
    · rw [← hy]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_right _ hq)
    · rw [t'def, tauM_def, if_pos rfl]; exact hg
    · apply (regValue_zero _ _).mpr
      intro q hq
      rw [t'def, tfix q (pne q hq).1 (pne q hq).2]; exact pclean q hq
  have hb : t'.basis layout.point.finite = false := by
    rw [t'def, tfix _ fne.1 fne.2]; exact hf
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn P
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) P) m t' = R0
    at ph0 v0
  have R0clean : ∀ q ∈ layout.dialogPool, R0.basis q = false :=
    fun q hq => (regValue_zero _ _).mp v0.clean q hq
  -- U swaps two clean pool sites
  have u684 := Square5Placement.pool_member layout hw 684 (by omega)
  have u717 := Square5Placement.pool_member layout hw 717 (by omega)
  have U_def : ∀ q, Wrapper5.U layout q = if q = layout.core.poolWire 684 then layout.core.poolWire 717
      else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
    intro q
    show (Equiv.swap _ _) q = _
    rw [Equiv.swap_apply_def]
  have R1 : run (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P)) m t' = R0 := by
    rw [run_rename_noop _ uinv]
    · exact hR0
    · apply swap_sym _ _ _ U_def
      have a : t'.basis (layout.core.poolWire 684) = false := by
        rw [t'def, tfix _ (pne _ u684).1 (pne _ u684).2]; exact pclean _ u684
      have b : t'.basis (layout.core.poolWire 717) = false := by
        rw [t'def, tfix _ (pne _ u717).1 (pne _ u717).2]; exact pclean _ u717
      rw [a, b]
    · rw [hR0]
      apply swap_sym _ _ _ U_def
      rw [R0clean _ u684, R0clean _ u717]
  -- tauM is the real swap between the generic flag and the generic select
  have R2 : run (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_invol _ tinv, ht', R1]
  -- R0 off the point registers equals the pulled start
  have R0rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → R0.basis q = t'.basis q := v0.rest
  have tq_off : ∀ q, q ∉ layout.point.x ++ layout.point.y → tauM layout q ∉ layout.point.x ++ layout.point.y := by
    intro q hq
    rw [tauM_def]
    split_ifs
    · exact flags_not_point _ sflag
    · exact flags_not_point _ gflag
    · exact hq
  have R2rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → (pullState (tauM layout) R0).basis q = t.basis q := by
    intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, R0rest _ (tq_off q hq), t'def, tinv]
  -- swapE and swapD act on clean wires before and after
  have spE := spare_pool layout hw
  have spD := spareD_pool layout hw
  have E_def : ∀ q, swapE layout q = if q = layout.core.equalNegY then spareWire layout
      else if q = spareWire layout then layout.core.equalNegY else q := fun q => rfl
  have D_def : ∀ q, swapD layout q = if q = layout.doubleSelect then spareD layout
      else if q = spareD layout then layout.doubleSelect else q := fun q => rfl
  have R2E : (pullState (tauM layout) R0).basis layout.core.equalNegY = false := by
    rw [R2rest _ (flags_not_point _ eflag)]; exact hE
  have R2Es : (pullState (tauM layout) R0).basis (spareWire layout) = false := by
    rw [R2rest _ (pool_not_point _ spE)]; exact pclean _ spE
  have R2D : (pullState (tauM layout) R0).basis layout.doubleSelect = false := by
    rw [R2rest _ (flags_not_point _ dflag)]; exact hD
  have R2Ds : (pullState (tauM layout) R0).basis (spareD layout) = false := by
    rw [R2rest _ (pool_not_point _ spD)]; exact pclean _ spD
  have R3 : run (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P)))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ dinv _ _ _ (swap_sym _ _ _ D_def _ (by rw [hD, pclean _ spD]))
      (by rw [R3]; exact swap_sym _ _ _ D_def _ (by rw [R2D, R2Ds])), R3]
  rw [R4]
  refine ⟨?_, ?_, ?_, R2rest⟩
  · have e1 : (pullState (tauM layout) R0).phase = R0.phase := rfl
    rw [e1, ph0, ← ht']; rfl
  · rw [← v0.x]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_left _ hq)).1 (xyne q (List.mem_append_left _ hq)).2]
  · rw [← v0.y]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_right _ hq)).1 (xyne q (List.mem_append_right _ hq)).2]

def genBlockOpt (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ParityStageUniform.genericAll L cx cy))
def finiteProgramOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlockOpt L cx cy))) ++ InputSentinel.outStage L C
def wrapperOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgramOpt L C cx cy)

open Classical in
theorem finite_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgramOpt layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgramOpt layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgramOpt
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlockOpt layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlockOpt
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run (ParityStageUniform.genericAll layout cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ParityStageUniform.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (ParityStageUniform.genericAll layout cx cy) (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ParityStageUniform.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run (ParityStageUniform.genericAll layout cx cy) x y x y false
        (fun base' => ParityStageUniform.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperOpt layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run hc b R s m hs
  unfold wrapperOpt
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h



theorem rename_wires_sub (f : Wire → Wire) (P Q : Program) (h : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  simp only [renameProgram_support]
  exact Finset.image_subset_image h

theorem wrapper_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆wires (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have h:=ParityStageUniform.generic_wires layout layout_widths cx cy
  rw [reference_eq] at h
  have b:=rename_wires_sub (Wrapper5.U layout) _ _ (rename_wires_sub (swapF layout) _ _ h)
  have m:=rename_wires_sub (swapD layout) _ _ (rename_wires_sub (swapE layout) _ _
    (rename_wires_sub (tauM layout) _ _ b))
  unfold wrapperOpt InputSentinel530.wrapper530
  apply rename_wires_sub
  simp only [finiteProgramOpt,InputSentinel530.finiteProgram530,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) m) (Finset.Subset.refl _)

theorem support_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆layout.dialogUsedWires.toFinset :=
  (wrapper_support hc).trans (InputSentinel530.support_used530 hc)

theorem wrapper_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperOpt layout (.some hc) cx cy)+2=
      toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    measurementCount (wrapperOpt layout (.some hc) cx cy)=
      measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    gateSlots (wrapperOpt layout (.some hc) cx cy)≤
      gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have t:=ParityStageUniform.generic_toffoli layout layout_widths cx cy
  have h:=ParityStageUniform.generic_counts layout layout_widths cx cy
  rw [reference_eq] at t h
  simp only [wrapperOpt,finiteProgramOpt,genBlockOpt,InputSentinel530.wrapper530,
    InputSentinel530.finiteProgram530,InputSentinel530.genBlock530,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega
theorem wrapper_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperOpt layout (.some hc) cx cy) := by
  have old:GatePhysical (ParityStageUniform.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0:=ParityStageUniform.generic_physical layout layout_widths layout_nodup cx cy old
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapperOpt
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgramOpt,genBlockOpt,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,InputSentinel.outStage_physical hc⟩

open Classical in
theorem full_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperOpt layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programOpt (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperOpt layout C cx cy

def entryOpt : Challenge.Entry := fun C=>normalizeProgram (programOpt C)
def boundsOpt : Challenge.Bounds := ⟨2150533,1498370,1587,50249314⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150533 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150535 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150533
    omega

theorem program_measurements (C : Point) : measurementCount (programOpt C)≤1498370 := by
  cases C with
  | zero=>simp [programOpt,measurementCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_measurements530 (.some hc)
    have delta:=(wrapper_metrics hc).2.1
    change measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370
    omega

theorem program_qubits (C : Point) : qubits (programOpt C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=InputSentinel530.program_qubits530 (.some hc)
    change qubits (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) (wrapper_support hc)

theorem program_physical (C : Point) : GatePhysical (programOpt C) := by
  cases C with
  | zero=>simp [programOpt,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical hc

theorem program_slots (C : Point) : gateSlots (programOpt C)≤50249314 := by
  cases C with
  | zero=>simp [programOpt]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_slots530 (.some hc)
    have delta:=(wrapper_metrics hc).2.2
    change gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤50249314 at old
    change gateSlots (wrapperOpt layout (.some hc) cx cy)≤50249314
    omega

theorem certificateOpt : Challenge.Certificate entryOpt boundsOpt where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programOpt C))≤1498370
    rw [normalize_measurements];exact program_measurements C
  qubits_le C:=by
    change qubits (normalizeProgram (programOpt C))≤1587
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C:=by
    change gateSlots (normalizeProgram (programOpt C))≤50249314
    rw [normalize_slots];exact program_slots C

end ECDSAAdd.Entrant.ParityFinalUniform


namespace ECDSAAdd.Entrant.ParityFinalX
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  ParityStageX.genericAll Entry530.generic530

theorem reference_eq (L : ControlledPointLayout) (cx cy : Fp) :
    ParityStageX.genericRef L cx cy=Entry530.generic530 L cx cy := by
  simp only [ParityStageX.genericRef,Entry530.generic530,ParityStageX.entryRef,Entry530.entryStage530,
    ParityStageX.restEntry,Entry530.restE530]

theorem gen_block_run (P : Program) (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      P (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          P))))) m t).basis q = t.basis q := by
  have hw := layout_widths
  have hn := layout_nodup
  have tinv := tauM_invol layout hn
  have einv := swapE_invol layout hw hn
  have dinv := swapD_invol layout hw hn
  have uinv : ∀ q, Wrapper5.U layout (Wrapper5.U layout q) = q := fun q => Equiv.swap_apply_self _ _ _
  have gflag : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have sflag : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have eflag : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have dflag : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have tauM_def : ∀ q, tauM layout q =
      if q = layout.core.generic then layout.genericSelect else
        if q = layout.genericSelect then layout.core.generic else q := fun q => rfl
  -- tauM fixes everything off the two generic flags
  have tfix : ∀ q, q ≠ layout.core.generic → q ≠ layout.genericSelect → tauM layout q = q := by
    intro q h1 h2; rw [tauM_def q, if_neg h1, if_neg h2]
  have pclean : ∀ q ∈ layout.dialogPool, t.basis q = false :=
    fun q hq => (regValue_zero _ _).mp hclean q hq
  have pne (q : Wire) (hq : q ∈ layout.dialogPool) : q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => pool_not_flag q hq (e ▸ gflag), fun e => pool_not_flag q hq (e ▸ sflag)⟩
  have xyne (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => flags_not_point _ gflag (e ▸ hq), fun e => flags_not_point _ sflag (e ▸ hq)⟩
  have fne : layout.point.finite ≠ layout.core.generic ∧ layout.point.finite ≠ layout.genericSelect :=
    ⟨fun e => finite_not_flag.1 (e ▸ gflag), fun e => finite_not_flag.1 (e ▸ sflag)⟩
  -- the generic block in its own frame
  generalize ht' : pullState (tauM layout) t = t'
  have t'def : ∀ q, t'.basis q = t.basis (tauM layout q) := by intro q; rw [← ht']; rfl
  have t'x : ∀ q ∈ layout.point.x ++ layout.point.y, t'.basis q = t.basis q := by
    intro q hq; rw [t'def, tfix q (xyne q hq).1 (xyne q hq).2]
  have v : PointDialogValues layout X Y G t'.basis t'.basis := by
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [← hx]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_left _ hq)
    · rw [← hy]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_right _ hq)
    · rw [t'def, tauM_def, if_pos rfl]; exact hg
    · apply (regValue_zero _ _).mpr
      intro q hq
      rw [t'def, tfix q (pne q hq).1 (pne q hq).2]; exact pclean q hq
  have hb : t'.basis layout.point.finite = false := by
    rw [t'def, tfix _ fne.1 fne.2]; exact hf
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn P
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) P) m t' = R0
    at ph0 v0
  have R0clean : ∀ q ∈ layout.dialogPool, R0.basis q = false :=
    fun q hq => (regValue_zero _ _).mp v0.clean q hq
  -- U swaps two clean pool sites
  have u684 := Square5Placement.pool_member layout hw 684 (by omega)
  have u717 := Square5Placement.pool_member layout hw 717 (by omega)
  have U_def : ∀ q, Wrapper5.U layout q = if q = layout.core.poolWire 684 then layout.core.poolWire 717
      else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
    intro q
    show (Equiv.swap _ _) q = _
    rw [Equiv.swap_apply_def]
  have R1 : run (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P)) m t' = R0 := by
    rw [run_rename_noop _ uinv]
    · exact hR0
    · apply swap_sym _ _ _ U_def
      have a : t'.basis (layout.core.poolWire 684) = false := by
        rw [t'def, tfix _ (pne _ u684).1 (pne _ u684).2]; exact pclean _ u684
      have b : t'.basis (layout.core.poolWire 717) = false := by
        rw [t'def, tfix _ (pne _ u717).1 (pne _ u717).2]; exact pclean _ u717
      rw [a, b]
    · rw [hR0]
      apply swap_sym _ _ _ U_def
      rw [R0clean _ u684, R0clean _ u717]
  -- tauM is the real swap between the generic flag and the generic select
  have R2 : run (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_invol _ tinv, ht', R1]
  -- R0 off the point registers equals the pulled start
  have R0rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → R0.basis q = t'.basis q := v0.rest
  have tq_off : ∀ q, q ∉ layout.point.x ++ layout.point.y → tauM layout q ∉ layout.point.x ++ layout.point.y := by
    intro q hq
    rw [tauM_def]
    split_ifs
    · exact flags_not_point _ sflag
    · exact flags_not_point _ gflag
    · exact hq
  have R2rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → (pullState (tauM layout) R0).basis q = t.basis q := by
    intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, R0rest _ (tq_off q hq), t'def, tinv]
  -- swapE and swapD act on clean wires before and after
  have spE := spare_pool layout hw
  have spD := spareD_pool layout hw
  have E_def : ∀ q, swapE layout q = if q = layout.core.equalNegY then spareWire layout
      else if q = spareWire layout then layout.core.equalNegY else q := fun q => rfl
  have D_def : ∀ q, swapD layout q = if q = layout.doubleSelect then spareD layout
      else if q = spareD layout then layout.doubleSelect else q := fun q => rfl
  have R2E : (pullState (tauM layout) R0).basis layout.core.equalNegY = false := by
    rw [R2rest _ (flags_not_point _ eflag)]; exact hE
  have R2Es : (pullState (tauM layout) R0).basis (spareWire layout) = false := by
    rw [R2rest _ (pool_not_point _ spE)]; exact pclean _ spE
  have R2D : (pullState (tauM layout) R0).basis layout.doubleSelect = false := by
    rw [R2rest _ (flags_not_point _ dflag)]; exact hD
  have R2Ds : (pullState (tauM layout) R0).basis (spareD layout) = false := by
    rw [R2rest _ (pool_not_point _ spD)]; exact pclean _ spD
  have R3 : run (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P)))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ dinv _ _ _ (swap_sym _ _ _ D_def _ (by rw [hD, pclean _ spD]))
      (by rw [R3]; exact swap_sym _ _ _ D_def _ (by rw [R2D, R2Ds])), R3]
  rw [R4]
  refine ⟨?_, ?_, ?_, R2rest⟩
  · have e1 : (pullState (tauM layout) R0).phase = R0.phase := rfl
    rw [e1, ph0, ← ht']; rfl
  · rw [← v0.x]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_left _ hq)).1 (xyne q (List.mem_append_left _ hq)).2]
  · rw [← v0.y]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_right _ hq)).1 (xyne q (List.mem_append_right _ hq)).2]

def genBlockOpt (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ParityStageX.genericAll L cx cy))
def finiteProgramOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlockOpt L cx cy))) ++ InputSentinel.outStage L C
def wrapperOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgramOpt L C cx cy)

open Classical in
theorem finite_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgramOpt layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgramOpt layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgramOpt
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlockOpt layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlockOpt
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run (ParityStageX.genericAll layout cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ParityStageX.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (ParityStageX.genericAll layout cx cy) (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ParityStageX.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run (ParityStageX.genericAll layout cx cy) x y x y false
        (fun base' => ParityStageX.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperOpt layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run hc b R s m hs
  unfold wrapperOpt
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h



theorem rename_wires_sub (f : Wire → Wire) (P Q : Program) (h : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  simp only [renameProgram_support]
  exact Finset.image_subset_image h

theorem wrapper_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆wires (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have h:=ParityStageX.generic_wires layout layout_widths cx cy
  rw [reference_eq] at h
  have b:=rename_wires_sub (Wrapper5.U layout) _ _ (rename_wires_sub (swapF layout) _ _ h)
  have m:=rename_wires_sub (swapD layout) _ _ (rename_wires_sub (swapE layout) _ _
    (rename_wires_sub (tauM layout) _ _ b))
  unfold wrapperOpt InputSentinel530.wrapper530
  apply rename_wires_sub
  simp only [finiteProgramOpt,InputSentinel530.finiteProgram530,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) m) (Finset.Subset.refl _)

theorem support_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆layout.dialogUsedWires.toFinset :=
  (wrapper_support hc).trans (InputSentinel530.support_used530 hc)

theorem wrapper_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperOpt layout (.some hc) cx cy)+3=
      toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    measurementCount (wrapperOpt layout (.some hc) cx cy)=
      measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    gateSlots (wrapperOpt layout (.some hc) cx cy)≤
      gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have t:=ParityStageX.generic_toffoli layout layout_widths cx cy
  have h:=ParityStageX.generic_counts layout layout_widths cx cy
  rw [reference_eq] at t h
  simp only [wrapperOpt,finiteProgramOpt,genBlockOpt,InputSentinel530.wrapper530,
    InputSentinel530.finiteProgram530,InputSentinel530.genBlock530,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega
theorem wrapper_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperOpt layout (.some hc) cx cy) := by
  have old:GatePhysical (ParityStageX.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0:=ParityStageX.generic_physical layout layout_widths layout_nodup cx cy old
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapperOpt
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgramOpt,genBlockOpt,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,InputSentinel.outStage_physical hc⟩

open Classical in
theorem full_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperOpt layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programOpt (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperOpt layout C cx cy

def entryOpt : Challenge.Entry := fun C=>normalizeProgram (programOpt C)
def boundsOpt : Challenge.Bounds := ⟨2150532,1498370,1587,50249314⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150532 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150535 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150532
    omega

theorem program_measurements (C : Point) : measurementCount (programOpt C)≤1498370 := by
  cases C with
  | zero=>simp [programOpt,measurementCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_measurements530 (.some hc)
    have delta:=(wrapper_metrics hc).2.1
    change measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370
    omega

theorem program_qubits (C : Point) : qubits (programOpt C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=InputSentinel530.program_qubits530 (.some hc)
    change qubits (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) (wrapper_support hc)

theorem program_physical (C : Point) : GatePhysical (programOpt C) := by
  cases C with
  | zero=>simp [programOpt,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical hc

theorem program_slots (C : Point) : gateSlots (programOpt C)≤50249314 := by
  cases C with
  | zero=>simp [programOpt]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_slots530 (.some hc)
    have delta:=(wrapper_metrics hc).2.2
    change gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤50249314 at old
    change gateSlots (wrapperOpt layout (.some hc) cx cy)≤50249314
    omega

theorem certificateOpt : Challenge.Certificate entryOpt boundsOpt where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programOpt C))≤1498370
    rw [normalize_measurements];exact program_measurements C
  qubits_le C:=by
    change qubits (normalizeProgram (programOpt C))≤1587
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C:=by
    change gateSlots (normalizeProgram (programOpt C))≤50249314
    rw [normalize_slots];exact program_slots C

end ECDSAAdd.Entrant.ParityFinalX

namespace ECDSAAdd.Entrant.ParityFinalXY
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  ParityStageXY.genericAll Entry530.generic530

theorem reference_eq (L : ControlledPointLayout) (cx cy : Fp) :
    ParityStageXY.genericRef L cx cy=Entry530.generic530 L cx cy := by
  simp only [ParityStageXY.genericRef,Entry530.generic530,ParityStageXY.entryRef,Entry530.entryStage530,
    ParityStageXY.restEntry,Entry530.restE530]

theorem gen_block_run (P : Program) (X Y X' Y' : Fp) (G : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues layout X Y G base')
      P (PointDialogValues layout X' Y' G base'))
    (t : State) (m : List Bool)
    (hx : regValue layout.point.x t.basis = X.val) (hy : regValue layout.point.y t.basis = Y.val)
    (hf : t.basis layout.point.finite = false) (hg : t.basis layout.genericSelect = G)
    (hE : t.basis layout.core.equalNegY = false)
    (hD : t.basis layout.doubleSelect = false) (hclean : regValue layout.dialogPool t.basis = 0) :
    (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).phase = t.phase ∧
    regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = X'.val ∧
    regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
      (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t).basis = Y'.val ∧
    ∀ q, q ∉ layout.point.x ++ layout.point.y →
      (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
        (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
          P))))) m t).basis q = t.basis q := by
  have hw := layout_widths
  have hn := layout_nodup
  have tinv := tauM_invol layout hn
  have einv := swapE_invol layout hw hn
  have dinv := swapD_invol layout hw hn
  have uinv : ∀ q, Wrapper5.U layout (Wrapper5.U layout q) = q := fun q => Equiv.swap_apply_self _ _ _
  have gflag : layout.core.generic ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have sflag : layout.genericSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have eflag : layout.core.equalNegY ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have dflag : layout.doubleSelect ∈ layout.inPlaceFlags := by simp [ControlledPointLayout.inPlaceFlags]
  have tauM_def : ∀ q, tauM layout q =
      if q = layout.core.generic then layout.genericSelect else
        if q = layout.genericSelect then layout.core.generic else q := fun q => rfl
  -- tauM fixes everything off the two generic flags
  have tfix : ∀ q, q ≠ layout.core.generic → q ≠ layout.genericSelect → tauM layout q = q := by
    intro q h1 h2; rw [tauM_def q, if_neg h1, if_neg h2]
  have pclean : ∀ q ∈ layout.dialogPool, t.basis q = false :=
    fun q hq => (regValue_zero _ _).mp hclean q hq
  have pne (q : Wire) (hq : q ∈ layout.dialogPool) : q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => pool_not_flag q hq (e ▸ gflag), fun e => pool_not_flag q hq (e ▸ sflag)⟩
  have xyne (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.core.generic ∧ q ≠ layout.genericSelect :=
    ⟨fun e => flags_not_point _ gflag (e ▸ hq), fun e => flags_not_point _ sflag (e ▸ hq)⟩
  have fne : layout.point.finite ≠ layout.core.generic ∧ layout.point.finite ≠ layout.genericSelect :=
    ⟨fun e => finite_not_flag.1 (e ▸ gflag), fun e => finite_not_flag.1 (e ▸ sflag)⟩
  -- the generic block in its own frame
  generalize ht' : pullState (tauM layout) t = t'
  have t'def : ∀ q, t'.basis q = t.basis (tauM layout q) := by intro q; rw [← ht']; rfl
  have t'x : ∀ q ∈ layout.point.x ++ layout.point.y, t'.basis q = t.basis q := by
    intro q hq; rw [t'def, tfix q (xyne q hq).1 (xyne q hq).2]
  have v : PointDialogValues layout X Y G t'.basis t'.basis := by
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · rw [← hx]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_left _ hq)
    · rw [← hy]; apply regValue_congr; intro q hq; exact t'x q (List.mem_append_right _ hq)
    · rw [t'def, tauM_def, if_pos rfl]; exact hg
    · apply (regValue_zero _ _).mpr
      intro q hq
      rw [t'def, tfix q (pne q hq).1 (pne q hq).2]; exact pclean q hq
  have hb : t'.basis layout.point.finite = false := by
    rw [t'def, tfix _ fne.1 fne.2]; exact hf
  obtain ⟨ph0, v0⟩ := swapF_values layout hw hn P
    X Y X' Y' G t'.basis hP hb t' m v
  generalize hR0 : run (renameProgram (swapF layout) P) m t' = R0
    at ph0 v0
  have R0clean : ∀ q ∈ layout.dialogPool, R0.basis q = false :=
    fun q hq => (regValue_zero _ _).mp v0.clean q hq
  -- U swaps two clean pool sites
  have u684 := Square5Placement.pool_member layout hw 684 (by omega)
  have u717 := Square5Placement.pool_member layout hw 717 (by omega)
  have U_def : ∀ q, Wrapper5.U layout q = if q = layout.core.poolWire 684 then layout.core.poolWire 717
      else if q = layout.core.poolWire 717 then layout.core.poolWire 684 else q := by
    intro q
    show (Equiv.swap _ _) q = _
    rw [Equiv.swap_apply_def]
  have R1 : run (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P)) m t' = R0 := by
    rw [run_rename_noop _ uinv]
    · exact hR0
    · apply swap_sym _ _ _ U_def
      have a : t'.basis (layout.core.poolWire 684) = false := by
        rw [t'def, tfix _ (pne _ u684).1 (pne _ u684).2]; exact pclean _ u684
      have b : t'.basis (layout.core.poolWire 717) = false := by
        rw [t'def, tfix _ (pne _ u717).1 (pne _ u717).2]; exact pclean _ u717
      rw [a, b]
    · rw [hR0]
      apply swap_sym _ _ _ U_def
      rw [R0clean _ u684, R0clean _ u717]
  -- tauM is the real swap between the generic flag and the generic select
  have R2 : run (renameProgram (tauM layout) (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
      P))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_invol _ tinv, ht', R1]
  -- R0 off the point registers equals the pulled start
  have R0rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → R0.basis q = t'.basis q := v0.rest
  have tq_off : ∀ q, q ∉ layout.point.x ++ layout.point.y → tauM layout q ∉ layout.point.x ++ layout.point.y := by
    intro q hq
    rw [tauM_def]
    split_ifs
    · exact flags_not_point _ sflag
    · exact flags_not_point _ gflag
    · exact hq
  have R2rest : ∀ q, q ∉ layout.point.x ++ layout.point.y → (pullState (tauM layout) R0).basis q = t.basis q := by
    intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, R0rest _ (tq_off q hq), t'def, tinv]
  -- swapE and swapD act on clean wires before and after
  have spE := spare_pool layout hw
  have spD := spareD_pool layout hw
  have E_def : ∀ q, swapE layout q = if q = layout.core.equalNegY then spareWire layout
      else if q = spareWire layout then layout.core.equalNegY else q := fun q => rfl
  have D_def : ∀ q, swapD layout q = if q = layout.doubleSelect then spareD layout
      else if q = spareD layout then layout.doubleSelect else q := fun q => rfl
  have R2E : (pullState (tauM layout) R0).basis layout.core.equalNegY = false := by
    rw [R2rest _ (flags_not_point _ eflag)]; exact hE
  have R2Es : (pullState (tauM layout) R0).basis (spareWire layout) = false := by
    rw [R2rest _ (pool_not_point _ spE)]; exact pclean _ spE
  have R2D : (pullState (tauM layout) R0).basis layout.doubleSelect = false := by
    rw [R2rest _ (flags_not_point _ dflag)]; exact hD
  have R2Ds : (pullState (tauM layout) R0).basis (spareD layout) = false := by
    rw [R2rest _ (pool_not_point _ spD)]; exact pclean _ spD
  have R3 : run (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P)))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ einv _ _ _ (swap_sym _ _ _ E_def _ (by rw [hE, pclean _ spE]))
      (by rw [R2]; exact swap_sym _ _ _ E_def _ (by rw [R2E, R2Es])), R2]
  have R4 : run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (renameProgram (Wrapper5.U layout) (renameProgram (swapF layout)
        P))))) m t = pullState (tauM layout) R0 := by
    rw [run_rename_noop _ dinv _ _ _ (swap_sym _ _ _ D_def _ (by rw [hD, pclean _ spD]))
      (by rw [R3]; exact swap_sym _ _ _ D_def _ (by rw [R2D, R2Ds])), R3]
  rw [R4]
  refine ⟨?_, ?_, ?_, R2rest⟩
  · have e1 : (pullState (tauM layout) R0).phase = R0.phase := rfl
    rw [e1, ph0, ← ht']; rfl
  · rw [← v0.x]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_left _ hq)).1 (xyne q (List.mem_append_left _ hq)).2]
  · rw [← v0.y]; apply regValue_congr; intro q hq
    have e1 : (pullState (tauM layout) R0).basis q = R0.basis (tauM layout q) := rfl
    rw [e1, tfix q (xyne q (List.mem_append_right _ hq)).1 (xyne q (List.mem_append_right _ hq)).2]

def genBlockOpt (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ParityStageXY.genericAll L cx cy))
def finiteProgramOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlockOpt L cx cy))) ++ InputSentinel.outStage L C
def wrapperOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgramOpt L C cx cy)

open Classical in
theorem finite_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgramOpt layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgramOpt layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgramOpt
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlockOpt layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlockOpt
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run (ParityStageXY.genericAll layout cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ParityStageXY.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (ParityStageXY.genericAll layout cx cy) (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ParityStageXY.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run (ParityStageXY.genericAll layout cx cy) x y x y false
        (fun base' => ParityStageXY.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperOpt layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run hc b R s m hs
  unfold wrapperOpt
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h



theorem rename_wires_sub (f : Wire → Wire) (P Q : Program) (h : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  simp only [renameProgram_support]
  exact Finset.image_subset_image h

theorem wrapper_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆wires (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have h:=ParityStageXY.generic_wires layout layout_widths cx cy
  rw [reference_eq] at h
  have b:=rename_wires_sub (Wrapper5.U layout) _ _ (rename_wires_sub (swapF layout) _ _ h)
  have m:=rename_wires_sub (swapD layout) _ _ (rename_wires_sub (swapE layout) _ _
    (rename_wires_sub (tauM layout) _ _ b))
  unfold wrapperOpt InputSentinel530.wrapper530
  apply rename_wires_sub
  simp only [finiteProgramOpt,InputSentinel530.finiteProgram530,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) m) (Finset.Subset.refl _)

theorem support_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆layout.dialogUsedWires.toFinset :=
  (wrapper_support hc).trans (InputSentinel530.support_used530 hc)

theorem wrapper_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperOpt layout (.some hc) cx cy)+4=
      toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    measurementCount (wrapperOpt layout (.some hc) cx cy)=
      measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    gateSlots (wrapperOpt layout (.some hc) cx cy)≤
      gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have t:=ParityStageXY.generic_toffoli layout layout_widths cx cy
  have h:=ParityStageXY.generic_counts layout layout_widths cx cy
  rw [reference_eq] at t h
  simp only [wrapperOpt,finiteProgramOpt,genBlockOpt,InputSentinel530.wrapper530,
    InputSentinel530.finiteProgram530,InputSentinel530.genBlock530,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  omega
theorem wrapper_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperOpt layout (.some hc) cx cy) := by
  have old:GatePhysical (ParityStageXY.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0:=ParityStageXY.generic_physical layout layout_widths layout_nodup cx cy old
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapperOpt
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgramOpt,genBlockOpt,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,InputSentinel.outStage_physical hc⟩

open Classical in
theorem full_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperOpt layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programOpt (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperOpt layout C cx cy

def entryOpt : Challenge.Entry := fun C=>normalizeProgram (programOpt C)
def boundsOpt : Challenge.Bounds := ⟨2150531,1498370,1587,50249314⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150531 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150535 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150531
    omega

theorem program_measurements (C : Point) : measurementCount (programOpt C)≤1498370 := by
  cases C with
  | zero=>simp [programOpt,measurementCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_measurements530 (.some hc)
    have delta:=(wrapper_metrics hc).2.1
    change measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370
    omega

theorem program_qubits (C : Point) : qubits (programOpt C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=InputSentinel530.program_qubits530 (.some hc)
    change qubits (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) (wrapper_support hc)

theorem program_physical (C : Point) : GatePhysical (programOpt C) := by
  cases C with
  | zero=>simp [programOpt,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical hc

theorem program_slots (C : Point) : gateSlots (programOpt C)≤50249314 := by
  cases C with
  | zero=>simp [programOpt]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_slots530 (.some hc)
    have delta:=(wrapper_metrics hc).2.2
    change gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤50249314 at old
    change gateSlots (wrapperOpt layout (.some hc) cx cy)≤50249314
    omega

theorem certificateOpt : Challenge.Certificate entryOpt boundsOpt where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programOpt C))≤1498370
    rw [normalize_measurements];exact program_measurements C
  qubits_le C:=by
    change qubits (normalizeProgram (programOpt C))≤1587
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C:=by
    change gateSlots (normalizeProgram (programOpt C))≤50249314
    rw [normalize_slots];exact program_slots C

end ECDSAAdd.Entrant.ParityFinalXY

-- Consolidated output proof: OutputOpt
section
namespace ECDSAAdd.Entrant.OutputOpt
open Arithmetic Challenge RecordedQuantum MeasuredCodec5 Baselines InputSentinel
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
def canonical0 : Program := [
 .CCX 0 2 10,
 .X 1,
 .CCX 10 1 5,
 .X 1,
 .CX 10 0,
 .CCX 4 0 11,
 .CX 10 0,
 .CX 7 8,
 .X 1,
 .measureX 9 [] [.CZ 11 1, .CZ 8 1],
 .measureX 7 [] [.CZ 8 1],
 .X 1,
 .X 3,
 .measureX 8 [] [.CZ 11 3],
 .X 3,
 .measureX 11 [] [.CZ 4 0, .CZ 4 10],
 .measureX 6 [] [.CZ 4 5],
 .measureX 10 [] [.CZ 0 2],
 .X 5,
 .measureX 10 [] [],
 .measureX 11 [] []
]

def canonical1 : Program := [
 .CCX 0 2 10,
 .X 1,
 .CCX 10 1 5,
 .X 1,
 .CX 10 0,
 .CCX 4 0 11,
 .CX 10 0,
 .CX 9 8,
 .X 1,
 .measureX 7 [] [.CZ 11 1, .CZ 8 1],
 .measureX 9 [] [.CZ 8 1],
 .X 1,
 .measureX 8 [] [.CZ 11 3],
 .measureX 11 [] [.CZ 4 0, .CZ 4 10],
 .measureX 6 [] [.CZ 4 5],
 .measureX 10 [] [.CZ 0 2],
 .X 5,
 .measureX 10 [] [],
 .measureX 11 [] []
]

def canonical (delta:Bool) : Program := if delta then canonical1 else canonical0

def prep1 (a1 s2 b2 yc:Bool) : Program :=
  (if a1 then [.X 1] else [])++(if !s2 then [.X 2] else [])++
  (if b2 ^^ !s2 then [.CX 1 2] else [])++(if yc then [.X 3] else [])

def prep2 (a1 s2 b2 yc:Bool) : Program :=
  (if a1 then [.X 1] else [])++(if !b2 then [.X 2] else [])++
  (if s2 ^^ !b2 then [.CX 1 2] else [])++[.CX 1 2,.CX 2 1,.CX 1 2]++
  (if yc then [.X 3] else [])

def otail1 (a1 s2 b2 yc y2c e:Bool) : Program :=
  if e then prep1 a1 s2 b2 yc++canonical (yc ^^ y2c)++(prep1 a1 s2 b2 yc).reverse
  else InputSentinel.otail1 a1 s2 b2 yc y2c e

def otail2 (a1 s2 b2 yc y2c e:Bool) : Program :=
  if e then prep2 a1 s2 b2 yc++canonical (yc ^^ y2c)++(prep2 a1 s2 b2 yc).reverse
  else InputSentinel.otail2 a1 s2 b2 yc y2c e

theorem otail1_ok : ∀ a1 s2 b2 yc y2c e:Bool,∀v:Fin 32,
    let xS:=oxS1 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xA:=oxA1 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xB:=oxB1 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    safe (otail1 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val)=true ∧
    bitRun (otail1 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val)=oout xS v.val := by
  decide +kernel

theorem otail2_ok : ∀ a1 s2 b2 yc y2c e:Bool,∀v:Fin 32,
    let xS:=oxS2 a1 s2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xA:=oxA2 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    let xB:=oxB2 a1 b2 (v.val.testBit 0) (v.val.testBit 1) (v.val.testBit 2)
    safe (otail2 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val)=true ∧
    bitRun (otail2 a1 s2 b2 yc y2c e) (oin xS xA xB yc y2c e v.val)=oout xS v.val := by
  decide +kernel

theorem otail_counts (a1 s2 b2 yc y2c e:Bool) :
    toffoliCount (otail1 a1 s2 b2 yc y2c e)=(if e then 3 else 5) ∧
    toffoliCount (otail2 a1 s2 b2 yc y2c e)=(if e then 3 else 5) ∧
    measurementCount (otail1 a1 s2 b2 yc y2c e)=8 ∧
    measurementCount (otail2 a1 s2 b2 yc y2c e)=8 := by
  cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> cases e <;> decide +kernel

end ECDSAAdd.Entrant.OutputOpt
end

-- Consolidated output proof: OutputTailBounds
section
namespace ECDSAAdd.Entrant.OutputOpt
open Arithmetic Challenge RecordedQuantum MeasuredCodec5 Baselines InputSentinel
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

theorem otail1_subset (a1 s2 b2 yc y2c e:Bool) :
    wires (otail1 a1 s2 b2 yc y2c e)⊆wires (InputSentinel.otail1 a1 s2 b2 yc y2c e) := by
  cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> cases e <;> decide +kernel

theorem otail1_slots_delta (a1 s2 b2 yc y2c e:Bool) :
    gateSlots (otail1 a1 s2 b2 yc y2c e)≤gateSlots (InputSentinel.otail1 a1 s2 b2 yc y2c e)+12 := by
  cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> cases e <;> decide +kernel

theorem otail2_subset (a1 s2 b2 yc y2c e:Bool) :
    wires (otail2 a1 s2 b2 yc y2c e)⊆wires (InputSentinel.otail2 a1 s2 b2 yc y2c e) := by
  cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> cases e <;> decide +kernel

theorem otail2_slots_delta (a1 s2 b2 yc y2c e:Bool) :
    gateSlots (otail2 a1 s2 b2 yc y2c e)≤gateSlots (InputSentinel.otail2 a1 s2 b2 yc y2c e)+12 := by
  cases a1 <;> cases s2 <;> cases b2 <;> cases yc <;> cases y2c <;> cases e <;> decide +kernel

end ECDSAAdd.Entrant.OutputOpt
end

-- Consolidated output proof: OutputLift
section
namespace ECDSAAdd.Entrant.OutputOpt
open Arithmetic Challenge RecordedQuantum MeasuredCodec5 Baselines InputSentinel Secp256k1 ControlledPointLayout
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
def otail (tr : Tri) (yc y2c e : Bool) : Program :=
  if tr.role1 then otail1 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) (tr.B.testBit tr.r2) yc y2c e
  else otail2 (tr.A.testBit tr.r1) (tr.S.testBit tr.r2) (tr.B.testBit tr.r2) yc y2c e

def otailL (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire) (h : Wire) : Program :=
  renameProgram (LocalWireModel.label
    (fun q : Fin 13 => [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].getD q.val 0)) (otail tr yc y2c e)

/-- Output classifier: the input-stage zero test on the output abscissa with the output tail. -/
def oclassifier (tr : Tri) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) : Program :=
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  (zeroWith (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work) ++
  ([.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ++
  tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx)))


theorem otail_core (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (w : Fin 32) :
    safe (otail tr yc y2c e) (oin (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.A (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.B (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) yc y2c e w.val) = true ∧
    bitRun (otail tr yc y2c e) (oin (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.A (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2))
      (tX tr tr.B (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) yc y2c e w.val) =
      oout (tX tr tr.S (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)) w.val := by
  have br := tX_bridge tr v (w.val.testBit 0) (w.val.testBit 1) (w.val.testBit 2)
  unfold otail
  by_cases ro : tr.role1 = true
  · obtain ⟨hS, hA, hB⟩ := br.1 ro
    rw [if_pos ro, hS, hA, hB]
    exact otail1_ok _ _ _ yc y2c e w
  · have ro' : tr.role1 = false := by simpa using ro
    obtain ⟨hS, hA, hB⟩ := br.2 ro'
    rw [if_neg ro, hS, hA, hB]
    exact otail2_ok _ _ _ yc y2c e w

theorem otail_support (tr : Tri) (yc y2c e : Bool) : wires (otail tr yc y2c e) ⊆ Finset.range 13 := by
  unfold otail
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_physical (tr : Tri) (yc y2c e : Bool) : GatePhysical (otail tr yc y2c e) := by
  unfold otail
  split_ifs <;> apply gatePhysical_of_all <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_slots (tr : Tri) (yc y2c e : Bool) : gateSlots (otail tr yc y2c e) ≤ 45 := by
  unfold otail
  split_ifs <;>
  · generalize tr.A.testBit tr.r1 = a; generalize tr.S.testBit tr.r2 = b
    generalize tr.B.testBit tr.r2 = c
    cases a <;> cases b <;> cases c <;> cases yc <;> cases y2c <;> cases e <;> decide

theorem otail_counts' (tr : Tri) (yc y2c e : Bool) :
    toffoliCount (otail tr yc y2c e) = (if e then 3 else 5) ∧ measurementCount (otail tr yc y2c e) = 8 := by
  unfold otail
  by_cases ro : tr.role1 = true
  · rw [if_pos ro]
    exact ⟨(otail_counts _ _ _ _ _ _).1, (otail_counts _ _ _ _ _ _).2.2.1⟩
  · rw [if_neg ro]
    exact ⟨(otail_counts _ _ _ _ _ _).2.1, (otail_counts _ _ _ _ _ _).2.2.2⟩

/-! ### The output tail on its thirteen wires -/

theorem otailL_support (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    wires (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) ⊆
      {h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u} := by
  unfold otailL
  rw [renameProgram_support]
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have ha13 : a < 13 := Finset.mem_range.mp (otail_support tr yc y2c e ha)
  simp only [LocalWireModel.label, dif_pos ha13]
  interval_cases a <;> simp

theorem otailL_physical (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup) :
    GatePhysical (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) := by
  have inj := LocalWireModel.listPorts_injective [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] hnd
    (n := 13) (by simp)
  unfold otailL
  exact gatePhysical_rename_support _ _ (fun a ha b hb heq =>
    LocalWireModel.label_injective _ inj a (otail_support tr yc y2c e ha) b (otail_support tr yc y2c e hb) heq)
    (otail_physical tr yc y2c e)

theorem otailL_counts (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    toffoliCount (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = (if e then 3 else 5) ∧
    measurementCount (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = 8 := by
  unfold otailL
  rw [(renameProgram_counts _ _).1, (renameProgram_counts _ _).2]
  exact otail_counts' tr yc y2c e

theorem otailL_slots (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h : Wire) :
    gateSlots (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) = gateSlots (otail tr yc y2c e) := by
  unfold otailL
  exact rename_gateSlots _ _

/-- Tail precondition: clean scratch, and the four corner flags hold their match bits. -/
def otailPre (tr : Tri) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire) (uu : Bool)
    (st : BasisState) : Prop :=
  st f = false ∧ st t1 = false ∧ st t2 = false ∧ st u = false ∧
  st g = (st c && tX tr tr.S uu (st xr1) (st xr2)) ∧
  st O = (st c && tX tr tr.A uu (st xr1) (st xr2) && (st y0 == yc)) ∧
  st D = (st c && tX tr tr.B uu (st xr1) (st xr2) && (st y0 == y2c)) ∧
  st H = (e && st c && tX tr tr.A uu (st xr1) (st xr2) && (st y0 != yc))

/-- Tail effect: the finite flag takes the negated sentinel match and the four flags are cleared. -/
def otailEff (tr : Tri) (xr1 xr2 f g O D H : Wire) (uu : Bool) (st : BasisState) : BasisState :=
  writeBit (writeBit (writeBit (writeBit (writeBit st f (!tX tr tr.S uu (st xr1) (st xr2))) g false)
    O false) D false) H false

theorem otailEff_apply (tr : Tri) (xr1 xr2 f g O D H : Wire) (uu : Bool) (st : BasisState) (q : Wire) :
    otailEff tr xr1 xr2 f g O D H uu st q =
      if q = H then false else if q = D then false else if q = O then false else if q = g then false
      else if q = f then !tX tr tr.S uu (st xr1) (st xr2) else st q := by
  unfold otailEff
  simp only [writeBit, Function.update_apply]

theorem otail_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (h xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (hnd : [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup) (s : State) (m : List Bool)
    (hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u (s.basis h) s.basis) :
    run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H (s.basis h) s.basis⟩ := by
  unfold otailPre at hp
  obtain ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩ := hp
  set r : List Wire := [h, xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] with hr
  have inj := LocalWireModel.listPorts_injective r hnd (n := 13) (by simp [hr])
  have rne : ∀ i j, i < 13 → j < 13 → i ≠ j → r.getD i 0 ≠ r.getD j 0 := by
    intro i j hi hj hij e
    have hi' : i < r.length := by simp [hr]; omega
    have hj' : j < r.length := by simp [hr]; omega
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at e
    exact hij (hnd.getElem_inj_iff.mp e)
  have n_h_f : h ≠ f := by simpa [hr] using rne 0 5 (by decide) (by decide) (by decide)
  have n_h_g : h ≠ g := by simpa [hr] using rne 0 6 (by decide) (by decide) (by decide)
  have n_h_O : h ≠ O := by simpa [hr] using rne 0 7 (by decide) (by decide) (by decide)
  have n_h_D : h ≠ D := by simpa [hr] using rne 0 8 (by decide) (by decide) (by decide)
  have n_h_H : h ≠ H := by simpa [hr] using rne 0 9 (by decide) (by decide) (by decide)
  have n_xr1_f : xr1 ≠ f := by simpa [hr] using rne 1 5 (by decide) (by decide) (by decide)
  have n_xr1_g : xr1 ≠ g := by simpa [hr] using rne 1 6 (by decide) (by decide) (by decide)
  have n_xr1_O : xr1 ≠ O := by simpa [hr] using rne 1 7 (by decide) (by decide) (by decide)
  have n_xr1_D : xr1 ≠ D := by simpa [hr] using rne 1 8 (by decide) (by decide) (by decide)
  have n_xr1_H : xr1 ≠ H := by simpa [hr] using rne 1 9 (by decide) (by decide) (by decide)
  have n_xr2_f : xr2 ≠ f := by simpa [hr] using rne 2 5 (by decide) (by decide) (by decide)
  have n_xr2_g : xr2 ≠ g := by simpa [hr] using rne 2 6 (by decide) (by decide) (by decide)
  have n_xr2_O : xr2 ≠ O := by simpa [hr] using rne 2 7 (by decide) (by decide) (by decide)
  have n_xr2_D : xr2 ≠ D := by simpa [hr] using rne 2 8 (by decide) (by decide) (by decide)
  have n_xr2_H : xr2 ≠ H := by simpa [hr] using rne 2 9 (by decide) (by decide) (by decide)
  have n_y0_f : y0 ≠ f := by simpa [hr] using rne 3 5 (by decide) (by decide) (by decide)
  have n_y0_g : y0 ≠ g := by simpa [hr] using rne 3 6 (by decide) (by decide) (by decide)
  have n_y0_O : y0 ≠ O := by simpa [hr] using rne 3 7 (by decide) (by decide) (by decide)
  have n_y0_D : y0 ≠ D := by simpa [hr] using rne 3 8 (by decide) (by decide) (by decide)
  have n_y0_H : y0 ≠ H := by simpa [hr] using rne 3 9 (by decide) (by decide) (by decide)
  have n_c_f : c ≠ f := by simpa [hr] using rne 4 5 (by decide) (by decide) (by decide)
  have n_c_g : c ≠ g := by simpa [hr] using rne 4 6 (by decide) (by decide) (by decide)
  have n_c_O : c ≠ O := by simpa [hr] using rne 4 7 (by decide) (by decide) (by decide)
  have n_c_D : c ≠ D := by simpa [hr] using rne 4 8 (by decide) (by decide) (by decide)
  have n_c_H : c ≠ H := by simpa [hr] using rne 4 9 (by decide) (by decide) (by decide)
  have n_f_g : f ≠ g := by simpa [hr] using rne 5 6 (by decide) (by decide) (by decide)
  have n_f_O : f ≠ O := by simpa [hr] using rne 5 7 (by decide) (by decide) (by decide)
  have n_f_D : f ≠ D := by simpa [hr] using rne 5 8 (by decide) (by decide) (by decide)
  have n_f_H : f ≠ H := by simpa [hr] using rne 5 9 (by decide) (by decide) (by decide)
  have n_g_f : g ≠ f := by simpa [hr] using rne 6 5 (by decide) (by decide) (by decide)
  have n_g_O : g ≠ O := by simpa [hr] using rne 6 7 (by decide) (by decide) (by decide)
  have n_g_D : g ≠ D := by simpa [hr] using rne 6 8 (by decide) (by decide) (by decide)
  have n_g_H : g ≠ H := by simpa [hr] using rne 6 9 (by decide) (by decide) (by decide)
  have n_O_f : O ≠ f := by simpa [hr] using rne 7 5 (by decide) (by decide) (by decide)
  have n_O_g : O ≠ g := by simpa [hr] using rne 7 6 (by decide) (by decide) (by decide)
  have n_O_D : O ≠ D := by simpa [hr] using rne 7 8 (by decide) (by decide) (by decide)
  have n_O_H : O ≠ H := by simpa [hr] using rne 7 9 (by decide) (by decide) (by decide)
  have n_D_f : D ≠ f := by simpa [hr] using rne 8 5 (by decide) (by decide) (by decide)
  have n_D_g : D ≠ g := by simpa [hr] using rne 8 6 (by decide) (by decide) (by decide)
  have n_D_O : D ≠ O := by simpa [hr] using rne 8 7 (by decide) (by decide) (by decide)
  have n_D_H : D ≠ H := by simpa [hr] using rne 8 9 (by decide) (by decide) (by decide)
  have n_H_f : H ≠ f := by simpa [hr] using rne 9 5 (by decide) (by decide) (by decide)
  have n_H_g : H ≠ g := by simpa [hr] using rne 9 6 (by decide) (by decide) (by decide)
  have n_H_O : H ≠ O := by simpa [hr] using rne 9 7 (by decide) (by decide) (by decide)
  have n_H_D : H ≠ D := by simpa [hr] using rne 9 8 (by decide) (by decide) (by decide)
  have n_t1_f : t1 ≠ f := by simpa [hr] using rne 10 5 (by decide) (by decide) (by decide)
  have n_t1_g : t1 ≠ g := by simpa [hr] using rne 10 6 (by decide) (by decide) (by decide)
  have n_t1_O : t1 ≠ O := by simpa [hr] using rne 10 7 (by decide) (by decide) (by decide)
  have n_t1_D : t1 ≠ D := by simpa [hr] using rne 10 8 (by decide) (by decide) (by decide)
  have n_t1_H : t1 ≠ H := by simpa [hr] using rne 10 9 (by decide) (by decide) (by decide)
  have n_t2_f : t2 ≠ f := by simpa [hr] using rne 11 5 (by decide) (by decide) (by decide)
  have n_t2_g : t2 ≠ g := by simpa [hr] using rne 11 6 (by decide) (by decide) (by decide)
  have n_t2_O : t2 ≠ O := by simpa [hr] using rne 11 7 (by decide) (by decide) (by decide)
  have n_t2_D : t2 ≠ D := by simpa [hr] using rne 11 8 (by decide) (by decide) (by decide)
  have n_t2_H : t2 ≠ H := by simpa [hr] using rne 11 9 (by decide) (by decide) (by decide)
  have n_u_f : u ≠ f := by simpa [hr] using rne 12 5 (by decide) (by decide) (by decide)
  have n_u_g : u ≠ g := by simpa [hr] using rne 12 6 (by decide) (by decide) (by decide)
  have n_u_O : u ≠ O := by simpa [hr] using rne 12 7 (by decide) (by decide) (by decide)
  have n_u_D : u ≠ D := by simpa [hr] using rne 12 8 (by decide) (by decide) (by decide)
  have n_u_H : u ≠ H := by simpa [hr] using rne 12 9 (by decide) (by decide) (by decide)
  set vv : Nat := ofBits [s.basis h, s.basis xr1, s.basis xr2, s.basis y0, s.basis c] with hvv
  have hv32 : vv < 32 := by
    simp only [hvv, ofBits]
    cases s.basis h <;> cases s.basis xr1 <;> cases s.basis xr2 <;> cases s.basis y0 <;> cases s.basis c <;> simp
  have v0 : vv.testBit 0 = s.basis h := by rw [hvv, ofBits_testBit]; rfl
  have v1 : vv.testBit 1 = s.basis xr1 := by rw [hvv, ofBits_testBit]; rfl
  have v2 : vv.testBit 2 = s.basis xr2 := by rw [hvv, ofBits_testBit]; rfl
  have v3 : vv.testBit 3 = s.basis y0 := by rw [hvv, ofBits_testBit]; rfl
  have v4 : vv.testBit 4 = s.basis c := by rw [hvv, ofBits_testBit]; rfl
  have core := otail_core tr v yc y2c e ⟨vv, hv32⟩
  simp only [v0, v1, v2] at core
  set xS := tX tr tr.S (s.basis h) (s.basis xr1) (s.basis xr2) with hxS
  set xA := tX tr tr.A (s.basis h) (s.basis xr1) (s.basis xr2) with hxA
  set xB := tX tr tr.B (s.basis h) (s.basis xr1) (s.basis xr2) with hxB
  have hx : ∀ q (hq : q < 13), s.basis ((fun q : Fin 13 => r.getD q.val 0) ⟨q, hq⟩) =
      (oin xS xA xB yc y2c e vv).testBit q := by
    intro q hq
    simp only [oin, ofBits_testBit]
    interval_cases q <;> simp [hr, v0, v1, v2, v3, v4, pf, pt1, pt2, pu, pg, pO, pD, pH]
  have L := lift_local 13 _ inj (otail tr yc y2c e) (otail_support tr yc y2c e) s m _ hx core.1
  rw [core.2] at L
  have port : ∀ q (hq : q < 13), (run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s).basis
      (r.getD q 0) = [vv.testBit 0, vv.testBit 1, vv.testBit 2, vv.testBit 3, vv.testBit 4, !xS,
        false, false, false, false, false, false, false].getD q false := by
    intro q hq
    have := L.2.1 q hq
    simp only [oout, ofBits_testBit] at this
    exact this
  apply State.extensionality
  · exact L.1
  · funext w
    show _ = otailEff tr xr1 xr2 f g O D H (s.basis h) s.basis w
    rw [otailEff_apply]
    by_cases wr : w ∈ r
    · obtain ⟨q, hq, hqw⟩ : ∃ q, q < 13 ∧ r.getD q 0 = w := by
        obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem wr
        exact ⟨i, by simpa [hr] using hi, by rw [List.getD_eq_getElem _ _ hi]; exact hiw⟩
      subst hqw
      rw [port q hq]
      interval_cases q <;> simp [hr, hxS, v0, v1, v2, v3, v4, pt1, pt2, pu, n_h_f, n_h_g, n_h_O, n_h_D, n_h_H, n_xr1_f, n_xr1_g, n_xr1_O, n_xr1_D, n_xr1_H, n_xr2_f, n_xr2_g, n_xr2_O, n_xr2_D, n_xr2_H, n_y0_f, n_y0_g, n_y0_O, n_y0_D, n_y0_H, n_c_f, n_c_g, n_c_O, n_c_D, n_c_H, n_f_g, n_f_O, n_f_D, n_f_H, n_g_f, n_g_O, n_g_D, n_g_H, n_O_f, n_O_g, n_O_D, n_O_H, n_D_f, n_D_g, n_D_O, n_D_H, n_H_f, n_H_g, n_H_O, n_H_D, n_t1_f, n_t1_g, n_t1_O, n_t1_D, n_t1_H, n_t2_f, n_t2_g, n_t2_O, n_t2_D, n_t2_H, n_u_f, n_u_g, n_u_O, n_u_D, n_u_H]
    · have nw : ∀ x ∈ r, w ≠ x := fun x hx heq => wr (heq ▸ hx)
      have hout : (run (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) m s).basis w = s.basis w :=
        L.2.2 w (fun q hq heq => wr (by
          rw [heq]
          show r.getD q 0 ∈ r
          rw [List.getD_eq_getElem _ _ (by simpa [hr] using hq)]
          exact List.getElem_mem _))
      rw [hout]
      simp [nw f (by simp [hr]), nw g (by simp [hr]), nw O (by simp [hr]), nw D (by simp [hr]),
        nw H (by simp [hr])]

/-! ### The zero chain with the output tail -/

theorem ochain_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (c0 : Wire) (bs : List ZeroBit) (hcu : c0 ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (hnd : (c0 :: bs.flatMap ZeroBit.wires).Nodup)
    (hdis : ∀ b ∈ bs, b.input ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (s : State) (m : List Bool)
    (hs : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis)
    (hz : ∀ b ∈ bs, s.basis b.work = false) :
    run (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) c0 bs) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H (s.basis c0 && bs.all (fun b => !s.basis b.input)) s.basis⟩ := by
  set used : List Wire := [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] with hu
  apply zeroWith_effect_runQ used (otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u)
    (otailEff tr xr1 xr2 f g O D H)
  · intro w hw uu st z
    have n : ∀ x ∈ used, x ≠ w := fun x hx heq => hw (heq ▸ hx)
    have p_xr1 : xr1 ≠ w := n xr1 (by simp [hu])
    have p_xr2 : xr2 ≠ w := n xr2 (by simp [hu])
    have p_y0 : y0 ≠ w := n y0 (by simp [hu])
    have p_c : c ≠ w := n c (by simp [hu])
    have p_f : f ≠ w := n f (by simp [hu])
    have p_g : g ≠ w := n g (by simp [hu])
    have p_O : O ≠ w := n O (by simp [hu])
    have p_D : D ≠ w := n D (by simp [hu])
    have p_H : H ≠ w := n H (by simp [hu])
    have p_t1 : t1 ≠ w := n t1 (by simp [hu])
    have p_t2 : t2 ≠ w := n t2 (by simp [hu])
    have p_u : u ≠ w := n u (by simp [hu])
    simp only [otailPre, writeBit, Function.update_apply, p_xr1, p_xr2, p_y0, p_c, p_f, p_g, p_O, p_D, p_H, p_t1, p_t2, p_u, if_false]
  · intro uu st w hw
    have n : ∀ x ∈ used, w ≠ x := fun x hx heq => hw (heq ▸ hx)
    rw [otailEff_apply]
    simp [n f (by simp [hu]), n g (by simp [hu]), n O (by simp [hu]), n D (by simp [hu]), n H (by simp [hu])]
  · intro uu st w z hw
    have n : ∀ x ∈ used, w ≠ x := fun x hx heq => hw (heq ▸ hx)
    have a1 : writeBit st w z xr1 = st xr1 := by
      simp [writeBit, Function.update, Ne.symm (n xr1 (by simp [hu]))]
    have a2 : writeBit st w z xr2 = st xr2 := by
      simp [writeBit, Function.update, Ne.symm (n xr2 (by simp [hu]))]
    funext q
    rw [otailEff_apply, a1, a2]
    by_cases hq : q = w
    · subst hq
      simp [writeBit, otailEff_apply, n f (by simp [hu]), n g (by simp [hu]), n O (by simp [hu]),
        n D (by simp [hu]), n H (by simp [hu])]
    · simp only [writeBit, Function.update_apply, hq, if_false]
      rw [otailEff_apply]
  · intro c' hc' st m' hp
    exact otail_run tr v yc y2c e c' xr1 xr2 y0 c f g O D H t1 t2 u (List.nodup_cons.mpr ⟨hc', hused⟩) st m' hp
  · exact hcu
  · exact hnd
  · exact hdis
  · exact hs
  · exact hz

/-! ### Remap, zero test with the output tail, undo -/

theorem oshape_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xr1 xr2 y0 c f g O D H t1 t2 u : Wire)
    (w : Nat → Wire) (i0 : Nat) (it : List Nat) (work : List Wire)
    (hPn : ((i0 :: it).map w).Nodup) (x1P : xr1 ∉ (i0 :: it).map w) (x2P : xr2 ∉ (i0 :: it).map w)
    (hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w)
    (hwl : (it.map w).length = work.length) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u])
    (s : State) (m : List Bool)
    (hz : ∀ q ∈ work, s.basis q = false)
    (hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis) :
    run (tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it))))) m s =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H
        ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis⟩ := by
  have hlw : (i0 :: it).map w = w i0 :: it.map w := rfl
  have p0l : w i0 ∈ (i0 :: it).map w := by simp
  have usedNotP : ∀ q ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | hq
    · exact x1P
    · exact x2P
    · exact hextP q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have itNe : ∀ i ∈ it, w i ≠ w i0 := by
    intro i hi heq
    rw [hlw] at hPn
    exact (List.nodup_cons.mp hPn).1 (heq ▸ List.mem_map_of_mem hi)
  -- step 1: remap
  have R1 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P m s
  rw [LocalWireModel.run_concat, remapList_mc, List.drop_zero, LocalWireModel.run_concat]
  generalize hs1 : run (tr.remapList xr1 xr2 w (i0 :: it)) m s = s1 at R1 ⊢
  -- step 2: X p0
  have e2 : run [Instr.X (w i0)] m s1 = ⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ := by
    simp [run]
  rw [e2]
  generalize hs2 : (⟨s1.phase, writeBit s1.basis (w i0) (!s1.basis (w i0))⟩ : State) = s2
  have s2ph : s2.phase = s.phase := by rw [← hs2]; exact R1.1
  have s2out : ∀ q, q ∉ (i0 :: it).map w → s2.basis q = s.basis q := by
    intro q hq
    have hq0 : q ≠ w i0 := fun heq => hq (heq ▸ p0l)
    rw [← hs2]; simp [writeBit, Function.update, hq0, R1.2.1 q hq]
  have s2p0 : s2.basis (w i0) = (s.basis (w i0) == tr.tgt i0 (s.basis xr1, s.basis xr2)) := by
    rw [← hs2]; simp only [writeBit, Function.update_self]
    rw [R1.2.2 i0 (by simp)]
    cases s.basis (w i0) <;> cases tr.tgt i0 (s.basis xr1, s.basis xr2) <;> rfl
  have s2it : ∀ i ∈ it, s2.basis (w i) = (s.basis (w i) ^^ tr.tgt i (s.basis xr1, s.basis xr2)) := by
    intro i hi
    rw [← hs2]; simp only [writeBit]
    rw [Function.update_of_ne (itNe i hi), R1.2.2 i (by simp [hi])]
  have k1 : s2.basis xr1 = s.basis xr1 := s2out xr1 x1P
  have k2 : s2.basis xr2 = s.basis xr2 := s2out xr2 x2P
  -- the zero-test value equals the match bit
  have zp := zeroPorts_maps (it.map w) work hwl
  have huV : (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    have hall : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
        it.all (fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
      have : (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input) =
          ((zeroPorts (it.map w) work).map ZeroBit.input).all (fun q => !s2.basis q) := by
        rw [List.all_map]; rfl
      rw [this, zp.1, List.all_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      apply forall₂_congr
      intro i hi
      simp only [Function.comp_apply, s2it i hi]
      cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> simp
    rw [hall, s2p0]
    simp [List.all_cons]
  -- step 3: the zero-test chain with the output tail
  have hcu : w i0 ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := fun h => usedNotP _ h p0l
  have hperm := zeroPorts_perm (it.map w) work hwl
  have hnd : (w i0 :: (zeroPorts (it.map w) work).flatMap ZeroBit.wires).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp (hperm.mem_iff.mp hm) with h | h
      · obtain ⟨i, hi, heq⟩ := List.mem_map.mp h
        exact itNe i hi heq
      · exact (hdisj _ h).1 p0l
    · apply hperm.symm.nodup_iff.mp
      apply List.nodup_append.mpr
      refine ⟨(List.nodup_cons.mp (hlw ▸ hPn)).2, hwn, ?_⟩
      intro a ha b hb heq
      subst heq
      exact (hdisj a hb).1 (by rw [hlw]; exact List.mem_cons_of_mem _ ha)
  have hdis' : ∀ b ∈ zeroPorts (it.map w) work, b.input ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] ∧
      b.work ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    intro b hb
    have hin : b.input ∈ it.map w := by
      have := (List.mem_map (f := ZeroBit.input)).mpr ⟨b, hb, rfl⟩; rwa [zp.1] at this
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    exact ⟨fun h => usedNotP _ h (by rw [hlw]; exact List.mem_cons_of_mem _ hin), (hdisj _ hwk).2⟩
  unfold otailPre at hp
  obtain ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩ := hp
  have qq : ∀ x ∈ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u], s2.basis x = s.basis x :=
    fun x hx => s2out x (usedNotP x hx)
  have hs3 : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      (s2.basis (w i0) && (zeroPorts (it.map w) work).all (fun b => !s2.basis b.input)) s2.basis := by
    rw [huV]
    unfold otailPre
    rw [qq f (by simp), qq t1 (by simp), qq t2 (by simp), qq u (by simp), qq g (by simp), qq c (by simp),
      qq O (by simp), qq D (by simp), qq H (by simp), qq y0 (by simp), k1, k2]
    exact ⟨pf, pt1, pt2, pu, pg, pO, pD, pH⟩
  have hz3 : ∀ b ∈ zeroPorts (it.map w) work, s2.basis b.work = false := by
    intro b hb
    have hwk : b.work ∈ work := by
      have := (List.mem_map (f := ZeroBit.work)).mpr ⟨b, hb, rfl⟩; rwa [zp.2] at this
    rw [s2out _ (hdisj _ hwk).1]; exact hz _ hwk
  rw [LocalWireModel.run_concat, ochain_run tr v yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u hused (w i0) _ hcu hnd
    hdis' s2 _ hs3 hz3, huV, LocalWireModel.run_concat]
  set V := (i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2) with hV
  set T3 := otailEff tr xr1 xr2 f g O D H V s2.basis with hT3
  have e4 : ∀ mm, run [Instr.X (w i0)] mm ⟨s2.phase, T3⟩ = ⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ := by
    intro mm; simp [run]
  rw [e4]
  generalize hs4 : (⟨s2.phase, writeBit T3 (w i0) (!T3 (w i0))⟩ : State) = s4
  have T3out : ∀ q, q ∉ (i0 :: it).map w → T3 q = otailEff tr xr1 xr2 f g O D H V s.basis q := by
    intro q hq
    rw [hT3, otailEff_apply, otailEff_apply, k1, k2, s2out q hq]
  have T3in : ∀ q, q ≠ f → q ≠ g → q ≠ O → q ≠ D → q ≠ H → T3 q = s2.basis q := by
    intro q h1 h2 h3 h4 h5
    rw [hT3, otailEff_apply]
    simp [h1, h2, h3, h4, h5]
  have u_xr1_f : xr1 ≠ f := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_g : xr1 ≠ g := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_O : xr1 ≠ O := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_D : xr1 ≠ D := fun heq => by rw [heq] at hused; simp at hused
  have u_xr1_H : xr1 ≠ H := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_f : xr2 ≠ f := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_g : xr2 ≠ g := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_O : xr2 ≠ O := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_D : xr2 ≠ D := fun heq => by rw [heq] at hused; simp at hused
  have u_xr2_H : xr2 ≠ H := fun heq => by rw [heq] at hused; simp at hused
  have s4x1 : s4.basis xr1 = s.basis xr1 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun heq => hcu (by simp [heq])), T3in xr1 u_xr1_f u_xr1_g u_xr1_O u_xr1_D u_xr1_H, k1]
  have s4x2 : s4.basis xr2 = s.basis xr2 := by
    rw [← hs4]; simp only [writeBit]
    rw [Function.update_of_ne (fun heq => hcu (by simp [heq])), T3in xr2 u_xr2_f u_xr2_g u_xr2_O u_xr2_D u_xr2_H, k2]
  -- step 5: remap again
  suffices key : ∀ mm, run (tr.remapList xr1 xr2 w (i0 :: it)) mm s4 =
      ⟨s.phase, otailEff tr xr1 xr2 f g O D H V s.basis⟩ from key _
  intro mm
  have R5 := Tri.remapList_run v xr1 xr2 w (i0 :: it) hPn x1P x2P mm s4
  apply State.extensionality
  · rw [R5.1, ← hs4]; exact s2ph
  · funext q
    by_cases hq : q ∈ (i0 :: it).map w
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      rw [R5.2.2 i hi, s4x1, s4x2]
      have nf : w i ≠ f := fun heq => usedNotP f (by simp) (heq ▸ hq)
      have ng : w i ≠ g := fun heq => usedNotP g (by simp) (heq ▸ hq)
      have nO : w i ≠ O := fun heq => usedNotP O (by simp) (heq ▸ hq)
      have nD : w i ≠ D := fun heq => usedNotP D (by simp) (heq ▸ hq)
      have nH : w i ≠ H := fun heq => usedNotP H (by simp) (heq ▸ hq)
      have rhs : otailEff tr xr1 xr2 f g O D H V s.basis (w i) = s.basis (w i) := by
        rw [otailEff_apply]; simp [nf, ng, nO, nD, nH]
      change (s4.basis (w i) ^^ _) = otailEff tr xr1 xr2 f g O D H V s.basis (w i)
      rw [rhs]
      rw [← hs4]; simp only [writeBit]
      rcases List.mem_cons.mp hi with rfl | hit
      · rw [Function.update_self, T3in _ nf ng nO nD nH, s2p0]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
      · rw [Function.update_of_ne (itNe i hit), T3in _ nf ng nO nD nH, s2it i hit]
        cases s.basis (w i) <;> cases tr.tgt i (s.basis xr1, s.basis xr2) <;> rfl
    · rw [R5.2.1 q hq, ← hs4]
      change writeBit T3 (w i0) (!T3 (w i0)) q = otailEff tr xr1 xr2 f g O D H V s.basis q
      simp only [writeBit]
      rw [Function.update_of_ne (fun heq : q = w i0 => hq (heq ▸ p0l)), T3out q hq]

/-! ### The output classifier -/

/-- The output classifier's match bit for constant `K`: the zero test and `K`'s pivot pattern. -/
theorem oclassifier_run (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire)
    (hxs : xs.Nodup) (hlen : xs.length = 256) (hwl : work.length = 253) (hwn : work.Nodup)
    (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ xs ∧ q ∉ work)
    (s : State) (m : List Bool)
    (hz : (∀ q ∈ work, s.basis q = false) ∧ s.basis f = false ∧ s.basis t1 = false ∧
      s.basis t2 = false ∧ s.basis u = false)
    (hfl : s.basis g = (s.basis c && oX tr tr.S xs s.basis) ∧
      s.basis O = (s.basis c && oX tr tr.A xs s.basis && (s.basis y0 == yc)) ∧
      s.basis D = (s.basis c && oX tr tr.B xs s.basis && (s.basis y0 == y2c)) ∧
      s.basis H = (e && s.basis c && oX tr tr.A xs s.basis && (s.basis y0 != yc))) :
    run (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) m s =
      ⟨s.phase, writeBit (writeBit (writeBit (writeBit (writeBit s.basis f (!oX tr tr.S xs s.basis))
        g false) O false) D false) H false⟩ := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  set w : Nat → Wire := fun i => xs.getD i 0 with hw
  set xr1 := w tr.r1 with hx1
  set xr2 := w tr.r2 with hx2
  set P := tr.idx.map w with hP
  have winj : ∀ i j, i < 256 → j < 256 → w i = w j → i = j := by
    intro i j hi hj heq
    simp only [hw] at heq
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
    exact hxs.getElem_inj_iff.mp heq
  have wmem : ∀ i, i < 256 → w i ∈ xs := by
    intro i hi; simp only [hw]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hPn : P.Nodup := by
    apply List.Nodup.map_on _ ix.1
    intro i hi j hj heq; exact winj i j (ix.2.2.2.2 i hi) (ix.2.2.2.2 j hj) heq
  have memP : ∀ q, q ∈ P ↔ ∃ i ∈ tr.idx, w i = q := by intro q; simp [hP]
  have x1P : xr1 ∉ P := by
    rw [memP]; rintro ⟨i, hi, heq⟩
    exact ix.2.2.1 (winj i tr.r1 (ix.2.2.2.2 i hi) pv.1 heq ▸ hi)
  have x2P : xr2 ∉ P := by
    rw [memP]; rintro ⟨i, hi, heq⟩
    exact ix.2.2.2.1 (winj i tr.r2 (ix.2.2.2.2 i hi) pv.2.1 heq ▸ hi)
  have x12 : xr1 ≠ xr2 := fun heq => pv.2.2.1 (winj _ _ pv.1 pv.2.1 heq)
  have Psub : ∀ q ∈ P, q ∈ xs := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := (memP q).mp hq; exact wmem i (ix.2.2.2.2 i hi)
  have hPl : P.length = 254 := by simp [hP, ix.2.1]
  obtain ⟨i0, it, hidx⟩ : ∃ i0 it, tr.idx = i0 :: it := by
    have hl := ix.2.1
    cases h : tr.idx with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact ⟨a, l, rfl⟩
  have hP0 : P = w i0 :: it.map w := by simp [hP, hidx]
  have hitl : (it.map w).length = 253 := by
    have := hPl; rw [hP0] at this; simpa using this
  have extx (q : Wire) (hq : q ∈ [y0, c, f, g, O, D, H, t1, t2, u]) :
      q ∉ P ∧ q ∉ work ∧ q ≠ xr1 ∧ q ≠ xr2 := by
    have h := hextx q hq
    exact ⟨fun hp => h.1 (Psub q hp), h.2, fun heq => h.1 (heq ▸ wmem _ pv.1),
      fun heq => h.1 (heq ▸ wmem _ pv.2.1)⟩
  have hused : [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u].Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hext⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨x12, ?_⟩
      have := fun q hq => (extx q hq).2.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      exact ⟨fun heq => this y0 (Or.inl rfl) heq.symm, fun heq => this c (by tauto) heq.symm,
        fun heq => this f (by tauto) heq.symm, fun heq => this g (by tauto) heq.symm,
        fun heq => this O (by tauto) heq.symm, fun heq => this D (by tauto) heq.symm,
        fun heq => this H (by tauto) heq.symm, fun heq => this t1 (by tauto) heq.symm,
        fun heq => this t2 (by tauto) heq.symm, fun heq => this u (by tauto) heq.symm⟩
    · intro hm
      exact (extx xr2 hm).2.2.2 rfl
  have hlP : (i0 :: it).map w = P := by rw [hP0]; rfl
  have hPn' : ((i0 :: it).map w).Nodup := by rw [hlP]; exact hPn
  have x1P' : xr1 ∉ (i0 :: it).map w := by rw [hlP]; exact x1P
  have x2P' : xr2 ∉ (i0 :: it).map w := by rw [hlP]; exact x2P
  have hextP : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ (i0 :: it).map w := by
    intro q hq; rw [hlP]; exact (extx q hq).1
  have hdisj' : ∀ q ∈ work, q ∉ (i0 :: it).map w ∧ q ∉ [xr1, xr2, y0, c, f, g, O, D, H, t1, t2, u] := by
    intro q hq
    refine ⟨fun hm => hdisj q hq (Psub q (by rw [← hlP]; exact hm)), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (heq | heq | heq)
    · exact hdisj q hq (heq ▸ wmem _ pv.1)
    · exact hdisj q hq (heq ▸ wmem _ pv.2.1)
    · exact (hextx q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)).2 hq
  have hmb : matchBit tr xs s.basis =
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) := by
    simp only [matchBit, hidx]; rfl
  have hoX : ∀ K, oX tr K xs s.basis = tX tr K
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2))
      (s.basis xr1) (s.basis xr2) := by
    intro K; simp only [oX, tX, ← hmb]; rfl
  have hp : otailPre tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u
      ((i0 :: it).all fun i => s.basis (w i) == tr.tgt i (s.basis xr1, s.basis xr2)) s.basis := by
    unfold otailPre
    rw [← hoX, ← hoX, ← hoX]
    exact ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2, hfl.1, hfl.2.1, hfl.2.2.1, hfl.2.2.2⟩
  have run_eq := oshape_run tr v yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u w i0 it work hPn' x1P' x2P' hused
    hextP (by rw [hitl, hwl]) hwn hdisj' s m hz.1 hp
  have hprog : oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u =
      tr.remapList xr1 xr2 w (i0 :: it) ++ ([.X (w i0)] ++
      (zeroWith (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u) (w i0) (zeroPorts (it.map w) work) ++
      ([.X (w i0)] ++ tr.remapList xr1 xr2 w (i0 :: it)))) := by
    simp only [oclassifier, hidx, List.map_cons, List.headD_cons, List.tail_cons]; rfl
  rw [hprog, run_eq]
  unfold otailEff
  rw [← hoX]

/-! ### Counts, slots, support and physical gates of the output classifier -/

theorem oclassifier_counts (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hwl : work.length = 253) :
    toffoliCount (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) = 253 + (if e then 3 else 5) ∧
    measurementCount (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) = 253 + 8 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zc := zeroWith_counts_general
    (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u) (if e then 3 else 5) 8
    (fun h => otailL_counts tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zc
  have rt := remapList_tc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  have rm := remapList_mc tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  unfold oclassifier
  simp only [toffoliCount_append, measurementCount_append, rt, rm, zc.1, zc.2]
  exact ⟨by simp [toffoliCount], by simp [measurementCount]⟩

/-- 3 slots a remapped bit twice, the two flips, 7 a chain rung, and the 45-slot worst output tail. -/
theorem oclassifier_slots (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hwl : work.length = 253) :
    gateSlots (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ≤ 3342 := by
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have ix := Tri.idx_facts v
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have hbl : (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work).length = 253 := by
    have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by
      rw [hidx]; rfl
    rw [hPt]
    have := congrArg List.length zp.2
    simpa [hwl] using this
  have zs := zeroWith_slots (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
    (gateSlots (otail tr yc y2c e)) (fun h => otailL_slots tr yc y2c e _ _ y0 c f g O D H t1 t2 u h)
    ((tr.idx.map (fun i => xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)
  rw [hbl] at zs
  have rs := remapList_slots tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx
  rw [ix.2.1] at rs
  have ds := otail_slots tr yc y2c e
  unfold oclassifier
  simp only [gateSlots_app, zs]
  simp only [gateSlots, instructionSlots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at rs ds ⊢
  omega

theorem oclassifier_support (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hxl : xs.length = 256) (hwl : work.length = 253) :
    wires (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ⊆
      xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, O, D, H, t1, t2, u} := by
  have _ := hwl
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  let U : Finset Wire := xs.toFinset ∪ work.toFinset ∪ {y0, c, f, g, O, D, H, t1, t2, u}
  have xsU : ∀ i, i < 256 → xs.getD i 0 ∈ U := by
    intro i hi
    have hm : xs.getD i 0 ∈ xs := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    simp only [U, Finset.mem_union, List.mem_toFinset]
    exact Or.inl (Or.inl hm)
  have workU : ∀ q ∈ work, q ∈ U := fun q hq => by simp [U, hq]
  have r1U := xsU _ pv.1
  have r2U := xsU _ pv.2.1
  have idxU : ∀ i ∈ tr.idx, xs.getD i 0 ∈ U := fun i hi => xsU i (ix.2.2.2.2 i hi)
  have PU : ∀ q ∈ tr.idx.map (fun i => xs.getD i 0), q ∈ U := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; exact idxU i hi
  have h0U : (tr.idx.map (fun i => xs.getD i 0)).headD 0 ∈ U := by
    rw [hidx]; exact idxU i0 (by rw [hidx]; simp)
  have portsU : ∀ b ∈ zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work,
      b.input ∈ U ∧ b.work ∈ U := by
    intro b hb
    have hm := zeroPorts_mem _ _ b hb
    exact ⟨PU _ (List.mem_of_mem_tail hm.1), workU _ hm.2⟩
  have extU : ∀ q ∈ ({y0, c, f, g, O, D, H, t1, t2, u} : Finset Wire), q ∈ U := by
    intro q hq; simp only [U, Finset.mem_union]; exact Or.inr hq
  have tailU : ∀ h ∈ U,
      wires (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u h) ⊆ U := by
    intro h hh
    refine (otailL_support tr yc y2c e _ _ y0 c f g O D H t1 t2 u h).trans ?_
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hh, r1U, r2U, extU y0 (by simp), extU c (by simp), extU f (by simp), extU g (by simp),
      extU O (by simp), extU D (by simp), extU H (by simp), extU t1 (by simp), extU t2 (by simp),
      extU u (by simp)⟩
  have remapU := remapList_sub tr (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx U
    r1U r2U idxU
  have zU := zeroWith_sub _ U tailU _ _ h0U portsU
  have xU : wires [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] ⊆ U := by
    generalize (tr.idx.map (fun i => xs.getD i 0)).headD 0 = h0 at h0U ⊢
    intro q hq
    simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_singleton] at hq
    rcases hq with rfl | hq
    · exact h0U
    · simp at hq
  intro q hq
  simp only [oclassifier, wires_append, Finset.mem_union] at hq
  rcases hq with h | h | h | h | h
  · exact remapU h
  · exact xU h
  · exact zU h
  · exact xU h
  · exact remapU h

theorem oclassifier_physical (tr : Tri) (v : tr.Valid) (yc y2c e : Bool) (xs work : List Wire)
    (y0 c f g O D H t1 t2 u : Wire) (hxl : xs.length = 256) (hwl : work.length = 253)
    (hxn : xs.Nodup) (hwn : work.Nodup) (hdisj : ∀ q ∈ work, q ∉ xs)
    (hext : [y0, c, f, g, O, D, H, t1, t2, u].Nodup)
    (hextx : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], q ∉ xs ∧ q ∉ work) :
    GatePhysical (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) := by
  have pv := Tri.pivots v
  have ix := Tri.idx_facts v
  obtain ⟨i0, it, hidx, hitl⟩ := idx_split tr v
  have winj : ∀ i j, i < 256 → j < 256 → xs.getD i 0 = xs.getD j 0 → i = j := by
    intro i j hi hj heq
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
    exact hxn.getElem_inj_iff.mp heq
  have wmem : ∀ i, i < 256 → xs.getD i 0 ∈ xs := by
    intro i hi; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hi0 : i0 ∈ tr.idx := by rw [hidx]; simp
  have i0lt := ix.2.2.2.2 i0 hi0
  have i0r1 : i0 ≠ tr.r1 := fun heq => ix.2.2.1 (heq ▸ hi0)
  have i0r2 : i0 ≠ tr.r2 := fun heq => ix.2.2.2.1 (heq ▸ hi0)
  have zp := zeroPorts_maps (it.map (fun i => xs.getD i 0)) work (by simp [hitl, hwl])
  have remapP : GatePhysical (tr.remapList (xs.getD tr.r1 0) (xs.getD tr.r2 0) (fun i => xs.getD i 0) tr.idx) := by
    apply remapList_physical
    intro i hi
    have hi256 := ix.2.2.2.2 i hi
    refine ⟨fun heq => ix.2.2.1 ((winj _ _ pv.1 hi256 heq) ▸ hi), fun heq => ix.2.2.2.1 ((winj _ _ pv.2.1 hi256 heq) ▸ hi)⟩
  have hP0 : (tr.idx.map (fun i => xs.getD i 0)).headD 0 = xs.getD i0 0 := by rw [hidx]; rfl
  have hPt : (tr.idx.map (fun i => xs.getD i 0)).tail = it.map (fun i => xs.getD i 0) := by rw [hidx]; rfl
  have x0x : xs.getD i0 0 ∈ xs := wmem i0 i0lt
  have ex : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], ∀ a ∈ xs, a ≠ q :=
    fun q hq a ha heq => (hextx q hq).1 (heq ▸ ha)
  have ew : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], ∀ a ∈ work, a ≠ q :=
    fun q hq a ha heq => (hextx q hq).2 (heq ▸ ha)
  -- any chain wire (the control `xs[i0]` or a pool wire) together with the tail's other twelve wires is nodup
  have hlist : ∀ h, (h = xs.getD i0 0 ∨ h ∈ work) →
      [h, xs.getD tr.r1 0, xs.getD tr.r2 0, y0, c, f, g, O, D, H, t1, t2, u].Nodup := by
    intro h hh
    have hx1 := wmem _ pv.1
    have hx2 := wmem _ pv.2.1
    have hxx : xs.getD tr.r1 0 ≠ xs.getD tr.r2 0 := fun heq => pv.2.2.1 (winj _ _ pv.1 pv.2.1 heq)
    have hh1 : h ≠ xs.getD tr.r1 0 := by
      rcases hh with rfl | hw
      · exact fun heq => i0r1 (winj _ _ i0lt pv.1 heq)
      · exact fun heq => hdisj h hw (heq ▸ hx1)
    have hh2 : h ≠ xs.getD tr.r2 0 := by
      rcases hh with rfl | hw
      · exact fun heq => i0r2 (winj _ _ i0lt pv.2.1 heq)
      · exact fun heq => hdisj h hw (heq ▸ hx2)
    have hhe : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], h ≠ q := by
      intro q hq
      rcases hh with rfl | hw
      · exact ex q hq _ x0x
      · exact ew q hq _ hw
    have r1e : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], xs.getD tr.r1 0 ≠ q := fun q hq => ex q hq _ hx1
    have r2e : ∀ q ∈ [y0, c, f, g, O, D, H, t1, t2, u], xs.getD tr.r2 0 ≠ q := fun q hq => ex q hq _ hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hhe r1e r2e
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hh1, hh2, hhe⟩, ⟨hxx, r1e⟩, r2e, ?_⟩
    simpa using hext
  have zP : GatePhysical (zeroWith (otailL tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
      ((tr.idx.map (fun i => xs.getD i 0)).headD 0)
      (zeroPorts (tr.idx.map (fun i => xs.getD i 0)).tail work)) := by
    rw [hP0, hPt]
    apply zeroWith_physical
    · rw [zp.2]
      exact List.nodup_cons.mpr ⟨fun hm => hdisj _ hm x0x, hwn⟩
    · intro b hb heq
      have hm := zeroPorts_mem _ _ b hb
      obtain ⟨i, hi, hie⟩ := List.mem_map.mp hm.1
      have hit : i ∈ tr.idx := by rw [hidx]; simp [hi]
      exact hdisj _ hm.2 (heq ▸ hie ▸ wmem i (ix.2.2.2.2 i hit))
    · intro h hh
      rw [zp.2] at hh
      apply otailL_physical
      exact hlist h (by simpa using hh)
  have xP : GatePhysical [Instr.X ((tr.idx.map (fun i => xs.getD i 0)).headD 0)] := by
    simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]
  unfold oclassifier
  simp only [gatePhysical_append]
  exact ⟨remapP, xP, zP, xP, remapP⟩

def outStage (L : ControlledPointLayout) (C : Point) : Program :=
  predecL (triOf C) (yBit C) L.genericSelect L.control (L.point.x.getD (triOf C).r1 0)
    (L.point.x.getD (triOf C).r2 0) (yLow L) (parkWire L) L.doubleSelect L.core.equalNegY ++
  ocorners L C ++
  oclassifier (triOf C) (yBit C) (yBit (C + C)) (exceptionBit C) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect (parkWire L) L.doubleSelect L.core.equalNegY
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0) ++
  FiniteFlagInterval.zrep L

open Classical in
theorem outStage_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s0 : State) (hs : PointDialogBoundary layout R b (fun _ => false) s0.basis) (t : State) (m : List Bool)
    (htx : regValue layout.point.x t.basis =
      codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (hty : regValue layout.point.y t.basis =
      pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R))
    (htf : t.basis layout.point.finite = false)
    (htg : t.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (htr : ∀ q, q ∉ layout.point.x → q ∉ layout.point.y → q ≠ layout.point.finite →
      q ≠ layout.genericSelect → t.basis q = s0.basis q) :
    (run (outStage layout (.some hc)) m t).phase = t.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (outStage layout (.some hc)) m t).basis := by
  set C : Point := .some hc with hCdef
  have hC : C ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hnC : -C ≠ 0 := neg_ne_zero.mpr hC
  have hCn : C ≠ -C := (doubling_enabled_iff hc).mp (of_decide_eq_true (cy_ne_neg hc))
  have h2C : C + C ≠ 0 := fun e => hCn (eq_neg_of_add_eq_zero_left e)
  have v : (triOf C).Valid := triOf_valid hc
  have pv := Tri.pivots v
  obtain ⟨fx6n, fx6x, fx10n, fx10x, parkP, parkY, p253, p254, p255⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  set xr1 := layout.point.x.getD (triOf C).r1 0 with hxr1
  set xr2 := layout.point.x.getD (triOf C).r2 0 with hxr2
  have x1m : xr1 ∈ layout.point.x := by
    rw [hxr1, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x2m : xr2 ∈ layout.point.x := by
    rw [hxr2, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have x12 : xr1 ≠ xr2 := by
    intro e
    rw [hxr1, hxr2, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    exact pv.2.2.1 ((List.Nodup.getElem_inj_iff hxn).mp e)
  have hnd8 : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
      layout.doubleSelect, layout.core.equalNegY].Nodup := by
    have hperm : [layout.genericSelect, layout.control, xr1, xr2, yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY].Perm
        ([xr1, xr2] ++ [layout.genericSelect, layout.control, yLow layout, parkWire layout,
          layout.doubleSelect, layout.core.equalNegY]) := by
      show (([layout.genericSelect, layout.control] ++ [xr1, xr2]) ++ [yLow layout, parkWire layout,
        layout.doubleSelect, layout.core.equalNegY]).Perm
        (([xr1, xr2] ++ [layout.genericSelect, layout.control]) ++ [yLow layout, parkWire layout,
          layout.doubleSelect, layout.core.equalNegY])
      exact List.perm_append_comm.append_right _
    apply hperm.nodup_iff.mpr
    rw [List.nodup_append]
    refine ⟨by simp [x12], fx6n, ?_⟩
    intro a ha b hb e
    subst e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact fx6x _ hb x1m
    · exact fx6x _ hb x2m
  -- reads of the post-generic state
  have off (q : Wire) (hq : q ∈ [layout.control, layout.infinitySelect, layout.doubleSelect, layout.core.generic,
      layout.core.equalX, layout.core.equalNegY, layout.core.double, parkWire layout]) :
      t.basis q = s0.basis q := by
    obtain ⟨a, b', c, d⟩ := out_off q hq
    exact htr q a b' c d
  have flag0 (q : Wire) (hq : q ∈ layout.inPlaceFlags) : s0.basis q = false := hs.flags q hq
  have pool0 (q : Wire) (hq : q ∈ layout.dialogPool) : s0.basis q = false :=
    (regValue_zero _ _).mp hs.clean q hq
  have tpool (q : Wire) (hq : q ∈ layout.dialogPool) : t.basis q = false := by
    obtain ⟨a, b', -, -, -⟩ := out_pool_off q hq
    rw [htr q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) a b']
    exact pool0 q hq
  have hb0 : t.basis layout.control = b := by rw [off _ (by simp)]; exact hs.control
  have hz1 : t.basis (parkWire layout) = false ∧ t.basis layout.doubleSelect = false ∧
      t.basis layout.core.equalNegY = false := by
    refine ⟨tpool _ parkP, ?_, ?_⟩
    · rw [off _ (by simp)]; exact flag0 _ (by simp [flags_list])
    · rw [off _ (by simp)]; exact flag0 _ (by simp [flags_list])
  have hx1v : t.basis xr1 = (codeX (if dialogOrdinary b R C then R + C else R)).testBit (triOf C).r1 := by
    rw [← htx, LocalWireModel.reg_bit _ _ _ (by omega)]
  have hx2v : t.basis xr2 = (codeX (if dialogOrdinary b R C then R + C else R)).testBit (triOf C).r2 := by
    rw [← htx, LocalWireModel.reg_bit _ _ _ (by omega)]
  have hy0v : t.basis (yLow layout) = yBit (if dialogOrdinary b R C then R + C else R) := by
    rw [yLow_bit t.basis, hty, pointY_bit0]
  have pfv : predFlags (triOf C) (yBit C) (t.basis layout.genericSelect ^^ t.basis layout.control)
      (t.basis xr1) (t.basis xr2) (t.basis (yLow layout)) =
      (dialogInfinity b R, dialogDouble b R C, dialogException b R C, dialogInversePoint b R C) := by
    rw [htg, hb0, hx1v, hx2v, hy0v]; exact predFlags_dialog hc b R
  unfold outStage
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat, LocalWireModel.run_concat,
    predecL_run (triOf C) (yBit C) _ _ _ _ _ _ _ _ hnd8 t m hz1, pfv]
  -- stage 2: corners
  generalize ht1 : (⟨t.phase, writeBit (writeBit (writeBit (writeBit t.basis layout.genericSelect
    (dialogInversePoint b R C)) (parkWire layout) (dialogInfinity b R)) layout.doubleSelect
    (dialogDouble b R C)) layout.core.equalNegY (dialogException b R C)⟩ : State) = t1
  obtain ⟨gp, gd, gh, pd, ph, dh⟩ := out_ne
  have t1off (q : Wire) (h1 : q ≠ layout.genericSelect) (h2 : q ≠ parkWire layout) (h3 : q ≠ layout.doubleSelect)
      (h4 : q ≠ layout.core.equalNegY) : t1.basis q = t.basis q := by
    rw [← ht1]; simp [writeBit, Function.update, h1, h2, h3, h4]
  have t1g : t1.basis layout.genericSelect = dialogInversePoint b R C := by
    rw [← ht1]; simp [writeBit, Function.update, gp, gd, gh]
  have t1p : t1.basis (parkWire layout) = dialogInfinity b R := by
    rw [← ht1]; simp [writeBit, Function.update, pd, ph]
  have t1d : t1.basis layout.doubleSelect = dialogDouble b R C := by
    rw [← ht1]; simp [writeBit, Function.update, dh]
  have t1h : t1.basis layout.core.equalNegY = dialogException b R C := by
    rw [← ht1]; simp [writeBit, Function.update]
  have t1ph : t1.phase = t.phase := by rw [← ht1]
  have notw (q : Wire) (hq : q ∈ layout.point.x ++ layout.point.y) :
      q ≠ layout.genericSelect ∧ q ≠ parkWire layout ∧ q ≠ layout.doubleSelect ∧ q ≠ layout.core.equalNegY := by
    refine ⟨fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq), fun e => pool_not_point _ parkP (e ▸ hq),
      fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq), fun e => flags_not_point _ (by simp [flags_list]) (e ▸ hq)⟩
  have t1x : regValue layout.point.x t1.basis = regValue layout.point.x t.basis := by
    apply regValue_congr; intro q hq
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_left _ hq)
    exact t1off q a b' c d
  have t1y : regValue layout.point.y t1.basis = regValue layout.point.y t.basis := by
    apply regValue_congr; intro q hq
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_right _ hq)
    exact t1off q a b' c d
  -- stage 2: corners
  obtain ⟨c1, c2, c3, c4⟩ := ocorners_run layout layout_widths layout_nodup C t1
    (List.drop (measurementCount (predecL (triOf C) (yBit C) layout.genericSelect layout.control xr1 xr2
      (yLow layout) (parkWire layout) layout.doubleSelect layout.core.equalNegY)) m)
  generalize ht2 : run (ocorners layout C) (List.drop (measurementCount (predecL (triOf C) (yBit C)
    layout.genericSelect layout.control xr1 xr2 (yLow layout) (parkWire layout) layout.doubleSelect
    layout.core.equalNegY)) m) t1 = t2 at c1 c2 c3 c4 ⊢
  have cv := corners_value hc b R
  rw [t1x, htx, t1p, t1d, t1g, t1h, cv.1] at c2
  rw [t1y, hty, t1p, t1d, t1g, t1h, cv.2] at c3
  set S := if b then R + C else R with hSdef
  have t2off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) : t2.basis q = t1.basis q := c4 q hx hy
  have offxy (q : Wire) (hq : q ∈ layout.dialogPool) : q ∉ layout.point.x ∧ q ∉ layout.point.y :=
    ⟨fun h => pool_not_point q hq (List.mem_append_left _ h), fun h => pool_not_point q hq (List.mem_append_right _ h)⟩
  have flxy (q : Wire) (hq : q ∈ layout.inPlaceFlags) : q ∉ layout.point.x ∧ q ∉ layout.point.y :=
    ⟨fun h => flags_not_point q hq (List.mem_append_left _ h), fun h => flags_not_point q hq (List.mem_append_right _ h)⟩
  have t2pool (q : Wire) (hq : q ∈ layout.dialogPool) (hp : q ≠ parkWire layout) : t2.basis q = false := by
    obtain ⟨a, b'⟩ := offxy q hq
    obtain ⟨-, g1, d1, h1, -⟩ := out_pool_off q hq
    rw [t2off q a b', t1off q g1 hp d1 h1]; exact tpool q hq
  have t2ctl : t2.basis layout.control = b := by
    obtain ⟨a, b', -, -⟩ := out_off layout.control (by simp)
    rw [t2off _ a b', t1off _ (by decide) (by decide) (by decide) (by decide)]; exact hb0
  have t2f : t2.basis layout.point.finite = false := by
    have hfx := finite_not_flag.2
    rw [t2off _ (fun h => hfx (List.mem_append_left _ h)) (fun h => hfx (List.mem_append_right _ h)),
      t1off _ (by decide) (by decide) (by decide) (by decide)]; exact htf
  have t2y0 : t2.basis (yLow layout) = yBit S := by rw [yLow_bit t2.basis, c3, pointY_bit0]
  have gF := flxy layout.genericSelect (by simp [flags_list])
  have dF := flxy layout.doubleSelect (by simp [flags_list])
  have hF := flxy layout.core.equalNegY (by simp [flags_list])
  have pF := offxy (parkWire layout) parkP
  have t2g : t2.basis layout.genericSelect = dialogInversePoint b R C := by rw [t2off _ gF.1 gF.2, t1g]
  have t2p : t2.basis (parkWire layout) = dialogInfinity b R := by rw [t2off _ pF.1 pF.2, t1p]
  have t2d : t2.basis layout.doubleSelect = dialogDouble b R C := by rw [t2off _ dF.1 dF.2, t1d]
  have t2h : t2.basis layout.core.equalNegY = dialogException b R C := by rw [t2off _ hF.1 hF.2, t1h]
  -- the match bits on the output abscissa
  have oS : oX (triOf C) (triOf C).S layout.point.x t2.basis = decide (S = 0) := by
    rw [oX_eq _ v _ hxl _ _ v.hS (Tri.tgt_S v), c2]
    exact decide_eq_decide.mpr (code_sentinel S)
  have oA : oX (triOf C) (triOf C).A layout.point.x t2.basis = decide (codeX S = pointX C) := by
    rw [oX_eq _ v _ hxl _ _ v.hA (Tri.tgt_A), c2]; rfl
  have oB : oX (triOf C) (triOf C).B layout.point.x t2.basis = decide (codeX S = pointX (C + C)) := by
    rw [oX_eq _ v _ hxl _ _ v.hB (Tri.tgt_B v), c2]
    have e : (triOf C).B = pointX (C + C) := by
      show pointX (dialogExceptionPoint C) = _
      unfold dialogExceptionPoint; exact DHClass.pointX_neg _
    rw [e]
  have fo := dialogFlags_output b R C
  dsimp only at fo
  have hwl' : (layout.dialogPool.take 253).length = 253 := hwl
  have hfl : t2.basis layout.genericSelect = (t2.basis layout.control && oX (triOf C) (triOf C).S layout.point.x t2.basis) ∧
      t2.basis (parkWire layout) = (t2.basis layout.control && oX (triOf C) (triOf C).A layout.point.x t2.basis &&
        (t2.basis (yLow layout) == yBit C)) ∧
      t2.basis layout.doubleSelect = (t2.basis layout.control && oX (triOf C) (triOf C).B layout.point.x t2.basis &&
        (t2.basis (yLow layout) == yBit (C + C))) ∧
      t2.basis layout.core.equalNegY = (exceptionBit C && t2.basis layout.control &&
        oX (triOf C) (triOf C).A layout.point.x t2.basis && (t2.basis (yLow layout) != yBit C)) := by
    rw [t2g, t2p, t2d, t2h, t2ctl, oS, oA, oB, t2y0]
    have bmC := bool_match S C hC
    have bm2 := bool_match S (C + C) h2C
    have bmN := bool_match S (-C) hnC
    have e1 : (yBit S != yBit C) = (yBit S == yBit (-C)) := by
      rw [yBit_neg hc]; cases yBit S <;> cases yBit (.some hc : Point) <;> rfl
    have e2 : pointX C = pointX (-C) := (DHClass.pointX_neg C).symm
    have hdec : decide (C ≠ -C) = true := decide_eq_true hCn
    refine ⟨fo.2.2.1.symm, ?_, ?_, ?_⟩
    · rw [← fo.1, Bool.and_assoc, bmC]
    · rw [← fo.2.1, hdec, Bool.and_true, Bool.and_assoc, bm2]
    · rw [← fo.2.2.2, e1, e2, exc_bit]
      by_cases hen : dialogExceptionEnabled C
      · have h1 : decide (dialogExceptionEnabled C) = true := decide_eq_true hen
        have h2 : decide (dialogExceptionPoint C ≠ 0 ∧ dialogExceptionPoint C ≠ C ∧
            dialogExceptionPoint C ≠ -C) = true := decide_eq_true hen
        rw [h1, h2, Bool.and_true, Bool.true_and, Bool.and_assoc, bmN]
      · have h1 : decide (dialogExceptionEnabled C) = false := decide_eq_false hen
        have h2 : decide (dialogExceptionPoint C ≠ 0 ∧ dialogExceptionPoint C ≠ C ∧
            dialogExceptionPoint C ≠ -C) = false := decide_eq_false hen
        rw [h1, h2]; simp
  rw [oclassifier_run (triOf C) v (yBit C) (yBit (C + C)) (exceptionBit C) layout.point.x
    (layout.dialogPool.take 253) (yLow layout) layout.control layout.point.finite layout.genericSelect
    (parkWire layout) layout.doubleSelect layout.core.equalNegY (layout.dialogPool.getD 253 0)
    (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0) hxn hxl hwl' hwn hdisj fx10n fx10x t2 _
    ⟨fun q hq => t2pool q (List.mem_of_mem_take hq) (fun e => (fx10x _ (by simp)).2 (e ▸ hq)), t2f,
      t2pool _ p253 (by decide), t2pool _ p254 (by decide), t2pool _ p255 (by decide)⟩ hfl]
  rw [oS]
  -- stage 4: back to the plain abscissa
  generalize ht3 : (⟨t2.phase, writeBit (writeBit (writeBit (writeBit (writeBit t2.basis layout.point.finite
    (!decide (S = 0))) layout.genericSelect false) (parkWire layout) false) layout.doubleSelect false)
    layout.core.equalNegY false⟩ : State) = t3
  have t3ph : t3.phase = t.phase := by rw [← ht3]; show t2.phase = t.phase; rw [c1, t1ph]
  have t3off (q : Wire) (h0 : q ≠ layout.point.finite) (h1 : q ≠ layout.genericSelect) (h2 : q ≠ parkWire layout)
      (h3 : q ≠ layout.doubleSelect) (h4 : q ≠ layout.core.equalNegY) : t3.basis q = t2.basis q := by
    rw [← ht3]; simp [writeBit, Function.update, h0, h1, h2, h3, h4]
  have fG : layout.point.finite ≠ layout.genericSelect := (gsel_off.2.2).symm
  have fP : layout.point.finite ≠ parkWire layout := fun e => (out_pool_off _ parkP).1 e.symm
  have fD : layout.point.finite ≠ layout.doubleSelect :=
    fun e => finite_not_flag.1 (e ▸ (by simp [flags_list] : layout.doubleSelect ∈ layout.inPlaceFlags))
  have fH : layout.point.finite ≠ layout.core.equalNegY :=
    fun e => finite_not_flag.1 (e ▸ (by simp [flags_list] : layout.core.equalNegY ∈ layout.inPlaceFlags))
  have t3f : t3.basis layout.point.finite = !decide (S = 0) := by
    rw [← ht3]; simp [writeBit, Function.update, fG, fP, fD, fH]
  have t3x : regValue layout.point.x t3.basis = codeX S := by
    rw [← c2]; apply regValue_congr; intro q hq
    have hf : q ≠ layout.point.finite := fun e => finite_not_flag.2 (e ▸ List.mem_append_left _ hq)
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_left _ hq)
    exact t3off q hf a b' c d
  have t3y : regValue layout.point.y t3.basis = pointY S := by
    rw [← c3]; apply regValue_congr; intro q hq
    have hf : q ≠ layout.point.finite := fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)
    obtain ⟨a, b', c, d⟩ := notw q (List.mem_append_right _ hq)
    exact t3off q hf a b' c d
  suffices key : ∀ mm, (run (FiniteFlagInterval.zrep layout) mm t3).phase = t.phase ∧
      PointDialogBoundary layout S b (fun _ => false) (run (FiniteFlagInterval.zrep layout) mm t3).basis by
    exact key _
  intro mm
  obtain ⟨z1, z2, z3⟩ := FiniteFlagInterval.zrep_run layout layout_widths layout_nodup t3 mm
  generalize run (FiniteFlagInterval.zrep layout) mm t3 = t4 at z1 z2 z3 ⊢
  have fx : layout.point.finite ∉ layout.point.x := fun h => finite_not_flag.2 (List.mem_append_left _ h)
  refine ⟨by rw [z1, t3ph], ?_, ?_, ?_, ?_⟩
  · apply (point_holds _ _ _).mpr
    refine ⟨by rw [z2 _ fx, t3f, finite_dec], by rw [z3, t3x, t3f, code_back], ?_⟩
    rw [← t3y]; apply regValue_congr; intro q hq
    exact z2 q (y_not_x layout layout_nodup q hq)
  · obtain ⟨a, -, c, d⟩ := out_off layout.control (by simp)
    rw [z2 _ a, t3off _ c.symm.symm (by decide) (by decide) (by decide) (by decide)]
    · exact t2ctl
  · intro q hq
    rw [z2 q (flags_not_point q hq ∘ List.mem_append_left _)]
    rw [flags_list] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨a, b', c, d⟩ := out_off layout.infinitySelect (by simp)
      rw [t3off _ c (by decide) (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ (by decide) (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · rw [← ht3]; simp [writeBit, Function.update, dh]
    · rw [← ht3]; simp [writeBit, Function.update, gp, gd, gh]
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.generic (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.equalX (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
    · rw [← ht3]; simp [writeBit, Function.update]
    · obtain ⟨a, b', c, d⟩ := out_off layout.core.double (by simp)
      rw [t3off _ c d (by decide) (by decide) (by decide), t2off _ a b',
        t1off _ d (by decide) (by decide) (by decide), off _ (by simp)]
      exact flag0 _ (by simp [flags_list])
  · apply (regValue_zero _ _).mpr
    intro q hq
    rw [z2 q (fun h => pool_not_point q hq (List.mem_append_left _ h))]
    by_cases hp : q = parkWire layout
    · subst hp; rw [← ht3]; simp [writeBit, Function.update, pd, ph]
    · obtain ⟨f1, g1, d1, h1, -⟩ := out_pool_off q hq
      rw [t3off q f1 g1 hp d1 h1]
      exact t2pool q hq hp

end ECDSAAdd.Entrant.OutputOpt
end

-- Consolidated output proof: OutputResources
section
namespace ECDSAAdd.Entrant.OutputOpt
open Arithmetic Challenge RecordedQuantum MeasuredCodec5 Baselines InputSentinel Secp256k1 ControlledPointLayout
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] outStage InputSentinel.outStage GatePhysical wires toffoliCount measurementCount gateSlots

theorem otail_subset (tr:Tri) (yc y2c e:Bool) :
    wires (otail tr yc y2c e)⊆wires (InputSentinel.otail tr yc y2c e) := by
  unfold otail InputSentinel.otail
  split_ifs
  · exact otail1_subset _ _ _ _ _ _
  · exact otail2_subset _ _ _ _ _ _

theorem otail_metrics (tr:Tri) (yc y2c e:Bool) :
    toffoliCount (otail tr yc y2c e)+(if e then 1 else 0)=toffoliCount (InputSentinel.otail tr yc y2c e) ∧
    measurementCount (otail tr yc y2c e)=measurementCount (InputSentinel.otail tr yc y2c e) ∧
    gateSlots (otail tr yc y2c e)≤gateSlots (InputSentinel.otail tr yc y2c e)+12 := by
  have n:=otail_counts' tr yc y2c e
  have o:=InputSentinel.otail_counts' tr yc y2c e
  have sl:gateSlots (otail tr yc y2c e)≤gateSlots (InputSentinel.otail tr yc y2c e)+12:=by
    unfold otail InputSentinel.otail
    split_ifs
    · exact otail1_slots_delta _ _ _ _ _ _
    · exact otail2_slots_delta _ _ _ _ _ _
  cases e <;> simp only [Bool.false_eq_true,ite_false,ite_true] at n o ⊢ <;> omega

theorem tailL_subset (tr:Tri) (yc y2c e:Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h:Wire) :
    wires (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h)⊆
      wires (InputSentinel.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) := by
  simp only [otailL,InputSentinel.otailL,renameProgram_support]
  exact Finset.image_subset_image (otail_subset tr yc y2c e)

theorem tailL_metrics (tr:Tri) (yc y2c e:Bool) (xr1 xr2 y0 c f g O D H t1 t2 u h:Wire) :
    toffoliCount (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h)+(if e then 1 else 0)=
      toffoliCount (InputSentinel.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) ∧
    measurementCount (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h)=
      measurementCount (InputSentinel.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h) ∧
    gateSlots (otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h)≤
      gateSlots (InputSentinel.otailL tr yc y2c e xr1 xr2 y0 c f g O D H t1 t2 u h)+12 := by
  simpa only [otailL,InputSentinel.otailL,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,rename_gateSlots] using otail_metrics tr yc y2c e

theorem zeroWith_subset (P Q:Wire→Program) (sub:∀h,wires (P h)⊆wires (Q h)) :
    ∀c bs,wires (zeroWith P c bs)⊆wires (zeroWith Q c bs) := by
  intro c bs
  induction bs generalizing c with
  | nil=>simpa only [zeroWith] using sub c
  | cons b bs ih=>
    simp only [zeroWith,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (ih b.work)) (Finset.Subset.refl _)

theorem zeroWith_metrics (P Q:Wire→Program) (d:Nat)
    (counts:∀h,toffoliCount (P h)+d=toffoliCount (Q h) ∧
      measurementCount (P h)=measurementCount (Q h) ∧ gateSlots (P h)≤gateSlots (Q h)+12) :
    ∀c bs,toffoliCount (zeroWith P c bs)+d=toffoliCount (zeroWith Q c bs) ∧
      measurementCount (zeroWith P c bs)=measurementCount (zeroWith Q c bs) ∧
      gateSlots (zeroWith P c bs)≤gateSlots (zeroWith Q c bs)+12 := by
  intro c bs
  induction bs generalizing c with
  | nil=>simpa only [zeroWith] using counts c
  | cons b bs ih=>
    have H:=ih b.work
    simp only [zeroWith,toffoliCount_append,measurementCount_append,gateSlots_append]
    omega


theorem surround_subset (R X A B:Program) (sub:wires A⊆wires B) :
    wires (R++(X++(A++(X++R))))⊆wires (R++(X++(B++(X++R)))) := by
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union sub (Finset.Subset.refl _)))

theorem surround_metrics (R X A B:Program) (d:Nat)
    (H:toffoliCount A+d=toffoliCount B ∧ measurementCount A=measurementCount B ∧ gateSlots A≤gateSlots B+12) :
    toffoliCount (R++(X++(A++(X++R))))+d=toffoliCount (R++(X++(B++(X++R)))) ∧
    measurementCount (R++(X++(A++(X++R))))=measurementCount (R++(X++(B++(X++R)))) ∧
    gateSlots (R++(X++(A++(X++R))))≤gateSlots (R++(X++(B++(X++R))))+12 := by
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem middle_subset (P Q A B:Program) (sub:wires A⊆wires B) :
    wires ((P++A)++Q)⊆wires ((P++B)++Q) := by
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub) (Finset.Subset.refl _)

theorem middle_metrics (P Q A B:Program) (d:Nat)
    (H:toffoliCount A+d=toffoliCount B ∧ measurementCount A=measurementCount B ∧ gateSlots A≤gateSlots B+12) :
    toffoliCount ((P++A)++Q)+d=toffoliCount ((P++B)++Q) ∧
    measurementCount ((P++A)++Q)=measurementCount ((P++B)++Q) ∧
    gateSlots ((P++A)++Q)≤gateSlots ((P++B)++Q)+12 := by
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem oclassifier_subset (tr:Tri) (yc y2c e:Bool) (xs work:List Wire)
    (y0 c f g O D H t1 t2 u:Wire) :
    wires (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u)⊆
      wires (InputSentinel.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) := by
  have Z:=zeroWith_subset _ _
    (tailL_subset tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
    ((tr.idx.map (fun i=>xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i=>xs.getD i 0)).tail work)
  unfold oclassifier InputSentinel.oclassifier
  exact surround_subset _ _ _ _ Z

theorem oclassifier_metrics (tr:Tri) (yc y2c e:Bool) (xs work:List Wire)
    (y0 c f g O D H t1 t2 u:Wire) :
    toffoliCount (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u)+(if e then 1 else 0)=
      toffoliCount (InputSentinel.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ∧
    measurementCount (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u)=
      measurementCount (InputSentinel.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u) ∧
    gateSlots (oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u)≤
      gateSlots (InputSentinel.oclassifier tr yc y2c e xs work y0 c f g O D H t1 t2 u)+12 := by
  have Z:=zeroWith_metrics _ _ (if e then 1 else 0)
    (tailL_metrics tr yc y2c e (xs.getD tr.r1 0) (xs.getD tr.r2 0) y0 c f g O D H t1 t2 u)
    ((tr.idx.map (fun i=>xs.getD i 0)).headD 0) (zeroPorts (tr.idx.map (fun i=>xs.getD i 0)).tail work)
  unfold oclassifier InputSentinel.oclassifier
  exact surround_metrics _ _ _ _ _ Z

theorem outStage_subset (L:ControlledPointLayout) (C:Point) :
    wires (outStage L C)⊆wires (InputSentinel.outStage L C) := by
  have Z:=oclassifier_subset (triOf C) (yBit C) (yBit (C+C)) (exceptionBit C) L.point.x (L.dialogPool.take 253)
    (yLow L) L.control L.point.finite L.genericSelect (parkWire L) L.doubleSelect L.core.equalNegY
    (L.dialogPool.getD 253 0) (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0)
  unfold outStage InputSentinel.outStage
  exact middle_subset _ _ _ _ Z

theorem outStage_metrics {cx cy:Fp} (hc:curve.toAffine.Nonsingular cx cy) :
    toffoliCount (outStage layout (.some hc))+1=toffoliCount (InputSentinel.outStage layout (.some hc)) ∧
    measurementCount (outStage layout (.some hc))=measurementCount (InputSentinel.outStage layout (.some hc)) ∧
    gateSlots (outStage layout (.some hc))≤gateSlots (InputSentinel.outStage layout (.some hc))+12 := by
  have Z:=oclassifier_metrics (triOf (.some hc)) (yBit (.some hc)) (yBit ((.some hc:Point)+.some hc))
    (exceptionBit (.some hc)) layout.point.x (layout.dialogPool.take 253) (yLow layout) layout.control
    layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect layout.core.equalNegY
    (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)
  have one : (if exceptionBit (.some hc) then 1 else 0)=1 := by rw [exceptionBit_finite hc]; rfl
  rw [one] at Z
  unfold outStage InputSentinel.outStage
  exact middle_metrics _ _ _ _ 1 Z

theorem outStage_physical_of (L:ControlledPointLayout) (C:Point)
    (A:GatePhysical (predecL (triOf C) (yBit C) L.genericSelect L.control
      (L.point.x.getD (triOf C).r1 0) (L.point.x.getD (triOf C).r2 0)
      (yLow L) (parkWire L) L.doubleSelect L.core.equalNegY))
    (B:GatePhysical (ocorners L C))
    (D:GatePhysical (oclassifier (triOf C) (yBit C) (yBit (C+C)) (exceptionBit C)
      L.point.x (L.dialogPool.take 253) (yLow L) L.control L.point.finite L.genericSelect
      (parkWire L) L.doubleSelect L.core.equalNegY (L.dialogPool.getD 253 0)
      (L.dialogPool.getD 254 0) (L.dialogPool.getD 255 0)))
    (E:GatePhysical (FiniteFlagInterval.zrep L)) : GatePhysical (outStage L C) := by
  unfold outStage
  simp only [gatePhysical_append]
  exact ⟨⟨⟨A,B⟩,D⟩,E⟩

theorem classifier_layout_physical (tr:Tri) (hv:tr.Valid) (yc y2c e:Bool) :
    GatePhysical (oclassifier tr yc y2c e layout.point.x (layout.dialogPool.take 253)
      (yLow layout) layout.control layout.point.finite layout.genericSelect (parkWire layout)
      layout.doubleSelect layout.core.equalNegY (layout.dialogPool.getD 253 0)
      (layout.dialogPool.getD 254 0) (layout.dialogPool.getD 255 0)) := by
  obtain ⟨-, -, fx10n, fx10x, -, -, -, -, -⟩ := out_fixed
  obtain ⟨hxn, hxl, hwl, hwn, hdisj, -, -⟩ := stage_layout layout layout_widths layout_nodup
  have C:=oclassifier_physical tr hv yc
    y2c e layout.point.x (layout.dialogPool.take 253)
    (yLow layout) layout.control layout.point.finite layout.genericSelect (parkWire layout) layout.doubleSelect
    layout.core.equalNegY (layout.dialogPool.getD 253 0) (layout.dialogPool.getD 254 0)
    (layout.dialogPool.getD 255 0) hxl hwl hxn hwn hdisj fx10n fx10x
  exact C


theorem old_parts (L:ControlledPointLayout) (C:Point) (h:GatePhysical (InputSentinel.outStage L C)) :
    GatePhysical (predecL (triOf C) (yBit C) L.genericSelect L.control
      (L.point.x.getD (triOf C).r1 0) (L.point.x.getD (triOf C).r2 0)
      (yLow L) (parkWire L) L.doubleSelect L.core.equalNegY) ∧
    GatePhysical (ocorners L C) ∧ GatePhysical (FiniteFlagInterval.zrep L) := by
  unfold InputSentinel.outStage at h
  simp only [gatePhysical_append] at h
  exact ⟨h.1.1.1,h.1.1.2,h.2⟩

theorem outStage_physical {cx cy:Fp} (hc:curve.toAffine.Nonsingular cx cy) :
    GatePhysical (outStage layout (.some hc)) := by
  have old:=old_parts layout (.some hc) (InputSentinel.outStage_physical hc)
  have cls:=classifier_layout_physical (triOf (.some hc)) (triOf_valid hc) (yBit (.some hc))
    (yBit ((.some hc:Point)+.some hc)) (exceptionBit (.some hc))
  apply outStage_physical_of layout (.some hc) old.1 old.2.1
  · exact cls
  · exact old.2.2



end ECDSAAdd.Entrant.OutputOpt
end

-- Consolidated output proof: ParityFinalOut
section

namespace ECDSAAdd.Entrant.ParityFinalOut
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  ParityStageXY.genericAll Entry530.generic530

theorem reference_eq (L : ControlledPointLayout) (cx cy : Fp) :
    ParityStageXY.genericRef L cx cy=Entry530.generic530 L cx cy := by
  simp only [ParityStageXY.genericRef,Entry530.generic530,ParityStageXY.entryRef,Entry530.entryStage530,
    ParityStageXY.restEntry,Entry530.restE530]

abbrev gen_block_run := ParityFinalXY.gen_block_run

def genBlockOpt (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (renameProgram (swapF L) (ParityStageXY.genericAll L cx cy))
def finiteProgramOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  InputSentinel.stage L C ++ renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) (genBlockOpt L cx cy))) ++ OutputOpt.outStage L C
def wrapperOpt (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgramOpt L C cx cy)

open Classical in
theorem finite_run {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool) (hs : PointDialogBoundary layout R b (fun _ => false) s.basis) :
    (run (finiteProgramOpt layout (.some hc) cx cy) m s).phase = s.phase ∧
    PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)
      (run (finiteProgramOpt layout (.some hc) cx cy) m s).basis := by
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  obtain ⟨m1, m2, m3, m4, m5⟩ := stage_mid layout layout_widths layout_nodup hc b R s m hs
  have hp := (point_holds _ _ _).mp hs.point
  unfold finiteProgramOpt
  rw [LocalWireModel.run_concat, LocalWireModel.run_concat]
  generalize ht1 : run (stage layout (.some hc)) m s = t1 at m1 m2 m3 m4 m5 ⊢
  have gsx := gsel_off
  have t1off (q : Wire) (hx : q ∉ layout.point.x) (hy : q ∉ layout.point.y) (hf : q ≠ layout.point.finite)
      (hg : q ≠ layout.genericSelect) : t1.basis q = s.basis q := m5 q hx hf hg
  have t1y : regValue layout.point.y t1.basis = pointY R := by
    rw [← hp.2.2]; apply regValue_congr; intro q hq
    exact m5 q (y_not_x layout layout_nodup q hq)
      (fun e => finite_not_flag.2 (e ▸ List.mem_append_right _ hq)) (fun e => gsx.2.1 (e ▸ hq))
  have hE : t1.basis layout.core.equalNegY = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.core.equalNegY (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hD : t1.basis layout.doubleSelect = false := by
    obtain ⟨a, b', c, d⟩ := out_off layout.doubleSelect (by simp)
    rw [t1off _ a b' c d]; exact hs.flags _ (by simp [flags_list])
  have hclean : regValue layout.dialogPool t1.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨f1, g1, -, -, -⟩ := out_pool_off q hq
    rw [t1off q (fun h => pool_not_point q hq (List.mem_append_left _ h))
      (fun h => pool_not_point q hq (List.mem_append_right _ h)) f1 g1]
    exact (regValue_zero _ _).mp hs.clean q hq
  -- the generic block moves the coordinates only
  suffices key : ∀ mm, (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) mm t1).phase = t1.phase ∧
      regValue layout.point.x (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        codeX (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      regValue layout.point.y (run (renameProgram (swapD layout) (renameProgram (swapE layout)
        (renameProgram (tauM layout) (genBlockOpt layout cx cy)))) mm t1).basis =
        pointY (if dialogOrdinary b R (.some hc) then R + .some hc else R) ∧
      ∀ q, q ∉ layout.point.x ++ layout.point.y →
        (run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
          (genBlockOpt layout cx cy)))) mm t1).basis q = t1.basis q by
    obtain ⟨k1, k2, k3, k4⟩ := key (List.drop (measurementCount (stage layout (.some hc))) m)
    generalize run (renameProgram (swapD layout) (renameProgram (swapE layout) (renameProgram (tauM layout)
      (genBlockOpt layout cx cy)))) (List.drop (measurementCount (stage layout (.some hc))) m) t1 = t2 at k1 k2 k3 k4 ⊢
    have fxy : layout.point.finite ∉ layout.point.x ++ layout.point.y := finite_not_flag.2
    have gxy : layout.genericSelect ∉ layout.point.x ++ layout.point.y := by
      simp only [List.mem_append, not_or]; exact ⟨gsx.1, gsx.2.1⟩
    obtain ⟨o1, o2⟩ := OutputOpt.outStage_run hc b R s hs t2
      (List.drop (measurementCount (stage layout (.some hc) ++ renameProgram (swapD layout)
        (renameProgram (swapE layout) (renameProgram (tauM layout) (genBlockOpt layout cx cy))))) m)
      k2 k3 (by rw [k4 _ fxy]; exact m3) (by rw [k4 _ gxy]; exact m4)
      (fun q hx hy hf hg => by
        rw [k4 q (by simp only [List.mem_append, not_or]; exact ⟨hx, hy⟩)]; exact m5 q hx hf hg)
    exact ⟨by rw [o1, k1, m1], o2⟩
  intro mm
  unfold genBlockOpt
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      have g := gen_block_run (ParityStageXY.genericAll layout cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true
        (fun base' => ParityStageXY.generic_true layout layout_widths layout_nodup x y cx cy base'
          den.1 den.2) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG]) hE hD hclean
      rw [hG, if_pos rfl, ← genericAdd_correct hr hc den.1]
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    rw [hG']
    simp only [Bool.false_eq_true, if_false]
    cases R with
    | zero =>
      have g := gen_block_run (ParityStageXY.genericAll layout cx cy) (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false
        (fun base' => ParityStageXY.generic_false layout layout_widths layout_nodup _ 0 cx cy base'
          FiniteFlagInterval.sentinel_ne_zero) t1 mm
        (by rw [m2, FiniteFlagInterval.sentinel_val]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      refine ⟨g.1, ?_, ?_, g.2.2.2⟩
      · rw [g.2.1, FiniteFlagInterval.sentinel_val]; rfl
      · rw [g.2.2.1]; rfl
    | @some x y hr =>
      have g := gen_block_run (ParityStageXY.genericAll layout cx cy) x y x y false
        (fun base' => ParityStageXY.generic_false layout layout_widths layout_nodup x y cx cy base'
          (curve_x_ne_zero hr)) t1 mm (by rw [m2]; rfl) (by rw [t1y]; rfl) m3 (by rw [m4, hG']) hE hD hclean
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2⟩

open Classical in
theorem wrapper_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    Triple (PointDialogBoundary layout R b (fun _ => false)) (wrapperOpt layout (.some hc) cx cy)
      (PointDialogBoundary layout (if b then R + .some hc else R) b (fun _ => false)) := by
  intro s m hs
  have h := finite_run hc b R s m hs
  unfold wrapperOpt
  rw [Square5Placement.pool_relabel_state_eq layout (Wrapper5.U layout) (Wrapper5.U_pool layout layout_widths)
    (Wrapper5.U_outside layout layout_widths) _ s m hs.clean h.2.clean]
  exact h



theorem rename_wires_sub (f : Wire → Wire) (P Q : Program) (h : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  simp only [renameProgram_support]
  exact Finset.image_subset_image h

theorem wrapper_support {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆wires (InputSentinel530.wrapper530 layout (.some hc) cx cy) := by
  have h:=ParityStageXY.generic_wires layout layout_widths cx cy
  rw [reference_eq] at h
  have b:=rename_wires_sub (Wrapper5.U layout) _ _ (rename_wires_sub (swapF layout) _ _ h)
  have m:=rename_wires_sub (swapD layout) _ _ (rename_wires_sub (swapE layout) _ _
    (rename_wires_sub (tauM layout) _ _ b))
  unfold wrapperOpt InputSentinel530.wrapper530
  apply rename_wires_sub
  simp only [finiteProgramOpt,InputSentinel530.finiteProgram530,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) m)
    (OutputOpt.outStage_subset layout (.some hc))

theorem support_used {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    wires (wrapperOpt layout (.some hc) cx cy)⊆layout.dialogUsedWires.toFinset :=
  (wrapper_support hc).trans (InputSentinel530.support_used530 hc)

theorem wrapper_metrics {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperOpt layout (.some hc) cx cy)+5=
      toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    measurementCount (wrapperOpt layout (.some hc) cx cy)=
      measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy) ∧
    gateSlots (wrapperOpt layout (.some hc) cx cy)≤
      gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)+12 := by
  have A:=ParityFinalXY.wrapper_metrics hc
  have B:=OutputOpt.outStage_metrics hc
  simp only [wrapperOpt,finiteProgramOpt,genBlockOpt,ParityFinalXY.wrapperOpt,
    ParityFinalXY.finiteProgramOpt,ParityFinalXY.genBlockOpt,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots] at A ⊢
  omega

theorem wrapper_physical {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GatePhysical (wrapperOpt layout (.some hc) cx cy) := by
  have old:GatePhysical (ParityStageXY.genericRef layout cx cy) := by
    rw [reference_eq]
    exact Entry530.generic_physical530 layout layout_widths layout_nodup cx cy
  have p0:=ParityStageXY.generic_physical layout layout_widths layout_nodup cx cy old
  have p1 := gatePhysical_rename (swapF layout) (swapF_injective layout layout_widths layout_nodup) _ p0
  have p2 := gatePhysical_rename (Wrapper5.U layout) (Wrapper5.U layout).injective _ p1
  have p3 := gatePhysical_rename (tauM layout) (tauM_injective layout layout_nodup) _ p2
  have p4 := gatePhysical_rename (swapE layout) (swapE_injective layout layout_widths layout_nodup) _ p3
  have p5 := gatePhysical_rename (swapD layout) (swapD_injective layout layout_widths layout_nodup) _ p4
  unfold wrapperOpt
  apply gatePhysical_rename _ (Wrapper5.U layout).injective
  simp only [finiteProgramOpt,genBlockOpt,gatePhysical_append]
  exact ⟨⟨InputSentinel.stage_physical hc,p5⟩,OutputOpt.outStage_physical hc⟩

open Classical in
theorem full_spec {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point) :
    {{ layout.control=b,layout.point=R,layout.work=0 }} wrapperOpt layout (.some hc) cx cy
    {{ layout.control=b,layout.point=(if b then R+.some hc else R),layout.work=0 }} := by
  intro s m hs
  have hz:regValue layout.work s.basis=0:=hs.2
  have clean (q : Wire) (hq:q∈layout.inPlaceFlags++layout.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work layout hq)
  have hi:PointDialogBoundary layout R b (fun _=>false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq=>clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq=>clean q (by simp [hq]))
  have a:=wrapper_spec hc b R s m hi
  have old:=InputSentinel530.wrapper530_spec hc b R s m hi
  rw [MeasuredDH.boundary_unique layout _ _ (support_used hc) (InputSentinel530.support_used530 hc)
    s m _ b a.2 old.2 (a.1.trans old.1.symm)]
  exact InputSentinel530.full_spec530 hc b R s m hs

def programOpt (C : Point) : Program :=
  match C with
  | .zero=>[]
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _=>wrapperOpt layout C cx cy

def entryOpt : Challenge.Entry := fun C=>normalizeProgram (programOpt C)
def boundsOpt : Challenge.Bounds := ⟨2150530,1498370,1587,50249326⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (programOpt C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero=>
    intro s m hs
    simpa only [programOpt,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc=>exact fixed_correct _ b R _ (full_spec hc b R) (support_used hc)

theorem program_toffoli (C : Point) : toffoliCount (programOpt C)≤2150530 := by
  cases C with
  | zero=>simp [programOpt,toffoliCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_toffoli530 (.some hc)
    have delta:=(wrapper_metrics hc).1
    change toffoliCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤2150535 at old
    change toffoliCount (wrapperOpt layout (.some hc) cx cy)≤2150530
    omega

theorem program_measurements (C : Point) : measurementCount (programOpt C)≤1498370 := by
  cases C with
  | zero=>simp [programOpt,measurementCount]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_measurements530 (.some hc)
    have delta:=(wrapper_metrics hc).2.1
    change measurementCount (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1498370 at old
    change measurementCount (wrapperOpt layout (.some hc) cx cy)≤1498370
    omega

theorem program_qubits (C : Point) : qubits (programOpt C)≤1587 := by
  cases C with
  | zero=>change qubits []≤1587;rw [qubits_empty];decide
  | @some cx cy hc=>
    have old:=InputSentinel530.program_qubits530 (.some hc)
    change qubits (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤1587 at old
    change qubits (wrapperOpt layout (.some hc) cx cy)≤1587
    apply le_trans (Finset.card_le_card ?_) old
    exact Finset.union_subset_union (Finset.Subset.refl _) (wrapper_support hc)

theorem program_physical (C : Point) : GatePhysical (programOpt C) := by
  cases C with
  | zero=>simp [programOpt,GatePhysical]
  | @some cx cy hc=>exact wrapper_physical hc

theorem program_slots (C : Point) : gateSlots (programOpt C)≤50249326 := by
  cases C with
  | zero=>simp [programOpt]
  | @some cx cy hc=>
    have old:=InputSentinel530.program_slots530 (.some hc)
    have delta:=(wrapper_metrics hc).2.2
    change gateSlots (InputSentinel530.wrapper530 layout (.some hc) cx cy)≤50249314 at old
    change gateSlots (wrapperOpt layout (.some hc) cx cy)≤50249326
    omega

theorem certificateOpt : Challenge.Certificate entryOpt boundsOpt where
  correct C b R:=(normalize_triple _ _ _).mpr (program_correct C b R)
  physical C:=normalize_physical _ (by simpa only [GatePhysical] using program_physical C)
  toffoli_le C:=(normalize_toffoli _).trans (program_toffoli C)
  measurements_le C:=by
    change measurementCount (normalizeProgram (programOpt C))≤1498370
    rw [normalize_measurements];exact program_measurements C
  qubits_le C:=by
    change qubits (normalizeProgram (programOpt C))≤1587
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C:=by
    change gateSlots (normalizeProgram (programOpt C))≤50249326
    rw [normalize_slots];exact program_slots C

end ECDSAAdd.Entrant.ParityFinalOut
end

namespace ECDSAAdd.Entrant

def program := ParityFinalOut.programOpt
def entry := ParityFinalOut.entryOpt
def bounds := ParityFinalOut.boundsOpt
theorem certificate : Challenge.Certificate entry bounds := ParityFinalOut.certificateOpt

end ECDSAAdd.Entrant
end
