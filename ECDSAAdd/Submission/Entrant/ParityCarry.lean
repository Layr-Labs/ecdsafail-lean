import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ExactBorrowErase
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.DisjointPrograms
import ECDSAAdd.Challenge.Contract

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
