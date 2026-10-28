import ECDSAAdd.Arithmetic.MappedAdder

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def constantBorrow (bit : Bool) (x cin target : Wire) : Program :=
  [.X x]++mappedMajority {wire:=none,flip:=bit} x cin target++[.X x]

def constantBorrowErase (bit : Bool) (x cin target : Wire) : Program :=
  [.X x]++mappedEraseCarry {wire:=none,flip:=bit} x cin target++[.X x]

theorem carryBit_swap (A B C : Bool) : carryBit A B C=carryBit B A C := by
  cases A <;> cases B <;> cases C <;> rfl

theorem constantBorrow_correct (bit : Bool) (x cin target : Wire)
    (hn : [x,cin,target].Nodup) (s : State) (m : List Bool) :
    run (constantBorrow bit x cin target) m s=
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ carryBit (!s.basis x) bit (s.basis cin))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxc,hxt⟩,hct⟩ := hn
  have hcx := Ne.symm hxc
  cases bit <;>
    simp only [constantBorrow,mappedMajority,Bool.false_eq_true,if_false,if_true,
      List.cons_append,List.nil_append,run]
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqx : q=x <;> by_cases hqc : q=cin <;> by_cases hqt : q=target <;>
      simp_all [writeBit,Function.update,carryBit] <;>
      cases s.basis x <;> cases s.basis cin <;> cases s.basis target <;> simp_all

theorem constantBorrowErase_correct (bit : Bool) (x cin target : Wire)
    (hn : [x,cin,target].Nodup) (s : State) (m : List Bool)
    (hk : s.basis target=carryBit (!s.basis x) bit (s.basis cin)) :
    run (constantBorrowErase bit x cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  have nd := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxc,hxt⟩,hct⟩ := hn
  let t : State := ⟨s.phase,writeBit s.basis x (!s.basis x)⟩
  have known : t.basis target=carryBit
      (({wire:=none,flip:=bit} : MappedBit).value t.basis) (t.basis x) (t.basis cin) := by
    have h := hk.trans (carryBit_swap (!s.basis x) bit (s.basis cin))
    simpa [t,writeBit,Ne.symm hxt,Ne.symm hxc,MappedBit.value] using h
  have clear := mappedEraseCarry_correct {wire:=none,flip:=bit} x cin target nd (by simp) t m known
  simp only [constantBorrowErase,List.cons_append,List.nil_append,run]
  change run (mappedEraseCarry {wire:=none,flip:=bit} x cin target++[.X x]) m t=_
  rw [run_append,run_take,clear]
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hqt : q=target <;> by_cases hqx : q=x <;>
    simp_all [t,writeBit,Function.update]

theorem constantBorrow_counts (bit : Bool) (x cin target : Wire) :
    toffoliCount (constantBorrow bit x cin target)=1 ∧
    measurementCount (constantBorrow bit x cin target)=0 ∧
    toffoliCount (constantBorrowErase bit x cin target)=0 ∧
    measurementCount (constantBorrowErase bit x cin target)=1 := by
  have h := mappedBit_counts {wire:=none,flip:=bit} x cin target
  simp only [constantBorrow,constantBorrowErase,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,h.1,h.2.1,h.2.2.1,h.2.2.2.1]
  simp

/-- Exact comparison with a literal source. Scratch contains n-1 borrow bits;
no constant register, truncated window or sampled envelope is required. -/
def compareConstantLt : List Wire → List Wire → Wire → Wire → Nat → Program
  | x::x'::xs,c::cs,cin,target,k =>
      constantBorrow (decide (k%2=1)) x cin c++
        compareConstantLt (x'::xs) cs c target (k/2)++
        constantBorrowErase (decide (k%2=1)) x cin c
  | [x],_,cin,target,k => constantBorrow (decide (k%2=1)) x cin target
  | _,_,_,_,_ => []

def compareConstantGe (xs carry : List Wire) (cin target : Wire) (k : Nat) : Program :=
  compareConstantLt xs carry cin target k++[.X target]

theorem compareConstantLt_counts (xs carry : List Wire) (cin target : Wire) (k : Nat)
    (hc : carry.length+1=xs.length) :
    toffoliCount (compareConstantLt xs carry cin target k)=xs.length ∧
    measurementCount (compareConstantLt xs carry cin target k)=xs.length-1 := by
  induction xs generalizing carry cin k with
  | nil => simp at hc
  | cons x xs ih =>
    cases xs with
    | nil =>
      have h := constantBorrow_counts (decide (k%2=1)) x cin target
      simpa [compareConstantLt] using And.intro h.1 h.2.1
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have h := ih cs c (k/2) (by simpa using hc)
        have b := constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareConstantLt]
        constructor
        · simp only [toffoliCount_append,b.1,b.2.2.1]
          rw [h.1]
          simp [Nat.add_comm]
        · simp only [measurementCount_append,b.2.1,b.2.2.2]
          rw [h.2]
          simp

theorem compareConstantGe_counts (xs carry : List Wire) (cin target : Wire) (k : Nat)
    (hc : carry.length+1=xs.length) :
    toffoliCount (compareConstantGe xs carry cin target k)=xs.length ∧
    measurementCount (compareConstantGe xs carry cin target k)=xs.length-1 := by
  have h := compareConstantLt_counts xs carry cin target k hc
  simp [compareConstantGe,h.1,h.2,toffoliCount,measurementCount]

/-- A literal comparison toggles only its target and returns all borrow
scratch to zero, for every input word and every measurement record. -/
theorem compareConstantLt_correct (xs carry : List Wire) (cin target : Wire) (k : Nat)
    (hn : (target::cin::(xs++carry)).Nodup)
    (hc : carry.length+1=xs.length) (hk : k<2^xs.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (compareConstantLt xs carry cin target k) m s).phase=s.phase ∧
    (∀q,q≠target → (run (compareConstantLt xs carry cin target k) m s).basis q=s.basis q) ∧
    (run (compareConstantLt xs carry cin target k) m s).basis target=
      (s.basis target ^^ decide (regValue xs s.basis<k+(s.basis cin).toNat)) := by
  induction xs generalizing carry cin k s m with
  | nil => simp at hc
  | cons x xs ih =>
    have cnt := List.nodup_iff_count.mp hn
    have htx : target≠x := by
      intro bad; have h := cnt target; subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have htci : target≠cin := by
      intro bad; have h := cnt target; subst cin
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have hxc : x≠cin := by
      intro bad; have h := cnt cin; subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    cases xs with
    | nil =>
      have nd : [x,cin,target].Nodup := by
        apply List.nodup_iff_count.mpr; intro q; have h := cnt q
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        omega
      rw [compareConstantLt,constantBorrow_correct _ _ _ _ nd]
      refine ⟨rfl,?_,?_⟩
      · intro q hq; simp [writeBit,hq]
      · have small : k<2 := by simpa using hk
        by_cases zero : k=0
        · subst k
          cases hx : s.basis x <;> cases hi : s.basis cin <;>
            simp [writeBit,regValue,carryBit,hx,hi]
        · have one : k=1 := by omega
          subst k
          cases hx : s.basis x <;> cases hi : s.basis cin <;>
            simp [writeBit,regValue,carryBit,hx,hi]
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have htc : target≠c := by
          intro bad; have h := cnt target; subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hxc' : x≠c := by
          intro bad; have h := cnt c; subst x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hcic : cin≠c := by
          intro bad; have h := cnt c; subst cin
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hctail : c∉x'::xs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
          omega
        have hccs : c∉cs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have nd : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have nd' : (target::c::((x'::xs)++cs)).Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        let bit := decide (k%2=1)
        let K := carryBit (!s.basis x) bit (s.basis cin)
        let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
        have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by simp [s1,writeBit,hq]
        have zero := hclean c (by simp)
        have first (record : List Bool) : run (constantBorrow bit x cin c) record s=s1 := by
          rw [constantBorrow_correct _ _ _ _ nd]
          simp [s1,K,zero]
        have clean' : ∀q∈cs,s1.basis q=false := by
          intro q hq
          rw [keep q (fun bad => hccs (bad ▸ hq))]
          exact hclean q (by simp [hq])
        have high : k/2<2^(x'::xs).length := by
          simp only [List.length_cons,Nat.pow_succ] at hk ⊢
          omega
        obtain ⟨hp,he,hv⟩ := ih cs c (k/2) nd' (by simpa using hc) high s1 m clean'
        let t := run (compareConstantLt (x'::xs) cs c target (k/2)) m s1
        have tx : t.basis x=s.basis x := (he x htx.symm).trans (keep x hxc')
        have ti : t.basis cin=s.basis cin := (he cin htci.symm).trans (keep cin hcic)
        have tk : t.basis c=K := by rw [he c htc.symm]; simp [s1,writeBit]
        have clear (record : List Bool) : run (constantBorrowErase bit x cin c) record t=
            ⟨t.phase,writeBit t.basis c false⟩ := by
          apply constantBorrowErase_correct _ _ _ _ nd t record
          rw [tx,ti,tk]
        have counts := constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareConstantLt]
        simp only [List.append_assoc,run_append,run_take,counts.2.1,List.take_zero,List.drop_zero]
        rw [first]
        change (run (constantBorrowErase bit x cin c) _ t).phase=_ ∧ _
        rw [clear]
        refine ⟨hp,?_,?_⟩
        · intro q hq
          by_cases hqc : q=c
          · subst q; simp [writeBit,zero]
          · simp only [writeBit,Function.update_of_ne hqc]
            exact (he q hq).trans (keep q hqc)
        · simp only [writeBit,Function.update_of_ne htc]
          rw [hv,keep target htc]
          have v : regValue (x'::xs) s1.basis=regValue (x'::xs) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q (fun bad => hctail (bad ▸ hq)))
          have carryVal : s1.basis c=K := by simp [s1,writeBit]
          rw [v,carryVal]
          have split : bit.toNat+2*(k/2)=k := by
            have e := Nat.mod_add_div k 2
            have b := Nat.mod_lt k (by decide : 0<2)
            by_cases odd : k%2=1 <;> simp [bit,odd] <;> omega
          have thr := borrow_threshold (s.basis x) bit (s.basis cin)
            (regValue (x'::xs) s.basis) (k/2)
          rw [split] at thr
          have pred : decide (regValue (x::x'::xs) s.basis<k+(s.basis cin).toNat)=
              decide (regValue (x'::xs) s.basis<k/2+K.toNat) := by
            apply decide_eq_decide.mpr
            simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,K] using thr
          rw [pred]

theorem compareConstantGe_correct (xs carry : List Wire) (cin target : Wire) (k : Nat)
    (hn : (target::cin::(xs++carry)).Nodup)
    (hc : carry.length+1=xs.length) (hk : k<2^xs.length)
    (s : State) (m : List Bool) (hcin : s.basis cin=false)
    (hclean : ∀q∈carry,s.basis q=false) :
    (run (compareConstantGe xs carry cin target k) m s).phase=s.phase ∧
    (∀q,q≠target → (run (compareConstantGe xs carry cin target k) m s).basis q=s.basis q) ∧
    (run (compareConstantGe xs carry cin target k) m s).basis target=
      (s.basis target ^^ decide (k≤regValue xs s.basis)) := by
  obtain ⟨hp,he,hv⟩ := compareConstantLt_correct xs carry cin target k hn hc hk s m hclean
  simp only [compareConstantGe,run_append,run_take,run]
  refine ⟨hp,?_,?_⟩
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]
    exact he q hq
  · simp only [writeBit,Function.update_self,hv,hcin,Bool.toNat_false,Nat.add_zero]
    by_cases less : regValue xs s.basis<k
    · have no : ¬k≤regValue xs s.basis := by omega
      simp [less,no]
    · have yes : k≤regValue xs s.basis := by omega
      simp [less,yes]

end ECDSAAdd.Arithmetic
