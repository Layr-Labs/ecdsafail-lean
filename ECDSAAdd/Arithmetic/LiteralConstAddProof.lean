import ECDSAAdd.Arithmetic.LiteralConstAdd

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

private theorem literal_split (k : Nat) : (decide (k%2=1)).toNat+2*(k/2)=k := by
  have h := Nat.mod_add_div k 2
  have hm := Nat.mod_lt k (by decide : 0<2)
  by_cases ho : k%2=1 <;> simp [ho] <;> omega

/-- Exact arbitrary-word addition for every literal k, with unrestricted
incoming phase and carry-in, and independent arbitrary measurement records.
No canonical-input bound or literal-size restriction is imposed. -/
theorem literalConstAdd_correct (xs carry : List Wire) (cin one : Wire) (k : Nat)
    (hn : (one::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length)
    (s : State) (m : List Bool) (ho : s.basis one=false)
    (hclean : ∀ q∈carry,s.basis q=false) :
    (run (literalConstAdd xs carry cin one k) m s).phase=s.phase ∧
    (∀ q,q∉xs → (run (literalConstAdd xs carry cin one k) m s).basis q=s.basis q) ∧
    regValue xs (run (literalConstAdd xs carry cin one k) m s).basis=
      (regValue xs s.basis+k+(s.basis cin).toNat)%2^xs.length := by
  induction xs generalizing carry cin k s m with
  | nil => simp at hc
  | cons x xs ih =>
    have hd := List.nodup_cons.mp hn
    have hi := List.nodup_cons.mp hd.2
    have words := List.nodup_append'.mp hi.2
    have hxi : x≠cin := by intro h; exact hi.1 (by simp [h])
    cases xs with
    | nil =>
      rw [literalConstAdd,literalConstSum_correct _ _ _ hxi]
      refine ⟨rfl,?_,?_⟩
      · intro q hq
        have hqx : q≠x := by simpa using hq
        simp [writeBit,hqx]
      · have hcol := sum_value_step (s.basis x) (decide (k%2=1)) (s.basis cin) 0 (k/2) 0
        rw [literal_split] at hcol
        simpa [regValue,writeBit,Bool.toNat,Bool.cond_eq_ite,Nat.mod_one] using hcol
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have count := List.nodup_iff_count.mp hn
        have nd : [one,x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q; have hh := count q
          simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
          omega
        have tailND : (one::c::((x'::xs)++cs)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q; have hh := count q
          simp only [List.count_cons,List.count_append] at hh ⊢
          omega
        have stepND : [x,cin,c].Nodup := (List.nodup_cons.mp nd).2
        have nd' := nd
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
          not_or,not_false_eq_true,and_true] at nd'
        obtain ⟨⟨hox,hoi,hoc⟩,⟨hxi,hxc⟩,hic⟩ := nd'
        have xTail : x∉x'::xs := (List.nodup_cons.mp words.1).1
        have cTail : c∉x'::xs := by
          intro h; exact List.disjoint_left.mp words.2.2 (List.mem_cons_of_mem x h) List.mem_cons_self
        have iTail : cin∉x'::xs := fun h => hi.1
          (List.mem_append_left _ (List.mem_cons_of_mem x h))
        have oTail : one∉x'::xs := fun h => hd.1
          (List.mem_cons_of_mem cin (List.mem_append_left _ (List.mem_cons_of_mem x h)))
        have cScratch : c∉cs := (List.nodup_cons.mp words.2.1).1
        have xScratch : x∉cs := by
          intro h; exact List.disjoint_left.mp words.2.2
            (show x∈x::x'::xs from List.mem_cons_self) (List.mem_cons_of_mem c h)
        let bit := decide (k%2=1)
        let S := sumBit (s.basis x) bit (s.basis cin)
        let K := carryBit (s.basis x) bit (s.basis cin)
        let s1 : State := ⟨s.phase,writeBit (writeBit s.basis x S) c K⟩
        have keep (q : Wire) (hqx : q≠x) (hqc : q≠c) : s1.basis q=s.basis q := by
          simp [s1,writeBit,hqx,hqc]
        have first (record : List Bool) : run (literalConstStep bit x cin c) record s=s1 := by
          exact literalConstStep_correct bit x cin c stepND s record (hclean c (by simp))
        have one1 : s1.basis one=false := (keep one hox hoc).trans ho
        have clean1 : ∀ q∈cs,s1.basis q=false := by
          intro q hq
          exact (keep q (fun h => xScratch (h ▸ hq))
            (fun h => cScratch (h ▸ hq))).trans (hclean q (by simp [hq]))
        have high := ih cs c (k/2) tailND (by simpa using hc) s1 m one1 clean1
        let t := run (literalConstAdd (x'::xs) cs c one (k/2)) m s1
        have tx : t.basis x=S := by rw [high.2.1 x xTail]; simp [s1,writeBit,hxc]
        have ti : t.basis cin=s.basis cin :=
          (high.2.1 cin iTail).trans (keep cin (Ne.symm hxi) hic)
        have tc : t.basis c=K := by rw [high.2.1 c cTail]; simp [s1,writeBit]
        have ton : t.basis one=false := (high.2.1 one oTail).trans one1
        have erase (record : List Bool) : run (literalConstErase bit x cin c one) record t=
            ⟨t.phase,writeBit t.basis c false⟩ := by
          apply literalConstErase_correct bit x cin c one nd t record ton
          rw [tx,ti,tc]
          exact (literalCarryPredicate_sum (s.basis x) bit (s.basis cin)).symm
        have counts := literalConstCell_counts (decide (k%2=1)) x cin c one
        rw [literalConstAdd]
        simp only [List.append_assoc,run_append,run_take,counts.2.1,List.drop_zero]
        rw [first]
        change (run (literalConstErase bit x cin c one) _ t).phase=s.phase ∧ _
        rw [erase]
        refine ⟨high.1,?_,?_⟩
        · intro q hq
          have hxq : q≠x := fun h => hq (by simp [h])
          have htq : q∉x'::xs := fun h => hq (by simp [h])
          by_cases hqc : q=c
          · subst q; simp [writeBit,hclean c (by simp)]
          · simp only [writeBit,Function.update_of_ne hqc]
            exact (high.2.1 q htq).trans (keep q hxq hqc)
        · have tailKeep : regValue (x'::xs) (writeBit t.basis c false)=regValue (x'::xs) t.basis :=
            regValue_congr _ _ _ (fun q hq => by
              simp [writeBit,show q≠c from fun h => cTail (h ▸ hq)])
          have tailIn : regValue (x'::xs) s1.basis=regValue (x'::xs) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q
              (fun h => xTail (h ▸ hq)) (fun h => cTail (h ▸ hq)))
          have kc : s1.basis c=K := by simp [s1,writeBit]
          change (if (writeBit t.basis c false) x then 1 else 0)+
            2*regValue (x'::xs) (writeBit t.basis c false)=_
          rw [tailKeep,high.2.2,tailIn,kc]
          simp only [writeBit,Function.update_of_ne hxc,tx]
          have col := sum_value_step (s.basis x) bit (s.basis cin)
            (regValue (x'::xs) s.basis) (k/2) (x'::xs).length
          have split : bit.toNat+2*(k/2)=k := literal_split k
          rw [split] at col
          simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,List.length_cons,S,K] using col

/-- Explicit restoration of the quantum carry-in, clean One and every
borrowed carry wire, alongside the complete outsider frame and word result. -/
theorem literalConstAdd_full (xs carry : List Wire) (cin one : Wire) (k : Nat)
    (hn : (one::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length)
    (s : State) (m : List Bool) (ho : s.basis one=false)
    (hclean : ∀ q∈carry,s.basis q=false) :
    (run (literalConstAdd xs carry cin one k) m s).phase=s.phase ∧
    regValue xs (run (literalConstAdd xs carry cin one k) m s).basis=
      (regValue xs s.basis+k+(s.basis cin).toNat)%2^xs.length ∧
    (run (literalConstAdd xs carry cin one k) m s).basis cin=s.basis cin ∧
    (run (literalConstAdd xs carry cin one k) m s).basis one=false ∧
    (∀ q∈carry,(run (literalConstAdd xs carry cin one k) m s).basis q=false) ∧
    (∀ q,q∉xs → (run (literalConstAdd xs carry cin one k) m s).basis q=s.basis q) := by
  have h := literalConstAdd_correct xs carry cin one k hn hc s m ho hclean
  have nd := List.nodup_cons.mp hn
  have ni := List.nodup_cons.mp nd.2
  have ic : cin∉xs := fun hi => ni.1 (by simp [hi])
  have oc : one∉xs := fun hi => nd.1 (by simp [hi])
  refine ⟨h.1,h.2.2,h.2.1 cin ic,(h.2.1 one oc).trans ho,?_,h.2.1⟩
  intro q hq
  have away : q∉xs := by
    have dis := (List.nodup_append'.mp ni.2).2.2
    exact fun hx => List.disjoint_left.mp dis hx hq
  exact (h.2.1 q away).trans (hclean q hq)

end ECDSAAdd.Arithmetic
