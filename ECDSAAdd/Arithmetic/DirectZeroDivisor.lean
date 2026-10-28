import ECDSAAdd.Arithmetic.ZeroSeededConstantCompare
import ECDSAAdd.Arithmetic.MaskedConstant

namespace ECDSAAdd.Arithmetic

/-- Replace the zero divisor by one while retaining the original-zero flag.
The literal comparator uses n-1 borrow scratch bits and no constant register. -/
def directZeroDivisorEnter (xs carry : List Wire) (cin flag : Wire) : Program :=
  ZeroSeededConstantCompare.program xs carry cin flag ++ maskedConstant flag xs 1

/-- The caller returns the repaired word unchanged; other caller coordinates
may have changed. Undo the repair before uncomputing the original-zero flag. -/
def directZeroDivisorLeave (xs carry : List Wire) (cin flag : Wire) : Program :=
  maskedConstant flag xs 1 ++ ZeroSeededConstantCompare.program xs carry cin flag

def directDivisor (X : Nat) : Nat := if X=0 then 1 else X

private theorem directDivisor_xor (X : Nat) :
    X ^^^ (if decide (X=0) then 1 else 0) = directDivisor X ∧
    directDivisor X ^^^ (if decide (X=0) then 1 else 0) = X := by
  by_cases h : X=0 <;> simp [directDivisor,h]

private theorem directLayout (xs carry : List Wire) (cin flag : Wire)
    (hn : (flag::cin::(xs++carry)).Nodup) :
    xs.Nodup ∧ flag∉xs ∧ cin≠flag ∧ (∀ q∈carry,q≠flag ∧ q∉xs) := by
  obtain ⟨hf,hrest⟩ := List.nodup_cons.mp hn
  obtain ⟨hc,hwords⟩ := List.nodup_cons.mp hrest
  have hh := List.nodup_append.mp hwords
  refine ⟨hh.1,?_,?_,?_⟩
  · intro h; exact hf (by simp [h])
  · intro h; exact hf (by simp [h])
  · intro q hq
    constructor
    · intro h; subst q; exact hf (by simp [hq])
    · intro hx; exact hh.2.2 q hx q hq rfl

private theorem directWidth (xs carry : List Wire)
    (hc : carry.length+1=xs.length) : 1<2^xs.length := by
  have hp : 0<xs.length := by omega
  exact Nat.one_lt_two_pow (by omega)

private theorem directZeroCompare_correct (xs carry : List Wire) (cin flag : Wire)
    (hn : (flag::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hcin : s.basis cin=false) :
    (run (ZeroSeededConstantCompare.program xs carry cin flag) m s).phase=s.phase ∧
    (∀q,q≠flag → (run (ZeroSeededConstantCompare.program xs carry cin flag) m s).basis q=s.basis q) ∧
    (run (ZeroSeededConstantCompare.program xs carry cin flag) m s).basis flag=
      (s.basis flag ^^ decide (regValue xs s.basis<1+(s.basis cin).toNat)) := by
  rw [ZeroSeededConstantCompare.equiv xs carry cin flag hn hc s m hcin hclean]
  exact compareConstantLt_correct xs carry cin flag 1 hn hc (directWidth xs carry hc) s m hclean

/-- Complete enter contract, valid on every n-bit word (including 0 and 1),
with arbitrary measurement records and unrestricted incoming phase. -/
theorem directZeroDivisorEnter_correct (xs carry : List Wire) (cin flag : Wire)
    (hn : (flag::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length)
    (s : State) (m : List Bool) (hcin : s.basis cin=false)
    (hflag : s.basis flag=false) (hclean : ∀ q∈carry,s.basis q=false) :
    (run (directZeroDivisorEnter xs carry cin flag) m s).phase=s.phase ∧
    (∀ q,q≠flag → q∉xs →
      (run (directZeroDivisorEnter xs carry cin flag) m s).basis q=s.basis q) ∧
    (run (directZeroDivisorEnter xs carry cin flag) m s).basis flag=
      decide (regValue xs s.basis=0) ∧
    regValue xs (run (directZeroDivisorEnter xs carry cin flag) m s).basis=
      directDivisor (regValue xs s.basis) ∧
    (run (directZeroDivisorEnter xs carry cin flag) m s).basis cin=false ∧
    (∀ q∈carry,(run (directZeroDivisorEnter xs carry cin flag) m s).basis q=false) := by
  obtain ⟨hxs,hfx,hcf,hcarry⟩ := directLayout xs carry cin flag hn
  let a := ZeroSeededConstantCompare.program xs carry cin flag
  let t := run a (m.take (measurementCount a)) s
  have cmp := directZeroCompare_correct xs carry cin flag hn hc
    s (m.take (measurementCount a)) hclean hcin
  change t.phase=s.phase ∧ (∀ q,q≠flag → t.basis q=s.basis q) ∧ _ at cmp
  have tz : t.basis flag=decide (regValue xs s.basis=0) := by
    simpa [hcin,hflag,Nat.lt_one_iff] using cmp.2.2
  have tx : regValue xs t.basis=regValue xs s.basis :=
    regValue_congr xs _ _ (fun q hq => cmp.2.1 q (fun h => hfx (h ▸ hq)))
  have mask := maskedConstant_correct flag xs 1 hxs hfx (directWidth xs carry hc)
    t (m.drop (measurementCount a))
  rw [directZeroDivisorEnter,run_append]
  change (run (maskedConstant flag xs 1) _ t).phase=_ ∧ _
  refine ⟨mask.1.trans cmp.1,?_,?_,?_,?_,?_⟩
  · intro q hq hx; exact (mask.2.1 q hx).trans (cmp.2.1 q hq)
  · exact (mask.2.1 flag hfx).trans tz
  · rw [mask.2.2,tx,tz]; exact (directDivisor_xor _).1
  · have hcx : cin∉xs := by
      obtain ⟨_,hr⟩ := List.nodup_cons.mp hn
      exact fun h => (List.nodup_cons.mp hr).1 (by simp [h])
    exact ((mask.2.1 cin hcx).trans (cmp.2.1 cin hcf)).trans hcin
  · intro q hq
    exact ((mask.2.1 q (hcarry q hq).2).trans
      (cmp.2.1 q (hcarry q hq).1)).trans (hclean q hq)

/-- Leave uses the original X as a ghost witness. It restores X and clears
the flag, cin and all borrow scratch, preserving all other caller coordinates
and the current phase. No constraint is imposed on those other coordinates. -/
theorem directZeroDivisorLeave_correct (xs carry : List Wire) (cin flag : Wire)
    (hn : (flag::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length)
    (X : Nat) (s : State) (m : List Bool) (hcin : s.basis cin=false)
    (hflag : s.basis flag=decide (X=0)) (hword : regValue xs s.basis=directDivisor X)
    (hclean : ∀ q∈carry,s.basis q=false) :
    (run (directZeroDivisorLeave xs carry cin flag) m s).phase=s.phase ∧
    (∀ q,q≠flag → q∉xs →
      (run (directZeroDivisorLeave xs carry cin flag) m s).basis q=s.basis q) ∧
    (run (directZeroDivisorLeave xs carry cin flag) m s).basis flag=false ∧
    regValue xs (run (directZeroDivisorLeave xs carry cin flag) m s).basis=X ∧
    (run (directZeroDivisorLeave xs carry cin flag) m s).basis cin=false ∧
    (∀ q∈carry,(run (directZeroDivisorLeave xs carry cin flag) m s).basis q=false) := by
  obtain ⟨hxs,hfx,hcf,hcarry⟩ := directLayout xs carry cin flag hn
  let t := run (maskedConstant flag xs 1) m s
  have mask := maskedConstant_correct flag xs 1 hxs hfx (directWidth xs carry hc) s m
  have tz : t.basis flag=decide (X=0) := (mask.2.1 flag hfx).trans hflag
  have tx : regValue xs t.basis=X := by
    rw [mask.2.2,hword,hflag]; exact (directDivisor_xor X).2
  have hcx : cin∉xs := by
    obtain ⟨_,hr⟩ := List.nodup_cons.mp hn
    exact fun h => (List.nodup_cons.mp hr).1 (by simp [h])
  have ti : t.basis cin=false := (mask.2.1 cin hcx).trans hcin
  have tc : ∀ q∈carry,t.basis q=false := by
    intro q hq; exact (mask.2.1 q (hcarry q hq).2).trans (hclean q hq)
  have cmp := directZeroCompare_correct xs carry cin flag hn hc t m tc ti
  have count := maskedConstant_counts flag xs 1
  rw [directZeroDivisorLeave,run_append,run_take,count.2,List.drop_zero]
  change (run (ZeroSeededConstantCompare.program xs carry cin flag) m t).phase=_ ∧ _
  refine ⟨cmp.1.trans mask.1,?_,?_,?_,?_,?_⟩
  · intro q hq hx; exact (cmp.2.1 q hq).trans (mask.2.1 q hx)
  · simpa [tz,tx,ti,Nat.lt_one_iff] using cmp.2.2
  · exact (regValue_congr xs _ _
      (fun q hq => cmp.2.1 q (fun h => hfx (h ▸ hq)))).trans tx
  · exact (cmp.2.1 cin hcf).trans ti
  · intro q hq; exact (cmp.2.1 q (hcarry q hq).1).trans (tc q hq)

/-- Nonzero repaired divisor, with no empirical restriction on X. -/
theorem directDivisor_ne_zero (X : Nat) : directDivisor X≠0 := by
  by_cases h : X=0 <;> simp [directDivisor,h]

/-- Repair respects the exact n-bit bound. In particular, the zero input
becomes the representable word one even at the smallest legal width. -/
theorem directDivisor_lt (xs carry : List Wire)
    (hc : carry.length+1=xs.length) (X : Nat) (hx : X<2^xs.length) :
    directDivisor X<2^xs.length := by
  by_cases hz : X=0
  · simp only [directDivisor,hz,if_true]; exact directWidth xs carry hc
  · simpa [directDivisor,hz] using hx

/-- The value witness in the leave contract restores every original word
bit, even when the arithmetic between enter and leave changed other wires. -/
theorem directZeroDivisorLeave_restores_word (xs carry : List Wire) (cin flag : Wire)
    (hn : (flag::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length)
    (original s : State) (m : List Bool) (hcin : s.basis cin=false)
    (hflag : s.basis flag=decide (regValue xs original.basis=0))
    (hword : regValue xs s.basis=directDivisor (regValue xs original.basis))
    (hclean : ∀ q∈carry,s.basis q=false) :
    ∀ q∈xs,(run (directZeroDivisorLeave xs carry cin flag) m s).basis q=
      original.basis q := by
  have h := directZeroDivisorLeave_correct xs carry cin flag hn hc
    (regValue xs original.basis) s m hcin hflag hword hclean
  exact (regValue_eq_iff xs _ _).mp h.2.2.2.1

/-- Enter followed by leave restores the complete state, including phase,
for independent arbitrary measurement records on the two programs. -/
theorem directZeroDivisor_roundtrip (xs carry : List Wire) (cin flag : Wire)
    (hn : (flag::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length)
    (s : State) (enterRecord leaveRecord : List Bool) (hcin : s.basis cin=false)
    (hflag : s.basis flag=false) (hclean : ∀ q∈carry,s.basis q=false) :
    run (directZeroDivisorLeave xs carry cin flag) leaveRecord
      (run (directZeroDivisorEnter xs carry cin flag) enterRecord s)=s := by
  let t := run (directZeroDivisorEnter xs carry cin flag) enterRecord s
  have enter := directZeroDivisorEnter_correct xs carry cin flag hn hc
    s enterRecord hcin hflag hclean
  have leave := directZeroDivisorLeave_correct xs carry cin flag hn hc
    (regValue xs s.basis) t leaveRecord enter.2.2.2.2.1 enter.2.2.1
      enter.2.2.2.1 enter.2.2.2.2.2
  have word := (regValue_eq_iff xs _ _).mp leave.2.2.2.1
  have phase := leave.1.trans enter.1
  have bits : (run (directZeroDivisorLeave xs carry cin flag) leaveRecord t).basis=s.basis := by
    funext q
    by_cases hz : q=flag
    · subst q; exact leave.2.2.1.trans hflag.symm
    · by_cases hx : q∈xs
      · exact word q hx
      · exact (leave.2.1 q hz hx).trans (enter.2.1 q hz hx)
  cases hr : run (directZeroDivisorLeave xs carry cin flag) leaveRecord t
  cases s
  simp_all only

theorem directZeroDivisor_counts (xs carry : List Wire) (cin flag : Wire)
    (hc : carry.length+1=xs.length) :
    toffoliCount (directZeroDivisorEnter xs carry cin flag)=xs.length-1 ∧
    measurementCount (directZeroDivisorEnter xs carry cin flag)=xs.length-2 ∧
    toffoliCount (directZeroDivisorLeave xs carry cin flag)=xs.length-1 ∧
    measurementCount (directZeroDivisorLeave xs carry cin flag)=xs.length-2 := by
  have cmp := ZeroSeededConstantCompare.counts xs carry cin flag hc
  have mask := maskedConstant_counts flag xs 1
  simp [directZeroDivisorEnter,directZeroDivisorLeave,toffoliCount_append,
    measurementCount_append,cmp.1,cmp.2,mask.1,mask.2]

theorem directZeroDivisor_counts_256 (xs carry : List Wire) (cin flag : Wire)
    (hx : xs.length=256) (hc : carry.length=255) :
    toffoliCount (directZeroDivisorEnter xs carry cin flag)=255 ∧
    measurementCount (directZeroDivisorEnter xs carry cin flag)=254 ∧
    toffoliCount (directZeroDivisorLeave xs carry cin flag)=255 ∧
    measurementCount (directZeroDivisorLeave xs carry cin flag)=254 := by
  simpa [hx] using directZeroDivisor_counts xs carry cin flag (by omega)

private theorem directBorrow_wires (bit : Bool) (x cin target : Wire) :
    wires (constantBorrow bit x cin target) ⊆ [target,cin,x].toFinset ∧
    wires (constantBorrowErase bit x cin target) ⊆ [target,cin,x].toFinset := by
  cases bit <;>
    simp [constantBorrow,constantBorrowErase,mappedMajority,mappedEraseCarry,
      wires,Instr.wires,correctionWires,Finset.subset_iff]

private theorem directCompare_wires (xs carry : List Wire) (cin target : Wire) (k : Nat) :
    wires (compareConstantLt xs carry cin target k) ⊆ (target::cin::(xs++carry)).toFinset := by
  induction xs generalizing carry cin k with
  | nil => simp [compareConstantLt,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      intro q hq
      have h := (directBorrow_wires (decide (k%2=1)) x cin target).1 hq
      simpa only [List.mem_toFinset,List.mem_cons,List.mem_singleton,List.mem_append,
        List.not_mem_nil,or_false] using
        (show q=target ∨ q=cin ∨ q=x ∨ q∈carry from by
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h; tauto)
    | cons x' xs =>
      cases carry with
      | nil => simp [compareConstantLt,wires]
      | cons c cs =>
        intro q hq
        simp only [compareConstantLt,wires_append,Finset.mem_union] at hq
        rcases hq with (hq|hq)|hq
        · have h := (directBorrow_wires (decide (k%2=1)) x cin c).1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append]; tauto
        · have h := ih cs c (k/2) hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
        · have h := (directBorrow_wires (decide (k%2=1)) x cin c).2 hq
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append]; tauto

/-- Static support of both halves lies within the declared word, borrow
scratch, cin and one flag. There is no materialized constant register. -/
theorem directZeroDivisor_wires (xs carry : List Wire) (cin flag : Wire) :
    wires (directZeroDivisorEnter xs carry cin flag ++
      directZeroDivisorLeave xs carry cin flag) ⊆ (flag::cin::(xs++carry)).toFinset := by
  intro q hq
  simp only [directZeroDivisorEnter,directZeroDivisorLeave,wires_append,
    Finset.mem_union] at hq
  have cmp : wires (ZeroSeededConstantCompare.program xs carry cin flag) ⊆
      (flag::cin::(xs++carry)).toFinset := by
    intro q hq
    exact directCompare_wires xs carry cin flag 1
      (ZeroSeededConstantCompare.support xs carry cin flag hq)
  have mask := maskedConstant_wires_subset flag xs 1
  rcases hq with (hq|hq)|(hq|hq)
  · exact cmp hq
  · have h := mask hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
  · have h := mask hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
  · exact cmp hq

theorem directZeroDivisor_qubitCount (xs carry : List Wire) (cin flag : Wire)
    (hn : (flag::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length) :
    qubitCount (directZeroDivisorEnter xs carry cin flag ++
      directZeroDivisorLeave xs carry cin flag) ≤ 2*xs.length+1 := by
  have h := Finset.card_le_card (directZeroDivisor_wires xs carry cin flag)
  rw [List.toFinset_card_of_nodup hn] at h
  simp only [List.length_cons,List.length_append] at h
  unfold qubitCount
  omega

end ECDSAAdd.Arithmetic
