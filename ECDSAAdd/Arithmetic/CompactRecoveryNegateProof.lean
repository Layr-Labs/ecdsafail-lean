import ECDSAAdd.Arithmetic.CompactRecoveryNegate
import ECDSAAdd.Math.CompactRecoveryNegate
import ECDSAAdd.Arithmetic.MeasuredGateSupport

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout

theorem program_frame (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (npos : 0<L.word.length)
    (p c X : Nat) (hpc : p+c=2^L.word.length) (hcpos : 1<c) (hX : X<p)
    (base : BasisState) (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X false) (L.program control p c)
      (L.Frame base (if base control then (p-X)%p else X) false) := by
  let B := base control
  let D := B && decide (X=0)
  let X1 := if B then 2^L.word.length-1-X else X
  let X2 := ((if B then p+1 else 0)+X1)%2^L.word.length
  let X3 := ((if D then c else 0)+X2)%2^L.word.length
  have pcBound : p+1<2^L.word.length := by omega
  have cBound : c<2^L.word.length := by omega
  have ne : control≠L.zero := by
    intro bad;have h := List.nodup_iff_count.mp hn control
    simp only [wires,bad,List.count_cons,beq_self_eq_true,if_true] at h
    omega
  have zero := L.checkZero_frame control hn hw base X false hc hi
  simp only [Bool.false_xor] at zero
  have flip := L.complement_frame control hn base X D hc hi
  have add1 := L.add_frame control control hn hw npos (Or.inl rfl) (p+1) pcBound base X1 D B
    (by simp [ne,B]) hc hi
  have add2 := L.add_frame control L.zero hn hw npos (Or.inr rfl) c cBound base X2 D D
    (by simp) hc hi
  have clear := L.checkZero_frame control hn hw base X3 D hc hi
  have eq : X3=(if B then (p-X)%p else X) :=
    compactNegateValue_exact _ p c X B hpc hcpos hX
  have sameZero : (B && decide (X3=0))=D :=
    compactNegateValue_zero _ p c X B hpc hcpos hX
  change Triple (L.Frame base X3 D) (L.checkZero control)
    (L.Frame base X3 (D ^^ (B && decide (X3=0)))) at clear
  rw [sameZero,Bool.xor_self] at clear
  have all := (((zero.seq flip).seq add1).seq add2).seq clear
  rw [eq] at all
  exact all

/-- Direct exact canonical negation; the zero input is restored to zero,
all shared work/control sites and phase return for every measurement record. -/
theorem program_correct (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (npos : 0<L.word.length)
    (p c X : Nat) (hpc : p+c=2^L.word.length) (hcpos : 1<c) (hX : X<p)
    (s : State) (records : List Bool) (hx : regValue L.word s.basis=X)
    (hc : regValue L.work s.basis=0) (hi : s.basis L.cin=false) (hz : s.basis L.zero=false) :
    (run (L.program control p c) records s).phase=s.phase ∧
    regValue L.word (run (L.program control p c) records s).basis=
      (if s.basis control then (p-X)%p else X) ∧
    ∀q,q∉L.word → (run (L.program control p c) records s).basis q=s.basis q := by
  have pre : L.Frame s.basis X false s.basis := ⟨hx,hz,fun _ _ => rfl⟩
  have result := L.program_frame control hn hw npos p c X hpc hcpos hX s.basis hc hi s records pre
  refine ⟨result.1,result.2.1,?_⟩
  intro q hq
  by_cases zero : q=L.zero
  · subst q;exact result.2.2.1.trans hz.symm
  · exact result.2.2.2 q (by simpa only [mutable,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using And.intro hq zero)

theorem program_counts (L : CompactRecoveryNegateLayout) (control : Wire) (p c : Nat)
    (hw : L.work.length=L.word.length) (npos : 0<L.word.length) :
    toffoliCount (L.program control p c)=4*L.word.length-2 ∧
    measurementCount (L.program control p c)=4*L.word.length-2 := by
  have maps := zeroPorts_maps L.word L.work hw.symm
  have len : (zeroPorts L.word L.work).length=L.word.length := by
    simpa only [List.length_map] using congrArg List.length maps.1
  have carryLen : L.carries.length+1=L.word.length := by simp [carries,hw];omega
  have zero := equalConstant_counts control L.zero (zeroPorts L.word L.work) 0
  have flip := maskedConstant_counts control L.word (2^L.word.length-1)
  have add1 := mappedConstAdd_counts (some control) L.word L.carries L.cin (p+1) carryLen
  have add2 := mappedConstAdd_counts (some L.zero) L.word L.carries L.cin c carryLen
  simp only [program,checkZero,complement,add,toffoliCount_append,measurementCount_append,
    zero.1,zero.2,flip.1,flip.2,add1.1,add1.2,add2.1,add2.2,len]
  constructor <;> omega

theorem program_support (L : CompactRecoveryNegateLayout) (control : Wire) (p c : Nat)
    (hw : L.work.length=L.word.length) :
    ECDSAAdd.wires (L.program control p c)⊆(L.wires control).toFinset := by
  have eq := equalConstant_wires control L.zero (zeroPorts L.word L.work) 0
  have perm := zeroPorts_perm L.word L.work hw.symm
  have zero : ECDSAAdd.wires (L.checkZero control)⊆(L.wires control).toFinset := by
    rw [checkZero,eq,List.toFinset_cons,List.toFinset_cons,List.toFinset_eq_of_perm _ _ perm]
    intro q hq
    simp [wires] at hq ⊢
    tauto
  have flip := maskedConstant_wires_subset control L.word (2^L.word.length-1)
  have add1 := mappedConstAdd_wires_subset (some control) L.word L.carries L.cin (p+1)
  have add2 := mappedConstAdd_wires_subset (some L.zero) L.word L.carries L.cin c
  have embed (q : Wire) (hq : q∈L.carries) : q∈L.work := List.mem_of_mem_take hq
  have flipS : ECDSAAdd.wires (L.complement control)⊆(L.wires control).toFinset := by
    intro q hq;have h := flip hq
    simp [wires] at h ⊢
    tauto
  have one : ECDSAAdd.wires (L.add control (p+1))⊆(L.wires control).toFinset := by
    intro q hq;have h := add1 hq
    simp [wires] at h ⊢
    have ht : q∈L.carries → q∈L.work := embed q
    tauto
  have two : ECDSAAdd.wires (L.add L.zero c)⊆(L.wires control).toFinset := by
    intro q hq;have h := add2 hq
    simp [wires] at h ⊢
    have ht : q∈L.carries → q∈L.work := embed q
    tauto
  simpa only [program,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro zero flipS) one) two) zero

def reflection (L : CompactRecoveryNegateLayout) (control : Wire) (p : Nat) : Program :=
  L.complement control++L.add control p

/-- Conditional canonical reflection is the exact frame for fused reverse
subtraction: adding the classical offset+1 finishes offset-X without a
separate zero test or temporary quantum coordinate. -/
theorem reflection_frame (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (npos : 0<L.word.length)
    (p X : Nat) (hp : p<2^L.word.length) (hX : X<p)
    (base : BasisState) (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X false) (L.reflection control p)
      (L.Frame base (if base control then p-1-X else X) false) := by
  have ne : control≠L.zero := by
    intro bad;have h := List.nodup_iff_count.mp hn control
    simp only [wires,bad,List.count_cons,beq_self_eq_true,if_true] at h
    omega
  let V := if base control then 2^L.word.length-1-X else X
  have flip := L.complement_frame control hn base X false hc hi
  have add := L.add_frame control control hn hw npos (Or.inl rfl) p hp base V false (base control)
    (by simp [ne]) hc hi
  have value : ((if base control then p else 0)+V)%2^L.word.length=
      (if base control then p-1-X else X) := by
    cases hb : base control
    · simp [V,hb,Nat.mod_eq_of_lt (hX.trans hp)]
    · have eq : p+(2^L.word.length-1-X)=2^L.word.length+(p-1-X) := by omega
      simp only [V,hb,if_true]
      rw [eq,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
  rw [value] at add
  exact flip.seq add

theorem reflection_correct (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (npos : 0<L.word.length)
    (p X : Nat) (hp : p<2^L.word.length) (hX : X<p)
    (s : State) (records : List Bool) (hx : regValue L.word s.basis=X)
    (hc : regValue L.work s.basis=0) (hi : s.basis L.cin=false) (hz : s.basis L.zero=false) :
    (run (L.reflection control p) records s).phase=s.phase ∧
    regValue L.word (run (L.reflection control p) records s).basis=(if s.basis control then p-1-X else X) ∧
    ∀q,q∉L.word → (run (L.reflection control p) records s).basis q=s.basis q := by
  have pre : L.Frame s.basis X false s.basis := ⟨hx,hz,fun _ _ => rfl⟩
  have result := L.reflection_frame control hn hw npos p X hp hX s.basis hc hi s records pre
  refine ⟨result.1,result.2.1,?_⟩
  intro q hq
  by_cases zero : q=L.zero
  · subst q;exact result.2.2.1.trans hz.symm
  · exact result.2.2.2 q (by simpa only [mutable,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using And.intro hq zero)

theorem reflection_counts (L : CompactRecoveryNegateLayout) (control : Wire) (p : Nat)
    (hw : L.work.length=L.word.length) (npos : 0<L.word.length) :
    toffoliCount (L.reflection control p)=L.word.length-1 ∧
    measurementCount (L.reflection control p)=L.word.length-1 := by
  have carryLen : L.carries.length+1=L.word.length := by simp [carries,hw];omega
  have add := mappedConstAdd_counts (some control) L.word L.carries L.cin p carryLen
  have flip := maskedConstant_counts control L.word (2^L.word.length-1)
  simp [reflection,complement,CompactRecoveryNegateLayout.add,add.1,add.2,flip.1,flip.2]

theorem reflection_support (L : CompactRecoveryNegateLayout) (control : Wire) (p : Nat) :
    ECDSAAdd.wires (L.reflection control p)⊆(L.wires control).toFinset := by
  have flip := maskedConstant_wires_subset control L.word (2^L.word.length-1)
  have add := mappedConstAdd_wires_subset (some control) L.word L.carries L.cin p
  have a : ECDSAAdd.wires (L.complement control)⊆(L.wires control).toFinset := by
    intro q hq;have h := flip hq;simp [wires] at h ⊢;tauto
  have b : ECDSAAdd.wires (L.add control p)⊆(L.wires control).toFinset := by
    intro q hq;have h := add hq
    have take : q∈L.carries → q∈L.work := List.mem_of_mem_take
    simp [wires] at h ⊢
    tauto
  simpa only [reflection,wires_append,Finset.union_subset_iff] using And.intro a b

end ECDSAAdd.Arithmetic.CompactRecoveryNegateLayout
