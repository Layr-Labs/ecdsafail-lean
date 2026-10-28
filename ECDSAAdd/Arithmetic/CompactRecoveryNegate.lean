import ECDSAAdd.Arithmetic.PointFlagLayout
import ECDSAAdd.Arithmetic.EqualConstant
import ECDSAAdd.Arithmetic.MappedSources
import ECDSAAdd.Arithmetic.MaskedConstant

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

theorem xorConstant_ones (word : List Wire) :
    xorConstant word (2^word.length-1)=notRegister word := by
  induction word with
  | nil => rfl
  | cons q qs ih =>
    have pos := Nat.two_pow_pos qs.length
    have value : 2^(qs.length+1)-1=2*(2^qs.length-1)+1 := by rw [Nat.pow_succ];omega
    simp only [List.length_cons,value,xorConstant,Nat.add_mod,Nat.mul_mod,Nat.mod_self,
      Nat.zero_mul,Nat.zero_add,Nat.mod_eq_of_lt (by decide : 1<2),if_true]
    have half : (2*(2^qs.length-1)+1)/2=2^qs.length-1 := by omega
    rw [half,ih]
    rfl

structure CompactRecoveryNegateLayout where
  word : List Wire
  work : List Wire
  cin : Wire
  zero : Wire

namespace CompactRecoveryNegateLayout

def wires (L : CompactRecoveryNegateLayout) (control : Wire) : List Wire :=
  control::L.cin::L.zero::(L.word++L.work)
def carries (L : CompactRecoveryNegateLayout) : List Wire := L.work.take (L.word.length-1)
def checkZero (L : CompactRecoveryNegateLayout) (control : Wire) : Program :=
  equalConstant control L.zero (zeroPorts L.word L.work) 0
def complement (L : CompactRecoveryNegateLayout) (control : Wire) : Program :=
  maskedConstant control L.word (2^L.word.length-1)
def add (L : CompactRecoveryNegateLayout) (control : Wire) (k : Nat) : Program :=
  mappedConstAdd (some control) L.word L.carries L.cin k
def program (L : CompactRecoveryNegateLayout) (control : Wire) (p c : Nat) : Program :=
  L.checkZero control++L.complement control++L.add control (p+1)++L.add L.zero c++L.checkZero control

def mutable (L : CompactRecoveryNegateLayout) : List Wire := L.word++[L.zero]
def Frame (L : CompactRecoveryNegateLayout) (base : BasisState) (X : Nat) (Z : Bool)
    (s : BasisState) : Prop := regValue L.word s=X ∧ s L.zero=Z ∧ ∀q,q∉L.mutable → s q=base q

theorem known_away (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (q : Wire) (hq : q∈control::L.cin::L.work) : q∉L.mutable := by
  intro bad
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [wires,mutable,List.count_cons,List.count_append,List.count_nil] at h a b
  omega

theorem zero_away (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) : L.zero∉L.word := by
  intro bad
  have h := List.nodup_iff_count.mp hn L.zero
  have pos := List.count_pos_iff.mpr bad
  simp only [wires,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
  omega

theorem Frame.clean (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (base s : BasisState) (X : Nat) (Z : Bool)
    (hf : L.Frame base X Z s) (hc : regValue L.work base=0) (hi : base L.cin=false) :
    (∀q∈L.work,s q=false) ∧ s L.cin=false ∧ s control=base control := by
  refine ⟨?_,?_,?_⟩
  · intro q hq
    exact (hf.2.2 q (L.known_away control hn q (by simp [hq]))).trans ((regValue_zero _ _).mp hc q hq)
  · exact (hf.2.2 L.cin (L.known_away control hn L.cin (by simp))).trans hi
  · exact hf.2.2 control (L.known_away control hn control (by simp))

theorem checkZero_frame (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length)
    (base : BasisState) (X : Nat) (Z : Bool) (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X Z) (L.checkZero control)
      (L.Frame base X (Z ^^ (base control && decide (X=0)))) := by
  have maps := zeroPorts_maps L.word L.work hw.symm
  have nd : (control::L.zero::(zeroPorts L.word L.work).flatMap ZeroBit.wires).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have eq := (zeroPorts_perm L.word L.work hw.symm).count_eq q
    simp only [wires,List.count_cons,List.count_append] at h ⊢
    rw [eq]
    simp only [List.count_append]
    omega
  have length : (zeroPorts L.word L.work).length=L.word.length := by
    simpa only [List.length_map] using congrArg List.length maps.1
  intro s m hf
  have clean := Frame.clean L control hn base s.basis X Z hf hc hi
  have zeroWork : ∀b∈zeroPorts L.word L.work,s.basis b.work=false := by
    intro b hb
    apply clean.1 b.work
    rw [←maps.2]
    exact List.mem_map.mpr ⟨b,hb,rfl⟩
  have result := equalConstant_correct control L.zero (zeroPorts L.word L.work) 0 nd
    (by rw [length];exact Nat.two_pow_pos _) s m zeroWork
  rw [checkZero,result]
  refine ⟨rfl,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    simp [writeBit,show q≠L.zero from fun bad => L.zero_away control hn (bad ▸ hq)]
  · simp [writeBit,maps.1,hf.1,hf.2.1,clean.2.2]
  · intro q hq
    have ne : q≠L.zero := fun bad => hq (by simp [mutable,bad])
    simpa [writeBit,ne] using hf.2.2 q hq

theorem complement_frame (L : CompactRecoveryNegateLayout) (control : Wire)
    (hn : (L.wires control).Nodup) (base : BasisState) (X : Nat) (Z : Bool)
    (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X Z) (L.complement control)
      (L.Frame base (if base control then 2^L.word.length-1-X else X) Z) := by
  have nd : L.word.Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    simp only [wires,List.count_cons,List.count_append] at h
    omega
  have ctrlAway : control∉L.word := fun bad => L.known_away control hn control (by simp) (by simp [mutable,bad])
  intro s m hf
  have clean := Frame.clean L control hn base s.basis X Z hf hc hi
  simp only [complement,maskedConstant_run control L.word _ ctrlAway,xorConstant_ones,clean.2.2]
  cases hb : base control
  · exact ⟨rfl,hf⟩
  · rw [notRegister_correct L.word nd]
    refine ⟨rfl,?_,?_,?_⟩
    · have value : regValue L.word (fun q => if q∈L.word then !s.basis q else s.basis q)=
          2^L.word.length-1-regValue L.word s.basis := by
        rw [regValue_congr _ _ (fun q => !s.basis q) (by intro q hq;simp [hq]),regValue_complement]
      simpa [hb,hf.1] using value
    · simpa [L.zero_away control hn] using hf.2.1
    · intro q hq
      have notWord : q∉L.word := fun bad => hq (by simp [mutable,bad])
      simpa [notWord] using hf.2.2 q hq

theorem add_frame (L : CompactRecoveryNegateLayout) (control selector : Wire)
    (hn : (L.wires control).Nodup) (hw : L.work.length=L.word.length) (hnpos : 0<L.word.length)
    (hsel : selector=control ∨ selector=L.zero) (k : Nat) (hk : k<2^L.word.length)
    (base : BasisState) (X : Nat) (Z : Bool) (E : Bool)
    (henabled : E=if selector=L.zero then Z else base control)
    (hc : regValue L.work base=0) (hi : base L.cin=false) :
    Triple (L.Frame base X Z) (L.add selector k)
      (L.Frame base (((if E then k else 0)+X)%2^L.word.length) Z) := by
  have nd : (L.cin::L.word++L.carries).Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    have bound := (List.take_sublist (L.word.length-1) L.work).count_le q
    simp only [wires,carries,List.count_cons,List.count_append] at h ⊢
    omega
  have away : ∀q∈some selector,q∉L.cin::L.word++L.carries := by
    intro q hq bad
    have eq : q=selector := by simpa [eq_comm] using hq
    subst q
    have h := List.nodup_iff_count.mp hn selector
    have pos := List.count_pos_iff.mpr bad
    have bound := (List.take_sublist (L.word.length-1) L.work).count_le selector
    simp only [wires,carries,List.count_cons,List.count_append] at h pos
    rcases hsel with rfl|rfl <;> simp only [beq_self_eq_true,if_true] at h <;> omega
  have len : L.carries.length+1=L.word.length := by simp [carries,hw];omega
  intro s m hf
  have clean := Frame.clean L control hn base s.basis X Z hf hc hi
  have selValue : s.basis selector=E := by
    rw [henabled]
    rcases hsel with hsel|hsel
    · subst selector
      have ne : control≠L.zero := by
        intro bad;have h := List.nodup_iff_count.mp hn control
        simp only [wires,bad,List.count_cons,beq_self_eq_true,if_true] at h
        omega
      simp [ne,clean.2.2]
    · rw [hsel]
      simp [hf.2.1]
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct (some selector) L.word L.carries L.cin k nd away len hk s m
    (fun q hq => clean.1 q (List.mem_of_mem_take hq))
  refine ⟨phase,?_,(same L.zero (L.zero_away control hn)).trans hf.2.1,?_⟩
  · simpa [mappedEnabled,selValue,hf.1,clean.2.1] using value
  · intro q hq
    exact (same q (fun bad => hq (by simp [mutable,bad]))).trans (hf.2.2 q hq)

end CompactRecoveryNegateLayout
end ECDSAAdd.Arithmetic
