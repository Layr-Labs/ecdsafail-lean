import ECDSAAdd.Arithmetic.MeasuredStreamedResources

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- Normalize one raw word without storing the literal modulus in qubits.
The branch bit is retained until the original source is restored. -/
structure MeasuredSourceNormalizeLayout where
  word : List Wire
  carry : List Wire
  cin : Wire
  flag : Wire

namespace MeasuredSourceNormalizeLayout

def wires (L : MeasuredSourceNormalizeLayout) : List Wire := L.flag::L.cin::(L.word++L.carry)
def mutable (L : MeasuredSourceNormalizeLayout) : List Wire := L.word++[L.flag]
def Frame (L : MeasuredSourceNormalizeLayout) (base : BasisState) (V : Nat) (F : Bool)
    (s : BasisState) : Prop :=
  regValue L.word s=V ∧ s L.flag=F ∧ ∀q,q∉L.mutable → s q=base q

def normalize (L : MeasuredSourceNormalizeLayout) (p c : Nat) : Program :=
  compareConstantGe L.word L.carry L.cin L.flag p++
    mappedConstAdd (some L.flag) L.word L.carry L.cin c
def restore (L : MeasuredSourceNormalizeLayout) (p : Nat) : Program :=
  mappedConstAdd (some L.flag) L.word L.carry L.cin p++
    compareConstantGe L.word L.carry L.cin L.flag p

def reflect (L : MeasuredSourceNormalizeLayout) (p : Nat) : Program :=
  notRegister L.word++mappedConstAdd none L.word L.carry L.cin p

theorem canonical_and_restore (B p c X : Nat) (hpc : p+c=B) (hc : 0<c)
    (hcp : c<p) (hX : X<B) :
    ((if p≤X then c else 0)+X)%B=X%p ∧
    ((if p≤X then p else 0)+X%p)%B=X ∧ X%p<p := by
  have hp : 0<p := by omega
  refine ⟨?_,?_,Nat.mod_lt _ hp⟩
  · by_cases small : X<p
    · rw [if_neg (by omega),Nat.zero_add,Nat.mod_eq_of_lt hX,Nat.mod_eq_of_lt small]
    · have hx : X%p=X-p := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      rw [if_pos (by omega),hx,show c+X=(X-p)+B by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  · by_cases small : X<p
    · rw [if_neg (by omega),Nat.mod_eq_of_lt small,Nat.zero_add,Nat.mod_eq_of_lt hX]
    · have hx : X%p=X-p := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      rw [if_pos (by omega),hx,show p+(X-p)=X by omega,Nat.mod_eq_of_lt hX]

theorem protected_away (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.cin::L.carry) : q∉L.mutable := by
  intro bad
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [wires,mutable,List.count_cons,List.count_append,List.count_nil] at h a b
  omega

theorem flag_away (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup) :
    L.flag∉L.word := by
  intro bad
  have h := List.nodup_iff_count.mp hn L.flag
  have b := List.count_pos_iff.mpr bad
  simp only [wires,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
  omega

theorem Frame.clean (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (base s : BasisState) (V : Nat) (F : Bool) (hf : L.Frame base V F s)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    (∀q∈L.carry,s q=false) ∧ s L.cin=false := by
  constructor
  · intro q hq
    exact (hf.2.2 q (L.protected_away hn q (by simp [hq]))).trans (hc q hq)
  · exact (hf.2.2 L.cin (L.protected_away hn L.cin (by simp))).trans hi

theorem ge_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (p : Nat) (hp : p<2^L.word.length)
    (base : BasisState) (V : Nat) (F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base V F) (compareConstantGe L.word L.carry L.cin L.flag p)
      (L.Frame base V (F ^^ decide (p≤V))) := by
  intro s m hf
  have clean := Frame.clean L hn base s.basis V F hf hc hi
  obtain ⟨phase,same,value⟩ := compareConstantGe_correct L.word L.carry L.cin L.flag p hn hl hp s m clean.2 clean.1
  refine ⟨phase,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => same q (fun bad => L.flag_away hn (bad ▸ hq)))).trans hf.1
  · simpa [hf.1,hf.2.1] using value
  · intro q hq
    exact (same q (fun bad => hq (by simp [mutable,bad]))).trans (hf.2.2 q hq)

theorem add_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (k : Nat) (hk : k<2^L.word.length)
    (base : BasisState) (V : Nat) (F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base V F) (mappedConstAdd (some L.flag) L.word L.carry L.cin k)
      (L.Frame base (((if F then k else 0)+V)%2^L.word.length) F) := by
  have nd : (L.cin::L.word++L.carry).Nodup := (List.nodup_cons.mp hn).2
  have away : ∀q∈some L.flag,q∉L.cin::L.word++L.carry := by
    intro q hq
    have e : q=L.flag := by simpa [eq_comm] using hq
    subst q
    exact (List.nodup_cons.mp hn).1
  intro s m hf
  have clean := Frame.clean L hn base s.basis V F hf hc hi
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct (some L.flag) L.word L.carry L.cin k nd away hl hk s m clean.1
  refine ⟨phase,?_,(same L.flag (L.flag_away hn)).trans hf.2.1,?_⟩
  · simpa [mappedEnabled,hf.1,hf.2.1,clean.2] using value
  · intro q hq
    have awayWord : q∉L.word := fun bad => hq (by simp [mutable,bad])
    exact (same q awayWord).trans (hf.2.2 q hq)

theorem normalize_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (p c X : Nat)
    (hpc : p+c=2^L.word.length) (hcpos : 0<c) (hcp : c<p) (hX : X<2^L.word.length)
    (base : BasisState) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base X false) (L.normalize p c)
      (L.Frame base (X%p) (decide (p≤X))) := by
  have hp : p<2^L.word.length := by omega
  have cb : c<2^L.word.length := by omega
  have ge := L.ge_frame hn hl p hp base X false hc hi
  have add := L.add_frame hn hl c cb base X (decide (p≤X)) hc hi
  have math := canonical_and_restore (2^L.word.length) p c X hpc hcpos hcp hX
  have eq : ((if decide (p≤X) then c else 0)+X)%2^L.word.length=X%p := by
    simpa using math.1
  simp only [Bool.false_xor] at ge
  rw [eq] at add
  exact ge.seq add

theorem restore_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (p c X : Nat)
    (hpc : p+c=2^L.word.length) (hcpos : 0<c) (hcp : c<p) (hX : X<2^L.word.length)
    (base : BasisState) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base (X%p) (decide (p≤X))) (L.restore p)
      (L.Frame base X false) := by
  have hp : p<2^L.word.length := by omega
  have add := L.add_frame hn hl p hp base (X%p) (decide (p≤X)) hc hi
  have ge := L.ge_frame hn hl p hp base X (decide (p≤X)) hc hi
  have math := canonical_and_restore (2^L.word.length) p c X hpc hcpos hcp hX
  have eq : ((if decide (p≤X) then p else 0)+X%p)%2^L.word.length=X := by
    simpa using math.2.1
  rw [eq] at add
  simp only [Bool.xor_self] at ge
  exact add.seq ge

theorem not_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (base : BasisState) (V : Nat) (F : Bool) :
    Triple (L.Frame base V F) (notRegister L.word)
      (L.Frame base (2^L.word.length-1-V) F) := by
  have nd : L.word.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [wires,List.count_cons,List.count_append] at h
    omega
  intro s m hf
  rw [notRegister_correct L.word nd]
  refine ⟨rfl,?_,?_,?_⟩
  · have val : regValue L.word (fun q => if q∈L.word then !s.basis q else s.basis q)=
        2^L.word.length-1-regValue L.word s.basis := by
      rw [regValue_congr L.word _ (fun q => !s.basis q) (by intro q hq; simp [hq]),regValue_complement]
    exact val.trans (by rw [hf.1])
  · simpa [L.flag_away hn] using hf.2.1
  · intro q hq
    have out : q∉L.word := fun bad => hq (by simp [mutable,bad])
    simpa [out] using hf.2.2 q hq

theorem literal_add_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (k : Nat) (hk : k<2^L.word.length)
    (base : BasisState) (V : Nat) (F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base V F) (mappedConstAdd none L.word L.carry L.cin k)
      (L.Frame base ((k+V)%2^L.word.length) F) := by
  have nd : (L.cin::L.word++L.carry).Nodup := (List.nodup_cons.mp hn).2
  intro s m hf
  have clean := Frame.clean L hn base s.basis V F hf hc hi
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct none L.word L.carry L.cin k nd
    (by simp) hl hk s m clean.1
  refine ⟨phase,?_,(same L.flag (L.flag_away hn)).trans hf.2.1,?_⟩
  · simpa [mappedEnabled,hf.1,clean.2] using value
  · intro q hq
    have out : q∉L.word := fun bad => hq (by simp [mutable,bad])
    exact (same q out).trans (hf.2.2 q hq)

/-- Exact canonical reflection, including zero and p-1. Carries and every
wire outside the output are restored; measurement records are arbitrary. -/
theorem reflect_frame (L : MeasuredSourceNormalizeLayout) (hn : L.wires.Nodup)
    (hl : L.carry.length+1=L.word.length) (p V : Nat)
    (hp : p<2^L.word.length) (hV : V<p) (base : BasisState) (F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base V F) (L.reflect p) (L.Frame base (p-1-V) F) := by
  have inv := L.not_frame hn base V F
  have add := L.literal_add_frame hn hl p hp base (2^L.word.length-1-V) F hc hi
  have math : (p+(2^L.word.length-1-V))%2^L.word.length=p-1-V := by
    have eq : p+(2^L.word.length-1-V)=(p-1-V)+2^L.word.length := by omega
    rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  rw [math] at add
  exact inv.seq add

end MeasuredSourceNormalizeLayout
end ECDSAAdd.Arithmetic
