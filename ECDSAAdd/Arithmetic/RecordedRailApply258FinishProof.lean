import ECDSAAdd.Arithmetic.RecordedRailApply258Wrapped

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply258
open RecordedRailDefer

private theorem truncate_value (A0 B0 A1 B1 cin M K : Nat)
    (small : (A0+B0+cin)%M+M*((A1+B1+(A0+B0+cin)/M)%K)<M*K) :
    (A0+B0+cin)%M+M*((A1+B1+(A0+B0+cin)/M)%K)=
      ((A0+M*A1)+(B0+M*B1)+cin)%(M*K) := by
  have whole := concatenate_value A0 B0 A1 B1 cin M
  have split := Nat.mod_add_div (A1+B1+(A0+B0+cin)/M) K
  have decomposition : (A0+M*A1)+(B0+M*B1)+cin=
      ((A0+B0+cin)%M+M*((A1+B1+(A0+B0+cin)/M)%K))+
        (M*K)*((A1+B1+(A0+B0+cin)/M)/K) := by
    calc
      _=(A0+B0+cin)%M+M*(A1+B1+(A0+B0+cin)/M) := whole.symm
      _=(A0+B0+cin)%M+M*((A1+B1+(A0+B0+cin)/M)%K+
          K*((A1+B1+(A0+B0+cin)/M)/K)) :=
        congrArg (fun t => (A0+B0+cin)%M+M*t) split.symm
      _=_ := by ring
  rw [decomposition,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]

/-- Last-word rolling transition: wrapped arithmetic followed by actual bare
MX returns both the prefix boundary and bank clean, with the seventh debt. -/
theorem finish_prefix (a0 b0 a1 b1 bank : List Wire) (cin q0 q1 : Wire)
    (original : BasisState) (s : State) (m : List Bool) (cursor : Nat)
    (ready : PrefixWrappedReady a0 b0 a1 b1 bank cin q0 q1 original s) :
    let out := runWithTape (finish a1 b1 bank q0) m cursor s
    out.phase=(s.phase ^^ (m.getD (cursor+(a1.length-2)) false && firstCarry a0 b0 cin original)) ∧
    regValue (b0++b1) out.basis=
      (regValue (a0++a1) original+regValue (b0++b1) original+(original cin).toNat)%2^(b0.length+b1.length) ∧
    (∀q,q∉b0++b1 → out.basis q=original q) ∧
    (∀q∈bank,out.basis q=false) ∧ out.basis q0=false := by
  obtain ⟨width0,positive1,width1,bankWidth,nd,clean,q0zero,wide0,outside0⟩ := ready
  obtain ⟨_,nd1,dis0,dis1,q0away⟩ := two_layout a0 b0 a1 b1 bank cin q0 q1 nd
  have ndWork : ([q0]++a1++b1++bank).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd1 q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have currentReady : WrappedReady a1 b1 bank q0 s.basis :=
    ⟨positive1,width1,bankWidth,ndWork,clean⟩
  let r := runWithTape (RecordedRailRipple.ripple a1 b1 (some q0) bank
    (List.replicate (a1.length-2) none)) m cursor ⟨s.phase,s.basis⟩
  have result := wrapped_result a1 b1 bank q0 s.basis s.phase m cursor currentReady
  obtain ⟨phase1,source1,sum1,outside1,work1⟩ := result
  change regValue b1 r.basis=
    (regValue a1 s.basis+regValue b1 s.basis+(s.basis q0).toNat)%2^b1.length at sum1
  have not0 : ∀q∈cin::q1::(a0++a1++b1++bank),q∉b0++[q0] := by
    intro q hq ht
    exact List.disjoint_left.mp dis0 hq ht
  have not1 : ∀q∈cin::q0::(a0++b0++a1++bank),q∉b1 := by
    intro q hq ht
    exact List.disjoint_left.mp dis1 hq (List.mem_append_left _ ht)
  have carry := prefix_boundary a0 b0 cin q0 original s wide0
  have low0 : regValue b0 s.basis=
      (regValue a0 original+regValue b0 original+(original cin).toNat)%2^b0.length := by
    rw [←wide0]
    exact regValue_low b0 q0 s.basis
  have quotient0 : (s.basis q0).toNat=
      (regValue a0 original+regValue b0 original+(original cin).toNat)/2^b0.length := by
    rw [←wide0,regValue_append,Nat.add_mul_div_left _ _ (Nat.two_pow_pos b0.length),
      Nat.div_eq_of_lt (regValue_lt b0 s.basis),Nat.zero_add]
    cases hc : s.basis q0 <;> simp [regValue,hc]
  let outBits := writeBit r.basis q0 false
  have hrun : runWithTape (finish a1 b1 bank q0) m cursor s=
      ⟨s.phase ^^ (m.getD (cursor+(a1.length-2)) false && firstCarry a0 b0 cin original),outBits⟩ := by
    change runWithTape (finish a1 b1 bank q0) m cursor ⟨s.phase,s.basis⟩=_
    dsimp only [outBits,r]
    rw [finish_state a1 b1 bank q0 s.basis s.phase m cursor currentReady,carry]
  have q0data : q0∉b0++b1 := by
    intro h
    exact q0away (List.mem_append_left _ h)
  have writeSame : ∀q∈b0++b1,outBits q=r.basis q := by
    intro q hq
    have hn : q≠q0 := by intro he; exact q0data (he ▸ hq)
    simp [outBits,writeBit,hn]
  have b0old : regValue b0 r.basis=regValue b0 s.basis :=
    regValue_congr b0 r.basis s.basis (fun q hq => outside1 q (not1 q (by simp [hq])))
  have b0out : regValue b0 outBits=regValue b0 r.basis :=
    regValue_congr b0 outBits r.basis (fun q hq => writeSame q (by simp [hq]))
  have b1out : regValue b1 outBits=regValue b1 r.basis :=
    regValue_congr b1 outBits r.basis (fun q hq => writeSame q (by simp [hq]))
  have a1orig : regValue a1 s.basis=regValue a1 original :=
    regValue_congr a1 s.basis original (fun q hq => outside0 q (not0 q (by simp [hq])))
  have b1orig : regValue b1 s.basis=regValue b1 original :=
    regValue_congr b1 s.basis original (fun q hq => outside0 q (not0 q (by simp [hq])))
  have value : regValue (b0++b1) outBits=
      (regValue a0 original+regValue b0 original+(original cin).toNat)%2^b0.length+
        2^b0.length*((regValue a1 original+regValue b1 original+
          (regValue a0 original+regValue b0 original+(original cin).toNat)/2^b0.length)%2^b1.length) := by
    rw [regValue_append,b0out,b0old,low0,b1out,sum1,a1orig,b1orig,quotient0]
  have total : regValue (b0++b1) outBits=
      (regValue (a0++a1) original+regValue (b0++b1) original+(original cin).toNat)%2^(b0.length+b1.length) := by
    have small := regValue_lt (b0++b1) outBits
    rw [value] at small
    simp only [List.length_append,Nat.pow_add] at small
    rw [value,regValue_append,regValue_append,width0,Nat.pow_add]
    exact truncate_value (regValue a0 original) (regValue b0 original)
      (regValue a1 original) (regValue b1 original) (original cin).toNat
      (2^b0.length) (2^b1.length) small
  have outside : ∀q,q∉b0++b1 → outBits q=original q := by
    intro q hq
    by_cases he : q=q0
    · subst q; simp [outBits,writeBit,q0zero]
    have ht1 : q∉b1 := fun h => hq (List.mem_append_right _ h)
    have ht0 : q∉b0++[q0] := by
      intro h
      simp only [List.mem_append,List.mem_singleton] at h
      rcases h with hb | hc
      · exact hq (List.mem_append_left _ hb)
      · exact he hc
    have nextSame := outside1 q ht1
    change r.basis q=s.basis q at nextSame
    simpa [outBits,writeBit,he] using nextSame.trans (outside0 q ht0)
  dsimp only
  rw [hrun]
  refine ⟨rfl,total,outside,?_,?_⟩
  · intro q hq
    change outBits q=false
    have ht0 := not0 q (by simp [hq])
    have ht1 := not1 q (by simp [hq])
    have nextSame := outside1 q ht1
    change r.basis q=s.basis q at nextSame
    have hneq : q≠q0 := by intro he; exact ht0 (by simp [he])
    simpa [outBits,writeBit,hneq] using nextSame.trans (clean q hq)
  · simp [outBits,writeBit]

end ECDSAAdd.Arithmetic.RecordedRailApply258
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.finish_prefix
