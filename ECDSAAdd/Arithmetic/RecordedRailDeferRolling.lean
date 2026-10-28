import ECDSAAdd.Arithmetic.RecordedRailDeferTwoProof

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

/-- Internal prefix invariant to be established by earlier actual gates. It is
not a precondition on the original public inputs or an execution oracle. -/
def PrefixReady (a0 b0 a1 b1 bank : List Wire) (cin q0 q1 : Wire)
    (original : BasisState) (s : State) : Prop :=
  a0.length=b0.length ∧ RecordedRailVented.Aligned a1 b1 bank ∧
    ([cin,q0,q1]++a0++b0++a1++b1++bank).Nodup ∧
    (∀q∈bank,s.basis q=false) ∧ s.basis q1=false ∧ original q0=false ∧
    regValue (b0++[q0]) s.basis=regValue a0 original+regValue b0 original+(original cin).toNat ∧
    (∀q,q∉b0++[q0] → s.basis q=original q)

/-- The prefix's actual live boundary is its original arithmetic overflow. -/
theorem prefix_boundary (a0 b0 : List Wire) (cin q0 : Wire)
    (original : BasisState) (s : State)
    (wide : regValue (b0++[q0]) s.basis=
      regValue a0 original+regValue b0 original+(original cin).toNat) :
    s.basis q0=firstCarry a0 b0 cin original := by
  have high := regValue_highBit b0 q0 s.basis
  rw [wide] at high
  cases hc : s.basis q0 with
  | false =>
    have hn : ¬(2^b0.length ≤ regValue a0 original+regValue b0 original+(original cin).toNat) := by
      intro hp
      have ht := high.mpr hp
      simp only [hc,Bool.false_eq_true] at ht
    simp only [firstCarry,decide_eq_false hn]
  | true =>
    have bound := high.mp hc
    simp [firstCarry,bound]

/-- A rolling step computes the next word on the shared bank, then really
measures the old boundary. Its new phase comes from the original prefix. -/
theorem advance_prefix (a0 b0 a1 b1 bank : List Wire) (cin q0 q1 : Wire)
    (original : BasisState) (s : State) (m : List Bool) (cursor : Nat)
    (ready : PrefixReady a0 b0 a1 b1 bank cin q0 q1 original s) :
    let out := runWithTape (advance a1 b1 bank q0 q1) m cursor s
    out.phase=(s.phase ^^ (m.getD (cursor+a1.length-1) false && firstCarry a0 b0 cin original)) ∧
    regValue ((b0++b1)++[q1]) out.basis=
      regValue (a0++a1) original+regValue (b0++b1) original+(original cin).toNat ∧
    (∀q,q∉(b0++b1)++[q1] → out.basis q=original q) ∧
    (∀q∈bank,out.basis q=false) ∧ out.basis q0=false := by
  obtain ⟨width0,align1,nd,clean,q1clean,q0zero,wide0,outside0⟩ := ready
  obtain ⟨_,nd1,dis0,dis1,q0away⟩ := two_layout a0 b0 a1 b1 bank cin q0 q1 nd
  have currentReady : RecordedRailVented.Ready a1 b1 (some q0) bank q1 s.basis :=
    ⟨align1,nd1,clean,q1clean⟩
  let v := runWithTape (RecordedRailVented.vented a1 b1 (some q0) bank q1) m cursor ⟨s.phase,s.basis⟩
  have result := RecordedRailVented.correct a1 b1 (some q0) bank q1 s.basis s.phase m cursor currentReady
  obtain ⟨phase1,source1,sum1,low1,quotient1,cin1,outside1,work1⟩ := result
  change regValue (b1++[q1]) v.basis=
    regValue a1 s.basis+regValue b1 s.basis+(s.basis q0).toNat at sum1
  have not0 : ∀q∈cin::q1::(a0++a1++b1++bank),q∉b0++[q0] := by
    intro q hq ht
    exact List.disjoint_left.mp dis0 hq ht
  have not1 : ∀q∈cin::q0::(a0++b0++a1++bank),q∉b1++[q1] := by
    intro q hq ht
    exact List.disjoint_left.mp dis1 hq ht
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
  let outBits := writeBit v.basis q0 false
  have hrun : runWithTape (advance a1 b1 bank q0 q1) m cursor s=
      ⟨s.phase ^^ (m.getD (cursor+a1.length-1) false && firstCarry a0 b0 cin original),outBits⟩ := by
    change runWithTape (advance a1 b1 bank q0 q1) m cursor ⟨s.phase,s.basis⟩=_
    dsimp only [outBits,v]
    rw [advance_state a1 b1 bank q0 q1 s.basis s.phase m cursor currentReady,carry]
  have writeSame : ∀q∈(b0++b1)++[q1],outBits q=v.basis q := by
    intro q hq
    have hn : q≠q0 := by intro he; exact q0away (he ▸ hq)
    simp [outBits,writeBit,hn]
  have b0old : regValue b0 v.basis=regValue b0 s.basis :=
    regValue_congr b0 v.basis s.basis (fun q hq => outside1 q (not1 q (by simp [hq])))
  have b0out : regValue b0 outBits=regValue b0 v.basis :=
    regValue_congr b0 outBits v.basis (fun q hq => writeSame q (by simp [hq]))
  have wide1out : regValue (b1++[q1]) outBits=regValue (b1++[q1]) v.basis := by
    apply regValue_congr
    intro q hq
    apply writeSame
    simp only [List.mem_append,List.mem_singleton] at hq ⊢
    tauto
  have a1orig : regValue a1 s.basis=regValue a1 original :=
    regValue_congr a1 s.basis original (fun q hq => outside0 q (not0 q (by simp [hq])))
  have b1orig : regValue b1 s.basis=regValue b1 original :=
    regValue_congr b1 s.basis original (fun q hq => outside0 q (not0 q (by simp [hq])))
  have value : regValue ((b0++b1)++[q1]) outBits=
      regValue (a0++a1) original+regValue (b0++b1) original+(original cin).toNat := by
    rw [List.append_assoc,regValue_append,b0out,b0old,low0,wide1out,sum1,
      a1orig,b1orig,quotient0,regValue_append,regValue_append,width0]
    exact concatenate_value (regValue a0 original) (regValue b0 original)
      (regValue a1 original) (regValue b1 original) (original cin).toNat (2^b0.length)
  have outside : ∀q,q∉(b0++b1)++[q1] → outBits q=original q := by
    intro q hq
    by_cases he : q=q0
    · subst q; simp [outBits,writeBit,q0zero]
    have ht1 : q∉b1++[q1] := by
      intro h
      apply hq
      simp only [List.mem_append,List.mem_singleton] at h ⊢
      tauto
    have ht0 : q∉b0++[q0] := by
      intro h
      simp only [List.mem_append,List.mem_singleton] at h
      rcases h with hb | hc
      · exact hq (by simp [hb])
      · exact he hc
    have nextSame := outside1 q ht1
    change v.basis q=s.basis q at nextSame
    have chain := nextSame.trans (outside0 q ht0)
    simpa [outBits,writeBit,he] using chain
  dsimp only
  rw [hrun]
  refine ⟨rfl,value,outside,?_,?_⟩
  · intro q hq
    change outBits q=false
    have ht0 := not0 q (by simp [hq])
    have ht1 := not1 q (by simp [hq])
    have nextSame := outside1 q ht1
    change v.basis q=s.basis q at nextSame
    have hneq : q≠q0 := by intro he; exact ht0 (by simp [he])
    simpa [outBits,writeBit,hneq] using nextSame.trans (clean q hq)
  · simp [outBits,writeBit]

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.prefix_boundary
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.advance_prefix
