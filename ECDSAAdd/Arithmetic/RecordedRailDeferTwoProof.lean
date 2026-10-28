import ECDSAAdd.Arithmetic.RecordedRailDeferTwoLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

/-- Complete two-chunk Defer transition. The shared bank is restored, q0 is
really measured after chunk one, and its phase is the original prefix carry
weighted by that measurement's own absolute tape ordinal. -/
theorem two_correct (a0 b0 a1 b1 bank : List Wire) (cin q0 q1 : Wire)
    (bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : TwoReady a0 b0 a1 b1 bank cin q0 q1 bits) :
    let out := runWithTape (two a0 b0 a1 b1 bank cin q0 q1) m cursor ⟨phase,bits⟩
    out.phase=(phase ^^ (m.getD (cursor+(a0.length-1)+(a1.length-1)) false &&
      firstCarry a0 b0 cin bits)) ∧
    regValue ((b0++b1)++[q1]) out.basis=
      regValue (a0++a1) bits+regValue (b0++b1) bits+(bits cin).toNat ∧
    (∀q,q∉(b0++b1)++[q1] → out.basis q=bits q) ∧
    (∀q∈bank,out.basis q=false) ∧ out.basis q0=false ∧ out.basis cin=bits cin ∧
    regValue (a0++a1) out.basis=regValue (a0++a1) bits := by
  obtain ⟨align0,align1,nd,clean,hq0,hq1⟩ := ready
  obtain ⟨nd0,nd1,dis0,dis1,q0away⟩ := two_layout a0 b0 a1 b1 bank cin q0 q1 nd
  have ready0 : RecordedRailVented.Ready a0 b0 (some cin) bank q0 bits :=
    ⟨align0,nd0,clean,hq0⟩
  let t0 := runWithTape (RecordedRailVented.vented a0 b0 (some cin) bank q0) m cursor ⟨phase,bits⟩
  have result0 := RecordedRailVented.correct a0 b0 (some cin) bank q0 bits phase m cursor ready0
  obtain ⟨phase0,source0,sum0,low0,quotient0,cin0,outside0,work0⟩ := result0
  change t0.phase=phase at phase0
  change regValue b0 t0.basis=(regValue a0 bits+regValue b0 bits+(bits cin).toNat)%2^b0.length at low0
  change (t0.basis q0).toNat=(regValue a0 bits+regValue b0 bits+(bits cin).toNat)/2^b0.length at quotient0
  have not0 : ∀q∈cin::q1::(a0++a1++b1++bank),q∉b0++[q0] := by
    intro q hq ht
    exact List.disjoint_left.mp dis0 hq ht
  have not1 : ∀q∈cin::q0::(a0++b0++a1++bank),q∉b1++[q1] := by
    intro q hq ht
    exact List.disjoint_left.mp dis1 hq ht
  have q1clean : t0.basis q1=false :=
    (outside0 q1 (not0 q1 (by simp))).trans hq1
  have ready1 : RecordedRailVented.Ready a1 b1 (some q0) bank q1 t0.basis :=
    ⟨align1,nd1,work0,q1clean⟩
  let cur1 := cursor+(a0.length-1)
  let v1 := runWithTape (RecordedRailVented.vented a1 b1 (some q0) bank q1)
    m cur1 ⟨t0.phase,t0.basis⟩
  have result1 := RecordedRailVented.correct a1 b1 (some q0) bank q1 t0.basis t0.phase m cur1 ready1
  obtain ⟨phase1,source1,sum1,low1,quotient1,cin1,outside1,work1⟩ := result1
  change regValue (b1++[q1]) v1.basis=
    regValue a1 t0.basis+regValue b1 t0.basis+(t0.basis q0).toNat at sum1
  have carry0 : t0.basis q0=firstCarry a0 b0 cin bits :=
    first_carry a0 b0 bank cin q0 bits phase m cursor ready0
  let outBits := writeBit v1.basis q0 false
  have hrun : runWithTape (two a0 b0 a1 b1 bank cin q0 q1) m cursor ⟨phase,bits⟩=
      ⟨phase ^^ (m.getD (cursor+(a0.length-1)+(a1.length-1)) false && firstCarry a0 b0 cin bits),outBits⟩ := by
    have counts0 := RecordedRailVented.counts a0 b0 bank
      (RecordedRailVented.aligned_shape a0 b0 bank align0) (some cin) q0
    rw [two,runWithTape_append,counts0.2]
    change runWithTape (advance a1 b1 bank q0 q1) m cur1 ⟨t0.phase,t0.basis⟩=_
    dsimp only [outBits,v1]
    rw [advance_state a1 b1 bank q0 q1 t0.basis t0.phase m cur1 ready1]
    have ordinal : cur1+a1.length-1=cursor+(a0.length-1)+(a1.length-1) := by
      have positive : 0<a1.length := align1.1
      dsimp only [cur1]
      omega
    rw [ordinal,phase0,carry0]
  have writeSame : ∀q∈(b0++b1)++[q1],outBits q=v1.basis q := by
    intro q hq
    have hn : q≠q0 := by intro he; exact q0away (he ▸ hq)
    simp [outBits,writeBit,hn]
  have b0old : regValue b0 v1.basis=regValue b0 t0.basis :=
    regValue_congr b0 v1.basis t0.basis (fun q hq => outside1 q (not1 q (by simp [hq])))
  have b0out : regValue b0 outBits=regValue b0 v1.basis :=
    regValue_congr b0 outBits v1.basis (fun q hq => writeSame q (by simp [hq]))
  have wide1out : regValue (b1++[q1]) outBits=regValue (b1++[q1]) v1.basis := by
    apply regValue_congr
    intro q hq
    apply writeSame
    simp only [List.mem_append,List.mem_singleton] at hq ⊢
    tauto
  have a1orig : regValue a1 t0.basis=regValue a1 bits :=
    regValue_congr a1 t0.basis bits (fun q hq => outside0 q (not0 q (by simp [hq])))
  have b1orig : regValue b1 t0.basis=regValue b1 bits :=
    regValue_congr b1 t0.basis bits (fun q hq => outside0 q (not0 q (by simp [hq])))
  have value : regValue ((b0++b1)++[q1]) outBits=
      regValue (a0++a1) bits+regValue (b0++b1) bits+(bits cin).toNat := by
    rw [List.append_assoc,regValue_append,b0out,b0old,low0,wide1out,sum1,
      a1orig,b1orig,quotient0,regValue_append,regValue_append]
    rw [←align0.2.1]
    exact concatenate_value (regValue a0 bits) (regValue b0 bits)
      (regValue a1 bits) (regValue b1 bits) (bits cin).toNat (2^b0.length)
  have outside : ∀q,q∉(b0++b1)++[q1] → outBits q=bits q := by
    intro q hq
    by_cases he : q=q0
    · subst q; simp [outBits,writeBit,hq0]
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
    have firstSame := outside0 q ht0
    change v1.basis q=t0.basis q at nextSame
    change t0.basis q=bits q at firstSame
    have chain := nextSame.trans firstSame
    simpa [outBits,writeBit,he] using chain
  have protectedPort : ∀q∈cin::(a0++a1++bank),q∉(b0++b1)++[q1] := by
    intro q hq ht
    have h0 : q∉b0++[q0] := not0 q (by
      simp only [List.mem_cons,List.mem_append] at hq ⊢
      tauto)
    have h1 : q∉b1++[q1] := not1 q (by
      simp only [List.mem_cons,List.mem_append] at hq ⊢
      tauto)
    simp only [List.mem_append,List.mem_singleton] at ht h0 h1
    tauto
  dsimp only
  rw [hrun]
  refine ⟨rfl,value,outside,?_,?_,?_,?_⟩
  · intro q hq
    change outBits q=false
    rw [outside q (protectedPort q
      (List.mem_cons_of_mem cin (List.mem_append_right (a0++a1) hq)))]
    exact clean q hq
  · simp [outBits,writeBit]
  · exact outside cin (protectedPort cin (by simp))
  · apply regValue_congr
    intro q hq
    exact outside q (protectedPort q
      (List.mem_cons_of_mem cin (List.mem_append_left bank hq)))

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.two_correct
