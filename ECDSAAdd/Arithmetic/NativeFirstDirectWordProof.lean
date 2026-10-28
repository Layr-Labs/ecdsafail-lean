import ECDSAAdd.Arithmetic.NativeFirstDirectAddProof

set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] mappedAdd run hAdd kTail kAdd

private theorem block_one (w : Nat → Wire) (a : Nat) :
    wireBlock w a 1=[w a] := by simp [wireBlock,List.range']

private theorem cons_value (h : Wire) (r : List Wire) (s : BasisState) :
    regValue (h::r) s=(s h).toNat+2*regValue r s := by
  cases hb : s h <;> simp [regValue,hb]

private theorem low_one_mod (C T : Nat) (b : Bool) (hc : C%2=1) :
    (!b).toNat+2*((C/2+T+b.toNat)%2^257)=(b.toNat+2*T+C)%2^258 := by
  have split := Nat.mod_add_div C 2
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true,Bool.not_false,
    Bool.not_true,Nat.add_zero] <;> omega

/-- Abstract basis-state proof: no embedded gate program is normalized. -/
private theorem toggle_head_value (h : Wire) (r : List Wire) (s : BasisState)
    (ha : h∉r) :
    regValue (h::r) (writeBit s h (!(s h)))=(!s h).toNat+2*regValue r s := by
  have head : (writeBit s h (!(s h))) h=!(s h) := by simp [writeBit]
  have tail : regValue r (writeBit s h (!(s h)))=regValue r s := by
    apply regValue_congr
    intro q hq
    have ne : q≠h := by intro e; subst q; exact ha hq
    simp [writeBit,ne]
  rw [cons_value,head,tail]

/-- A high-slice addition, including preservation of the untouched low slice. -/
private theorem high_value (lo hi : List Wire) (s t : BasisState) (C : Nat)
    (low : regValue lo t=regValue lo s)
    (high : regValue hi t=(C+regValue hi s)%2^hi.length)
    (fit : regValue (lo++hi) s+2^lo.length*C<2^(lo.length+hi.length)) :
    regValue (lo++hi) t=regValue (lo++hi) s+2^lo.length*C := by
  have pos : 0<2^lo.length := Nat.two_pow_pos _
  have bound : C+regValue hi s<2^hi.length := by
    rw [regValue_append,Nat.pow_add] at fit
    nlinarith
  rw [regValue_append,low,high,Nat.mod_eq_of_lt bound,regValue_append]
  ring

/-- Actual H word arithmetic, phase, and full frame for every independent tape.
The three untouched low H bits cannot carry when the fixed increment is /8. -/
theorem hAdd_word (w : Nat → Wire) (s : State) (m : List Bool)
    (hn : (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup)
    (hs : ∀q∈mappedWires (hBits w false),
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252))
    (hc : ∀q∈wireBlock w 1540 252,s.basis q=false)
    (hcin : s.basis (w 1797)=false)
    (hl : ∀q∈wireBlock w 1 3,q∉wireBlock w 4 253)
    (fit : regValue (wireBlock w 1 256) s.basis+
      (if s.basis (w 1028) then hConstant else 0)<2^256) :
    (run (hAdd w false) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 4 253 → (run (hAdd w false) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 1 256) (run (hAdd w false) m s).basis=
      regValue (wireBlock w 1 256) s.basis+
        (if s.basis (w 1028) then hConstant else 0) := by
  have a := hAdd_spec w false s m hn hs hc
  refine ⟨a.1,a.2.1,?_⟩
  have low := regValue_congr (wireBlock w 1 3) _ s.basis
    (fun q hq => a.2.1 q (hl q hq))
  have high : regValue (wireBlock w 4 253) (run (hAdd w false) m s).basis=
      ((if s.basis (w 1028) then hConstant/8 else 0)+
        regValue (wireBlock w 4 253) s.basis)%2^253 := by
    simpa [hcin] using a.2.2
  have mult : 8*(if s.basis (w 1028) then hConstant/8 else 0)=
      (if s.basis (w 1028) then hConstant else 0) := by
    cases s.basis (w 1028) <;> simp
    have z := hConstant_low_zero
    omega
  have split := wireBlock_append w 1 3 253
  have f : regValue (wireBlock w 1 3++wireBlock w 4 253) s.basis+
      2^(wireBlock w 1 3).length*(if s.basis (w 1028) then hConstant/8 else 0)<
      2^((wireBlock w 1 3).length+(wireBlock w 4 253).length) := by
    simpa [wireBlock_length,split,mult] using fit
  have out := high_value (wireBlock w 1 3) (wireBlock w 4 253) s.basis
    (run (hAdd w false) m s).basis _ low
    (by simpa [wireBlock_length] using high) f
  simpa [wireBlock_length,split,mult] using out

/-- Full K word: the retained head is the tail carry-in, then the final X
implements the low-one constant. All other wires and incoming phase return. -/
theorem kAdd_word (w : Nat → Wire) (s : State) (m : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀q∈mappedWires (kBits w false),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    (run (kAdd w false) m s).phase=s.phase ∧
    (∀q,q∉wireBlock w 770 258 → (run (kAdd w false) m s).basis q=s.basis q) ∧
    regValue (wireBlock w 770 258) (run (kAdd w false) m s).basis=
      (regValue (wireBlock w 770 258) s.basis+
        kConstant false (s.basis (w 1028)))%2^258 := by
  let u := run (kTail w false) (m.take (measurementCount (kTail w false))) s
  have a := kTail_spec w false s (m.take (measurementCount (kTail w false))) hn hs hc
  have hb : w 770∉wireBlock w 771 257 := by
    intro h
    exact (List.nodup_cons.mp hn).1 (List.mem_append_left _ h)
  have head : u.basis (w 770)=s.basis (w 770) := a.2.1 _ hb
  have split : w 770::wireBlock w 771 257=wireBlock w 770 258 := by
    simpa [block_one] using wireBlock_append w 770 1 257
  rw [kAdd_run]
  refine ⟨a.1,?_,?_⟩
  · intro q hq
    have hq0 : q≠w 770 := by intro e; subst q; exact hq (by rw [←split]; simp)
    have hqt : q∉wireBlock w 771 257 := by intro h; exact hq (by rw [←split]; simp [h])
    simpa [u,writeBit,hq0] using a.2.1 q hqt
  · rw [←split,toggle_head_value (w 770) (wireBlock w 771 257) u.basis hb,head]
    have value := a.2.2
    change regValue (wireBlock w 771 257) u.basis=_ at value
    rw [value,cons_value]
    have parity := kConstant_low_one false (s.basis (w 1028))
    exact low_one_mod _ _ _ parity

/-- The actual three Clifford gates set both coherent transcript bits. -/
theorem front_spec (w : Nat → Wire) (s : State) (m : List Bool)
    (hne : w 0≠w 1028) (ha : s.basis (w 0)=false)
    (hs : s.basis (w 1028)=false) :
    run [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] m s=
      ⟨s.phase,writeBit (writeBit s.basis (w 1028) (s.basis (w 770)))
        (w 0) (!(s.basis (w 770)))⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=w 0
  · subst q
    simp [run,writeBit,ha,hs,hne,Ne.symm hne]
  by_cases ht : q=w 1028
  · subst q
    simp [run,writeBit,ha,hs,hne,Ne.symm hne]
  simp [run,writeBit,ha,hs,hne,Ne.symm hne,hq,ht]

/-- The low-bit clear is coherent and preserves every other bit and phase. -/
theorem clear_spec (w : Nat → Wire) (s : State) (m : List Bool)
    (h : s.basis (w 770)=s.basis (w 1028)) :
    run [.CX (w 1028) (w 770)] m s=
      ⟨s.phase,writeBit s.basis (w 770) false⟩ := by
  simp only [run,h,Bool.xor_self]

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.hAdd_word
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kAdd_word

#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.front_spec
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.clear_spec
