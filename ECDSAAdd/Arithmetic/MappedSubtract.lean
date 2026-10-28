import ECDSAAdd.Arithmetic.MappedSources

namespace ECDSAAdd.Arithmetic

theorem mappedValue_lt (bits : List MappedBit) (s : BasisState) :
    mappedValue bits s<2^bits.length := by
  induction bits with
  | nil => simp [mappedValue]
  | cons b bits ih =>
    have hb : (b.value s).toNat≤1 := by cases b.value s <;> decide
    simp only [mappedValue,List.length_cons,Nat.pow_succ]
    omega

/-- The source stays implicit, including complemented and repeated reads. -/
def mappedSub (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++mappedAdd bits ys carry cin++notRegister ys

private theorem mapped_complement_sub (X Y N : Nat) (hN : 0<N) (hX : X<N) (hY : Y<N) :
    N-1-((X+(N-1-Y))%N)=(Y+N-X)%N := by
  by_cases less : X≤Y
  · rw [Nat.mod_eq_of_lt (show X+(N-1-Y)<N by omega),
      show Y+N-X=(Y-X)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X+(N-1-Y)=(X-1-Y)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X-1-Y<N by omega),Nat.mod_eq_of_lt (show Y+N-X<N by omega)]
    omega

theorem mappedSub_correct (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hi : s.basis cin=false) :
    (run (mappedSub bits ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (mappedSub bits ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (mappedSub bits ys carry cin) m s).basis=
      (regValue ys s.basis+2^ys.length-mappedValue bits s.basis)%2^ys.length := by
  have nd := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1
  have away (q : Wire) (hq : q∈cin::carry) : q∉ys := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  let s1 : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have first (record : List Bool) : run (notRegister ys) record s=s1 :=
    notRegister_correct ys nd s record
  have keep (q : Wire) (hq : q∉ys) : s1.basis q=s.basis q := by simp [s1,hq]
  have clean : ∀q∈carry,s1.basis q=false := by
    intro q hq
    exact (keep q (away q (by simp [hq]))).trans (hclean q hq)
  have ci : s1.basis cin=false := (keep cin (away cin (by simp))).trans hi
  have src : mappedValue bits s1.basis=mappedValue bits s.basis := by
    apply mappedValue_congr
    intro q hq
    exact keep q (fun bad => hs q hq (by simp [bad]))
  have inverted : regValue ys s1.basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys s1.basis (fun q => !s.basis q) (by intro q hq; simp [s1,hq]),regValue_complement]
  obtain ⟨phase,same,value⟩ := mappedAdd_correct bits ys carry cin hn hs hl hc s1 m clean
  let t := run (mappedAdd bits ys carry cin) m s1
  have flipValue : regValue ys (fun q => if q∈ys then !t.basis q else t.basis q)=
      2^ys.length-1-regValue ys t.basis := by
    rw [regValue_congr ys _ (fun q => !t.basis q) (by intro q hq; simp [hq]),regValue_complement]
  have zeroM := (notRegister_counts ys).2
  simp only [mappedSub,List.append_assoc,run_append,run_take,zeroM,List.take_zero,List.drop_zero]
  rw [first]
  change (run (notRegister ys) _ t).phase=s.phase ∧ _
  rw [notRegister_correct ys nd]
  refine ⟨phase,?_,?_⟩
  · intro q hq
    simp only [hq,if_false]
    exact (same q hq).trans (keep q hq)
  · rw [flipValue,value,src,inverted,ci,Bool.toNat_false,Nat.add_zero]
    apply mapped_complement_sub _ _ _ (Nat.two_pow_pos _)
    · simpa [hl] using mappedValue_lt bits s.basis
    · exact regValue_lt ys s.basis

theorem mappedSub_counts (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (mappedSub bits ys carry cin)=ys.length-1 ∧
    measurementCount (mappedSub bits ys carry cin)=ys.length-1 := by
  have h := mappedAdd_counts bits ys carry cin hl hc
  simp [mappedSub,h.1,h.2,(notRegister_counts ys).1,(notRegister_counts ys).2]

end ECDSAAdd.Arithmetic
