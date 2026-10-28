import ECDSAAdd.Arithmetic.SignedWordBits

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Exact conditional two's-complement negation. The clean source and carries
are reusable across both rows; the control doubles as the adder carry-in. -/
def negateSigned (q : Wire) (zero y carry : List Wire) : Program :=
  signComplement q y ++ addInPlace zero y carry q

theorem negateSigned_spec (q : Wire) (zero y carry : List Wire)
    (hn : (q::(zero++y++carry)).Nodup) (hz : zero.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (Y : Nat) :
    {{ q=Q,zero=0,y=Y,carry=0 }} negateSigned q zero y carry
    {{ q=Q,zero=0,y=(if Q then (2^y.length-Y)%2^y.length else Y),carry=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have outside (a : Wire) (ha : a=q ∨ a∈zero ∨ a∈carry) : a∉y := by
    intro hy
    have hh := List.nodup_iff_count.mp hn a
    have hy' := List.count_pos_iff.mpr hy
    simp only [List.count_cons,List.count_append] at hh
    rcases ha with rfl | ha | ha
    · simp only [beq_self_eq_true,if_true] at hh; omega
    · have := List.count_pos_iff.mpr ha; omega
    · have := List.count_pos_iff.mpr ha; omega
  have hynd : y.Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have := List.nodup_iff_count.mp hn a
    simp only [List.count_cons,List.count_append] at this
    omega
  have hY : Y<2^y.length := by rw [← h.1.2]; exact regValue_lt y s.basis
  let t := run (signComplement q y) m s
  obtain ⟨hp,he,hv⟩ := signComplement_correct q y hynd (outside q (Or.inl rfl)) s m
  have hq : t.basis q=Q := (he q (outside q (by tauto))).trans h.1.1.1
  have hz0 : regValue zero t.basis=0 :=
    (regValue_congr _ _ _ (fun a ha => he a (outside a (by tauto)))).trans h.1.1.2
  have hc0 : regValue carry t.basis=0 :=
    (regValue_congr _ _ _ (fun a ha => he a (outside a (by tauto)))).trans h.2
  have hy : regValue y t.basis=(if Q then 2^y.length-1-Y else Y) := by
    simpa only [h.1.1.1,h.1.2] using hv
  obtain ⟨hp2,ho⟩ := addInPlace_spec zero y carry q hn hz hc 0
    (if Q then 2^y.length-1-Y else Y) Q t m ⟨⟨⟨hz0,hy⟩,hq⟩,hc0⟩
  rw [negateSigned,run_append,run_take, (signComplement_counts q y).2, List.drop_zero]
  simp only [Holds.holds] at ho
  refine ⟨hp2.trans hp,⟨⟨⟨ho.1.2,ho.1.1.1⟩,?_⟩,ho.2⟩⟩
  rw [ho.1.1.2]
  cases Q
  · simpa using Nat.mod_eq_of_lt hY
  · simp only [Bool.toNat_true,if_true,zero_add]
    congr 1
    omega

theorem negateSigned_counts (q : Wire) (zero y carry : List Wire)
    (hz : zero.length=y.length) (hc : carry.length+1=y.length) :
    toffoliCount (negateSigned q zero y carry)=y.length-1 ∧
    measurementCount (negateSigned q zero y carry)=y.length-1 := by
  have hs := signComplement_counts q y
  have ha := addInPlace_counts zero y carry q hz hc
  simp [negateSigned,toffoliCount_append,measurementCount_append,hs.1,hs.2,ha.1,ha.2]

/-- Signed correctness excludes the most-negative overflow only when negating.
All bounds are explicit obligations of the calling divstep invariant. -/
theorem negateSigned_int_spec (q : Wire) (zero y carry : List Wire)
    (hn : (q::(zero++y++carry)).Nodup) (hz : zero.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (A : Int)
    (hlo : -((2^(y.length-1):Nat):Int) ≤ (if Q then -A else A))
    (hhi : (if Q then -A else A) < ((2^(y.length-1):Nat):Int)) :
    Triple (fun s => s q=Q ∧ regValue zero s=0 ∧ signedRegValue y s=A ∧ regValue carry s=0)
      (negateSigned q zero y carry)
      (fun s => s q=Q ∧ regValue zero s=0 ∧
        signedRegValue y s=(if Q then -A else A) ∧ regValue carry s=0) := by
  intro s m h
  let Y := regValue y s.basis
  have hY : Y<2^y.length := regValue_lt y s.basis
  have hA : signedDecode y.length Y=A := h.2.2.1
  have hzero : signedDecode y.length 0=0 := by simp [signedDecode]
  have hval : signedIntegerValue Q (signedDecode y.length Y) (signedDecode y.length 0)=
      (if Q then -A else A) := by rw [hA,hzero]; cases Q <;> simp [signedIntegerValue]
  have hv := signedWordValue_lift y.length Q Y 0 (by omega) hY
    (by rw [hval]; exact hlo) (by rw [hval]; exact hhi)
  rw [hval] at hv
  have he : (if Q then (2^y.length-Y)%2^y.length else Y)=
      signedWordValue y.length Q Y 0 := by
    cases Q <;> simp [signedWordValue,Nat.mod_eq_of_lt hY]
  obtain ⟨hp,ho⟩ := negateSigned_spec q zero y carry hn hz hc Q Y s m
    ⟨⟨⟨h.1,h.2.1⟩,rfl⟩,h.2.2.2⟩
  simp only [Holds.holds] at ho
  refine ⟨hp,ho.1.1.1,ho.1.1.2,?_,ho.2⟩
  unfold signedRegValue
  rw [ho.1.2,he]
  exact hv

theorem negateSigned_wires (q : Wire) (zero y carry : List Wire)
    (hz : zero.length=y.length) (hc : carry.length+1=y.length) :
    wires (negateSigned q zero y carry)=(q::(zero++y++carry)).toFinset := by
  rw [negateSigned,wires_append,addInPlace_wires zero y carry q hz hc]
  apply Finset.union_eq_right.mpr
  intro w hw
  have hh := signComplement_wires_subset q y hw
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
  tauto

theorem negateSigned_frame (q : Wire) (zero y carry : List Wire)
    (hn : (q::(zero++y++carry)).Nodup) (hz : zero.length=y.length)
    (hc : carry.length+1=y.length) (s : State) (m : List Bool)
    (hz0 : regValue zero s.basis=0) (hc0 : regValue carry s.basis=0)
    (w : Wire) (hw : w∉y) :
    (run (negateSigned q zero y carry) m s).basis w=s.basis w := by
  obtain ⟨_,ho⟩ := negateSigned_spec q zero y carry hn hz hc (s.basis q)
    (regValue y s.basis) s m ⟨⟨⟨rfl,hz0⟩,rfl⟩,hc0⟩
  simp only [Holds.holds] at ho
  by_cases hq : w=q
  · subst w; exact ho.1.1.1
  by_cases hzero : w∈zero
  · exact (regValue_eq_iff _ _ _).mp (ho.1.1.2.trans hz0.symm) w hzero
  by_cases hcarry : w∈carry
  · exact (regValue_eq_iff _ _ _).mp (ho.2.trans hc0.symm) w hcarry
  apply run_preserves_outside
  rw [negateSigned_wires q zero y carry hz hc]
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

end ECDSAAdd.Arithmetic.Divsteps
