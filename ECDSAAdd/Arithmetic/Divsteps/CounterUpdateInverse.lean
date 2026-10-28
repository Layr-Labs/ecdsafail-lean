import ECDSAAdd.Arithmetic.Divsteps.CounterUpdate

namespace ECDSAAdd.Arithmetic.Divsteps

/-- A physical inverse, using a fresh ripple adder and its own measurement
records. This is not reversal of a gate list containing measurements. -/
def counterUpdateInverse (active swap : Wire) (zero z carry : List Wire) : Program :=
  negateSigned active zero z carry ++ signComplement active z ++ signComplement swap z

def counterPrev (A S : Bool) (Z : Int) : Int :=
  if A then (if S then -Z else Z-1) else Z

def counterInverseWord (n : Nat) (A S : Bool) (Z : Nat) : Nat :=
  signSourceValue n S (signSourceValue n A
    (if A then (2^n-Z)%2^n else Z))

private def CounterState (active swap : Wire) (zero z carry : List Wire)
    (A S : Bool) (Z : Nat) (s : BasisState) : Prop :=
  s active=A ∧ s swap=S ∧ regValue zero s=0 ∧ regValue z s=Z ∧ regValue carry s=0

private theorem complement_spec (active swap q : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hq : q=active ∨ q=swap) (A S : Bool) (Z : Nat) :
    Triple (CounterState active swap zero z carry A S Z)
      (signComplement q z)
      (CounterState active swap zero z carry A S
        (signSourceValue z.length (if q=active then A else S) Z)) := by
  intro s m h
  have outside (a : Wire) (ha : a=active ∨ a=swap ∨ a∈zero ∨ a∈carry) : a∉z := by
    intro hh
    have hn' := List.nodup_iff_count.mp hn a
    have hz' := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append] at hn'
    rcases ha with rfl | rfl | ha | ha
    · simp only [beq_self_eq_true,if_true] at hn'; omega
    · simp only [beq_self_eq_true,if_true] at hn'; omega
    · have := List.count_pos_iff.mpr ha; omega
    · have := List.count_pos_iff.mpr ha; omega
  have znd : z.Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have := List.nodup_iff_count.mp hn a
    simp only [List.count_cons,List.count_append] at this
    omega
  obtain ⟨hp,he,hv⟩ := signComplement_correct q z znd (outside q (by tauto)) s m
  have hqv : s.basis q=(if q=active then A else S) := by
    rcases hq with hq | hq
    · rw [hq]; simp [h.1]
    · rw [hq]
      have hneq : swap≠active := by
        have := (List.nodup_cons.mp hn).1
        simp only [List.mem_cons,not_or] at this
        exact Ne.symm this.1
      simp [hneq,h.2.1]
  exact ⟨hp,(he active (outside active (by tauto))).trans h.1,
    (he swap (outside swap (by tauto))).trans h.2.1,
    (regValue_congr _ _ _ (fun w hw => he w (outside w (by tauto)))).trans h.2.2.1,
    by simpa only [hqv,h.2.2.2.1,signSourceValue] using hv,
    (regValue_congr _ _ _ (fun w hw => he w (outside w (by tauto)))).trans h.2.2.2.2⟩

/-- Modular action with phase, physical controls and clean scratch restored. -/
theorem counterUpdateInverse_spec (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (A S : Bool) (Z : Nat) :
    Triple (fun s => s active=A ∧ s swap=S ∧ regValue zero s=0 ∧
      regValue z s=Z ∧ regValue carry s=0)
      (counterUpdateInverse active swap zero z carry)
      (fun s => s active=A ∧ s swap=S ∧ regValue zero s=0 ∧
        regValue z s=counterInverseWord z.length A S Z ∧ regValue carry s=0) := by
  let Y := if A then (2^z.length-Z)%2^z.length else Z
  have hneg : Triple (CounterState active swap zero z carry A S Z)
      (negateSigned active zero z carry) (CounterState active swap zero z carry A S Y) := by
    intro s m h
    have han : (active::(zero++z++carry)).Nodup := hn.sublist (by simp)
    obtain ⟨hp,ho⟩ := negateSigned_spec active zero z carry han hz hc A Z s m
      ⟨⟨⟨h.1,h.2.2.1⟩,h.2.2.2.1⟩,h.2.2.2.2⟩
    have hs : (run (negateSigned active zero z carry) m s).basis swap=S := by
      refine (negateSigned_frame active zero z carry han hz hc s m h.2.2.1 h.2.2.2.2 swap ?_).trans h.2.1
      have := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      simp only [List.mem_append,not_or] at this
      exact this.1.2
    exact ⟨hp,ho.1.1.1,hs,ho.1.1.2,ho.1.2,ho.2⟩
  have h1 := complement_spec active swap active zero z carry hn (Or.inl rfl) A S Y
  have h2 := complement_spec active swap swap zero z carry hn (Or.inr rfl) A S
    (signSourceValue z.length A Y)
  have hneq : swap≠active := by
    have := (List.nodup_cons.mp hn).1
    simp only [List.mem_cons,not_or] at this
    exact Ne.symm this.1
  simp only [ite_true] at h1
  simp only [if_neg hneq] at h2
  simpa only [counterUpdateInverse,CounterState,counterInverseWord,Y,List.append_assoc] using
    (hneg.seq h1).seq h2

/-- Pure word-level inverse for all representable words, including wraparound. -/
theorem counterInverseWord_forward (n : Nat) (A S : Bool) (Z : Nat)
    (hZ : Z<2^n) (hAS : S=true → A=true) :
    counterInverseWord n A S (counterWord n A S Z)=Z := by
  have hm : 0<2^n := by positivity
  cases A <;> cases S
  · simp [counterInverseWord,counterWord,signSourceValue,Nat.mod_eq_of_lt hZ]
  · simp at hAS
  · by_cases he : Z+1=2^n
    · simp [counterInverseWord,counterWord,signSourceValue,he]
      omega
    · have hlt : Z+1<2^n := by omega
      have hlt2 : 2^n-(Z+1)<2^n := by omega
      simp [counterInverseWord,counterWord,signSourceValue,Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt hlt2]
      omega
  · have he : 2^n-1-Z+1=2^n-Z := by omega
    by_cases hzero : Z=0
    · have he0 : 2^n-1+1=2^n := by omega
      subst Z
      simp [counterInverseWord,counterWord,signSourceValue,he0]
    · have hlt : 2^n-Z<2^n := by omega
      have hdouble : 2^n-(2^n-Z)=Z := by omega
      simp [counterInverseWord,counterWord,signSourceValue,he,Nat.mod_eq_of_lt hlt,
        hdouble,Nat.mod_eq_of_lt hZ]
      omega

private theorem complement_lt (n Z : Nat) (Q : Bool) (hZ : Z<2^n) :
    signSourceValue n Q Z<2^n := by
  have hm : 0<2^n := by positivity
  cases Q with
  | false => exact hZ
  | true => change 2^n-1-Z<2^n; omega

private theorem complement_decode (n Z : Nat) (Q : Bool) (hn : 0<n) (hZ : Z<2^n) :
    signedDecode n (signSourceValue n Q Z)=
      if Q then -signedDecode n Z-1 else signedDecode n Z := by
  cases Q
  · rfl
  · have hm : 2^n=2*2^(n-1) := by
      conv_lhs => rw [show n=n-1+1 by omega,pow_succ]
      omega
    simp only [signSourceValue,if_true,signedDecode]
    split_ifs <;> omega

/-- Signed inverse action under an explicit representable-output obligation.
The excluded minimum-negative negation is not silently treated as integer negation. -/
theorem counterInverseWord_signed (n : Nat) (A S : Bool) (Z : Nat)
    (hn : 0<n) (hZ : Z<2^n) (hAS : S=true → A=true)
    (hlo : -((2^(n-1):Nat):Int)≤counterPrev A S (signedDecode n Z))
    (hhi : counterPrev A S (signedDecode n Z)<((2^(n-1):Nat):Int)) :
    signedDecode n (counterInverseWord n A S Z)=counterPrev A S (signedDecode n Z) := by
  have hr := signedDecode_range n Z hn hZ
  have hneg : -((2^(n-1):Nat):Int)≤(if A then -signedDecode n Z else signedDecode n Z) ∧
      (if A then -signedDecode n Z else signedDecode n Z)<((2^(n-1):Nat):Int) := by
    cases A <;> cases S <;> simp_all [counterPrev]
    omega
  have hzero : signedDecode n 0=0 := by simp [signedDecode]
  have hv := signedWordValue_lift n A Z 0 hn hZ
    (by simpa [signedIntegerValue,hzero] using hneg.1)
    (by simpa [signedIntegerValue,hzero] using hneg.2)
  let V := if A then (2^n-Z)%2^n else Z
  have hV : V<2^n := by
    dsimp only [V]
    split
    · exact Nat.mod_lt _ (by positivity)
    · exact hZ
  have he : V=signedWordValue n A Z 0 := by
    cases A <;> simp [V,signedWordValue,Nat.mod_eq_of_lt hZ]
  have hd : signedDecode n V=(if A then -signedDecode n Z else signedDecode n Z) := by
    rw [he]
    simpa [signedIntegerValue,hzero] using hv
  change signedDecode n (signSourceValue n S (signSourceValue n A V))=_
  rw [complement_decode n _ S hn (complement_lt n V A hV),
    complement_decode n V A hn hV,hd]
  cases A <;> cases S <;> simp_all [counterPrev]

theorem counterUpdateInverse_int_spec (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (A S : Bool) (Z : Int) (hAS : S=true → A=true)
    (hlo : -((2^(z.length-1):Nat):Int)≤counterPrev A S Z)
    (hhi : counterPrev A S Z<((2^(z.length-1):Nat):Int)) :
    Triple (fun s => s active=A ∧ s swap=S ∧ regValue zero s=0 ∧
      signedRegValue z s=Z ∧ regValue carry s=0)
      (counterUpdateInverse active swap zero z carry)
      (fun s => s active=A ∧ s swap=S ∧ regValue zero s=0 ∧
        signedRegValue z s=counterPrev A S Z ∧ regValue carry s=0) := by
  intro s m h
  obtain ⟨hp,ho⟩ := counterUpdateInverse_spec active swap zero z carry hn hz hc A S
    (regValue z s.basis) s m ⟨h.1,h.2.1,h.2.2.1,rfl,h.2.2.2.2⟩
  have hv := counterInverseWord_signed z.length A S (regValue z s.basis) (by omega)
    (regValue_lt z s.basis) hAS
    (by change _≤counterPrev A S (signedRegValue z s.basis); rwa [h.2.2.2.1])
    (by change counterPrev A S (signedRegValue z s.basis)<_; rwa [h.2.2.2.1])
  refine ⟨hp,ho.1,ho.2.1,ho.2.2.1,?_,ho.2.2.2.2⟩
  change signedDecode z.length (regValue z _)=_
  rw [ho.2.2.2.1,hv]
  exact congrArg (counterPrev A S) h.2.2.2.1

/-- Costs of the actual fresh inverse program, not an abstract inverse map. -/
theorem counterUpdateInverse_counts (active swap : Wire) (zero z carry : List Wire)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    toffoliCount (counterUpdateInverse active swap zero z carry)=z.length-1 ∧
    measurementCount (counterUpdateInverse active swap zero z carry)=z.length-1 := by
  have hn := negateSigned_counts active zero z carry hz hc
  have ha := signComplement_counts active z
  have hs := signComplement_counts swap z
  simp [counterUpdateInverse,toffoliCount_append,measurementCount_append,
    hn.1,hn.2,ha.1,ha.2,hs.1,hs.2]

theorem counterUpdateInverse_wires_subset (active swap : Wire) (zero z carry : List Wire)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    wires (counterUpdateInverse active swap zero z carry)⊆(active::swap::(zero++z++carry)).toFinset := by
  rw [counterUpdateInverse,wires_append,wires_append,
    Finset.union_subset_iff,Finset.union_subset_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [negateSigned_wires active zero z carry hz hc]
    intro w hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
    tauto
  · exact (signComplement_wires_subset active z).trans (by
      intro w hw; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢; tauto)
  · exact (signComplement_wires_subset swap z).trans (by
      intro w hw; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢; tauto)

theorem counterUpdateInverse_qubits (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    qubitCount (counterUpdateInverse active swap zero z carry)≤3*z.length+1 := by
  have h := Finset.card_le_card (counterUpdateInverse_wires_subset active swap zero z carry hz hc)
  rw [List.toFinset_card_of_nodup hn] at h
  simp only [List.length_cons,List.length_append] at h
  unfold qubitCount
  omega

theorem counterUpdateInverse_frame (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (s : State) (m : List Bool) (hz0 : regValue zero s.basis=0)
    (hc0 : regValue carry s.basis=0) (w : Wire) (hw : w∉z) :
    (run (counterUpdateInverse active swap zero z carry) m s).basis w=s.basis w := by
  obtain ⟨_,ho⟩ := counterUpdateInverse_spec active swap zero z carry hn hz hc
    (s.basis active) (s.basis swap) (regValue z s.basis) s m ⟨rfl,rfl,hz0,rfl,hc0⟩
  by_cases ha : w=active
  · subst w; exact ho.1
  by_cases hs : w=swap
  · subst w; exact ho.2.1
  by_cases hzero : w∈zero
  · exact (regValue_eq_iff _ _ _).mp (ho.2.2.1.trans hz0.symm) w hzero
  by_cases hcarry : w∈carry
  · exact (regValue_eq_iff _ _ _).mp (ho.2.2.2.2.trans hc0.symm) w hcarry
  apply run_preserves_outside
  intro hh
  have := counterUpdateInverse_wires_subset active swap zero z carry hz hc hh
  simp_all

/-- Independent forward and inverse measurement records restore the entire
state, including phase, controls, source, carries and all untouched wires.
No signed-range premise is needed for the modular round trip. -/
theorem counterUpdateInverse_after_forward (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (s : State) (mF mI : List Bool) (hAS : s.basis swap=true → s.basis active=true)
    (hz0 : regValue zero s.basis=0) (hc0 : regValue carry s.basis=0) :
    run (counterUpdateInverse active swap zero z carry) mI
      (run (counterUpdate active swap zero z carry) mF s)=s := by
  let t := run (counterUpdate active swap zero z carry) mF s
  obtain ⟨hpF,hF⟩ := counterUpdate_spec active swap zero z carry hn hz hc
    (s.basis active) (s.basis swap) (regValue z s.basis) s mF ⟨rfl,rfl,hz0,rfl,hc0⟩
  obtain ⟨hpI,hI⟩ := counterUpdateInverse_spec active swap zero z carry hn hz hc
    (s.basis active) (s.basis swap)
    (counterWord z.length (s.basis active) (s.basis swap) (regValue z s.basis)) t mI hF
  have hv : regValue z (run (counterUpdateInverse active swap zero z carry) mI t).basis=
      regValue z s.basis := hI.2.2.2.1.trans
    (counterInverseWord_forward z.length _ _ _ (regValue_lt z s.basis) hAS)
  have hb : (run (counterUpdateInverse active swap zero z carry) mI t).basis=s.basis := by
    funext w
    by_cases hw : w∈z
    · exact (regValue_eq_iff _ _ _).mp hv w hw
    · exact (counterUpdateInverse_frame active swap zero z carry hn hz hc t mI hF.2.2.1 hF.2.2.2.2 w hw).trans
        (counterUpdate_frame active swap zero z carry hn hz hc s mF hz0 hc0 w hw)
  have hp := hpI.trans hpF
  change run (counterUpdateInverse active swap zero z carry) mI t=s
  cases he : run (counterUpdateInverse active swap zero z carry) mI t
  cases s
  simp_all

/-- Sequential program form uses disjoint portions of the supplied record. -/
theorem counterUpdate_roundTrip (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (s : State) (m : List Bool) (hAS : s.basis swap=true → s.basis active=true)
    (hz0 : regValue zero s.basis=0) (hc0 : regValue carry s.basis=0) :
    run (counterUpdate active swap zero z carry ++ counterUpdateInverse active swap zero z carry) m s=s := by
  rw [run_append,run_take]
  exact counterUpdateInverse_after_forward active swap zero z carry hn hz hc s _ _ hAS hz0 hc0

/-- Inverse frozen execution is an identity despite its static gate schedule. -/
theorem counterUpdateInverse_frozen (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (s : State) (m : List Bool) (ha : s.basis active=false) (hs : s.basis swap=false)
    (hz0 : regValue zero s.basis=0) (hc0 : regValue carry s.basis=0) :
    run (counterUpdateInverse active swap zero z carry) m s=s := by
  have h := counterUpdateInverse_after_forward active swap zero z carry hn hz hc s [] m
    (by simp [hs]) hz0 hc0
  rwa [counterUpdate_frozen active swap zero z carry hn hz hc s [] ha hs hz0 hc0] at h

/-- Full round-trip resources of the same concrete concatenated program. -/
theorem counterUpdate_roundTrip_resources (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    let p := counterUpdate active swap zero z carry ++ counterUpdateInverse active swap zero z carry
    toffoliCount p=2*(z.length-1) ∧ measurementCount p=2*(z.length-1) ∧
      qubitCount p≤3*z.length+1 := by
  dsimp only
  have hf := counterUpdate_counts active swap zero z carry hz hc
  have hi := counterUpdateInverse_counts active swap zero z carry hz hc
  refine ⟨by rw [toffoliCount_append,hf.1,hi.1]; omega,
    by rw [measurementCount_append,hf.2,hi.2]; omega,?_⟩
  have hsub : wires (counterUpdate active swap zero z carry ++
      counterUpdateInverse active swap zero z carry)⊆
      (active::swap::(zero++z++carry)).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨counterUpdate_wires_subset active swap zero z carry hz hc,
      counterUpdateInverse_wires_subset active swap zero z carry hz hc⟩
  have h := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at h
  simp only [List.length_cons,List.length_append] at h
  unfold qubitCount
  omega

end ECDSAAdd.Arithmetic.Divsteps
