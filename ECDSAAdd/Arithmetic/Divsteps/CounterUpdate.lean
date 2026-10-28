import ECDSAAdd.Arithmetic.Divsteps.SignedNegate
import ECDSAAdd.Math.Divsteps.Bounds

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Update the signed z counter using physical active and swap controls.
The active bit is the carry-in; no additional control scratch is needed. -/
def counterUpdate (active swap : Wire) (zero z carry : List Wire) : Program :=
  signComplement swap z ++ addInPlace zero z carry active

def counterNext (active swap : Bool) (Z : Int) : Int :=
  if active then (if swap then -Z else Z+1) else Z

def counterWord (n : Nat) (active swap : Bool) (Z : Nat) : Nat :=
  ((if swap then 2^n-1-Z else Z)+active.toNat)%2^n

/-- Modular correctness, phase preservation and scratch restoration for every
measurement record. The controls need not satisfy swap⇒active for this lemma. -/
theorem counterUpdate_spec (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (A S : Bool) (Z : Nat) :
    Triple (fun s => s active=A ∧ s swap=S ∧ regValue zero s=0 ∧
      regValue z s=Z ∧ regValue carry s=0)
      (counterUpdate active swap zero z carry)
      (fun s => s active=A ∧ s swap=S ∧ regValue zero s=0 ∧
        regValue z s=counterWord z.length A S Z ∧ regValue carry s=0) := by
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
  have han : (active::(zero++z++carry)).Nodup := by
    exact hn.sublist (by simp)
  have hsw : swap∉(active::(zero++z++carry)) := by
    have h1 := (List.nodup_cons.mp hn).1
    have h2 := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    simp only [List.mem_cons] at h1 ⊢
    tauto
  let t := run (signComplement swap z) m s
  obtain ⟨hp,he,hv⟩ := signComplement_correct swap z znd (outside swap (by tauto)) s m
  have ha : t.basis active=A := (he active (outside active (by tauto))).trans h.1
  have hs : t.basis swap=S := (he swap (outside swap (by tauto))).trans h.2.1
  have hz0 : regValue zero t.basis=0 :=
    (regValue_congr _ _ _ (fun a ha => he a (outside a (by tauto)))).trans h.2.2.1
  have hc0 : regValue carry t.basis=0 :=
    (regValue_congr _ _ _ (fun a ha => he a (outside a (by tauto)))).trans h.2.2.2.2
  have hv' : regValue z t.basis=(if S then 2^z.length-1-Z else Z) := by
    simpa only [h.2.1,h.2.2.2.1] using hv
  obtain ⟨hp2,ho⟩ := addInPlace_spec zero z carry active han hz hc 0
    (if S then 2^z.length-1-Z else Z) A t m ⟨⟨⟨hz0,hv'⟩,ha⟩,hc0⟩
  have hs2 : (run (addInPlace zero z carry active) m t).basis swap=S := by
    refine (run_preserves_outside _ _ _ _ ?_).trans hs
    rw [addInPlace_wires zero z carry active hz hc]
    simpa only [List.mem_toFinset] using hsw
  rw [counterUpdate,run_append,run_take,(signComplement_counts swap z).2,List.drop_zero]
  exact ⟨hp2.trans hp,ho.1.2,hs2,ho.1.1.1,by simpa [counterWord] using ho.1.1.2,ho.2⟩

/-- Only one ripple adder is needed for both branches. -/
theorem counterUpdate_counts (active swap : Wire) (zero z carry : List Wire)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    toffoliCount (counterUpdate active swap zero z carry)=z.length-1 ∧
    measurementCount (counterUpdate active swap zero z carry)=z.length-1 := by
  have hs := signComplement_counts swap z
  have ha := addInPlace_counts zero z carry active hz hc
  simp [counterUpdate,toffoliCount_append,measurementCount_append,hs.1,hs.2,ha.1,ha.2]

theorem counterUpdate_wires_subset (active swap : Wire) (zero z carry : List Wire)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    wires (counterUpdate active swap zero z carry)⊆(active::swap::(zero++z++carry)).toFinset := by
  rw [counterUpdate,wires_append,Finset.union_subset_iff]
  constructor
  · exact (signComplement_wires_subset swap z).trans (by intro w hw; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢; tauto)
  · rw [addInPlace_wires zero z carry active hz hc]
    intro w hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
    tauto

/-- Every bit outside the target counter is restored, including both controls,
zero source and carries. -/
theorem counterUpdate_frame (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (s : State) (m : List Bool) (hz0 : regValue zero s.basis=0)
    (hc0 : regValue carry s.basis=0) (w : Wire) (hw : w∉z) :
    (run (counterUpdate active swap zero z carry) m s).basis w=s.basis w := by
  obtain ⟨_,ho⟩ := counterUpdate_spec active swap zero z carry hn hz hc
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
  have := counterUpdate_wires_subset active swap zero z carry hz hc hh
  simp_all

/-- The signed lift uses the caller's no-overflow bounds. Two or more bits
ensure that the increment operand 1 is positive in signed representation. -/
theorem counterWord_signed (n : Nat) (A S : Bool) (Z : Nat)
    (hn : 2≤n) (hZ : Z<2^n) (hAS : S=true → A=true)
    (hlo : -((2^(n-1):Nat):Int)≤counterNext A S (signedDecode n Z))
    (hhi : counterNext A S (signedDecode n Z)<((2^(n-1):Nat):Int)) :
    signedDecode n (counterWord n A S Z)=counterNext A S (signedDecode n Z) := by
  have hzero : signedDecode n 0=0 := by simp [signedDecode]
  have hpow : 1<2^(n-1) := by
    have := Nat.pow_le_pow_right (by omega : 1≤(2:Nat)) (by omega : 1≤n-1)
    norm_num at this ⊢
    omega
  have hone : signedDecode n 1=1 := by simp [signedDecode,hpow]
  have hpowN : 1<2^n := lt_of_lt_of_le hpow
    (Nat.pow_le_pow_right (by omega) (by omega))
  cases A <;> cases S
  · simp [counterWord,counterNext,Nat.mod_eq_of_lt hZ]
  · simp at hAS
  · have hv := signedWordValue_lift n false 1 Z (by omega) (by omega)
      (by simpa [signedIntegerValue,counterNext,hone] using hlo)
      (by simpa [signedIntegerValue,counterNext,hone] using hhi)
    simpa [counterWord,counterNext,signedWordValue,signedIntegerValue,hone] using hv
  · have hv := signedWordValue_lift n true Z 0 (by omega) hZ
      (by simpa [signedIntegerValue,counterNext,hzero] using hlo)
      (by simpa [signedIntegerValue,counterNext,hzero] using hhi)
    have he : 2^n-1-Z+1=2^n-Z := by omega
    simpa [counterWord,counterNext,signedWordValue,signedIntegerValue,hzero,he] using hv

theorem counterUpdate_int_spec (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hw : 2≤z.length) (A S : Bool) (Z : Int) (hAS : S=true → A=true)
    (hlo : -((2^(z.length-1):Nat):Int)≤counterNext A S Z)
    (hhi : counterNext A S Z<((2^(z.length-1):Nat):Int)) :
    Triple (fun s => s active=A ∧ s swap=S ∧ regValue zero s=0 ∧
      signedRegValue z s=Z ∧ regValue carry s=0)
      (counterUpdate active swap zero z carry)
      (fun s => s active=A ∧ s swap=S ∧ regValue zero s=0 ∧
        signedRegValue z s=counterNext A S Z ∧ regValue carry s=0) := by
  intro s m h
  obtain ⟨hp,ho⟩ := counterUpdate_spec active swap zero z carry hn hz hc A S
    (regValue z s.basis) s m ⟨h.1,h.2.1,h.2.2.1,rfl,h.2.2.2.2⟩
  have hv := counterWord_signed z.length A S (regValue z s.basis) hw
    (regValue_lt z s.basis) hAS
    (by change _≤counterNext A S (signedRegValue z s.basis); rwa [h.2.2.2.1])
    (by change counterNext A S (signedRegValue z s.basis)<_; rwa [h.2.2.2.1])
  refine ⟨hp,ho.1,ho.2.1,ho.2.2.1,?_,ho.2.2.2.2⟩
  change signedDecode z.length (regValue z _)=_
  rw [ho.2.2.2.1,hv]
  exact congrArg (counterNext A S) h.2.2.2.1

/-- Static allocation including both physical controls, the target, zero source
and ripple carries. These scratch rows may be reused by neighboring components. -/
theorem counterUpdate_qubits (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    qubitCount (counterUpdate active swap zero z carry)≤3*z.length+1 := by
  have h := Finset.card_le_card (counterUpdate_wires_subset active swap zero z carry hz hc)
  rw [List.toFinset_card_of_nodup hn] at h
  simp only [List.length_cons,List.length_append] at h
  unfold qubitCount
  omega

/-- Frozen execution is the identity on the entire state, for every record. -/
theorem counterUpdate_frozen (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (s : State) (m : List Bool) (ha : s.basis active=false) (hs : s.basis swap=false)
    (hz0 : regValue zero s.basis=0) (hc0 : regValue carry s.basis=0) :
    run (counterUpdate active swap zero z carry) m s=s := by
  obtain ⟨hp,ho⟩ := counterUpdate_spec active swap zero z carry hn hz hc
    false false (regValue z s.basis) s m ⟨ha,hs,hz0,rfl,hc0⟩
  have hv : regValue z (run (counterUpdate active swap zero z carry) m s).basis=
      regValue z s.basis := by
    simpa [counterWord,Nat.mod_eq_of_lt (regValue_lt z s.basis)] using ho.2.2.2.1
  have hb : (run (counterUpdate active swap zero z carry) m s).basis=s.basis := by
    funext w
    by_cases hw : w∈z
    · exact (regValue_eq_iff _ _ _).mp hv w hw
    · exact counterUpdate_frame active swap zero z carry hn hz hc s m hz0 hc0 w hw
  cases he : run (counterUpdate active swap zero z carry) m s
  cases s
  simp_all

/-- A deterministic width obligation derived from |z|≤t, without a paper's
probabilistic or fixed six-bit assumption. -/
theorem counterNext_bounds (A S : Bool) (Z : Int) (t n : Nat)
    (hlo : -(t:Int)≤Z) (hhi : Z≤(t:Int)) (hw : t+1<2^(n-1)) :
    -((2^(n-1):Nat):Int)≤counterNext A S Z ∧
      counterNext A S Z<((2^(n-1):Nat):Int) := by
  cases A <;> cases S <;> simp only [counterNext,Bool.false_eq_true,if_false,if_true]
  all_goals constructor <;> omega

/-- Sufficient width for every update before a horizon T. This is a capacity
statement only: it does not assert that a divsteps walk has terminated. -/
theorem counter_width_before (T n t : Nat) (hT : T<2^(n-1)) (ht : t<T) :
    2≤n ∧ t+1<2^(n-1) := by
  have hn : 2≤n := by
    by_contra hh
    have he : n-1=0 := by omega
    simp only [he,pow_zero] at hT
    omega
  exact ⟨hn,by omega⟩

/-- Eleven signed bits suffice for the conservative 590-step horizon;
this deliberately does not use a six-bit counter assumption. -/
theorem counter_width_590 (t : Nat) (ht : t<590) :
    2≤11 ∧ t+1<2^(11-1) :=
  counter_width_before 590 11 t (by norm_num) ht

/-- Logical controls expected from the caller's finite-register predicates. -/
def counterActive (s : ECDSAAdd.Divsteps.ZState) : Bool := decide (s.g≠0)
def counterSwap (s : ECDSAAdd.Divsteps.ZState) : Bool :=
  counterActive s && decide (0≤s.z ∧ s.g%2=1)

theorem counterSwap_active (s : ECDSAAdd.Divsteps.ZState) :
    counterSwap s=true → counterActive s=true := by
  simp only [counterSwap,Bool.and_eq_true]
  tauto

theorem counterNext_zStep (s : ECDSAAdd.Divsteps.ZState) :
    counterNext (counterActive s) (counterSwap s) s.z=
      (if s.g=0 then s else ECDSAAdd.Divsteps.zStep s).z := by
  by_cases hg : s.g=0
  · simp [counterNext,counterActive,hg]
  · by_cases hs : 0≤s.z ∧ s.g%2=1 <;>
      simp [counterNext,counterSwap,counterActive,ECDSAAdd.Divsteps.zStep,hg,hs]

/-- Direct connection to the canonical frozen integer walk. The caller must
compute the two physical controls; this component updates only z. -/
theorem counterUpdate_walk_spec (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (p x : Int) (hp : 0≤p) (hx0 : 0≤x) (hxp : x≤p)
    (T t : Nat) (ht : t<T) (hw : T<2^(z.length-1)) :
    let a := ECDSAAdd.Divsteps.zWalk p x t
    let b := ECDSAAdd.Divsteps.zWalk p x (t+1)
    Triple (fun s => s active=counterActive a ∧ s swap=counterSwap a ∧
      regValue zero s=0 ∧ signedRegValue z s=a.z ∧ regValue carry s=0)
      (counterUpdate active swap zero z carry)
      (fun s => s active=counterActive a ∧ s swap=counterSwap a ∧
        regValue zero s=0 ∧ signedRegValue z s=b.z ∧ regValue carry s=0) := by
  dsimp only
  have hb := ECDSAAdd.Divsteps.zWalk_bounds p x hp hx0 hxp t
  obtain ⟨hn2,htw⟩ := counter_width_before T z.length t hw ht
  have hr := counterNext_bounds
    (counterActive (ECDSAAdd.Divsteps.zWalk p x t))
    (counterSwap (ECDSAAdd.Divsteps.zWalk p x t))
    (ECDSAAdd.Divsteps.zWalk p x t).z t z.length hb.z_lo hb.z_hi htw
  have hh := counterUpdate_int_spec active swap zero z carry hn hz hc hn2
    (counterActive (ECDSAAdd.Divsteps.zWalk p x t))
    (counterSwap (ECDSAAdd.Divsteps.zWalk p x t))
    (ECDSAAdd.Divsteps.zWalk p x t).z (counterSwap_active _) hr.1 hr.2
  simpa only [counterNext_zStep,ECDSAAdd.Divsteps.zWalk_succ] using hh

end ECDSAAdd.Arithmetic.Divsteps
