import ECDSAAdd.Arithmetic.DivideState

namespace ECDSAAdd.Arithmetic

private theorem divideInverse_values (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (D E Z S : Nat) (B : Bool) (hS0 : 0<S) (hS : S<p) :
    let extra := fun st => st L.control=B ∧ regValue L.denominator st=D ∧
      regValue L.numerator st=E ∧ regValue L.acc st=Z ∧ regValue L.inner.out st=0
    let middle := InverseScaledMiddle L.inner p (kaliskiStep^[512] (kaliskiInit p S))
      (kaliskiCodes 512 (kaliskiInit p S)) (-((kaliskiStep^[512] (kaliskiInit p S)).r : Fp)).val
    Triple (fun st => InverseInitial L.inner p S st ∧ extra st) (inverseCompute L.inner p)
      (fun st => middle st ∧ extra st) ∧
    Triple (fun st => middle st ∧ extra st) (inverseUncompute L.inner p)
      (fun st => InverseInitial L.inner p S st ∧ extra st) := by
  dsimp only
  have hp : p<2^256 := by norm_num [p]
  have hd : L.inner.first.data.width=257 := by
    simp [KaliskiRoundLayout.data,RoundDataLayout.width,show L.inner.first.low.length=256 from hw.inverse.low]
  have ha : L.inner.arithmetic.width=256 := hw.inverse.arithmetic
  have hc := inverseCompute_values L.inner (L.inner_nodup hnd) hw.inverse.records hw.inverse.counter
    hw.inverse.low hw.inverse.arithmetic hw.inverse.a hw.inverse.temp p S hp (by norm_num [p]) hS
    (Secp256k1.p_prime.coprime_iff_not_dvd.mpr (fun h => (Nat.not_le_of_lt hS) (Nat.le_of_dvd hS0 h)))
  have hs := inverseCompute_wires L.inner hw.inverse.records hw.inverse.counter (by omega)
    (by omega) (by rw [show L.inner.a.length=257 from hw.inverse.a,ha])
    (by rw [show L.inner.temp.length=257 from hw.inverse.temp,ha]) hw.inverse.low hw.inverse.arithmetic p
  have frame (P : Program) (hP : wires P=L.inner.usedCoreWires.toFinset)
      (s t : BasisState) (he : ∀ q, q∉wires P → s q=t q)
      (h : s L.control=B ∧ regValue L.denominator s=D ∧ regValue L.numerator s=E ∧
        regValue L.acc s=Z ∧ regValue L.inner.out s=0) :
      t L.control=B ∧ regValue L.denominator t=D ∧ regValue L.numerator t=E ∧
        regValue L.acc t=Z ∧ regValue L.inner.out t=0 := by
    have keep (q : Wire) (hq : q∈L.control :: L.denominator++L.numerator++L.acc) : t q=s q := by
      apply (he q ?_).symm
      rw [hP]
      intro hh
      exact List.disjoint_left.mp (L.external_disjoint hnd) hq (L.inverse_used_subset (List.mem_toFinset.mp hh))
    refine ⟨(keep _ (by simp)).trans h.1,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2.1,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2.2.1,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2.2.2.1,?_⟩
    apply Eq.trans (regValue_congr _ _ _ ?_) h.2.2.2.2
    intro q hq
    apply (he q ?_).symm
    rw [hP]
    intro hh
    have hdis : L.inner.coreWires.Disjoint L.inner.out :=
      (List.nodup_append'.mp (L.inner_nodup hnd)).2.2
    exact List.disjoint_left.mp hdis (L.inner.usedCoreWires_sublist.subset (List.mem_toFinset.mp hh)) hq
  exact ⟨hc.1.frame (frame _ hs.1),hc.2.frame (frame _ hs.2)⟩

private theorem divideLoad_extra (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (D E Z : Nat) (B : Bool) :
    let values := fun U V S st =>
      (InverseValues L.inverseView (inverseValues D U V S 0) st ∧ st L.control=B) ∧
        (regValue L.numerator st=E ∧ regValue L.acc st=Z)
    Triple (values 0 0 0) (divideLoad L) (values p (if B then D else 1) 1) ∧
    Triple (values p (if B then D else 1) 1) (divideUnload L) (values 0 0 0) := by
  dsimp only
  have hs := divideLoad_wires_subset L hw
  have hd : (L.numerator++L.acc).Disjoint (L.control::L.inverseView.wires) := by
    apply List.disjoint_left.mpr; intro q hq hv
    have h := List.nodup_iff_count.mp hnd q
    have hp := List.count_pos_iff.mpr hq
    have hq' := List.count_pos_iff.mpr hv
    have hv' := L.inverseView.wires_perm.count_eq q
    change L.inverseView.wires.count q=(L.denominator++L.inner.wires).count q at hv'
    simp only [DivideLayout.wires,DivideLayout.work,List.count_cons,List.count_append] at h hp hq' hv'
    omega
  have frame (P : Program) (hP : wires P ⊆ (L.control::L.inverseView.wires).toFinset)
      (s t : BasisState) (he : ∀ q, q∉wires P → s q=t q)
      (h : regValue L.numerator s=E ∧ regValue L.acc s=Z) :
      regValue L.numerator t=E ∧ regValue L.acc t=Z := by
    have keep (q : Wire) (hq : q∈L.numerator++L.acc) : t q=s q := by
      apply (he q ?_).symm
      intro hh
      exact List.disjoint_left.mp hd hq (List.mem_toFinset.mp (hP hh))
    exact ⟨(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2⟩
  have hv := divideLoad_values L hw hnd D B
  exact ⟨hv.1.frame (frame _ hs.1),hv.2.frame (frame _ hs.2)⟩

/-- 加减除法保留控制、分母、分子，清零全部工作位；只要求启用时分母非零。 -/
private theorem divide_spec (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (D E Z : Nat) (B : Bool) (hD : D<p) (hE : E<p) (hZ : Z<p) (hD0 : B=true → D≠0) :
    ({{ L.control=B,L.denominator=D,L.numerator=E,L.acc=Z,L.work=0 }} divideAdd L
     {{ L.control=B,L.denominator=D,L.numerator=E,
       L.acc=(if B then (Z+(((D : Fp)⁻¹).val*E)%p)%p else Z),L.work=0 }}) ∧
    ({{ L.control=B,L.denominator=D,L.numerator=E,L.acc=Z,L.work=0 }} divideSub L
     {{ L.control=B,L.denominator=D,L.numerator=E,
       L.acc=(if B then (Z+p-(((D : Fp)⁻¹).val*E)%p)%p else Z),L.work=0 }}) := by
  letI : NeZero p := ⟨by norm_num [p]⟩
  let S := if B then D else 1
  let A := ((S : Fp)⁻¹).val
  have hp : p<2^256 := by norm_num [p]
  have hp0 : 0<p := by norm_num [p]
  have hS0 : 0<S := by
    dsimp [S]; split
    · exact Nat.pos_of_ne_zero (hD0 ‹B=true›)
    · decide
  have hS : S<p := by dsimp [S]; split; exact hD; norm_num [p]
  have hA : A<p := ZMod.val_lt _
  have hscale := kaliski_montgomery_scale p S (by norm_num [p]) hp hS0 hS
    (Secp256k1.p_prime.coprime_iff_not_dvd.mpr (fun h => (Nat.not_le_of_lt hS) (Nat.le_of_dvd hS0 h)))
  let ready := fun Z st =>
    (InverseValues L.inverseView (inverseValues D p S 1 0) st ∧ st L.control=B) ∧
      (regValue L.numerator st=E ∧ regValue L.acc st=Z)
  let prepared := fun Z st =>
    InverseScaledMiddle L.inner p (kaliskiStep^[512] (kaliskiInit p S)) (kaliskiCodes 512 (kaliskiInit p S))
      (-((kaliskiStep^[512] (kaliskiInit p S)).r : Fp)).val st ∧
      (st L.control=B ∧ regValue L.denominator st=D ∧ regValue L.numerator st=E ∧
        regValue L.acc st=Z ∧ regValue L.inner.out st=0)
  have hinverse (V : Nat) :
      Triple (ready V) (inverseCompute L.inner p) (prepared V) ∧
      Triple (prepared V) (inverseUncompute L.inner p) (ready V) := by
    have hi := divideInverse_values L hw hnd D E V S B hS0 hS
    constructor
    · apply hi.1.conseq
      · intro st h
        have hv := (divideReady_iff L hw D S hS0 (hS.trans hp) st).mp h.1.1
        exact ⟨hv.1.1,h.1.2,hv.2,h.2.1,h.2.2,hv.1.2⟩
      · intro st h; exact h
    · apply hi.2.conseq
      · intro st h; exact h
      · intro st h
        exact ⟨⟨(divideReady_iff L hw D S hS0 (hS.trans hp) st).mpr ⟨⟨h.1,h.2.2.2.2.2⟩,h.2.2.1⟩,
          h.2.1⟩,h.2.2.2.1,h.2.2.2.2.1⟩
  have hproduct :
      Triple (prepared Z)
        (montMulControlledAdd L.control L.multiply p)
        (prepared (if B then (Z+(A*E)%p)%p else Z)) ∧
      Triple (prepared Z)
        (montMulControlledSub L.control L.multiply p)
        (prepared (if B then (Z+p-(A*E)%p)%p else Z)) := by
    have finish (P : Program) (V : Nat) (s : State) (m : List Bool) (h : prepared Z s.basis)
        (hc : (run P m s).phase=s.phase ∧ regValue L.acc (run P m s).basis=V ∧
          ∀ q∉L.acc, (run P m s).basis q=s.basis q) :
        (run P m s).phase=s.phase ∧ prepared V (run P m s).basis := by
      have keep (q : Wire) (hq : q∈L.control::L.denominator++L.numerator++L.inner.wires) :
          (run P m s).basis q=s.basis q :=
        hc.2.2 q (List.disjoint_left.mp (L.acc_disjoint_other hnd) hq)
      refine ⟨hc.1,divideMiddle_congr L S _ _ _ h.1 (fun q hq => keep q (by simp [hq])),
        (keep _ (by simp)).trans h.2.1,
        (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2.2.1,
        (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2.2.2.1,hc.2.1,?_⟩
      apply Eq.trans (regValue_congr _ _ _ ?_) h.2.2.2.2.2
      intro q hq
      apply keep q
      have hi : q∈L.inner.wires := List.mem_append_right _ hq
      simp [hi]
    constructor
    · intro s m h
      have hc := divideProduct_correct L hw hnd A E Z B hA (hE.trans hp) hZ s m h.2.1
        (h.1.1.2.1.trans hscale) h.2.2.2.1 h.2.2.2.2.1 h.1.2.1
      exact finish _ _ s m h hc.1
    · intro s m h
      have hc := divideProduct_correct L hw hnd A E Z B hA (hE.trans hp) hZ s m h.2.1
        (h.1.1.2.1.trans hscale) h.2.2.2.1 h.2.2.2.2.1 h.1.2.1
      exact finish _ _ s m h hc.2
  have hload := (divideLoad_extra L hw hnd D E Z B).1
  have hadd := (((hload.seq (hinverse Z).1).seq hproduct.1).seq
    (hinverse (if B then (Z+(A*E)%p)%p else Z)).2).seq
    (divideLoad_extra L hw hnd D E (if B then (Z+(A*E)%p)%p else Z) B).2
  have hsub := (((hload.seq (hinverse Z).1).seq hproduct.2).seq
    (hinverse (if B then (Z+p-(A*E)%p)%p else Z)).2).seq
    (divideLoad_extra L hw hnd D E (if B then (Z+p-(A*E)%p)%p else Z) B).2
  have heA : (if B then (Z+(A*E)%p)%p else Z)=(if B then (Z+(((D : Fp)⁻¹).val*E)%p)%p else Z) := by
    cases B <;> simp [A,S]
  have heS : (if B then (Z+p-(A*E)%p)%p else Z)=(if B then (Z+p-(((D : Fp)⁻¹).val*E)%p)%p else Z) := by
    cases B <;> simp [A,S]
  simp only [heA] at hadd
  simp only [heS] at hsub
  constructor
  · apply Triple.conseq ?_ (by simpa only [divideAdd,List.append_assoc] using hadd) ?_
    · intro st h
      exact ⟨⟨(divideZero_iff L D st).mpr ⟨h.1.1.1.2,h.2⟩,h.1.1.1.1⟩,h.1.1.2,h.1.2⟩
    · intro st h
      have hz := (divideZero_iff L D st).mp h.1.1
      exact ⟨⟨⟨⟨h.1.2,hz.1⟩,h.2.1⟩,h.2.2⟩,hz.2⟩
  · apply Triple.conseq ?_ (by simpa only [divideSub,List.append_assoc] using hsub) ?_
    · intro st h
      exact ⟨⟨(divideZero_iff L D st).mpr ⟨h.1.1.1.2,h.2⟩,h.1.1.1.1⟩,h.1.1.2,h.1.2⟩
    · intro st h
      have hz := (divideZero_iff L D st).mp h.1.1
      exact ⟨⟨⟨⟨h.1.2,hz.1⟩,h.2.1⟩,h.2.2⟩,hz.2⟩

/-- 受控除法模加，输入保持且全部工作区清零。 -/
theorem divideAdd_spec (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (D E Z : Nat) (B : Bool) (hD : D<p) (hE : E<p) (hZ : Z<p) (hD0 : B=true → D≠0) :
    {{ L.control=B,L.denominator=D,L.numerator=E,L.acc=Z,L.work=0 }} divideAdd L
    {{ L.control=B,L.denominator=D,L.numerator=E,
      L.acc=(if B then (Z+(((D : Fp)⁻¹).val*E)%p)%p else Z),L.work=0 }} :=
  (divide_spec L hw hnd D E Z B hD hE hZ hD0).1

/-- 受控除法模减，输入保持且全部工作区清零。 -/
theorem divideSub_spec (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (D E Z : Nat) (B : Bool) (hD : D<p) (hE : E<p) (hZ : Z<p) (hD0 : B=true → D≠0) :
    {{ L.control=B,L.denominator=D,L.numerator=E,L.acc=Z,L.work=0 }} divideSub L
    {{ L.control=B,L.denominator=D,L.numerator=E,
      L.acc=(if B then (Z+p-(((D : Fp)⁻¹).val*E)%p)%p else Z),L.work=0 }} :=
  (divide_spec L hw hnd D E Z B hD hE hZ hD0).2

/-- 除法只改变acc；所有输入、控制和工作位逐线恢复。 -/
theorem divide_frame (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (D E Z : Nat) (B : Bool) (hD : D<p) (hE : E<p) (hZ : Z<p) (hD0 : B=true → D≠0)
    (s : State) (m : List Bool) (hb : s.basis L.control=B)
    (hd : regValue L.denominator s.basis=D) (he : regValue L.numerator s.basis=E)
    (hz : regValue L.acc s.basis=Z) (hc : regValue L.work s.basis=0)
    (q : Wire) (hq : q∉L.acc) :
    (run (divideAdd L) m s).basis q=s.basis q ∧ (run (divideSub L) m s).basis q=s.basis q := by
  have ht := divide_spec L hw hnd D E Z B hD hE hZ hD0
  have keep (P : Program) (hp : wires P=L.usedWires.toFinset)
      (hb' : (run P m s).basis L.control=B)
      (hd' : regValue L.denominator (run P m s).basis=D)
      (he' : regValue L.numerator (run P m s).basis=E)
      (hc' : regValue L.work (run P m s).basis=0) : (run P m s).basis q=s.basis q := by
    by_cases hqc : q=L.control
    · subst q; exact hb'.trans hb.symm
    by_cases hqd : q∈L.denominator
    · exact (regValue_eq_iff _ _ _).mp (hd'.trans hd.symm) q hqd
    by_cases hqe : q∈L.numerator
    · exact (regValue_eq_iff _ _ _).mp (he'.trans he.symm) q hqe
    by_cases hqw : q∈L.work
    · exact (regValue_eq_iff _ _ _).mp (hc'.trans hc.symm) q hqw
    apply run_preserves_outside
    rw [hp]
    have hi : q∉L.inner.compactCoreWires := fun h => hqw (List.mem_append_left _ (L.inner.compactCore_sublist.subset h))
    simp [DivideLayout.usedWires,hqc,hqd,hqe,hq,hi]
  obtain ⟨_,ha⟩ := ht.1 s m ⟨⟨⟨⟨hb,hd⟩,he⟩,hz⟩,hc⟩
  obtain ⟨_,hs⟩ := ht.2 s m ⟨⟨⟨⟨hb,hd⟩,he⟩,hz⟩,hc⟩
  exact ⟨keep _ (divide_wires L hw).1 ha.1.1.1.1 ha.1.1.1.2 ha.1.1.2 ha.2,
    keep _ (divide_wires L hw).2 hs.1.1.1.1 hs.1.1.1.2 hs.1.1.2 hs.2⟩

end ECDSAAdd.Arithmetic
