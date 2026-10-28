import ECDSAAdd.Arithmetic.CuccaroSignedSquareInverse

namespace ECDSAAdd.Arithmetic

private theorem cuccaroSignedSquare_not_dst (cin : Wire) (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup) (q : Wire)
    (hq : q∈cin::xs++pad++mask++carry) : q∉dst := by
  intro hdq
  have hn := List.nodup_iff_count.mp hnd q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hdq
  simp only [List.count_cons,List.count_append] at hn h1
  omega

theorem cuccaroSignedTriangularSquare_frame (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (s : State) (records : List Bool)
    (hd0 : regValue dst s.basis=0) (hp0 : regValue pad s.basis=0)
    (hm0 : regValue mask s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    ∀q,q∉dst →
      (run (cuccaroSignedTriangularSquare xs dst pad mask carry cin) records s).basis q=
        s.basis q := by
  let out := run (cuccaroSignedTriangularSquare xs dst pad mask carry cin) records s
  have hr := cuccaroSignedTriangularSquare_forward_correct cin xs dst pad mask carry hnd hx hd
    hp hm s records hd0 hp0 hm0 hc0 hi0
  have hsupp := (cuccaroSignedTriangularSquare_wires_subset cin xs dst pad mask carry
    hx hd hp hm).1
  intro q hqdst
  by_cases hqcin : q=cin
  · subst q
    exact hr.2.2.2.2.2.2.trans hi0.symm
  by_cases hqxs : q∈xs
  · exact (regValue_eq_iff xs out.basis s.basis).mp hr.2.2.1 q hqxs
  by_cases hqpad : q∈pad
  · exact (regValue_eq_iff pad out.basis s.basis).mp
      (hr.2.2.2.1.trans hp0.symm) q hqpad
  by_cases hqmask : q∈mask
  · exact (regValue_eq_iff mask out.basis s.basis).mp
      (hr.2.2.2.2.1.trans hm0.symm) q hqmask
  by_cases hqcarry : q∈carry
  · exact (regValue_eq_iff carry out.basis s.basis).mp
      (hr.2.2.2.2.2.1.trans hc0.symm) q hqcarry
  · apply run_preserves_outside
    intro hw
    have h := hsupp hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    grind

theorem cuccaroSignedTriangularSquare_spec (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (X : Nat) :
    {{ xs=X, dst=0, pad=0, mask=0, carry=0, cin=false }}
      cuccaroSignedTriangularSquare xs dst pad mask carry cin
    {{ xs=X, dst=X^2, pad=0, mask=0, carry=0, cin=false }} := by
  intro s records h
  simp only [Holds.holds] at h ⊢
  obtain ⟨⟨⟨⟨⟨hxv,hd0⟩,hp0⟩,hm0⟩,hc0⟩,hi0⟩ := h
  have hr := cuccaroSignedTriangularSquare_forward_correct cin xs dst pad mask carry hnd hx hd
    hp hm s records hd0 hp0 hm0 hc0 hi0
  refine ⟨hr.1,⟨⟨⟨⟨⟨?_,?_⟩,hr.2.2.2.1⟩,hr.2.2.2.2.1⟩,
    hr.2.2.2.2.2.1⟩,hr.2.2.2.2.2.2⟩⟩
  · simpa [hxv] using hr.2.2.1
  · simpa [hxv] using hr.2.1

private theorem cuccaroSignedTriangularSquareClear_state (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (s : State) (records : List Bool)
    (hv : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hm0 : regValue mask s.basis=0)
    (hc0 : regValue carry s.basis=0) (hi0 : s.basis cin=false) :
    let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
    run (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin) records s=base := by
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have away (q : Wire) (hq : q∈cin::xs++pad++mask++carry) : q∉dst :=
    cuccaroSignedSquare_not_dst cin xs dst pad mask carry hnd q hq
  have baseReg (r : List Wire) (hr : r=xs ∨ r=pad ∨ r=mask ∨ r=carry) :
      regValue r base.basis=regValue r s.basis := by
    apply regValue_congr; intro q hq
    simp only [base]
    rw [if_neg (away q (by rcases hr with rfl|rfl|rfl|rfl <;> simp [hq]))]
  have bdst : regValue dst base.basis=0 := (regValue_zero _ _).mpr (fun q hq => by
    simp [base,hq])
  have bpad : regValue pad base.basis=0 := (baseReg pad (Or.inr (Or.inl rfl))).trans hp0
  have bmask : regValue mask base.basis=0 :=
    (baseReg mask (Or.inr (Or.inr (Or.inl rfl)))).trans hm0
  have bcarry : regValue carry base.basis=0 :=
    (baseReg carry (Or.inr (Or.inr (Or.inr rfl)))).trans hc0
  have bcin : base.basis cin=false := by simp [base,away cin (by simp),hi0]
  let forwardRecords := List.replicate
    (measurementCount (cuccaroSignedTriangularSquare xs dst pad mask carry cin)) false
  let u := run (cuccaroSignedTriangularSquare xs dst pad mask carry cin) forwardRecords base
  have fc := cuccaroSignedTriangularSquare_forward_correct cin xs dst pad mask carry hnd hx hd
    hp hm base forwardRecords bdst bpad bmask bcarry bcin
  have ff := cuccaroSignedTriangularSquare_frame cin xs dst pad mask carry hnd hx hd hp hm hc
    base forwardRecords bdst bpad bmask bcarry bcin
  have xsBase : regValue xs base.basis=regValue xs s.basis := baseReg xs (Or.inl rfl)
  have us : u=s := by
    have uphase : u.phase=s.phase := fc.1
    have udst : regValue dst u.basis=regValue dst s.basis := by
      rw [fc.2.1,xsBase,hv]
    have ubasis : u.basis=s.basis := by
      funext q
      by_cases hq : q∈dst
      · exact (regValue_eq_iff dst u.basis s.basis).mp udst q hq
      · exact (ff q hq).trans (by simp [base,hq])
    calc
      u = ⟨u.phase,u.basis⟩ := rfl
      _ = ⟨s.phase,s.basis⟩ := by rw [uphase,ubasis]
      _ = s := rfl
  have rr := cuccaroSignedTriangularSquare_roundtrip cin xs dst pad mask carry hnd
    base forwardRecords records
  change run (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin) records u=base at rr
  change run (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin) records s=base
  rw [us] at rr
  exact rr

theorem cuccaroSignedTriangularSquareClear_frame (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (s : State) (records : List Bool)
    (hv : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hm0 : regValue mask s.basis=0)
    (hc0 : regValue carry s.basis=0) (hi0 : s.basis cin=false) :
    ∀q,q∉dst →
      (run (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin) records s).basis q=
        s.basis q := by
  have hr := cuccaroSignedTriangularSquareClear_state cin xs dst pad mask carry hnd hx hd hp hm hc
    s records hv hp0 hm0 hc0 hi0
  intro q hq
  simpa [hq] using congrArg (fun st => st.basis q) hr

theorem cuccaroSignedTriangularSquareClear_spec (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (X : Nat) :
    {{ xs=X, dst=X^2, pad=0, mask=0, carry=0, cin=false }}
      cuccaroSignedTriangularSquareClear xs dst pad mask carry cin
    {{ xs=X, dst=0, pad=0, mask=0, carry=0, cin=false }} := by
  intro s records h
  simp only [Holds.holds] at h ⊢
  obtain ⟨⟨⟨⟨⟨hxv,hv⟩,hp0⟩,hm0⟩,hc0⟩,hi0⟩ := h
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have hr := cuccaroSignedTriangularSquareClear_state cin xs dst pad mask carry hnd hx hd hp hm hc
    s records (by simpa [hxv] using hv) hp0 hm0 hc0 hi0
  let out := run (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin) records s
  have hr0 : out=base := by simpa [out,base] using hr
  have away (q : Wire) (hq : q∈cin::xs++pad++mask++carry) : q∉dst :=
    cuccaroSignedSquare_not_dst cin xs dst pad mask carry hnd q hq
  have keep (r : List Wire) (hreg : r=xs ∨ r=pad ∨ r=mask ∨ r=carry) :
      regValue r out.basis=regValue r s.basis := by
    rw [hr0]
    apply regValue_congr; intro q hq
    simp only [base]
    rw [if_neg (away q (by rcases hreg with rfl|rfl|rfl|rfl <;> simp [hq]))]
  have hdst : regValue dst out.basis=0 := by
    rw [hr0]
    apply (regValue_zero _ _).mpr
    intro q hq
    simp [base,hq]
  have hphase : out.phase=s.phase := by
    simpa [base] using congrArg State.phase hr0
  refine ⟨hphase,⟨⟨⟨⟨⟨?_,hdst⟩,?_⟩,?_⟩,?_⟩,?_⟩⟩
  · exact (keep xs (Or.inl rfl)).trans hxv
  · exact (keep pad (Or.inr (Or.inl rfl))).trans hp0
  · exact (keep mask (Or.inr (Or.inr (Or.inl rfl)))).trans hm0
  · exact (keep carry (Or.inr (Or.inr (Or.inr rfl)))).trans hc0
  · have hcineq := congrArg (fun st => st.basis cin) hr0
    simpa [base,away cin (by simp),hi0] using hcineq

end ECDSAAdd.Arithmetic
