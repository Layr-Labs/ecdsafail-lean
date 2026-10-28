import ECDSAAdd.Arithmetic.SignedSquareLeafProof

namespace ECDSAAdd.Arithmetic

theorem signedSquareRow_wires_subset (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    wires (signedSquareRow c xs dst pad carry)⊆
      (c::xs++dst++pad++carry).toFinset := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have hk : (carry.take xs.length).length+1=dst.length := by simp [hd,hc]
  have ha := addInPlace_wires (xs++pad.take 1) dst (carry.take xs.length) c hs hk
  have hxl := xorWhenFalse_wires_subset c (dst.take xs.length)
  have hxr := xorWhenFalse_wires_subset c dst
  intro q hq
  simp only [signedSquareRow,wires_append,Finset.mem_union] at hq
  rcases hq with (hq|hq)|hq
  · have h := hxl hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    have ht : q∈dst.take xs.length → q∈dst := List.mem_of_mem_take
    grind
  · rw [ha] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp' : q∈pad.take 1 → q∈pad := List.mem_of_mem_take
    have hc' : q∈carry.take xs.length → q∈carry := List.mem_of_mem_take
    grind
  · have h := hxr hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    grind

theorem signedSquareRowClear_wires_subset (c : Wire) (xs dst pad carry : List Wire)
    (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    wires (signedSquareRowClear c xs dst pad carry)⊆
      (c::xs++dst++pad++carry).toFinset := by
  have hs : (xs++pad.take 1).length=dst.length := by simp [hd,hp]
  have hk : (carry.take xs.length).length+1=dst.length := by simp [hd,hc]
  have ha := addInPlace_wires (xs++pad.take 1) dst (carry.take xs.length) c hs hk
  have hxl := xorWhenFalse_wires_subset c (dst.take xs.length)
  have hxr := xorWhenFalse_wires_subset c dst
  intro q hq
  simp only [signedSquareRowClear,wires_append,Finset.mem_union,notRegister_wires] at hq
  rcases hq with hq|hq|hq|hq|hq
  · have h := hxr hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    grind
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    grind
  · rw [ha] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp' : q∈pad.take 1 → q∈pad := List.mem_of_mem_take
    have hc' : q∈carry.take xs.length → q∈carry := List.mem_of_mem_take
    grind
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    grind
  · have h := hxl hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    have ht : q∈dst.take xs.length → q∈dst := List.mem_of_mem_take
    grind

theorem signedSquareTop_wires_subset (xs dst : List Wire) :
    wires (signedSquareTop xs dst)⊆(xs++dst).toFinset := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,wires]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,wires]
        | cons z zs => simp [signedSquareTop,wires,Instr.wires]
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,wires]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,wires]
        | cons b tail =>
          intro q hq
          have h := ih tail hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at h ⊢
          tauto

theorem signedSquareRows_wires_subset (xs dst pad carry : List Wire)
    (hd : dst.length=2*xs.length) (hp : xs.length≤1 ∨ 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    wires (signedSquareRows xs dst pad carry)⊆(xs++dst++pad++carry).toFinset ∧
      wires (signedSquareRowsClear xs dst pad carry)⊆
        (xs++dst++pad++carry).toFinset := by
  induction xs generalizing dst with
  | nil => simp [signedSquareRows,signedSquareRowsClear,wires]
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedSquareRows,signedSquareRowsClear,wires]
    | cons d tail =>
      simp only [List.length_cons] at hd hp hc
      let rest := d::tail
      let row := (dst.drop 1).take (rest.length+1)
      let dst2 := dst.drop 2
      have hpad : 1≤pad.length := by rcases hp with hp|hp <;> omega
      have hcarry : rest.length≤carry.length := by dsimp [rest]; omega
      have rowLen : row.length=rest.length+1 := by
        apply List.length_take_of_le
        dsimp [row,rest]
        simp
        omega
      have dst2Len : dst2.length=2*rest.length := by
        dsimp [dst2,rest]
        simp
        omega
      have hrecCarry : rest.length-1≤carry.length := by omega
      have hr := signedSquareRow_wires_subset c rest row pad carry rowLen hpad hcarry
      have hrc := signedSquareRowClear_wires_subset c rest row pad carry rowLen hpad hcarry
      have hi := ih dst2 dst2Len (Or.inr hpad) hrecCarry
      have rowMem (q : Wire) (hq : q∈row) : q∈dst :=
        List.mem_of_mem_drop (List.mem_of_mem_take hq)
      have dst2Mem (q : Wire) (hq : q∈dst2) : q∈dst := List.mem_of_mem_drop hq
      constructor
      · intro q hq
        simp only [signedSquareRows,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq
        · have h := hr hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hi.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
      · intro q hq
        simp only [signedSquareRowsClear,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq
        · have h := hi.2 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hrc hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind

theorem signedTriangularSquare_wires_subset (cin : Wire)
    (xs dst pad mask carry : List Wire) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hm : xs.length≤mask.length) (hc : dst.length-1≤carry.length) :
    wires (signedTriangularSquare xs dst pad mask carry cin)⊆
        (cin::xs++dst++pad++mask++carry).toFinset ∧
      wires (signedTriangularSquareClear xs dst pad mask carry cin)⊆
        (cin::xs++dst++pad++mask++carry).toFinset := by
  have hr := signedSquareRows_wires_subset xs dst pad carry hd (Or.inr hp) (by omega)
  have ht := signedSquareTop_wires_subset xs dst
  have hs := signedDiagSub_wires_subset cin xs dst mask carry
    (List.ne_nil_of_length_pos (by omega)) hd hm hc
  have ha := signedDiagAdd_wires_subset cin xs dst mask carry
    (List.ne_nil_of_length_pos (by omega)) hd hm hc
  cases xs with
  | nil => simp at hx
  | cons x tail =>
    cases tail with
    | nil => simp at hx
    | cons y ys =>
      constructor
      · intro q hq
        simp only [signedTriangularSquare,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq|hq
        · have h := hr.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := ht hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hs hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
      · intro q hq
        simp only [signedTriangularSquareClear,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq|hq
        · have h := ha hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := ht hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind
        · have h := hr.2 hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          grind

private theorem signedSquare_not_dst (cin : Wire) (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup) (q : Wire)
    (hq : q∈cin::xs++pad++mask++carry) : q∉dst := by
  intro hdq
  have hn := List.nodup_iff_count.mp hnd q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hdq
  simp only [List.count_cons,List.count_append] at hn h1
  omega

theorem signedTriangularSquare_frame (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (s : State) (records : List Bool)
    (hd0 : regValue dst s.basis=0) (hp0 : regValue pad s.basis=0)
    (hm0 : regValue mask s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    ∀q,q∉dst →
      (run (signedTriangularSquare xs dst pad mask carry cin) records s).basis q=
        s.basis q := by
  let out := run (signedTriangularSquare xs dst pad mask carry cin) records s
  have hr := signedTriangularSquare_forward_correct cin xs dst pad mask carry hnd hx hd
    hp hm hc s records hd0 hp0 hm0 hc0 hi0
  have hsupp := (signedTriangularSquare_wires_subset cin xs dst pad mask carry
    hx hd hp hm hc).1
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

theorem signedTriangularSquare_spec (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (X : Nat) :
    {{ xs=X, dst=0, pad=0, mask=0, carry=0, cin=false }}
      signedTriangularSquare xs dst pad mask carry cin
    {{ xs=X, dst=X^2, pad=0, mask=0, carry=0, cin=false }} := by
  intro s records h
  simp only [Holds.holds] at h ⊢
  obtain ⟨⟨⟨⟨⟨hxv,hd0⟩,hp0⟩,hm0⟩,hc0⟩,hi0⟩ := h
  have hr := signedTriangularSquare_forward_correct cin xs dst pad mask carry hnd hx hd
    hp hm hc s records hd0 hp0 hm0 hc0 hi0
  refine ⟨hr.1,⟨⟨⟨⟨⟨?_,?_⟩,hr.2.2.2.1⟩,hr.2.2.2.2.1⟩,
    hr.2.2.2.2.2.1⟩,hr.2.2.2.2.2.2⟩⟩
  · simpa [hxv] using hr.2.2.1
  · simpa [hxv] using hr.2.1

private theorem signedTriangularSquareClear_state (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (s : State) (records : List Bool)
    (hv : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hm0 : regValue mask s.basis=0)
    (hc0 : regValue carry s.basis=0) (hi0 : s.basis cin=false) :
    let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
    run (signedTriangularSquareClear xs dst pad mask carry cin) records s=base := by
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have away (q : Wire) (hq : q∈cin::xs++pad++mask++carry) : q∉dst :=
    signedSquare_not_dst cin xs dst pad mask carry hnd q hq
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
    (measurementCount (signedTriangularSquare xs dst pad mask carry cin)) false
  let u := run (signedTriangularSquare xs dst pad mask carry cin) forwardRecords base
  have fc := signedTriangularSquare_forward_correct cin xs dst pad mask carry hnd hx hd
    hp hm hc base forwardRecords bdst bpad bmask bcarry bcin
  have ff := signedTriangularSquare_frame cin xs dst pad mask carry hnd hx hd hp hm hc
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
  have rr := signedTriangularSquare_roundtrip cin xs dst pad mask carry hnd hx hd hp hm hc
    base forwardRecords records bdst bpad bmask bcarry bcin
  change run (signedTriangularSquareClear xs dst pad mask carry cin) records u=base at rr
  change run (signedTriangularSquareClear xs dst pad mask carry cin) records s=base
  rw [us] at rr
  exact rr

theorem signedTriangularSquareClear_frame (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (s : State) (records : List Bool)
    (hv : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hm0 : regValue mask s.basis=0)
    (hc0 : regValue carry s.basis=0) (hi0 : s.basis cin=false) :
    ∀q,q∉dst →
      (run (signedTriangularSquareClear xs dst pad mask carry cin) records s).basis q=
        s.basis q := by
  have hr := signedTriangularSquareClear_state cin xs dst pad mask carry hnd hx hd hp hm hc
    s records hv hp0 hm0 hc0 hi0
  intro q hq
  simpa [hq] using congrArg (fun st => st.basis q) hr

theorem signedTriangularSquareClear_spec (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length) (X : Nat) :
    {{ xs=X, dst=X^2, pad=0, mask=0, carry=0, cin=false }}
      signedTriangularSquareClear xs dst pad mask carry cin
    {{ xs=X, dst=0, pad=0, mask=0, carry=0, cin=false }} := by
  intro s records h
  simp only [Holds.holds] at h ⊢
  obtain ⟨⟨⟨⟨⟨hxv,hv⟩,hp0⟩,hm0⟩,hc0⟩,hi0⟩ := h
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have hr := signedTriangularSquareClear_state cin xs dst pad mask carry hnd hx hd hp hm hc
    s records (by simpa [hxv] using hv) hp0 hm0 hc0 hi0
  let out := run (signedTriangularSquareClear xs dst pad mask carry cin) records s
  have hr0 : out=base := by simpa [out,base] using hr
  have away (q : Wire) (hq : q∈cin::xs++pad++mask++carry) : q∉dst :=
    signedSquare_not_dst cin xs dst pad mask carry hnd q hq
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
