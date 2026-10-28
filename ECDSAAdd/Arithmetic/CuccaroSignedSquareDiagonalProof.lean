import ECDSAAdd.Arithmetic.CuccaroSignedSquareRowsProof

namespace ECDSAAdd.Arithmetic

theorem cuccaroSignedDiagSub_wires_subset (cin : Wire) (xs dst mask carry : List Wire)
    (_hx : xs≠[]) (hd : dst.length=2*xs.length) (hm : xs.length≤mask.length) :
    wires (cuccaroSignedDiagSub xs dst mask carry cin)⊆
      (cin::xs++mask++dst++carry).toFinset := by
  let k := xs.length-1
  let low := xs.take k
  let mlow := mask.take k
  let src := signedDiagSource xs mask
  have lm : low.length=mlow.length := by simp [low,mlow,k]; omega
  have cp := copyRegister_wires none low mlow lm
  have xf := xorWhenFalse_wires_subset cin mlow
  have sl : src.length=dst.length := by
    simp [src,signedDiagSource,List.length_take,Nat.min_eq_left hm,hd]
    omega
  have ar := cuccaroSub_wires_subset src dst cin
  intro q hq
  simp only [cuccaroSignedDiagSub,signedDiagLoad,signedDiagUnload,wires_append,
    Finset.mem_union] at hq
  rcases hq with hload | harith | hunload
  · rcases hload with hcopy | hxor
    · rw [cp] at hcopy
      split at hcopy
      · simp at hcopy
      · simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hcopy
        have hl : q∈low → q∈xs := fun h => List.mem_of_mem_take h
        have hm' : q∈mlow → q∈mask := fun h => List.mem_of_mem_take h
        simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
        tauto

    · have h := xf hxor
      have hm' : q∈mlow → q∈mask := fun h => List.mem_of_mem_take h
      simp only [List.mem_toFinset,List.mem_cons] at h
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
      tauto
  · have harith' := ar harith
    have hs (h : q∈src) : q∈xs ∨ q∈mask := by
      simp only [src,signedDiagSource,List.mem_append] at h
      rcases h with h|h
      · exact Or.inl h
      · exact Or.inr (List.mem_of_mem_take h)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at harith' ⊢
    tauto
  · rcases hunload with hxor | hcopy
    · have h := xf hxor
      have hm' : q∈mlow → q∈mask := fun h => List.mem_of_mem_take h
      simp only [List.mem_toFinset,List.mem_cons] at h
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
      tauto
    · rw [cp] at hcopy
      split at hcopy
      · simp at hcopy
      · simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hcopy
        have hl : q∈low → q∈xs := fun h => List.mem_of_mem_take h
        have hm' : q∈mlow → q∈mask := fun h => List.mem_of_mem_take h
        simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
        tauto

theorem cuccaroSignedDiagSub_preserves_outside (cin : Wire) (xs dst mask carry : List Wire)
    (hx : xs≠[]) (hd : dst.length=2*xs.length) (hm : xs.length≤mask.length)
    (s : State) (records : List Bool)
    (q : Wire) (hq : q∉cin::xs++mask++dst++carry) :
    (run (cuccaroSignedDiagSub xs dst mask carry cin) records s).basis q=s.basis q := by
  apply run_preserves_outside
  intro hw
  have hs := cuccaroSignedDiagSub_wires_subset cin xs dst mask carry hx hd hm hw
  exact hq (List.mem_toFinset.mp hs)


theorem cuccaroSignedDiagSub_correct (cin : Wire) (xs dst mask carry : List Wire)
    (hnd : (cin::xs++mask++dst++carry).Nodup) (hx : xs≠[])
    (hd : dst.length=2*xs.length) (hm : xs.length≤mask.length)
    (s : State) (records : List Bool)
    (A : Nat) (hv : regValue dst s.basis=A) (hmask : regValue mask s.basis=0)
    (hcarry : regValue carry s.basis=0) (hcin : s.basis cin=false) :
    let out := run (cuccaroSignedDiagSub xs dst mask carry cin) records s
    out.phase=s.phase ∧
      regValue dst out.basis=
        (A+2^dst.length-signedDiagValue (regValue xs s.basis) xs.length)%2^dst.length ∧
      regValue mask out.basis=0 ∧ regValue carry out.basis=0 ∧
      out.basis cin=false ∧ regValue xs out.basis=regValue xs s.basis := by
  let load := signedDiagLoad xs mask cin
  let src := signedDiagSource xs mask
  let arith := cuccaroSub src dst cin
  let unload := signedDiagUnload xs mask cin
  let rest := records.drop (measurementCount load)
  let u := run load (records.take (measurementCount load)) s
  let v := run arith (rest.take (measurementCount arith)) u
  let out := run unload (rest.drop (measurementCount arith)) v
  have lf := signedDiagLoad_frame cin xs mask dst carry hnd hm s.basis hcin
  have lu := lf s (records.take (measurementCount load)) ⟨hmask,fun _ _ => rfl⟩
  have keepU (q : Wire) (hq : q∉mask) : u.basis q=s.basis q := lu.2.2 q hq
  have disXM (q : Wire) (hq : q∈xs) : q∉mask := by
    intro hmemb
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hmemb
    simp only [List.count_cons,List.count_append] at hn
    omega
  have disDM (q : Wire) (hq : q∈dst) : q∉mask := by
    intro hmemb
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hmemb
    simp only [List.count_cons,List.count_append] at hn
    omega
  have disCM (q : Wire) (hq : q∈carry) : q∉mask := by
    intro hmemb
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hmemb
    simp only [List.count_cons,List.count_append] at hn
    omega
  have xsU : regValue xs u.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => keepU q (disXM q hq))
  have dstU : regValue dst u.basis=A :=
    (regValue_congr _ _ _ (fun q hq => keepU q (disDM q hq))).trans hv
  have carryU : regValue carry u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => keepU q (disCM q hq))).trans hcarry
  have cinU : u.basis cin=false := (keepU cin (by
    intro hmemb
    have hn := List.nodup_iff_count.mp hnd cin
    have h2 := List.count_pos_iff.mpr hmemb
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at hn
    omega)).trans hcin
  have maskU : regValue mask u.basis=signedDiagHigh xs u.basis := by
    rw [lu.2.1]
    simp [signedDiagHigh,xsU]
  have srcU : regValue src u.basis=signedDiagValue (regValue xs s.basis) xs.length := by
    rw [signedDiagSource_value xs mask hx hm u.basis maskU,xsU]
  have srcLen : src.length=dst.length := by
    simp [src,signedDiagSource,List.length_take,Nat.min_eq_left hm,hd]
    omega
  have ndarith : (cin::src++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hn := List.nodup_iff_count.mp hnd q
    have hm' := (List.take_sublist xs.length mask).count_le q
    simp only [src,signedDiagSource,List.count_cons,List.count_append] at hn ⊢
    omega
  have af := cuccaroSub_frame cin src dst ndarith srcLen u.basis cinU A
  have av0 := af u (rest.take (measurementCount arith)) ⟨dstU,fun _ _ => rfl⟩
  have av : v.phase=u.phase ∧ SquareFrame dst u.basis
      ((A+2^dst.length-regValue src u.basis)%2^dst.length) v.basis := by
    simpa [v,arith] using av0
  have targetV : regValue dst v.basis=
      (A+2^dst.length-signedDiagValue (regValue xs s.basis) xs.length)%2^dst.length := by
    rw [av.2.1,srcU]
  have keepV (q : Wire) (hq : q∉dst) : v.basis q=u.basis q := av.2.2 q hq
  have maskV0 : regValue mask v.basis=regValue mask u.basis := by
    apply regValue_congr; intro q hq; apply keepV q
    intro hdq
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hdq
    simp only [List.count_cons,List.count_append] at hn
    omega
  have xsV : regValue xs v.basis=regValue xs u.basis := by
    apply regValue_congr; intro q hq; apply keepV q
    intro hdq
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hdq
    simp only [List.count_cons,List.count_append] at hn
    omega
  have maskV : regValue mask v.basis=signedDiagHigh xs v.basis := by
    rw [maskV0,maskU]
    simp [signedDiagHigh,xsV]
  have cinV : v.basis cin=false := (keepV cin (by
    intro hdq
    have hn := List.nodup_iff_count.mp hnd cin
    have h2 := List.count_pos_iff.mpr hdq
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at hn
    omega)).trans cinU
  have uf := signedDiagUnload_frame cin xs mask dst carry hnd hm v.basis cinV
  have uv := uf v (rest.drop (measurementCount arith)) ⟨maskV,fun _ _ => rfl⟩
  have keepOut (q : Wire) (hq : q∉mask) : out.basis q=v.basis q := uv.2.2 q hq
  have final : out.phase=s.phase ∧
      regValue dst out.basis=
        (A+2^dst.length-signedDiagValue (regValue xs s.basis) xs.length)%2^dst.length ∧
      regValue mask out.basis=0 ∧ regValue carry out.basis=0 ∧
      out.basis cin=false ∧ regValue xs out.basis=regValue xs s.basis := by
    refine ⟨uv.1.trans (av.1.trans lu.1),?_,uv.2.1,?_,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => keepOut q (disDM q hq))).trans targetV
    · have cv : regValue carry v.basis=0 :=
        (regValue_congr _ _ _ (fun q hq => keepV q (by
          intro hdq
          have hn := List.nodup_iff_count.mp hnd q
          have h1 := List.count_pos_iff.mpr hq
          have h2 := List.count_pos_iff.mpr hdq
          simp only [List.count_cons,List.count_append] at hn
          omega))).trans carryU
      exact (regValue_congr _ _ _ (fun q hq => keepOut q (disCM q hq))).trans cv
    · exact (keepOut cin (by
        intro hmemb
        have hn := List.nodup_iff_count.mp hnd cin
        have h2 := List.count_pos_iff.mpr hmemb
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at hn
        omega)).trans cinV
    · calc
        regValue xs out.basis = regValue xs v.basis :=
          regValue_congr _ _ _ (fun q hq => keepOut q (disXM q hq))
        _ = regValue xs u.basis := xsV
        _ = regValue xs s.basis := xsU
  simpa [cuccaroSignedDiagSub,load,arith,unload,rest,u,v,out,run_append] using final



end ECDSAAdd.Arithmetic
