import ECDSAAdd.Arithmetic.CuccaroSignedSquareDiagonalProof

namespace ECDSAAdd.Arithmetic

theorem cuccaroSignedTriangularSquare_forward_correct (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (s : State) (records : List Bool)
    (hd0 : regValue dst s.basis=0) (hp0 : regValue pad s.basis=0)
    (hm0 : regValue mask s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    let out := run (cuccaroSignedTriangularSquare xs dst pad mask carry cin) records s
    out.phase=s.phase ∧ regValue dst out.basis=(regValue xs s.basis)^2 ∧
      regValue xs out.basis=regValue xs s.basis ∧ regValue pad out.basis=0 ∧
      regValue mask out.basis=0 ∧ regValue carry out.basis=0 ∧ out.basis cin=false := by
  let rows := cuccaroSignedSquareRows xs dst pad carry
  let top := signedSquareTop xs dst
  let diag := cuccaroSignedDiagSub xs dst mask carry cin
  let rest := records.drop (measurementCount rows)
  let u := run rows (records.take (measurementCount rows)) s
  let v := run top (rest.take (measurementCount top)) u
  let out := run diag (rest.drop (measurementCount top)) v
  have ndRows : (xs++dst++pad++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndTop : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have high0 : regValue (dst.drop xs.length) s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    exact (regValue_zero _ _).mp hd0 q (List.mem_of_mem_drop hq)
  have work0 : regValue (pad++carry) s.basis=0 := by simp [regValue_append,hp0,hc0]
  have rc := cuccaroSignedSquareRows_correct xs dst pad carry ndRows hd (Or.inr hp)
    s (records.take (measurementCount rows)) 0 hd0 high0 work0
  have tc := signedSquareTop_correct xs dst ndTop hd u
    (rest.take (measurementCount top)) rc.2.2.2.2
  have keepR (q : Wire) (hq : q∉dst) : u.basis q=s.basis q := rc.2.2.1 q hq
  have keepT (q : Wire) (hq : q∉dst) : v.basis q=u.basis q := tc.2.2.1 q hq
  have away (q : Wire) (hq : q∈cin::xs++pad++mask++carry) : q∉dst := by
    intro hdq
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hdq
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  have xsV : regValue xs v.basis=regValue xs s.basis := by
    calc
      regValue xs v.basis = regValue xs u.basis :=
        regValue_congr _ _ _ (fun q hq => keepT q (away q (by simp [hq])))
      _ = regValue xs s.basis :=
        regValue_congr _ _ _ (fun q hq => keepR q (away q (by simp [hq])))
  have regV (r : List Wire) (hr : r=pad ∨ r=mask ∨ r=carry)
      (h0 : regValue r s.basis=0) : regValue r v.basis=0 := by
    rw [← h0]
    apply regValue_congr; intro q hq
    exact (keepT q (away q (by rcases hr with rfl|rfl|rfl <;> simp [hq]))).trans
      (keepR q (away q (by rcases hr with rfl|rfl|rfl <;> simp [hq])))
  have padV := regV pad (Or.inl rfl) hp0
  have maskV := regV mask (Or.inr (Or.inl rfl)) hm0
  have carryV := regV carry (Or.inr (Or.inr rfl)) hc0
  have cinV : v.basis cin=false :=
    ((keepT cin (away cin (by simp))).trans (keepR cin (away cin (by simp)))).trans hi0
  have topSame : signedTopTerm xs u.basis=signedTopTerm xs s.basis := by
    apply signedTopTerm_congr
    intro q hq
    exact keepR q (away q (by simp [hq]))
  have rawV : regValue dst v.basis=signedRawValue xs s.basis := by
    rw [tc.2.1,rc.2.1,topSame]
    simp only [Nat.zero_add]
    exact (signedRawValue_rows_top xs s.basis).symm
  have ndDiag : (cin::xs++mask++dst++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have xsne : xs≠[] := List.ne_nil_of_length_pos (by omega)
  have dc := cuccaroSignedDiagSub_correct cin xs dst mask carry ndDiag xsne hd hm v
    (rest.drop (measurementCount top)) (signedRawValue xs s.basis) rawV maskV carryV cinV
  have squareEq :
      (signedRawValue xs s.basis+2^dst.length-
        signedDiagValue (regValue xs s.basis) xs.length)%2^dst.length=
        (regValue xs s.basis)^2 := by
    have raw := signedRawValue_correct xs s.basis (by omega)
    have sqb := square_bound (regValue xs s.basis) xs.length (regValue_lt xs s.basis)
    rw [raw,hd]
    have he : (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length+
        2^(2*xs.length)-signedDiagValue (regValue xs s.basis) xs.length=
        (regValue xs s.basis)^2+2^(2*xs.length) := by omega
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt sqb]
  have padAway (q : Wire) (hq : q∈pad) : q∉cin::xs++mask++dst++carry := by
    intro hmemb
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hmemb
    simp only [List.count_cons,List.count_append] at hn h1 h2
    omega
  have padOut : regValue pad out.basis=0 := by
    rw [← padV]
    apply regValue_congr; intro q hq
    exact cuccaroSignedDiagSub_preserves_outside cin xs dst mask carry (by omega) hd hm v
      (rest.drop (measurementCount top)) q (padAway q hq)
  have final : out.phase=s.phase ∧ regValue dst out.basis=(regValue xs s.basis)^2 ∧
      regValue xs out.basis=regValue xs s.basis ∧ regValue pad out.basis=0 ∧
      regValue mask out.basis=0 ∧ regValue carry out.basis=0 ∧ out.basis cin=false := by
    refine ⟨dc.1.trans (tc.1.trans rc.1),?_,dc.2.2.2.2.2.trans xsV,padOut,
      dc.2.2.1,dc.2.2.2.1,dc.2.2.2.2.1⟩
    rw [dc.2.1]
    rw [xsV,squareEq]
  cases xs with
  | nil => simp at hx
  | cons x tail =>
    cases tail with
    | nil => simp at hx
    | cons y ys =>
      simpa [cuccaroSignedTriangularSquare,rows,top,diag,rest,u,v,out,run_append] using final

end ECDSAAdd.Arithmetic
