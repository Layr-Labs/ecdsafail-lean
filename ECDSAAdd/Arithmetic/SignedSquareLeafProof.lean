import ECDSAAdd.Arithmetic.SignedSquareDiagonalProof

namespace ECDSAAdd.Arithmetic

theorem signedSquareTop_correct (xs dst : List Wire)
    (hnd : (xs++dst).Nodup) (hd : dst.length=2*xs.length)
    (s : State) (m : List Bool)
    (htop : regValue (dst.drop (2*xs.length-1)) s.basis=0) :
    let out := run (signedSquareTop xs dst) m s
    out.phase=s.phase ∧
      regValue dst out.basis=regValue dst s.basis+signedTopTerm xs s.basis ∧
      (∀q,q∉dst → out.basis q=s.basis q) ∧
      regValue xs out.basis=regValue xs s.basis := by
  induction xs generalizing dst s with
  | nil =>
    have de : dst=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst dst
    simp [signedSquareTop,signedTopTerm,run]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp at hd
      | cons a ds =>
        cases ds with
        | nil => simp at hd
        | cons z tail =>
          have te : tail=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
          subst tail
          have hxz : x≠z := by
            intro e; subst z; simp at hnd
          have haz : a≠z := by
            intro e; subst z; simp at hnd
          have hzx : z≠x := Ne.symm hxz
          have top0 : s.basis z=false := by
            change regValue [z] s.basis=0 at htop
            simpa [regValue] using htop
          simp only [signedSquareTop,run,signedTopTerm,regValue,List.foldr_cons,List.foldr_nil]
          refine ⟨True.intro,?_,?_,?_⟩
          · simp [writeBit,top0,haz]
            cases s.basis x <;> cases s.basis a <;> rfl
          · intro q hq
            simp [writeBit,show q≠z from fun e => hq (by simp [e])]
          · simp [writeBit,hxz]
    | cons y ys =>
      cases dst with
      | nil => simp at hd
      | cons a ds =>
        cases ds with
        | nil => simp at hd; omega
        | cons b tail =>
          let rest := y::ys
          have htail : tail.length=2*rest.length := by
            dsimp [rest]
            simp only [List.length_cons] at hd
            omega
          have hnTail : (rest++tail).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := List.nodup_iff_count.mp hnd q
            simp only [rest,List.count_cons,List.count_append] at h ⊢
            omega
          have topTail : regValue (tail.drop (2*rest.length-1)) s.basis=0 := by
            simpa [rest,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using htop
          have hi := ih tail hnTail htail s topTail
          let out := run (signedSquareTop rest tail) m s
          have dstN : (a::b::tail).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := List.nodup_iff_count.mp hnd q
            simp only [List.count_cons,List.count_append] at h ⊢
            omega
          have lowSame : regValue [a,b] out.basis=regValue [a,b] s.basis := by
            apply regValue_congr
            intro q hq
            exact hi.2.2.1 q (fun ht =>
              List.disjoint_left.mp (List.disjoint_take_drop dstN (show 2≤2 from le_rfl)) hq ht)
          have splitS := regValue_append [a,b] tail s.basis
          have splitO := regValue_append [a,b] tail out.basis
          change out.phase=s.phase ∧ _
          refine ⟨hi.1,?_,?_,?_⟩
          · change regValue (a::b::tail) out.basis=
              regValue (a::b::tail) s.basis+signedTopTerm (x::rest) s.basis
            rw [← show [a,b]++tail=a::b::tail by rfl,splitO,lowSame,hi.2.1,splitS]
            simp [signedTopTerm,rest]
            omega
          · intro q hq
            exact hi.2.2.1 q (fun ht => hq (by simp [ht]))
          · have srcSame : regValue rest out.basis=regValue rest s.basis := hi.2.2.2
            change (if out.basis x then 1 else 0)+2*regValue rest out.basis=
              (if s.basis x then 1 else 0)+2*regValue rest s.basis
            rw [srcSame,hi.2.2.1 x (by
              intro ht
              have hn := List.nodup_iff_count.mp hnd x
              have h2 := List.count_pos_iff.mpr ht
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at hn
              omega)]

theorem signedSquareTop_roundtrip (xs dst : List Wire) (hnd : (xs++dst).Nodup)
    (s : State) (m : List Bool) :
    run (signedSquareTop xs dst++signedSquareTop xs dst) m s=s := by
  induction xs generalizing dst s with
  | nil => simp [signedSquareTop,run]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,run]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,run]
        | cons z tail =>
          have hxz : x≠z := by
            intro e; subst z; simp at hnd
          simp [signedSquareTop,run,writeBit,hxz]
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,run]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,run]
        | cons b tail =>
          have hn : (y::ys++tail).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := List.nodup_iff_count.mp hnd q
            simp only [List.count_cons,List.count_append] at h ⊢
            omega
          simpa [signedSquareTop] using ih tail hn s

theorem signedTriangularSquare_forward_correct (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool)
    (hd0 : regValue dst s.basis=0) (hp0 : regValue pad s.basis=0)
    (hm0 : regValue mask s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    let out := run (signedTriangularSquare xs dst pad mask carry cin) records s
    out.phase=s.phase ∧ regValue dst out.basis=(regValue xs s.basis)^2 ∧
      regValue xs out.basis=regValue xs s.basis ∧ regValue pad out.basis=0 ∧
      regValue mask out.basis=0 ∧ regValue carry out.basis=0 ∧ out.basis cin=false := by
  let rows := signedSquareRows xs dst pad carry
  let top := signedSquareTop xs dst
  let diag := signedDiagSub xs dst mask carry cin
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
  have rc := signedSquareRows_correct xs dst pad carry ndRows hd (Or.inr hp)
    (by omega) s (records.take (measurementCount rows)) 0 hd0 high0 work0
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
  have dc := signedDiagSub_correct cin xs dst mask carry ndDiag xsne hd hm hc v
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
    exact signedDiagSub_preserves_outside cin xs dst mask carry (by omega) hd hm hc v
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
      simpa [signedTriangularSquare,rows,top,diag,rest,u,v,out,run_append] using final

/-- Give a program an exact record stream: supplied outcomes first, followed
by the interpreter's default zero outcomes if the supplied stream is short. -/
private def normalizedRecords : Program → List Bool → List Bool
  | [], _ => []
  | .measureX _ _ _ :: p, [] => false::normalizedRecords p []
  | .measureX _ _ _ :: p, b::bs => b::normalizedRecords p bs
  | _::p, m => normalizedRecords p m

private theorem run_append_normalized (p q : Program) (m₁ m₂ : List Bool) (s : State) :
    run (p++q) (normalizedRecords p m₁++m₂) s=run q m₂ (run p m₁ s) := by
  induction p generalizing m₁ s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [normalizedRecords,List.cons_append,run]
    all_goals try exact ih m₁ _
    cases m₁ <;> simp [normalizedRecords,ih]

private theorem signedSquareRows_roundtrip_separate (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : xs.length≤1 ∨ 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m₁ m₂ : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    run (signedSquareRowsClear xs dst pad carry) m₂
      (run (signedSquareRows xs dst pad carry) m₁ s)=s := by
  let rows := signedSquareRows xs dst pad carry
  let clear := signedSquareRowsClear xs dst pad carry
  have hr := signedSquareRows_roundtrip xs dst pad carry hnd hd hp hc s
    (normalizedRecords rows m₁++m₂) A hv hhi hw
  have he := run_append_normalized rows clear m₁ m₂ s
  rw [show signedSquareRows xs dst pad carry++signedSquareRowsClear xs dst pad carry=
    rows++clear by rfl,he] at hr
  let out := run clear m₂ (run rows m₁ s)
  have hp' : out.phase=s.phase := hr.1
  have hb' : out.basis=s.basis := hr.2
  calc
    run clear m₂ (run rows m₁ s) = ⟨out.phase,out.basis⟩ := rfl
    _ = ⟨s.phase,s.basis⟩ := by rw [hp',hb']
    _ = s := rfl

private theorem signedSquareTop_roundtrip_separate (xs dst : List Wire)
    (hnd : (xs++dst).Nodup) (s : State) (m₁ m₂ : List Bool) :
    run (signedSquareTop xs dst) m₂ (run (signedSquareTop xs dst) m₁ s)=s := by
  let top := signedSquareTop xs dst
  have hr := signedSquareTop_roundtrip xs dst hnd s (normalizedRecords top m₁++m₂)
  have he := run_append_normalized top top m₁ m₂ s
  simpa [top,he] using hr

/-- The independently measured cleanup leaf restores the complete physical
state after the signed triangular square producer. -/
theorem signedTriangularSquare_roundtrip (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hm : xs.length≤mask.length)
    (hc : dst.length-1≤carry.length)
    (s : State) (forwardRecords clearRecords : List Bool)
    (hd0 : regValue dst s.basis=0) (hp0 : regValue pad s.basis=0)
    (hm0 : regValue mask s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    run (signedTriangularSquareClear xs dst pad mask carry cin) clearRecords
      (run (signedTriangularSquare xs dst pad mask carry cin) forwardRecords s)=s := by
  let rows := signedSquareRows xs dst pad carry
  let top := signedSquareTop xs dst
  let sub := signedDiagSub xs dst mask carry cin
  let add := signedDiagAdd xs dst mask carry cin
  let clearRows := signedSquareRowsClear xs dst pad carry
  let forwardRest := forwardRecords.drop (measurementCount rows)
  let clearRest := clearRecords.drop (measurementCount add)
  let u := run rows (forwardRecords.take (measurementCount rows)) s
  let v := run top (forwardRest.take (measurementCount top)) u
  let w := run sub (forwardRest.drop (measurementCount top)) v
  let a := run add (clearRecords.take (measurementCount add)) w
  let b := run top (clearRest.take (measurementCount top)) a
  let out := run clearRows (clearRest.drop (measurementCount top)) b
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
  have ndDiag : (cin::xs++mask++dst++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have high0 : regValue (dst.drop xs.length) s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    exact (regValue_zero _ _).mp hd0 q (List.mem_of_mem_drop hq)
  have work0 : regValue (pad++carry) s.basis=0 := by
    simp [regValue_append,hp0,hc0]
  have rc := signedSquareRows_correct xs dst pad carry ndRows hd (Or.inr hp)
    (by omega) s (forwardRecords.take (measurementCount rows)) 0 hd0 high0 work0
  have tc := signedSquareTop_correct xs dst ndTop hd u
    (forwardRest.take (measurementCount top)) rc.2.2.2.2
  have keepR (q : Wire) (hq : q∉dst) : u.basis q=s.basis q := rc.2.2.1 q hq
  have keepT (q : Wire) (hq : q∉dst) : v.basis q=u.basis q := tc.2.2.1 q hq
  have away (q : Wire) (hq : q∈cin::xs++pad++mask++carry) : q∉dst := by
    intro hdq
    have hn := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hdq
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  have regV (r : List Wire) (hr : r=mask ∨ r=carry)
      (h0 : regValue r s.basis=0) : regValue r v.basis=0 := by
    rw [← h0]
    apply regValue_congr; intro q hq
    exact (keepT q (away q (by rcases hr with rfl|rfl <;> simp [hq]))).trans
      (keepR q (away q (by rcases hr with rfl|rfl <;> simp [hq])))
  have maskV := regV mask (Or.inl rfl) hm0
  have carryV := regV carry (Or.inr rfl) hc0
  have cinV : v.basis cin=false :=
    ((keepT cin (away cin (by simp))).trans (keepR cin (away cin (by simp)))).trans hi0
  have diagRestore : a=v := signedDiag_roundtrip cin xs dst mask carry ndDiag
    (List.ne_nil_of_length_pos (by omega)) hd hm hc v
    (forwardRest.drop (measurementCount top))
    (clearRecords.take (measurementCount add)) maskV carryV cinV
  have topRestore : run top (clearRest.take (measurementCount top)) v=u := by
    exact signedSquareTop_roundtrip_separate xs dst ndTop u
      (forwardRest.take (measurementCount top)) (clearRest.take (measurementCount top))
  have rowsRestore : run clearRows (clearRest.drop (measurementCount top)) u=s := by
    exact signedSquareRows_roundtrip_separate xs dst pad carry ndRows hd (Or.inr hp)
      (by omega) s (forwardRecords.take (measurementCount rows))
      (clearRest.drop (measurementCount top)) 0 hd0 high0 work0
  have staged : out=s := by
    change run clearRows (clearRest.drop (measurementCount top))
      (run top (clearRest.take (measurementCount top)) a)=s
    rw [diagRestore,topRestore,rowsRestore]
  cases xs with
  | nil => simp at hx
  | cons x tail =>
    cases tail with
    | nil => simp at hx
    | cons y ys =>
      simpa [signedTriangularSquare,signedTriangularSquareClear,rows,top,sub,add,
        clearRows,forwardRest,clearRest,u,v,w,a,b,out,run_append] using staged

end ECDSAAdd.Arithmetic
