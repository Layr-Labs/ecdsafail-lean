import ECDSAAdd.Arithmetic.SignedTriangularSquareProof

namespace ECDSAAdd.Arithmetic

private theorem row_tail_identity (dst : List Wire) (n : Nat) :
    (dst.drop 1).take n++dst.drop (n+1)=dst.drop 1 := by
  rw [show dst.drop (n+1)=(dst.drop 1).drop n by
    rw [List.drop_drop]; congr 1; omega]
  exact List.take_append_drop n (dst.drop 1)

private theorem drop_tail_sublist (dst : List Wire) (n : Nat) :
    (dst.drop (n+1)).Sublist (dst.drop n) := by
  have h := List.drop_sublist 1 (dst.drop n)
  simpa [List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

private theorem drop_value_div_local (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.drop n) s=regValue r s/2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  have hl : regValue (r.take n) s<2^n := by
    simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [h,Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),Nat.div_eq_of_lt hl,Nat.zero_add]

/-- If bits `n` and above are clean, the row window at positions `1..n`
contains exactly the full word divided by two. -/
theorem signed_row_slice_value (dst : List Wire) (n A : Nat) (hn : 1≤dst.length)
    (s : BasisState) (hv : regValue dst s=A)
    (hhi : regValue (dst.drop n) s=0) :
    regValue ((dst.drop 1).take n) s=A/2 := by
  have tail0 : regValue (dst.drop (n+1)) s=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero _ _).mp hhi q ((drop_tail_sublist dst n).subset hq)
  have split := regValue_append ((dst.drop 1).take n) (dst.drop (n+1)) s
  rw [row_tail_identity,tail0,Nat.mul_zero,Nat.add_zero] at split
  have dropv := drop_value_div_local dst 1 hn s
  rw [hv] at dropv
  exact split.symm.trans dropv

/-- Updating only the row window by `D` updates the complete word by `2D` and
preserves the clean tail above the row. -/
theorem signed_row_lift_update (dst : List Wire) (n A D : Nat)
    (hn : 1≤dst.length) (hnd : dst.Nodup) (s t : BasisState)
    (hv : regValue dst s=A)
    (hrow : regValue ((dst.drop 1).take n) t=A/2+D)
    (htail : regValue (dst.drop (n+1)) s=0)
    (hkeep : ∀q,q∉(dst.drop 1).take n → t q=s q) :
    regValue dst t=A+2*D ∧ regValue (dst.drop (n+1)) t=0 := by
  let row := (dst.drop 1).take n
  let tail := dst.drop (n+1)
  have dropN : (dst.drop 1).Nodup := (List.drop_sublist 1 dst).nodup hnd
  have dis : row.Disjoint tail := by
    have h := List.disjoint_take_drop dropN (Nat.le_refl n)
    simpa [row,tail,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
  have tailt : regValue tail t=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    rw [hkeep q (fun hr => List.disjoint_left.mp dis hr hq)]
    exact (regValue_zero _ _).mp htail q hq
  have drop1t := regValue_append row tail t
  rw [row_tail_identity,hrow,tailt,Nat.mul_zero,Nat.add_zero] at drop1t
  have take1same : regValue (dst.take 1) t=regValue (dst.take 1) s := by
    apply regValue_congr
    intro q hq
    apply hkeep q
    intro hr
    have dis1 := List.disjoint_take_drop hnd (show 1≤1 from le_rfl)
    exact List.disjoint_left.mp dis1 hq (List.mem_of_mem_take hr)
  have ss := regValue_append (dst.take 1) (dst.drop 1) s
  have tt := regValue_append (dst.take 1) (dst.drop 1) t
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at ss tt
  have drop1s := drop_value_div_local dst 1 hn s
  rw [hv] at drop1s
  constructor
  · rw [tt,take1same,drop1t,← hv,ss,drop1s]
    norm_num
    omega
  · exact tailt

/-- Exact semantics of the complete overlapping signed-row ladder. -/
theorem signedSquareRows_correct (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : xs.length≤1 ∨ 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    let out := run (signedSquareRows xs dst pad carry) m s
    out.phase=s.phase ∧ regValue dst out.basis=A+signedRowsValue xs s.basis ∧
      (∀q,q∉dst → out.basis q=s.basis q) ∧ regValue (pad++carry) out.basis=0 ∧
      regValue (dst.drop (2*xs.length-1)) out.basis=0 := by
  induction xs generalizing dst s m A with
  | nil =>
    have de : dst=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst dst
    have ha : A=0 := by simpa using hv.symm
    subst A
    change s.phase=s.phase ∧ regValue [] s.basis=0+0 ∧
      (∀q,q∉[] → s.basis q=s.basis q) ∧ regValue (pad++carry) s.basis=0 ∧
      regValue [] s.basis=0
    exact ⟨rfl,rfl,fun _ _ => rfl,hw,rfl⟩
  | cons c xs ih =>
    cases xs with
    | nil =>
      simp only [List.length_cons,List.length_nil] at hd hhi ⊢
      refine ⟨rfl,?_,fun _ _ => rfl,hw,?_⟩
      · simpa [signedRowsValue] using hv
      · simpa using hhi
    | cons d tail =>
      simp only [List.length_cons] at hd hp hc hhi
      let rest := d::tail
      let n := rest.length+1
      let row := (dst.drop 1).take n
      let dst2 := dst.drop 2
      have hpad : 1≤pad.length := by
        rcases hp with hp|hp
        · simp at hp
        · exact hp
      have hcarry : rest.length≤carry.length := by
        change tail.length+1≤carry.length
        omega
      have hdst : 2≤dst.length := by omega
      have rowLen : row.length=rest.length+1 := by
        have cap : n≤(dst.drop 1).length := by dsimp [n,rest]; simp; omega
        simpa [row,n] using List.length_take_of_le cap
      have dst2Len : dst2.length=2*rest.length := by
        dsimp [dst2,rest]
        simp
        omega
      have rowSub : row.Sublist dst :=
        (List.take_sublist n (dst.drop 1)).trans (List.drop_sublist 1 dst)
      have dst2Sub : dst2.Sublist dst := List.drop_sublist 2 dst
      have ndrow : (c::rest++row++pad++carry).Nodup := by
        have pre := (List.Sublist.refl (c::rest)).append rowSub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub : (c::rest++row++pad++carry).Sublist
            (c::rest++dst++pad++carry) := by simpa [List.append_assoc] using all
        exact sub.nodup hnd
      have ndrec : (rest++dst2++pad++carry).Nodup := by
        have pre := (List.Sublist.refl rest).append dst2Sub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub0 : (rest++dst2++pad++carry).Sublist (rest++dst++pad++carry) := by
          simpa [List.append_assoc] using all
        have htail : (rest++dst++pad++carry).Nodup := by
          simpa [rest,List.append_assoc] using (List.nodup_cons.mp hnd).2
        exact sub0.nodup htail
      have dstN : dst.Nodup := by
        apply List.nodup_iff_count.mpr
        intro q
        have hh := List.nodup_iff_count.mp hnd q
        simp only [List.count_cons,List.count_append] at hh ⊢
        omega
      have high0 : regValue (dst.drop n) s.basis=0 := by
        simpa [n,rest] using hhi
      have rowv : regValue row s.basis=A/2 := by
        simpa [row,n] using signed_row_slice_value dst n A (by omega) s.basis hv high0
      have work0 : regValue (pad++carry) s.basis=0 := hw
      have rowBound : A/2<2^row.length := by
        rw [← rowv]
        exact regValue_lt row s.basis
      have rf := signedSquareRow_frame c rest row pad carry ndrow rowLen hpad hcarry
        s.basis (s.basis c) rfl work0 (A/2) rowBound
      let mr := m.take (measurementCount (signedSquareRow c rest row pad carry))
      let u := run (signedSquareRow c rest row pad carry) mr s
      have ru := rf s mr ⟨rowv,fun _ _ => rfl⟩
      let D := signedDeltaValue c rest s.basis
      have delta : signedRowValue (s.basis c) (A/2) (regValue rest s.basis) rest.length=A/2+D := by
        have hbA : A/2<2^rest.length := by
          have hnDst : n≤dst.length := by dsimp [n,rest]; omega
          have Ahi : A<2^n := by
            have split := regValue_append (dst.take n) (dst.drop n) s.basis
            rw [List.take_append_drop,List.length_take,Nat.min_eq_left hnDst,
              high0,Nat.mul_zero,Nat.add_zero,hv] at split
            rw [split]
            have b := regValue_lt (dst.take n) s.basis
            simpa [List.length_take,Nat.min_eq_left hnDst] using b
          dsimp [n] at Ahi
          rw [Nat.pow_succ] at Ahi
          omega
        have hbS := regValue_lt rest s.basis
        cases hb : s.basis c
        · simp only [signedRowValue,hb,Bool.false_eq_true,if_false,signedDeltaValue,D]
          have hlt : A/2+2^rest.length-regValue rest s.basis<2^(rest.length+1) := by
            rw [Nat.pow_succ]; omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
        · simp only [signedRowValue,hb,if_true,signedDeltaValue,D]
          have hlt : A/2+regValue rest s.basis+1<2^(rest.length+1) := by
            rw [Nat.pow_succ]; omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
      have rowOut : regValue row u.basis=A/2+D := by
        change regValue row (run (signedSquareRow c rest row pad carry) mr s).basis=_
        rw [ru.2.1,delta]
      have keepRow (q : Wire) (hq : q∉row) : u.basis q=s.basis q := ru.2.2 q hq
      have lift := signed_row_lift_update dst n A D (by omega)
        dstN s.basis u.basis hv rowOut
        (by
          have sub := drop_tail_sublist dst n
          apply (regValue_zero _ _).mpr; intro q hq
          exact (regValue_zero _ _).mp high0 q (sub.subset hq)) keepRow
      have workU : regValue (pad++carry) u.basis=0 := by
        rw [← hw]
        apply regValue_congr
        intro q hq
        apply keepRow q
        intro hr
        have hnq := List.nodup_iff_count.mp ndrow q
        have h1 := List.count_pos_iff.mpr hq
        have h2 := List.count_pos_iff.mpr hr
        simp only [List.count_cons,List.count_append] at hnq h1
        omega
      have high2 : regValue (dst2.drop rest.length) u.basis=0 := by
        simpa [dst2,n,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using lift.2
      let A2 := regValue dst2 u.basis
      have hcrec : rest.length-1≤carry.length := by omega
      have recResult := ih dst2 (by simpa [rest] using ndrec) (by simpa [rest] using dst2Len)
        (Or.inr hpad) (by simpa [rest] using hcrec) u
        (m.drop (measurementCount (signedSquareRow c rest row pad carry))) A2 rfl
        (by simpa [rest] using high2) workU
      let out := run (signedSquareRows rest dst2 pad carry)
        (m.drop (measurementCount (signedSquareRow c rest row pad carry))) u
      have restRows : signedRowsValue rest u.basis=signedRowsValue rest s.basis := by
        apply signedRowsValue_congr
        intro q hq
        apply keepRow q
        intro hr
        have hnq := List.nodup_iff_count.mp ndrow q
        have h1 := List.count_pos_iff.mpr hq
        have h2 := List.count_pos_iff.mpr hr
        simp only [List.count_cons,List.count_append] at hnq h1
        omega
      have low2same : regValue (dst.take 2) out.basis=regValue (dst.take 2) u.basis := by
        apply regValue_congr
        intro q hq
        exact recResult.2.2.1 q (fun hdq => by
          have dis := List.disjoint_take_drop dstN (show 2≤2 from le_rfl)
          exact List.disjoint_left.mp dis hq hdq)
      have finalValue : regValue dst out.basis=A+signedRowsValue (c::rest) s.basis := by
        have su := regValue_append (dst.take 2) dst2 u.basis
        have so := regValue_append (dst.take 2) dst2 out.basis
        rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at su so
        have su' : regValue (dst.take 2) u.basis+4*A2=A+2*D := by
          dsimp [A2]
          norm_num at su ⊢
          rw [← su,lift.1]
        rw [so,low2same,recResult.2.1,restRows]
        norm_num
        have rowsFull : signedRowsValue (c::rest) s.basis=
            2*D+4*signedRowsValue rest s.basis := by
          simp [signedRowsValue,D,rest]
        rw [rowsFull]
        omega
      rw [signedSquareRows,run_append]
      change out.phase=s.phase ∧ _
      refine ⟨recResult.1.trans ru.1,finalValue,?_,recResult.2.2.2.1,?_⟩
      · intro q hq
        exact (recResult.2.2.1 q (fun hdq => hq (dst2Sub.subset hdq))).trans
          (keepRow q (fun hr => hq (rowSub.subset hr)))
      · have top := recResult.2.2.2.2
        change regValue (dst2.drop (2*rest.length-1)) out.basis=0 at top
        have he : 2+(2*rest.length-1)=2*(rest.length+1)-1 := by
          have : 1≤rest.length := by simp [rest]
          omega
        dsimp [dst2] at top
        rw [List.drop_drop,he] at top
        change regValue (dst.drop (2*(rest.length+1)-1)) out.basis=0
        exact top

theorem signedSquareRows_roundtrip (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : xs.length≤1 ∨ 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    let out := run (signedSquareRows xs dst pad carry++
      signedSquareRowsClear xs dst pad carry) m s
    out.phase=s.phase ∧ out.basis=s.basis := by
  induction xs generalizing dst s m A with
  | nil =>
    have de : dst=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst dst
    simp [signedSquareRows,signedSquareRowsClear,run]
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedSquareRows,signedSquareRowsClear,run]
    | cons d tail =>
      simp only [List.length_cons] at hd hp hc hhi
      let rest := d::tail
      let n := rest.length+1
      let row := (dst.drop 1).take n
      let dst2 := dst.drop 2
      let rfwd := signedSquareRow c rest row pad carry
      let rclr := signedSquareRowClear c rest row pad carry
      let middle := signedSquareRows rest dst2 pad carry++signedSquareRowsClear rest dst2 pad carry
      have hpad : 1≤pad.length := by rcases hp with hp|hp <;> omega
      have hcarry : rest.length≤carry.length := by change tail.length+1≤carry.length; omega
      have rowLen : row.length=rest.length+1 := by
        have cap : n≤(dst.drop 1).length := by dsimp [n,rest]; simp; omega
        simpa [row,n] using List.length_take_of_le cap
      have dst2Len : dst2.length=2*rest.length := by dsimp [dst2,rest]; simp; omega
      have rowSub : row.Sublist dst :=
        (List.take_sublist n (dst.drop 1)).trans (List.drop_sublist 1 dst)
      have dst2Sub : dst2.Sublist dst := List.drop_sublist 2 dst
      have ndrow : (c::rest++row++pad++carry).Nodup := by
        have pre := (List.Sublist.refl (c::rest)).append rowSub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub : (c::rest++row++pad++carry).Sublist
            (c::rest++dst++pad++carry) := by simpa [List.append_assoc] using all
        exact sub.nodup hnd
      have ndrec : (rest++dst2++pad++carry).Nodup := by
        have pre := (List.Sublist.refl rest).append dst2Sub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub0 : (rest++dst2++pad++carry).Sublist (rest++dst++pad++carry) := by
          simpa [List.append_assoc] using all
        have ht : (rest++dst++pad++carry).Nodup := by
          simpa [rest,List.append_assoc] using (List.nodup_cons.mp hnd).2
        exact sub0.nodup ht
      have dstN : dst.Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hnd q
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
      have high0 : regValue (dst.drop n) s.basis=0 := by simpa [n,rest] using hhi
      have rowv : regValue row s.basis=A/2 := by
        simpa [row,n] using signed_row_slice_value dst n A (by omega) s.basis hv high0
      have hA : A/2<2^rest.length := by
        have hnDst : n≤dst.length := by dsimp [n,rest]; omega
        have split := regValue_append (dst.take n) (dst.drop n) s.basis
        rw [List.take_append_drop,List.length_take,Nat.min_eq_left hnDst,
          high0,Nat.mul_zero,Nat.add_zero,hv] at split
        have b := regValue_lt (dst.take n) s.basis
        rw [List.length_take,Nat.min_eq_left hnDst] at b
        dsimp [n] at split b
        rw [Nat.pow_succ] at b
        omega
      have work0 : regValue (pad++carry) s.basis=0 := hw
      have ff := signedSquareRow_frame c rest row pad carry ndrow rowLen hpad hcarry
        s.basis (s.basis c) rfl work0 (A/2)
        (hA.trans (Nat.pow_lt_pow_right (by decide) (by omega)))
      let m1 := m.drop (measurementCount rfwd)
      let u := run rfwd (m.take (measurementCount rfwd)) s
      have fu := ff s (m.take (measurementCount rfwd)) ⟨rowv,fun _ _ => rfl⟩
      let D := signedDeltaValue c rest s.basis
      have delta : signedRowValue (s.basis c) (A/2) (regValue rest s.basis) rest.length=A/2+D := by
        have hs := regValue_lt rest s.basis
        cases hb : s.basis c
        · simp only [signedRowValue,hb,Bool.false_eq_true,if_false,signedDeltaValue,D]
          have fit : A/2+2^rest.length-regValue rest s.basis<2^(rest.length+1) := by
            rw [Nat.pow_succ]; omega
          rw [Nat.mod_eq_of_lt fit]; omega
        · simp only [signedRowValue,hb,if_true,signedDeltaValue,D]
          have fit : A/2+regValue rest s.basis+1<2^(rest.length+1) := by
            rw [Nat.pow_succ]; omega
          rw [Nat.mod_eq_of_lt fit]; omega
      have rowU : regValue row u.basis=A/2+D := by
        change regValue row (run rfwd (m.take (measurementCount rfwd)) s).basis=_
        rw [fu.2.1,delta]
      have keepU (q : Wire) (hq : q∉row) : u.basis q=s.basis q := fu.2.2 q hq
      have lift := signed_row_lift_update dst n A D (by omega) dstN s.basis u.basis
        hv rowU (by
          have sub := drop_tail_sublist dst n
          apply (regValue_zero _ _).mpr; intro q hq
          exact (regValue_zero _ _).mp high0 q (sub.subset hq)) keepU
      have workU : regValue (pad++carry) u.basis=0 := by
        rw [← hw]; apply regValue_congr; intro q hq; apply keepU q
        intro hr
        have hn := List.nodup_iff_count.mp ndrow q
        have h1 := List.count_pos_iff.mpr hq
        have h2 := List.count_pos_iff.mpr hr
        simp only [List.count_cons,List.count_append] at hn h1
        omega
      have high2 : regValue (dst2.drop rest.length) u.basis=0 := by
        simpa [dst2,n,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using lift.2
      let A2 := regValue dst2 u.basis
      have hcrec : rest.length-1≤carry.length := by omega
      have mid := ih dst2 (by simpa [rest] using ndrec) (by simpa [rest] using dst2Len)
        (Or.inr hpad) (by simpa [rest] using hcrec) u (m1.take (measurementCount middle)) A2 rfl
        (by simpa [rest] using high2) workU
      let w := run middle (m1.take (measurementCount middle)) u
      have wbasis : w.basis=u.basis := mid.2
      have wphase : w.phase=u.phase := mid.1
      have rr := signedSquareRowClear_frame c rest row pad carry ndrow rowLen hpad hcarry
        s.basis (s.basis c) rfl work0 (A/2) hA
      have preW : SquareFrame row s.basis
          (signedRowValue (s.basis c) (A/2) (regValue rest s.basis) rest.length) w.basis := by
        rw [wbasis]
        exact fu.2
      let out := run rclr (m1.drop (measurementCount middle)) w
      have fin := rr w (m1.drop (measurementCount middle)) preW
      change out.phase=w.phase ∧ SquareFrame row s.basis (A/2) out.basis at fin
      have outbasis : out.basis=s.basis := by
        funext q
        by_cases hq : q∈row
        · exact (regValue_eq_iff row out.basis s.basis).mp (fin.2.1.trans rowv.symm) q hq
        · exact fin.2.2 q hq
      have outphase : out.phase=s.phase := fin.1.trans (wphase.trans fu.1)
      have exec : run (rfwd++(middle++rclr)) m s=out := by
        rw [run_append]
        change run (middle++rclr) m1 u=out
        rw [run_append]
      have result : (run (rfwd++(middle++rclr)) m s).phase=s.phase ∧
          (run (rfwd++(middle++rclr)) m s).basis=s.basis := by
        rw [exec]
        exact ⟨outphase,outbasis⟩
      change (run (signedSquareRows (c::rest) dst pad carry++
        signedSquareRowsClear (c::rest) dst pad carry) m s).phase=s.phase ∧
        (run (signedSquareRows (c::rest) dst pad carry++
          signedSquareRowsClear (c::rest) dst pad carry) m s).basis=s.basis
      rw [show signedSquareRows (c::rest) dst pad carry=
        rfwd++signedSquareRows rest dst2 pad carry by rfl,
        show signedSquareRowsClear (c::rest) dst pad carry=
          signedSquareRowsClear rest dst2 pad carry++rclr by rfl]
      simpa [middle,List.append_assoc] using result

end ECDSAAdd.Arithmetic
