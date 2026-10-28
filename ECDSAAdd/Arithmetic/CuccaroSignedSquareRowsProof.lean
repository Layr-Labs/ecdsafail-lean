import ECDSAAdd.Arithmetic.CuccaroSignedSquare

namespace ECDSAAdd.Arithmetic

private theorem cuccaro_drop_tail_sublist (dst : List Wire) (n : Nat) :
    (dst.drop (n+1)).Sublist (dst.drop n) := by
  have h := List.drop_sublist 1 (dst.drop n)
  simpa [List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h


theorem cuccaroSignedSquareRows_correct (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : xs.length≤1 ∨ 1≤pad.length)
    (s : State) (m : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    let out := run (cuccaroSignedSquareRows xs dst pad carry) m s
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
      simp only [List.length_cons] at hd hp hhi
      let rest := d::tail
      let n := rest.length+1
      let row := (dst.drop 1).take n
      let dst2 := dst.drop 2
      have hpad : 1≤pad.length := by
        rcases hp with hp|hp
        · simp at hp
        · exact hp
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
      have rf := cuccaroSignedSquareRow_frame c rest row pad carry ndrow rowLen hpad
        s.basis (s.basis c) rfl work0 (A/2) rowBound
      let mr := m.take (measurementCount (cuccaroSignedSquareRow c rest row pad carry))
      let u := run (cuccaroSignedSquareRow c rest row pad carry) mr s
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
        change regValue row (run (cuccaroSignedSquareRow c rest row pad carry) mr s).basis=_
        rw [ru.2.1,delta]
      have keepRow (q : Wire) (hq : q∉row) : u.basis q=s.basis q := ru.2.2 q hq
      have lift := signed_row_lift_update dst n A D (by omega)
        dstN s.basis u.basis hv rowOut
        (by
          have sub := cuccaro_drop_tail_sublist dst n
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
      have recResult := ih dst2 (by simpa [rest] using ndrec) (by simpa [rest] using dst2Len)
        (Or.inr hpad) u
        (m.drop (measurementCount (cuccaroSignedSquareRow c rest row pad carry))) A2 rfl
        (by simpa [rest] using high2) workU
      let out := run (cuccaroSignedSquareRows rest dst2 pad carry)
        (m.drop (measurementCount (cuccaroSignedSquareRow c rest row pad carry))) u
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
      rw [cuccaroSignedSquareRows,run_append]
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


end ECDSAAdd.Arithmetic
