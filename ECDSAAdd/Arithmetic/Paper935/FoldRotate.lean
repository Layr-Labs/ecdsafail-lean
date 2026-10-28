import ECDSAAdd.Arithmetic.Paper935.Repack

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

private theorem rotate_value (a : Wire) (bs : List Wire) (hnd : (a::bs).Nodup)
    (s : State) (m : List Bool) :
    regValue (a::bs) (run (rotateRight (a::bs)) m s).basis=
      regValue bs s.basis+2^bs.length*(s.basis a).toNat := by
  induction bs generalizing a s with
  | nil => simp [rotateRight,run,regValue,Bool.toNat]
  | cons b bs ih =>
    have ha := (List.nodup_cons.mp hnd).1
    have ht := (List.nodup_cons.mp hnd).2
    have hab : a≠b := fun hh => ha (by simp [hh])
    let s1 := run (swapBits a b) m s
    have hv := ih b ht s1
    have swap := (rehome_run a b hab s m).2
    have hA : s1.basis a=s.basis b := by simpa only [Equiv.swap_apply_right] using swap b
    have hB : s1.basis b=s.basis a := by simpa only [Equiv.swap_apply_left] using swap a
    have hbs : regValue bs s1.basis=regValue bs s.basis := regValue_congr _ _ _ (by
      intro q hq
      have qa : q≠a := by intro hh; subst q; exact ha (List.mem_cons_of_mem _ hq)
      have qb : q≠b := by intro hh; subst q; exact (List.nodup_cons.mp ht).1 hq
      simpa only [Equiv.swap_apply_of_ne_of_ne qa qb] using swap q)
    have hk := (rotate_frame (b::bs) s1 m).2.1 a ha
    change regValue (a::b::bs) (run (swapBits a b ++ rotateRight (b::bs)) m s).basis=_
    rw [run_append,run_take]
    change (if (run (rotateRight (b::bs)) m s1).basis a then 1 else 0)+
      2*regValue (b::bs) (run (rotateRight (b::bs)) m s1).basis=_
    rw [hk,hv,hbs,hA,hB]
    simp only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,List.length_cons,pow_succ]
    ring

/-- Actual adjacent three-CX swaps implement cyclic halving, including the
odd input whose old low bit must become the high bit. -/
theorem foldRotate_value (r : List Wire) (hn : r.Nodup) (s : State) (m : List Bool) :
    regValue r (run (rotateRight r) m s).basis=
      regValue r s.basis/2+(regValue r s.basis%2)*2^(r.length-1) := by
  cases r with
  | nil => simp [regValue,rotateRight,run]
  | cons a bs =>
    rw [rotate_value a bs hn s m]
    have value : regValue (a::bs) s.basis=(s.basis a).toNat+2*regValue bs s.basis := by
      simp only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite]
    rw [value]
    simp only [List.length_cons,Nat.add_sub_cancel]
    cases s.basis a <;> simp [Nat.mul_comm]
    omega

end ECDSAAdd.Arithmetic.Paper935
