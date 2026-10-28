import ECDSAAdd.Arithmetic.Paper935.HistoryPredicate

namespace ECDSAAdd.Arithmetic.Paper935

private theorem odd_factor_value {v q : Int} {j : Nat}
    (hq : q%2=1) (hv : v=(2:Int)^j*q) : padicValInt 2 v=j := by
  rw [hv,padicValInt.mul (by positivity) (by omega),
    padicValInt.eq_zero_of_not_dvd (p:=2) (z:=q) (by push_cast; omega),add_zero,
    show ((2:Int)^j)=((2^j:Nat):Int) by push_cast; ring,
    padicValInt.of_nat,padicValNat.prime_pow]

/-- Positive finite valuation is an exact low residue, including for negative
integers. The positive-depth premise excludes valuation's zero convention. -/
theorem depthResidue_iff (v : Int) (j : Nat) (hj : 0<j) :
    v%(2:Int)^(j+1)=(2:Int)^j ↔ padicValInt 2 v=j := by
  constructor
  · intro h
    have he := Int.mul_ediv_add_emod v ((2:Int)^(j+1))
    have hv : v=(2:Int)^j*(2*(v/(2:Int)^(j+1))+1) := by
      rw [h,pow_succ] at he
      rw [pow_succ]
      linear_combination -he
    apply odd_factor_value (q:=2*(v/(2:Int)^(j+1))+1) (by omega) hv
  · intro hv
    have hn : v≠0 := by intro h; subst v; simp at hv; omega
    have hd : (2:Int)^j ∣ v := (historyCutoff_valuation v j).mpr (Or.inr (by omega))
    obtain ⟨q,hq⟩ := hd
    have hodd : q%2=1 := by
      have h0 := Int.emod_nonneg q (by norm_num : (2:Int)≠0)
      have h2 := Int.emod_lt_of_pos q (by norm_num : (0:Int)<2)
      by_contra h
      have he : q%2=0 := by omega
      obtain ⟨k,hk⟩ := Int.dvd_of_emod_eq_zero he
      have hnext : (2:Int)^(j+1)∣v := by
        refine ⟨k,?_⟩
        rw [hq,hk,pow_succ]
        ring
      have hh := (historyCutoff_valuation v (j+1)).mp hnext
      rcases hh with hh | hh
      · exact hn hh
      · omega
    rw [hq,pow_succ,Int.mul_emod_mul_of_pos q 2 (by positivity : (0:Int)<2^j),hodd,mul_one]


private theorem signed_prefix (xs tail : List Wire) (s : BasisState) (hne : tail≠[]) :
    signedRegValue (xs++tail) s=(regValue xs s:Int)+(2:Int)^xs.length*signedRegValue tail s := by
  induction xs with
  | nil => simp [regValue]
  | cons w xs ih =>
    rw [List.cons_append,signedRegValue_cons w (xs++tail) s (by simp [hne]),ih]
    cases hw : s w <;> simp [regValue,hw,pow_succ] <;> ring

private theorem signed_prefix_mod (xs tail : List Wire) (s : BasisState) (hne : tail≠[]) :
    signedRegValue (xs++tail) s%(2:Int)^xs.length=(regValue xs s:Int) := by
  rw [signed_prefix xs tail s hne,Int.add_emod,Int.mul_emod_right,add_zero,Int.emod_emod]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast regValue_lt xs s)

/-- The actual equality comparator on coefficient bits one through j
recognizes valuation j. It rejects zero coefficient automatically. -/
theorem historyDepth_test (vlow : Wire) (bits tail : List Wire) (s : BasisState)
    (hne : tail≠[]) (heven : s vlow=false) (hlen : 0<bits.length) :
    regValue bits s=2^(bits.length-1) ↔
      padicValInt 2 (signedRegValue (vlow::(bits++tail)) s)=bits.length := by
  have hm := signed_prefix_mod (vlow::bits) tail s hne
  change signedRegValue (vlow::(bits++tail)) s%(2:Int)^(bits.length+1)=
    (((if s vlow then 1 else 0)+2*regValue bits s:Nat):Int) at hm
  rw [heven] at hm
  simp only [Bool.false_eq_true,ite_false,zero_add,Nat.cast_mul,Nat.cast_ofNat] at hm
  have hp : (2:Int)^bits.length=2*(2:Int)^(bits.length-1) := by
    have he : bits.length=(bits.length-1)+1 := by omega
    conv_lhs => rw [he,pow_succ]
    ring
  rw [←depthResidue_iff _ bits.length hlen,hm,hp]
  norm_cast
  omega

end ECDSAAdd.Arithmetic.Paper935
