import ECDSAAdd.Arithmetic.Paper935.HistoryPredicate

namespace ECDSAAdd.Arithmetic.Paper935

private theorem signed_slice (xs tail : List Wire) (s : BasisState) (hne : tail≠[]) :
    signedRegValue (xs++tail) s=(regValue xs s:Int)+(2:Int)^xs.length*signedRegValue tail s := by
  induction xs with
  | nil => simp [regValue]
  | cons w xs ih =>
    rw [List.cons_append,signedRegValue_cons w (xs++tail) s (by simp [hne]),ih]
    cases hw : s w <;> simp [regValue,hw,pow_succ] <;> ring

/-- Physical suffix extraction agrees with signed Euclidean division,
including negative coefficients and arbitrary low bits. -/
theorem signedSuffix_value (xs tail : List Wire) (s : BasisState) (hne : tail≠[]) :
    signedRegValue tail s=signedRegValue (xs++tail) s/(2:Int)^xs.length := by
  rw [signed_slice xs tail s hne,mul_comm ((2:Int)^xs.length),Int.add_mul_ediv_right _ _ (by positivity : (2:Int)^xs.length≠0)]
  have hr0 : (0:Int)≤regValue xs s := Int.natCast_nonneg _
  have hrlt : (regValue xs s:Int)<(2:Int)^xs.length := by exact_mod_cast regValue_lt xs s
  rw [Int.ediv_eq_zero_of_lt hr0 hrlt,zero_add]

/-- Five physical bits above an odd low bit determine every residue needed
at depths two through six. No finite truth table is assumed correct. -/
theorem oddResidue5_value (low : Wire) (bits tail : List Wire) (s : BasisState)
    (hlen : bits.length=5) (hne : tail≠[]) (hodd : s low=true)
    (depth : Nat) (hd : depth≤6) :
    ((signedRegValue (low::(bits++tail)) s:Int):ZMod (2^depth))=
      ((2*regValue bits s+1:Nat):ZMod (2^depth)) := by
  have hpow : (2:Int)^depth ∣ (64:Int) := by
    have h := pow_dvd_pow (2:Int) hd
    norm_num only [Int.reducePow] at h
    exact h
  have he : signedRegValue (low::(bits++tail)) s=
      2*(regValue bits s:Int)+1+64*signedRegValue tail s := by
    rw [signedRegValue_cons low (bits++tail) s (by simp [hne]),signed_slice bits tail s hne,hlen,hodd]
    simp only [Bool.toNat_true,Nat.cast_one]
    ring
  have h64 : (64:ZMod (2^depth))=0 := by
    rw [←Int.cast_ofNat, ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hpow
  rw [he]
  push_cast
  rw [h64,zero_mul,add_zero]


/-- The quotient extracted at the actual valuation has an odd low bit.
This follows from the reachable negative-counter invariant. -/
theorem recoveryQuotient_odd (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hz : st.z<0) (depth : Nat)
    (hd : depth=padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv) :
    ((ECDSAAdd.Divsteps.zStep st).fv/(2:Int)^depth)%2=1 := by
  obtain ⟨j,q,r,hj,hq,hfv,hr0,hr1,hdiv⟩ := hi.low hz
  have hn : ¬(0≤st.z ∧ st.g%2=1) := by omega
  have hfnew : (ECDSAAdd.Divsteps.zStep st).fv=(2:Int)^(j+1)*q := by
    rw [ECDSAAdd.Divsteps.zStep_nonswap hn]
    change 2*st.fv=_
    rw [hfv,pow_succ]
    ring
  have hval : padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv=j+1 := by
    rw [hfnew,padicValInt.mul (by positivity) (by omega),
      padicValInt.eq_zero_of_not_dvd (p:=2) (z:=q) (by push_cast; omega),add_zero,
      show ((2:Int)^(j+1))=((2^(j+1):Nat):Int) by push_cast; ring,
      padicValInt.of_nat,padicValNat.prime_pow]
  rw [hd,hval,hfnew,Int.mul_ediv_cancel_left _ (by positivity)]
  exact hq

/-- Bind both five-bit addresses directly to the current physical rows.
The coefficient slice is the public depth, not an assumed division oracle. -/
theorem recoveryResidues_physical (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (hz : st.z<0)
    (depth : Nat) (hd : depth=padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv) (hdepth : depth≤6)
    (flow qlow : Wire) (fbits ftail slice qbits qtail : List Wire) (s : BasisState)
    (hflen : fbits.length=5) (hqlen : qbits.length=5) (hplen : slice.length=depth)
    (hftail : ftail≠[]) (hqtail : qtail≠[])
    (hf : signedRegValue (flow::(fbits++ftail)) s=(ECDSAAdd.Divsteps.zStep st).f)
    (hq : signedRegValue (slice++(qlow::(qbits++qtail))) s=(ECDSAAdd.Divsteps.zStep st).fv) :
    ((ECDSAAdd.Divsteps.zStep st).f:ZMod (2^depth))=((2*regValue fbits s+1:Nat):ZMod (2^depth)) ∧
    (((ECDSAAdd.Divsteps.zStep st).fv/(2:Int)^depth:Int):ZMod (2^depth))=
      ((2*regValue qbits s+1:Nat):ZMod (2^depth)) := by
  have hfo : s flow=true := by
    have h := signedDecode_mod_two (flow::(fbits++ftail)).length (regValue (flow::(fbits++ftail)) s) (by simp)
    change signedRegValue (flow::(fbits++ftail)) s%2=_ at h
    rw [hf,(hi.zStep hp).fodd] at h
    cases hs : s flow <;> simp [regValue,hs] at h ⊢
  have qvalue := signedSuffix_value slice (qlow::(qbits++qtail)) s (by simp)
  rw [hq,hplen] at qvalue
  have hqo : s qlow=true := by
    have h := signedDecode_mod_two (qlow::(qbits++qtail)).length (regValue (qlow::(qbits++qtail)) s) (by simp)
    change signedRegValue (qlow::(qbits++qtail)) s%2=_ at h
    rw [qvalue,recoveryQuotient_odd p st hi hz depth hd] at h
    cases hs : s qlow <;> simp [regValue,hs] at h ⊢
  constructor
  · rw [←hf]
    exact oddResidue5_value flow fbits ftail s hflen hftail hfo depth hdepth
  · rw [←qvalue]
    exact oddResidue5_value qlow qbits qtail s hqlen hqtail hqo depth hdepth

end ECDSAAdd.Arithmetic.Paper935
