import ECDSAAdd.Arithmetic.Paper935.StoreFlag
import ECDSAAdd.Arithmetic.Divsteps.SwapHistory

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem signed_prefix (xs tail : List Wire) (s : BasisState) (hne : tail≠[]) :
    signedRegValue (xs++tail) s=(regValue xs s:Int)+(2:Int)^xs.length*signedRegValue tail s := by
  induction xs with
  | nil => simp [regValue]
  | cons w xs ih =>
    rw [List.cons_append,signedRegValue_cons w (xs++tail) s (by simp [hne]),ih]
    cases hw : s w <;> simp [regValue,hw,pow_succ] <;> ring

/-- The coefficient test reads precisely bits one through `low.length`.
With an even coefficient it is the divisibility test used by the history cutoff. -/
theorem historyPrefix_zero_iff (vlow : Wire) (low tail : List Wire) (s : BasisState)
    (hne : tail≠[]) (heven : s vlow=false) :
    regValue low s=0 ↔ (2:Int)^(low.length+1) ∣ signedRegValue (vlow::(low++tail)) s := by
  rw [signedRegValue_cons vlow (low++tail) s (by simp [hne]),signed_prefix low tail s hne]
  simp only [heven,Bool.toNat_false,Nat.cast_zero,add_zero,pow_succ]
  have hr0 : (0:Int)≤regValue low s := Int.natCast_nonneg _
  have hrlt : (regValue low s:Int)<(2:Int)^low.length := by exact_mod_cast regValue_lt low s
  have hmod : (regValue low s:Int) % (2:Int)^low.length = regValue low s := Int.emod_eq_of_lt hr0 hrlt
  rw [mul_comm ((2:Int)^low.length) 2,Int.mul_dvd_mul_iff_left (by norm_num : (2:Int)≠0)]
  rw [Int.dvd_iff_emod_eq_zero,Int.add_emod,Int.mul_emod_right,add_zero,Int.emod_emod,hmod]
  exact Int.natCast_eq_zero.symm


/-- Bind the actual detector inputs to the mathematical counter and coefficient,
including the zero coefficient (which must go into stored history). -/
theorem historyPredicate_value (sign frozen vlow : Wire) (zb low : List ZeroBit)
    (zlo tail : List Wire) (s : BasisState) (st : ECDSAAdd.Divsteps.ZState)
    (hzview : zb.map ZeroBit.input=zlo++[sign]) (htail : tail≠[])
    (hz : signedRegValue (zlo++[sign]) s=st.z)
    (hv : signedRegValue (vlow::(low.map ZeroBit.input++tail)) s=st.fv)
    (heven : st.fv%2=0) :
    (!s frozen && !(!s sign && !decide (regValue (zb.map ZeroBit.input) s=0)) &&
      decide (regValue (low.map ZeroBit.input) s=0))=
    (!s frozen && decide (st.z≤0) && decide ((2:Int)^(low.length+1) ∣ st.fv)) := by
  have hbit : s vlow=false := (signedRegValue_even_iff vlow _ s).mp (by rw [hv]; exact heven)
  have hlow := historyPrefix_zero_iff vlow (low.map ZeroBit.input) tail s htail hbit
  rw [hv,List.length_map] at hlow
  rw [storeFlag_predicate_value sign frozen zb low zlo s hzview,hz]
  simp only [hlow]

/-- Divisibility includes the infinite-depth zero case, rather than silently
using the finite valuation of zero. -/
theorem historyCutoff_valuation (v : Int) (depth : Nat) :
    (2:Int)^depth ∣ v ↔ v=0 ∨ depth≤padicValInt 2 v := by
  simpa only [Nat.cast_ofNat] using padicValInt_dvd_iff (p:=2) depth v

/-- A stored active step belongs to the negative-counter nonswap class.
The physical coefficient prefix itself excludes swap; no retained swap tag
is assumed by the selector. -/
theorem historyCutoff_class (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (depth : Nat) (hd : 2≤depth)
    (hz : (ECDSAAdd.Divsteps.zStep st).z≤0)
    (hv : (2:Int)^depth ∣ (ECDSAAdd.Divsteps.zStep st).fv) :
    ¬(0≤st.z ∧ st.g%2=1) ∧ st.z<0 := by
  have h4 : (4:Int)∣(2:Int)^depth := by
    have h := pow_dvd_pow (2:Int) hd
    norm_num only [Int.reducePow] at h
    exact h
  have hmod := Int.emod_eq_zero_of_dvd (dvd_trans h4 hv)
  have hn : ¬(0≤st.z ∧ st.g%2=1) := by
    intro hs
    have hh := (ECDSAAdd.Divsteps.sigma_class hi hp).1.mp hs
    change (ECDSAAdd.Divsteps.zStep st).fv%4=2%4 at hh
    omega
  refine ⟨hn,?_⟩
  rw [ECDSAAdd.Divsteps.zStep_nonswap hn] at hz
  dsimp at hz
  omega

/-- When the cutoff test fails, the valuation is finite and strictly below
its threshold; zero can never be routed to a finite-depth decoder. -/
theorem historyCutoff_unstored (v : Int) (depth : Nat)
    (h : ¬(2:Int)^depth ∣ v) : v≠0 ∧ padicValInt 2 v<depth := by
  simpa only [historyCutoff_valuation,not_or,not_le] using h

/-- The nonstored negative-counter class has exactly the finite range of
recovery depths that the reverse decoder must implement. -/
theorem historyCutoff_recovery_range (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (hz : st.z<0)
    (depth : Nat) (h : ¬(2:Int)^depth ∣ (ECDSAAdd.Divsteps.zStep st).fv) :
    (ECDSAAdd.Divsteps.zStep st).fv≠0 ∧
      2≤padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv ∧
      padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv<depth := by
  have hr := historyCutoff_unstored _ depth h
  have hn : ¬(0≤st.z ∧ st.g%2=1) := by omega
  have hd := (ECDSAAdd.Divsteps.sigma_class hi hp).2.2 hn
  have hval := (historyCutoff_valuation (ECDSAAdd.Divsteps.zStep st).fv 2).mp (by norm_num; exact hd)
  exact ⟨hr.1,hval.resolve_left hr.1,hr.2⟩

end ECDSAAdd.Arithmetic.Paper935
