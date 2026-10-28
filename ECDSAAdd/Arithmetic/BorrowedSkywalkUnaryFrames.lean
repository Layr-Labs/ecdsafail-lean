import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryClean
import ECDSAAdd.Arithmetic.SkywalkPayloadProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Exact canonical doubling keeps the entire original caller frame. -/
theorem borrowedSkywalkUnary_double_nat_frame (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (q X Y : Nat)
    (ho : q%2=1) (hp : q<2^256) (hx : X<q) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X Y)
      (dblInPlace (borrowedSkywalkUnary w) q)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base ((2*X)%q) Y) := by
  have uw := borrowedSkywalkUnary_widths w
  have un := borrowedSkywalkUnary_nodup w hn
  intro s m h
  have hc := borrowedSkywalkUnary_clean_frame w hn base s.basis X Y hw hu h
  have hz : regValue (borrowedSkywalkUnary w).z s.basis=X := by
    simpa only [borrowedSkywalkUnary_z] using h.1
  obtain ⟨hf,hv⟩ := dblInPlace_spec (borrowedSkywalkUnary w) 256 q X uw un ho hp hx
    s m ⟨hz,hc⟩
  have keep : ∀r,r∉(skywalkSharedField w).z →
      (run (dblInPlace (borrowedSkywalkUnary w) q) m s).basis r=s.basis r := by
    intro r hr
    exact (modUnary_frame (borrowedSkywalkUnary w) 256 q X uw un ho hp hx s m hz hc r
      (by simpa only [borrowedSkywalkUnary_z] using hr)).1
  refine ⟨hf,PairFrame.update_temp (skywalkSharedField w).z (skywalkSharedField w).a
    base s.basis _ X Y _ (borrowedSkywalkUnary_pairDisjoint w hn) h keep ?_⟩
  simpa only [borrowedSkywalkUnary_z] using hv.1

/-- Exact canonical halving has the same complete old 257-bit caller frame. -/
theorem borrowedSkywalkUnary_half_nat_frame (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (q X Y : Nat)
    (ho : q%2=1) (hp : q<2^256) (hx : X<q) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X Y)
      (halfInPlace (borrowedSkywalkUnary w) q)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base (halveMod q X) Y) := by
  have uw := borrowedSkywalkUnary_widths w
  have un := borrowedSkywalkUnary_nodup w hn
  intro s m h
  have hc := borrowedSkywalkUnary_clean_frame w hn base s.basis X Y hw hu h
  have hz : regValue (borrowedSkywalkUnary w).z s.basis=X := by
    simpa only [borrowedSkywalkUnary_z] using h.1
  obtain ⟨hf,hv⟩ := halfInPlace_spec (borrowedSkywalkUnary w) 256 q X uw un ho hp hx
    s m ⟨hz,hc⟩
  have keep : ∀r,r∉(skywalkSharedField w).z →
      (run (halfInPlace (borrowedSkywalkUnary w) q) m s).basis r=s.basis r := by
    intro r hr
    exact (modUnary_frame (borrowedSkywalkUnary w) 256 q X uw un ho hp hx s m hz hc r
      (by simpa only [borrowedSkywalkUnary_z] using hr)).2
  refine ⟨hf,PairFrame.update_temp (skywalkSharedField w).z (skywalkSharedField w).a
    base s.basis _ X Y _ (borrowedSkywalkUnary_pairDisjoint w hn) h keep ?_⟩
  simpa only [borrowedSkywalkUnary_z] using hv.1

private theorem double_val (X : Fp) : (2*X.val)%p=(2*X).val := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hh := skywalkFieldUnnat_field true false X.val 0 (ZMod.val_lt X) p_prime.pos
  simp only [skywalkFieldUnnat,skywalkSignedNat,Bool.not_true,Bool.false_eq_true,
    if_false,if_true,Nat.sub_zero,Nat.add_mod_right,Nat.mod_mod,Nat.cast_zero,
    add_zero,neg_zero,skywalkPayloadUncell,ZMod.natCast_zmod_val] at hh
  have hx := congrArg (fun q : Fp×Fp => q.1.val) hh
  simp only at hx
  rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ p_prime.pos)] at hx
  exact hx

private theorem half_val (X : Fp) : halveMod p X.val=(X/2).val := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hh := skywalkFieldNat_field true false X.val 0 p_prime.pos
  simp only [skywalkFieldNat,skywalkSignedNat,Bool.false_eq_true,if_false,if_true,
    Nat.mod_eq_of_lt (ZMod.val_lt X),Nat.cast_zero,add_zero,
    skywalkPayloadCell,ZMod.natCast_zmod_val] at hh
  have hx := congrArg (fun q : Fp×Fp => q.1.val) hh
  simp only at hx
  rw [ZMod.val_natCast_of_lt (halve_mod_bound p X.val (by norm_num [p]) (ZMod.val_lt X))] at hx
  exact hx

/-- All Fp inputs and arbitrary measurement streams are covered. -/
theorem borrowedSkywalkUnary_double_frame (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (dblInPlace (borrowedSkywalkUnary w) p)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base (2*X).val Y.val) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have h := borrowedSkywalkUnary_double_nat_frame w hn p X.val Y.val
    (by norm_num [p]) (by norm_num [p]) (ZMod.val_lt X) base hw hu
  rw [double_val X] at h
  exact h

theorem borrowedSkywalkUnary_half_frame (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (halfInPlace (borrowedSkywalkUnary w) p)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base (X/2).val Y.val) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have h := borrowedSkywalkUnary_half_nat_frame w hn p X.val Y.val
    (by norm_num [p]) (by norm_num [p]) (ZMod.val_lt X) base hw hu
  rw [half_val X] at h
  exact h

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_double_frame
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_half_frame
