import ECDSAAdd.Arithmetic.MixedTranscriptDivision

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem balancedSharedDivision_double_val (X : Fp) : (2*X.val)%p=(2*X).val := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hh := skywalkFieldUnnat_field true false X.val 0 (ZMod.val_lt X) p_prime.pos
  simp only [skywalkFieldUnnat,skywalkSignedNat,Bool.not_true,Bool.false_eq_true,
    if_false,if_true,Nat.sub_zero,Nat.add_mod_right,Nat.mod_mod,Nat.cast_zero,
    add_zero,neg_zero,skywalkPayloadUncell,ZMod.natCast_zmod_val] at hh
  have hx := congrArg (fun q : Fp×Fp => q.1.val) hh
  simp only at hx
  rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ p_prime.pos)] at hx
  exact hx

theorem balancedSharedDivision_double_frame (active g swap : Wire) (w : Nat → Wire)
    (hnd : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (base : BasisState) (hk : regValue (skywalkSharedField w).work base=0)
    (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (dblInPlace (skywalkSharedField w).unary p)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (2*X).val Y.val) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hw := skywalkShared_field_widths w
  have hu := (skywalkSharedField w).unary_widths 256 hw
  have hn' := (List.nodup_cons.mp (ReplayValues.unary_nodup active
    (skywalkSharedField w) (ReplayValues.control_nodup active swap g
      (skywalkSharedField w) hnd active (by simp)))).2
  intro s m h
  have hc := fusedShared_work_clean active g swap w hnd base s.basis X.val Y.val hk h
  obtain ⟨hf,hv⟩ := dblInPlace_spec (skywalkSharedField w).unary 256 p X.val
    hu hn' (by norm_num [p]) (by norm_num [p]) (ZMod.val_lt X) s m ⟨h.1,hc⟩
  have keep (q : Wire) (hq : q∉(skywalkSharedField w).z) :
      (run (dblInPlace (skywalkSharedField w).unary p) m s).basis q=s.basis q :=
    (modUnary_frame (skywalkSharedField w).unary 256 p X.val hu hn'
      (by norm_num [p]) (by norm_num [p]) (ZMod.val_lt X) s m h.1 hc q hq).1
  have hdis : (skywalkSharedField w).z.Disjoint (skywalkSharedField w).a := by
    apply List.disjoint_left.mpr
    intro q hz ha
    have hh := List.nodup_iff_count.mp hnd q
    have hZ := List.count_pos_iff.mpr hz
    have hA := List.count_pos_iff.mpr ha
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hh
    omega
  have hout := PairFrame.update_temp (skywalkSharedField w).z (skywalkSharedField w).a
    base s.basis _ X.val Y.val _ hdis h keep hv.1
  rw [balancedSharedDivision_double_val X] at hout
  exact ⟨hf,hout⟩

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.balancedSharedDivision_double_frame
