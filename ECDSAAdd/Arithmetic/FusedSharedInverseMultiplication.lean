import ECDSAAdd.Arithmetic.FusedSharedInverseReplay
import ECDSAAdd.Arithmetic.FusedSharedRetainedDivision

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Complete multiplication endpoint with all 512 recorded inverse cells. -/
def skywalkFieldMultiplicationRetained (w : Nat → Wire) : Program :=
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a ++
    fusedSharedInverseReplay w (skywalkSharedTape w) ++ halfInPlace (skywalkSharedField w).unary p

private theorem inverse_half_val (X : Fp) : halveMod p X.val=(X/2).val := by
  letI : NeZero p := ⟨Secp256k1.p_prime.ne_zero⟩
  have hh := skywalkFieldNat_field true false X.val 0 p_prime.pos
  simp only [skywalkFieldNat,skywalkSignedNat,Bool.false_eq_true,if_false,if_true,
    Nat.mod_eq_of_lt (ZMod.val_lt X),Nat.cast_zero,add_zero,
    skywalkPayloadCell,ZMod.natCast_zmod_val] at hh
  have hx := congrArg (fun q : Fp×Fp => q.1.val) hh
  simp only at hx
  rw [ZMod.val_natCast_of_lt (halve_mod_bound p X.val (by norm_num [p]) (ZMod.val_lt X))] at hx
  exact hx

private theorem inverse_half_frame (active g swap : Wire) (w : Nat → Wire)
    (hnd : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (base : BasisState) (hk : regValue (skywalkSharedField w).work base=0)
    (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (halfInPlace (skywalkSharedField w).unary p)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (X/2).val Y.val) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hw := skywalkShared_field_widths w
  have hu := (skywalkSharedField w).unary_widths 256 hw
  have hn' := (List.nodup_cons.mp (ReplayValues.unary_nodup active
    (skywalkSharedField w) (ReplayValues.control_nodup active swap g
      (skywalkSharedField w) hnd active (by simp)))).2
  intro s m h
  have hc := fusedShared_work_clean active g swap w hnd base s.basis X.val Y.val hk h
  obtain ⟨hf,hv⟩ := halfInPlace_spec (skywalkSharedField w).unary 256 p X.val
    hu hn' (by norm_num [p]) (by norm_num [p]) (ZMod.val_lt X) s m ⟨h.1,hc⟩
  have keep (q : Wire) (hq : q∉(skywalkSharedField w).z) :
      (run (halfInPlace (skywalkSharedField w).unary p) m s).basis q=s.basis q :=
    (modUnary_frame (skywalkSharedField w).unary 256 p X.val hu hn'
      (by norm_num [p]) (by norm_num [p]) (ZMod.val_lt X) s m h.1 hc q hq).2
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
  rw [inverse_half_val X] at hout
  exact ⟨hf,hout⟩


theorem skywalkFieldMultiplicationRetained_spec (active : Wire) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (ha : active∉skywalkSharedWires w)
    (base : BasisState) (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val 0)
      (skywalkFieldMultiplicationRetained w)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (Y*(x : Fp)).val 0) := by
  cases htape : skywalkSharedTape w with
  | nil =>
    have hlen := skywalkShared_tape_length w
    rw [htape] at hlen
    norm_num at hlen
  | cons r rs =>
    have ht := skywalkShared_tape_layout w hn active ha
    have hnd := ht r (by rw [htape]; simp)
    have h1 := retained_copy_frame active r.1 r.2 w hnd base Y.val 0
    simp only [Nat.zero_xor] at h1
    have h2 := fusedSharedInverseReplay_spec active w (r::rs) hn
      (by simpa only [htape] using ht)
      (by simpa only [htape] using skywalkShared_fused_tape_layout w hn)
      base hk hu Y Y
    have hr' : skywalkTapeControls base (r::rs)=
        SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) := by
      simpa only [htape] using hr
    have hq := SkywalkTrace.product512 x Y hx0 hx
    rw [←hr'] at hq
    rw [hq] at h2
    have h3 := inverse_half_frame active r.1 r.2 w hnd base hk (2*(Y*(x : Fp))) 0
    have ht2 : (2 : Fp)≠0 := by decide
    have he : (2*(Y*(x : Fp)))/2=Y*(x : Fp) := by field_simp [ht2]
    rw [he] at h3
    simpa only [skywalkFieldMultiplicationRetained,htape,List.append_assoc,ZMod.val_zero]
      using (h1.seq h2).seq h3

theorem skywalkFieldMultiplicationRetained_counts (active : Wire) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (ha : active∉skywalkSharedWires w) :
    toffoliCount (skywalkFieldMultiplicationRetained w)=919040 ∧
    measurementCount (skywalkFieldMultiplicationRetained w)=787968 := by
  have hw := skywalkShared_field_widths w
  have hu := modUnary_counts (skywalkSharedField w).unary 256 p
    ((skywalkSharedField w).unary_widths 256 hw) (by omega)
  have hr := fusedSharedInverseReplay_counts active w (skywalkSharedTape w)
    (skywalkShared_tape_layout w hn active ha)
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hc := copyRegister_counts none (skywalkSharedField w).z (skywalkSharedField w).a hlen
  rw [skywalkShared_tape_length] at hr
  simp only [skywalkFieldMultiplicationRetained,toffoliCount_append,measurementCount_append,
    hu.2.2.1,hu.2.2.2,hr.1,hr.2,hc.1,hc.2]
  norm_num

end ECDSAAdd.Arithmetic
