import ECDSAAdd.Arithmetic.MixedTranscriptReplay
import ECDSAAdd.Arithmetic.FusedSharedRetainedDivision

namespace ECDSAAdd.Arithmetic
open Secp256k1

def mixedTranscriptFieldDivision (w : Nat → Wire) (b effG effS : Wire) : Program :=
  dblInPlace (skywalkSharedField w).unary p ++
  mixedTranscriptReplay w b effG effS (mixedTranscriptTape w) ++
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a

private theorem mixed_double_val (X : Fp) : (2*X.val)%p=(2*X).val := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hh := skywalkFieldUnnat_field true false X.val 0 (ZMod.val_lt X) p_prime.pos
  simp only [skywalkFieldUnnat,skywalkSignedNat,Bool.not_true,Bool.false_eq_true,
    if_false,if_true,Nat.sub_zero,Nat.add_mod_right,Nat.mod_mod,Nat.cast_zero,
    add_zero,neg_zero,skywalkPayloadUncell,ZMod.natCast_zmod_val] at hh
  have hx := congrArg (fun q : Fp×Fp => q.1.val) hh
  simp only at hx
  rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ p_prime.pos)] at hx
  exact hx

private theorem mixed_double_frame (active g swap : Wire) (w : Nat → Wire)
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
  rw [mixed_double_val X] at hout
  exact ⟨hf,hout⟩

theorem mixedTranscriptFieldDivision_spec (w : Nat → Wire) (b effG effS : Wire)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w))
    (base : BasisState) (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val 0)
      (mixedTranscriptFieldDivision w b effG effS)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (if base b then Y/(x : Fp) else Y).val 0) := by
  cases htape : mixedTranscriptTape w with
  | nil =>
    have hlen := mixedTranscriptTape_length w
    rw [htape] at hlen
    norm_num at hlen
  | cons l ls =>
    have hl0 := hl l (by rw [htape]; simp)
    have h1 := mixed_double_frame b effG effS w hl0.cell base hk Y 0
    have h2 := mixedTranscriptReplay_spec w b effG effS (mixedTranscriptTape w)
      hl base hg0 hs0 hk hu (2*Y) 0
    have hq := mixedTranscriptTape_quotient w base b x Y hx0 hx hr
    rw [hq] at h2
    have h3 := retained_copy_frame b effG effS w hl0.cell base
      (if base b then Y/(x : Fp) else Y).val (if base b then Y/(x : Fp) else Y).val
    simp only [Nat.xor_self] at h3
    simpa only [mixedTranscriptFieldDivision,List.append_assoc,ZMod.val_zero]
      using (h1.seq h2).seq h3

theorem mixedTranscriptFieldDivision_counts (w : Nat → Wire) (b effG effS : Wire)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w)) :
    toffoliCount (mixedTranscriptFieldDivision w b effG effS)=920063 ∧
    measurementCount (mixedTranscriptFieldDivision w b effG effS)=788991 := by
  have hw := skywalkShared_field_widths w
  have hu := modUnary_counts (skywalkSharedField w).unary 256 p
    ((skywalkSharedField w).unary_widths 256 hw) (by omega)
  have hr := mixedTranscriptReplay_counts w b effG effS (mixedTranscriptTape w) hl
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hc := copyRegister_counts none (skywalkSharedField w).z (skywalkSharedField w).a hlen
  rw [mixedTranscriptTape_length] at hr
  simp only [mixedTranscriptFieldDivision,toffoliCount_append,measurementCount_append,
    hu.1,hu.2.1,hr.1,hr.2,hc.1,hc.2]
  norm_num

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.mixedTranscriptFieldDivision_spec
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptFieldDivision_counts

#print axioms ECDSAAdd.Arithmetic.mixedTranscriptFieldDivision
