import ECDSAAdd.Arithmetic.MixedTranscriptReplay
import ECDSAAdd.Arithmetic.FusedSharedRetainedDivision

namespace ECDSAAdd.Arithmetic
open Secp256k1

def mixedTranscriptFieldMultiplication (w : Nat → Wire) (b effG effS : Wire) : Program :=
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a ++
  mixedTranscriptInverseReplay w b effG effS (mixedTranscriptTape w) ++
  halfInPlace (skywalkSharedField w).unary p

private theorem mixed_half_val (X : Fp) : halveMod p X.val=(X/2).val := by
  letI : NeZero p := ⟨Secp256k1.p_prime.ne_zero⟩
  have hh := skywalkFieldNat_field true false X.val 0 p_prime.pos
  simp only [skywalkFieldNat,skywalkSignedNat,Bool.false_eq_true,if_false,if_true,
    Nat.mod_eq_of_lt (ZMod.val_lt X),Nat.cast_zero,add_zero,
    skywalkPayloadCell,ZMod.natCast_zmod_val] at hh
  have hx := congrArg (fun q : Fp×Fp => q.1.val) hh
  simp only at hx
  rw [ZMod.val_natCast_of_lt (halve_mod_bound p X.val (by norm_num [p]) (ZMod.val_lt X))] at hx
  exact hx

private theorem mixed_half_frame (active g swap : Wire) (w : Nat → Wire)
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
  rw [mixed_half_val X] at hout
  exact ⟨hf,hout⟩


theorem mixedTranscriptFieldMultiplication_spec (w : Nat → Wire) (b effG effS : Wire)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w))
    (base : BasisState) (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val 0)
      (mixedTranscriptFieldMultiplication w b effG effS)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (if base b then Y*(x : Fp) else Y).val 0) := by
  cases htape : mixedTranscriptTape w with
  | nil =>
    have hlen := mixedTranscriptTape_length w
    rw [htape] at hlen
    norm_num at hlen
  | cons l ls =>
    have hl0 := hl l (by rw [htape]; simp)
    have h1 := retained_copy_frame b effG effS w hl0.cell base Y.val 0
    simp only [Nat.zero_xor] at h1
    have h2 := mixedTranscriptInverseReplay_spec w b effG effS (mixedTranscriptTape w)
      hl base hg0 hs0 hk hu Y Y
    have hq := mixedTranscriptTape_product w base b x Y hx0 hx hr
    rw [hq] at h2
    have h3 := mixed_half_frame b effG effS w hl0.cell base hk
      (2*(if base b then Y*(x : Fp) else Y)) 0
    have ht2 : (2 : Fp)≠0 := by decide
    have he : (2*(if base b then Y*(x : Fp) else Y))/2=
        (if base b then Y*(x : Fp) else Y) := by field_simp [ht2]
    rw [he] at h3
    simpa only [mixedTranscriptFieldMultiplication,List.append_assoc,ZMod.val_zero]
      using (h1.seq h2).seq h3

theorem mixedTranscriptFieldMultiplication_counts (w : Nat → Wire) (b effG effS : Wire)
    (hl : MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w)) :
    toffoliCount (mixedTranscriptFieldMultiplication w b effG effS)=920064 ∧
    measurementCount (mixedTranscriptFieldMultiplication w b effG effS)=788992 := by
  have hw := skywalkShared_field_widths w
  have hu := modUnary_counts (skywalkSharedField w).unary 256 p
    ((skywalkSharedField w).unary_widths 256 hw) (by omega)
  have hr := mixedTranscriptInverseReplay_counts w b effG effS (mixedTranscriptTape w) hl
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hc := copyRegister_counts none (skywalkSharedField w).z (skywalkSharedField w).a hlen
  rw [mixedTranscriptTape_length] at hr
  simp only [mixedTranscriptFieldMultiplication,toffoliCount_append,measurementCount_append,
    hu.2.2.1,hu.2.2.2,hr.1,hr.2,hc.1,hc.2]
  norm_num

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.mixedTranscriptFieldMultiplication_spec
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptFieldMultiplication_counts

#print axioms ECDSAAdd.Arithmetic.mixedTranscriptFieldMultiplication
