import ECDSAAdd.Arithmetic.CompactGuardPorts

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

theorem compactSource_sublist (L : FusedHalfPorts) : L.compactSource.Sublist L.source := by
  exact (List.Sublist.refl (L.e::L.yTail)).append (by simp)

theorem compactTarget_sublist (L : FusedHalfPorts) : L.compactTarget.Sublist L.target := by
  exact (List.Sublist.refl L.targetLow).append (by simp)

theorem compactConstant_sublist (L : FusedHalfPorts) : L.compactConstant.Sublist L.constant := by
  exact (List.Sublist.refl L.C).append (by simp)

theorem compactCarry_sublist (L : FusedHalfPorts) : L.compactCarry.Sublist L.carry :=
  List.take_sublist _ _

theorem compact_front_nodup (L : FusedHalfPorts) (hn : L.wires.Nodup)
    (he : L.early.Sublist L.A) :
    ([L.b,L.a,L.h,L.j,L.l,L.m,L.cin]++L.compactSource++L.compactTarget++
      L.compactConstant++L.compactCarry).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp (L.front_nodup hn he) w
  have hs := L.compactSource_sublist.count_le w
  have ht := L.compactTarget_sublist.count_le w
  have hc := L.compactConstant_sublist.count_le w
  have hk := L.compactCarry_sublist.count_le w
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

private theorem compact_prefix_value (r : List Wire) (q h : Wire) (st : BasisState)
    (Z : Nat) (hz : Z<2^r.length) (hv : regValue (r++[q,h]) st=Z) :
    regValue (r++[q]) st=Z := by
  have hg := fusedCanonicalGuards r q h st Z hz hv
  rw [regValue_append,hg.1]
  simp [regValue,hg.2.1]

theorem compact_source_value (L : FusedHalfPorts) (hw : L.Widths)
    (hwidth : p+1<2^L.A.length) (Y : Nat) (hY : Y<p) (st : BasisState)
    (hy : regValue L.source st=Y) : regValue L.compactSource st=Y := by
  have hy' : Y<2^(L.e::L.yTail).length := by
    simp only [List.length_cons,hw.source]
    omega
  exact compact_prefix_value (L.e::L.yTail) L.yg0 L.yg1 st Y hy' hy

theorem compact_target_value (L : FusedHalfPorts) (hw : L.Widths)
    (hwidth : p+1<2^L.A.length) (X : Nat) (hX : X<p) (st : BasisState)
    (hx : regValue L.target st=X) : regValue L.compactTarget st=X := by
  have hx' : X<2^L.targetLow.length := by
    rw [(L.widths hw).2.2.2.2]
    omega
  exact compact_prefix_value L.targetLow L.qOut L.hOut st X hx' hx

theorem compact_constant_clean (L : FusedHalfPorts) (st : BasisState)
    (h : regValue L.constant st=0) : regValue L.compactConstant st=0 :=
  (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp h w (L.compactConstant_sublist.subset hw))

theorem compact_carry_clean (L : FusedHalfPorts) (st : BasisState)
    (h : regValue L.carry st=0) : regValue L.compactCarry st=0 :=
  (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp h w (L.compactCarry_sublist.subset hw))

theorem compact_target_lift (L : FusedHalfPorts) (st : BasisState) (X : Nat)
    (hx : regValue L.compactTarget st=X) (hh : st L.hOut=false) : regValue L.target st=X := by
  have he : L.target=L.compactTarget++[L.hOut] := by
    simp only [target,compactTarget,List.append_assoc]
    rfl
  rw [he,regValue_append,hx]
  simp [regValue,hh]

end FusedHalfPorts
end ECDSAAdd.Arithmetic
