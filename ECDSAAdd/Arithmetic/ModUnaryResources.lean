import ECDSAAdd.Arithmetic.ModHalf
import ECDSAAdd.Arithmetic.ModDouble

namespace ECDSAAdd.Arithmetic

/-- 半倍都只更新目标；scratch 的所有物理位与未借用线路保持。 -/
theorem modUnary_frame (U : ModUnaryLayout) (n p Z : Nat)
    (hw : U.Widths n) (hnd : U.wires.Nodup) (hp : p%2=1) (hpn : p<2^n) (hZ : Z<p)
    (s : State) (m : List Bool) (hz : regValue U.z s.basis=Z) (hc : regValue U.work s.basis=0)
    (q : Wire) (hq : q∉U.z) :
    (run (dblInPlace U p) m s).basis q=s.basis q ∧
    (run (halfInPlace U p) m s).basis q=s.basis q := by
  obtain ⟨_,hd⟩ := dblInPlace_spec U n p Z hw hnd hp hpn hZ s m ⟨hz,hc⟩
  obtain ⟨_,hh⟩ := halfInPlace_spec U n p Z hw hnd hp hpn hZ s m ⟨hz,hc⟩
  simp only [Holds.holds] at hd hh
  by_cases hqw : q∈U.work
  · exact ⟨(regValue_eq_iff _ _ _).mp (hd.2.trans hc.symm) q hqw,
      (regValue_eq_iff _ _ _).mp (hh.2.trans hc.symm) q hqw⟩
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  have hkc : q∉U.core.work := fun hh => hqw (by simp [ModUnaryLayout.work,hh])
  have hqf : q≠U.flag := fun hh => hqw (by simp [ModUnaryLayout.work,hh])
  constructor
  · apply run_preserves_outside
    rw [(modUnary_wires U n p hw hn).1]
    simpa using And.intro hq hkc
  · apply run_preserves_outside
    rw [(modUnary_wires U n p hw hn).2]
    simp [hq,hkc,hqf]

theorem modUnary_resources (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hnd : U.wires.Nodup) (hn : 0<n) :
    toffoliCount (dblInPlace U p)=2*n-1 ∧ measurementCount (dblInPlace U p)=2*n-1 ∧
    qubitCount (dblInPlace U p)=3*n+3 ∧
    toffoliCount (halfInPlace U p)=2*n ∧ measurementCount (halfInPlace U p)=2*n ∧
    qubitCount (halfInPlace U p)=3*n+4 := by
  have h := modUnary_counts U n p hw hn
  have hd : (U.z++U.core.work).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hh := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,List.count_append] at hh ⊢
    omega
  have hh : (U.z++U.core.work++[U.flag]).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hh := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,List.count_append] at hh ⊢
    omega
  refine ⟨h.1,h.2.1,?_,h.2.2.1,h.2.2.2,?_⟩
  · rw [qubitCount,(modUnary_wires U n p hw hn).1,List.toFinset_card_of_nodup hd]
    simp [ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,hw.low,hw.constant,hw.carry]
    omega
  · rw [qubitCount,(modUnary_wires U n p hw hn).2,List.toFinset_card_of_nodup hh]
    simp [ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,hw.low,hw.constant,hw.carry]
    omega

end ECDSAAdd.Arithmetic
