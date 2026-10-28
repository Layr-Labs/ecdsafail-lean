import ECDSAAdd.Arithmetic.ModInPlaceWrappers

namespace ECDSAAdd.Arithmetic

/-- 扩宽源取补后加 p+1；0 暂时映为 p，不归一化，第二次调用恢复原值。 -/
def negRaw (L : ModInPlaceLayout) (p : Nat) : Program :=
  notRegister L.a ++ xorConstant L.constant (p+1) ++
  addInPlace L.constant L.a L.carry L.cin ++ xorConstant L.constant (p+1)

private theorem negRaw_nodup (L : ModInPlaceLayout) (hnd : L.wires.Nodup) :
    (L.cin::L.constant++L.a++L.carry).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModAddCoreLayout.work,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

private theorem negRaw_not (L : ModInPlaceLayout) (hnd : L.wires.Nodup) (A : Nat) :
    {{ L.a=A,L.constant=0,L.carry=0,L.cin=false }} notRegister L.a
    {{ L.a=(2^L.a.length-1-A),L.constant=0,L.carry=0,L.cin=false }} := by
  have hn := negRaw_nodup L hnd
  have ha := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).2.1
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hp,hv⟩ := notRegister_spec L.a ha A s m h.1.1.1
  have keep (q : Wire) (hq : q∈L.constant++L.carry++[L.cin]) :
      (run (notRegister L.a) m s).basis q=s.basis q := by
    rw [notRegister_correct L.a ha]
    have hnot : q∉L.a := by
      intro hh
      have h1 := List.count_pos_iff.mpr hq
      have h2 := List.count_pos_iff.mpr hh
      have h3 := List.nodup_iff_count.mp hn q
      simp only [List.count_append,List.count_cons,List.count_nil] at h1 h3
      omega
    simp [hnot]
  exact ⟨hp,⟨⟨hv,(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1.1.2⟩,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1.2⟩,
    (keep L.cin (by simp)).trans h.2⟩

private theorem negRaw_load (L : ModInPlaceLayout) (hnd : L.wires.Nodup) (A T k : Nat)
    (hk : k<2^L.constant.length) :
    {{ L.a=A,L.constant=T,L.carry=0,L.cin=false }} xorConstant L.constant k
    {{ L.a=A,L.constant=(T^^^k),L.carry=0,L.cin=false }} := by
  have hn := negRaw_nodup L hnd
  have hc := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).1
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hp,he,hv⟩ := xorConstant_correct L.constant hc k hk s m
  have keep (q : Wire) (hq : q∈L.a++L.carry++[L.cin]) :
      (run (xorConstant L.constant k) m s).basis q=s.basis q := by
    apply he
    intro hh
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    have h3 := List.nodup_iff_count.mp hn q
    simp only [List.count_append,List.count_cons,List.count_nil] at h1 h3
    omega
  exact ⟨hp,⟨⟨(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1.1.1,
    by rw [hv,h.1.1.2]⟩,(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1.2⟩,
    (keep L.cin (by simp)).trans h.2⟩

private theorem negRaw_add (L : ModInPlaceLayout) (n A k : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) :
    {{ L.a=A,L.constant=k,L.carry=0,L.cin=false }} addInPlace L.constant L.a L.carry L.cin
    {{ L.a=((k+A)%2^(n+1)),L.constant=k,L.carry=0,L.cin=false }} := by
  have hn := negRaw_nodup L hnd
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hp,he,hv⟩ := addInPlace_correct L.constant L.a L.carry L.cin hn
    (hw.core.constant.trans hw.core.a.symm) (by rw [hw.core.carry,hw.core.a]) s m
    ((regValue_zero _ _).mp h.1.2)
  have keep (q : Wire) (hq : q∈L.constant++L.carry++[L.cin]) :
      (run (addInPlace L.constant L.a L.carry L.cin) m s).basis q=s.basis q := by
    apply he
    intro hh
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    have h3 := List.nodup_iff_count.mp hn q
    simp only [List.count_append,List.count_cons,List.count_nil] at h1 h3
    omega
  refine ⟨hp,⟨⟨?_,(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1.1.2⟩,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1.2⟩,
    (keep L.cin (by simp)).trans h.2⟩
  simpa only [h.1.1.1,h.1.1.2,h.2,Bool.toNat_false,Nat.add_zero,hw.core.a] using hv

private theorem negRaw_core (L : ModInPlaceLayout) (n p A : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hpn : p<2^n) (hA : A≤p) :
    {{ L.a=A,L.constant=0,L.carry=0,L.cin=false }} negRaw L p
    {{ L.a=(p-A),L.constant=0,L.carry=0,L.cin=false }} := by
  have hpow : 0<2^n := by positivity
  have hk : p+1<2^L.constant.length := by rw [hw.core.constant,Nat.pow_succ]; omega
  have hv : (p+1+(2^L.a.length-1-A))%2^(n+1)=p-A := by
    rw [hw.core.a]
    have hfit : p-A<2^(n+1) := by rw [Nat.pow_succ]; omega
    have he : p+1+(2^(n+1)-1-A)=2^(n+1)+(p-A) := by rw [Nat.pow_succ]; omega
    simp [he,Nat.mod_eq_of_lt hfit]
  have h1 := negRaw_not L hnd A
  have h2 := negRaw_load L hnd (2^L.a.length-1-A) 0 (p+1) hk
  have h3 := negRaw_add L n (2^L.a.length-1-A) (p+1) hw hnd
  have h4 := negRaw_load L hnd (p-A) (p+1) (p+1) hk
  simp only [Nat.zero_xor] at h2
  simp only [hv] at h3
  simp only [Nat.xor_self] at h4
  exact ((h1.seq h2).seq h3).seq h4

theorem negRaw_wires (L : ModInPlaceLayout) (n p : Nat) (hw : L.Widths n) :
    wires (negRaw L p)=(L.a++L.toModAddCoreLayout.work).toFinset := by
  have hc := xorConstant_wires_subset L.constant (p+1)
  have ha := addInPlace_wires L.constant L.a L.carry L.cin
    (hw.core.constant.trans hw.core.a.symm) (by rw [hw.core.carry,hw.core.a])
  simp only [negRaw,wires_append,notRegister_wires,ha]
  ext q
  have hm : q∈wires (xorConstant L.constant (p+1)) → q∈L.constant :=
    fun hh => List.mem_toFinset.mp (hc hh)
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,List.mem_cons,
    ModAddCoreLayout.work,List.not_mem_nil,or_false]
  tauto

/-- 扩宽取负保持全部源外位，恢复常数与进位；允许输入等于 p。 -/
theorem negRaw_correct (L : ModInPlaceLayout) (n p A : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hpn : p<2^n) (hA : A≤p)
    (s : State) (m : List Bool) (ha : regValue L.a s.basis=A)
    (hc : regValue L.work s.basis=0) :
    (run (negRaw L p) m s).phase=s.phase ∧
    (∀ q, q∉L.a → (run (negRaw L p) m s).basis q=s.basis q) ∧
    regValue L.a (run (negRaw L p) m s).basis=p-A := by
  have clean := (regValue_zero _ _).mp hc
  have hconst : regValue L.constant s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModInPlaceLayout.work,ModAddCoreLayout.work,hq]))
  have hcarry : regValue L.carry s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModInPlaceLayout.work,ModAddCoreLayout.work,hq]))
  have hcin := clean L.cin (by simp [ModInPlaceLayout.work,ModAddCoreLayout.work])
  obtain ⟨hf,hv⟩ := negRaw_core L n p A hw hnd hpn hA s m ⟨⟨⟨ha,hconst⟩,hcarry⟩,hcin⟩
  simp only [Holds.holds] at hv
  refine ⟨hf,?_,hv.1.1.1⟩
  intro q hq
  by_cases hh : q∈L.constant
  · exact (regValue_eq_iff _ _ _).mp (hv.1.1.2.trans hconst.symm) q hh
  by_cases hh' : q∈L.carry
  · exact (regValue_eq_iff _ _ _).mp (hv.1.2.trans hcarry.symm) q hh'
  by_cases he : q=L.cin
  · subst q; exact hv.2.trans hcin.symm
  apply run_preserves_outside
  rw [negRaw_wires L n p hw]
  simp only [ModAddCoreLayout.work,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false]
  tauto

/-- 公开取负规格供模减组合使用；所有目标与工作区保持。 -/
theorem negRaw_spec (L : ModInPlaceLayout) (n p A Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hpn : p<2^n) (hA : A≤p) :
    {{ L.a=A,L.z=Z,L.work=0 }} negRaw L p
    {{ L.a=(p-A),L.z=Z,L.work=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hf,he,hv⟩ := negRaw_correct L n p A hw hnd hpn hA s m h.1.1 h.2
  have away (q : Wire) (hq : q∈L.z++L.work) : q∉L.a := by
    intro hh
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    have h3 := List.nodup_iff_count.mp hnd q
    simp only [ModInPlaceLayout.wires,List.count_append] at h1 h3
    omega
  exact ⟨hf,⟨hv,(regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans h.1.2⟩,
    (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans h.2⟩

theorem negRaw_counts (L : ModInPlaceLayout) (n p : Nat) (hw : L.Widths n) :
    toffoliCount (negRaw L p)=n ∧ measurementCount (negRaw L p)=n := by
  have ha := addInPlace_counts L.constant L.a L.carry L.cin
    (hw.core.constant.trans hw.core.a.symm) (by rw [hw.core.carry,hw.core.a])
  simp only [negRaw,toffoliCount_append,measurementCount_append,(notRegister_counts L.a).1,
    (notRegister_counts L.a).2,(xorConstant_counts L.constant (p+1)).1,
    (xorConstant_counts L.constant (p+1)).2,ha.1,ha.2,hw.core.a]
  omega

end ECDSAAdd.Arithmetic
