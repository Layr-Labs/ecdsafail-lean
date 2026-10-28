import ECDSAAdd.Arithmetic.ModInPlace
import ECDSAAdd.Arithmetic.ModInPlaceCopy
import ECDSAAdd.Arithmetic.MeasuredMaskedAdder

namespace ECDSAAdd.Arithmetic

/-- 外层模算术布局：核工作区之外的 mask 用于受控源，flag 留给单目半倍。
子视图只借用线路，不把 mask 重复加入核工作区。 -/
structure ModInPlaceLayout extends ModAddCoreLayout where
  mask : List Wire
  flag : Wire

namespace ModInPlaceLayout

def z (L : ModInPlaceLayout) : List Wire := L.toModAddCoreLayout.z
def work (L : ModInPlaceLayout) : List Wire := L.toModAddCoreLayout.work ++ L.mask ++ [L.flag]
def wires (L : ModInPlaceLayout) : List Wire := L.a ++ L.z ++ L.work

structure Widths (L : ModInPlaceLayout) (n : Nat) : Prop where
  core : L.toModAddCoreLayout.Widths n
  mask : L.mask.length=n+1

/-- mask 存活时作为源；constant/carry/cin 是唯一核工作区。 -/
def maskedCore (L : ModInPlaceLayout) : ModAddCoreLayout := { L.toModAddCoreLayout with a := L.mask }

end ModInPlaceLayout

/-- 普通模加直接调用核，未使用的 mask/flag 保持零。 -/
def modAddInPlace (L : ModInPlaceLayout) (p : Nat) : Program := modAddCore L.toModAddCoreLayout p

/-- 装载受控源，计算模和，再清源掩码；mask 必须存活到核比较清借位之后。 -/
def controlledModAdd (c : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  copyRegister (some c) (L.a.take L.low.length) (L.mask.take L.low.length) ++
  modAddCore L.maskedCore p ++
  copyRegister (some c) (L.a.take L.low.length) (L.mask.take L.low.length)

private theorem outer_core_nodup (L : ModInPlaceLayout) (hnd : L.wires.Nodup) :
    L.toModAddCoreLayout.wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  simp only [ModInPlaceLayout.wires, ModInPlaceLayout.z, ModInPlaceLayout.work,
    ModAddCoreLayout.wires, List.count_append] at h ⊢
  omega

/-- 公开模加允许临时源等于 p，所有外层工作线初末为零。 -/
theorem modAddInPlace_spec (L : ModInPlaceLayout) (n p A Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A≤p) (hZ : Z<p) :
    {{ L.a=A, L.z=Z, L.work=0 }} modAddInPlace L p
    {{ L.a=A, L.z=(Z+A)%p, L.work=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero L.work s.basis).mp h.2
  have hc : regValue L.toModAddCoreLayout.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModInPlaceLayout.work, hq]))
  have hcnd := outer_core_nodup L hnd
  obtain ⟨hf,hv⟩ := modAddCore_spec L.toModAddCoreLayout n p A Z hw.core hcnd hp hpn hA hZ
    s m ⟨h.1,hc⟩
  simp only [Holds.holds] at hv
  refine ⟨hf, ⟨hv.1.1, by simpa only [Nat.add_comm] using hv.1.2⟩, (regValue_zero _ _).mpr ?_⟩
  intro q hq
  have hnot : q ∉ L.z := by
    intro hz
    have h1 := List.nodup_iff_count.mp hnd q
    have h2 := List.count_pos_iff.mpr hq
    have h3 := List.count_pos_iff.mpr hz
    simp only [ModInPlaceLayout.wires, List.count_append] at h1
    omega
  exact (modAddCore_frame L.toModAddCoreLayout n p A Z hw.core hcnd hp hpn hA hZ
    s m h.1.1 h.1.2 hc q hnot).trans (clean q hq)

/-- 公共模加不改变目标之外的任何物理位。 -/
theorem modAddInPlace_frame (L : ModInPlaceLayout) (n p A Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A≤p) (hZ : Z<p) (s : State) (m : List Bool)
    (ha : regValue L.a s.basis=A) (hz : regValue L.z s.basis=Z)
    (hc : regValue L.work s.basis=0) (q : Wire) (hq : q∉L.z) :
    (run (modAddInPlace L p) m s).basis q=s.basis q := by
  have hk : regValue L.toModAddCoreLayout.work s.basis=0 := (regValue_zero _ _).mpr
    (fun r hr => (regValue_zero _ _).mp hc r (by simp [ModInPlaceLayout.work, hr]))
  exact modAddCore_frame L.toModAddCoreLayout n p A Z hw.core (outer_core_nodup L hnd)
    hp hpn hA hZ s m ha hz hk q hq

theorem modAddInPlace_resources (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hn : 0<n) :
    toffoliCount (modAddInPlace L p)=4*n-1 ∧
    measurementCount (modAddInPlace L p)=4*n-1 ∧
    qubitCount (modAddInPlace L p)=4*n+4 :=
  modAddCore_resources L.toModAddCoreLayout n p hw.core (outer_core_nodup L hnd) hn

private theorem outer_mask_copy (c : Wire) (L : ModInPlaceLayout) (n p A Z V : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : p<2^n) (hA : A≤p) (hV : V<2^n) :
    {{ c=B, L.a=A, L.z=Z, L.mask=V, L.toModAddCoreLayout.work=0, L.flag=false }}
      copyRegister (some c) (L.a.take L.low.length) (L.mask.take L.low.length)
    {{ c=B, L.a=A, L.z=Z, L.mask=(V ^^^ (if B then A else 0)), L.toModAddCoreLayout.work=0, L.flag=false }} := by
  have hcnt := List.nodup_iff_count.mp hnd
  have hs : (c::L.a++L.mask).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcnt q
    simp only [ModInPlaceLayout.wires, ModInPlaceLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h ⊢
    omega
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hf,he,hv⟩ := copyLow_correct c L.a L.mask L.low.length A V
    (by rw [hw.core.low, hw.core.a]; omega) (by rw [hw.core.low, hw.mask]; omega) hs
    (by rw [hw.core.low]; omega) (by simpa only [hw.core.low] using hV)
    s m h.1.1.1.1.2 h.1.1.2
  have away (q : Wire) (hq : q ∈ c::(L.a++L.z++L.toModAddCoreLayout.work++[L.flag])) : q∉L.mask.take L.low.length := by
    intro hh
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr ((List.take_sublist L.low.length L.mask).subset hh)
    have h3 := hcnt q
    simp only [ModInPlaceLayout.wires, ModInPlaceLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h1 h3
    omega
  refine ⟨hf, ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · exact (he c (away c (by simp))).trans h.1.1.1.1.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans h.1.1.1.1.2
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans h.1.1.1.2
  · simpa only [h.1.1.1.1.1] using hv
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans h.1.2
  · exact (he L.flag (away L.flag (by simp))).trans h.2

private theorem outer_mask_core (c : Wire) (L : ModInPlaceLayout) (n p A Z V : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : 0<p) (hpn : p<2^n)
    (hV : V≤p) (hZ : Z<p) :
    {{ c=B, L.a=A, L.z=Z, L.mask=V, L.toModAddCoreLayout.work=0, L.flag=false }}
      modAddCore L.maskedCore p
    {{ c=B, L.a=A, L.z=(Z+V)%p, L.mask=V, L.toModAddCoreLayout.work=0, L.flag=false }} := by
  have hcnt := List.nodup_iff_count.mp hnd
  have hkw : L.maskedCore.Widths n := ⟨hw.mask, hw.core.low, hw.core.constant, hw.core.carry⟩
  have hkn : L.maskedCore.wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcnt q
    simp only [ModInPlaceLayout.wires, ModInPlaceLayout.work, ModInPlaceLayout.z,
      ModInPlaceLayout.maskedCore, ModAddCoreLayout.wires, ModAddCoreLayout.work, ModAddCoreLayout.z,
      List.count_append, List.count_cons, List.count_nil] at h ⊢
    omega
  intro s m h
  simp only [Holds.holds] at h ⊢
  have away (q : Wire) (hq : q∈c::L.a++[L.flag]) : q∉L.z := by
    intro hh
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    have h3 := hcnt q
    simp only [ModInPlaceLayout.wires, ModInPlaceLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h1 h3
    omega
  obtain ⟨hf,hv⟩ := modAddCore_spec L.maskedCore n p V Z hkw hkn hp hpn hV hZ
    s m ⟨⟨h.1.1.2,h.1.1.1.2⟩,h.1.2⟩
  simp only [Holds.holds] at hv
  have keep (q : Wire) (hq : q∈c::L.a++[L.flag]) :=
    modAddCore_frame L.maskedCore n p V Z hkw hkn hp hpn hV hZ s m
      h.1.1.2 h.1.1.1.2 h.1.2 q (away q hq)
  refine ⟨hf, ⟨⟨⟨⟨?_,?_⟩,?_⟩,hv.1.1⟩,hv.2⟩,?_⟩
  · exact (keep c (by simp)).trans h.1.1.1.1.1
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1.1.1.1.2
  · simpa only [Nat.add_comm] using hv.1.2
  · exact (keep L.flag (by simp)).trans h.2

/-- 控制保持，源保持；掩码只在两个复制阶段之间存活，最终所有外层工作线归零。 -/
theorem controlledModAdd_spec (c : Wire) (L : ModInPlaceLayout) (n p A Z : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A≤p) (hZ : Z<p) :
    {{ c=B, L.a=A, L.z=Z, L.work=0 }} controlledModAdd c L p
    {{ c=B, L.a=A, L.z=(if B then (Z+A)%p else Z), L.work=0 }} := by
  let V := if B then A else 0
  have hV : V≤p := by dsimp [V]; split <;> omega
  have h1 := outer_mask_copy c L n p A Z 0 B hw hnd hpn hA (by positivity)
  have h2 := outer_mask_core c L n p A Z V B hw hnd hp hpn hV hZ
  have h3 := outer_mask_copy c L n p A ((Z+V)%p) V B hw hnd hpn hA (by omega)
  simp only [Nat.zero_xor] at h1
  have hall := (h1.seq h2).seq h3
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero L.work s.basis).mp h.2
  have hm : regValue L.mask s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModInPlaceLayout.work,hq]))
  have hk : regValue L.toModAddCoreLayout.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModInPlaceLayout.work,hq]))
  obtain ⟨hf,hv⟩ := hall s m ⟨⟨⟨h.1,hm⟩,hk⟩,clean L.flag (by simp [ModInPlaceLayout.work])⟩
  simp only [Holds.holds, V, Nat.xor_self] at hv
  refine ⟨hf, ⟨hv.1.1.1.1,?_⟩,?_⟩
  · cases B <;> simpa [controlledModAdd, V,Nat.mod_eq_of_lt hZ] using hv.1.1.1.2
  · apply (regValue_zero _ _).mpr
    intro q hq
    simp only [ModInPlaceLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with (hq | hq) | hq
    · exact (regValue_zero _ _).mp hv.1.2 q hq
    · exact (regValue_zero _ _).mp hv.1.1.2 q hq
    · subst q; exact hv.2

/-- 实际支持不含源高位与 flag；mask 高位由核接入。 -/
theorem controlledModAdd_wires (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    wires (controlledModAdd c L p) =
      (c :: L.a.take n ++ L.maskedCore.wires).toFinset := by
  have hs : (L.a.take L.low.length).length=n := by simp [hw.core.low,hw.core.a]
  have hd : (L.mask.take L.low.length).length=n := by simp [hw.core.low,hw.mask]
  have hc := copyRegister_wires (some c) (L.a.take L.low.length)
    (L.mask.take L.low.length) (hs.trans hd.symm)
  have hne : (L.a.take L.low.length).isEmpty=false := by
    cases h : L.a.take L.low.length with
    | nil => simp [h] at hs; omega
    | cons a as => rfl
  rw [hne] at hc
  simp only [Bool.false_eq_true,if_false,Option.toList_some] at hc
  have hk := modAddCore_wires L.maskedCore n p
    ⟨hw.mask,hw.core.low,hw.core.constant,hw.core.carry⟩ hn
  simp only [hw.core.low] at hc
  simp only [controlledModAdd,wires_append,hw.core.low,hc,hk]
  ext q
  have hm : q∈L.mask.take n → q∈L.mask := fun hh => (List.take_sublist n L.mask).subset hh
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
    List.not_mem_nil,or_false,ModAddCoreLayout.wires,ModInPlaceLayout.maskedCore]
  tauto

theorem controlledModAdd_frame (c : Wire) (L : ModInPlaceLayout) (n p A Z : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A≤p) (hZ : Z<p) (s : State) (m : List Bool)
    (hb : s.basis c=B) (ha : regValue L.a s.basis=A) (hz : regValue L.z s.basis=Z)
    (hc : regValue L.work s.basis=0) (q : Wire) (hq : q∉L.z) :
    (run (controlledModAdd c L p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := controlledModAdd_spec c L n p A Z B hw hnd hp hpn hA hZ
    s m ⟨⟨⟨hb,ha⟩,hz⟩,hc⟩
  simp only [Holds.holds] at h
  by_cases he : q=c
  · subst q; exact h.1.1.1.trans hb.symm
  by_cases hqa : q∈L.a
  · exact (regValue_eq_iff _ _ _).mp (h.1.1.2.trans ha.symm) q hqa
  by_cases hqc : q∈L.work
  · exact (regValue_eq_iff _ _ _).mp (h.2.trans hc.symm) q hqc
  apply run_preserves_outside
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  rw [controlledModAdd_wires c L n p hw hn]
  intro hh
  have ha' : q∉L.a.take n := fun hh => hqa ((List.take_sublist n L.a).subset hh)
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,ModAddCoreLayout.wires,
    ModInPlaceLayout.maskedCore,ModAddCoreLayout.z,ModAddCoreLayout.work,
    List.not_mem_nil,or_false] at hh
  simp only [ModInPlaceLayout.work,ModAddCoreLayout.work,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hqc
  simp only [ModInPlaceLayout.z,ModAddCoreLayout.z,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  tauto

theorem controlledModAdd_resources (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hn : 0<n) :
    toffoliCount (controlledModAdd c L p)=6*n-1 ∧
    measurementCount (controlledModAdd c L p)=4*n-1 ∧
    qubitCount (controlledModAdd c L p)=5*n+5 := by
  have hs : (L.a.take L.low.length).length=n := by simp [hw.core.low,hw.core.a]
  have hd : (L.mask.take L.low.length).length=n := by simp [hw.core.low,hw.mask]
  have hc := copyRegister_counts (some c) (L.a.take L.low.length)
    (L.mask.take L.low.length) (hs.trans hd.symm)
  have hk := modAddCore_counts L.maskedCore n p
    ⟨hw.mask,hw.core.low,hw.core.constant,hw.core.carry⟩ hn
  simp only [Option.isSome_some,if_true,hs] at hc
  refine ⟨?_,?_,?_⟩
  · simp only [controlledModAdd,toffoliCount_append,hc.1,hk.1]; omega
  · simp only [controlledModAdd,measurementCount_append,hc.2,hk.2]; omega
  · have hsub : (c::L.a.take n++L.maskedCore.wires).Nodup := by
      apply List.nodup_iff_count.mpr; intro q
      have hh := List.nodup_iff_count.mp hnd q
      have ht := (List.take_sublist n L.a).count_le q
      simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.z,
        ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.work,
        ModAddCoreLayout.z,List.count_append,List.count_cons,List.count_nil] at hh ⊢
      omega
    rw [qubitCount,controlledModAdd_wires c L n p hw hn,List.toFinset_card_of_nodup hsub]
    simp only [ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.work,
      ModAddCoreLayout.z,List.length_cons,List.length_nil,List.length_append,
      List.length_take,hw.core.a,hw.core.low,hw.mask,hw.core.constant,hw.core.carry]
    omega


/-- 只将末次受控复制换成测量清掩码；中间核保持其与源的逐位关系。 -/
def measuredControlledModAdd (c : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  copyRegister (some c) (L.a.take L.low.length) (L.mask.take L.low.length) ++
  modAddCore L.maskedCore p ++
  eraseMask c (L.a.take L.low.length) (L.mask.take L.low.length)

private theorem outer_mask_erase (c : Wire) (L : ModInPlaceLayout) (n p A Z : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : p<2^n) (hA : A≤p) :
    {{ c=B, L.a=A, L.z=Z, L.mask=(if B then A else 0), L.toModAddCoreLayout.work=0, L.flag=false }}
      eraseMask c (L.a.take L.low.length) (L.mask.take L.low.length)
    {{ c=B, L.a=A, L.z=Z, L.mask=0, L.toModAddCoreLayout.work=0, L.flag=false }} := by
  have hs : (L.a.take L.low.length).length=n := by simp [hw.core.low,hw.core.a]
  have hd : (L.mask.take L.low.length).length=n := by simp [hw.core.low,hw.mask]
  have hst : (c::(L.a.take L.low.length ++ L.mask.take L.low.length)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hnd q
    have ha := (List.take_sublist L.low.length L.a).count_le q
    have hm := (List.take_sublist L.low.length L.mask).count_le q
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,List.count_cons,
      List.count_append,List.count_nil] at h ⊢
    omega
  intro s m h
  simp only [Holds.holds] at h ⊢
  have low (r : List Wire) (N : Nat) (hr : n≤r.length)
      (hv : regValue r s.basis=N) (hb : N<2^n) : regValue (r.take n) s.basis=N := by
    have hh := regValue_append (r.take n) (r.drop n) s.basis
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left hr,hv] at hh
    have hn : 0<2^n := by positivity
    have hz : regValue (r.drop n) s.basis=0 := by
      by_contra h
      have : 1≤regValue (r.drop n) s.basis := by omega
      nlinarith
    simpa [hz] using hh.symm
  have ha := low L.a A (by rw [hw.core.a]; omega) h.1.1.1.1.2 (by omega)
  have hm := low L.mask (if B then A else 0) (by rw [hw.mask]; omega) h.1.1.2
    (by split <;> omega)
  have rel : regValue (L.mask.take L.low.length) s.basis =
      if s.basis c then regValue (L.a.take L.low.length) s.basis else 0 := by
    rw [hw.core.low,ha,hm,h.1.1.1.1.1]
  rw [eraseMask_eq_copy c _ _ (hs.trans hd.symm) hst s m rel]
  have hc := outer_mask_copy c L n p A Z (if B then A else 0) B hw hnd hp hA
    (by split <;> omega) s m h
  simpa only [Holds.holds,Nat.xor_self] using hc

/-- 控制与源保持；测量清理恢复全部工作位和任意测量记录下的符号。 -/
theorem measuredControlledModAdd_spec (c : Wire) (L : ModInPlaceLayout) (n p A Z : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A≤p) (hZ : Z<p) :
    {{ c=B, L.a=A, L.z=Z, L.work=0 }} measuredControlledModAdd c L p
    {{ c=B, L.a=A, L.z=(if B then (Z+A)%p else Z), L.work=0 }} := by
  let V := if B then A else 0
  have hV : V≤p := by dsimp [V]; split <;> omega
  have h1 := outer_mask_copy c L n p A Z 0 B hw hnd hpn hA (by positivity)
  have h2 := outer_mask_core c L n p A Z V B hw hnd hp hpn hV hZ
  have h3 := outer_mask_erase c L n p A ((Z+V)%p) B hw hnd hpn hA
  simp only [Nat.zero_xor] at h1
  have hall := (h1.seq h2).seq h3
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero L.work s.basis).mp h.2
  have hm : regValue L.mask s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModInPlaceLayout.work,hq]))
  have hk : regValue L.toModAddCoreLayout.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModInPlaceLayout.work,hq]))
  obtain ⟨hf,hv⟩ := hall s m ⟨⟨⟨h.1,hm⟩,hk⟩,clean L.flag (by simp [ModInPlaceLayout.work])⟩
  simp only [Holds.holds, V] at hv
  refine ⟨hf, ⟨hv.1.1.1.1,?_⟩,?_⟩
  · cases B <;> simpa [measuredControlledModAdd, V,Nat.mod_eq_of_lt hZ] using hv.1.1.1.2
  · apply (regValue_zero _ _).mpr
    intro q hq
    simp only [ModInPlaceLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with (hq | hq) | hq
    · exact (regValue_zero _ _).mp hv.1.2 q hq
    · exact (regValue_zero _ _).mp hv.1.1.2 q hq
    · subst q; exact hv.2

theorem measuredControlledModAdd_wires (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    wires (measuredControlledModAdd c L p) =
      (c :: L.a.take n ++ L.maskedCore.wires).toFinset := by
  have hs : (L.a.take L.low.length).length=n := by simp [hw.core.low,hw.core.a]
  have hd : (L.mask.take L.low.length).length=n := by simp [hw.core.low,hw.mask]
  have hc := copyRegister_wires (some c) (L.a.take L.low.length)
    (L.mask.take L.low.length) (hs.trans hd.symm)
  have hne : (L.a.take L.low.length).isEmpty=false := by
    cases h : L.a.take L.low.length with
    | nil => simp [h] at hs; omega
    | cons a as => rfl
  rw [hne] at hc
  simp only [Bool.false_eq_true,if_false,Option.toList_some] at hc
  have hk := modAddCore_wires L.maskedCore n p
    ⟨hw.mask,hw.core.low,hw.core.constant,hw.core.carry⟩ hn
  simp only [hw.core.low] at hc
  have he := eraseMask_wires_subset c (L.a.take n) (L.mask.take n)
  simp only [measuredControlledModAdd,wires_append,hw.core.low,hc,hk]
  ext q
  have heq := @he q
  have hm : q∈L.mask.take n → q∈L.mask := fun hh => (List.take_sublist n L.mask).subset hh
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,
    List.not_mem_nil,or_false,ModAddCoreLayout.wires,ModInPlaceLayout.maskedCore] at heq ⊢
  tauto

theorem measuredControlledModAdd_frame (c : Wire) (L : ModInPlaceLayout) (n p A Z : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A≤p) (hZ : Z<p) (s : State) (m : List Bool)
    (hb : s.basis c=B) (ha : regValue L.a s.basis=A) (hz : regValue L.z s.basis=Z)
    (hc : regValue L.work s.basis=0) (q : Wire) (hq : q∉L.z) :
    (run (measuredControlledModAdd c L p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := measuredControlledModAdd_spec c L n p A Z B hw hnd hp hpn hA hZ
    s m ⟨⟨⟨hb,ha⟩,hz⟩,hc⟩
  simp only [Holds.holds] at h
  by_cases he : q=c
  · subst q; exact h.1.1.1.trans hb.symm
  by_cases hqa : q∈L.a
  · exact (regValue_eq_iff _ _ _).mp (h.1.1.2.trans ha.symm) q hqa
  by_cases hqc : q∈L.work
  · exact (regValue_eq_iff _ _ _).mp (h.2.trans hc.symm) q hqc
  apply run_preserves_outside
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  rw [measuredControlledModAdd_wires c L n p hw hn]
  intro hh
  have ha' : q∉L.a.take n := fun hh => hqa ((List.take_sublist n L.a).subset hh)
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,ModAddCoreLayout.wires,
    ModInPlaceLayout.maskedCore,ModAddCoreLayout.z,ModAddCoreLayout.work,
    List.not_mem_nil,or_false] at hh
  simp only [ModInPlaceLayout.work,ModAddCoreLayout.work,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hqc
  simp only [ModInPlaceLayout.z,ModAddCoreLayout.z,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hq
  tauto

theorem measuredControlledModAdd_resources (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hn : 0<n) :
    toffoliCount (measuredControlledModAdd c L p)=5*n-1 ∧
    measurementCount (measuredControlledModAdd c L p)=5*n-1 ∧
    qubitCount (measuredControlledModAdd c L p)=5*n+5 := by
  have hs : (L.a.take L.low.length).length=n := by simp [hw.core.low,hw.core.a]
  have hd : (L.mask.take L.low.length).length=n := by simp [hw.core.low,hw.mask]
  have hc := copyRegister_counts (some c) (L.a.take L.low.length)
    (L.mask.take L.low.length) (hs.trans hd.symm)
  have he := eraseMask_counts c (L.a.take L.low.length)
    (L.mask.take L.low.length) (hs.trans hd.symm)
  have hk := modAddCore_counts L.maskedCore n p
    ⟨hw.mask,hw.core.low,hw.core.constant,hw.core.carry⟩ hn
  simp only [Option.isSome_some,if_true,hs] at hc
  refine ⟨?_,?_,?_⟩
  · simp only [measuredControlledModAdd,toffoliCount_append,hc.1,hk.1,he.1]; omega
  · simp only [measuredControlledModAdd,measurementCount_append,hc.2,hk.2,he.2,hd]; omega
  · have hsub : (c::L.a.take n++L.maskedCore.wires).Nodup := by
      apply List.nodup_iff_count.mpr; intro q
      have hh := List.nodup_iff_count.mp hnd q
      have ht := (List.take_sublist n L.a).count_le q
      simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.z,
        ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.work,
        ModAddCoreLayout.z,List.count_append,List.count_cons,List.count_nil] at hh ⊢
      omega
    rw [qubitCount,measuredControlledModAdd_wires c L n p hw hn,List.toFinset_card_of_nodup hsub]
    simp only [ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.work,
      ModAddCoreLayout.z,List.length_cons,List.length_nil,List.length_append,
      List.length_take,hw.core.a,hw.core.low,hw.mask,hw.core.constant,hw.core.carry]
    omega

end ECDSAAdd.Arithmetic
