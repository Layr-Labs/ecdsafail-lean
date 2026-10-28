import ECDSAAdd.Arithmetic.InPlaceAdder
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Math.ModInPlace

namespace ECDSAAdd.Arithmetic

/-- 模加核的固定线路：最高位借作约减标志；mask/flag 属于外层，不放入核工作区。 -/
structure ModAddCoreLayout where
  a : List Wire
  low : List Wire
  high : Wire
  constant : List Wire
  carry : List Wire
  cin : Wire

namespace ModAddCoreLayout

def z (L : ModAddCoreLayout) : List Wire := L.low ++ [L.high]
def work (L : ModAddCoreLayout) : List Wire := L.constant ++ L.carry ++ [L.cin]
def wires (L : ModAddCoreLayout) : List Wire := L.a ++ L.z ++ L.work

/-- 低位 n 根，扩宽数据与常数 n+1 根，完整进位链 n 根。 -/
structure Widths (L : ModAddCoreLayout) (n : Nat) : Prop where
  a : L.a.length = n+1
  low : L.low.length = n
  constant : L.constant.length = n+1
  carry : L.carry.length = n

end ModAddCoreLayout

/-- 四个可辨认阶段：计算扩宽和、试减 p、借位时低位加回 p、由结果与源比较清借位。
constant/carry/cin 初末零；核源可以是外层已装载的 mask，不能提前清该源。 -/
def modAddCore (L : ModAddCoreLayout) (p : Nat) : Program :=
  -- 1. 高位初始零；扩宽寄存器容纳完整 A+Z。
  addInPlace L.a L.z L.carry L.cin ++
  -- 2. 试减 p；结果最高位记录 A+Z<p。装卸常数不影响该标志。
  xorConstant L.constant p ++ subInPlace L.constant L.z L.carry L.cin ++
  xorConstant L.constant p ++
  -- 3. 借位为真时只向低位加回 p，最高位保持直到最后比较。
  maskedAddConst L.high (L.constant.take L.low.length) L.low
    (L.carry.take (L.low.length-1)) L.cin p ++
  -- 4. 规范结果小于源当且仅当曾约减；比较后 X 清原借位。
  compareLt none L.low (L.a.take L.low.length) L.carry L.cin L.high ++ [.X L.high]

/-- 同一核门列的计数，不把尚未证明的正确性或支持集作为假设。 -/
theorem modAddCore_counts (L : ModAddCoreLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0 < n) :
    toffoliCount (modAddCore L p) = 4*n-1 ∧
    measurementCount (modAddCore L p) = 4*n-1 := by
  have hz : L.z.length = n+1 := by simp [ModAddCoreLayout.z, hw.low]
  have ha := addInPlace_counts L.a L.z L.carry L.cin (hw.a.trans hz.symm)
    (by rw [hw.carry, hz])
  have hs := subInPlace_counts L.constant L.z L.carry L.cin
    (hw.constant.trans hz.symm) (by rw [hw.carry, hz])
  have ht : (L.constant.take L.low.length).length = n := by
    simp [hw.low, hw.constant]
  have hk : (L.carry.take (L.low.length-1)).length = n-1 := by
    simp [hw.low, hw.carry]
  have hm := addInPlace_counts (L.constant.take L.low.length) L.low
    (L.carry.take (L.low.length-1)) L.cin (ht.trans hw.low.symm)
    (by rw [hk, hw.low]; omega)
  have hx : (L.a.take L.low.length).length = n := by simp [hw.low, hw.a]
  have hc := compareLt_counts none L.low (L.a.take L.low.length) L.carry L.cin L.high
    (hw.low.trans hx.symm) (hw.carry.trans hx.symm)
  simp only [hw.low] at hm hc
  simp only [modAddCore, maskedAddConst, toffoliCount_append, measurementCount_append,
    ha.1, ha.2, hs.1, hs.2, hm.1, hm.2, hc.1, hc.2,
    (xorConstant_counts _ _).1, (xorConstant_counts _ _).2,
    (maskedConstant_counts _ _ _).1, (maskedConstant_counts _ _ _).2,
    hz, hw.low, toffoliCount, measurementCount]
  simp only [List.length_take, hw.a, Nat.min_eq_left (by omega : n ≤ n+1)]
  simp
  omega

/-- 第一阶段只改变扩宽目标；其余寄存器逐线保持。 -/
private theorem modAddCore_sum (L : ModAddCoreLayout) (n A Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) :
    {{ L.a=A, L.z=Z, L.work=0 }} addInPlace L.a L.z L.carry L.cin
    {{ L.a=A, L.z=(A+Z)%2^(n+1), L.work=0 }} := by
  have hcnt := List.nodup_iff_count.mp hnd
  have hsub : (L.cin :: (L.a ++ L.z ++ L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := hcnt q
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h ⊢
    omega
  have outside (q : Wire) (hq : q ∈ L.a ++ L.work) : q ∉ L.z := by
    intro hz
    have h := hcnt q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hz
    simp only [ModAddCoreLayout.wires, List.count_append] at h h1
    omega
  have hz : L.z.length = n+1 := by simp [ModAddCoreLayout.z, hw.low]
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero L.work s.basis).mp h.2
  obtain ⟨hp, he, hv⟩ := addInPlace_correct L.a L.z L.carry L.cin hsub
    (hw.a.trans hz.symm) (by rw [hw.carry, hz]) s m
    (fun q hq => clean q (by simp [ModAddCoreLayout.work, hq]))
  refine ⟨hp, ⟨?_, ?_⟩, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => he q (outside q (by simp [hq])))).trans h.1.1
  · rw [hv, h.1.1, h.1.2, clean L.cin (by simp [ModAddCoreLayout.work]),
      Bool.toNat_false, Nat.add_zero, hz]
  · exact (regValue_congr _ _ _ (fun q hq => he q (outside q (by simp [hq])))).trans h.2

/-- 常数装卸只改变常数字；将源、目标和进位零条件显式带过。 -/
private theorem modAddCore_load (L : ModAddCoreLayout) (hnd : L.wires.Nodup)
    (A Z T p : Nat) (hp : p < 2^L.constant.length) :
    {{ L.a=A, L.z=Z, L.constant=T, L.carry=0, L.cin=false }} xorConstant L.constant p
    {{ L.a=A, L.z=Z, L.constant=(T ^^^ p), L.carry=0, L.cin=false }} := by
  have hcnt := List.nodup_iff_count.mp hnd
  have hc : L.constant.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcnt q
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h
    omega
  have outside (q : Wire) (hq : q ∈ L.a ++ L.z ++ L.carry ++ [L.cin]) : q ∉ L.constant := by
    intro ht
    have h := hcnt q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr ht
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h h1
    omega
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hf, he, hv⟩ := xorConstant_correct L.constant hc p hp s m
  refine ⟨hf, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => he q (outside q (by simp [hq])))).trans h.1.1.1.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (outside q (by simp [hq])))).trans h.1.1.1.2
  · rw [hv, h.1.1.2]
  · exact (regValue_congr _ _ _ (fun q hq => he q (outside q (by simp [hq])))).trans h.1.2
  · exact (he L.cin (outside L.cin (by simp))).trans h.2

/-- 用常数字做扩宽减法，原源 a 不在门列支持中。 -/
private theorem modAddCore_subtract (L : ModAddCoreLayout) (n A Z p : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) :
    {{ L.a=A, L.z=Z, L.constant=p, L.carry=0, L.cin=false }}
      subInPlace L.constant L.z L.carry L.cin
    {{ L.a=A, L.z=(Z+2^(n+1)-p)%2^(n+1), L.constant=p, L.carry=0, L.cin=false }} := by
  have hcnt := List.nodup_iff_count.mp hnd
  have hs : (L.cin :: (L.constant ++ L.z ++ L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := hcnt q
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h ⊢
    omega
  have hz : L.z.length = n+1 := by simp [ModAddCoreLayout.z, hw.low]
  have ht := hw.constant.trans hz.symm
  have hk : L.carry.length+1=L.z.length := by rw [hw.carry, hz]
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hP : ((regValue L.constant s.basis = p ∧ regValue L.z s.basis = Z) ∧
      s.basis L.cin = false) ∧ regValue L.carry s.basis = 0 :=
    ⟨⟨⟨h.1.1.2, h.1.1.1.2⟩, h.2⟩, h.1.2⟩
  obtain ⟨hf, hv⟩ := subInPlace_spec L.constant L.z L.carry L.cin hs ht hk p Z s m hP
  simp only [Holds.holds] at hv
  have ha : regValue L.a (run (subInPlace L.constant L.z L.carry L.cin) m s).basis = A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) h.1.1.1.1
    intro q hq
    apply run_preserves_outside
    rw [subInPlace_wires _ _ _ _ ht hk]
    intro hm
    have h1 := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have h2 := List.count_pos_iff.mpr hq
    have h3 := hcnt q
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h1 h3
    omega
  exact ⟨hf, ⟨⟨⟨ha, by simpa only [hz] using hv.1.1.2⟩, hv.1.1.1⟩, hv.2⟩, hv.1.2⟩

/-- 第二阶段：装 p、扩宽减 p、卸 p；整体恢复全部核工作位。 -/
theorem modAddCore_reduce (L : ModAddCoreLayout) (n A Z p : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hp : p < 2^(n+1)) :
    {{ L.a=A, L.z=Z, L.work=0 }}
      (xorConstant L.constant p ++ subInPlace L.constant L.z L.carry L.cin ++
        xorConstant L.constant p)
    {{ L.a=A, L.z=(Z+2^(n+1)-p)%2^(n+1), L.work=0 }} := by
  have h1 := modAddCore_load L hnd A Z 0 p (by simpa only [hw.constant] using hp)
  have h2 := modAddCore_subtract L n A Z p hw hnd
  have h3 := modAddCore_load L hnd A ((Z+2^(n+1)-p)%2^(n+1)) p p
    (by simpa only [hw.constant] using hp)
  simp only [Nat.zero_xor, Nat.xor_self] at h1 h3
  have hh := (h1.seq h2).seq h3
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero L.work s.basis).mp h.2
  have hc : regValue L.constant s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModAddCoreLayout.work, hq]))
  have hk : regValue L.carry s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModAddCoreLayout.work, hq]))
  obtain ⟨hf, hv⟩ := hh s m ⟨⟨⟨h.1, hc⟩, hk⟩, clean L.cin (by simp [ModAddCoreLayout.work])⟩
  simp only [Holds.holds] at hv
  refine ⟨hf, hv.1.1.1, (regValue_zero _ _).mpr ?_⟩
  intro q hq
  simp only [ModAddCoreLayout.work, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (hq | hq) | hq
  · exact (regValue_zero _ _).mp hv.1.1.2 q hq
  · exact (regValue_zero _ _).mp hv.1.2 q hq
  · subst q; exact hv.2

/-- 第三阶段：只向低位加回 p；借位与原源保持，借用的常数/进位前缀归零。 -/
theorem modAddCore_addback (L : ModAddCoreLayout) (n A Z p : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hn : 0<n) (hp : p<2^n) :
    {{ L.a=A, L.low=Z, L.high=B, L.work=0 }}
      maskedAddConst L.high (L.constant.take L.low.length) L.low
        (L.carry.take (L.low.length-1)) L.cin p
    {{ L.a=A, L.low=(Z+(if B then p else 0))%2^n, L.high=B, L.work=0 }} := by
  let T := L.constant.take L.low.length
  let C := L.carry.take (L.low.length-1)
  have hT : T.length=n := by simp [T, hw.low, hw.constant]
  have hC : C.length=n-1 := by simp [C, hw.low, hw.carry]
  have tsub : T.Sublist L.constant := List.take_sublist _ _
  have csub : C.Sublist L.carry := List.take_sublist _ _
  have hcnt := List.nodup_iff_count.mp hnd
  have hs : (L.high :: L.cin :: (T ++ L.low ++ C)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have ht := tsub.count_le q
    have hc := csub.count_le q
    have h := hcnt q
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.z, ModAddCoreLayout.work,
      List.count_append, List.count_cons, List.count_nil] at h ⊢
    omega
  have ht : T.length=L.low.length := hT.trans hw.low.symm
  have hc : C.length+1=L.low.length := by rw [hC, hw.low]; omega
  let circuit := maskedAddConst L.high T L.low C L.cin p
  have ws := (maskedConst_wires_subset L.high T L.low C L.cin p ht hc).1
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero L.work s.basis).mp h.2
  have htv : regValue T s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModAddCoreLayout.work, tsub.subset hq]))
  have hcv : regValue C s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModAddCoreLayout.work, csub.subset hq]))
  have hcin := clean L.cin (by simp [ModAddCoreLayout.work])
  obtain ⟨hf, hv⟩ := maskedAddConst_spec L.high L.cin T L.low C hs ht hc p
    (by simpa only [hT] using hp) B Z s m ⟨⟨⟨⟨h.1.2, htv⟩, h.1.1.2⟩, hcin⟩, hcv⟩
  simp only [Holds.holds] at hv
  have away (q : Wire) (hq : q ∈ L.a ++ L.work) : q ≠ L.high ∧ q ≠ L.cin ∧ q ∉ L.low ∨ q=L.cin := by
    have h := hcnt q
    have hm := List.count_pos_iff.mpr hq
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.z, ModAddCoreLayout.work,
      List.count_append, List.count_cons, List.count_nil] at h hm
    by_cases he : q=L.cin
    · exact Or.inr he
    · left
      constructor
      · intro he; subst q; simp only [beq_iff_eq] at h hm; simp at h; omega
      constructor
      · exact he
      · intro hl
        have := List.count_pos_iff.mpr hl
        omega
  have keep (q : Wire) (hq : q ∈ L.a ++ L.work) (hcin' : q ≠ L.cin)
      (hqt : q ∉ T) (hqc : q ∉ C) : (run circuit m s).basis q = s.basis q := by
    apply run_preserves_outside
    intro hh
    have hm := List.mem_toFinset.mp (ws hh)
    rcases away q hq with hh | hh
    · simp only [List.mem_cons, List.mem_append] at hm
      rcases hm with hh' | hh' | (hh' | hh') | hh'
      · exact hh.1 hh'
      · exact hcin' hh'
      · exact hqt hh'
      · exact hh.2.2 hh'
      · exact hqc hh'
    · exact hcin' hh
  have ha : regValue L.a (run circuit m s).basis=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) h.1.1.1
    intro q hq
    have h := hcnt q
    have hm := List.count_pos_iff.mpr hq
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.work, List.count_append,
      List.count_cons, List.count_nil] at h
    apply keep q (by simp [hq])
    · intro he; subst q; simp only [beq_iff_eq] at h hm; simp at h; omega
    · intro he; have := List.count_pos_iff.mpr (tsub.subset he); omega
    · intro he; have := List.count_pos_iff.mpr (csub.subset he); omega
  refine ⟨hf, ⟨⟨ha, ?_⟩, hv.1.1.1.1⟩, (regValue_zero _ _).mpr ?_⟩
  · simpa only [T, C, hw.low] using hv.1.1.2
  · intro q hq
    by_cases htq : q∈T
    · exact (regValue_zero _ _).mp hv.1.1.1.2 q htq
    by_cases hcq : q∈C
    · exact (regValue_zero _ _).mp hv.2 q hcq
    by_cases he : q=L.cin
    · subst q; exact hv.1.2
    · exact (keep q (by simp [hq]) he htq hcq).trans (clean q hq)

private theorem regValue_take_mod (r : List Wire) (n : Nat) (hn : n ≤ r.length)
    (s : BasisState) : regValue (r.take n) s = regValue r s % 2^n := by
  have hh := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hn] at hh
  rw [hh, Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt ?_).symm
  simpa only [List.length_take, Nat.min_eq_left hn] using regValue_lt (r.take n) s

/-- 最后比较只翻转最高位；在正确的借位前提下清零，不改低位、源和工作区。 -/
private theorem modAddCore_finish (L : ModAddCoreLayout) (n A R : Nat) (B : Bool)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hA : A<2^n)
    (hB : B = !decide (R<A)) :
    {{ L.a=A, L.low=R, L.high=B, L.work=0 }}
      (compareLt none L.low (L.a.take L.low.length) L.carry L.cin L.high ++ [.X L.high])
    {{ L.a=A, L.z=R, L.work=0 }} := by
  have hcnt := List.nodup_iff_count.mp hnd
  have hs : (L.high :: L.cin :: (L.low ++ L.a.take L.low.length ++ L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have ht := (List.take_sublist L.low.length L.a).count_le q
    have h := hcnt q
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.z, ModAddCoreLayout.work,
      List.count_append, List.count_cons, List.count_nil] at h ⊢
    omega
  have hh (q : Wire) (hq : q ∈ L.a ++ L.low ++ L.work) : q ≠ L.high := by
    intro he; subst q
    have h := hcnt L.high
    have hm := List.count_pos_iff.mpr hq
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.z, List.count_append,
      List.count_cons, List.count_nil, beq_self_eq_true, if_true] at h hm
    omega
  have ht : (L.a.take L.low.length).length=n := by simp [hw.a, hw.low]
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero L.work s.basis).mp h.2
  have hv : regValue (L.a.take L.low.length) s.basis=A := by
    rw [regValue_take_mod _ _ (by rw [hw.low, hw.a]; omega), h.1.1.1,
      hw.low, Nat.mod_eq_of_lt hA]
  obtain ⟨hf, he, hb⟩ := compareLt_correct none L.low (L.a.take L.low.length)
    L.carry L.cin L.high hs (by simp) (hw.low.trans ht.symm) (hw.carry.trans ht.symm)
    s m (clean L.cin (by simp [ModAddCoreLayout.work]))
    (fun q hq => clean q (by simp [ModAddCoreLayout.work, hq]))
  have hb' : (run (compareLt none L.low (L.a.take L.low.length) L.carry L.cin L.high) m s).basis L.high = true := by
    rw [hb, h.1.2, h.1.1.2, hv, hB]
    simp [controlValue]
  rw [run_append, run_take]
  simp only [run]
  refine ⟨hf, ⟨?_, ?_⟩, ?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) h.1.1.1
    intro q hq
    have hn := hh q (by simp [hq])
    simpa only [writeBit, Function.update_of_ne hn] using he q hn
  · rw [ModAddCoreLayout.z, regValue_append]
    have hl : regValue L.low
        (writeBit (run (compareLt none L.low (L.a.take L.low.length) L.carry L.cin L.high) m s).basis
          L.high (!(run (compareLt none L.low (L.a.take L.low.length) L.carry L.cin L.high) m s).basis L.high)) = R := by
      apply Eq.trans (regValue_congr _ _ _ ?_) h.1.1.2
      intro q hq
      have hn := hh q (by simp [hq])
      simpa only [writeBit, Function.update_of_ne hn] using he q hn
    rw [hl]
    simp [regValue, writeBit, hb']
  · apply Eq.trans (regValue_congr _ _ _ ?_) h.2
    intro q hq
    have hn := hh q (by simp [hq])
    simpa only [writeBit, Function.update_of_ne hn] using he q hn

/-- 扩展源 A≤p 的完整模加：保留源、规范化目标、全部核工作位归零，并恢复相位。 -/
theorem modAddCore_spec (L : ModAddCoreLayout) (n p A Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A≤p) (hZ : Z<p) :
    {{ L.a=A, L.z=Z, L.work=0 }} modAddCore L p
    {{ L.a=A, L.z=(A+Z)%p, L.work=0 }} := by
  have hn : 0<n := by
    by_contra h
    have he : n=0 := by omega
    rw [he] at hpn
    simp at hpn
    omega
  have hsum : A+Z<2^(n+1) := by rw [Nat.pow_succ]; omega
  have hwide : p<2^(n+1) := by rw [Nat.pow_succ]; omega
  let D := (A+Z+2^(n+1)-p)%2^(n+1)
  let R := (A+Z)%p
  let B := decide (A+Z<p)
  have hfirst := (modAddCore_sum L n A Z hw hnd).seq
    (modAddCore_reduce L n A ((A+Z)%2^(n+1)) p hw hnd hwide)
  simp only [Nat.mod_eq_of_lt hsum] at hfirst
  have hlow := modAddCore_low (A+Z) p n hp hpn (by omega)
  have hborrow := (addReduction (A+Z) p n hp hpn (by omega)).1
  have hlast : B = !decide (R<A) := by
    have hh := modAddCore_cleanup A Z p hA hZ
    dsimp [B, R]
    by_cases h : A+Z<p
    · have hh' := hh.mp h
      simp [h, Nat.not_lt.mpr hh']
    · have hh' : ¬ A≤(A+Z)%p := fun he => h (hh.mpr he)
      simp [h, Nat.lt_of_not_ge hh']
  have hadd := modAddCore_addback L n A (D%2^n) p B hw hnd hn hpn
  have hfinish := modAddCore_finish L n A R B hw hnd (by omega) hlast
  have hrest :
      {{ L.a=A, L.z=D, L.work=0 }}
        (maskedAddConst L.high (L.constant.take L.low.length) L.low
          (L.carry.take (L.low.length-1)) L.cin p ++
          (compareLt none L.low (L.a.take L.low.length) L.carry L.cin L.high ++ [.X L.high]))
      {{ L.a=A, L.z=R, L.work=0 }} := by
    have hmiddle :
        {{ L.a=A, L.low=D%2^n, L.high=B, L.work=0 }}
          maskedAddConst L.high (L.constant.take L.low.length) L.low
            (L.carry.take (L.low.length-1)) L.cin p
        {{ L.a=A, L.low=R, L.high=B, L.work=0 }} := hadd.conseq (fun _ h => h) (fun st h => by
      simp only [Holds.holds] at h ⊢
      have he : (D%2^n+(if B then p else 0))%2^n=R := by
        simpa only [D, B, R, decide_eq_true_eq] using hlow
      exact ⟨⟨⟨h.1.1.1, he ▸ h.1.1.2⟩, h.1.2⟩, h.2⟩)
    apply (hmiddle.seq hfinish).conseq ?_ (fun _ h => h)
    intro st h
    simp only [Holds.holds] at h ⊢
    have hl : regValue L.low st=D%2^n := by
      rw [regValue_low L.low L.high, ← ModAddCoreLayout.z, h.1.2, hw.low]
    have hb : st L.high=B := by
      have hh := regValue_highBit L.low L.high st
      rw [← ModAddCoreLayout.z, h.1.2, hw.low] at hh
      have he : st L.high=true ↔ A+Z<p := hh.trans hborrow
      cases hv : st L.high
      · have hn : ¬ A+Z<p := fun ht => by simpa only [hv, Bool.false_eq_true] using he.mpr ht
        simp only [B, decide_eq_false hn]
      · have hy : A+Z<p := he.mp hv
        simp only [B, decide_eq_true hy]
    exact ⟨⟨⟨h.1.1, hl⟩, hb⟩, h.2⟩
  simpa only [modAddCore, List.append_assoc, D, R] using hfirst.seq hrest

/-- 核的实际支持恰为源、目标、常数字及进位工作线；没有隐含的 mask/flag。 -/
theorem modAddCore_wires (L : ModAddCoreLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) : wires (modAddCore L p) = L.wires.toFinset := by
  have hz : L.z.length=n+1 := by simp [ModAddCoreLayout.z, hw.low]
  have ha := addInPlace_wires L.a L.z L.carry L.cin (hw.a.trans hz.symm)
    (by rw [hw.carry, hz])
  have hs := subInPlace_wires L.constant L.z L.carry L.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry, hz])
  have ht : (L.constant.take L.low.length).length=L.low.length := by simp [hw.low, hw.constant]
  have hk : (L.carry.take (L.low.length-1)).length+1=L.low.length := by
    simp [hw.low, hw.carry]; omega
  have hm := (maskedConst_wires_subset L.high (L.constant.take L.low.length) L.low
    (L.carry.take (L.low.length-1)) L.cin p ht hk).1
  have hx : (L.a.take L.low.length).length=n := by simp [hw.low, hw.a]
  have hc := (compareLt_wires none L.low (L.a.take L.low.length) L.carry L.cin L.high
    (hw.low.trans hx.symm) (hw.carry.trans hx.symm)).1
  have htSub := (List.take_sublist L.low.length L.constant).subset
  have hcSub := (List.take_sublist (L.low.length-1) L.carry).subset
  have hxSub := (List.take_sublist L.low.length L.a).subset
  have hconst := xorConstant_wires_subset L.constant p
  apply Finset.Subset.antisymm
  · intro q hq
    simp only [modAddCore, wires_append, Finset.mem_union, ha, hs, hc] at hq
    have base : q ∈ L.a ∨ q ∈ L.z ∨ q ∈ L.constant ∨ q ∈ L.carry ∨ q=L.cin ∨ q=L.high := by
      rcases hq with (((((hq | hq) | hq) | hq) | hq) | hq) | hq
      · simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq; tauto
      · have := List.mem_toFinset.mp (hconst hq); tauto
      · simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq; tauto
      · have := List.mem_toFinset.mp (hconst hq); tauto
      · have hh := List.mem_toFinset.mp (hm hq)
        simp only [List.mem_cons, List.mem_append] at hh
        rcases hh with hh | hh | (hh | hh) | hh
        · tauto
        · tauto
        · have := htSub hh; tauto
        · have : q ∈ L.z := by simp [ModAddCoreLayout.z, hh]
          tauto
        · have := hcSub hh; tauto
      · simp only [List.mem_toFinset, Option.toList_none, List.nil_append,
          List.mem_cons, List.mem_append] at hq
        rcases hq with hq | hq | (hq | hq) | hq
        · tauto
        · tauto
        · have : q ∈ L.z := by simp [ModAddCoreLayout.z, hq]
          tauto
        · have := hxSub hq; tauto
        · tauto
      · have : q=L.high := by simpa [wires, Instr.wires] using hq
        tauto
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.work, ModAddCoreLayout.z,
      List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at base ⊢
    tauto
  · intro q hq
    simp only [ModAddCoreLayout.wires, ModAddCoreLayout.work, List.mem_toFinset,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    have hbase : q ∈ wires (addInPlace L.a L.z L.carry L.cin) ∨
        q ∈ wires (subInPlace L.constant L.z L.carry L.cin) := by
      rw [ha, hs]
      simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
      tauto
    simp only [modAddCore, wires_append, Finset.mem_union]
    rcases hbase with hb | hb
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hb)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hb))))

/-- 完整核规格与支持集共同推出目标之外逐线保持，包括借用视图外的控制和掩码。 -/
theorem modAddCore_frame (L : ModAddCoreLayout) (n p A Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hp : 0<p) (hpn : p<2^n)
    (hA : A≤p) (hZ : Z<p) (s : State) (m : List Bool)
    (ha : regValue L.a s.basis=A) (hz : regValue L.z s.basis=Z)
    (hc : regValue L.work s.basis=0) (q : Wire) (hq : q∉L.z) :
    (run (modAddCore L p) m s).basis q=s.basis q := by
  obtain ⟨_, h⟩ := modAddCore_spec L n p A Z hw hnd hp hpn hA hZ s m ⟨⟨ha,hz⟩,hc⟩
  simp only [Holds.holds] at h
  by_cases hqa : q∈L.a
  · exact (regValue_eq_iff _ _ _).mp (h.1.1.trans ha.symm) q hqa
  by_cases hqc : q∈L.work
  · exact (regValue_eq_iff _ _ _).mp (h.2.trans hc.symm) q hqc
  apply run_preserves_outside
  rw [modAddCore_wires L n p hw (by
    by_contra hn
    have he : n=0 := by omega
    rw [he] at hpn
    simp at hpn
    omega)]
  simpa [ModAddCoreLayout.wires] using And.intro hqa (And.intro hq hqc)

/-- 同一模加核程序的精确门数、测量数与实际静态线路数。 -/
theorem modAddCore_resources (L : ModAddCoreLayout) (n p : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hn : 0<n) :
    toffoliCount (modAddCore L p)=4*n-1 ∧
    measurementCount (modAddCore L p)=4*n-1 ∧
    qubitCount (modAddCore L p)=4*n+4 := by
  refine ⟨(modAddCore_counts L n p hw hn).1, (modAddCore_counts L n p hw hn).2, ?_⟩
  rw [qubitCount, modAddCore_wires L n p hw hn, List.toFinset_card_of_nodup hnd]
  simp only [ModAddCoreLayout.wires, ModAddCoreLayout.z, ModAddCoreLayout.work,
    List.length_append, List.length_cons, List.length_nil, hw.a, hw.low, hw.constant, hw.carry]
  omega

end ECDSAAdd.Arithmetic
