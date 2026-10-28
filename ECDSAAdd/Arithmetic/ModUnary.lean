import ECDSAAdd.Arithmetic.ModInPlaceSubtract
import ECDSAAdd.Arithmetic.Rotate

namespace ECDSAAdd.Arithmetic

/-- 单目模算术借用同一目标与 scratch；mask 在半倍期间保持零。 -/
structure ModUnaryLayout where
  low : List Wire
  high : Wire
  constant : List Wire
  carry : List Wire
  cin : Wire
  mask : List Wire
  flag : Wire

namespace ModUnaryLayout

def z (U : ModUnaryLayout) : List Wire := U.low++[U.high]
def core (U : ModUnaryLayout) : ModAddCoreLayout :=
  ⟨U.mask,U.low,U.high,U.constant,U.carry,U.cin⟩
def work (U : ModUnaryLayout) : List Wire := U.core.work++U.mask++[U.flag]
def wires (U : ModUnaryLayout) : List Wire := U.z++U.work
/-- 合法位宽下 low 非空；回退值仅使构造对所有布局有定义。 -/
def bit (U : ModUnaryLayout) : Wire := U.low.headD U.high

structure Widths (U : ModUnaryLayout) (n : Nat) : Prop where
  low : U.low.length=n
  constant : U.constant.length=n+1
  carry : U.carry.length=n
  mask : U.mask.length=n+1

theorem core_widths (U : ModUnaryLayout) (n : Nat) (hw : U.Widths n) : U.core.Widths n :=
  ⟨hw.mask,hw.low,hw.constant,hw.carry⟩

theorem core_nodup (U : ModUnaryLayout) (hnd : U.wires.Nodup) : U.core.wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  simp only [wires,work,core,z,ModAddCoreLayout.wires,ModAddCoreLayout.work,ModAddCoreLayout.z,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem bit_mem (U : ModUnaryLayout) (n : Nat) (hw : U.Widths n) (hn : 0<n) : U.bit∈U.low := by
  cases h : U.low with
  | nil => have hh := hw.low; simp [h] at hh; omega
  | cons a as => simp [bit,h]

theorem bit_value (U : ModUnaryLayout) (n : Nat) (hw : U.Widths n) (hn : 0<n) (s : BasisState) :
    (s U.bit).toNat=regValue U.z s%2 := by
  cases h : U.low with
  | nil => have hh := hw.low; simp [h] at hh; omega
  | cons a as => simp [z,bit,h,regValue,Bool.toNat]; cases s a <;> simp

end ModUnaryLayout

/-- 左旋得到 2Z，试减 p、借位低位加回，最后由结果奇偶清借位。 -/
def dblInPlace (U : ModUnaryLayout) (p : Nat) : Program :=
  rotateLeft U.z ++ xorConstant U.constant p ++ subInPlace U.constant U.z U.carry U.cin ++
  xorConstant U.constant p ++
  maskedAddConst U.high (U.constant.take U.low.length) U.low
    (U.carry.take (U.low.length-1)) U.cin p ++ [.X U.high,.CX U.bit U.high]

/-- 保存奇偶，奇数加 p 后右旋，由减半结果与 (p+1)/2 比较清奇偶位。 -/
def halfInPlace (U : ModUnaryLayout) (p : Nat) : Program :=
  [.CX U.bit U.flag] ++ maskedAddConst U.flag U.constant U.z U.carry U.cin p ++
  rotateRight U.z ++
  compareLtConst none U.low (U.constant.take U.low.length) U.carry U.cin U.flag ((p+1)/2) ++
  [.X U.flag]

/-- 半倍门列均复用 scratch，不增加量子控制或历史寄存器。 -/
theorem modUnary_counts (U : ModUnaryLayout) (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    toffoliCount (dblInPlace U p)=2*n-1 ∧ measurementCount (dblInPlace U p)=2*n-1 ∧
    toffoliCount (halfInPlace U p)=2*n ∧ measurementCount (halfInPlace U p)=2*n := by
  have hz : U.z.length=n+1 := by simp [ModUnaryLayout.z,hw.low]
  have ht : (U.constant.take U.low.length).length=n := by simp [hw.constant,hw.low]
  have hc : (U.carry.take (U.low.length-1)).length=n-1 := by simp [hw.carry,hw.low]
  have ha := addInPlace_counts U.constant U.z U.carry U.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry,hz])
  have hs := subInPlace_counts U.constant U.z U.carry U.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry,hz])
  have hl := addInPlace_counts (U.constant.take U.low.length) U.low
    (U.carry.take (U.low.length-1)) U.cin (ht.trans hw.low.symm)
    (by rw [hc,hw.low]; omega)
  have hm := compareLt_counts none U.low (U.constant.take U.low.length) U.carry U.cin U.flag
    (hw.low.trans ht.symm) (hw.carry.trans ht.symm)
  simp only [hw.low] at hl hm
  simp only [dblInPlace,halfInPlace,maskedAddConst,compareLtConst,toffoliCount_append,measurementCount_append,
    (rotate_counts U.z).1,(rotate_counts U.z).2.1,(rotate_counts U.z).2.2.1,(rotate_counts U.z).2.2.2,
    (xorConstant_counts _ _).1,(xorConstant_counts _ _).2,(maskedConstant_counts _ _ _).1,
    (maskedConstant_counts _ _ _).2,ha.1,ha.2,hs.1,hs.2,hl.1,hl.2,hm.1,hm.2.1,
    toffoliCount,measurementCount,hw.low,hz,Option.isSome_none,Bool.false_eq_true,if_false,
    List.length_take,hw.constant]
  simp only [Nat.min_eq_left (by omega : n≤n+1)]
  omega

/-- 资源按实际支持计：加倍不触及 mask/flag，减半不触及 mask。 -/
theorem modUnary_wires (U : ModUnaryLayout) (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    wires (dblInPlace U p)=(U.z++U.core.work).toFinset ∧
    wires (halfInPlace U p)=(U.z++U.core.work++[U.flag]).toFinset := by
  have hz : U.z.length=n+1 := by simp [ModUnaryLayout.z,hw.low]
  have hlen : ¬U.z.length<2 := by omega
  have ht : (U.constant.take U.low.length).length=n := by simp [hw.low,hw.constant]
  have hc : (U.carry.take (U.low.length-1)).length=n-1 := by simp [hw.low,hw.carry]
  have ha := addInPlace_wires U.constant U.z U.carry U.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry,hz])
  have hs := subInPlace_wires U.constant U.z U.carry U.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry,hz])
  have hcmp := (compareLt_wires none U.low (U.constant.take U.low.length) U.carry U.cin U.flag
    (hw.low.trans ht.symm) (hw.carry.trans ht.symm)).2 ((p+1)/2)
  have hdend : wires [.X U.high,.CX U.bit U.high]=[U.bit,U.high].toFinset := by
    ext q; simp [wires,Instr.wires]
  have hstart : wires [.CX U.bit U.flag]=[U.bit,U.flag].toFinset := by
    ext q; simp [wires,Instr.wires]
  have hend : wires [.X U.flag]=[U.flag].toFinset := by simp [wires,Instr.wires]
  constructor
  · simp only [dblInPlace,wires_append,(rotate_wires U.z).2,hlen,if_false,hs,hdend]
    ext q
    have hx : q∈wires (xorConstant U.constant p) → q∈U.constant :=
      fun hh => List.mem_toFinset.mp (xorConstant_wires_subset U.constant p hh)
    have hm : q∈wires (maskedAddConst U.high (U.constant.take U.low.length) U.low
        (U.carry.take (U.low.length-1)) U.cin p) →
        q∈U.high::U.cin::U.constant++U.low++U.carry := by
      intro hh
      have ht' := List.mem_toFinset.mp ((maskedConst_wires_subset U.high
        (U.constant.take U.low.length) U.low (U.carry.take (U.low.length-1)) U.cin p
        (ht.trans hw.low.symm) (by rw [hc,hw.low]; omega)).1 hh)
      have tsub := (List.take_sublist U.low.length U.constant).subset
      have csub := (List.take_sublist (U.low.length-1) U.carry).subset
      simp only [List.mem_cons,List.mem_append] at ht' ⊢
      rcases ht' with hh | hh | (hh | hh) | hh
      · exact Or.inl (Or.inl (Or.inl hh))
      · exact Or.inl (Or.inl (Or.inr (Or.inl hh)))
      · exact Or.inl (Or.inl (Or.inr (Or.inr (tsub hh))))
      · exact Or.inl (Or.inr hh)
      · exact Or.inr (csub hh)
    have hb : q=U.bit → q∈U.low := fun he => he.symm ▸ U.bit_mem n hw hn
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,ModUnaryLayout.core,ModAddCoreLayout.work,ModUnaryLayout.z] at hx hm hb ⊢
    clear hw hn hz ht hc ha hs hcmp hdend hstart hend hlen
    aesop
  · simp only [halfInPlace,maskedAddConst,wires_append,ha,hcmp,(rotate_wires U.z).1,
      hlen,if_false,hstart,hend]
    ext q
    have hm : q∈wires (maskedConstant U.flag U.constant p) → q∈U.flag::U.constant :=
      fun hh => List.mem_toFinset.mp (maskedConstant_wires_subset U.flag U.constant p hh)
    have hts : q∈U.constant.take U.low.length → q∈U.constant :=
      fun hh => (List.take_sublist U.low.length U.constant).subset hh
    have hb : q=U.bit → q∈U.low := fun he => he.symm ▸ U.bit_mem n hw hn
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,Option.toList_none,List.nil_append,ModUnaryLayout.core,ModAddCoreLayout.work,
      ModUnaryLayout.z] at hm hb ⊢
    clear hw hn hz ht hc ha hs hcmp hdend hstart hend hlen
    aesop

end ECDSAAdd.Arithmetic
