import ECDSAAdd.Arithmetic.InverseScaleBorrow
import ECDSAAdd.Arithmetic.NegativeEven

namespace ECDSAAdd.Arithmetic
namespace InverseLoopLayout

/-- 原银行只保留实际借用的804位，编号不变。 -/
def compactBank (I : InverseLoopLayout) : List Wire := I.arithmetic.wires.take 804

/-- 正循环结束后清u/s常量，v已经零；排除r和518位缩放历史。 -/
def compactBorrow (I : InverseLoopLayout) : List Wire :=
  I.middle.u++I.middle.v++I.middle.s++(I.middle.data.reg .zero).drop 4++I.compactBank

/-- 求逆未存活时的外层点运算工作区；完全不借记录带。 -/
def idleBorrow (I : InverseLoopLayout) : List Wire :=
  I.middle.u++I.middle.v++I.middle.r++I.middle.s++I.middle.data.reg .y++
    I.middle.data.reg .carry++I.middle.data.reg .zero++I.compactBank

/-- D1目标支持列表；第一阶段记录保持两位版本。 -/
def compactCoreWires (I : InverseLoopLayout) : List Wire :=
  I.first.usedRecordTapeWires I.records++I.compactBank

private theorem data_length (I : InverseLoopLayout) (hl : I.first.low.length=256) (f : RoundField) :
    (I.middle.data.reg f).length=257 := by
  rw [middle,loopEnd_data,I.first.data_reg_length,hl]

private theorem bank_length (I : InverseLoopLayout) (hm : I.arithmetic.width=256) :
    I.compactBank.length=804 := by
  have count (bs : List ModBit) : (bs.flatMap ModBit.all).length=8*bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [ModBit.all,ih]; omega
  simp only [compactBank,List.length_take,ModLayout.wires,List.length_cons,List.length_nil,
    count,ModLayout.bits,List.length_append]
  change min 804 (8*(I.arithmetic.low.length+1)+2)=804
  change I.arithmetic.low.length=256 at hm
  rw [hm]
  rfl

theorem compactBorrow_length (I : InverseLoopLayout) (hl : I.first.low.length=256)
    (hm : I.arithmetic.width=256) : I.compactBorrow.length=1828 := by
  simp [compactBorrow,KaliskiRoundLayout.u,KaliskiRoundLayout.v,KaliskiRoundLayout.s,
    RoundDataLayout.u,RoundDataLayout.v,RoundDataLayout.s,I.data_length hl,I.bank_length hm]

theorem idleBorrow_length (I : InverseLoopLayout) (hl : I.first.low.length=256)
    (hm : I.arithmetic.width=256) : I.idleBorrow.length=2603 := by
  simp [idleBorrow,KaliskiRoundLayout.u,KaliskiRoundLayout.v,KaliskiRoundLayout.r,KaliskiRoundLayout.s,
    RoundDataLayout.u,RoundDataLayout.v,RoundDataLayout.r,RoundDataLayout.s,I.data_length hl,I.bank_length hm]

/-- 逐位列出七个实际字段，不包括旧out分配字。 -/
private theorem data_count (D : RoundDataLayout) (w : Wire) :
    (D.u++D.v++D.r++D.s++D.reg .y++D.reg .carry++D.reg .zero).count w ≤ D.wires.count w := by
  rcases D with ⟨bs,cin⟩
  induction bs with
  | nil => simp [RoundDataLayout.u,RoundDataLayout.v,RoundDataLayout.r,RoundDataLayout.s,
      RoundDataLayout.reg,RoundDataLayout.wires]
  | cons b bs ih =>
    simp only [RoundDataLayout.u,RoundDataLayout.v,RoundDataLayout.r,RoundDataLayout.s,
      RoundDataLayout.reg,RoundDataLayout.wires,List.map_cons,List.flatMap_cons,
      List.count_append,List.count_cons,RoundBit.get,RoundBit.wires,List.count_nil] at ih ⊢
    omega

/-- r、存活历史与借用区构成同一组数据线，zero的低4/高253位不重叠。 -/
theorem compact_partition (I : InverseLoopLayout) :
    (I.middle.r++I.scaleLive++I.compactBorrow).Perm I.idleBorrow := by
  apply List.perm_iff_count.mpr; intro w
  have hz := congrArg (List.count w) (List.take_append_drop 4 (I.middle.data.reg .zero))
  simp only [List.count_append] at hz
  simp only [compactBorrow,idleBorrow,scaleLive,List.count_append]
  omega

private theorem idle_count (I : InverseLoopLayout) (w : Wire) :
    I.idleBorrow.count w ≤ I.middle.data.wires.count w+I.arithmetic.wires.count w := by
  have hd := data_count I.middle.data w
  have hb := (List.take_sublist 804 I.arithmetic.wires).count_le w
  simp only [idleBorrow,compactBank,KaliskiRoundLayout.u,KaliskiRoundLayout.v,
    KaliskiRoundLayout.r,KaliskiRoundLayout.s,List.count_append] at *
  omega

theorem idleBorrow_count (I : InverseLoopLayout) (w : Wire) :
    I.idleBorrow.count w≤I.wires.count w := by
  have hp := I.middle_perm.count_eq w
  have hi := I.idle_count w
  simp only [wires,extra,KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,
    List.count_append,List.count_cons,List.count_nil] at hp ⊢
  omega

theorem idleBorrow_nodup (I : InverseLoopLayout) (hn : I.wires.Nodup) : I.idleBorrow.Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  have hp := I.middle_perm.count_eq w
  have hi := I.idle_count w
  simp only [wires,extra,KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,
    List.count_append,List.count_cons,List.count_nil] at hh hp
  omega

theorem compact_parts_nodup (I : InverseLoopLayout) (hn : I.wires.Nodup) :
    (I.middle.r++I.scaleLive++I.compactBorrow).Nodup :=
  I.compact_partition.nodup_iff.mpr (I.idleBorrow_nodup hn)

private theorem counter_count (L : AdderLayout) (w : Wire) : L.x.count w≤L.wires.count w := by
  rcases L with ⟨bs,cin⟩
  have h : (bs.map AddBit.x).count w≤(addWires bs).count w := by
    induction bs with
    | nil => simp [addWires]
    | cons b bs ih =>
      simp only [List.map_cons,addWires,List.count_cons] at *
      omega
  simp only [AdderLayout.x,AdderLayout.wires,List.count_cons]
  omega

/-- 加入K后仍全局互异，供缩放查表与所有中段组合使用。 -/
theorem compact_inputs_nodup (I : InverseLoopLayout) (hn : I.wires.Nodup) :
    (I.middle.k++I.middle.r++I.scaleLive++I.compactBorrow).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  have hp := I.middle_perm.count_eq w
  have hi := I.idle_count w
  have he := I.compact_partition.count_eq w
  have hk := counter_count I.middle.counter w
  simp only [wires,extra,KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,
    KaliskiRoundLayout.k,List.count_append,List.count_cons,List.count_nil] at hh hp he ⊢
  omega

/-- 外层借用只使用原求逆布局已有线路，便于传递全局frame。 -/
theorem idleBorrow_subset_wires (I : InverseLoopLayout) : I.idleBorrow⊆I.wires := by
  intro w hw
  have hh := List.count_pos_iff.mpr hw
  have hi := I.idle_count w
  have hp := I.middle_perm.count_eq w
  apply List.count_pos_iff.mp
  simp only [wires,extra,KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,
    List.count_append,List.count_cons,List.count_nil] at hp ⊢
  omega

theorem compactCore_nodup (I : InverseLoopLayout) (hn : I.wires.Nodup) : I.compactCoreWires.Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  have hf := (I.first.usedRecordTapeWires_sublist I.records).count_le w
  have hb := (List.take_sublist 804 I.arithmetic.wires).count_le w
  simp only [compactCoreWires,compactBank,wires,extra,List.count_append] at hh ⊢
  omega

/-- 紧缩核心支持列表的长度；程序等式由后续组合定理给出。 -/
theorem compactCore_length (I : InverseLoopLayout) (hn : I.records.length=512)
    (hk : I.first.counter.width=10) (hl : I.first.low.length=256) (hm : I.arithmetic.width=256) :
    I.compactCoreWires.length=3162 := by
  have recs : (oneBitRecordWires I.records).length=513 := by
    cases he : I.records with
    | nil => simp [he] at hn
    | cons r rs => simp [oneBitRecordWires]; simp [he] at hn; omega
  have bits (bs : List RoundBit) : (bs.flatMap RoundBit.usedWires).length=7*bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [RoundBit.usedWires,ih]; omega
  have hc : I.first.counter.bits.length=10 := hk
  simp only [compactCoreWires,KaliskiRoundLayout.usedRecordTapeWires,KaliskiRoundLayout.usedSharedWires,
    RoundDataLayout.usedWires,AdderLayout.wires,List.length_append,List.length_cons,List.length_nil,
    recs,bits,addWires_length,I.bank_length hm,hc]
  simp [KaliskiRoundLayout.data,hl]

theorem compact_middle_perm (I : InverseLoopLayout) :
    I.middle.usedSharedWires.Perm I.first.usedSharedWires := by
  apply List.perm_iff_count.mpr; intro w
  have hp := I.middle_perm.count_eq w
  have hd : I.middle.data=I.first.data := loopEnd_data _ _
  simp only [KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,KaliskiRoundLayout.usedSharedWires,
    List.count_append,List.count_cons,List.count_nil,hd] at hp ⊢
  omega

theorem compact_reg_mem (I : InverseLoopLayout) (f : RoundField) (hf : f≠.out)
    {w : Wire} (hw : w∈I.middle.data.reg f) : w∈I.compactCoreWires := by
  have hd := I.middle.data.reg_used_mem f hf hw
  have hm : w∈I.middle.usedSharedWires := by simp [KaliskiRoundLayout.usedSharedWires,hd]
  have hh := I.compact_middle_perm.mem_iff.mp hm
  exact List.mem_append_left _ (List.mem_append_right _ hh)

/-- 外层借用P包含于D1支持目标，旧记录swap尾部从未被借回。 -/
theorem idleBorrow_subset (I : InverseLoopLayout) : I.idleBorrow⊆I.compactCoreWires := by
  intro w hw
  simp only [idleBorrow,List.mem_append,or_assoc,KaliskiRoundLayout.u,KaliskiRoundLayout.v,
    KaliskiRoundLayout.r,KaliskiRoundLayout.s,RoundDataLayout.u,RoundDataLayout.v,
    RoundDataLayout.r,RoundDataLayout.s] at hw
  rcases hw with hu|hv|hr|hs|hy|hc|hz|hb
  · exact I.compact_reg_mem .u (by decide) hu
  · exact I.compact_reg_mem .v (by decide) hv
  · exact I.compact_reg_mem .r (by decide) hr
  · exact I.compact_reg_mem .s (by decide) hs
  · exact I.compact_reg_mem .y (by decide) hy
  · exact I.compact_reg_mem .carry (by decide) hc
  · exact I.compact_reg_mem .zero (by decide) hz
  · exact List.mem_append_right _ hb

theorem compactBorrow_subset (I : InverseLoopLayout) : I.compactBorrow⊆I.compactCoreWires := by
  intro w hw
  exact I.idleBorrow_subset (I.compact_partition.mem_iff.mp (List.mem_append_right _ hw))

end InverseLoopLayout
end ECDSAAdd.Arithmetic
