import ECDSAAdd.Arithmetic.InverseCompactLayout

namespace ECDSAAdd.Arithmetic.InverseLoopLayout

/-- §22的固定借用视图；getD的默认位仅使坏布局上的定义全域成立。 -/
def compactScaling (I : InverseLoopLayout) : InverseScaleLayout where
  a := I.middle.r
  k := I.middle.k
  factor := I.compactBorrow.take 257
  stage := {
    acc := I.scaleLive.take 261
    history := (I.scaleLive.drop 261).take 256
    flag := I.scaleLive.getD 517 I.first.done
    table := (I.compactBorrow.drop 257).take 261
    mask := (I.compactBorrow.drop 518).take 261
    carry := (I.compactBorrow.drop 779).take 260
    cin := I.compactBorrow.getD 1039 I.first.done
    pad := (I.compactBorrow.drop 1040).take 5
    scratch := (I.compactBorrow.drop 1045).take 3 }
  extraScratch := (I.compactBorrow.drop 1048).take 6

theorem compactScaling_widths (I : InverseLoopLayout) (ha : I.middle.r.length=257)
    (hm : I.arithmetic.width=256)
    (hl : I.first.low.length=256) (hk : I.first.counter.width=10) : I.compactScaling.Widths := by
  have hb := I.compactBorrow_length hl hm
  have hh := I.scaleLive_length hl
  have hc : I.middle.k.length=10 := by
    change I.middle.counter.x.length=10
    simpa only [AdderLayout.x,List.length_map,AdderLayout.width] using
      (loopEnd_counter_width I.first I.records.length).trans hk
  refine ⟨ha,hc,?_,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_⟩ <;>
    simp [compactScaling,hb,hh]

private theorem one_slice (B : List Wire) (fallback : Wire) (n : Nat) (hn : n<B.length) :
    (B.drop n).take 1=[B.getD n fallback] := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hi'
    have : i=0 := by simpa using hi'
    subst i
    simp [hn]

theorem compactScaling_work (I : InverseLoopLayout) (hm : I.arithmetic.width=256) (hl : I.first.low.length=256) : I.compactScaling.work=I.compactBorrow.take 1054 := by
  have h := one_slice I.compactBorrow I.first.done 1039 (by rw [I.compactBorrow_length hl hm]; omega)
  simp only [compactScaling,InverseScaleLayout.work,MontStageLayout.work]
  rw [←h]
  simp only [←List.append_assoc,←List.take_add]

theorem compactScaling_live (I : InverseLoopLayout) (hl : I.first.low.length=256) :
    I.compactScaling.live=I.scaleLive := by
  have h := one_slice I.scaleLive I.first.done 517 (by rw [I.scaleLive_length hl]; omega)
  simp only [compactScaling,InverseScaleLayout.live]
  rw [←h,←List.take_add,←List.take_add]
  exact List.take_of_length_le (by rw [I.scaleLive_length hl])


theorem compactScaling_nodup (I : InverseLoopLayout) (hn : I.wires.Nodup)
    (hm : I.arithmetic.width=256) (hl : I.first.low.length=256) : I.compactScaling.wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp (I.compact_inputs_nodup hn) w
  have ht := (List.take_sublist 1054 I.compactBorrow).count_le w
  simp only [InverseScaleLayout.wires,I.compactScaling_work hm hl,I.compactScaling_live hl]
  change (I.middle.r++I.middle.k++I.scaleLive++I.compactBorrow.take 1054).count w≤1
  simp only [List.count_append] at h ⊢
  omega

/-- 原地取负的真实源为r，未触及的目标/mask也在同一B中取互异切片。 -/
def compactNeg (I : InverseLoopLayout) : ModInPlaceLayout :=
  ⟨⟨I.middle.r,(I.compactBorrow.drop 514).take 256,I.compactBorrow.getD 770 I.first.done,
    I.compactBorrow.take 257,(I.compactBorrow.drop 257).take 256,
    I.compactBorrow.getD 513 I.first.done⟩,
    (I.compactBorrow.drop 771).take 257,I.compactBorrow.getD 1028 I.first.done⟩

theorem compactNeg_widths (I : InverseLoopLayout)
    (hm : I.arithmetic.width=256) (hl : I.first.low.length=256) : I.compactNeg.Widths 256 := by
  have hb := I.compactBorrow_length hl hm
  have hr : I.middle.r.length=257 := by
    change (I.middle.data.reg .r).length=257
    rw [middle,loopEnd_data,I.first.data_reg_length,hl]
  exact ⟨⟨hr,by simp [compactNeg,hb],by simp [compactNeg,hb],
    by simp [compactNeg,hb]⟩,by simp [compactNeg,hb]⟩

private theorem compactNeg_target (I : InverseLoopLayout)
    (hm : I.arithmetic.width=256) (hl : I.first.low.length=256) :
    I.compactNeg.z=(I.compactBorrow.drop 514).take 257 := by
  have h := one_slice I.compactBorrow I.first.done 770 (by rw [I.compactBorrow_length hl hm]; omega)
  simp only [compactNeg,ModInPlaceLayout.z,ModAddCoreLayout.z]
  rw [← h]
  have he : I.compactBorrow.drop 770=(I.compactBorrow.drop 514).drop 256 := by rw [List.drop_drop]
  rw [he,←List.take_add]

/-- 取负视图只是r与B前1029位的置换，绝不借入K或记录。 -/
theorem compactNeg_partition (I : InverseLoopLayout)
    (hm : I.arithmetic.width=256) (hl : I.first.low.length=256) :
    I.compactNeg.wires.Perm (I.middle.r++I.compactBorrow.take 1029) := by
  have hc := one_slice I.compactBorrow I.first.done 513 (by rw [I.compactBorrow_length hl hm]; omega)
  have hf := one_slice I.compactBorrow I.first.done 1028 (by rw [I.compactBorrow_length hl hm]; omega)
  have hw : I.compactNeg.toModAddCoreLayout.work=I.compactBorrow.take 514 := by
    simp only [compactNeg,ModAddCoreLayout.work]
    rw [←hc,←List.take_add,←List.take_add]
  have ht : I.compactNeg.mask++[I.compactNeg.flag]=(I.compactBorrow.drop 771).take 258 := by
    simp only [compactNeg]
    rw [←hf]
    have he : I.compactBorrow.drop 1028=(I.compactBorrow.drop 771).drop 257 := by rw [List.drop_drop]
    rw [he,←List.take_add]
  have hall : I.compactBorrow.take 514++(I.compactBorrow.drop 514).take 257++
      (I.compactBorrow.drop 771).take 258=I.compactBorrow.take 1029 := by
    rw [←List.take_add,←List.take_add]
  apply List.perm_iff_count.mpr; intro w
  have he := congrArg (List.count w) hall
  simp only [List.count_append] at he
  simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,I.compactNeg_target hm hl,hw,
    List.append_assoc,ht,List.count_append]
  change (I.middle.r).count w+(((I.compactBorrow.drop 514).take 257).count w+
    ((I.compactBorrow.take 514).count w+((I.compactBorrow.drop 771).take 258).count w))=_
  omega

theorem compactNeg_nodup (I : InverseLoopLayout) (hn : I.wires.Nodup)
    (hm : I.arithmetic.width=256) (hl : I.first.low.length=256) : I.compactNeg.wires.Nodup := by
  apply (I.compactNeg_partition hm hl).nodup_iff.mpr
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp (I.compact_parts_nodup hn) w
  have ht := (List.take_sublist 1029 I.compactBorrow).count_le w
  simp only [List.count_append] at h ⊢
  omega

end ECDSAAdd.Arithmetic.InverseLoopLayout
