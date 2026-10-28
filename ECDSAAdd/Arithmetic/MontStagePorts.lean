import ECDSAAdd.Arithmetic.MontHistory

namespace ECDSAAdd.Arithmetic.MontStageLayout

theorem record_sublist (L : MontStageLayout) (i : Nat) : (L.record i).Sublist L.history :=
  (List.take_sublist 4 (L.history.drop (4*i))).trans (List.drop_sublist (4*i) L.history)

theorem record_length (L : MontStageLayout) (hw : L.Widths) (i : Nat) (hi : i<64) :
    (L.record i).length=4 := by simp only [record,List.length_take,List.length_drop,hw.history]; omega

theorem digit_nodup (L : MontStageLayout) (x y : List Wire) (hnd : (x++y++L.wires).Nodup) :
    (L.cin::(x++y++L.pad++L.mask++L.acc++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hnd w
  simp only [wires,work,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega

theorem reduce_nodup (L : MontStageLayout) (x y : List Wire) (i : Nat)
    (hnd : (x++y++L.wires).Nodup) :
    (L.cin::(L.record i++L.table++L.acc++L.carry++L.scratch)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hnd w
  have hr := (L.record_sublist i).count_le w
  simp only [wires,work,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega

theorem normalize_nodup (L : MontStageLayout) (x y : List Wire) (hnd : (x++y++L.wires).Nodup) :
    (L.flag::L.cin::(L.table++L.acc++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hnd w
  simp only [wires,work,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega

/-- 控制输入和临时工作区位于累加器与记录带以外。 -/
theorem inputs_disjoint (L : MontStageLayout) (x y : List Wire) (hnd : (x++y++L.wires).Nodup) :
    (x++y++[L.flag]++L.work).Disjoint (L.acc++L.history) := by
  apply List.disjoint_left.mpr; intro w hw hh
  have h := List.nodup_iff_count.mp hnd w
  have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr hh
  simp only [wires,work,List.count_cons,List.count_append,List.count_nil] at h h1 h2; omega

theorem acc_disjoint (L : MontStageLayout) (x y : List Wire) (hnd : (x++y++L.wires).Nodup) :
    (x++y++L.history++[L.flag]++L.work).Disjoint L.acc := by
  apply List.disjoint_left.mpr; intro w hw hh
  have h := List.nodup_iff_count.mp hnd w
  have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr hh
  simp only [wires,work,List.count_cons,List.count_append,List.count_nil] at h h1; omega

theorem history_nodup (L : MontStageLayout) (x y : List Wire) (hnd : (x++y++L.wires).Nodup) : L.history.Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hnd w
  simp only [wires,List.count_append] at h; omega

theorem work_clean (L : MontStageLayout) (s : BasisState) (h : regValue L.work s=0)
    (r : List Wire) (hr : r⊆L.work) : regValue r s=0 :=
  (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp h w (hr hw))

theorem cin_clean (L : MontStageLayout) (s : BasisState) (h : regValue L.work s=0) : s L.cin=false :=
  (regValue_zero _ _).mp h L.cin (by simp [work])


/-- 准备/恢复只允许 acc、history、flag 改变。 -/
theorem stable_disjoint (L : MontStageLayout) (x y : List Wire) (hnd : (x++y++L.wires).Nodup) :
    (x++y++L.work).Disjoint (L.acc++L.history++[L.flag]) := by
  apply List.disjoint_left.mpr; intro w hw hh
  have h := List.nodup_iff_count.mp hnd w
  have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr hh
  simp only [wires,work,List.count_cons,List.count_append,List.count_nil] at h h1 h2; omega

end ECDSAAdd.Arithmetic.MontStageLayout
