import ECDSAAdd.Arithmetic.PointInPlaceLayout

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

theorem inPlaceInverse_perm (L : ControlledPointLayout) (hw : L.Widths) :
    L.inPlaceInverse.wires.Perm (L.core.inverse++L.core.pool) := by
  let I := poolInverse L.core.poolWire L.core.divisor L.core.inverse
  have hp := poolInverse_work_perm L.core.poolWire L.core.divisor L.core.inverse hw.inverse
  have hl := L.core.pool_prefix hw 5699 (by omega)
  have he : L.core.pool.take 5699=L.core.pool := by rw [← hw.pool,List.take_length]
  rw [he] at hl
  rw [hl] at hp
  have hi := I.wires_perm
  have hout := poolInverse_inputs L.core.poolWire L.core.divisor L.core.inverse hw.inverse
  apply List.perm_iff_count.mpr; intro q
  have h := hi.count_eq q
  have hwork := hp.count_eq q
  have ho : I.out=L.core.inverse := hout.2
  simp only [InverseLayout.wires,ho,List.count_append] at h
  change I.inner.wires.count q=(L.core.inverse++L.core.pool).count q
  simp only [List.count_append]
  change I.work.count q=L.core.pool.count q at hwork
  omega

/-- 公共布局中抽出的点、控制、斜率、七个标志与整个求逆布局互异。 -/
theorem inPlace_interfaces_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (PointAddLayout.pointWires L.point++[L.control]++L.inPlaceSlope++L.inPlaceFlags++L.inPlaceInverse.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  have hi := (L.inPlaceInverse_perm hw).count_eq q
  have hs := (List.take_sublist 256 L.core.slope).count_le q
  simp only [inPlaceSlope] at *
  simp only [wires,point,inPlaceFlags,extras,selectors,PointAddLayout.wires,PointAddLayout.work,
    PointAddLayout.words,PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.count_append,List.count_cons,List.count_nil] at h hi ⊢
  omega

theorem inPlaceBit_prefix (L : ControlledPointLayout) (hw : L.Widths) (i : Nat) (hi : i<2603) :
    L.inPlaceBorrow.take i++[L.inPlaceBit i]=L.inPlaceBorrow.take (i+1) := by
  have h : i<L.inPlaceBorrow.length := by rw [L.inPlaceBorrow_length hw]; exact hi
  change L.inPlaceBorrow.take i++[L.inPlaceBorrow.getD i L.control]=_
  rw [List.getD_eq_getElem _ _ h,List.take_add_one,List.getElem?_eq_getElem h]
  rfl

/-- 固定scratch占借用区的连续772位；与前面的存活值不重复。 -/
theorem inPlaceUnary_prefix (L : ControlledPointLayout) (hw : L.Widths)
    (low : List Wire) (high : Wire) (k : Nat) (hk : k+772≤2603) :
    L.inPlaceBorrow.take k++(L.inPlaceUnary low high k).work=L.inPlaceBorrow.take (k+772) := by
  have one := L.inPlaceBit_prefix hw
  simp only [inPlaceUnary,ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work]
  simp only [← List.append_assoc]
  rw [← List.take_add,← List.take_add,show k+257+256=k+513 by omega,one (k+513) (by omega),
    show k+513+1=k+514 by omega,← List.take_add,show k+514+257=k+771 by omega,
    one (k+771) (by omega)]

theorem inPlaceBorrow_count (L : ControlledPointLayout) (q : Wire) :
    L.inPlaceBorrow.count q≤L.inPlaceInverse.wires.count q := by
  rw [L.inPlaceBorrow_eq]
  exact L.inPlaceInverse.idleBorrow_count q

theorem inPlaceOuterCore_sublist (L : ControlledPointLayout) :
    L.inPlaceOuterCoreWires.Sublist L.inPlaceInverse.wires :=
  L.inPlaceInverse.compactCore_sublist.trans (List.sublist_append_left _ _)

theorem compactCore_outer (L : ControlledPointLayout) : L.inPlaceInverse.compactCoreWires ⊆ L.inPlaceOuterCoreWires :=
  List.Subset.refl _

theorem inPlaceDivide_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (c : Wire) (hc : c∈L.inPlaceFlags) :
    (L.inPlaceDivide c L.point.x L.point.y).wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
  have hc' : [c].Sublist L.inPlaceFlags := List.singleton_sublist.mpr hc
  have hh := hc'.count_le q
  simp only [inPlaceDivide,DivideLayout.wires,DivideLayout.work,PointAddLayout.pointWires,
    List.count_append,List.count_cons,List.count_nil] at h hh ⊢
  omega

theorem inPlaceMultiply_borrow (L : ControlledPointLayout) (hw : L.Widths) :
    [L.inPlaceBit 0,L.inPlaceBit 1]++L.inPlaceMultiply.work=L.inPlaceBorrow.take 1829 := by
  have h0 := L.inPlaceBit_prefix hw 0 (by omega)
  have h1 := L.inPlaceBit_prefix hw 1 (by omega)
  have h01 : [L.inPlaceBit 0,L.inPlaceBit 1]=L.inPlaceBorrow.take 2 := by
    rw [← h1,← h0]; rfl
  rw [h01]
  exact borrowedMont_prefix _ _ 2 _ _ _ (by rw [L.inPlaceBorrow_length hw]; omega)

theorem inPlaceMultiply_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    L.inPlaceMultiply.wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
  have ht := (List.take_sublist 1829 L.inPlaceBorrow).count_le q
  rw [← L.inPlaceMultiply_borrow hw] at ht
  have hb := L.inPlaceBorrow_count q
  change (L.inPlaceSlope++[L.inPlaceBit 0]++L.point.x++(L.point.y++[L.inPlaceBit 1])++L.inPlaceMultiply.work).count q≤1
  simp only [PointAddLayout.pointWires,List.count_append,List.count_cons,List.count_nil] at h ht ⊢
  omega

theorem inPlaceConstant_widths (L : ControlledPointLayout) (hw : L.Widths) (r : List Wire)
    (hr : r.length=256) : (L.inPlaceConstant r).Widths 256 := by
  constructor
  · constructor
    all_goals simp only [inPlaceConstant, ModUnaryLayout.core, inPlaceUnary, List.length_take,
      List.length_drop, L.inPlaceBorrow_length hw, hr] <;> omega
  · simp only [inPlaceConstant, inPlaceUnary, List.length_take, List.length_drop,
      L.inPlaceBorrow_length hw]; omega

theorem inPlaceNegate_widths (L : ControlledPointLayout) (hw : L.Widths) : L.inPlaceNegate.Widths 256 := by
  constructor
  · constructor
    all_goals simp only [inPlaceNegate, ModUnaryLayout.core, inPlaceUnary, List.length_take,
      List.length_drop, List.length_append, List.length_cons, List.length_nil,
      L.inPlaceBorrow_length hw, point, hw.inputX] <;> omega
  · simp only [inPlaceNegate, inPlaceUnary, List.length_take, List.length_drop,
      L.inPlaceBorrow_length hw]; omega

theorem inPlaceConstant_borrow (L : ControlledPointLayout) (hw : L.Widths) (r : List Wire) :
    L.inPlaceBorrow.take 257++[L.inPlaceBit 257]++(L.inPlaceConstant r).work=L.inPlaceBorrow.take 1030 := by
  simp only [inPlaceConstant, ModInPlaceLayout.work, ModUnaryLayout.core, ModAddCoreLayout.work]
  rw [L.inPlaceBit_prefix hw 257 (by omega)]
  simpa only [ModUnaryLayout.work, ModUnaryLayout.core, ModAddCoreLayout.work] using
    L.inPlaceUnary_prefix hw r (L.inPlaceBit 257) 258 (by omega)

theorem inPlaceConstant_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (L.inPlaceConstant L.point.x).wires.Nodup ∧ (L.inPlaceConstant L.point.y).wires.Nodup := by
  constructor
  all_goals
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
    have ht := (List.take_sublist 1030 L.inPlaceBorrow).count_le q
    have hb := L.inPlaceBorrow_count q
    rw [← L.inPlaceConstant_borrow hw L.point.x] at ht
    simp only [inPlaceConstant,inPlaceUnary,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
      ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,PointAddLayout.pointWires,
      List.count_append,List.count_cons,List.count_nil] at h ht ⊢
    omega

theorem inPlaceNegate_borrow (L : ControlledPointLayout) (hw : L.Widths) :
    [L.inPlaceBit 0]++L.inPlaceNegate.z++L.inPlaceNegate.work=L.inPlaceBorrow.take 1030 := by
  have hp := L.inPlaceUnary_prefix hw ((L.inPlaceBorrow.drop 1).take 256) (L.inPlaceBit 257) 258 (by omega)
  simp only [ModUnaryLayout.work, ModUnaryLayout.core, ModAddCoreLayout.work, inPlaceUnary] at hp
  simp only [inPlaceNegate, ModInPlaceLayout.z, ModInPlaceLayout.work, ModUnaryLayout.core,
    ModAddCoreLayout.z, ModAddCoreLayout.work, inPlaceUnary]
  have h0 := L.inPlaceBit_prefix hw 0 (by omega)
  simp only [List.take_zero,List.nil_append] at h0
  rw [h0]
  simpa only [← List.append_assoc, ← List.take_add, L.inPlaceBit_prefix hw 257 (by omega)] using hp

theorem inPlaceNegate_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (L.core.generic::L.inPlaceNegate.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
  have ht := (List.take_sublist 1030 L.inPlaceBorrow).count_le q
  rw [← L.inPlaceNegate_borrow hw] at ht
  have hb := L.inPlaceBorrow_count q
  change (L.core.generic::(L.point.x++[L.inPlaceBit 0])++L.inPlaceNegate.z++L.inPlaceNegate.work).count q≤1
  simp only [inPlaceFlags,PointAddLayout.pointWires,List.count_append,List.count_cons,List.count_nil] at h ht ⊢
  omega

theorem inPlacePointZero_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (c t : Wire) (hct : c≠t) (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) :
    (c::t::PointAddLayout.pointWires L.point++L.inPlaceBorrow.take 513).Nodup := by
  have hc' : c∈([L.control]++L.inPlaceFlags) := by
    rcases hc with rfl | hc
    · simp
    · simp [hc]
  have ht' : t∈([L.control]++L.inPlaceFlags) := by simp [ht]
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
  have hb := L.inPlaceBorrow_count q
  have hp := (List.take_sublist 513 L.inPlaceBorrow).count_le q
  have hh := (List.singleton_sublist.mpr hc').count_le q
  have hh' := (List.singleton_sublist.mpr ht').count_le q
  simp only [List.count_append,List.count_cons,List.count_nil] at h hh hh' ⊢
  by_cases hqc : c=q <;> by_cases hqt : t=q
  · exact False.elim (hct (hqc.trans hqt.symm))
  all_goals simp_all only [beq_iff_eq, ↓reduceIte]
  all_goals omega

end ECDSAAdd.Arithmetic.ControlledPointLayout
