import ECDSAAdd.Arithmetic.Divide

namespace ECDSAAdd.Arithmetic.DivideLayout

/-- 输出高位与乘法工作区恰为借用区前1828位。 -/
theorem multiply_borrow (L : DivideLayout) (hw : L.Widths) :
    [L.borrowedBit 0] ++ L.multiply.work = L.borrow.take 1828 := by
  have h := borrowedMont_prefix L.borrow L.inner.first.done 1 L.inner.middle.r L.numerator
    (L.acc++[L.borrowedBit 0]) (by rw [L.borrow_length hw])
  have he : L.borrow.take 1=[L.borrowedBit 0] := by
    have hh : 0<L.borrow.length := by rw [L.borrow_length hw]; omega
    simp [borrowedBit,List.take_add_one,List.getElem?_eq_getElem hh]
  rw [he] at h
  exact h

theorem inner_nodup (L : DivideLayout) (hnd : L.wires.Nodup) : L.inner.wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  simp only [wires,work,List.count_cons,List.count_append] at h
  omega

theorem multiply_nodup (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (L.control :: L.multiply.wires).Nodup := by
  have hrb : (L.inner.middle.r++L.borrow).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inner.compact_parts_nodup (L.inner_nodup hnd)) q
    simp only [borrow,List.count_append] at h ⊢
    omega
  have hs : L.inner.middle.r++L.borrow ⊆ L.inner.wires := by
    intro q hq
    have hi : q∈L.inner.idleBorrow := L.inner.compact_partition.mem_iff.mp (by
      rcases List.mem_append.mp hq with hq|hq
      · exact List.mem_append_left _ (List.mem_append_left _ hq)
      · exact List.mem_append_right _ hq)
    exact L.inner.idleBorrow_subset_wires hi
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  have hb := List.Sublist.count_le q (List.take_sublist 1828 L.borrow)
  rw [← L.multiply_borrow hw] at hb
  have hc : (L.inner.middle.r++L.borrow).count q ≤ L.inner.wires.count q := by
    by_cases hq : q∈L.inner.middle.r++L.borrow
    · have h1 := List.nodup_iff_count.mp hrb q
      have h2 := List.count_pos_iff.mpr (hs hq)
      omega
    · simp [List.count_eq_zero.mpr hq]
  simp only [wires,work,List.count_cons,List.count_append] at h
  simp only [List.count_append,List.count_cons,List.count_nil] at hb hc
  change (L.control :: L.inner.middle.r ++ L.numerator ++ (L.acc++[L.borrowedBit 0]) ++ L.multiply.work).count q ≤ 1
  simp only [List.count_cons,List.count_append,List.count_nil]
  omega

theorem inverse_nodup (L : DivideLayout) (hnd : L.wires.Nodup) :
    (L.control :: L.inverseView.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  have hp := L.inverseView.wires_perm.count_eq q
  change (L.control :: L.inverseView.wires).count q ≤ 1
  simp only [wires,work,List.count_cons,List.count_append] at h ⊢
  change L.inverseView.wires.count q = (L.denominator++L.inner.wires).count q at hp
  simp only [List.count_append] at hp
  omega

end ECDSAAdd.Arithmetic.DivideLayout
