import ECDSAAdd.Arithmetic.SquareReduceProof
import ECDSAAdd.Arithmetic.SquareNormalizeProof

namespace ECDSAAdd.Arithmetic

/-- 各折叠阶段的显式值：q、b、f 是必须保留的记录，借用区始终为零。 -/
structure SquareReduceValues (L : SquareReduceLayout) (lo hi v q : Nat) (b f : Bool)
    (s : BasisState) : Prop where
  low : regValue L.low s=lo
  high : regValue L.high s=hi
  value : regValue L.value s=v
  quotient : regValue L.quotient s=q
  pad : regValue L.pad s=0
  mask : regValue L.mask s=0
  carry : regValue L.carry s=0
  cin : s L.cin=false
  bit : s L.b=b
  flag : s L.flag=f

namespace SquareReduceValues

variable {L : SquareReduceLayout} {lo hi v q : Nat} {b f : Bool} {s t : BasisState}

theorem work_zero (h : SquareReduceValues L lo hi v q b f s) :
    regValue (L.pad++L.carry) s=0 := by simp [regValue_append,h.pad,h.carry]

theorem r_read (h : SquareReduceValues L lo hi v q b f s) (hw : L.Widths) :
    regValue L.r s=v+SquareReduction.B*q := by
  rw [←L.value_quotient,regValue_append,L.value_length hw,h.value,h.quotient]
  rfl

theorem extended_read (h : SquareReduceValues L lo hi v q b f s) (hw : L.Widths) :
    regValue L.extended s=v+SquareReduction.B*b.toNat := by
  simp only [SquareReduceLayout.extended,regValue_append,L.value_length hw,h.value]
  cases b <;> simp [regValue,h.bit,SquareReduction.B]

/-- 整个289位目标改变时，所有其它寄存器由目标外保持推出。 -/
theorem of_r_frame (h : SquareReduceValues L lo hi v q b f s) (hw : L.Widths)
    (hn : L.wires.Nodup) (U : Nat) (ht : SquareFrame L.r s U t) :
    SquareReduceValues L lo hi (U%SquareReduction.B) (U/SquareReduction.B) b f t := by
  have outside (w : Wire) (hm : w∈L.low++L.high++L.pad++L.mask++L.carry++[L.cin,L.b,L.flag]) :
      w∉L.r := by
    intro hr
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h1 h2
    omega
  have keep (r : List Wire) (hr : r⊆L.low++L.high++L.pad++L.mask++L.carry++[L.cin,L.b,L.flag]) :
      regValue r t=regValue r s := regValue_congr _ _ _ (fun w hm => ht.2 w (outside w (hr hm)))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hm; simp [hm])).trans h.low
  · exact (keep _ (by intro w hm; simp [hm])).trans h.high
  · rw [L.value_read hw,ht.1]
  · rw [L.quotient_read hw,ht.1]
  · exact (keep _ (by intro w hm; simp [hm])).trans h.pad
  · exact (keep _ (by intro w hm; simp [hm])).trans h.mask
  · exact (keep _ (by intro w hm; simp [hm])).trans h.carry
  · exact (ht.2 _ (outside _ (by simp))).trans h.cin
  · exact (ht.2 _ (outside _ (by simp))).trans h.bit
  · exact (ht.2 _ (outside _ (by simp))).trans h.flag

/-- 第二折叠改变低256位和独立 b，商 q 逐位保持。 -/
theorem of_extended_frame (h : SquareReduceValues L lo hi v q b f s) (hw : L.Widths)
    (hn : L.wires.Nodup) (V : Nat) (ht : SquareFrame L.extended s V t) :
    SquareReduceValues L lo hi (V%SquareReduction.B) q (decide (SquareReduction.B≤V)) f t := by
  have hc (w : Wire) := congrArg (List.count w) L.value_quotient
  simp only [List.count_append] at hc
  have outside (w : Wire) (hm : w∈L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.flag]) :
      w∉L.extended := by
    intro hr
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    have he := hc w
    simp only [SquareReduceLayout.wires,SquareReduceLayout.extended,List.count_append,
      List.count_cons,List.count_nil] at h1 h2 h3
    omega
  have keep (r : List Wire) (hr : r⊆L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.flag]) :
      regValue r t=regValue r s := regValue_congr _ _ _ (fun w hm => ht.2 w (outside w (hr hm)))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hm; simp [hm])).trans h.low
  · exact (keep _ (by intro w hm; simp [hm])).trans h.high
  · rw [L.extended_low hw,ht.1]
  · exact (keep _ (by intro w hm; simp [hm])).trans h.quotient
  · exact (keep _ (by intro w hm; simp [hm])).trans h.pad
  · exact (keep _ (by intro w hm; simp [hm])).trans h.mask
  · exact (keep _ (by intro w hm; simp [hm])).trans h.carry
  · exact (ht.2 _ (outside _ (by simp))).trans h.cin
  · apply Bool.eq_iff_iff.mpr
    have he : regValue (L.value++[L.b]) t=V := ht.1
    simpa [L.value_length hw,SquareReduction.B,he] using
      regValue_highBit L.value L.b t
  · exact (ht.2 _ (outside _ (by simp))).trans h.flag

/-- 第三折叠仅更新低256位，保留 q、b、f。 -/
theorem of_value_frame (h : SquareReduceValues L lo hi v q b f s)
    (hn : L.wires.Nodup) (V : Nat) (ht : SquareFrame L.value s V t) :
    SquareReduceValues L lo hi V q b f t := by
  have hc (w : Wire) := congrArg (List.count w) L.value_quotient
  simp only [List.count_append] at hc
  have outside (w : Wire) (hm : w∈L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.b,L.flag]) :
      w∉L.value := by
    intro hr
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    have he := hc w
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h1 h2
    omega
  have keep (r : List Wire) (hr : r⊆L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.b,L.flag]) :
      regValue r t=regValue r s := regValue_congr _ _ _ (fun w hm => ht.2 w (outside w (hr hm)))
  refine ⟨?_,?_,ht.1,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hm; simp [hm])).trans h.low
  · exact (keep _ (by intro w hm; simp [hm])).trans h.high
  · exact (keep _ (by intro w hm; simp [hm])).trans h.quotient
  · exact (keep _ (by intro w hm; simp [hm])).trans h.pad
  · exact (keep _ (by intro w hm; simp [hm])).trans h.mask
  · exact (keep _ (by intro w hm; simp [hm])).trans h.carry
  · exact (ht.2 _ (outside _ (by simp))).trans h.cin
  · exact (ht.2 _ (outside _ (by simp))).trans h.bit
  · exact (ht.2 _ (outside _ (by simp))).trans h.flag

theorem of_norm_frame (h : SquareReduceValues L lo hi v q b f s)
    (hn : L.wires.Nodup) (V : Nat) (F : Bool) (ht : SquareNormFrame L s V F t) :
    SquareReduceValues L lo hi V q b F t := by
  have hc (w : Wire) := congrArg (List.count w) L.value_quotient
  simp only [List.count_append] at hc
  have outside (w : Wire) (hm : w∈L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.b]) :
      w∉L.value++[L.flag] := by
    intro hr
    have h1 := List.nodup_iff_count.mp hn w
    have h2 := List.count_pos_iff.mpr hm
    have h3 := List.count_pos_iff.mpr hr
    simp only [List.count_append,List.count_cons,List.count_nil] at h3
    have he := hc w
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h1 h2
    omega
  have keep (r : List Wire) (hr : r⊆L.low++L.high++L.quotient++L.pad++L.mask++L.carry++[L.cin,L.b]) :
      regValue r t=regValue r s := regValue_congr _ _ _ (fun w hm => ht.2.2 w (outside w (hr hm)))
  refine ⟨?_,?_,ht.1,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by intro w hm; simp [hm])).trans h.low
  · exact (keep _ (by intro w hm; simp [hm])).trans h.high
  · exact (keep _ (by intro w hm; simp [hm])).trans h.quotient
  · exact (keep _ (by intro w hm; simp [hm])).trans h.pad
  · exact (keep _ (by intro w hm; simp [hm])).trans h.mask
  · exact (keep _ (by intro w hm; simp [hm])).trans h.carry
  · exact (ht.2.2 _ (outside _ (by simp))).trans h.cin
  · exact (ht.2.2 _ (outside _ (by simp))).trans h.bit
  · exact ht.2.1

end SquareReduceValues
end ECDSAAdd.Arithmetic
