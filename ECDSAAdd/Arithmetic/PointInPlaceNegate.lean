import ECDSAAdd.Arithmetic.PointInPlaceLayoutProof
import ECDSAAdd.Arithmetic.PointInPlaceProgram

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout

private theorem negate_swap (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A T : Nat) (B : Bool) (hA : A<p) (hT : T<p) :
    {{ L.core.generic=B,L.inPlaceNegate.a=A,L.inPlaceNegate.z=T,L.inPlaceNegate.work=0 }}
      swapRegisters L.core.generic L.point.x L.inPlaceNegate.low
    {{ L.core.generic=B,L.inPlaceNegate.a=(if B then T else A),
      L.inPlaceNegate.z=(if B then A else T),L.inPlaceNegate.work=0 }} := by
  have hn := L.inPlaceNegate_nodup hw hnd
  have hm := L.inPlaceNegate_widths hw
  have he : L.inPlaceNegate.a=L.point.x++[L.inPlaceBit 0] := by
    simp only [inPlaceNegate]
  have hswap : (L.core.generic::L.point.x++L.inPlaceNegate.low).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [ModInPlaceLayout.wires,he,ModInPlaceLayout.z,ModAddCoreLayout.z,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have away (q : Wire) (hq : q∈L.core.generic::L.inPlaceBit 0::L.inPlaceNegate.high::L.inPlaceNegate.work) :
      q∉L.point.x ∧ q∉L.inPlaceNegate.low := by
    have h := List.nodup_iff_count.mp hn q
    have hpos := List.count_pos_iff.mpr hq
    simp only [ModInPlaceLayout.wires,he,ModInPlaceLayout.z,ModAddCoreLayout.z,
      List.count_append,List.count_cons,List.count_nil] at h hpos
    constructor
    all_goals intro hq'; have hp := List.count_pos_iff.mpr hq'; omega
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hp : p<2^256 := by norm_num [p]
  have hx := (regValue_low_iff L.point.x [L.inPlaceBit 0] s.basis A
    (by rw [show L.point.x.length=256 from hw.inputX]; exact hA.trans hp)).mp (he ▸ h.1.1.2)
  have ht := (regValue_low_iff L.inPlaceNegate.low [L.inPlaceNegate.high] s.basis T
    (by rw [hm.core.low]; exact hT.trans hp)).mp h.1.2
  obtain ⟨hphase,hframe,hx',ht'⟩ := swapRegisters_correct L.core.generic L.point.x L.inPlaceNegate.low
    (hw.inputX.trans hm.core.low.symm) hswap s m
  have keep (q : Wire) (hq : q∈L.core.generic::L.inPlaceBit 0::L.inPlaceNegate.high::L.inPlaceNegate.work) :=
    hframe q (away q hq).1 (away q hq).2
  have h0 := keep (L.inPlaceBit 0) (by simp)
  have h1 := keep L.inPlaceNegate.high (by simp)
  have high0 := (regValue_zero _ _).mp hx.2 (L.inPlaceBit 0) (by simp)
  have high1 := (regValue_zero _ _).mp ht.2 L.inPlaceNegate.high (by simp)
  refine ⟨hphase,⟨⟨(keep _ (by simp)).trans h.1.1.1,?_⟩,?_⟩,?_⟩
  · rw [he,regValue_append,hx',h.1.1.1,ht.1,hx.1]
    simp [regValue,h0,high0]
  · change regValue (L.inPlaceNegate.low++[L.inPlaceNegate.high]) _=_
    rw [regValue_append,ht',h.1.1.1,hx.1,ht.1]
    simp [regValue,h1,high1]
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.2

/-- 规范取负的三阶段规格；关闭控制时仍执行固定门列并清理临时寄存器。 -/
theorem pointInPlaceNegate_spec (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) :
    {{ L.core.generic=B,L.inPlaceNegate.a=A,L.inPlaceNegate.z=0,L.inPlaceNegate.work=0 }}
      pointInPlaceNegate L
    {{ L.core.generic=B,L.inPlaceNegate.a=(if B then (p-A)%p else A),
      L.inPlaceNegate.z=0,L.inPlaceNegate.work=0 }} := by
  have hp : 0<p := by norm_num [p]
  have hpn : p<2^256 := by norm_num [p]
  have hm := L.inPlaceNegate_widths hw
  have hn := L.inPlaceNegate_nodup hw hnd
  have hs := controlledModSub_spec L.core.generic L.inPlaceNegate 256 p A 0 B hm hn hp hpn
    (Nat.le_of_lt hA) hp
  simp only [Nat.zero_add] at hs
  have ht := negate_swap L hw hnd A (if B then (p-A)%p else 0) B hA
    (by split; exact Nat.mod_lt _ hp; exact hp)
  have ha := controlledModAdd_spec L.core.generic L.inPlaceNegate 256 p
    (if B then (if B then (p-A)%p else 0) else A) (if B then A else (if B then (p-A)%p else 0)) B
    hm hn hp hpn (by cases B <;> simp; omega; exact Nat.le_of_lt (Nat.mod_lt _ hp))
    (by cases B <;> simp; exact hp; exact hA)
  have hresult : (if B then ((if B then A else (if B then (p-A)%p else 0))+
      (if B then (if B then (p-A)%p else 0) else A))%p else (if B then A else (if B then (p-A)%p else 0)))=0 := by
    cases B
    · rfl
    · simp only [if_true]
      rw [Nat.add_mod_mod,Nat.add_sub_of_le (Nat.le_of_lt hA),Nat.mod_self]
  have h := (hs.seq ht).seq ha
  have he : (if B then (if B then (p-A)%p else 0) else A)=(if B then (p-A)%p else A) := by cases B <;> rfl
  rw [hresult] at h
  simpa only [pointInPlaceNegate,he] using h

/-- 取负后仅输入x的低位改变，临时差、高位与所有其它线路恢复。 -/
theorem pointInPlaceNegate_correct (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=A)
    (hc : regValue L.inPlaceBorrow s.basis=0) :
    (run (pointInPlaceNegate L) m s).phase=s.phase ∧
      regValue L.point.x (run (pointInPlaceNegate L) m s).basis=(if B then (p-A)%p else A) ∧
      ∀ q∉L.point.x,(run (pointInPlaceNegate L) m s).basis q=s.basis q := by
  have hm := L.inPlaceNegate_widths hw
  have hp : 0<p := by norm_num [p]
  have hp2 : p<2^256 := by norm_num [p]
  have he : L.inPlaceNegate.a=L.point.x++[L.inPlaceBit 0] := by simp only [inPlaceNegate]
  have hs : [L.inPlaceBit 0]++L.inPlaceNegate.z++L.inPlaceNegate.work ⊆ L.inPlaceBorrow := by
    rw [L.inPlaceNegate_borrow hw]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hc
  have hhigh : s.basis (L.inPlaceBit 0)=false := clean _ (hs (by simp))
  have ha : regValue L.inPlaceNegate.a s.basis=A := by
    rw [he,regValue_append,hx]
    simp [regValue,hhigh]
  have hz : regValue L.inPlaceNegate.z s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_left _ (List.mem_append_right _ hq))))
  have hwork : regValue L.inPlaceNegate.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  obtain ⟨hphase,hv⟩ := pointInPlaceNegate_spec L hw hnd A B hA s m ⟨⟨⟨hb,ha⟩,hz⟩,hwork⟩
  have hvbound : (if B then (p-A)%p else A)<p := by split; exact Nat.mod_lt _ hp; exact hA
  have hlow := (regValue_low_iff L.point.x [L.inPlaceBit 0] (run (pointInPlaceNegate L) m s).basis
    (if B then (p-A)%p else A) (by rw [show L.point.x.length=256 from hw.inputX]; exact hvbound.trans hp2)).mp
    (he ▸ hv.1.1.2)
  refine ⟨hphase,hlow.1,?_⟩
  intro q hq
  by_cases hqb : q=L.core.generic
  · subst q; exact hv.1.1.1.trans hb.symm
  by_cases hq0 : q=L.inPlaceBit 0
  · subst q; exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans hhigh.symm
  by_cases hqz : q∈L.inPlaceNegate.z
  · exact (regValue_eq_iff _ _ _).mp (hv.1.2.trans hz.symm) q hqz
  by_cases hqw : q∈L.inPlaceNegate.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.trans hwork.symm) q hqw
  have hqa : q∉L.inPlaceNegate.a := by rw [he]; simp [hq,hq0]
  have subset (M : ModInPlaceLayout) : M.maskedCore.wires ⊆ M.z++M.work := by
    intro w hh
    simp only [ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.z,
      ModAddCoreLayout.work,ModInPlaceLayout.z,ModInPlaceLayout.work,List.mem_append,List.mem_cons] at hh ⊢
    grind only
  have hmask : q∉L.inPlaceNegate.maskedCore.wires := by
    intro hh
    have hh' := subset L.inPlaceNegate hh
    simp only [List.mem_append] at hh'
    exact hh'.elim hqz hqw
  have hqlow : q∉L.inPlaceNegate.low := by
    intro h; exact hqz (by simp [ModInPlaceLayout.z,ModAddCoreLayout.z,h])
  have hswap : q∉wires (swapRegisters L.core.generic L.point.x L.inPlaceNegate.low) := by
    intro h
    have hh := swapRegisters_wires L.core.generic L.point.x L.inPlaceNegate.low (hw.inputX.trans hm.core.low.symm) h
    simp [hqb,hq,hqlow] at hh
  apply run_preserves_outside
  simp only [pointInPlaceNegate,wires_append,controlledModSub_wires _ _ 256 p hm (by omega),
    controlledModAdd_wires _ _ 256 p hm (by omega),Finset.mem_union,List.mem_toFinset,List.mem_cons,
    List.mem_append,not_or]
  have htake : q∉L.inPlaceNegate.a.take 256 := fun h => hqa ((List.take_sublist _ _).subset h)
  simp only [hqb,hqa,hmask,hswap,htake,not_false_eq_true,and_self]

end ECDSAAdd.Arithmetic
