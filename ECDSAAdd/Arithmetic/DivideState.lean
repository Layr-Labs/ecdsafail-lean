import ECDSAAdd.Arithmetic.DivideLoad
import ECDSAAdd.Arithmetic.DivideProduct

namespace ECDSAAdd.Arithmetic
namespace DivideLayout

theorem inverse_work_perm (L : DivideLayout) :
    (L.inverseView.out++L.inverseView.work).Perm L.inner.wires := by
  apply List.perm_iff_count.mpr; intro q
  have h := L.inverseView.wires_perm.count_eq q
  change (L.denominator++L.inverseView.out++L.inverseView.work).count q =
    (L.denominator++L.inner.wires).count q at h
  simp only [List.count_append] at h ⊢
  omega

theorem external_disjoint (L : DivideLayout) (hnd : L.wires.Nodup) :
    (L.control :: L.denominator++L.numerator++L.acc).Disjoint L.inner.wires := by
  apply List.disjoint_left.mpr; intro q hq hi
  have h := List.nodup_iff_count.mp hnd q
  have hx := List.count_pos_iff.mpr hq
  have hw := List.count_pos_iff.mpr hi
  simp only [wires,work,List.count_cons,List.count_append] at h hx
  omega

theorem inner_not_acc (L : DivideLayout) (hnd : L.wires.Nodup) {q : Wire} (hq : q∈L.inner.wires) :
    q∉L.acc := by
  intro ha
  exact List.disjoint_left.mp (L.external_disjoint hnd) (by simp [ha]) hq

theorem inverse_used_subset (L : DivideLayout) : L.inner.usedCoreWires ⊆ L.inner.wires := by
  intro q hq
  exact L.inner.usedWires_sublist.subset (List.mem_append_left _ hq)

theorem acc_disjoint_other (L : DivideLayout) (hnd : L.wires.Nodup) :
    (L.control :: L.denominator++L.numerator++L.inner.wires).Disjoint L.acc := by
  apply List.disjoint_left.mpr; intro q hq ha
  have h := List.nodup_iff_count.mp hnd q
  have hx := List.count_pos_iff.mpr hq
  have hw := List.count_pos_iff.mpr ha
  simp only [wires,work,List.count_cons,List.count_append] at h hx
  omega

end DivideLayout

/-- 空工作区同时包含旧XOR输出银行，后者在新除法中始终保持零。 -/
theorem divideZero_iff (L : DivideLayout) (D : Nat) (s : BasisState) :
    InverseValues L.inverseView (inverseValues D 0 0 0 0) s ↔
      regValue L.denominator s=D ∧ regValue L.work s=0 := by
  rw [inverseZero_iff]
  have hz : regValue L.work s=0 ↔
      regValue L.inverseView.out s=0 ∧ regValue L.inverseView.work s=0 := by
    simp only [regValue_zero,DivideLayout.work]
    have hm (q : Wire) := L.inverse_work_perm.mem_iff (a:=q)
    simp only [List.mem_append] at hm
    constructor
    · intro h; exact ⟨fun q hq => h q ((hm q).mp (Or.inl hq)),fun q hq => h q ((hm q).mp (Or.inr hq))⟩
    · rintro ⟨ho,hw⟩ q hq
      rcases (hm q).mpr hq with h|h
      · exact ho q h
      · exact hw q h
  rw [hz]
  exact and_assoc

/-- 外部分母D保持；实际送入求逆的S可为控制假分支使用的1。 -/
theorem divideReady_iff (L : DivideLayout) (hw : L.Widths) (D S : Nat)
    (hS0 : 0<S) (hS : S<2^256) (st : BasisState) :
    InverseValues L.inverseView (inverseValues D p S 1 0) st ↔
      (InverseInitial L.inner p S st ∧ regValue L.inner.out st=0) ∧ regValue L.denominator st=D := by
  have hv := regValue_low_iff L.vLow [L.inner.first.high.v] st S
    (by rw [L.vLow_length hw]; exact hS)
  have vs : L.inner.first.v=L.vLow++[L.inner.first.high.v] := L.inverseView.v_split
  rw [← vs] at hv
  have ho : regValue L.inner.out st=0 ↔
      regValue L.inverseView.out st=0 ∧ regValue (L.inner.out.drop 256) st=0 := by
    conv_lhs => rw [← List.take_append_drop 256 L.inner.out]
    simp only [regValue_zero,List.mem_append,or_imp,forall_and]
    rfl
  rw [inverseValues_iff,InverseInitial.iff L.inner p S hS0,ho,hv]
  have hr : regValue L.inverseView.rest st=0 ↔
      regValue L.inner.first.r st=0 ∧ regValue L.inner.first.k st=0 ∧
      st L.inner.first.done=false ∧ regValue L.inner.work st=0 ∧
      regValue [L.inner.first.high.v] st=0 ∧ regValue (L.inner.out.drop 256) st=0 := by
    simp only [InverseLayout.rest,DivideLayout.inverseView,regValue_zero,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_imp,forall_and,forall_eq]
    tauto
  rw [hr]
  simp only [DivideLayout.inverseView,DivideLayout.vLow] at hv ⊢
  clear hw hS0 hS hv ho hr vs
  grind only

/-- 所有求逆内部位保持时，准备段的历史与逆元断言保持。 -/
theorem divideMiddle_congr (L : DivideLayout) (S A : Nat) (s t : BasisState)
    (h : InverseScaledMiddle L.inner p (kaliskiStep^[512] (kaliskiInit p S)) (kaliskiCodes 512 (kaliskiInit p S)) A s)
    (he : ∀ q∈L.inner.wires, t q=s q) :
    InverseScaledMiddle L.inner p (kaliskiStep^[512] (kaliskiInit p S)) (kaliskiCodes 512 (kaliskiInit p S)) A t := by
  apply InverseScaledMiddle.congr L.inner p _ _ A s t h
  intro q hq
  exact he q (List.mem_append_left _ hq)

theorem divideLoad_wires_subset (L : DivideLayout) (hw : L.Widths) :
    wires (divideLoad L) ⊆ (L.control :: L.inverseView.wires).toFinset ∧
    wires (divideUnload L) ⊆ (L.control :: L.inverseView.wires).toFinset := by
  have hc := copyRegister_wires (some L.control) L.denominator L.vLow
    (hw.inverse.input.trans (L.vLow_length hw).symm)
  have hne : L.denominator.isEmpty=false := by
    cases he : L.denominator with
    | nil => have hh : L.denominator.length=256 := hw.inverse.input; simp [he] at hh
    | cons a as => rfl
  simp only [hne,Bool.false_eq_true,if_false,Option.toList_some,List.singleton_append] at hc
  have mem (q : Wire) (hq : q∈L.inner.wires) : q∈L.inverseView.wires :=
    L.inverseView.wires_perm.mem_iff.mpr (List.mem_append_right _ hq)
  have hv (q : Wire) (hq : q∈L.vLow) := mem q (L.inverse_used_subset (L.vLow_used_subset hq))
  have hvb : L.vBit∈L.vLow := by
    have hh : L.vLow≠[] := by intro he; have hl := L.vLow_length hw; simp [he] at hl
    cases he : L.vLow with
    | nil => exact False.elim (hh he)
    | cons a as => simp [DivideLayout.vBit,he]
  have hu (q : Wire) (hq : q∈wires (xorConstant L.inner.first.u p)) : q∈L.inverseView.wires :=
    mem q (L.inverse_used_subset (L.data_used_subset .u (by decide) (List.mem_toFinset.mp (xorConstant_wires_subset _ _ hq))))
  have hs (q : Wire) (hq : q∈wires (xorConstant L.inner.first.s 1)) : q∈L.inverseView.wires :=
    mem q (L.inverse_used_subset (L.data_used_subset .s (by decide) (List.mem_toFinset.mp (xorConstant_wires_subset _ _ hq))))
  have hd (q : Wire) (hq : q∈L.denominator) : q∈L.inverseView.wires :=
    L.inverseView.wires_perm.mem_iff.mpr (List.mem_append_left _ hq)
  constructor <;> intro q hq
  all_goals
    simp only [divideLoad,divideUnload,wires_append,hc,wires,Instr.wires,Finset.union_empty,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hvb' := hv _ hvb
    have hv' := hv q
    have hu' := hu q
    have hs' := hs q
    have hd' := hd q
    clear hw hc hne mem hv hvb hu hs hd
    grind only

end ECDSAAdd.Arithmetic
