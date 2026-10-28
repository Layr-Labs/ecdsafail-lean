import ECDSAAdd.Arithmetic.ControlledUnaryState

namespace ECDSAAdd.Arithmetic

/-- 加回后的借位单独存于高位，flag 仍为空。 -/
def DoubleValues (c : Wire) (U : ModUnaryLayout) (C : Bool) (R : Nat) (B : Bool)
    (s : BasisState) : Prop :=
  s c=C ∧ regValue U.mask s=0 ∧ regValue U.low s=R ∧ s U.high=B ∧
    regValue U.core.work s=0 ∧ s U.flag=false

namespace DoubleValues

theorem addback (c : Wire) (U : ModUnaryLayout) (n p D R : Nat) (C B : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hn : 0<n) (hp : p<2^n)
    (hb : (2^n≤D ↔ B=true))
    (hr : (D%2^n+(if B then p else 0))%2^n=R) :
    Triple (UnaryValues c U C D false)
      (maskedAddConst U.high (U.constant.take U.low.length) U.low
        (U.carry.take (U.low.length-1)) U.cin p)
      (DoubleValues c U C R B) := by
  have ht : (U.constant.take U.low.length).length=U.low.length := by simp [hw.low,hw.constant]
  have hcarry : (U.carry.take (U.low.length-1)).length+1=U.low.length := by
    simp only [List.length_take,hw.carry,hw.low]; omega
  intro s m h
  rcases h with ⟨hc,hz,hk,hm,hf⟩
  have hl : regValue U.low s.basis=D%2^n := by
    rw [regValue_low U.low U.high,← ModUnaryLayout.z,hz,hw.low]
  have hbit : s.basis U.high=B := by
    have hh := regValue_highBit U.low U.high s.basis
    rw [← ModUnaryLayout.z,hz,hw.low] at hh
    cases he : s.basis U.high <;> cases hB : B <;> simp_all
    omega
  obtain ⟨phase,v⟩ := modAddCore_addback U.core n 0 (D%2^n) p B (U.core_widths n hw)
    (U.core_nodup (List.nodup_cons.mp hnd).2) hn hp s m ⟨⟨⟨hm,hl⟩,hbit⟩,hk⟩
  simp only [Holds.holds] at v
  have away (q : Wire) (hq : q=c ∨ q=U.flag) :
      q∉wires (maskedAddConst U.high (U.constant.take U.low.length) U.low
        (U.carry.take (U.low.length-1)) U.cin p) := by
    intro hh
    have hmem := List.mem_toFinset.mp ((maskedConst_wires_subset U.high
      (U.constant.take U.low.length) U.low (U.carry.take (U.low.length-1)) U.cin p ht hcarry).1 hh)
    have h1 := List.count_pos_iff.mpr hmem
    have h2 := List.nodup_iff_count.mp hnd q
    have ht' := (List.take_sublist U.low.length U.constant).count_le q
    have hc' := (List.take_sublist (U.low.length-1) U.carry).count_le q
    rcases hq with rfl | rfl <;>
      simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,
        ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h1 h2 <;> omega
  refine ⟨phase,(run_preserves_outside _ _ _ c (away c (Or.inl rfl))).trans hc,
    v.1.1.1,?_,v.1.2,v.2,(run_preserves_outside _ _ _ U.flag (away U.flag (Or.inr rfl))).trans hf⟩
  exact v.1.1.2.trans hr

theorem finish (c : Wire) (U : ModUnaryLayout) (n R : Nat) (C B : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hn : 0<n)
    (hB : B=(C && !decide (R%2=1))) :
    Triple (DoubleValues c U C R B) [.CX c U.high,.CCX c U.bit U.high]
      (UnaryValues c U C R false) := by
  have away (q : Wire) (hq : q∈c::U.mask++U.low++U.core.work++[U.flag]) : q≠U.high := by
    intro hh; subst q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.nodup_iff_count.mp hnd U.high
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,ModUnaryLayout.core,
      ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h1 h2
    omega
  have hcne : c≠U.high := away c (by simp)
  have hbne : U.bit≠U.high := away U.bit (by simp [U.bit_mem n hw hn])
  intro s m h
  rcases h with ⟨hc,hm,hl,hb,hk,hf⟩
  have hbit : s.basis U.bit=decide (R%2=1) := by
    have hv : (s.basis U.bit).toNat=R%2 := by
      cases he : U.low with
      | nil => have hh := hw.low; simp [he] at hh; omega
      | cons a as =>
        simp only [ModUnaryLayout.bit,he,List.headD_cons]
        rw [← hl,he]
        simp [regValue,Bool.toNat]; cases s.basis a <;> simp
    cases he : s.basis U.bit <;> simp [he] at hv ⊢ <;> omega
  have hh : (run [.CX c U.high,.CCX c U.bit U.high] m s).basis U.high=false := by
    simp only [run,writeBit,Function.update_self,Function.update_of_ne hcne,
      Function.update_of_ne hbne,hc,hb,hbit,hB]
    cases C <;> cases decide (R%2=1) <;> rfl
  have keep (q : Wire) (hq : q∈c::U.mask++U.low++U.core.work++[U.flag]) :
      (run [.CX c U.high,.CCX c U.bit U.high] m s).basis q=s.basis q := by
    simp [run,writeBit,away q hq]
  refine ⟨rfl,(keep c (by simp)).trans hc,?_,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hk,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hm,
    (keep U.flag (by simp)).trans hf⟩
  rw [ModUnaryLayout.z,regValue_append]
  have hv := (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hl
  rw [hv]
  simp [regValue,hh]

end DoubleValues
end ECDSAAdd.Arithmetic
