import ECDSAAdd.Arithmetic.ControlledHalf
import ECDSAAdd.Arithmetic.ControlledDouble

namespace ECDSAAdd.Arithmetic

theorem controlledUnary_wires (c : Wire) (U : ModUnaryLayout) (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    wires (controlledDouble c U p)=(c::U.z++U.core.work).toFinset ∧
    wires (controlledHalf c U p)=(c::U.z++U.core.work++[U.flag]).toFinset := by
  have hz : U.z.length=n+1 := by simp [ModUnaryLayout.z,hw.low]
  have hlen : ¬U.z.length<2 := by omega
  have ht : (U.constant.take U.low.length).length=n := by simp [hw.low,hw.constant]
  have hc : (U.carry.take (U.low.length-1)).length=n-1 := by simp [hw.low,hw.carry]
  have ha := addInPlace_wires U.constant U.z U.carry U.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry,hz])
  have hs := subInPlace_wires U.constant U.z U.carry U.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry,hz])
  have hcmp := (compareLt_wires (some c) U.low (U.constant.take U.low.length) U.carry U.cin U.flag
    (hw.low.trans ht.symm) (hw.carry.trans ht.symm)).2 ((p+1)/2)
  have hdend : wires [.CX c U.high,.CCX c U.bit U.high]=[c,U.bit,U.high].toFinset := by
    ext q; simp [wires,Instr.wires,or_comm,or_assoc]
  have hstart : wires [.CCX c U.bit U.flag]=[c,U.bit,U.flag].toFinset := by
    ext q; simp [wires,Instr.wires,or_comm]
  have hend : wires [.CX c U.flag]=[c,U.flag].toFinset := by simp [wires,Instr.wires]
  constructor
  · simp only [controlledDouble,maskedSubConst,wires_append,(shift_wires c U.z).2,hlen,if_false,hs,hdend]
    ext q
    have hx : q∈wires (maskedConstant c U.constant p) → q∈c::U.constant :=
      fun hh => List.mem_toFinset.mp (maskedConstant_wires_subset c U.constant p hh)
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
  · simp only [controlledHalf,maskedAddConst,wires_append,ha,hcmp,(shift_wires c U.z).1,
      hlen,if_false,hstart,hend]
    ext q
    have hm : q∈wires (maskedConstant U.flag U.constant p) → q∈U.flag::U.constant :=
      fun hh => List.mem_toFinset.mp (maskedConstant_wires_subset U.flag U.constant p hh)
    have hts : q∈U.constant.take U.low.length → q∈U.constant :=
      fun hh => (List.take_sublist U.low.length U.constant).subset hh
    have hb : q=U.bit → q∈U.low := fun he => he.symm ▸ U.bit_mem n hw hn
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,Option.toList_some,ModUnaryLayout.core,ModAddCoreLayout.work,
      ModUnaryLayout.z] at hm hb ⊢
    clear hw hn hz ht hc ha hs hcmp hdend hstart hend hlen
    aesop



/-- 目标字以外逐线保持，包括控制及全部清零工作位。 -/
theorem controlledHalf_frame (c : Wire) (U : ModUnaryLayout) (n p Z : Nat) (C : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hp : p%2=1) (hpn : p<2^n) (hZ : Z<p)
    (s : State) (m : List Bool) (hc : s.basis c=C) (hz : regValue U.z s.basis=Z)
    (hwork : regValue U.work s.basis=0) (q : Wire) (hq : q∉U.z) :
    (run (controlledHalf c U p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := controlledHalf_spec c U n p Z C hw hnd hp hpn hZ s m ⟨⟨hc,hz⟩,hwork⟩
  simp only [Holds.holds] at h
  by_cases hqc : q=c
  · subst q; exact h.1.1.trans hc.symm
  by_cases hqw : q∈U.work
  · exact (regValue_eq_iff _ _ _).mp (h.2.trans hwork.symm) q hqw
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  apply run_preserves_outside
  rw [(controlledUnary_wires c U n p hw hn).2]
  simp only [ModUnaryLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hqw
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons]
  tauto

/-- 目标字以外逐线保持，包括控制及全部清零工作位。 -/
theorem controlledDouble_frame (c : Wire) (U : ModUnaryLayout) (n p Z : Nat) (C : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hp : p%2=1) (hpn : p<2^n) (hZ : Z<p)
    (s : State) (m : List Bool) (hc : s.basis c=C) (hz : regValue U.z s.basis=Z)
    (hwork : regValue U.work s.basis=0) (q : Wire) (hq : q∉U.z) :
    (run (controlledDouble c U p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := controlledDouble_spec c U n p Z C hw hnd hp hpn hZ s m ⟨⟨hc,hz⟩,hwork⟩
  simp only [Holds.holds] at h
  by_cases hqc : q=c
  · subst q; exact h.1.1.trans hc.symm
  by_cases hqw : q∈U.work
  · exact (regValue_eq_iff _ _ _).mp (h.2.trans hwork.symm) q hqw
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  apply run_preserves_outside
  rw [(controlledUnary_wires c U n p hw hn).1]
  simp only [ModUnaryLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hqw
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons]
  tauto

/-- 实际支持不计未被半倍门列触及的 mask。 -/
theorem controlledUnary_qubits (c : Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hn : 0<n) :
    qubitCount (controlledHalf c U p)=3*n+5 ∧
    qubitCount (controlledDouble c U p)=3*n+4 := by
  have hhalf : (c::U.z++U.core.work++[U.flag]).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hdbl : (c::U.z++U.core.work).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hhalf q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  constructor
  · rw [qubitCount,(controlledUnary_wires c U n p hw hn).2,List.toFinset_card_of_nodup hhalf]
    simp only [ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,
      List.length_append,List.length_cons,List.length_nil,hw.low,hw.constant,hw.carry]
    omega
  · rw [qubitCount,(controlledUnary_wires c U n p hw hn).1,List.toFinset_card_of_nodup hdbl]
    simp only [ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.work,
      List.length_append,List.length_cons,List.length_nil,hw.low,hw.constant,hw.carry]
    omega

end ECDSAAdd.Arithmetic
