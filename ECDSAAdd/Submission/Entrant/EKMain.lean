import ECDSAAdd.Submission.Entrant.EKSupport

/-! Frame, resources and validity of `finiteProgramFG` for any generic block,
and the instance with the Skywalk generic block. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

section Frame
attribute [local irreducible] run wires

private theorem boundary_frame_valuesE (L : ControlledPointLayout) (P : Program)
    (hP : wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

private theorem boundary_work_subsetE (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_pointE (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

theorem finiteProgramFG_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) (hG : wires Gen ⊆ (sitesE L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} finiteProgramFG L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subsetE L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finiteProgramFG_spec L hw hn R hc b Gen hGen s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (finiteProgramFG_support L hw (.some hc) cy Gen hG).trans (sitesE_used L hw)
  rw [boundary_frame_valuesE L _ hsup R _ b s m hi ho q (work_not_pointE L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end Frame

section Resources
open Challenge Baselines

theorem gatedShort_counts (L : ControlledPointLayout) (hw : L.Widths) (en : Bool) (t : Wire) (P : Point) :
    toffoliCount (gatedShort L en t P) ≤ 257 ∧ measurementCount (gatedShort L en t P) ≤ 257 := by
  cases en
  · simp [gatedShort, toffoliCount, measurementCount]
  · have h := shortEqual_counts L hw L.control t P
    simp only [gatedShort, if_true, h.1, h.2, le_refl, and_self]

theorem genericFlag2_counts (L : ControlledPointLayout) :
    toffoliCount (genericFlag2 L) = 1 ∧ measurementCount (genericFlag2 L) = 0 := by
  simp [genericFlag2, toffoliCount, measurementCount]

theorem genericFlag3_counts (L : ControlledPointLayout) :
    toffoliCount (genericFlag3 L) = 0 ∧ measurementCount (genericFlag3 L) = 0 := by
  simp [genericFlag3, toffoliCount, measurementCount]

theorem finiteProgramFG_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) {cx : Fp} (hc : curve.toAffine.Nonsingular cx cy) (hC : C = .some hc) :
    toffoliCount (finiteProgramFG L C cy Gen) ≤ 1029 + toffoliCount Gen ∧
    measurementCount (finiteProgramFG L C cy Gen) ≤ 1027 + measurementCount Gen := by
  have p1 := pairEqual_counts L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_counts L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)
  have c1 : tailCost (decide (cy≠-cy)) (yBit C) true (yBit (-C)) = 1 := by
    subst hC
    rw [cy_ne_neg hc, yBit_neg hc]
    cases yBit (.some hc) <;> decide
  have c2 : tailCost true (yBit C) (exceptionBit C) (yBit (-C)) ≤ 1 := by
    subst hC
    rw [yBit_neg hc]
    cases yBit (.some hc) <;> cases exceptionBit (.some hc) <;> decide
  have g1 := gatedShort_counts L hw (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C)
  have g2 := gatedShort_counts L hw (decide (cy≠-cy)) L.doubleSelect (C+C)
  have z2 : toffoliCount (chainErase L.control L.point.finite L.genericSelect) = 0 ∧
      measurementCount (chainErase L.control L.point.finite L.genericSelect) = 1 := by
    simp [chainErase, toffoliCount, measurementCount]
  have f := genericFlag2_counts L
  have f3 := genericFlag3_counts L
  have c := (show toffoliCount (corners2 L C) = 0 ∧ measurementCount (corners2 L C) = 0 by
    simp only [corners2, toffoliCount_append, measurementCount_append,
      (maskedPointConstant_counts _ _ _).1, (maskedPointConstant_counts _ _ _).2]; decide)
  simp only [finiteProgramFG, toffoliCount_append, measurementCount_append]
  omega

theorem finiteProgramFG_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : GatePhysical Gen) :
    GatePhysical (finiteProgramFG L C cy Gen) := by
  have sep := dialogFlag_separation (L:=L) hn
  have hg (en : Bool) (t : Wire) (ht : t∈L.inPlaceFlags) (P : Point) : GatePhysical (gatedShort L en t P) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    cases en
    · simp [gatedShort, GatePhysical]
    · simpa only [gatedShort, if_true] using shortEqual_physical L hw hn L.control t hct (Or.inl rfl) ht P
  have z2 : GatePhysical (chainErase L.control L.point.finite L.genericSelect) := by
    intro i hi
    simp only [chainErase, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals trivial
  have fd := flags_distinct L hn
  have gf : GatePhysical (genericFlag2 L) := by
    intro i hi
    simp only [genericFlag2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨fd.1, fd.2.1⟩
    · exact fd.2.2.1
    · exact fd.2.2.2.1
    · exact fd.2.2.2.2.1
  have gf3 : GatePhysical (genericFlag3 L) := by
    intro i hi
    simp only [genericFlag3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact fd.1
    · exact fd.2.2.1
    · exact fd.2.2.2.1
    · exact fd.2.2.2.2.1
  have away (c : Wire) (hc : c ∈ L.inPlaceFlags) : c ∉ PointAddLayout.pointWires L.point := by
    intro hm
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) c
    have hf := List.count_pos_iff.mpr hc
    have hp := List.count_pos_iff.mpr hm
    simp only [dialogUsedWires,List.count_append,List.count_cons] at h
    omega
  have all (c : Wire) (hc : c ∈ L.inPlaceFlags) (D : Point) : GatePhysical (maskedPointConstant c L.point D) :=
    maskedPointConstant_physical c L.point D (away c hc)
  have co : GatePhysical (corners2 L C) := by
    simp only [corners2, gatePhysical_append]
    repeat constructor
    all_goals apply all _ (by simp [inPlaceFlags])
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have q3 := hg (exceptionBit C) L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have q5 := hg (decide (cy≠-cy)) L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have p1 := pairEqual_physical L hw hn L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_physical L hw hn L.core.generic L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) true (exceptionBit C) C (-C)
  simp only [finiteProgramFG, gatePhysical_append]
  tauto

theorem finiteProgramFG_gateSlots (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) : gateSlots (finiteProgramFG L C cy Gen) ≤ 20000 + gateSlots Gen := by
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have hf : gateSlots (genericFlag2 L) = 4 := rfl
  have hf3 : gateSlots (genericFlag3 L) = 4 := rfl
  have hze : gateSlots (chainErase L.control L.point.finite L.genericSelect) = 4 := rfl
  have hgs (en : Bool) (t : Wire) (P : Point) : gateSlots (gatedShort L en t P) ≤ 2314 := by
    cases en
    · simp [gatedShort]
    · simpa only [gatedShort, if_true] using shortEqual_gateSlots_le L hw L.control t P
  have z2 := pairEqual_gateSlots_le L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have z4 := hgs (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C)
  have z5 := pairEqual_gateSlots_le L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)
  have z6 := hgs (decide (cy≠-cy)) L.doubleSelect (C+C)
  have m1 := hm L.core.generic C
  have m2 := hm L.doubleSelect C
  have m3 := hm L.doubleSelect (C+C)
  have m4 := hm L.genericSelect (-C)
  have m5 := hm L.core.equalNegY (dialogExceptionPoint C)
  have m6 := hm L.core.equalNegY (-C)
  simp only [finiteProgramFG, corners2, gateSlots_append, hf, hf3, hze]
  omega

end Resources

end ECDSAAdd.Entrant
