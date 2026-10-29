import ECDSAAdd.Submission.Entrant.PairEqual
import ECDSAAdd.Submission.Entrant.FastGeneric

/-! The Skywalk finite-addend circuit with both infinity comparisons replaced
by `zeroFlag`.  Every other block is the unchanged Skywalk block. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout CompressedPointDialog

/-- Classical enable bit of the exception comparison (as in `pointDialogExceptionEnable`). -/
def exceptionBit (C : Point) : Bool :=
  !pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
    !pointEqual (dialogExceptionPoint C) (-C)

def finiteProgram (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  zeroFlag L.point.finite L.control L.infinitySelect ++
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  shortEqual L L.core.equalX L.core.equalNegY (dialogExceptionPoint C) ++
  pointDialogGenericFlag L ++ fastGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  pairEqual L L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C) ++
  shortEqual L L.core.double L.doubleSelect (C+C) ++
  zeroFlag L.point.finite L.control L.genericSelect ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

section Spec
attribute [local irreducible] run wires shortEqual pairEqual pointCompressedDialogGeneric pointDialogGeneric fastGeneric
  MappedCompressed.pointCompressedArithmetic CompressedPointSquare.computableProgram

private theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgram_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgram L (.some hc) cx cy)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C))=decide (dialogExceptionEnabled C) := by
    simp [equal_simp,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simp]
  have hD : (K && pointEqual R C)=D := by rw [hK]; simp only [D,dialogDouble,equal_simp]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simp]
  have hH : (E && pointEqual R (dialogExceptionPoint C))=H := by
    simp [E,H,dialogException,dialogExceptionEnabled,equal_simp]
  have h0 := dialogFlag_doubleEnable L hn R b false false false false false false false cy
  simp only [Bool.false_xor] at h0
  have h1 := dialogFlag_exceptionEnable L hn R b false false false false false false K C
  rw [hE,Bool.false_xor] at h1
  have h2 := zeroFlag_equalO L hn R b false false false false E false K
  rw [hO,Bool.false_xor] at h2
  have h3 := pairFlag_input L hw hn R C cy b O false false false E false K rfl
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := shortFlag_equalH L hw hn R (dialogExceptionPoint C) b O D I false E false K
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false E H K
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G E H K
  have h7 := fast_boundary_generic L hw hn R b (dialogFlagState L O D I G E H K) hc
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := dialogBoundary_corners L hw hn R C hC b (dialogFlagState L O D I G E H K)
    read.1 read.2.1 read.2.2.1 read.2.2.2.2.2.1
  have h9 := dialogFlag_generic L hw hn S b O D I G E H K
  have hgclear : (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H)=false := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hgclear] at h9
  have hf := dialogFlags_output b R C
  have heout : (E && pointEqual S (-C))=H := by
    simpa [E,H,S,dialogExceptionEnabled,equal_simp] using hf.2.2.2
  have h10 := pairFlag_output L hw hn S C (exceptionBit C) b O D I false E H K (by
    simp only [E, exceptionBit, hE])
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simp] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := shortFlag_equalD L hw hn S (C+C) b false D I false E false K
  have hdo : (K && pointEqual S (C+C))=D := by
    rw [hK]; simpa only [equal_simp] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := zeroFlag_equalI L hn S b false false I false E false K
  simp only [equal_simp] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h14 := dialogFlag_exceptionEnable L hn S b false false false false E false K C
  rw [hE,show (E ^^ (b && decide (dialogExceptionEnabled C)))=false from Bool.xor_self E] at h14
  have h15 := dialogFlag_doubleEnable L hn S b false false false false false false K cy
  rw [show (K ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self K] at h15
  have h := ((((((((((((h0.seq h1).seq h2).seq h3).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).seq h14).seq h15
  simpa only [finiteProgram,List.append_assoc,dialogFlagState_zero] using h

end Spec

section Support
attribute [local irreducible] wires pointCompressedDialogGeneric fastGeneric

theorem zeroFlag_wires (f c t : Wire) : wires (zeroFlag f c t) = {f, c, t} := by
  ext q
  simp only [zeroFlag, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.notMem_empty]
  tauto

/-- Support is contained in the unchanged Skywalk static-site certificate. -/
theorem finiteProgram_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) :
    wires (finiteProgram L C cx cy) ⊆ (CompressedPointDialog.sites L).toFinset := by
  have h := CompressedPointDialog.finite_support L hw hn C cx cy
  simp only [pointCompressedDialogFinite, wires_append, Finset.union_subset_iff] at h
  have hz (t : Wire) (ht : t ∈ L.inPlaceFlags) :
      wires (zeroFlag L.point.finite L.control t) ⊆ (CompressedPointDialog.sites L).toFinset := by
    rw [zeroFlag_wires]
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [CompressedPointDialog.sites, CompressedPointSquare.residents,
      PointAddLayout.pointWires, List.mem_toFinset, List.mem_append, List.mem_cons]
    rcases hq with rfl | rfl | rfl
    · simp
    · simp
    · simp [ht]
  have z1 := hz L.infinitySelect (by simp [inPlaceFlags])
  have z2 := hz L.genericSelect (by simp [inPlaceFlags])
  have q3 := shortEqual_wires_subset L hw L.core.equalX L.core.equalNegY (dialogExceptionPoint C)
    (pointCode (dialogExceptionPoint C))
  have q5 := shortEqual_wires_subset L hw L.core.double L.doubleSelect (C+C) (pointCode (C+C))
  have p1 := pairEqual_sites L hw L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_sites L hw L.infinitySelect L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) true (exceptionBit C) C (-C)
  simp only [finiteProgram, wires_append, Finset.union_subset_iff]
  have r (A B : Program) (hAB : wires A ⊆ wires B) :
      wires B ⊆ (CompressedPointDialog.sites L).toFinset →
        wires A ⊆ (CompressedPointDialog.sites L).toFinset := fun h' => hAB.trans h'
  have r3 := r _ _ q3
  have r5 := r _ _ q5
  have hgen := fastGeneric_support L hw hn cx cy
  clear r q3 q5
  tauto

theorem sites_used (L : ControlledPointLayout) (hw : L.Widths) :
    (CompressedPointDialog.sites L).toFinset ⊆ L.dialogUsedWires.toFinset := by
  intro q hq
  exact List.mem_toFinset.mpr (CompressedPointDialog.sites_subset L hw (List.mem_toFinset.mp hq))

end Support

section Frame
attribute [local irreducible] run wires

private theorem boundary_frame_values (L : ControlledPointLayout) (P : Program)
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

private theorem boundary_work_subset (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

theorem finiteProgram_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    {{ L.control=b,L.point=R,L.work=0 }} finiteProgram L (.some hc) cx cy
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subset L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finiteProgram_spec L hw hn R hc b s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (finiteProgram_support L hw hn (.some hc) cx cy).trans (sites_used L hw)
  rw [boundary_frame_values L _ hsup R _ b s m hi ho q (work_not_point L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end Frame

section Counts

theorem zeroFlag_counts (f c t : Wire) :
    toffoliCount (zeroFlag f c t) = 1 ∧ measurementCount (zeroFlag f c t) = 0 := by
  simp [zeroFlag, toffoliCount, measurementCount]

theorem finiteProgram_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (finiteProgram L C cx cy)≤2212523 ∧
    measurementCount (finiteProgram L C cx cy)=1553064 := by
  have h := CompressedPointDialog.finite_counts L hw hn C cx cy
  have g0 := CompressedPointDialog.generic_counts L hw hn cx cy
  have g1 := fastGeneric_counts L hw cx cy
  have hpl : (PointAddLayout.pointWires L.point).length=513 := by
    simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
      show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
  have hzl : L.dialogPointZero.length=513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have e1 := equalConstant_counts L.control L.infinitySelect L.dialogPointZero (pointCode 0)
  have e2 := equalConstant_counts L.control L.genericSelect L.dialogPointZero (pointCode 0)
  have e3 := equalConstant_counts L.core.double L.doubleSelect L.dialogPointZero (pointCode C)
  have e4 := equalConstant_counts L.control L.genericSelect L.dialogPointZero (pointCode (-C))
  have e5 := equalConstant_counts L.core.equalX L.core.equalNegY L.dialogPointZero
    (pointCode (dialogExceptionPoint C))
  have e6 := equalConstant_counts L.control L.infinitySelect L.dialogPointZero (pointCode C)
  have e7 := equalConstant_counts L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C))
  have e8 := equalConstant_counts L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C))
  have s5 := shortEqual_counts L hw L.core.equalX L.core.equalNegY (dialogExceptionPoint C)
  have s7 := shortEqual_counts L hw L.core.double L.doubleSelect (C+C)
  have p1 := pairEqual_counts L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_counts L hw L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C)
  have z1 := zeroFlag_counts L.point.finite L.control L.infinitySelect
  have z2 := zeroFlag_counts L.point.finite L.control L.genericSelect
  rw [hzl] at e1 e2 e3 e4 e5 e6 e7 e8
  simp only [pointCompressedDialogFinite, toffoliCount_append, measurementCount_append] at h
  simp only [finiteProgram, toffoliCount_append, measurementCount_append]
  omega

end Counts

section Physical
open MappedCompressed
attribute [local irreducible] pointCompressedDialogGeneric fastGeneric

theorem zeroFlag_physical (f c t : Wire) (hft : f ≠ t) (hct : c ≠ t) :
    GatePhysical (zeroFlag f c t) := by
  intro i hi
  simp only [zeroFlag, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact trivial
  · exact ⟨hct, hft⟩
  · exact trivial

theorem finiteProgram_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    GatePhysical (finiteProgram L C cx cy) := by
  have orig := skywalkFinite_physical L hw hn C cx cy
  simp only [pointCompressedDialogFinite, gatePhysical_append] at orig
  have hz (t : Wire) (ht : t∈L.inPlaceFlags) : GatePhysical (zeroFlag L.point.finite L.control t) := by
    have hct : L.control ≠ t := by
      have sep := dialogFlag_separation (L:=L) hn
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    have hnd := L.dialogPointZero_nodup hn L.control t hct (Or.inl rfl) ht
    simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
      List.mem_append, not_or] at hnd
    exact zeroFlag_physical _ _ _ (fun h => hnd.2.1.1 h.symm) hct
  have z1 := hz L.infinitySelect (by simp [inPlaceFlags])
  have z2 := hz L.genericSelect (by simp [inPlaceFlags])
  have sep := dialogFlag_separation (L:=L) hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have q3 := shortEqual_physical L hw hn L.core.equalX L.core.equalNegY (by tauto)
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have q5 := shortEqual_physical L hw hn L.core.double L.doubleSelect (by tauto)
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags]) (C+C)
  have p1 := pairEqual_physical L hw hn L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_physical L hw hn L.infinitySelect L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) true (exceptionBit C) C (-C)
  have fg := fastGeneric_physical L hw hn cx cy
  simp only [finiteProgram, gatePhysical_append]
  tauto

end Physical

section Slots
open Challenge MappedCompressed Baselines

theorem finiteProgram_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (C : Point) (cx cy : Fp) : gateSlots (finiteProgram L C cx cy) ≤ 47000000 := by
  have hg := fastGeneric_gateSlots_le L hw cx cy
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hpl : (PointAddLayout.pointWires L.point).length = 513 := by
    simp [PointAddLayout.pointWires, hx, hy]
  have hzl : L.dialogPointZero.length = 513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have hz c t k : gateSlots (equalConstant c t L.dialogPointZero k) ≤ 4618 := by
    have h := equalConstant_gateSlots_le c t L.dialogPointZero k
    rw [hzl] at h; exact h
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have he : gateSlots (pointInPlaceDoubleEnable L cy) ≤ 1 := by
    unfold pointInPlaceDoubleEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hh : gateSlots (pointDialogExceptionEnable L C) ≤ 1 := by
    unfold pointDialogExceptionEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hf : gateSlots (pointDialogGenericFlag L) = 5 := rfl
  have hzf (t : Wire) : gateSlots (zeroFlag L.point.finite L.control t) = 3 := rfl
  have z2 := pairEqual_gateSlots_le L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have z4 := shortEqual_gateSlots_le L hw L.core.equalX L.core.equalNegY (dialogExceptionPoint C)
  have z5 := pairEqual_gateSlots_le L hw L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C)
  have z6 := shortEqual_gateSlots_le L hw L.core.double L.doubleSelect (C+C)
  have m1 := hm L.infinitySelect C
  have m2 := hm L.doubleSelect C
  have m3 := hm L.doubleSelect (C+C)
  have m4 := hm L.genericSelect (-C)
  have m5 := hm L.core.equalNegY (dialogExceptionPoint C)
  have m6 := hm L.core.equalNegY (-C)
  simp only [finiteProgram, pointDialogCorners, pointInPlaceCorners, gateSlots_append, hf, hzf]
  omega

end Slots

end ECDSAAdd.Entrant
