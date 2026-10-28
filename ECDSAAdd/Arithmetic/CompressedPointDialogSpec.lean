import ECDSAAdd.Arithmetic.CompressedPointDialogSteps
import ECDSAAdd.Arithmetic.PointDialogFiniteSpec
import ECDSAAdd.Arithmetic.PointDialogWires
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.CompressedPointDialog
open ControlledPointLayout Secp256k1
attribute [local irreducible] run wires pointCompressedDialogGeneric pointDialogGeneric
  MappedCompressed.pointCompressedArithmetic CompressedPointSquare.computableProgram

private theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finite_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (pointCompressedDialogFinite L (.some hc) cx cy)
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
  have h2 := dialogFlag_equalO L hw hn R 0 b false false false false E false K
  rw [hO,Bool.false_xor] at h2
  have h3 := dialogFlag_equalD L hw hn R C b O false false false E false K
  rw [hD,Bool.false_xor] at h3
  have h4 := dialogFlag_equalI L hw hn R (-C) b O D false false E false K
  rw [hI,Bool.false_xor] at h4
  have h5 := dialogFlag_equalH L hw hn R (dialogExceptionPoint C) b O D I false E false K
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false E H K
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G E H K
  have h7 := boundary_generic L hw hn R b (dialogFlagState L O D I G E H K) hc
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
  have h10 := dialogFlag_equalO L hw hn S C b O D I false E H K
  simp only [equal_simp] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := dialogFlag_equalD L hw hn S (C+C) b false D I false E H K
  have hdo : (K && pointEqual S (C+C))=D := by
    rw [hK]; simpa only [equal_simp] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := dialogFlag_equalI L hw hn S 0 b false false I false E H K
  simp only [equal_simp] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h13 := dialogFlag_equalH L hw hn S (-C) b false false false false E H K
  have heout : (E && pointEqual S (-C))=H := by
    simpa [E,H,S,dialogExceptionEnabled,equal_simp] using hf.2.2.2
  rw [heout,Bool.xor_self] at h13
  have h14 := dialogFlag_exceptionEnable L hn S b false false false false E false K C
  rw [hE,show (E ^^ (b && decide (dialogExceptionEnabled C)))=false from Bool.xor_self E] at h14
  have h15 := dialogFlag_doubleEnable L hn S b false false false false false false K cy
  rw [show (K ^^ (b && decide (cy≠-cy)))=false from Bool.xor_self K] at h15
  have h := ((((((((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).seq h13).seq h14).seq h15
  simpa only [pointCompressedDialogFinite,List.append_assoc,dialogFlagState_zero] using h


private theorem shared_subset (L : ControlledPointLayout) (hw : L.Widths) :
    CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L ⊆ L.dialogUsedWires := by
  intro q hq
  rcases List.mem_append.mp hq with res|pool
  · exact List.mem_append_left _ res
  · have mem : q∈L.dialogPool := by
      simp only [CompressedPointSquare.sharedPool,List.mem_append] at pool
      rcases pool with (pool|pool)|pool
      all_goals
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp pool
        simp only [List.mem_range'_1] at hi
        change L.core.poolWire i∈L.core.pool.take 2613
        rw [←L.core.pool_prefix hw 2613 (by omega)]
        exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1];omega,rfl⟩
    exact List.mem_append_right _ mem

private theorem generic_used (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (pointCompressedDialogGeneric L cx cy)⊆L.dialogUsedWires.toFinset := by
  have old := pointDialogGeneric_wires L hw hn cx cy
  have embed : (L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset⊆L.dialogUsedWires.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    tauto
  have original := old.trans embed
  have common : (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).toFinset⊆
      L.dialogUsedWires.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (shared_subset L hw (List.mem_toFinset.mp hq))
  have div := (MappedCompressed.pointCompressedArithmetic_support L hw false).trans common
  have mul := (MappedCompressed.pointCompressedArithmetic_support L hw true).trans common
  have square := (CompressedPointSquare.computable_support L hw hn).trans common
  intro q hq
  have ho := @original q
  have hd := @div q
  have hm := @mul q
  have hs := @square q
  simp only [pointCompressedDialogGeneric,pointDialogGeneric,wires_append,Finset.mem_union] at hq ho
  tauto

private theorem finite_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : wires (pointCompressedDialogFinite L C cx cy)⊆L.dialogUsedWires.toFinset := by
  have old := pointDialogFinite_wires L hw hn C cx cy
  have generic := generic_used L hw hn cx cy
  intro q hq
  have ho := @old q
  have hg := @generic q
  simp only [pointCompressedDialogFinite,pointDialogFinite,wires_append,Finset.mem_union] at hq ho
  tauto

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

theorem finite_frame (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) :
    (run (pointCompressedDialogFinite L (.some hc) cx cy) m s).basis q=s.basis q := by
  have ho := (finite_spec L hw hn R hc b s m hi).2
  exact boundary_frame_values L _ (finite_wires L hw hn (.some hc) cx cy) R _ b s m hi ho q hq

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

/-- 公共布局的全部分配工作位恢复为零，包括本实现未使用的旧银行。 -/
theorem full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    {{ L.control=b,L.point=R,L.work=0 }} pointCompressedDialogFinite L (.some hc) cx cy
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subset L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finite_spec L hw hn R hc b s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  rw [finite_frame L hw hn R hc b s m hi q (work_not_point L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

/-- All valid points and all constants, including infinity and exceptional
branches; original work and control contracts and arbitrary phase retained. -/
theorem add_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) :
    {{ L.control=b,L.point=R,L.work=0 }} pointCompressedAdd L C
    {{ L.control=b,L.point=(if b then R+C else R),L.work=0 }} := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [pointCompressedAdd,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self] using And.intro (Eq.refl s.phase) hs
  | some hc => exact full_spec L hw hn R hc b

end ECDSAAdd.Arithmetic.CompressedPointDialog
#print axioms ECDSAAdd.Arithmetic.CompressedPointDialog.finite_spec
#print axioms ECDSAAdd.Arithmetic.CompressedPointDialog.full_spec
#print axioms ECDSAAdd.Arithmetic.CompressedPointDialog.add_spec
