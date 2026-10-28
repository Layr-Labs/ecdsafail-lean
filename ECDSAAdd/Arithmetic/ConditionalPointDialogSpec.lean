import ECDSAAdd.Arithmetic.ConditionalPointDialog
import ECDSAAdd.Arithmetic.PointDialogFiniteSpec
import ECDSAAdd.Arithmetic.PointDialogWires
namespace ECDSAAdd.Arithmetic.ConditionalPointDialog
open ControlledPointLayout Secp256k1
noncomputable section
local instance : DecidableEq Point := Classical.decEq _
attribute [local irreducible] runWithTape recordedWires wires generic pointDialogGeneric
  recordedThen embedRecorded
  CompressedPointSquare.computableProgram
def finite (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout)
    (C : Point) (cx cy : Fp) : RecordedProgram :=
  recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (recordedThen (embedRecorded (pointInPlaceDoubleEnable L cy))
    (embedRecorded (pointDialogExceptionEnable L C)))
    (embedRecorded (equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0))))
    (embedRecorded (equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C))))
    (embedRecorded (equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)))))
    (embedRecorded (equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)))))
    (embedRecorded (pointDialogGenericFlag L)))
    (generic backend L cx cy))
    (embedRecorded (pointDialogCorners L C)))
    (embedRecorded (pointDialogGenericFlag L)))
    (embedRecorded (equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C))))
    (embedRecorded (equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)))))
    (embedRecorded (equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0))))
    (embedRecorded (equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)))))
    (embedRecorded (pointDialogExceptionEnable L C)))
    (embedRecorded (pointInPlaceDoubleEnable L cy))

def program (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout)
    (C : Point) : RecordedProgram :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _hc => finite backend L C cx cy

theorem generic_wellFormed (backend : ConditionalPointArithmeticBackend)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    RecordedWellFormedAt 0 (generic backend L cx cy) := by
  unfold generic
  repeat first | apply recordedThen_wellFormed | apply embedRecorded_wellFormed | exact backend.wellFormed L hw hn _

theorem program_wellFormed (backend : ConditionalPointArithmeticBackend)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) :
    RecordedWellFormedAt 0 (program backend L C) := by
  cases C with
  | zero => trivial
  | some hc =>
    unfold program finite
    repeat first | apply recordedThen_wellFormed | apply embedRecorded_wellFormed | exact generic_wellFormed backend L hw hn _ _

private theorem equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finite_spec (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (hsafe : GenericSafe backend ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 cx cy (dialogOrdinary b R (.some hc))) :
    RecordedTriple (PointDialogBoundary L R b (fun _=>false)) (finite backend L (.some hc) cx cy)
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
  have h7 := boundary_generic backend L hw hn R b (dialogFlagState L O D I G E H K) hc
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
    (by simpa only [read.2.2.2.1] using hsafe)
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
  have h := ((((((((((((((h0.recorded.seq h1.recorded).seq h2.recorded).seq h3.recorded).seq h4.recorded).seq h5.recorded).seq h6.recorded).seq h7).seq h8.recorded).seq h9.recorded).seq h10.recorded).seq h11.recorded).seq h12.recorded).seq h13.recorded).seq h14.recorded).seq h15.recorded
  simpa only [finite,dialogFlagState_zero] using h


private theorem generic_used (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    recordedWires (generic backend L cx cy)⊆L.dialogUsedWires.toFinset := by
  have old := pointDialogGeneric_wires L hw hn cx cy
  have embed : (L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset⊆L.dialogUsedWires.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    tauto
  have original := old.trans embed
  have div := backend.support L hw hn false
  have mul := backend.support L hw hn true
  have square := (CompressedPointSquare.computable_support L hw hn).trans (by
    intro q hq
    exact List.mem_toFinset.mpr (PointArithmeticBackend.shared_subset L hw (List.mem_toFinset.mp hq)))
  simp only [pointDialogGeneric,wires_append,Finset.union_subset_iff] at original
  simp only [generic,recordedThen_wires,embedRecorded_wires,Finset.union_subset_iff]
  tauto

private theorem finite_wires (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : recordedWires (finite backend L C cx cy)⊆L.dialogUsedWires.toFinset := by
  have old := pointDialogFinite_wires L hw hn C cx cy
  have generic := generic_used backend L hw hn cx cy
  simp only [pointDialogFinite,wires_append,Finset.union_subset_iff] at old
  simp only [finite,recordedThen_wires,embedRecorded_wires,Finset.union_subset_iff]
  tauto

/-- Support includes every instruction and both measurement correction branches. -/
theorem program_wires (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) :
    recordedWires (program backend L C) ⊆ L.dialogUsedWires.toFinset := by
  cases C with
  | zero => simp [program, recordedWires]
  | some hc => exact finite_wires backend L hw hn _ _ _

private theorem boundary_frame_values (L : ControlledPointLayout) (P : RecordedProgram)
    (hP : recordedWires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (runWithTape P m 0 s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (runWithTape P m 0 s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply runWithTape_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

theorem finite_frame (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (hsafe : GenericSafe backend ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 cx cy (dialogOrdinary b R (.some hc))) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) :
    (runWithTape (finite backend L (.some hc) cx cy) m 0 s).basis q=s.basis q := by
  have ho := (finite_spec backend L hw hn R hc b hsafe s m hi).2
  exact boundary_frame_values L _ (finite_wires backend L hw hn (.some hc) cx cy) R _ b s m hi ho q hq

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
theorem full_spec (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (hsafe : GenericSafe backend ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 cx cy (dialogOrdinary b R (.some hc))) :
    RecordedTriple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ regValue L.work st=0)
      (finite backend L (.some hc) cx cy)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+.some hc else R)) ∧ regValue L.work st=0) := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subset L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finite_spec backend L hw hn R hc b hsafe s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  rw [finite_frame backend L hw hn R hc b hsafe s m hi q (work_not_point L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

/-- Original-input success condition for the two actual arithmetic operands.
No condition is required for addition of infinity (the empty program). -/
def Safe (backend : ConditionalPointArithmeticBackend) (b : Bool) (R C : Point) : Prop :=
  match C with
  | .zero => True
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
    GenericSafe backend ((coordinates R).getD (0,0)).1 ((coordinates R).getD (0,0)).2
      cx cy (dialogOrdinary b R (.some hc))

/-- All valid points and all constants, including infinity and exceptional
branches; original work and control contracts and arbitrary phase retained. -/
theorem add_spec (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) (hsafe : Safe backend b R C) :
    RecordedTriple (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point R) ∧ regValue L.work st=0)
      (program backend L C)
      (fun st => (Holds.holds st L.control b ∧ Holds.holds st L.point (if b then R+C else R)) ∧ regValue L.work st=0) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,runWithTape,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self] using And.intro (Eq.refl s.phase) hs
  | some hc => exact full_spec backend L hw hn R hc b hsafe


/-- Conditional correctness with only the workspace used by this program clean. -/
theorem add_boundary (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (b : Bool) (R C : Point)
    (hsafe : Safe backend b R C) :
    RecordedTriple (PointDialogBoundary L R b (fun _ => false)) (program backend L C)
      (PointDialogBoundary L (if b then R+C else R) b (fun _ => false)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program, runWithTape, ←WeierstrassCurve.Affine.Point.zero_def,
      add_zero, ite_self] using And.intro (Eq.refl s.phase) hs
  | some hc => exact finite_spec backend L hw hn R hc b hsafe

/-- Every non-point wire, including unused ancillas, is restored. -/
theorem add_frame (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (b : Bool) (R C : Point)
    (hsafe : Safe backend b R C) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) :
    (runWithTape (program backend L C) m 0 s).basis q = s.basis q := by
  cases C with
  | zero => simp only [program, runWithTape]
  | some hc => exact finite_frame backend L hw hn R hc b hsafe s m hi q hq

end
end ECDSAAdd.Arithmetic.ConditionalPointDialog
