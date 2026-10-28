import ECDSAAdd.Arithmetic.MeasuredStreamedPayloads

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def measuredAResult (P O : Nat) : Nat := addModValue (P*2^128) (subModValue P O)
def measuredBResult (P O : Nat) : Nat :=
  SquareReduction.p-1-subModValue (SquareReduction.c*P) (addModValue (P*2^128) O)
def measuredCMiddleResult (P O : Nat) : Nat := addModValue (P*2^128) O

theorem measured_results_lt (P O : Nat) :
    measuredAResult P O<SquareReduction.p ∧ measuredBResult P O<SquareReduction.p ∧
      measuredCMiddleResult P O<SquareReduction.p := by
  have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  refine ⟨Nat.mod_lt _ hp,?_,Nat.mod_lt _ hp⟩
  dsimp [measuredBResult]
  omega

theorem measuredAResult_cast (P O : Nat) :
    measuredOrientationCast false (measuredAResult P O)=
      measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-P) := by
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,measuredAResult,
    addModValue_cast,subModValue_cast,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem measuredBResult_cast (P O : Nat) :
    measuredOrientationCast true (measuredBResult P O)=
      measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P) := by
  let D := subModValue (SquareReduction.c*P) (addModValue (P*2^128) O)
  have db : D<SquareReduction.p := Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  change -1-((SquareReduction.p-1-D : Nat) : ZMod SquareReduction.p)=_
  rw [measuredReflection_zmod D db]
  simp only [D,subModValue_cast,addModValue_cast,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    measuredOrientationCast,Bool.false_eq_true,if_false]
  ring

theorem measuredCMiddleResult_cast (P O : Nat) :
    measuredOrientationCast true (measuredCMiddleResult P O)=
      measuredOrientationCast true O-(P : ZMod SquareReduction.p)*2^128 := by
  simp only [measuredOrientationCast,if_true,measuredCMiddleResult,addModValue_cast,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem measuredOrientationCast_injective (orientation : Bool) (V W : Nat)
    (hv : V<SquareReduction.p) (hw : W<SquareReduction.p)
    (he : measuredOrientationCast orientation V=measuredOrientationCast orientation W) : V=W := by
  have cast : (V : ZMod SquareReduction.p)=(W : ZMod SquareReduction.p) := by
    cases h : orientation
    · simpa only [measuredOrientationCast,h,Bool.false_eq_true,if_false] using he
    · simp only [measuredOrientationCast,h,if_true] at he
      linear_combination -he
  have result := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt hv,ZMod.val_natCast_of_lt hw] using result

theorem measured_product_frame_clean (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (src : List Wire) (hs : ∀q,src.count q≤L.core.product.count q)
    (base t : BasisState) (hc : L.PairClean base) (same : ∀q,q∉src → t q=base q) : L.PairClean t := by
  have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : t q=base q := by
    apply same q
    intro bad
    have notProduct := (L.pairAuxAway hn q hq).1
    have bound := hs q
    have pos := List.count_pos_iff.mpr bad
    rw [List.count_eq_zero.mpr notProduct] at bound
    omega
  constructor
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
  · exact (keep _ (by simp)).trans hc.productHigh
  · exact (keep _ (by simp)).trans hc.outHigh
  · exact (keep _ (by simp)).trans hc.workHigh
  · exact (keep _ (by simp)).trans hc.cin
  · exact (keep _ (by simp)).trans hc.normFlag
  · exact (keep _ (by simp)).trans hc.modFlag

/-- Convert the concrete signed contribution of a live leaf into a complete
controlled producer/fold/cleanup contract in the physical workspace. -/
theorem withMeasuredSquare_contribution (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (hs2 : 2≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (orientation : Bool) (items : List MeasuredSquareFold)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (O P V : Nat) (hO : O<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O)
    (hp : P=(if s.basis control then regValue src s.basis else 0)^2)
    (whole : ∀t : BasisState,regValue dst t=P → (∀q,q∉dst → t q=s.basis q) → regValue L.core.product t=P)
    (views : ∀t : BasisState,regValue L.core.product t=P → ∀f∈items,L.MeasuredFoldView t f)
    (delta : ZMod SquareReduction.p)
    (payload : ∀t : BasisState,regValue L.core.product t=P → measuredSignedSum t items=delta)
    (hV : V<SquareReduction.p)
    (target : measuredOrientationCast (measuredFinalOrientation orientation items) V=
      measuredOrientationCast orientation O+delta) :
    (run (L.withMeasuredSquare control src dst (L.measuredFolds orientation items)) records s).phase=s.phase ∧
    regValue L.core.out (run (L.withMeasuredSquare control src dst (L.measuredFolds orientation items)) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (L.withMeasuredSquare control src dst (L.measuredFolds orientation items)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  apply L.withMeasuredSquare_correct hw control hn src dst hs hd hs2 hsmax hlen
    (L.measuredFolds orientation items) s records hc hzero V
  intro t m dstValue same
  have pv : regValue L.core.product t.basis=P := whole t.basis (by simpa [hp] using dstValue) same
  have clean := L.measured_product_frame_clean nd dst hd s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉dst := by
    intro bad
    have dis := L.product_out_disjoint nd
    have pos := List.count_pos_iff.mpr bad
    have bound := hd q
    have product : q∈L.core.product := List.count_pos_iff.mp (by omega)
    exact List.disjoint_left.mp dis product hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have initial : SquareFrame L.core.out t.basis O t.basis := ⟨outO,fun _ _ => rfl⟩
  have folded := L.measuredFolds_frame hw nd t.basis clean orientation O hO items (views t.basis pv) t m initial
  have cast := measuredFoldsValue_cast t.basis orientation O items hO
  rw [payload t.basis pv] at cast
  have result : measuredFoldsValue t.basis orientation O items=V :=
    measuredOrientationCast_injective _ _ _ (measuredFoldsValue_lt _ _ _ _ hO) hV (cast.trans target.symm)
  exact ⟨folded.1,folded.2.1.trans result,folded.2.2⟩

theorem measured_partial_product_value (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (base t : BasisState) (hzero : regValue L.core.product base=0) (P : Nat)
    (hp : regValue (L.core.product.take 256) t=P)
    (same : ∀q,q∉L.core.product.take 256 → t q=base q) : regValue L.core.product t=P := by
  have nd : L.core.product.Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have dis := List.disjoint_take_drop nd (show 256≤256 by omega)
  have high0 : regValue (L.core.product.drop 256) t=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have away : q∉L.core.product.take 256 := fun bad => List.disjoint_left.mp dis bad hq
    exact (same q away).trans ((regValue_zero _ _).mp hzero q (List.mem_of_mem_drop hq))
  have split := regValue_append (L.core.product.take 256) (L.core.product.drop 256) t
  rw [List.take_append_drop,hp,high0,Nat.mul_zero,Nat.add_zero] at split
  exact split

theorem measuredBranchA_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (L.measuredBranchA control) records s).phase=s.phase ∧
    regValue L.core.out (run (L.measuredBranchA control) records s).basis=
      measuredAResult ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (L.measuredBranchA control) records s).basis q=s.basis q := by
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := L.withMeasuredSquare_contribution hw control hn L.core.low (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) false L.measuredAItems s records hc dstZero
    O (M^2) (measuredAResult (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp => L.measuredA_views hw t M mb hp)
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => L.measuredA_sum hw t (M^2) hp pb)
    (measured_results_lt (M^2) O).1 (by
      rw [(L.measured_concrete_orientations).1]
      exact measuredAResult_cast (M^2) O)
  exact result

theorem measuredBranchB_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (L.measuredBranchB control) records s).phase=s.phase ∧
    regValue L.core.out (run (L.measuredBranchB control) records s).basis=
      measuredBResult ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (L.measuredBranchB control) records s).basis q=s.basis q := by
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := L.withMeasuredSquare_contribution hw control hn L.core.high (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) false L.measuredBItems s records hc dstZero
    O (M^2) (measuredBResult (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp => L.measuredB_views hw t M mb hp)
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => L.measuredB_sum hw t (M^2) hp pb)
    (measured_results_lt (M^2) O).2.1 (by
      rw [(L.measured_concrete_orientations).2.1]
      exact measuredBResult_cast (M^2) O)
  exact result

theorem measuredBranchC_middle_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (L.withMeasuredSquare control L.core.sum L.core.product (L.measuredFolds true L.measuredCItems)) records s).phase=s.phase ∧
    regValue L.core.out (run (L.withMeasuredSquare control L.core.sum L.core.product (L.measuredFolds true L.measuredCItems)) records s).basis=
      measuredCMiddleResult ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (L.withMeasuredSquare control L.core.sum L.core.product (L.measuredFolds true L.measuredCItems)) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have result := L.withMeasuredSquare_contribution hw control hn L.core.sum L.core.product srcCount
    (fun _ => le_rfl) (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) true L.measuredCItems s records hc hp0
    O (M^2) (measuredCMiddleResult (M^2) O) hO ho (by rw [hs])
    (fun _ hp _ => hp) (fun t hp => L.measuredC_views hw t M hp)
    (-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)
    (fun t hp => L.measuredC_sum hw t (M^2) hp)
    (measured_results_lt (M^2) O).2.2 (by
      rw [(L.measured_concrete_orientations).2.2]
      simpa only [sub_eq_add_neg,neg_mul] using measuredCMiddleResult_cast (M^2) O)
  exact result

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
