import ECDSAAdd.Arithmetic.MeasuredStreamedSquareProof
import ECDSAAdd.Arithmetic.MeasuredStreamedSupport
import ECDSAAdd.Arithmetic.MeasuredStreamedPhysical
import ECDSAAdd.Baselines.SlotStreamedSquare

/-! Sign-grouped fold schedule for the measured streamed square.
Each fold list is reordered so that all folds of one sign are applied
consecutively, and each branch starts in the orientation the previous branch
ended in. Modular addition is commutative, so the signed payload sum is
unchanged, while the number of 255-Toffoli output reflections drops from 20
to 4 (one per branch plus the final restoring reflection). -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- Folds of sign `first`, then the folds of the other sign. -/
def sortedItems (first : Bool) (items : List MeasuredSquareFold) : List MeasuredSquareFold :=
  items.filter (fun f => f.negative == first) ++ items.filter (fun f => !(f.negative == first))

theorem sorted_perm (first : Bool) (items : List MeasuredSquareFold) :
    (sortedItems first items).Perm items :=
  List.filter_append_perm _ _

theorem signedSum_perm (base : BasisState) {a b : List MeasuredSquareFold} (h : a.Perm b) :
    measuredSignedSum base a=measuredSignedSum base b := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [measuredSignedSum, ih]
  | swap x y l => simp only [measuredSignedSum]; ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def fastAItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  sortedItems false L.measuredAItems
def fastBItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  sortedItems true L.measuredBItems
def fastCItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  sortedItems false L.measuredCItems

def fastBranchA (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.low (L.core.product.take 256)
    (L.measuredFolds false (fastAItems L))
def fastBranchB (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.high (L.core.product.take 256)
    (L.measuredFolds true (fastBItems L))
def fastMiddleC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.sum L.core.product (L.measuredFolds false (fastCItems L))
def fastBranchC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.core.prepareSum++fastMiddleC L control++L.core.clearSum

def fastProgram (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  fastBranchA L control++fastBranchB L control++fastBranchC L control++L.reflectOutput

def fastNR (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  fastBranchA L control++fastBranchB L control++fastBranchC L control

theorem fastProgram_split (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    fastProgram L control=fastNR L control++L.reflectOutput := rfl

theorem fastNR_wires_subset (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    ECDSAAdd.wires (fastNR L control)⊆ECDSAAdd.wires (fastProgram L control) := by
  rw [fastProgram_split, wires_append]
  exact Finset.subset_union_left

theorem fast_orientations (L : CuccaroStreamedSquareWideLayout) :
    measuredFinalOrientation false (fastAItems L)=true ∧
    measuredFinalOrientation true (fastBItems L)=false ∧
    measuredFinalOrientation false (fastCItems L)=true := by
  simp [measuredFinalOrientation,fastAItems,fastBItems,fastCItems,sortedItems,measuredAItems,
    measuredBItems,measuredCItems,shiftedProductItems,nafMinusOneItems,List.filter_cons]

/-- The unique canonical value with a given orientation cast. -/
def ofCast (o : Bool) (z : ZMod SquareReduction.p) : Nat := if o then (-1-z).val else z.val

theorem ofCast_lt (o : Bool) (z : ZMod SquareReduction.p) : ofCast o z<SquareReduction.p := by
  haveI : NeZero SquareReduction.p := ⟨by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]⟩
  cases o
  · simp only [ofCast,Bool.false_eq_true,if_false]
    exact ZMod.val_lt _
  · simp only [ofCast,if_true]
    exact ZMod.val_lt _

theorem cast_ofCast (o : Bool) (z : ZMod SquareReduction.p) :
    measuredOrientationCast o (ofCast o z)=z := by
  haveI : NeZero SquareReduction.p := ⟨by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]⟩
  cases o
  · simp [measuredOrientationCast,ofCast,ZMod.natCast_zmod_val]
  · simp only [measuredOrientationCast,ofCast,if_true,ZMod.natCast_zmod_val]
    ring

def resA (P O : Nat) : Nat :=
  ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-P))
def resB (P O : Nat) : Nat :=
  ofCast false (measuredOrientationCast true O+((P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P))
def resC (P O : Nat) : Nat :=
  ofCast true (measuredOrientationCast false O+(-(P : ZMod SquareReduction.p)*2^128))

theorem fastA_mem (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold)
    (hf : f∈fastAItems L) : f∈L.measuredAItems := (sorted_perm _ _).subset hf
theorem fastB_mem (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold)
    (hf : f∈fastBItems L) : f∈L.measuredBItems := (sorted_perm _ _).subset hf
theorem fastC_mem (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold)
    (hf : f∈fastCItems L) : f∈L.measuredCItems := (sorted_perm _ _).subset hf

theorem fastBranchA_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (fastBranchA L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastBranchA L control) records s).basis=
      resA ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (fastBranchA L control) records s).basis q=s.basis q := by
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
    (by simp [hw.core.product,L.core.low_length hw.core]) false (fastAItems L) s records hc dstZero
    O (M^2) (resA (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp f hf => L.measuredA_views hw t M mb hp f (fastA_mem L f hf))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (signedSum_perm t (sorted_perm _ _)).trans (L.measuredA_sum hw t (M^2) hp pb))
    (ofCast_lt _ _) (by
      rw [(fast_orientations L).1]
      exact cast_ofCast _ _)
  exact result

theorem fastBranchB_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (fastBranchB L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastBranchB L control) records s).basis=
      resB ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (fastBranchB L control) records s).basis q=s.basis q := by
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
    (by simp [hw.core.product,L.core.high_length hw.core]) true (fastBItems L) s records hc dstZero
    O (M^2) (resB (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp f hf => L.measuredB_views hw t M mb hp f (fastB_mem L f hf))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (signedSum_perm t (sorted_perm _ _)).trans (L.measuredB_sum hw t (M^2) hp pb))
    (ofCast_lt _ _) (by
      rw [(fast_orientations L).2.1]
      exact cast_ofCast _ _)
  exact result

theorem fastMiddleC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (fastMiddleC L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastMiddleC L control) records s).basis=
      resC ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (fastMiddleC L control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have result := L.withMeasuredSquare_contribution hw control hn L.core.sum L.core.product srcCount
    (fun _ => le_rfl) (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) false (fastCItems L) s records hc hp0
    O (M^2) (resC (M^2) O) hO ho (by rw [hs])
    (fun _ hp _ => hp) (fun t hp f hf => L.measuredC_views hw t M hp f (fastC_mem L f hf))
    (-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)
    (fun t hp => (signedSum_perm t (sorted_perm _ _)).trans (L.measuredC_sum hw t (M^2) hp))
    (ofCast_lt _ _) (by
      rw [(fast_orientations L).2.2]
      exact cast_ofCast _ _)
  exact result

theorem fastBranchC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis) :
    (run (fastBranchC L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastBranchC L control) records s).basis=
      resC ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (fastBranchC L control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := fastMiddleC L control
  let u := run L.core.prepareSum [] s
  let v := run middle (records.take (measurementCount middle)) u
  let out := run L.core.clearSum (records.drop (measurementCount middle)) v
  have prep := L.prepareSum_frame hw nd s.basis A B ha hb bound (PairClean.corePad L s.basis hc) hc.cin
    s [] (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have used := fastMiddleC_correct L hw control hn (A+B) O hO u
    (records.take (measurementCount middle)) prep.2.1 outU productU cleanU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have cleared := L.clearSum_frame hw nd restoreBase A B lowRestore sumRestore bound padRestore cinRestore
    v (records.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      resC ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      resC ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  have prepM := (L.core.sum_counts hw.core).1.2
  simpa [fastBranchC,middle,u,v,out,run_append,prepM] using final

theorem fast_complete_exact (enabled : Bool) (A B O : Nat) :
    SquareReduction.p-1-resC ((if enabled then A+B else 0)^2)
      (resB ((if enabled then B else 0)^2) (resA ((if enabled then A else 0)^2) O))=
      subModValue (if enabled then (A+2^128*B)^2 else 0) O := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := resA PA O
  let OB := resB PB OA
  let OC := resC PC OB
  have ea : measuredOrientationCast true OA=measuredOrientationCast false O+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  have eb : measuredOrientationCast false OB=measuredOrientationCast true OA+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  have ec : measuredOrientationCast true OC=measuredOrientationCast false OB+(-(PC : ZMod SquareReduction.p)*2^128) :=
    cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have ocBound : OC<SquareReduction.p := ofCast_lt _ _
  have lhsBound : SquareReduction.p-1-OC<SquareReduction.p := by
    have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
    omega
  have cast : ((SquareReduction.p-1-OC : Nat) : ZMod SquareReduction.p)=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [measuredReflection_zmod OC ocBound,subModValue_cast]
    linear_combination ea+eb+ec+identity
  have targetBound : subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt lhsBound,ZMod.val_natCast_of_lt targetBound] using value

theorem fastProgram_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (fastProgram L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastProgram L control) records s).basis=
      (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (fastProgram L control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := resA PA O
  let OB := resB PB OA
  let OC := resC PC OB
  let restA := records.drop (measurementCount (fastBranchA L control))
  let restB := restA.drop (measurementCount (fastBranchB L control))
  let restC := restB.drop (measurementCount (fastBranchC L control))
  let u := run (fastBranchA L control) (records.take (measurementCount (fastBranchA L control))) s
  let v := run (fastBranchB L control) (restA.take (measurementCount (fastBranchB L control))) u
  let w := run (fastBranchC L control) (restB.take (measurementCount (fastBranchC L control))) v
  let out := run L.reflectOutput restC w
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ea := fastBranchA_correct L hw control hn A O hO s
    (records.take (measurementCount (fastBranchA L control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := fastBranchB_correct L hw control hn B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (fastBranchB L control))) highU ea.2.1 productU cleanU
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ea.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A := regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have sumV : regValue L.core.sum v.basis=B :=
    (regValue_congr _ _ _ (fun q hq => sameV q (sumAway q hq))).trans sumB
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ec := fastBranchC_correct L hw control hn A B OB (ofCast_lt _ _) v
    (restB.take (measurementCount (fastBranchC L control))) lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have cleanW : L.PairClean w.basis :=
    L.squareFrame_clean nd s.basis w.basis OC ⟨ec.2.1,sameW⟩ hc
  have er := L.reflectOutput_correct hw nd OC (ofCast_lt _ _) w restC ec.2.1 cleanW
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out out.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := fast_complete_exact enabled A B O
    rw [split] at exactResult
    exact er.2.1.trans exactResult
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨er.1.trans (ec.1.trans (eb.1.trans ea.1)),fullValue,?_⟩
    intro q hq
    exact (er.2.2 q hq).trans (sameW q hq)
  simpa [fastProgram,u,v,w,out,restA,restB,restC,enabled,run_append,Nat.add_assoc] using final

theorem fastNR_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (fastNR L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastNR L control) records s).basis=
      SquareReduction.p-1-subModValue (if s.basis control then Y^2 else 0) O ∧
    ∀q,q∉L.core.out → (run (fastNR L control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := resA PA O
  let OB := resB PB OA
  let OC := resC PC OB
  let restA := records.drop (measurementCount (fastBranchA L control))
  let restB := restA.drop (measurementCount (fastBranchB L control))
  let u := run (fastBranchA L control) (records.take (measurementCount (fastBranchA L control))) s
  let v := run (fastBranchB L control) (restA.take (measurementCount (fastBranchB L control))) u
  let w := run (fastBranchC L control) restB v
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ea := fastBranchA_correct L hw control hn A O hO s
    (records.take (measurementCount (fastBranchA L control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := fastBranchB_correct L hw control hn B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (fastBranchB L control))) highU ea.2.1 productU cleanU
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ea.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A := regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have sumV : regValue L.core.sum v.basis=B :=
    (regValue_congr _ _ _ (fun q hq => sameV q (sumAway q hq))).trans sumB
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ec := fastBranchC_correct L hw control hn A B OB (ofCast_lt _ _) v
    restB lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have ocBound : OC<SquareReduction.p := ofCast_lt _ _
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out w.basis=
      SquareReduction.p-1-subModValue (if enabled then Y^2 else 0) O := by
    have exactResult := fast_complete_exact enabled A B O
    rw [split] at exactResult
    have hOC : OC=(O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
      rw [ec.2.1]; exact exactResult
    rw [ec.2.1, subModValue, subModValue, hOC]
    omega
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      SquareReduction.p-1-subModValue (if enabled then Y^2 else 0) O ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ec.1.trans (eb.1.trans ea.1),fullValue,sameW⟩
  simpa [fastNR,u,v,w,restA,restB,enabled,run_append,Nat.add_assoc] using final

theorem fast_item_prices (L : CuccaroStreamedSquareWideLayout) :
    (measuredFoldsT false (fastAItems L)=6393 ∧ measuredFoldsM false (fastAItems L)=6393) ∧
    (measuredFoldsT true (fastBItems L)=30941 ∧ measuredFoldsM true (fastBItems L)=30933) ∧
    (measuredFoldsT false (fastCItems L)=6393 ∧ measuredFoldsM false (fastCItems L)=6393) := by
  norm_num [fastAItems,fastBItems,fastCItems,sortedItems,measuredAItems,measuredBItems,measuredCItems,
    nafMinusOneItems,shiftedProductItems,List.filter_cons,measuredFoldsT,measuredFoldsM]

theorem fastProgram_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (fastProgram L control)=95822 ∧ measurementCount (fastProgram L control)=95302 := by
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := L.withMeasuredSquare_counts hw control L.core.low (L.core.product.take 256)
    (L.measuredFolds false (fastAItems L)) (by omega) (by omega) (by omega)
  have b := L.withMeasuredSquare_counts hw control L.core.high (L.core.product.take 256)
    (L.measuredFolds true (fastBItems L)) (by omega) (by omega) (by omega)
  have c := L.withMeasuredSquare_counts hw control L.core.sum L.core.product
    (L.measuredFolds false (fastCItems L)) (by omega) (by omega) (by rw [hw.core.product,su])
  have fa := L.measuredFolds_counts hw false (fastAItems L)
  have fb := L.measuredFolds_counts hw true (fastBItems L)
  have fc := L.measuredFolds_counts hw false (fastCItems L)
  have prices := fast_item_prices L
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  rw [prices.2.2.1,prices.2.2.2] at fc
  have reflection := (L.measured_small_operation_counts hw).2.2
  have sum := L.core.sum_counts hw.core
  simp only [fastProgram,fastBranchA,fastBranchB,fastBranchC,fastMiddleC,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    reflection.1,reflection.2,sum.1.1,sum.1.2,sum.2.1,sum.2.2,lo,hi,su,p256,hw.core.product]
  norm_num [signedSquareRowsCount]

theorem fastNR_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (fastNR L control)=95567 ∧ measurementCount (fastNR L control)=95047 := by
  have full := fastProgram_counts L hw control
  have reflection := (L.measured_small_operation_counts hw).2.2
  rw [fastProgram_split,toffoliCount_append,measurementCount_append] at full
  omega

theorem fastNR_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (fastNR L control)⊆(control::L.wires).toFinset :=
  (fastNR_wires_subset L control).trans (fastProgram_support L hw hn control)

theorem fastNR_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (fastNR L control) := by
  have full := fastProgram_physical L hw control hn
  rw [fastProgram_split,gatePhysical_append] at full
  exact full.1

theorem fastNR_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : Challenge.gateSlots (fastNR L control) ≤ 5000000 := by
  have full := fastProgram_gateSlots_le L hw control
  rw [fastProgram_split,Challenge.gateSlots_append] at full
  omega

theorem fastProgram_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (fastProgram L control)⊆(control::L.wires).toFinset := by
  have items := L.measured_items_support
  have a : ECDSAAdd.wires (L.measuredFolds false (fastAItems L))⊆(control::L.wires).toFinset :=
    L.measuredFolds_support control false (fastAItems L) (fun f hf => items.1 f (fastA_mem L f hf))
  have b : ECDSAAdd.wires (L.measuredFolds true (fastBItems L))⊆(control::L.wires).toFinset :=
    L.measuredFolds_support control true (fastBItems L) (fun f hf => items.2.1 f (fastB_mem L f hf))
  have c : ECDSAAdd.wires (L.measuredFolds false (fastCItems L))⊆(control::L.wires).toFinset :=
    L.measuredFolds_support control false (fastCItems L) (fun f hf => items.2.2 f (fastC_mem L f hf))
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sa : ECDSAAdd.wires (fastBranchA L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.low (L.core.product.take 256)
    (L.measuredFolds false (fastAItems L)) (by omega) (by omega) (by omega)
    (by intro q hq; simp [CuccaroStreamedSquareLayout.low] at hq; exact List.mem_append_left _ (List.mem_of_mem_take hq))
    (fun _ hq => List.mem_of_mem_take hq) a
  have sb : ECDSAAdd.wires (fastBranchB L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.high (L.core.product.take 256)
    (L.measuredFolds true (fastBItems L)) (by omega) (by omega) (by omega)
    (by intro q hq; exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
    (fun _ hq => List.mem_of_mem_take hq) b
  have sc : ECDSAAdd.wires (fastMiddleC L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.sum L.core.product
    (L.measuredFolds false (fastCItems L)) (by omega) (by omega) (by rw [hw.core.product,sum])
    (by
      intro q hq
      simp only [CuccaroStreamedSquareLayout.sum,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl
      · exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq))
      · simp)
    (fun _ hq => hq) c
  have sumCert := L.sum_certified hw hn
  have embed : L.wires.toFinset⊆(control::L.wires).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons] at hq ⊢; exact Or.inr hq
  have prep := sumCert.1.2.trans embed
  have unprep := sumCert.2.2.trans embed
  have reflection : ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
    (L.measured_small_support control).2.2.1
  simpa only [fastProgram,fastBranchC,
    wires_append,Finset.union_subset_iff] using And.intro (And.intro (And.intro sa sb)
      (And.intro (And.intro prep sc) unprep)) reflection

theorem fastProgram_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (fastProgram L control) := by
  have nd := (List.nodup_cons.mp hn).2
  have hc := L.measuredItems_counts hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have a := L.withMeasuredSquare_physical control hn _ _ hl hp _
    (L.measuredFolds_physical hw nd false (fastAItems L) (fun f hf => hc.1 f (fastA_mem L f hf)))
  have b := L.withMeasuredSquare_physical control hn _ _ hb hp _
    (L.measuredFolds_physical hw nd true (fastBItems L) (fun f hf => hc.2.1 f (fastB_mem L f hf)))
  have c := L.withMeasuredSquare_physical control hn _ _ hs (fun _ => le_rfl) _
    (L.measuredFolds_physical hw nd false (fastCItems L) (fun f hf => hc.2.2 f (fastC_mem L f hf)))
  have prep := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).1.1)
  have clear := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).2.1)
  simp only [fastProgram,fastBranchA,fastBranchB,fastBranchC,fastMiddleC,gatePhysical_append]
  exact ⟨⟨⟨a,b⟩,⟨prep,c⟩,clear⟩,L.reflectOutput_physical nd⟩

theorem fastProgram_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : Challenge.gateSlots (fastProgram L control) ≤ 5000000 := by
  have ha := Baselines.measuredFolds_gateSlots_le L hw false (fastAItems L)
  have hb := Baselines.measuredFolds_gateSlots_le L hw true (fastBItems L)
  have hc := Baselines.measuredFolds_gateSlots_le L hw false (fastCItems L)
  have la : (fastAItems L).length = 6 := (sorted_perm _ _).length_eq
  have lb : (fastBItems L).length = 26 := (sorted_perm _ _).length_eq
  have lc : (fastCItems L).length = 6 := (sorted_perm _ _).length_eq
  rw [la] at ha
  rw [lb] at hb
  rw [lc] at hc
  have hd : (L.core.product.take 256).length ≤ 258 := by
    simp only [List.length_take]; omega
  have a := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.low _
    (L.measuredFolds false (fastAItems L)) hd
  have b := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.high _
    (L.measuredFolds true (fastBItems L)) hd
  have c := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.sum L.core.product
    (L.measuredFolds false (fastCItems L)) (by rw [hw.core.product])
  have hp := Baselines.cuccaroAdd_gateSlots_le (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin
  have hl := L.core.low_length hw.core
  simp only [List.length_append, List.length_cons, List.length_nil, hl] at hp
  change Challenge.gateSlots L.core.prepareSum ≤ _ at hp
  have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
  simp only [fastProgram,fastBranchA,fastBranchB,fastBranchC,fastMiddleC,
    CuccaroStreamedSquareLayout.clearSum, Challenge.gateSlots_append, Baselines.reverse_gateSlots]
  omega

end ECDSAAdd.Entrant
