import ECDSAAdd.Arithmetic.MeasuredStreamedFoldProof
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

structure MeasuredFoldView (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (f : MeasuredSquareFold) : Prop where
  count : ∀q,f.src.count q≤L.core.product.count q
  span : f.shift+f.src.length≤256
  canonical : f.canonical=true → regValue f.src base*2^f.shift<SquareReduction.p

def measuredFoldPayload (base : BasisState) (f : MeasuredSquareFold) : Nat :=
  regValue f.src base*2^f.shift

def measuredFoldsValue (base : BasisState) : Bool → Nat → List MeasuredSquareFold → Nat
  | _,O,[] => O
  | orientation,O,f::fs => measuredFoldsValue base f.negative
      ((measuredFoldPayload base f+(if orientation=f.negative then O else SquareReduction.p-1-O))%SquareReduction.p) fs

theorem measuredFoldsValue_lt (base : BasisState) (orientation : Bool) (O : Nat)
    (items : List MeasuredSquareFold) (hO : O<SquareReduction.p) :
    measuredFoldsValue base orientation O items<SquareReduction.p := by
  induction items generalizing orientation O with
  | nil => exact hO
  | cons f fs ih =>
    apply ih
    exact Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])

theorem squareFrame_clean (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
    (base s : BasisState) (O : Nat) (hf : SquareFrame L.core.out base O s)
    (hc : L.PairClean base) : L.PairClean s := by
  have productAway (q : Wire) (hq : q∈L.core.product) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have pair : L.PairFrame base (regValue L.core.product base) O s :=
    ⟨regValue_congr _ _ _ (fun q hq => hf.2 q (productAway q hq)),hf.1,fun q _ hq => hf.2 q hq⟩
  exact PairFrame.clean L hn base _ O s pair hc

theorem measuredFold_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (f : MeasuredSquareFold)
    (hv : L.MeasuredFoldView base f) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (L.measuredFold f)
      (SquareFrame L.core.out base ((measuredFoldPayload base f+O)%SquareReduction.p)) := by
  have away (q : Wire) (hq : q∈f.src) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have count := hv.count q
    simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  intro s m hf
  have source : regValue f.src s.basis=regValue f.src base :=
    regValue_congr _ _ _ (fun q hq => hf.2 q (away q hq))
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  have result := L.measuredFold_correct hw hn f hv.count hv.span O hO s m
    (by rw [source];exact hv.canonical) hf.1 clean
  refine ⟨result.1,?_,?_⟩
  · simpa [measuredFoldPayload,source] using result.2.1
  · intro q hq
    exact (result.2.2 q hq).trans (hf.2 q hq)

theorem measuredReflection_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (hc : L.PairClean base)
    (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) L.reflectOutput
      (SquareFrame L.core.out base (SquareReduction.p-1-O)) := by
  intro s m hf
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  have result := L.reflectOutput_correct hw hn O hO s m hf.1 clean
  refine ⟨result.1,result.2.1,?_⟩
  intro q hq
  exact (result.2.2 q hq).trans (hf.2 q hq)

/-- Functional composition of an arbitrary certified signed fold list.
The retained orientation is an analysis parameter, not an extra qubit. -/
theorem measuredFolds_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (hc : L.PairClean base)
    (orientation : Bool) (O : Nat) (hO : O<SquareReduction.p) (items : List MeasuredSquareFold)
    (views : ∀f∈items,L.MeasuredFoldView base f) :
    Triple (SquareFrame L.core.out base O) (L.measuredFolds orientation items)
      (SquareFrame L.core.out base (measuredFoldsValue base orientation O items)) := by
  induction items generalizing orientation O with
  | nil => intro s m hf;exact ⟨rfl,hf⟩
  | cons f fs ih =>
    let R := if orientation=f.negative then O else SquareReduction.p-1-O
    have rb : R<SquareReduction.p := by
      dsimp [R]
      split
      · exact hO
      · omega
    have prep : Triple (SquareFrame L.core.out base O)
        (if orientation=f.negative then [] else L.reflectOutput) (SquareFrame L.core.out base R) := by
      by_cases same : orientation=f.negative
      · simp only [same,if_true,R]
        intro s m hf;exact ⟨rfl,hf⟩
      · simpa only [same,if_false,R] using L.measuredReflection_frame hw hn base hc O hO
    have fold := L.measuredFold_frame hw hn base f (views f (by simp)) hc R rb
    have ob : (measuredFoldPayload base f+R)%SquareReduction.p<SquareReduction.p :=
      Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    have tail := ih f.negative _ ob (by intro f hf;exact views f (by simp [hf]))
    exact (prep.seq fold).seq tail

def measuredOrientationCast (orientation : Bool) (O : Nat) : ZMod SquareReduction.p :=
  if orientation then -1-(O : ZMod SquareReduction.p) else O

def measuredFinalOrientation : Bool → List MeasuredSquareFold → Bool
  | orientation,[] => orientation
  | _,f::fs => measuredFinalOrientation f.negative fs

def measuredSignedPayload (base : BasisState) (f : MeasuredSquareFold) : ZMod SquareReduction.p :=
  if f.negative then -(measuredFoldPayload base f : ZMod SquareReduction.p) else measuredFoldPayload base f

def measuredSignedSum (base : BasisState) : List MeasuredSquareFold → ZMod SquareReduction.p
  | [] => 0
  | f::fs => measuredSignedPayload base f+measuredSignedSum base fs

theorem measuredReflection_zmod (O : Nat) (hO : O<SquareReduction.p) :
    ((SquareReduction.p-1-O : Nat) : ZMod SquareReduction.p)=-1-(O : ZMod SquareReduction.p) := by
  have hp : 1≤SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  rw [Nat.cast_sub (by omega : O≤SquareReduction.p-1),Nat.cast_sub hp]
  simp only [ZMod.natCast_self,Nat.cast_one,zero_sub]

/-- The full retained-orientation schedule has exactly the same signed
field update as its payload sum. Reflections introduce no residual offset. -/
theorem measuredFoldsValue_cast (base : BasisState) (orientation : Bool) (O : Nat)
    (items : List MeasuredSquareFold) (hO : O<SquareReduction.p) :
    measuredOrientationCast (measuredFinalOrientation orientation items)
      (measuredFoldsValue base orientation O items)=
        measuredOrientationCast orientation O+measuredSignedSum base items := by
  induction items generalizing orientation O with
  | nil => simp [measuredFinalOrientation,measuredFoldsValue,measuredSignedSum]
  | cons f fs ih =>
    let R := if orientation=f.negative then O else SquareReduction.p-1-O
    let V := (measuredFoldPayload base f+R)%SquareReduction.p
    have vb : V<SquareReduction.p :=
      Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    have same : measuredOrientationCast f.negative R=measuredOrientationCast orientation O := by
      cases orientation <;> cases h : f.negative <;>
        simp [R,measuredOrientationCast,h,measuredReflection_zmod O hO]
    have step : measuredOrientationCast f.negative V=
        measuredOrientationCast f.negative R+measuredSignedPayload base f := by
      cases h : f.negative <;>
        simp [V,measuredOrientationCast,measuredSignedPayload,h,ZMod.natCast_mod,Nat.cast_add] <;> ring
    have tail := ih f.negative V vb
    rw [step,same] at tail
    simpa only [measuredFinalOrientation,measuredFoldsValue,measuredSignedSum,R,V,add_assoc] using tail

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
