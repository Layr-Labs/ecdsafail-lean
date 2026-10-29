import ECDSAAdd.Arithmetic.MeasuredStreamedSquare
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.TriangularSquareProof
import ECDSAAdd.Baselines.SlotAlgebra
import ECDSAAdd.Arithmetic.MeasuredStreamedSquareProof
import ECDSAAdd.Arithmetic.MeasuredStreamedSupport
import ECDSAAdd.Arithmetic.MeasuredStreamedPhysical
import ECDSAAdd.Baselines.SlotStreamedSquare
import ECDSAAdd.Math.SquareReduction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ECDSAAdd.Arithmetic.CompressedPointSquareCorrect
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SkywalkSlots
import ECDSAAdd.Baselines.SkywalkCertificate
import Mathlib.Tactic.ReduceModChar
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ComparePhysical
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.CompressedPointDialogSteps
import ECDSAAdd.Arithmetic.CompressedPointDialogResources
import ECDSAAdd.Arithmetic.SkywalkPointPhysical
import ECDSAAdd.Framework.CleanWireRebind
import ECDSAAdd.Arithmetic.CompactWalkPhysical
import ECDSAAdd.Arithmetic.CompressedCompactRestore
import ECDSAAdd.Arithmetic.CompressedCompactStage
import ECDSAAdd.Arithmetic.EntryForwardSelectedFieldSegment
import ECDSAAdd.Arithmetic.BalancedTranscriptBoundary
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptReplay
import ECDSAAdd.Arithmetic.FieldRenameCells
import ECDSAAdd.Arithmetic.MappedCompressedConversionNaturality
import ECDSAAdd.Arithmetic.EntryInverseFirstGroupFrame
import ECDSAAdd.Arithmetic.MappedCompressedGroupsFrame
import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrimForward
import ECDSAAdd.Baselines.SlotField
import ECDSAAdd.Arithmetic.MappedFieldPhysical
import ECDSAAdd.Arithmetic.BalancedTranscriptSupport
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptSupport
import ECDSAAdd.Arithmetic.ParametricPointDialogSteps

section
-- ===== AccBuild =====
/-! Short integer accumulator for fold corrections.
A list of signed shifted sources is summed exactly (no modular reduction)
into a short accumulator by in-place adders/subtractors, then removed again
by the inverse operations in reverse order. -/

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.Acc
open Arithmetic

def tx (Z : List Wire) (w : Nat) (f : MeasuredSquareFold) : List Wire :=
  f.src++Z.take (w-f.shift-f.src.length)
def ty (acc : List Wire) (f : MeasuredSquareFold) : List Wire := acc.drop f.shift
def tc (bank : List Wire) (w : Nat) (f : MeasuredSquareFold) : List Wire := bank.take (w-f.shift-1)

def op (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold) : Program :=
  if neg then subInPlace (tx Z w f) (ty acc f) (tc bank w f) cin
  else addInPlace (tx Z w f) (ty acc f) (tc bank w f) cin

def build (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | [] => []
  | f::fs => op acc Z bank cin w f.negative f++build acc Z bank cin w fs

def unbuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | [] => []
  | f::fs => unbuild acc Z bank cin w fs++op acc Z bank cin w (!f.negative) f

def step (base : BasisState) (neg : Bool) (V : Nat) (f : MeasuredSquareFold) : Nat :=
  if neg then V-regValue f.src base*2^f.shift else V+regValue f.src base*2^f.shift

def accVal (base : BasisState) : Nat → List MeasuredSquareFold → Nat
  | V,[] => V
  | V,f::fs => accVal base (step base f.negative V f) fs

def Valid (base : BasisState) (w : Nat) : Nat → List MeasuredSquareFold → Prop
  | _,[] => True
  | V,f::fs => (if f.negative then regValue f.src base*2^f.shift≤V
      else V+regValue f.src base*2^f.shift<2^w) ∧ Valid base w (step base f.negative V f) fs

structure FitsLen (Z bank : List Wire) (w : Nat) (f : MeasuredSquareFold) : Prop where
  len : f.src.length+f.shift<w
  zpad : w-f.shift-f.src.length≤Z.length
  bankLen : w-f.shift-1≤bank.length

structure Fits (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold) : Prop
    extends FitsLen Z bank w f where
  nd : (cin::(f.src++acc++Z++bank)).Nodup

theorem fits_lengths (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : FitsLen Z bank w f) :
    (tx Z w f).length=(ty acc f).length ∧ (tc bank w f).length+1=(ty acc f).length ∧
      (ty acc f).length=w-f.shift := by
  have l := hf.len; have z := hf.zpad; have b := hf.bankLen
  simp only [tx,ty,tc,List.length_append,List.length_take,List.length_drop,hacc]
  rw [Nat.min_eq_left z,Nat.min_eq_left b]
  refine ⟨?_,?_,?_⟩
  · generalize f.src.length=k at l ⊢
    generalize f.shift=j at l ⊢
    omega
  · generalize f.shift=j at l ⊢
    omega
  · trivial

theorem fits_nodup (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hf : Fits acc Z bank cin w f) :
    (cin::(tx Z w f++ty acc f++tc bank w f)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hf.nd q
  have a := (List.take_sublist (w-f.shift-f.src.length) Z).count_le q
  have b := (List.drop_sublist f.shift acc).count_le q
  have c := (List.take_sublist (w-f.shift-1) bank).count_le q
  simp only [tx,ty,tc,List.count_cons,List.count_append] at h a b c ⊢
  omega

theorem op_wires (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) :
    wires (op acc Z bank cin w neg f)=(cin::(tx Z w f++ty acc f++tc bank w f)).toFinset := by
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  cases neg
  · simp only [op,Bool.false_eq_true,if_false]
    exact addInPlace_wires _ _ _ _ L.1 L.2.1
  · simp only [op,if_true,subInPlace,wires_append,notRegister_wires,addInPlace_wires _ _ _ _ L.1 L.2.1]
    ext q
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto

theorem op_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) :
    wires (op acc Z bank cin w neg f)⊆(cin::(f.src++acc++Z++bank)).toFinset := by
  rw [op_wires acc Z bank cin w neg f hacc hf]
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,tx,ty,tc] at hq ⊢
  rcases hq with h|((h|h)|h)|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inl (Or.inr (List.mem_of_mem_take h)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr (List.mem_of_mem_drop h))))
  · exact Or.inr (Or.inr (List.mem_of_mem_take h))

theorem op_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : FitsLen Z bank w f) :
    toffoliCount (op acc Z bank cin w neg f)=w-f.shift-1 ∧
    measurementCount (op acc Z bank cin w neg f)=w-f.shift-1 := by
  have L := fits_lengths acc Z bank cin w f hacc hf
  have c := addInPlace_counts (tx Z w f) (ty acc f) (tc bank w f) cin L.1 L.2.1
  rw [L.2.2] at c
  have n := notRegister_counts (ty acc f)
  cases neg
  · simpa only [op,Bool.false_eq_true,if_false] using c
  · simp only [op,if_true,subInPlace,toffoliCount_append,measurementCount_append,n.1,n.2,c.1,c.2]
    omega

theorem op_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hf : Fits acc Z bank cin w f) : GatePhysical (op acc Z bank cin w neg f) := by
  have nd := fits_nodup acc Z bank cin w f hf
  have nd' : (cin::tx Z w f++ty acc f++tc bank w f).Nodup := by simpa using nd
  cases neg
  · simpa only [op,Bool.false_eq_true,if_false] using addInPlace_physical _ _ _ _ nd'
  · simpa only [op,if_true] using subInPlace_physical _ _ _ _ nd'

theorem op_gateSlots (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold) :
    Challenge.gateSlots (op acc Z bank cin w neg f)≤12*(tx Z w f).length+2*(ty acc f).length := by
  have a := Baselines.addInPlace_gateSlots_le (tx Z w f) (ty acc f) (tc bank w f) cin
  have b := Baselines.subInPlace_gateSlots_le (tx Z w f) (ty acc f) (tc bank w f) cin
  cases neg
  · simp only [op,Bool.false_eq_true,if_false]; omega
  · simp only [op,if_true]; omega

/-- One exact signed shifted accumulation step. -/
theorem op_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) (base : BasisState)
    (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (neg : Bool) (V : Nat)
    (hok : if neg then regValue f.src base*2^f.shift≤V else V+regValue f.src base*2^f.shift<2^w) :
    Triple (SquareFrame acc base V) (op acc Z bank cin w neg f)
      (SquareFrame acc base (step base neg V f)) := by
  intro s m hs
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  have nd := fits_nodup acc Z bank cin w f hf
  have hnd := List.nodup_iff_count_le_one.mp hf.nd
  have away (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h := hnd q
    have a := List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b := List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  let T := regValue f.src base
  let x := tx Z w f
  let y := ty acc f
  let c := tc bank w f
  have xv : regValue x s.basis=T := by
    have zero : regValue (Z.take (w-f.shift-f.src.length)) s.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have hq' := List.mem_of_mem_take hq
      exact (same q (Or.inl (by simp [hq']))).trans (hz q hq')
    have src : regValue f.src s.basis=T :=
      regValue_congr _ _ _ (fun q hq => same q (Or.inl (by simp [hq])))
    simp only [x,tx,regValue_append,zero,src,Nat.mul_zero,Nat.add_zero]
  have cv : regValue c s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have hq' := List.mem_of_mem_take hq
    exact (same q (Or.inl (by simp [hq']))).trans (hb q hq')
  have iv : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have accNd : acc.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := hnd q
    simp only [List.count_cons,List.count_append] at h
    split at h <;> omega
  have dis := List.disjoint_take_drop accNd (show f.shift≤f.shift by omega)
  have shiftLe : f.shift≤acc.length := by have := hf.len; omega
  have split (t : BasisState) : regValue acc t=regValue (acc.take f.shift) t+2^f.shift*regValue y t := by
    have h := regValue_append (acc.take f.shift) (acc.drop f.shift) t
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left shiftLe] at h
    exact h
  have lowLt : regValue (acc.take f.shift) s.basis<2^f.shift := by
    have h := regValue_lt (acc.take f.shift) s.basis
    rwa [List.length_take,Nat.min_eq_left shiftLe] at h
  have yLt : regValue y s.basis<2^(w-f.shift) := by
    have h := regValue_lt y s.basis; rwa [L.2.2] at h
  have vsplit := split s.basis
  rw [hs.1] at vsplit
  -- the operation's own spec: values of x, y, cin, carry
  have post : (run (op acc Z bank cin w neg f) m s).phase=s.phase ∧
      regValue x (run (op acc Z bank cin w neg f) m s).basis=T ∧
      regValue y (run (op acc Z bank cin w neg f) m s).basis=
        (if neg then (regValue y s.basis+2^y.length-T)%2^y.length
          else (T+regValue y s.basis)%2^y.length) ∧
      (run (op acc Z bank cin w neg f) m s).basis cin=false ∧
      regValue c (run (op acc Z bank cin w neg f) m s).basis=0 := by
    cases neg
    · have h := addInPlace_spec x y c cin nd L.1 L.2.1 T (regValue y s.basis) false s m
        ⟨⟨⟨xv,rfl⟩,iv⟩,cv⟩
      simp only [Holds.holds,Bool.toNat_false,Nat.add_zero] at h
      simp only [op,Bool.false_eq_true,if_false]
      exact ⟨h.1,h.2.1.1.1,h.2.1.1.2,h.2.1.2,h.2.2⟩
    · have h := subInPlace_spec x y c cin nd L.1 L.2.1 T (regValue y s.basis) s m
        ⟨⟨⟨xv,rfl⟩,iv⟩,cv⟩
      simp only [Holds.holds] at h
      simp only [op,if_true]
      exact ⟨h.1,h.2.1.1.1,h.2.1.1.2,h.2.1.2,h.2.2⟩
  let r := run (op acc Z bank cin w neg f) m s
  have frame (q : Wire) (hq : q∉y) : r.basis q=s.basis q := by
    by_cases hx : q∈x
    · exact (regValue_eq_iff x r.basis s.basis).mp (post.2.1.trans xv.symm) q hx
    by_cases hc : q∈c
    · exact ((regValue_zero _ _).mp post.2.2.2.2 q hc).trans ((regValue_zero _ _).mp cv q hc).symm
    by_cases hi' : q=cin
    · subst q; exact post.2.2.2.1.trans iv.symm
    apply run_preserves_outside
    rw [op_wires acc Z bank cin w neg f hacc hf]
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  have lowSame : regValue (acc.take f.shift) r.basis=regValue (acc.take f.shift) s.basis :=
    regValue_congr _ _ _ (fun q hq => frame q (fun hy => List.disjoint_left.mp dis hq hy))
  refine ⟨post.1,?_,?_⟩
  · rw [split r.basis,lowSame,post.2.2.1]
    rw [L.2.2]
    have hok' := hok
    simp only [T] at post ⊢
    generalize hlo : regValue (acc.take f.shift) s.basis=lo at vsplit lowLt
    generalize hY : regValue y s.basis=Y at vsplit yLt ⊢
    generalize hT : regValue f.src base=T0 at hok' ⊢
    have pw : 2^w=2^f.shift*2^(w-f.shift) := by
      rw [←pow_add]; congr 1; have := hf.len; omega
    cases neg
    · simp only [Bool.false_eq_true,if_false] at hok' ⊢
      simp only [step,Bool.false_eq_true,if_false,hT]
      have bound : T0+Y<2^(w-f.shift) := by
        have h1 : 2^f.shift*(T0+Y)<2^f.shift*2^(w-f.shift) := by
          rw [←pw]; rw [vsplit] at hok'; nlinarith
        exact Nat.lt_of_mul_lt_mul_left h1
      rw [Nat.mod_eq_of_lt bound,vsplit]
      ring
    · simp only [if_true] at hok' ⊢
      simp only [step,if_true,hT]
      have le : T0≤Y := by
        by_contra hlt
        have h1 : 2^f.shift*(Y+1)≤2^f.shift*T0 := Nat.mul_le_mul_left _ (by omega)
        rw [vsplit] at hok'
        nlinarith
      have e : Y+2^(w-f.shift)-T0=(Y-T0)+2^(w-f.shift) := by omega
      rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),vsplit,Nat.mul_sub]
      have m1 : 2^f.shift*T0≤2^f.shift*Y := Nat.mul_le_mul_left _ le
      have m2 : T0*2^f.shift=2^f.shift*T0 := Nat.mul_comm _ _
      omega
  · intro q hq
    have hy : q∉y := fun h => hq (List.mem_of_mem_drop h)
    exact (frame q hy).trans (hs.2 q hq)

theorem step_valid_lt (base : BasisState) (w : Nat) (V : Nat) (f : MeasuredSquareFold) (hV : V<2^w)
    (h : if f.negative then regValue f.src base*2^f.shift≤V else V+regValue f.src base*2^f.shift<2^w) :
    step base f.negative V f<2^w := by
  cases hn : f.negative <;> simp only [hn,step,Bool.false_eq_true,if_false,if_true] at h ⊢ <;> omega

theorem accVal_lt (base : BasisState) (w : Nat) (fs : List MeasuredSquareFold) :
    ∀ V,V<2^w → Valid base w V fs → accVal base V fs<2^w := by
  induction fs with
  | nil => intro V hV _; exact hV
  | cons f fs ih =>
    intro V hV hv
    exact ih _ (step_valid_lt base w V f hV hv.1) hv.2

theorem build_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    ∀ V,Valid base w V fs → Triple (SquareFrame acc base V) (build acc Z bank cin w fs)
      (SquareFrame acc base (accVal base V fs)) := by
  induction fs with
  | nil => intro V _ s m h; exact ⟨rfl,h⟩
  | cons f fs ih =>
    intro V hv
    have h1 := op_triple acc Z bank cin w f hacc (hf f (by simp)) base hz hb hi f.negative V hv.1
    have h2 := ih (fun g hg => hf g (by simp [hg])) _ hv.2
    exact h1.seq h2

theorem unbuild_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    ∀ V,V<2^w → Valid base w V fs → Triple (SquareFrame acc base (accVal base V fs))
      (unbuild acc Z bank cin w fs) (SquareFrame acc base V) := by
  induction fs with
  | nil => intro V _ _ s m h; exact ⟨rfl,h⟩
  | cons f fs ih =>
    intro V hV hv
    have V1 := step_valid_lt base w V f hV hv.1
    have h1 := ih (fun g hg => hf g (by simp [hg])) _ V1 hv.2
    have ok : if (!f.negative) then regValue f.src base*2^f.shift≤step base f.negative V f
        else step base f.negative V f+regValue f.src base*2^f.shift<2^w := by
      have := hv.1
      cases hn : f.negative <;> simp only [hn,step,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        if_true,if_false] at this ⊢ <;> omega
    have h2 := op_triple acc Z bank cin w f hacc (hf f (by simp)) base hz hb hi (!f.negative) _ ok
    have back : step base (!f.negative) (step base f.negative V f) f=V := by
      have := hv.1
      cases hn : f.negative <;> simp only [hn,step,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        if_true,if_false] at this ⊢ <;> omega
    rw [back] at h2
    exact h1.seq h2

theorem valid_congr (b1 b2 : BasisState) (w : Nat) (fs : List MeasuredSquareFold)
    (h : ∀f∈fs,regValue f.src b1=regValue f.src b2) :
    ∀ V,(Valid b1 w V fs ↔ Valid b2 w V fs) ∧ accVal b1 V fs=accVal b2 V fs := by
  induction fs with
  | nil => intro V; exact ⟨Iff.rfl,rfl⟩
  | cons f fs ih =>
    intro V
    have e := h f (by simp)
    have t := ih (fun g hg => h g (by simp [hg]))
    have se : step b1 f.negative V f=step b2 f.negative V f := by simp only [step,e]
    simp only [Valid,accVal,e,se]
    exact ⟨and_congr_right (fun _ => (t _).1),(t _).2⟩

theorem accVal_cast (base : BasisState) (w : Nat) (fs : List MeasuredSquareFold) :
    ∀ V,Valid base w V fs →
      (accVal base V fs : ZMod SquareReduction.p)=V+CuccaroStreamedSquareWideLayout.measuredSignedSum base fs := by
  induction fs with
  | nil => intro V _; simp [accVal,CuccaroStreamedSquareWideLayout.measuredSignedSum]
  | cons f fs ih =>
    intro V hv
    rw [accVal,ih _ hv.2]
    have h1 := hv.1
    simp only [CuccaroStreamedSquareWideLayout.measuredSignedSum,
      CuccaroStreamedSquareWideLayout.measuredSignedPayload,
      CuccaroStreamedSquareWideLayout.measuredFoldPayload]
    cases hn : f.negative <;> simp only [hn,step,Bool.false_eq_true,if_false,if_true] at h1 ⊢
    · push_cast; ring
    · rw [Nat.cast_sub h1]; push_cast; ring

def buildT (w : Nat) : List MeasuredSquareFold → Nat
  | [] => 0
  | f::fs => (w-f.shift-1)+buildT w fs

theorem build_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    (toffoliCount (build acc Z bank cin w fs)=buildT w fs ∧
      measurementCount (build acc Z bank cin w fs)=buildT w fs) ∧
    (toffoliCount (unbuild acc Z bank cin w fs)=buildT w fs ∧
      measurementCount (unbuild acc Z bank cin w fs)=buildT w fs) := by
  induction fs with
  | nil => simp [build,unbuild,buildT,toffoliCount,measurementCount]
  | cons f fs ih =>
    have t := ih (fun g hg => hf g (by simp [hg]))
    have a := op_counts acc Z bank cin w f.negative f hacc (hf f (by simp))
    have b := op_counts acc Z bank cin w (!f.negative) f hacc (hf f (by simp))
    simp only [build,unbuild,buildT,toffoliCount_append,measurementCount_append]
    refine ⟨⟨?_,?_⟩,?_,?_⟩ <;> omega

theorem build_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (S : Finset Wire)
    (hS : ∀f∈fs,(cin::(f.src++acc++Z++bank)).toFinset⊆S) :
    wires (build acc Z bank cin w fs)⊆S ∧ wires (unbuild acc Z bank cin w fs)⊆S := by
  induction fs with
  | nil => simp [build,unbuild,wires]
  | cons f fs ih =>
    have t := ih (fun g hg => hf g (by simp [hg])) (fun g hg => hS g (by simp [hg]))
    have a := (op_support acc Z bank cin w f.negative f hacc (hf f (by simp))).trans (hS f (by simp))
    have b := (op_support acc Z bank cin w (!f.negative) f hacc (hf f (by simp))).trans (hS f (by simp))
    simp only [build,unbuild,wires_append,Finset.union_subset_iff]
    exact ⟨⟨a,t.1⟩,⟨t.2,b⟩⟩

theorem build_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    GatePhysical (build acc Z bank cin w fs) ∧ GatePhysical (unbuild acc Z bank cin w fs) := by
  induction fs with
  | nil => simp [build,unbuild,GatePhysical]
  | cons f fs ih =>
    have t := ih (fun g hg => hf g (by simp [hg]))
    simp only [build,unbuild,gatePhysical_append]
    exact ⟨⟨op_physical _ _ _ _ _ _ _ (hf f (by simp)),t.1⟩,⟨t.2,op_physical _ _ _ _ _ _ _ (hf f (by simp))⟩⟩

theorem build_gateSlots (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    Challenge.gateSlots (build acc Z bank cin w fs)≤fs.length*(14*w) ∧
      Challenge.gateSlots (unbuild acc Z bank cin w fs)≤fs.length*(14*w) := by
  induction fs with
  | nil => simp [build,unbuild,Challenge.gateSlots]
  | cons f fs ih =>
    have t := ih (fun g hg => hf g (by simp [hg]))
    have L := fits_lengths acc Z bank cin w f hacc (hf f (by simp))
    have a := op_gateSlots acc Z bank cin w f.negative f
    have b := op_gateSlots acc Z bank cin w (!f.negative) f
    rw [L.1,L.2.2] at a b
    simp only [build,unbuild,Challenge.gateSlots_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    constructor <;> omega

/-! Seeded accumulation: when the first term is positive it is added into a
zero accumulator, so the shifted window can be filled by a plain CX copy
(no Toffoli); the matching last step of the clear is the same copy. -/

def seedOp (acc Z : List Wire) (w : Nat) (f : MeasuredSquareFold) : Program :=
  copyRegister none (tx Z w f) (ty acc f)

def sbuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | [] => []
  | f::fs => (if f.negative then op acc Z bank cin w true f else seedOp acc Z w f)++
      build acc Z bank cin w fs

def sunbuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | [] => []
  | f::fs => unbuild acc Z bank cin w fs++
      (if f.negative then op acc Z bank cin w false f else seedOp acc Z w f)

def sbuildT (w : Nat) : List MeasuredSquareFold → Nat
  | [] => 0
  | f::fs => (if f.negative then w-f.shift-1 else 0)+buildT w fs

theorem seed_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) (base : BasisState)
    (hz : ∀q∈Z,base q=false) (V W : Nat)
    (hVW : (V=0 ∧ W=regValue f.src base*2^f.shift) ∨ (V=regValue f.src base*2^f.shift ∧ W=0)) :
    Triple (SquareFrame acc base V) (seedOp acc Z w f) (SquareFrame acc base W) := by
  intro s m hs
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  have nd := fits_nodup acc Z bank cin w f hf
  have xy : (tx Z w f++ty acc f).Nodup :=
    (List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)
  have hnd := List.nodup_iff_count_le_one.mp hf.nd
  have away (q : Wire) (hq : q∈f.src++Z) : q∉acc := by
    intro bad
    have h := hnd q
    have a := List.count_pos_iff.mpr bad
    have b := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append] at h b
    split at h <;> omega
  have xv : regValue (tx Z w f) s.basis=regValue f.src base := by
    have zero : regValue (Z.take (w-f.shift-f.src.length)) s.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have hq' := List.mem_of_mem_take hq
      exact (hs.2 q (away q (by simp [hq']))).trans (hz q hq')
    have src : regValue f.src s.basis=regValue f.src base :=
      regValue_congr _ _ _ (fun q hq => hs.2 q (away q (by simp [hq])))
    simp only [tx,regValue_append,zero,src,Nat.mul_zero,Nat.add_zero]
  have accNd : acc.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := hnd q
    simp only [List.count_cons,List.count_append] at h
    split at h <;> omega
  have dis := List.disjoint_take_drop accNd (show f.shift≤f.shift by omega)
  have shiftLe : f.shift≤acc.length := by have := hf.len; omega
  have split (t : BasisState) : regValue acc t=regValue (acc.take f.shift) t+2^f.shift*regValue (ty acc f) t := by
    have h := regValue_append (acc.take f.shift) (acc.drop f.shift) t
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left shiftLe] at h
    exact h
  have lowLt : regValue (acc.take f.shift) s.basis<2^f.shift := by
    have h := regValue_lt (acc.take f.shift) s.basis
    rwa [List.length_take,Nat.min_eq_left shiftLe] at h
  have pos : 0<2^f.shift := Nat.two_pow_pos _
  have vs := split s.basis
  rw [hs.1] at vs
  have vmod : V%2^f.shift=0 := by
    rcases hVW with ⟨rfl,_⟩|⟨rfl,_⟩
    · simp
    · exact Nat.mul_mod_left _ _
  have low0 : regValue (acc.take f.shift) s.basis=0 := by
    have h := congrArg (· % 2^f.shift) vs
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lowLt] at h
    omega
  have yv : regValue (ty acc f) s.basis*2^f.shift=V := by
    rw [low0,Nat.zero_add] at vs; rw [vs, Nat.mul_comm]
  have cp := copyRegister_correct none (tx Z w f) (ty acc f) L.1 xy (by simp) s m
  simp only [copyValue] at cp
  let r := run (seedOp acc Z w f) m s
  have lowSame : regValue (acc.take f.shift) r.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => cp.2.1 q (fun hy => List.disjoint_left.mp dis hq hy))).trans low0
  refine ⟨cp.1,?_,?_⟩
  · change regValue acc r.basis=W
    rw [split r.basis,lowSame,Nat.zero_add]
    change 2^f.shift*regValue (ty acc f) (run (copyRegister none (tx Z w f) (ty acc f)) m s).basis=W
    rw [cp.2.2,xv]
    rcases hVW with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have y0 : regValue (ty acc f) s.basis=0 := by
        have := yv; rw [Nat.mul_eq_zero] at this
        rcases this with h|h
        · exact h
        · omega
      rw [y0,Nat.zero_xor,Nat.mul_comm]
    · have yT : regValue (ty acc f) s.basis=regValue f.src base :=
        Nat.eq_of_mul_eq_mul_right pos yv
      rw [yT,Nat.xor_self,Nat.mul_zero]
  · intro q hq
    have hy : q∉ty acc f := fun h => hq (List.mem_of_mem_drop h)
    exact (cp.2.1 q hy).trans (hs.2 q hq)

theorem sbuild_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (hv : Valid base w 0 fs) :
    Triple (SquareFrame acc base 0) (sbuild acc Z bank cin w fs)
      (SquareFrame acc base (accVal base 0 fs)) := by
  cases fs with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons f fs =>
    have hf1 := hf f (by simp)
    have rest := build_triple acc Z bank cin w hacc base hz hb hi fs
      (fun g hg => hf g (by simp [hg])) _ hv.2
    have first : Triple (SquareFrame acc base 0)
        (if f.negative then op acc Z bank cin w true f else seedOp acc Z w f)
        (SquareFrame acc base (step base f.negative 0 f)) := by
      have h1 := hv.1
      cases hn : f.negative
      · simp only [Bool.false_eq_true,if_false]
        apply seed_triple acc Z bank cin w f hacc hf1 base hz
        left; simp [step]
      · simp only [if_true]
        simp only [hn,if_true] at h1
        exact op_triple acc Z bank cin w f hacc hf1 base hz hb hi true 0 (by simpa using h1)
    exact first.seq rest

theorem sunbuild_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (hv : Valid base w 0 fs) :
    Triple (SquareFrame acc base (accVal base 0 fs)) (sunbuild acc Z bank cin w fs)
      (SquareFrame acc base 0) := by
  cases fs with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons f fs =>
    have hf1 := hf f (by simp)
    have V1 := step_valid_lt base w 0 f (Nat.two_pow_pos w) hv.1
    have rest := unbuild_triple acc Z bank cin w hacc base hz hb hi fs
      (fun g hg => hf g (by simp [hg])) _ V1 hv.2
    have last : Triple (SquareFrame acc base (step base f.negative 0 f))
        (if f.negative then op acc Z bank cin w false f else seedOp acc Z w f)
        (SquareFrame acc base 0) := by
      have h1 := hv.1
      have pw := Nat.two_pow_pos w
      cases hn : f.negative
      · simp only [Bool.false_eq_true,if_false]
        apply seed_triple acc Z bank cin w f hacc hf1 base hz
        right; simp [step]
      · simp only [if_true]
        simp only [hn,if_true] at h1
        have h2 := op_triple acc Z bank cin w f hacc hf1 base hz hb hi false (step base true 0 f)
          (by simp only [step,if_true,Bool.false_eq_true,if_false]; omega)
        have back : step base false (step base true 0 f) f=0 := by
          simp only [step,if_true,Bool.false_eq_true,if_false]; omega
        rw [back] at h2; exact h2
    exact rest.seq last

theorem seed_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : FitsLen Z bank w f) :
    toffoliCount (seedOp acc Z w f)=0 ∧ measurementCount (seedOp acc Z w f)=0 := by
  have L := fits_lengths acc Z bank cin w f hacc hf
  have c := copyRegister_counts none (tx Z w f) (ty acc f) L.1
  simpa [seedOp] using c

theorem sbuild_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    (toffoliCount (sbuild acc Z bank cin w fs)=sbuildT w fs ∧
      measurementCount (sbuild acc Z bank cin w fs)=sbuildT w fs) ∧
    (toffoliCount (sunbuild acc Z bank cin w fs)=sbuildT w fs ∧
      measurementCount (sunbuild acc Z bank cin w fs)=sbuildT w fs) := by
  cases fs with
  | nil => simp [sbuild,sunbuild,sbuildT,toffoliCount,measurementCount]
  | cons f fs =>
    have t := build_counts acc Z bank cin w hacc fs (fun g hg => hf g (by simp [hg]))
    have c := seed_counts acc Z bank cin w f hacc (hf f (by simp))
    have a := op_counts acc Z bank cin w true f hacc (hf f (by simp))
    have b := op_counts acc Z bank cin w false f hacc (hf f (by simp))
    cases hn : f.negative <;>
      simp only [sbuild,sunbuild,sbuildT,hn,if_true,Bool.false_eq_true,if_false,
        toffoliCount_append,measurementCount_append] <;> omega

theorem seed_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) :
    wires (seedOp acc Z w f)⊆(cin::(f.src++acc++Z++bank)).toFinset := by
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  have h := op_support acc Z bank cin w false f hacc hf
  rw [op_wires acc Z bank cin w false f hacc hf] at h
  refine Finset.Subset.trans ?_ h
  rw [seedOp,copyRegister_wires none _ _ L.1]
  split
  · exact Finset.empty_subset _
  · intro q hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,Option.toList_none,List.nil_append] at hq ⊢
    tauto

theorem sbuild_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (S : Finset Wire)
    (hS : ∀f∈fs,(cin::(f.src++acc++Z++bank)).toFinset⊆S) :
    wires (sbuild acc Z bank cin w fs)⊆S ∧ wires (sunbuild acc Z bank cin w fs)⊆S := by
  cases fs with
  | nil => simp [sbuild,sunbuild,wires]
  | cons f fs =>
    have t := build_support acc Z bank cin w hacc fs (fun g hg => hf g (by simp [hg])) S
      (fun g hg => hS g (by simp [hg]))
    have hf1 := hf f (by simp)
    have hS1 := hS f (by simp)
    have first (neg : Bool) : wires (if f.negative then op acc Z bank cin w neg f else seedOp acc Z w f)⊆S := by
      split
      · exact (op_support acc Z bank cin w neg f hacc hf1).trans hS1
      · exact (seed_support acc Z bank cin w f hacc hf1).trans hS1
    simp only [sbuild,sunbuild,wires_append,Finset.union_subset_iff]
    exact ⟨⟨first true,t.1⟩,⟨t.2,first false⟩⟩

theorem sbuild_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    GatePhysical (sbuild acc Z bank cin w fs) ∧ GatePhysical (sunbuild acc Z bank cin w fs) := by
  cases fs with
  | nil => simp [sbuild,sunbuild,GatePhysical]
  | cons f fs =>
    have t := build_physical acc Z bank cin w fs (fun g hg => hf g (by simp [hg]))
    have hf1 := hf f (by simp)
    have first (neg : Bool) : GatePhysical (if f.negative then op acc Z bank cin w neg f else seedOp acc Z w f) := by
      split
      · exact op_physical _ _ _ _ _ _ _ hf1
      · have L := fits_lengths acc Z bank cin w f hacc hf1.toFitsLen
        have nd := fits_nodup acc Z bank cin w f hf1
        exact copyRegister_physical none _ _
          ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
    simp only [sbuild,sunbuild,gatePhysical_append]
    exact ⟨⟨first true,t.1⟩,⟨t.2,first false⟩⟩

theorem sbuild_gateSlots (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    Challenge.gateSlots (sbuild acc Z bank cin w fs)≤fs.length*(14*w) ∧
      Challenge.gateSlots (sunbuild acc Z bank cin w fs)≤fs.length*(14*w) := by
  cases fs with
  | nil => simp [sbuild,sunbuild,Challenge.gateSlots]
  | cons f fs =>
    have t := build_gateSlots acc Z bank cin w hacc fs (fun g hg => hf g (by simp [hg]))
    have L := fits_lengths acc Z bank cin w f hacc (hf f (by simp))
    have first (neg : Bool) :
        Challenge.gateSlots (if f.negative then op acc Z bank cin w neg f else seedOp acc Z w f)≤14*w := by
      split
      · have a := op_gateSlots acc Z bank cin w neg f
        rw [L.1,L.2.2] at a; omega
      · have c : Challenge.gateSlots (seedOp acc Z w f)≤(tx Z w f).length := by
          simp [seedOp,Baselines.copyRegister_gateSlots]
        rw [L.1,L.2.2] at c; omega
    have f1 := first true
    have f2 := first false
    simp only [sbuild,sunbuild,Challenge.gateSlots_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    constructor <;> omega

end ECDSAAdd.Entrant.Acc

end

section
-- ===== SquareFolds =====
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

end

section
-- ===== AccFold =====
/-! Accumulated correction fold in the streamed-square workspace, and a fold
schedule mixing ordinary folds with accumulated ones. The accumulator is the
low 163 bits of the fold work register; zero padding comes from the unused
work bits and fold pad; carries come from the fold pad. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- An accumulated fold. `terms` are summed into the 163-bit accumulator; they
may read the 33-bit temporary `wTemp`, which `pre` fills (from product slices)
before the accumulator is built and empties afterwards, on both sides of the
modular addition. `spec` is the original term list whose exact sum the
accumulator must equal; it fixes the payload. Plain items use `pre=[]` and
`spec=terms`. -/
structure AccItem where
  negative : Bool
  pre : List MeasuredSquareFold
  terms : List MeasuredSquareFold
  spec : List MeasuredSquareFold

def accReg (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 163
def wTemp (L : CuccaroStreamedSquareWideLayout) : List Wire := (L.core.work.drop 163).take 33
def accZ (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.drop 196++L.foldPad.drop 160
def accBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.take 160

def tempIn (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  Acc.sbuild (wTemp L) (accZ L) (accBank L) L.core.cin 33 a.pre
def tempOut (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  Acc.sunbuild (wTemp L) (accZ L) (accBank L) L.core.cin 33 a.pre

def fillIn (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  tempIn L a++Acc.sbuild (accReg L) (accZ L) (accBank L) L.core.cin 163 a.terms++tempOut L a
def fillOut (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  tempIn L a++Acc.sunbuild (accReg L) (accZ L) (accBank L) L.core.cin 163 a.terms++tempOut L a

def accFold (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  fillIn L a++L.measuredCore.program SquareReduction.c SquareReduction.p++fillOut L a

def TermOK (f : MeasuredSquareFold) : Prop :=
  f.src.length+f.shift<163 ∧ 163-f.shift-f.src.length≤154 ∧ 163-f.shift-1≤160

def TermOK33 (f : MeasuredSquareFold) : Prop :=
  f.src.length+f.shift<33 ∧ 33-f.shift-f.src.length≤154 ∧ 33-f.shift-1≤160

def SrcOK (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) : Prop :=
  ∀q,f.src.count q≤(L.core.product++wTemp L).count q

structure AccView (L : CuccaroStreamedSquareWideLayout) (base : BasisState) (a : AccItem) : Prop where
  count : ∀f∈a.terms,SrcOK L f
  ok : ∀f∈a.terms,TermOK f
  preCount : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q
  preOk : ∀f∈a.pre,TermOK33 f
  preValid : Acc.Valid base 33 0 a.pre
  specValid : Acc.Valid base 163 0 a.spec
  value : ∀t : BasisState,(∀q∈L.core.product,t q=base q) →
    regValue (wTemp L) t=Acc.accVal base 0 a.pre →
    Acc.Valid t 163 0 a.terms ∧ Acc.accVal t 0 a.terms=Acc.accVal base 0 a.spec

theorem acc_lengths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (accReg L).length=163 ∧ (accZ L).length=154 ∧ (accBank L).length=160 ∧ (wTemp L).length=33 := by
  simp [accReg,accZ,accBank,wTemp,foldPad,hw.core.work,hw.core.pad,hw.overflowPad]

theorem fitsLen_of (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold)
    (ok : TermOK f) : Acc.FitsLen (accZ L) (accBank L) 163 f := by
  have l := acc_lengths L hw
  exact ⟨ok.1,by rw [l.2.1]; exact ok.2.1,by rw [l.2.2.1]; exact ok.2.2⟩

theorem fitsLen33_of (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold)
    (ok : TermOK33 f) : Acc.FitsLen (accZ L) (accBank L) 33 f := by
  have l := acc_lengths L hw
  exact ⟨ok.1,by rw [l.2.1]; exact ok.2.1,by rw [l.2.2.1]; exact ok.2.2⟩

theorem work_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.core.work.take 163).count q+(wTemp L).count q+(L.core.work.drop 196).count q=L.core.work.count q := by
  have h1 := congrArg (List.count q) (List.take_append_drop 163 L.core.work)
  have h2 := congrArg (List.count q) (List.take_append_drop 33 (L.core.work.drop 163))
  have dd : (L.core.work.drop 163).drop 33=L.core.work.drop 196 := by simp [List.drop_drop]
  rw [dd] at h2
  simp only [List.count_append] at h1 h2
  simp only [wTemp]
  omega

theorem pad_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.foldPad.take 160).count q+(L.foldPad.drop 160).count q=L.core.pad.count q+L.overflowPad.count q := by
  rw [←List.count_append,List.take_append_drop]
  simp [foldPad,List.count_append]

theorem fits_of (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (f : MeasuredSquareFold) (hs : SrcOK L f) (ok : TermOK f) :
    Acc.Fits (accReg L) (accZ L) (accBank L) L.core.cin 163 f := by
  refine ⟨fitsLen_of L hw f ok,?_⟩
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have b := hs q
  have e1 := work_split L q
  have e2 := pad_split L q
  simp only [accReg,accZ,accBank,List.count_cons,List.count_append] at b ⊢
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  split <;> split at h <;> omega

theorem fitsPre_of (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (f : MeasuredSquareFold) (hs : ∀q,f.src.count q≤L.core.product.count q) (ok : TermOK33 f) :
    Acc.Fits (wTemp L) (accZ L) (accBank L) L.core.cin 33 f := by
  refine ⟨fitsLen33_of L hw f ok,?_⟩
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have b := hs q
  have e1 := work_split L q
  have e2 := pad_split L q
  simp only [accZ,accBank,List.count_cons,List.count_append] at ⊢
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  split <;> split at h <;> omega

/-- Membership in two disjoint parts of the layout, by counting. -/
theorem layout_count_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 196) :
    q∉accReg L ∧ q∉wTemp L := by
  have h := List.nodup_iff_count_le_one.mp hn q
  have b := List.count_pos_iff.mpr hq
  have e1 := work_split L q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
    List.count_append,List.count_cons,List.count_nil] at h b
  constructor
  · intro bad; have a := List.count_pos_iff.mpr bad; simp only [accReg] at a; omega
  · intro bad; have a := List.count_pos_iff.mpr bad; omega

theorem accReg_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) :
    q∉accReg L := by
  intro bad
  have h := List.nodup_iff_count_le_one.mp hn q
  have a := List.count_pos_iff.mpr bad
  have b := List.count_pos_iff.mpr hq
  have e1 : (L.core.work.take 163).count q+(L.core.work.drop 163).count q=L.core.work.count q := by
    rw [←List.count_append,List.take_append_drop]
  simp only [accReg] at a
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
    List.count_append,List.count_cons,List.count_nil] at h b
  omega

theorem acc_temp_disjoint (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈accReg L) : q∉wTemp L := by
  intro bad
  have h := List.nodup_iff_count_le_one.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  have e1 := work_split L q
  simp only [accReg] at a
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  omega

theorem accReg_work (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈accReg L) : q∈L.core.work :=
  List.mem_of_mem_take hq

theorem wTemp_work (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈wTemp L) : q∈L.core.work :=
  List.mem_of_mem_drop (List.mem_of_mem_take hq)

theorem accZ_mem (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈accZ L) :
    q∈L.foldPad ∨ q∈L.core.work.drop 196 := by
  simp only [accZ,List.mem_append] at hq
  rcases hq with h|h
  · exact Or.inr h
  · exact Or.inl (List.mem_of_mem_drop h)

theorem accZ_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈accZ L) :
    q∉accReg L ∧ q∉wTemp L := by
  apply layout_count_away L hn q
  rcases accZ_mem L q hq with h|h <;> simp [h]

theorem accBank_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈accBank L) :
    q∉accReg L ∧ q∉wTemp L :=
  layout_count_away L hn q (by simp [List.mem_of_mem_take hq])

theorem cin_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    L.core.cin∉accReg L ∧ L.core.cin∉wTemp L :=
  layout_count_away L hn _ (by simp)

theorem product_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.core.product) : q∉accReg L ∧ q∉wTemp L :=
  layout_count_away L hn q (by simp [hq])

/-- Temporary filled, middle step on the accumulator, temporary emptied. -/
theorem fill_core (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (a : AccItem) (hv : AccView L base a)
    (b : BasisState) (agree : ∀q∈L.core.product,b q=base q)
    (hz : ∀q∈accZ L,b q=false) (hb : ∀q∈accBank L,b q=false) (hi : b L.core.cin=false)
    (hW : ∀q∈wTemp L,b q=false) (M : Program) (V0 V1 : Nat)
    (hM : ∀t : BasisState,(∀q∈L.core.product,t q=base q) →
      regValue (wTemp L) t=Acc.accVal base 0 a.pre →
      (∀q∈accZ L,t q=false) → (∀q∈accBank L,t q=false) → t L.core.cin=false →
      Triple (SquareFrame (accReg L) t V0) M (SquareFrame (accReg L) t V1)) :
    Triple (SquareFrame (accReg L) b V0) (tempIn L a++M++tempOut L a)
      (SquareFrame (accReg L) b V1) := by
  have lens := acc_lengths L hw
  have fitsP (f : MeasuredSquareFold) (hf : f∈a.pre) := fitsPre_of L hw hn f (hv.preCount f hf) (hv.preOk f hf)
  have memP (f : MeasuredSquareFold) (hf : f∈a.pre) (q : Wire) (hq : q∈f.src) : q∈L.core.product := by
    have pos := List.count_pos_iff.mpr hq
    have bound := hv.preCount f hf q
    exact List.count_pos_iff.mp (by omega)
  let Wv := Acc.accVal base 0 a.pre
  let Rest (t : BasisState) : Prop := ∀q,q∉accReg L → q∉wTemp L → t q=b q
  have restProd (t : BasisState) (h : Rest t) : ∀q∈L.core.product,t q=base q :=
    fun q hq => (h q (product_away L hn q hq).1 (product_away L hn q hq).2).trans (agree q hq)
  have restZ (t : BasisState) (h : Rest t) : ∀q∈accZ L,t q=false :=
    fun q hq => (h q (accZ_away L hn q hq).1 (accZ_away L hn q hq).2).trans (hz q hq)
  have restB (t : BasisState) (h : Rest t) : ∀q∈accBank L,t q=false :=
    fun q hq => (h q (accBank_away L hn q hq).1 (accBank_away L hn q hq).2).trans (hb q hq)
  have restC (t : BasisState) (h : Rest t) : t L.core.cin=false :=
    (h _ (cin_away L hn).1 (cin_away L hn).2).trans hi
  have preCongr (t : BasisState) (ht : ∀q∈L.core.product,t q=base q) :=
    Acc.valid_congr base t 33 a.pre (fun f hf => regValue_congr _ _ _
      (fun q hq => (ht q (memP f hf q hq)).symm)) 0
  -- step 1: fill the temporary
  have t1 : Triple (SquareFrame (accReg L) b V0) (tempIn L a)
      (fun t => regValue (accReg L) t=V0 ∧ regValue (wTemp L) t=Wv ∧ Rest t) := by
    unfold tempIn
    intro s m hs
    have rs : Rest s.basis := fun q hq _ => hs.2 q hq
    have hW1 : ∀q∈wTemp L,s.basis q=false :=
      fun q hq => (hs.2 q (fun h => acc_temp_disjoint L hn q h hq)).trans (hW q hq)
    have pc := preCongr s.basis (restProd _ rs)
    have h1 := Acc.sbuild_triple (wTemp L) (accZ L) (accBank L) L.core.cin 33 lens.2.2.2 s.basis
      (restZ _ rs) (restB _ rs) (restC _ rs) a.pre fitsP (pc.1.mp hv.preValid)
    obtain ⟨ph,hv1,hf1⟩ := h1 s m ⟨(regValue_zero _ _).mpr hW1,fun _ _ => rfl⟩
    refine ⟨ph,?_,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => hf1 q (acc_temp_disjoint L hn q hq))]; exact hs.1
    · rw [hv1]; exact pc.2.symm
    · intro q h1q h2q; rw [hf1 q h2q]; exact hs.2 q h1q
  -- step 2: the middle program on the accumulator
  have t2 : Triple (fun t => regValue (accReg L) t=V0 ∧ regValue (wTemp L) t=Wv ∧ Rest t) M
      (fun t => regValue (accReg L) t=V1 ∧ regValue (wTemp L) t=Wv ∧ Rest t) := by
    intro s m ⟨ha,hwv,hr⟩
    have h2 := hM s.basis (restProd _ hr) hwv (restZ _ hr) (restB _ hr) (restC _ hr)
    obtain ⟨ph,hv2,hf2⟩ := h2 s m ⟨ha,fun _ _ => rfl⟩
    refine ⟨ph,hv2,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => hf2 q (fun h => acc_temp_disjoint L hn q h hq))]; exact hwv
    · intro q h1q h2q; rw [hf2 q h1q]; exact hr q h1q h2q
  -- step 3: empty the temporary
  have t3 : Triple (fun t => regValue (accReg L) t=V1 ∧ regValue (wTemp L) t=Wv ∧ Rest t) (tempOut L a)
      (SquareFrame (accReg L) b V1) := by
    unfold tempOut
    intro s m ⟨ha,hwv,hr⟩
    have pc := preCongr s.basis (restProd _ hr)
    have h3 := Acc.sunbuild_triple (wTemp L) (accZ L) (accBank L) L.core.cin 33 lens.2.2.2 s.basis
      (restZ _ hr) (restB _ hr) (restC _ hr) a.pre fitsP (pc.1.mp hv.preValid)
    obtain ⟨ph,hv3,hf3⟩ := h3 s m ⟨by rw [hwv]; exact pc.2,fun _ _ => rfl⟩
    refine ⟨ph,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => hf3 q (acc_temp_disjoint L hn q hq))]; exact ha
    · intro q hq
      by_cases hwq : q∈wTemp L
      · rw [(regValue_zero _ _).mp hv3 q hwq]; exact (hW q hwq).symm
      · rw [hf3 q hwq]; exact hr q hq hwq
  exact (t1.seq t2).seq t3

theorem fillIn_triple (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (a : AccItem) (hv : AccView L base a)
    (b : BasisState) (agree : ∀q∈L.core.product,b q=base q)
    (hz : ∀q∈accZ L,b q=false) (hb : ∀q∈accBank L,b q=false) (hi : b L.core.cin=false)
    (hW : ∀q∈wTemp L,b q=false) :
    Triple (SquareFrame (accReg L) b 0) (fillIn L a)
      (SquareFrame (accReg L) b (Acc.accVal base 0 a.spec)) := by
  have lens := acc_lengths L hw
  have fits (f : MeasuredSquareFold) (hf : f∈a.terms) := fits_of L hw hn f (hv.count f hf) (hv.ok f hf)
  apply fill_core L hw hn base a hv b agree hz hb hi hW
  intro t ht hwv tz tb tc
  have val := hv.value t ht hwv
  have tr := Acc.sbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 t tz tb tc a.terms fits val.1
  rwa [val.2] at tr

theorem fillOut_triple (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (a : AccItem) (hv : AccView L base a)
    (b : BasisState) (agree : ∀q∈L.core.product,b q=base q)
    (hz : ∀q∈accZ L,b q=false) (hb : ∀q∈accBank L,b q=false) (hi : b L.core.cin=false)
    (hW : ∀q∈wTemp L,b q=false) :
    Triple (SquareFrame (accReg L) b (Acc.accVal base 0 a.spec)) (fillOut L a)
      (SquareFrame (accReg L) b 0) := by
  have lens := acc_lengths L hw
  have fits (f : MeasuredSquareFold) (hf : f∈a.terms) := fits_of L hw hn f (hv.count f hf) (hv.ok f hf)
  apply fill_core L hw hn base a hv b agree hz hb hi hW
  intro t ht hwv tz tb tc
  have val := hv.value t ht hwv
  have tr := Acc.sunbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 t tz tb tc a.terms fits val.1
  rwa [val.2] at tr

theorem accFold_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFold L a)
      (SquareFrame L.core.out base ((Acc.accVal base 0 a.spec+O)%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFold,List.append_assoc,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let mk := measurementCount (L.measuredCore.program SquareReduction.c SquareReduction.p)
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workNd : L.core.work.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := List.nodup_iff_count_le_one.mp hn q
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
      List.count_append,List.count_cons,List.count_nil] at h
    omega
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := L.measuredCore.program_correct 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A O hAp hO u ((m.drop mb).take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (L.measuredCore.program SquareReduction.c SquareReduction.p) ((m.drop mb).take mk) u
  change v.phase=u.phase ∧ regValue L.core.out v.basis=(A+O)%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u.basis q at ek
  let base2 : BasisState := fun q => if q∈L.core.out then v.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have frame2 : SquareFrame (accReg L) base2 A v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans eu.2.1
    · intro q hq
      by_cases ho : q∈L.core.out
      · simp [base2,ho]
      · rw [b2off q ho,ek.2.2 q ho]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v ((m.drop mb).drop mk) frame2
  refine ⟨eo.1.trans (ek.1.trans eu.1),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) ((m.drop mb).drop mk) v).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq

def accPrice (a : AccItem) : Nat := 4*Acc.sbuildT 33 a.pre+2*Acc.sbuildT 163 a.terms+1023

theorem accFold_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    toffoliCount (accFold L a)=accPrice a ∧ measurementCount (accFold L a)=accPrice a := by
  have b := Acc.sbuild_counts (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have w := Acc.sbuild_counts (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsLen33_of L hw f (okP f hf))
  have k := L.measuredCore.secp_program_counts (L.measuredCore_widths hw) SquareReduction.c SquareReduction.p
  simp only [accFold,fillIn,fillOut,tempIn,tempOut,accPrice,toffoliCount_append,measurementCount_append]
  omega

theorem accFold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFold L a)⊆(control::L.wires).toFinset := by
  have fits (f : MeasuredSquareFold) (hf : f∈a.terms) := fits_of L hw hn f (cnt f hf) (ok f hf)
  have fitsP (f : MeasuredSquareFold) (hf : f∈a.pre) := fitsPre_of L hw hn f (cntP f hf) (okP f hf)
  have inW (q : Wire) (hq : q∈L.core.work∨q∈L.foldPad∨q∈L.core.product∨q=L.core.cin) :
      q∈(control::L.wires).toFinset := by
    simp only [List.mem_toFinset,List.mem_cons,CuccaroStreamedSquareWideLayout.wires,
      CuccaroStreamedSquareLayout.wires,foldPad,List.mem_append] at hq ⊢
    tauto
  have srcIn (f : MeasuredSquareFold) (h : SrcOK L f) (q : Wire) (hq : q∈f.src) :
      q∈L.core.product ∨ q∈wTemp L := by
    have pos := List.count_pos_iff.mpr hq
    have bound := h q
    have mem : q∈L.core.product++wTemp L := List.count_pos_iff.mp (by omega)
    simpa using mem
  have zIn (q : Wire) (hq : q∈accZ L) : q∈(control::L.wires).toFinset := by
    rcases accZ_mem L q hq with h|h
    · exact inW q (Or.inr (Or.inl h))
    · exact inW q (Or.inl (List.mem_of_mem_drop h))
  have b := Acc.sbuild_support (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms fits
    (control::L.wires).toFinset (by
      intro f hf q hq
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
      rcases hq with h|(((h|h)|h)|h)
      · exact inW q (Or.inr (Or.inr (Or.inr h)))
      · rcases srcIn f (cnt f hf) q h with h'|h'
        · exact inW q (Or.inr (Or.inr (Or.inl h')))
        · exact inW q (Or.inl (wTemp_work L q h'))
      · exact inW q (Or.inl (accReg_work L q h))
      · exact zIn q h
      · exact inW q (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have w := Acc.sbuild_support (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre fitsP
    (control::L.wires).toFinset (by
      intro f hf q hq
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
      rcases hq with h|(((h|h)|h)|h)
      · exact inW q (Or.inr (Or.inr (Or.inr h)))
      · have pos := List.count_pos_iff.mpr h
        have bound := cntP f hf q
        exact inW q (Or.inr (Or.inr (Or.inl (List.count_pos_iff.mp (by omega)))))
      · exact inW q (Or.inl (wTemp_work L q h))
      · exact zIn q h
      · exact inW q (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have k : ECDSAAdd.wires (L.measuredCore.program SquareReduction.c SquareReduction.p)⊆
      (control::L.wires).toFinset := (L.measured_small_support control).2.2.2
  simp only [accFold,fillIn,fillOut,tempIn,tempOut,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨w.1,b.1⟩,w.2⟩,k⟩,⟨⟨w.1,b.2⟩,w.2⟩⟩

theorem accFold_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFold L a) := by
  have b := Acc.sbuild_physical (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fits_of L hw hn f (cnt f hf) (ok f hf))
  have w := Acc.sbuild_physical (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsPre_of L hw hn f (cntP f hf) (okP f hf))
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  simp only [accFold,fillIn,fillOut,tempIn,tempOut,gatePhysical_append]
  exact ⟨⟨⟨⟨w.1,b.1⟩,w.2⟩,L.measuredCore.physical _ _ coreNd⟩,⟨⟨w.1,b.2⟩,w.2⟩⟩

theorem accFold_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFold L a)≤2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(66*256+37) := by
  have b := Acc.sbuild_gateSlots (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have w := Acc.sbuild_gateSlots (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsLen33_of L hw f (okP f hf))
  have k := Baselines.canonicalMod_gateSlots_le L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw)
  simp only [accFold,fillIn,fillOut,tempIn,tempOut,Challenge.gateSlots_append]
  omega

/-! Mixed fold schedules. -/

abbrev MixItem := MeasuredSquareFold ⊕ AccItem

def mixNeg : MixItem → Bool
  | .inl f => f.negative
  | .inr a => a.negative

def mixProg (L : CuccaroStreamedSquareWideLayout) : MixItem → Program
  | .inl f => L.measuredFold f
  | .inr a => accFold L a

def mixPayload (base : BasisState) : MixItem → Nat
  | .inl f => measuredFoldPayload base f
  | .inr a => Acc.accVal base 0 a.spec

def MixView (L : CuccaroStreamedSquareWideLayout) (base : BasisState) : MixItem → Prop
  | .inl f => L.MeasuredFoldView base f
  | .inr a => AccView L base a

def mixFolds (L : CuccaroStreamedSquareWideLayout) : Bool → List MixItem → Program
  | _,[] => []
  | o,i::is => (if o=mixNeg i then [] else L.reflectOutput)++mixProg L i++mixFolds L (mixNeg i) is

def mixValue (base : BasisState) : Bool → Nat → List MixItem → Nat
  | _,O,[] => O
  | o,O,i::is => mixValue base (mixNeg i)
      ((mixPayload base i+(if o=mixNeg i then O else SquareReduction.p-1-O))%SquareReduction.p) is

theorem mixValue_lt (base : BasisState) (o : Bool) (O : Nat) (items : List MixItem) (hO : O<SquareReduction.p) :
    mixValue base o O items<SquareReduction.p := by
  induction items generalizing o O with
  | nil => exact hO
  | cons i is ih =>
    apply ih
    exact Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])

theorem mixProg_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (i : MixItem) (hv : MixView L base i) (hc : L.PairClean base)
    (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (mixProg L i)
      (SquareFrame L.core.out base ((mixPayload base i+O)%SquareReduction.p)) := by
  cases i with
  | inl f => exact L.measuredFold_frame hw hn base f hv hc O hO
  | inr a => exact accFold_frame L hw hn base a hv hc O hO

theorem mixFolds_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (hc : L.PairClean base)
    (o : Bool) (O : Nat) (hO : O<SquareReduction.p) (items : List MixItem)
    (views : ∀i∈items,MixView L base i) :
    Triple (SquareFrame L.core.out base O) (mixFolds L o items)
      (SquareFrame L.core.out base (mixValue base o O items)) := by
  induction items generalizing o O with
  | nil => intro s m hf;exact ⟨rfl,hf⟩
  | cons i is ih =>
    let R := if o=mixNeg i then O else SquareReduction.p-1-O
    have rb : R<SquareReduction.p := by
      dsimp [R]
      split
      · exact hO
      · omega
    have prep : Triple (SquareFrame L.core.out base O)
        (if o=mixNeg i then [] else L.reflectOutput) (SquareFrame L.core.out base R) := by
      by_cases same : o=mixNeg i
      · simp only [same,if_true,R]
        intro s m hf;exact ⟨rfl,hf⟩
      · simpa only [same,if_false,R] using L.measuredReflection_frame hw hn base hc O hO
    have fold := mixProg_frame L hw hn base i (views i (by simp)) hc R rb
    have ob : (mixPayload base i+R)%SquareReduction.p<SquareReduction.p :=
      Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    have tail := ih (mixNeg i) _ ob (by intro j hj;exact views j (by simp [hj]))
    exact (prep.seq fold).seq tail

def mixFinal : Bool → List MixItem → Bool
  | o,[] => o
  | _,i::is => mixFinal (mixNeg i) is

def mixSignedPayload (base : BasisState) (i : MixItem) : ZMod SquareReduction.p :=
  if mixNeg i then -(mixPayload base i : ZMod SquareReduction.p) else mixPayload base i

def mixSignedSum (base : BasisState) : List MixItem → ZMod SquareReduction.p
  | [] => 0
  | i::is => mixSignedPayload base i+mixSignedSum base is

theorem mixValue_cast (base : BasisState) (o : Bool) (O : Nat)
    (items : List MixItem) (hO : O<SquareReduction.p) :
    measuredOrientationCast (mixFinal o items) (mixValue base o O items)=
        measuredOrientationCast o O+mixSignedSum base items := by
  induction items generalizing o O with
  | nil => simp [mixFinal,mixValue,mixSignedSum]
  | cons i is ih =>
    let R := if o=mixNeg i then O else SquareReduction.p-1-O
    let V := (mixPayload base i+R)%SquareReduction.p
    have vb : V<SquareReduction.p :=
      Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    have same : measuredOrientationCast (mixNeg i) R=measuredOrientationCast o O := by
      cases o <;> cases h : mixNeg i <;>
        simp [R,measuredOrientationCast,h,measuredReflection_zmod O hO]
    have step : measuredOrientationCast (mixNeg i) V=
        measuredOrientationCast (mixNeg i) R+mixSignedPayload base i := by
      cases h : mixNeg i <;>
        simp [V,measuredOrientationCast,mixSignedPayload,h,ZMod.natCast_mod,Nat.cast_add] <;> ring
    have tail := ih (mixNeg i) V vb
    rw [step,same] at tail
    simpa only [mixFinal,mixValue,mixSignedSum,R,V,add_assoc] using tail

/-- Producer/fold/cleanup contract with a mixed fold schedule. -/
theorem withMixed_contribution (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (hs2 : 2≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (orientation : Bool) (items : List MixItem)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (O P V : Nat) (hO : O<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O)
    (hp : P=(if s.basis control then regValue src s.basis else 0)^2)
    (whole : ∀t : BasisState,regValue dst t=P → (∀q,q∉dst → t q=s.basis q) → regValue L.core.product t=P)
    (views : ∀t : BasisState,regValue L.core.product t=P → ∀i∈items,MixView L t i)
    (delta : ZMod SquareReduction.p)
    (payload : ∀t : BasisState,regValue L.core.product t=P → mixSignedSum t items=delta)
    (hV : V<SquareReduction.p)
    (target : measuredOrientationCast (mixFinal orientation items) V=
      measuredOrientationCast orientation O+delta) :
    (run (L.withMeasuredSquare control src dst (mixFolds L orientation items)) records s).phase=s.phase ∧
    regValue L.core.out (run (L.withMeasuredSquare control src dst (mixFolds L orientation items)) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (L.withMeasuredSquare control src dst (mixFolds L orientation items)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  apply L.withMeasuredSquare_correct hw control hn src dst hs hd hs2 hsmax hlen
    (mixFolds L orientation items) s records hc hzero V
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
  have folded := mixFolds_frame L hw nd t.basis clean orientation O hO items (views t.basis pv) t m initial
  have cast := mixValue_cast t.basis orientation O items hO
  rw [payload t.basis pv] at cast
  have result : mixValue t.basis orientation O items=V :=
    measuredOrientationCast_injective _ _ _ (mixValue_lt _ _ _ _ hO) hV (cast.trans target.symm)
  exact ⟨folded.1,folded.2.1.trans result,folded.2.2⟩

def mixFoldsT : Bool → List MixItem → Nat
  | _,[] => 0
  | o,i::is => (if o=mixNeg i then 0 else 255)+
      (match i with
        | .inl f => 1023+(if f.canonical then 0 else 1022)
        | .inr a => accPrice a)+mixFoldsT (mixNeg i) is

def mixFoldsM : Bool → List MixItem → Nat
  | _,[] => 0
  | o,i::is => (if o=mixNeg i then 0 else 255)+
      (match i with
        | .inl f => 1023+(if f.canonical then 0 else 1020)
        | .inr a => accPrice a)+mixFoldsM (mixNeg i) is

def MixStatic (L : CuccaroStreamedSquareWideLayout) : MixItem → Prop
  | .inl f => ∀q,f.src.count q≤L.core.product.count q
  | .inr a => (∀f∈a.terms,SrcOK L f) ∧ (∀f∈a.terms,TermOK f) ∧
      (∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) ∧ (∀f∈a.pre,TermOK33 f)

theorem mixFolds_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    toffoliCount (mixFolds L o items)=mixFoldsT o items ∧
    measurementCount (mixFolds L o items)=mixFoldsM o items := by
  induction items generalizing o with
  | nil => simp [mixFolds,mixFoldsT,mixFoldsM,toffoliCount,measurementCount]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have reflect := (L.measured_small_operation_counts hw).2.2
    have hi := hst i (by simp)
    cases i with
    | inl f =>
      have op := L.measuredFold_counts hw f
      by_cases same : o=mixNeg (.inl f) <;>
        simp only [mixFolds,mixFoldsT,mixFoldsM,same,if_true,if_false,mixProg,toffoliCount_append,
          measurementCount_append,op.1,op.2,reflect.1,reflect.2,t.1,t.2] <;>
        simp [toffoliCount,measurementCount] <;> omega
    | inr a =>
      have op := accFold_counts L hw a hi.2.1 hi.2.2.2
      by_cases same : o=mixNeg (.inr a) <;>
        simp only [mixFolds,mixFoldsT,mixFoldsM,same,if_true,if_false,mixProg,toffoliCount_append,
          measurementCount_append,op.1,op.2,reflect.1,reflect.2,t.1,t.2] <;>
        simp [toffoliCount,measurementCount] <;> omega

theorem mixFolds_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    ECDSAAdd.wires (mixFolds L o items)⊆(control::L.wires).toFinset := by
  induction items generalizing o with
  | nil => simp [mixFolds,ECDSAAdd.wires]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have reflect : ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
      (L.measured_small_support control).2.2.1
    have hi := hst i (by simp)
    have mem (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) :
        ∀q∈f.src,q∈L.core.product := by
      intro q hq
      have pos := List.count_pos_iff.mpr hq
      have b := h q
      exact List.count_pos_iff.mp (by omega)
    have hprog : ECDSAAdd.wires (mixProg L i)⊆(control::L.wires).toFinset := by
      cases i with
      | inl f => exact L.measuredFold_support control f (mem f hi)
      | inr a => exact accFold_support L hw hn control a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    by_cases same : o=mixNeg i <;>
      simp only [mixFolds,same,if_false,if_true,wires_append,ECDSAAdd.wires,Finset.union_subset_iff,
        Finset.empty_subset] <;> tauto

theorem mixFolds_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    GatePhysical (mixFolds L o items) := by
  induction items generalizing o with
  | nil => simp [mixFolds,GatePhysical]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have hi := hst i (by simp)
    have hprog : GatePhysical (mixProg L i) := by
      cases i with
      | inl f => exact L.measuredFold_physical hw hn f hi
      | inr a => exact accFold_physical L hw hn a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    have hr := L.reflectOutput_physical hn
    simp only [mixFolds,gatePhysical_append]
    refine ⟨⟨?_,hprog⟩,t⟩
    split
    · simp [GatePhysical]
    · exact hr

theorem mixFolds_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) (B : Nat)
    (hB : ∀i∈items,∀a,i=.inr a → a.terms.length≤B ∧ a.pre.length≤4) :
    Challenge.gateSlots (mixFolds L o items)≤ items.length*(41000+2*(B*(14*163))+(66*256+37)) := by
  induction items generalizing o with
  | nil => simp [mixFolds,Challenge.gateSlots]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj])) (fun j hj a e => hB j (by simp [hj]) a e)
    have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
    have hi := hst i (by simp)
    have hprog : Challenge.gateSlots (mixProg L i)≤36000+2*(B*(14*163))+(66*256+37) := by
      cases i with
      | inl f => have := Baselines.measuredFold_gateSlots_le L hw f; simp only [mixProg]; omega
      | inr a =>
        have h1 := accFold_gateSlots L hw a hi.2.1 hi.2.2.2
        have h2 := hB (.inr a) (by simp) a rfl
        have h3 : a.terms.length*(14*163)≤B*(14*163) := Nat.mul_le_mul_right _ h2.1
        have h4 : a.pre.length*(14*33)≤4*(14*33) := Nat.mul_le_mul_right _ h2.2
        simp only [mixProg]; omega
    simp only [mixFolds,Challenge.gateSlots_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    split
    · simp only [Baselines.gateSlots_nil]; omega
    · omega

end ECDSAAdd.Entrant

end

section
-- ===== RotCert =====
set_option maxRecDepth 100000

/-! Rotated 128-bit squares stay canonical.

For a square `P < 2^256` and `N2 = 2^(256-j)`, the left rotation by `j` of `P` is
`P / N2 + 2^j * (P % N2)`.  It can reach `p` only when the top part `h = P / N2`
and the low part force `P` into the interval `[rotLo h, rotHi h]`.  For each
`h < 2^j` a certificate `r` with `r*r < rotLo h` and `rotHi h < (r+1)*(r+1)`
shows that interval contains no square.  `certOK` checks the whole certificate
list by kernel evaluation of natural-number arithmetic. -/
namespace ECDSAAdd.Entrant
open Arithmetic

def rotLo (B N2 h : Nat) : Nat := h*N2 + (SquareReduction.p - h + B - 1)/B
def rotHi (N2 h : Nat) : Nat := h*N2 + N2 - 1

def certOK (B N2 : Nat) : Nat → List Nat → Bool
  | h, [] => h == B
  | h, r :: rs =>
      (decide (r*r < rotLo B N2 h) && decide (rotHi N2 h < (r+1)*(r+1))) && certOK B N2 (h+1) rs

theorem certOK_spec (B N2 : Nat) : ∀ (h0 : Nat) (rs : List Nat), certOK B N2 h0 rs = true →
    ∀ h, h0 ≤ h → h < B → ∃ r, r*r < rotLo B N2 h ∧ rotHi N2 h < (r+1)*(r+1) := by
  intro h0 rs
  induction rs generalizing h0 with
  | nil =>
    intro hc h hh hb
    simp only [certOK, beq_iff_eq] at hc
    omega
  | cons r rs ih =>
    intro hc h hh hb
    simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases e : h = h0
    · subst e; exact ⟨r, hc.1.1, hc.1.2⟩
    · exact ih (h0+1) hc.2 h (by omega) hb

/-- A square below `2^256` rotated with a valid certificate list stays below `p`. -/
theorem rot_lt_p (B N2 : Nat) (hB : 0 < B) (hN : 0 < N2) (hBN : B*N2 = 2^256)
    (cert : List Nat) (hc : certOK B N2 0 cert = true) (Y : Nat) (hb : Y*Y < 2^256) :
    (Y*Y) / N2 + B * ((Y*Y) % N2) < SquareReduction.p := by
  by_contra hge
  push_neg at hge
  have hdiv : N2 * ((Y*Y) / N2) + (Y*Y) % N2 = Y*Y := Nat.div_add_mod (Y*Y) N2
  have hhB : (Y*Y) / N2 < B := by
    rw [Nat.div_lt_iff_lt_mul hN]; rw [hBN]; exact hb
  obtain ⟨r, hr1, hr2⟩ := certOK_spec B N2 0 cert hc ((Y*Y) / N2) (Nat.zero_le _) hhB
  generalize hh : (Y*Y) / N2 = h at hdiv hhB hr1 hr2 hge
  generalize hL : (Y*Y) % N2 = L at hdiv hge
  have hLlt : L < N2 := by rw [← hL]; exact Nat.mod_lt _ hN
  have hlo : rotLo B N2 h ≤ Y*Y := by
    unfold rotLo
    have hq : (SquareReduction.p - h + B - 1)/B ≤ L := by
      apply Nat.lt_succ_iff.mp
      rw [Nat.div_lt_iff_lt_mul hB, Nat.succ_mul]
      have e : B * L = L * B := Nat.mul_comm B L
      omega
    have e2 : h * N2 = N2 * h := Nat.mul_comm h N2
    omega
  have hhi : Y*Y ≤ rotHi N2 h := by
    unfold rotHi
    have e2 : h * N2 = N2 * h := Nat.mul_comm h N2
    omega
  have a := Nat.mul_self_lt_mul_self_iff.mp (lt_of_lt_of_le hr1 hlo)
  have b := Nat.mul_self_lt_mul_self_iff.mp (lt_of_le_of_lt hhi hr2)
  omega

/-- Certificates for the rotation by 4: `r_h = isqrt (rotHi h)` for `h < 2^4`. -/
def rotCert4 : List Nat := [
  85070591730234615865843651857942052863, 120307984584002255772516886238812528463, 147346587106715120692043727842883538658, 170141183460469231731687303715884105727,
  190223625994936052448711836799948219418, 208379541855705147060497221923602346553, 225075629603308753018814965684675446837, 240615969168004511545033772477625056927,
  255211775190703847597530955573826158591, 269016831765825801719526439316123156306, 282147233462699194961827797147224560430, 294693174213430241384087455685767077316,
  306726380517423719006373237817322128119, 318305007944662521603433860153578694457, 329476985023209069078162071863942203380, 340282366920938463463374607431768211455]

theorem rotCert4_ok : certOK (2^4) (2^252) 0 rotCert4 = true := by decide +kernel

theorem rot4_canonical (Y : Nat) (hb : Y*Y < 2^256) :
    (Y*Y) / 2^252 + 2^4 * ((Y*Y) % 2^252) < SquareReduction.p :=
  rot_lt_p (2^4) (2^252) (by positivity) (by positivity) (by norm_num) rotCert4 rotCert4_ok Y hb

/-- Certificates for the rotation by 6: `r_h = isqrt (rotHi h)` for `h < 2^6`. -/
def rotCert6 : List Nat := [
  42535295865117307932921825928971026431, 60153992292001127886258443119406264231, 73673293553357560346021863921441769329, 85070591730234615865843651857942052863,
  95111812997468026224355918399974109709, 104189770927852573530248610961801173276, 112537814801654376509407482842337723418, 120307984584002255772516886238812528463,
  127605887595351923798765477786913079295, 134508415882912900859763219658061578153, 141073616731349597480913898573612280215, 147346587106715120692043727842883538658,
  153363190258711859503186618908661064059, 159152503972331260801716930076789347228, 164738492511604534539081035931971101690, 170141183460469231731687303715884105727,
  175377517668776787853951800790642601648, 180461976876003383658775329358218792695, 185407056209649813630662448518363628108, 190223625994936052448711836799948219418,
  194921213009242215272059206077382237867, 199508222074498579239763080511020768050, 203992112763362759702255349553060103316, 208379541855705147060497221923602346553,
  212676479325586539664609129644855132159, 216888303632675647313601872656300690638, 221019880660072681038065591764325307987, 225075629603308753018814965684675446837,
  229059578353883514371252488813878024045, 232975410354809691028999546292736078212, 236826504480231334090187096672132418653, 240615969168004511545033772477625056927,
  244346671786196349790200515401475186231, 248021264022511240847206814133050500226, 251642203935781198228857763314028473402, 255211775190703847597530955573826158591,
  258732103903484357453253474976449672980, 262205173451357536391972035370709648437, 265632837538941251634075828277143597658, 269016831765825801719526439316123156306,
  272358783900309864218087857043330409306, 275660223031885311660837236230928240409, 278922587748503829917427540838876006752, 282147233462699194961827797147224560430,
  285335438992404078673067755199922329127, 288488412487089358763283015427614820925, 291607296777110982179066369266086494232, 294693174213430241384087455685767077316,
  297747071055821155530452781502797185023, 300769961460005639431292215597031321158, 303762771107629881702280654470904942690, 306726380517423719006373237817322128119,
  309661628071113251284217280308471805592, 312569312783557720590745832885403519830, 315450196843049386996416775608544988928, 318305007944662521603433860153578694457,
  321134441436892185223825193844146861358, 323939162299524695956483584526126981093, 326719806968679001232275300715203276489, 329476985023209069078162071863942203380,
  332211280745126111021694046270932974510, 334923254565355709814280786110416129476, 337613444404963129528222448527013170255, 340282366920938463463374607431768211455]

theorem rotCert6_ok : certOK (2^6) (2^250) 0 rotCert6 = true := by decide +kernel

theorem rot6_canonical (Y : Nat) (hb : Y*Y < 2^256) :
    (Y*Y) / 2^250 + 2^6 * ((Y*Y) % 2^250) < SquareReduction.p :=
  rot_lt_p (2^6) (2^250) (by positivity) (by positivity) (by norm_num) rotCert6 rotCert6_ok Y hb

/-- Certificates for the rotation by 10: `r_h = isqrt (rotHi h)` for `h < 2^10`. -/
def rotCert10 : List Nat := [
  10633823966279326983230456482242756607, 15038498073000281971564610779851566057, 18418323388339390086505465980360442332, 21267647932558653966460912964485513215,
  23777953249367006556088979599993527427, 26047442731963143382562152740450293319, 28134453700413594127351870710584430854, 30076996146000563943129221559703132115,
  31901471898837980949691369446728269823, 33627103970728225214940804914515394538, 35268404182837399370228474643403070053, 36836646776678780173010931960720884664,
  38340797564677964875796654727165266014, 39788125993082815200429232519197336807, 41184623127901133634770258982992775422, 42535295865117307932921825928971026431,
  43844379417194196963487950197660650412, 45115494219000845914693832339554698173, 46351764052412453407665612129590907027, 47555906498734013112177959199987054854,
  48730303252310553818014801519345559466, 49877055518624644809940770127755192012, 50998028190840689925563837388265025829, 52094885463926286765124305480900586638,
  53169119831396634916152282411213783039, 54222075908168911828400468164075172659, 55254970165018170259516397941081326996, 56268907400827188254703741421168861709,
  57264894588470878592813122203469506011, 58243852588702422757249886573184019553, 59206626120057833522546774168033104663, 60153992292001127886258443119406264231,
  61086667946549087447550128850368796557, 62005316005627810211801703533262625056, 62910550983945299557214440828507118350, 63802943797675961899382738893456539647,
  64683025975871089363313368744112418245, 65551293362839384097993008842677412109, 66408209384735312908518957069285899414, 67254207941456450429881609829030789076,
  68089695975077466054521964260832602326, 68915055757971327915209309057732060102, 69730646937125957479356885209719001688, 70536808365674798740456949286806140107,
  71333859748101019668266938799980582281, 72122103121772339690820753856903705231, 72901824194277745544766592316521623558, 73673293553357560346021863921441769329,
  74436767763955288882613195375699296255, 75192490365001409857823053899257830289, 75940692776907470425570163617726235672, 76681595129355929751593309454330532029,
  77415407017778312821054320077117951398, 78142328195889430147686458221350879957, 78862549210762346749104193902136247232, 79576251986165630400858465038394673614,
  80283610359223046305956298461036715339, 80984790574881173989120896131531745273, 81679951742169750308068825178800819122, 82369246255802267269540517965985550845,
  83052820186281527755423511567733243627, 83730813641338927453570196527604032369, 84403361101240782382055612131753292563, 85070591730234615865843651857942052863,
  85732629666178319151235667203935475380, 86389594290191543925699642002929328613, 87041600477988179082073860895186456611, 87688758834388393926975900395321300824,
  88331175912365987246451476950740602474, 88968954417859501989461455287242856883, 89602193401461877347437606131173517257, 90230988438001691829387664679109396347,
  90855431794937894003754770589036446577, 91475612590408096074420234834267234969, 92091616941696950432527329901802211661, 92703528104824906815331224259181814054,
  93311426605897940135831683800530642542, 93915390364804929416771759117077744496, 94515494811800626632459302190721262802, 95111812997468026224355918399974109709,
  95704415696513942849074108340184809471, 96293371505815294937613268783965082473, 96878746937100593150684230783613621955, 97460606504621107636029603038691118933,
  98039012808138836098454154115084970993, 98614026611533449491522177570809842251, 99185706917307616410304814283328547768, 99754111037249289619881540255510384025,
  100319294659490489966858998267591051868, 100881311912184675644822414743546183615, 101440215424008787617956412390675090648, 101996056381681379851127674776530051658,
  102548884584674754665468704570670082983, 103098748497286620199690180208776580996, 103645695298225370744670471111804453001, 104189770927852573530248610961801173276,
  104731020133216547973592075349842287743, 105269486511001973800952275458960962405, 105805212548512198110685423930209210161, 106338239662793269832304564822427566079,
  106868608238001660177802843644280841454, 107396357661111081572589580048653690706, 107921526356047751649856654500879263045, 108444151816337823656800936328150345319,
  108964270636345484119997243339852359991, 109481918541175370160314093953336572724, 109997130415308452668289210942862264587, 110509940330036340519032795882162653993,
  111020381569755060372888895709465855331, 111528486657175733777944718709129052661, 112034287377506187614015090569593809066, 112537814801654376509407482842337723418,
  113039099308501549434559813334360681802, 113538170606290341393787483530978863730, 114035057753170400478106559148369887933, 114529789176941757185626244406939012022,
  115022392694033894627389964181495798044, 115512895527756373773189013518293919470, 116001324325854896914473924118812815030, 116487705177404845514499773146368039106,
  116972063629072596815535021304670322687, 117454424700773298902317934109332799149, 117934812900752258930658599587897845119, 118413252240115667045093548336066209326,
  118889766246835032780444897999967637136, 119364377979248445601287697557592010421, 119837110039080581254528544016317791164, 120307984584002255772516886238812528463,
  120777023339749274618277909377214560099, 121244247611819331303241716078434769919, 121709678296764773838104457293229142782, 122173335893098174895100257700737593115,
  122635240511826809126994597088091329274, 123095411886631355511665657422101680279, 123553869383703400904310776948978326267, 124010632011255620423603407066525250113,
  124465718428717848307384363577127638186, 124919146955631627059185454609077069589, 125370935580255230844680553925818150011, 125821101967890599114428881657014236701,
  126269663468943086393808061284496995255, 126716637126724432290583619053040885394, 127162039685008880343249185307917680376, 127605887595351923798765477786913079295,
  128048197024180729299719437429595255261, 128488983859664884407259330412768868952, 128928263718375730605538261862523096326, 129366051951742178726626737488224836490,
  129802363652310557479594040856350627018, 130237213659815716912810763702251466596, 130670616567070296200043421448225912051, 131102586725678768195986017685354824218,
  131533138251582590890463850592981951236, 131962285030442527391239976987954583436, 132390040722863940621719105743186974597, 132816418769470625817037914138571798829,
  133241432395832512468680145077534976981, 133665094617252346973046846784762584290, 134087418243416257290404984359872233197, 134508415882912900859763219658061578153,
  134928099947625706317969462287557034034, 135346482657002537744081497018664094521, 135763576042206936728123359168803558127, 136179391950154932109043928521665204653,
  136593942047441249327693278923280732090, 137007237824158600608285946571145645724, 137419290597613593249696883352861744490, 137830111515942655830418618115464120204,
  138239711561631250781995934269155835903, 138648101554939516257450976930543233054, 139055292157237360222996836388772721081, 139461293874251914958713770419438003376,
  139866117059230150407471665245893249237, 140269771916019339816089704927116173812, 140672268502067970636759353552922154273, 141073616731349597480913898573612280215,
  141473826377212041834617060485007628099, 141872907075154255057890521250674255714, 142270868325533076714392689771781663904, 142667719496202039336533877599961164563,
  143063469825084293157776103670948134087, 143458128422681649980566008983331351047, 143851704274521674045367689242075150054, 144244206243544679381641507713807410462,
  144635643072432427520717648595969320706, 145026023385880256505606587198529767136, 145415355692814311722655540610392645118, 145803648388555491089533184633043247116,
  146190909756931661454044404558036678400, 146577147972339649584967373713505100983, 146962371101758459770873744661281035206, 147346587106715120692043727842883538658,
  147729803845204516805055969314155218447, 148112029073564513894730603091853074022, 148493270448307644623287670146908451855, 148873535527910577765226390751398592511,
  149252831774562554285617082827417880885, 149631166555873934429822310383265576037, 150008547146545962478048526964414245861, 150384980730002819715646107798515660579,
  150760474399987001419781745130253503955, 151135035162119020207889895868414091270, 151508669935422405878739267750029449377, 151881385553814940851140327235452471345,
  152253188767567040418798001367545769278, 152624086244728158245397527922330370843, 152994084572522069776691512164795077487, 153363190258711859503186618908661064059,
  153731409732935412227022094338387510395, 154098749348012183630663472987059069213, 154465215381222001475745315995122939981, 154830814035556625642108640154235902796,
  155195551440944772915710769210258249202, 155559433655451290917074915686132123294, 155922466666451144798175027604503451164, 156284656391778860295372916442701759915,
  156646008680854047380800798496888326984, 157006529315783610077218121091526916869, 157366224012441229965855676778993695220, 157725098421524693498208387804272494464,
  158083158129591616397339977260678597465, 158440408660074102179229652459741451948, 158796855474272856118208637948402379872, 159152503972331260801716930076789347228,
  159507359494189904748456847233641349119, 159861427320522041381372243222448754666, 160214712673650441934387486750896987835, 160567220718446092611912596922073430679,
  160918956563209173495906333934164636517, 161269925260532744290632082712656673156, 161620131808149549994653126145600496811, 161969581149762347978241792263063490546,
  162318278175858146707975932838304305087, 162666227724506735485201404492225517978, 163013434582143874038140023266547641340, 163359903484339500616137650357601638244,
  163705639116551307366801363642574286123, 164050646114864022220976331694954710308, 164394929066714727255532510186441302089, 164738492511604534539081035931971101690,
  165081340941796931780755232359436415351, 165423478803003101687210718578367226637, 165764910495054510778549193823243980990, 166105640372563055510847023135466487255,
  166445672745569045892622857199954691990, 166785011880177299356497202105288763286, 167123661999181610447394627848342152402, 167461627282677854907140393055208064738,
  167798911868665979964729461872834748616, 168135519853641126074704024572576972691, 168471455293174118976045606701009670572, 168806722202481564764111224263506585127,
  169141324556985774672012145136831997849, 169475266292864740439281352063224509948, 169808551307592375498764917165894767142, 170141183460469231731687303715884105727,
  170473166573143896220277130060632893550, 170804504430125267261897446203023907131, 171135200779285903893197364907035423989, 171465259332356638302471334407870950760,
  171794683765412635778439366610408518034, 172123477719351082249479404134277321767, 172451644800360675004550415995933420682, 172779188580383087851399284005858657226,
  173106112597566577755056132167968603481, 173432420356711895906147996930703269668, 173758115329710662190396882846780948878, 174083200955976358164147721790372913222,
  174407680642868089882356868641908474071, 174731557766107268271749659719552058659, 175054835670187351189533342962056088341, 175377517668776787853951800790642601648,
  175699607045115302974024248587369552565, 176021107052403654639061444925175345579, 176342020914186996851142373217015350269, 176662351824731974492902953901481204949,
  176982102949397675516072104900894219042, 177301277425000562210616653522122601413, 177619878360173500567640322504099313989, 177937908835719003978922910574485713766,
  178255371904956804819864877068926108790, 178572270594065864838379165833633658937, 178888607902420932717781028185394352110, 179204386802923754694875212262347034515,
  179519610242329041693205499849301990627, 179834281141565294073858879462976907436, 180148402396050582810415227411166149800, 180461976876003383658775329358218792695,
  180775007426748558714917760198126862335, 181087496869018577632418953276365366954, 181399447999250068705167091403963766956, 181710863589875788007509541178072893154,
  182021746389612092822547729710178859200, 182332099123742003677935069183152053234, 182641924494393937445893560097330630017, 182951225180816192148840469668534469938,
  183260003839647262342650386551106389673, 183568263105182062224855784903013184980, 183876005589634131933738639342754331830, 184183233883393900865054659803604423322,
  184489950555283080234867383993516756557, 184796158152805255558496318868441406989, 185101859202392748195782519429384141369, 185407056209649813630662448518363628108,
  185711751659592242707366537550895861432, 186015948016883430635405110599787875170, 186319647726066977199885350562139132596, 186622853211795880271663367601061285084,
  186925566879058383402449213246101815028, 187227791113400537012352350565439315521, 187529528281145531430610606590410107749, 187830780729609858833543518234155488993,
  188131550787316359936293420512261256141, 188431840764204210135871601597528025399, 188731652951835898671643322485521355052, 189030989623601253264918604381442525604,
  189329853034918561621041964653587477329, 189628245423432840124591936816009773028, 189926169009211299030329395380320858152, 190223625994936052448711836799948219418,
  190520618566094120444477853450631571996, 190817148891164769609380044560698103806, 191113219121804237535001840071236674701, 191408831393027885698148216680369618943,
  191703987823389824378983273635826330074, 191998690515160052360346936501454397142, 192292941554499153304982576244453063910, 192586743011630589875226537567930164947,
  192880096941010635846543998503935458890, 193173005381495985671652351559434670314, 193465470356509080175376644752794525193, 193757493874201186301368461567227243911,
  194049077927613268089940106232337254735, 194340224494834685341083072846699845463, 194630935539159755707828912811322673478, 194921213009242215272059206077382237867,
  195211058839247611977278475398813455214, 195500474949003665630339940138070358753, 195789463244148627536280311081574976168, 196078025616277672196908308230169941987,
  196366163943087352884244444614426889125, 196653880088518152293979026528032236328, 196941175902895158891463094974091015982, 197228053223066898983044355141619684503,
  197514513872542353978487265211959055724, 197800559661626191755462435876167666086, 198086192387552240494352912252222954458, 198371413834615232820609628566657095536,
  198656225774300847572309225209019709781, 198940629965414076002146162595986684035, 199224628154205938725556871207857698244, 199508222074498579239763080511020768050,
  199791413447808759361978115084130249823, 200074203983469781468594372246347999629, 200356595378751861960619629910966598511, 200638589318980979933717996535182103736,
  200920187477656224593708228043454800206, 201201391516565664530053936271358893493, 201482203085900761540528973032487822945, 201762623824369351289644829487092367230,
  202042655359307212681378673162612375551, 202322299306788247433039518135803848506, 202601557271733290951560125783964865655, 202880430848017575235912824781350181296,
  203158921618576864159532755009841625182, 203437031155512281124411147832973042986, 203714761020193848723717914999721759080, 203992112763362759702255349553060103316,
  204269087925232398163565892782497806980, 204545688035588129638953742809756352816, 204821914613885878306873805195077862788, 205097769169349509330937409141340165966,
  205373253201067033971031577777625658685, 205648368198085654814600528058781930700, 205923115639505668173851294914963877112, 206197496994573240399380360417553161992,
  206471513722772074571338880821220324780, 206745167273913983745627927173196180307, 207018459088228386654612804277381788304, 207291390596450741489340942223608906003,
  207563963219909933123118167607690695555, 207836178370614628874423523517729885661, 208108037451338617650406362142637271817, 208379541855705147060497221923602346553,
  208650692968270272842864880474754220720, 208921492164605234704457543712744270625, 209191940811377872438070655629157005064, 209462040266433095947184150699684575487,
  209731791878872422581107504595979192823, 210001196989132594959163506878062337269, 210270256929063292243135509534303736950, 210538973022003947601904550917921924811,
  210807346582859684401021032347297911446, 211075378918176383442801553733640325664, 211343071326214893379328258545780467980, 211610425097024396221370847860418420323,
  211877441512514939670667580682287086417, 212144121846529147811110343814615809770, 212410467364913121506101435979716613664, 212676479325586539664609129644855132159,
  212942158978611972357170238263189138549, 213207507566263416585197492920295926731, 213472526323094065332375919152612068673, 213737216476003320355605687288561682908,
  214001579244303059004800816399941746845, 214265615839783165195816971642881610432, 214529327466776334498792295309869468772, 214792715322222163145179160097307381412,
  215055780595730530600659815536469083023, 215318524469644285197914443720676308350, 215580948119101242172786881826962047120, 215843052712095503299713309001758526090,
  216104839409538107177285970697959825657, 216366309365317019072462261570711115694, 216627463726356469092145212972658530630, 216888303632675647313601872656300690638,
  217148830217446764370399666359406347112, 217409044607052485858177211232486982236, 217668947921142748794575971654548432762, 217928541272690968239994486679704719982,
  218187825768049642060440620806514383058, 218446802507005361690603422331275755881, 218705472582833236634299776949564870674, 218963837082350740320628187906673145449,
  219221897085970984817439750988303252060, 219479653667755431789072735540647040229, 219737107895466046972651079863985664941, 219994260830616905336578421885724529174,
  220251113528525253976128765555582357638, 220507667038362039694204150123599608696, 220763922403201908110361211005882787847, 221019880660072681038065591764325307987,
  221275542840004318768779887996807578267, 221530909968077373801892063995158006525, 221785983063470942461612738357133905486, 222040763139510120745777791418931710663,
  222295251203712970656954543052511550007, 222549448257837003173333135689062887166, 222803355297925183925558282916779478329, 223056973314351467555889437418258105323,
  223310303291865866647839586127097888767, 223563346209639061027704836266938691852, 223816103041306553154129887177037185813, 224068574755012375228030181139187618132,
  224320762313452353572782386636243987764, 224572666673916935753573873424380263623, 224824288788333585825142549459171463978, 225075629603308753018814965684675446837,
  225326690060169419102737625059391808049, 225577471095004229573469161697773490869, 225827973638704213762635212563541860171, 226078198617003098869119626668721363605,
  226328146950517222855251883248047550676, 226577819554785051074628446497907516705, 226827217340306301429552972095434252851, 227076341212580682787574967061957727461,
  227325192072146251319227311424225635707, 227573770814617389352789043539206929208, 227822078330722411276710490853178707018, 228070115506340800956213118296739775866,
  228317883222540085067496705897694394685, 228565382355612346690932398903117173701, 228812613777110383443572936877822383272, 229059578353883514371252488813878024045,
  229306276948113039761459903209089679766, 229552710417347357980033098823453020272, 229798879614536743377521408059511783813, 230044785388067789254779928362991596089,
  230290428581797519821978670583941461218, 230535810035087175030713187184913020688, 230780930582835672105276417735176923797, 231025791055512747546378027036587838941,
  231270392279191783328662170608183570185, 231514735075582320962262349609183047260, 231758820262062267038328060647954535135, 232002648651709793828947848237625630060,
  232246221053334938463162960231353854194, 232489538271510904152801202755316589403, 232732601106605066894648180155822897876, 232975410354809691028999546292736078212,
  233217966808172356988890109053373632663, 233460271254626104529260801284625216669, 233702324478019294680990092027612559542, 233944127258145193631070042609340645375,
  234185680370771281687236835102521780700, 234426984587668290443059374664052639873, 234668040676638971217835882407386938195, 234908849401546597804635868218665598298,
  235149411522343206519442341248810497512, 235389727795097576504585634401607761768, 235629798972022953200505054786649334374, 235869625801504517861317199175795690238,
  236109209028126605951699869489373382489, 236348549392699677225207964553033056424, 236587647632287040247312581706408741696, 236826504480231334090187096672132418653,
  237065120666180769890544650203437668425, 237303496916115134926650885712198992228, 237541633952371561835984762279151499254, 237779532493670065560889795999935274272,
  238017193255138850575939314582643301265, 238254616948339390917623568178547347519, 238491804281291285504345310422552145025, 238728755958496891202575395115184020843,
  238965472680965736063362830785222387747, 239201955146238715122206556513020114370, 239438204048412071124571057744685750319, 239674220078161162509057088032635582328,
  239910003922764020950414604062224348448, 240145556266124700735200101064641494228, 240380877788796422213927536687545598901, 240615969168004511545033772477625056927,
  240850831077669138917868895383110146018, 241085464188427857414221989623407313082, 241319869167657944640597122202517574277, 241554046679498549236555818754429120198,
  241787997384872644337934598434403232474, 242021721941508790047622785493064468255, 242255221003962706940840516990091610477, 242488495223638662606483432156869539838,
  242721545248810673201092883546845490312, 242954371724643521967362688394595235819, 243186975293213596644799584121410578479, 243419356593529547676208914586458285564,
  243651516261552769090074007596727797334, 243883454930217703915631665580191080896, 244115173229451975964511736497096565299, 244346671786196349790200515401475186231,
  244577951224424520614300499091583401983, 244809012165162735986587621755167555333, 245039855226509250924206475536402457367, 245270481023653618253989194176182658548,
  245500890168895815860829766706848029395, 245731083271665212524287755020238019072, 245961060938539374005129002671191350511, 246190823773262711023331314844203360559,
  246420372376764970749185715298526243384, 246649707347179573409504279996519110050, 246878829279861795591599322503821490376, 247107738767406801808621553897956652535,
  247336436399667525871032526380080848475, 247564922763772403590435035904359616327, 247793198444142958323690118639371946403, 248021264022511240847206814133050500226,
  248249120077937125033497039923899925316, 248476767186825460784538852013889250601, 248704205922943085659183244488997746277, 248931436857435696614768727154255276372,
  249158460558844583266270534703199730882, 249385277593123224049703850638775960062, 249611888523653746660119322271657690993, 249838293911263254118370909218154139179,
  250064494314240017804897316522415192637, 250290490288349538783035543359940683230, 250516282386850478718875115553099293197, 250741871160510461689361107851636300022,
  250967257157621748155259898734446027679, 251192440924016782360710589582812097107, 251417423003083614406394068220107664894, 251642203935781198228857763314028473402,
  251866784260654566704234231860644343162, 252091164513849885080482908376542308605, 252315345229129383928363732628662223430, 252539326937886172787616122568993990511,
  252763110169158935671264078269627784912, 252986695449646509577595345659574977653, 253210083303722347146166836395259877691, 253433274253448864581167238106081770789,
  253656268818591675952618347771594583439, 253879067516633714973216553887987356175, 254101670862789245336102556900763081382, 254324079370017760686498370615835360753,
  254546293549037775287963449646638655584, 254768313908340506431994039545570271667, 254990140954203449627819186941325129145, 255211775190703847597530955573826158591,
  255433217119732054090122987666859236425, 255654467241004793516598383257476622985, 255875526052078317397042734451716309496, 256096394048361458599438874859190510523,
  256317071723128584339024350000205857656, 256537559567532448896158680525999049838, 256757858070616946999973109185469923489, 256977967719329768814518660825537737905,
  257197888998534957453707001611806426141, 257417622391025369941050790862963508850, 257637168377535042520054040062439575522, 257856527436751461211076523725046192652,
  258075700045327738500597651600725085181, 258294686677894697039032567155506353673, 258513487807072861213604769024266816643, 258732103903484357453253474976449672980,
  258950535435764724113148505305823780454, 259168782870574631777098926008787985839, 259386846672611514806972360844698226647, 259604727304621114959188081712701254037,
  259822425227408937879407071735523610273, 260039940899851623277714604212135592898, 260257274778908229577873898126556519873, 260474427319631433825621527404502933192,
  260691398975178647632474931662825545459, 260908190196823049923128080279083987301, 261124801433964537246221582685559369833, 261341233134140592400086842896451824103,
  261557485743037072116978775599928801699, 261773559704498914541326707635330350778, 261989455460540767229646977639594347427, 262205173451357536391972035370709648437,
  262420714115334858086958169580731366701, 262636077889059492075236019421518545676, 262851265207329639028063430186542954135, 263066276503165181780927701185963902472,
  263281112207817851314422563332615245256, 263495772750781318137493058000418624129, 263710258559801209740997627786168362537, 263924570060885054782479953975909166873,
  264138707678312154656072183610661003640, 264352671834643383094564998372653332900, 264566462950730914443877323555357286122, 264780081445727881243438211486373949194,
  264993527737097961739354430852221807424, 265206802240624897950678439604651782563, 265419905370421944902611619660153613168, 265632837538941251634075828277143597658,
  265845599156983174580761412056068915199, 266058190633705523928510789335701199090, 266270612376632743525722505595358691420, 266482864791665024937360290155069953963,
  266694948283087356217124092166729047629, 266906863253578505968384365861728570649, 267118610104219943258596040345479940739, 267330189234504693946093693569525168580,
  267541601042346133972423513470128845682, 267752845924086720167689745742695147512, 267963924274506659110782585296871553389, 268174836486832514580809968719744466394,
  268385582952745754130576583090156862104, 268596164062391235307538750455003108013, 268806580204385632042312818393520551772, 269016831765825801719526439316123156306,
  269226919132297093440575820981803530714, 269436842687881597982686857032176425375, 269646602815166339953573190136599845062, 269856199895251412635938924575114068068,
  270065634307758056011087104460955311518, 270274906430836678445966434590790579282, 270484016641174822523117280751280746452, 270692965314005075488162994037328189043,
  270901752823112924784733319190899535080, 271110379540844559142002340820375863297, 271318845838114615675373374935077103393, 271527152084413873456246718337607116255,
  271735298647816894002262527182444674430, 271943285894989609134919620706242846216, 272151114191196856647031019023199395431, 272358783900309864218087857043330409306,
  272566295384813682011264311767109339731, 272773649005814564381506688705731795737, 272980845123047301119909195603888845279, 273187884094882498655386557846561464180,
  273394766278333811630508878825172580792, 273601492029065125264266407956665079603, 273808061701397688910480545608480596042, 274014475648317201216571893142291291449,
  274220734221480847283435861414895734398, 274426837771224288223260704502801704907, 274632786646568603508251277524278290978, 274838581195227186499393766705723488980,
  275044221763612593540611552747348163121, 275249708696843346999919699413097743991, 275455042338750692635484770162390451077, 275660223031885311660837236230928240409,
  275865251117523987879865127023215223724, 276070126935676230258639272546694157880, 276274850825090851297581989705406634984, 276479423123262501563991868538311671807,
  276683844166438160741476926931056122854, 276888114289623585549426335876827931943, 277092233826589714882266691760965608546, 277296203109879032514901953861086466108,
  277500022470811887717426207368612421461, 277703692239492774118924894338906602795, 277907212744816567156942623066978977288, 278110584314474720445993672777545442162,
  278313807274961421395324413741414527560, 278516881951579706403004627634381357650, 278719808668447535950326709816406952601, 278922587748503829917427540838876006752,
  279125219513514463438017011341288414635, 279327704284078223608099360786057190822, 279530042379632727360608240078898067411, 279732234118460300814943330491786498474,
  279934279817693820407495051401591927626, 280136179793322516106373977549771373468, 280337934360197737010722678518061843015, 280539543832038679632179409854232347625,
  280741008521438079153285052894859843718, 280942328739867863954876550037052339471, 281143504797684773701791450243781847916, 281344537004135941273518707105844308546,
  281545425667364438823770204873271465843, 281746171094414788250315277351233233490, 281946773591238436353816385994457897849, 282147233462699194961827797147224560430,
  282347551012578646291570208963831335770, 282547726543581513822572495423177564900, 282747760357340998947776731784931922487, 282947652754424083669234120970015256198,
  283147404034336799602077036148276805084, 283347014495529463548035817997986841082, 283546484435401879897377906572163788406, 283745814150308510115781042501348511429,
  283945003935563609570311339484412244341, 284144054085446331946360712779266430091, 284342964893205801505106153763693721473, 284541736651066153428785379543563327808,
  284740369650231542498839173825878111072, 284938864180891120349749989409571831711, 285137220532223981539208825962352514423, 285335438992404078673067755199922329127,
  285533519848605106821383468732001275513, 285731463387005357459727604817179755100, 285929269892792542167832105715410437667, 286126939650168586315552207341896268174,
  286324472942354392964065611017347530057, 286521870051594577208183680144953226511, 286719131259162171183628892803030200723, 286916256845363299961132017966662702095,
  287113247089541828547222325020554428415, 287310102270083980209624343227646759124, 287506822664422926343235022827125798395, 287703408549043348090735378484150300109,
  287899860199485969929990587970314894118, 288096177890352065438511846278812750931, 288292361895307935443391812880949427958, 288488412487089358763283015427614820925,
  288684329937506015747164867672672734024, 288880114517445884812839806351895247421, 289075766496879612186312237582580729800, 289271286144864855041435297191938641412,
  289466673729550598237459663079412401366, 289661929518181444850385605779844294686, 289857053777101880692303922961314832411, 290052046771760513011213174397059534273,
  290246908766714283562119518284839297365, 290441640025632656238561252459574406280, 290636240811301779452052692350840865867, 290830711385628623445311081220785290236,
  291025052009645092723515639440496221678, 291219262943512113786249432865920097766, 291413344446523698341192292648430579320, 291607296777110982179066369266086494232,
  291801120192846239887784873678595989396, 291994814950446875582218972032579053771, 292188381305779389824477483234468619868, 292381819513863322908088809116073356801,
  292575129828875174677984235150989266136, 292768312504152301056706208176089650321, 292961367792196787445804260868012734329, 293154295944679299169934747427010201966,
  293347097212442909129748319678569379940, 293539771845506902828230948279310129756, 293732320093070560933760122556063018650, 293924742203516919541747489322562070413,
  294117038424416508295362462345254912981, 294309209002531066524468098411880741218, 294501254183817237560550643516235203893, 294693174213430241384087455685767077316,
  294884969335727525759474363449133542331, 295076639794272396011322776675390203528, 295268185831837623594638887100353268865, 295459607690409033610111938628310436894,
  295650905611189071414465673528509651801, 295842079834600348474566532712429526755, 296033130600289167612733870840165523316, 296224058147129027789461206183706148044,
  296414862713224108568533228731231731847, 296605544535912734408310807325972842270, 296796103851770818921755438666256768031, 296986540896615289246575340293816903711,
  297176855905507490665697580360768082811, 297367049112756571617104134618389497755, 297557120751922849230914442849985643304, 297747071055821155530452781502797185023,
  297936900256524164432905456657641113483, 298126608585365699684050333257697629919, 298316196272944023860429435678873846160, 298505663549125108571234165654835761770,
  298695010643045885991081972054804028594, 298884237783117481853782960211032936121, 299073345197028430036124834921529646727, 299262333111747868859644620766531152075,
  299451201753528719237305687149824352449, 299639951347910844790958615986747460388, 299828582119724194064434280974289124593, 300017094293091924956097053928828491723,
  300205488091433511493675212049805616059, 300393763737467833073184287684901649135, 300581921453216246282767177975664090850, 300769961460005639431292215597031321158,
  300957883978471469900576994802773155604, 301145689228560784439141451456568645291, 301333377429535222514438415127262763206, 301520948799974002839563490260507007911,
  301708403557776893189508587638069017388, 301895741920167163621094623643319936318, 302082964103694523209798741207171758402, 302270070324238040415779791736828182540,
  302457060797009047190502661923237053845, 302643935736554026934467244230638550845, 302830695356757486415661347283404761700, 303017339870844811757478535500058898755,
  303203869491385108603971690415531081503, 303390284430294026569450914415821822312, 303576584898836568078580167308738393976, 303762771107629881702280654470904942690,
  303948843266646040093910390409155885340, 304134801585214802629358462569323478416, 304320646272026362853869237172025271945, 304506377535134080837596002735091538556,
  304691995581957200541075259652670927586, 304877500619283552291011958542215995727, 305062892853272240465972389734820310944, 305248172489456316490795055844660741687,
  305433339732745437237750644251843982788, 305618394787428508931710082870302333089, 305803337857176316655814537896445445964, 305988169145044139553383024329590154974,
  306172888853474351821041977732314013584, 306357497184299009587316608583921829654, 306541994338742423770186059104533431574, 306726380517423719006373237817322128119,
  306910655920359378744415651383624552884, 307094820746965776592845519176619807181, 307278875196061694014095877206047123087, 307462819465870824454044188676775020790,
  307646653754024263996406113712010248949, 307830378257562988630499486388522379928, 308013993172940318220212139735131308841, 308197498696024367261326945974118138426,
  308380895022100482513683237985039941631, 308564182345873667593985587389270536132, 308747360861470994614408674131081478618, 308930430762444002951490631990245879962,
  309113392241771085229156734799915856554, 309296245491859860599070540626329742989, 309478990704549535400870577816428739401, 309661628071113251284217280308471805592,
  309844157782260420873947103244038846969, 310026580028139051059008517666313125283, 310208894998338053985237839514412264385, 310391102881889545831421538420516498404,
  310573203867271133447485741790270916979, 310755198142408188933053045705470101962, 310937085894676112234011413335413359005, 311118867310902581834149831372264246588,
  311300542577369793618330453690430923290, 311482111879816687983087137718907771390, 311663575403441165269965522224493275579, 311844933332902289596350055209006902329,
  312026185852322481157958607854784808824, 312207333145289697076625455886341627246, 312388375394859600866438424868770828906, 312569312783557720590745832885403519830,
  312750145493381595782003475305713606529, 312930873705802913195891235067382977740, 313111497601769631470592921666127519648, 313292017361708094761601596993776653969,
  313472433165525135421885890911633197587, 313652745192610165796730599110684736739, 313832953621837259202047146001107286189, 314013058631567220154436242183053833738,
  314193060399649643920776226049526863230, 314372959103424965454606109303232761517, 314552754919726497786072204142535591753, 314732448024882459931711353557987390441,
  314912038594717994389852174007095734683, 315091526804557174286928310577891167661, 315270912829225000239514457933199481482, 315450196843049386996416775608544988928,
  315629379019863139924674283812822012495, 315808459533005921402856826376882887216, 315987438555326207184578191959603703709, 316166316259183232794679954521357194931,
  316345092816448930020082491292675638667, 316523768398509853556844423291821901462, 316702343176269097874520362573820237420, 316880817320148204358459304919482903897,
  317059191000089058790242240085071327368, 317237464385555779226017527910472562484, 317415637645536594332056271790627630484, 317593710948545712236417275896804759745,
  317771684462625179955182164112984021892, 317949558355346733451295832321931608619, 318127332793813638383625567196950110194, 318305007944662521603433860153578694457,
  318482583974065193455045141074535543158, 318660061047730460937075319679662240348, 318837439330905931780185120159982264567, 319014718988379809496913694467282698239,
  319191900184482679458747869326509445021, 319368983083089286055184589834960440950, 319545967847620300989149636981646089436, 319722854641044082762744486444897509332,
  319899643625878427406905210815895041033, 320076334964192310508172576482941575693, 320252928817607620585390919648079502489, 320429425347300883868774973501793975671,
  320605824714004980533408530932842524362, 320782127078010852438866635086918277610, 320958332599169202426283864702982677025, 321134441436892185223825193844146861358,
  321310453750155090011152828093285550832, 321486369697498014693122323488948106593, 321662189437027531932584152712489696757, 321837913126418346991812667868329273034,
  322013540922914947431733093475947847571, 322189072983333244717768740145961072118, 322364509464062207780785032252602899436, 322539850521065488581264165425313346312,
  322715096309883039724504225818571445046, 322890246985632724174299387105963554473, 323065302703011917112223327471549576064, 323240263616299099989306252291200993622,
  323415129879355446816566843720562091226, 323589901645626402740534061303022610799, 323764579068143254949569963502637789135, 323939162299524695956483584526126981093,
  324113651491978379302607359945710471396, 324288046797302467728191624736538180672, 324462348366887173853659284907136349190, 324636556351716293415951865676608610175,
  324810670902368731103889742123183760987, 324984692169020019036163439614293656790, 325158620301443827925269428579529583156, 325332455449013470970402808984451035957,
  325506197760703400522020662111673333530, 325679847385090697560493619086248401105, 325853404470356554030969335346820951760, 326026869164287748076280046533095282680,
  326200241614278112209437192821006551426, 326373521967329994466969214590975320217, 326546710370055712584074021674770231221, 326719806968679001232275300715203276489,
  326892811909036452359991730019557079973, 327065725336578948676150298526445474880, 327238547396373090316699255173346953773, 327411278233102614733602727285148572247,
  327583917991069809845627722037515668592, 327756466814196920489965044213387060546, 327928924846027548213458607190655991692, 328101292229728044441952663389909420616,
  328273569108088897066003616478131629456, 328445755623526110480942281860009718173, 328617851918082579119013715970632252847, 328789858133429454511065020372882604179,
  328961774410867505914996825601828621255, 329133600891328474547941454208244772488, 329305337715376421458880034832663844198, 329476985023209069078162071863942203380,
  329648542954659136480144150949525454847, 329820011649195668394919562147206473044, 329991391245925358004867632828586793761, 330162681883593863561510464718872830702,
  330333883700587118857925547008197082113, 330504996834932637591725353782632086059, 330676021424300811653379512747102254175, 330846957606006203374421437156734453274,
  331017805517008831769849428005917034351, 331188565293915452808802162970688873560, 331359237072980833747360176640719543611, 331529820990109021557098387646487961981,
  331700317180854605482789926971832579683, 331870725780423973762438452778797144656, 332041046923676564542594785346429497073, 332211280745126111021694046270932974510,
  332381427378941880853931524069992596162, 332551486958949909845979199101953677689, 332721459618634229978630229716105484643, 332891345491138091785245714399909383981,
  333061144709265181118666687128397565994, 333230857405480830338044561033945401398, 333400483711913223946835094921506024964, 333570023760354598712994404210577526573,
  333739477682262438302210558879667558425, 333908845608760662454800892343048147188, 334078127670640810736703273455172981417, 334247323998363220894789255696684304805,
  334416434722058201846528199856921670440, 334585459971527201333834156127387157984, 334754399876243968270731475520177100241, 334923254565355709814280786110416129476,
  335092024167684243188014104080371819071, 335260708811727142286936440344725912389, 335429308625658879092961298211079824338, 335597823737331959929458923745669497233,
  335766254274278056583409056057539964723, 335934600363709132323464217487517641510, 336102862132518562842045271708781427198, 336271039707282252149408049145153945383,
  336439133214259743447438282135616280880, 336607142779395325010751895274738852330, 336775068528319131102498847804835214161, 336942910586348237952091213402019341145,
  337110669078487754821899996868390173567, 337278344129431910189790315906636032807, 337445935863565133074191008207632413414, 337613444404963129528222448527013170255,
  337780869877393954329235366367777255883, 337948212404319077889943731529859176829, 338115472108894448417166311442841789056, 338282649113971549344024290273663995699,
  338449743542098452061276364805709047626, 338616755515520863973307985625853813150, 338783685156183171904127883936066202782, 338950532585729480878562704126449019897,
  339117297925504648303679440003082045408, 339283981296555313575305438246810257146, 339450582819630923134356976371853708885, 339617102615184750997529834331789534285,
  339783540803374914786748849252570169619, 339949897504065387281618161915820656447, 340116172836827003518959722018333391818, 340282366920938463463374607431768211455]

theorem rotCert10_ok : certOK (2^10) (2^246) 0 rotCert10 = true := by decide +kernel

theorem rot10_canonical (Y : Nat) (hb : Y*Y < 2^256) :
    (Y*Y) / 2^246 + 2^10 * ((Y*Y) % 2^246) < SquareReduction.p :=
  rot_lt_p (2^10) (2^246) (by positivity) (by positivity) (by norm_num) rotCert10 rotCert10_ok Y hb

end ECDSAAdd.Entrant

end

section
-- ===== SquareAcc =====
/-! Streamed square with accumulated (c−1)-corrections. All small
(c−1)·slice corrections of a branch are summed exactly in a 163-bit
accumulator and then folded with a single modular addition. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def rot128F (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=false,canonical:=true,src:=L.rotated128}
def negP (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=true,canonical:=true,src:=L.core.product.take 256}
def negRot (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=true,canonical:=true,src:=L.rotated128}
def topSlice (L : CuccaroStreamedSquareWideLayout) (j : Nat) : List Wire :=
  (L.core.product.take 256).drop (256-j)
def rotF (L : CuccaroStreamedSquareWideLayout) (neg : Bool) (j : Nat) : MeasuredSquareFold :=
  {negative:=neg,canonical:=false,src:=rotateFull (L.core.product.take 256) j}
/-- Same rotated source, folded without source normalization (proved canonical). -/
def rotC (L : CuccaroStreamedSquareWideLayout) (neg : Bool) (j : Nat) : MeasuredSquareFold :=
  {negative:=neg,canonical:=true,src:=rotateFull (L.core.product.take 256) j}
def posTop (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=false,canonical:=true,src:=L.core.product.drop 256,shift:=128}

/-- Branch B's small correction W = top32 + top10 + top4 - top6, built in the 33-bit temporary. -/
def preW (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=false,canonical:=true,src:=topSlice L 32},
   {negative:=false,canonical:=true,src:=topSlice L 10},
   {negative:=false,canonical:=true,src:=topSlice L 4},
   {negative:=true,canonical:=true,src:=topSlice L 6}]

/-- Branch B's accumulator terms: d*H - d*W instead of five d-multiples. -/
def termsB (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  sortedItems false (nafMinusOneItems false (L.core.product.drop 128)++nafMinusOneItems true (wTemp L))

def accARaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)
def accBRaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)++nafMinusOneItems true (topSlice L 4)++
    nafMinusOneItems false (topSlice L 6)++nafMinusOneItems true (topSlice L 10)++
    nafMinusOneItems true (topSlice L 32)
def accCRaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)++[posTop L]

def accAMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (rot128F L),.inr ⟨false,[],sortedItems false (accARaw L),sortedItems false (accARaw L)⟩,.inl (negP L)]
def accBMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negP L),.inl (rotC L true 4),.inl (rotC L true 10),.inl (rotC L true 32),
    .inl (rotC L false 6),.inl (rot128F L),.inr ⟨false,preW L,termsB L,sortedItems false (accBRaw L)⟩]
def accCMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negRot L),.inr ⟨true,[],sortedItems false (accCRaw L),sortedItems false (accCRaw L)⟩]

def accBranchA (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.low (L.core.product.take 256) (mixFolds L false (accAMix L))
def accBranchB (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.high (L.core.product.take 256) (mixFolds L true (accBMix L))
def accMiddleC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.sum L.core.product (mixFolds L false (accCMix L))
def accBranchC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.core.prepareSum++accMiddleC L control++L.core.clearSum

def accProgram (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  accBranchA L control++accBranchB L control++accBranchC L control++L.reflectOutput

/-- The accumulated square without its final output reflection. -/
def accPrefix (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  accBranchA L control++accBranchB L control++accBranchC L control

theorem accProgram_split (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    accProgram L control=accPrefix L control++L.reflectOutput := by
  simp only [accProgram,accPrefix,List.append_assoc]

theorem acc_orientations (L : CuccaroStreamedSquareWideLayout) :
    mixFinal false (accAMix L)=true ∧ mixFinal true (accBMix L)=false ∧
    mixFinal false (accCMix L)=true := by
  simp [mixFinal,mixNeg,accAMix,accBMix,accCMix,rot128F,negP,negRot,rotF,rotC]

theorem naf_facts (neg : Bool) (src : List Wire) (f : MeasuredSquareFold)
    (hf : f∈nafMinusOneItems neg src) :
    f.src=src ∧ (f.shift=4 ∨ f.shift=6 ∨ f.shift=10 ∨ f.shift=32) := by
  simp only [nafMinusOneItems,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> simp

theorem topSlice_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (j : Nat) (hj : j≤256) :
    (topSlice L j).length=j := by
  simp [topSlice,hw.core.product]; omega

theorem topSlice_count (L : CuccaroStreamedSquareWideLayout) (j : Nat) (q : Wire) :
    (topSlice L j).count q≤L.core.product.count q :=
  ((List.drop_sublist _ _).count_le q).trans ((List.take_sublist _ _).count_le q)

/-- Every accumulated term is a short slice at a small shift. -/
theorem raw_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold)
    (hf : f∈accARaw L ∨ f∈accCRaw L) :
    (∀q,f.src.count q≤L.core.product.count q) ∧ TermOK f := by
  have dl : (L.core.product.drop 128).length=130 := by simp [hw.core.product]
  have naf (neg : Bool) (src : List Wire) (hs : ∀q,src.count q≤L.core.product.count q)
      (hl : src.length=130) (hf : f∈nafMinusOneItems neg src) :
      (∀q,f.src.count q≤L.core.product.count q) ∧ TermOK f := by
    obtain ⟨e,sh⟩ := naf_facts neg src f hf
    rw [e]
    refine ⟨hs,?_⟩
    simp only [TermOK,e]
    omega
  have dc := L.productDrop_count 128
  rcases hf with hf|hf
  · exact naf false _ dc (by omega) hf
  · simp only [accCRaw,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with hf|rfl
    · exact naf false _ dc (by omega) hf
    · refine ⟨L.productDrop_count 256,?_⟩
      simp [TermOK,posTop,hw.core.product]

theorem sorted_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (raw : List MeasuredSquareFold)
    (hr : ∀f∈raw,(∀q,f.src.count q≤L.core.product.count q) ∧ TermOK f) :
    (∀f∈sortedItems false raw,∀q,f.src.count q≤L.core.product.count q) ∧
      (∀f∈sortedItems false raw,TermOK f) :=
  ⟨fun f hf => (hr f ((sorted_perm _ _).subset hf)).1,fun f hf => (hr f ((sorted_perm _ _).subset hf)).2⟩

theorem validA (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    Acc.Valid t 163 0 (sortedItems false (accARaw L)) := by
  have hT := regValue_lt (L.core.product.drop 128) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  simp [Acc.Valid,Acc.step,sortedItems,accARaw,nafMinusOneItems,List.filter_cons]
  generalize regValue (L.core.product.drop 128) t=T at hT ⊢
  omega

theorem validC (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    Acc.Valid t 163 0 (sortedItems false (accCRaw L)) := by
  have hT := regValue_lt (L.core.product.drop 128) t
  have hU := regValue_lt (L.core.product.drop 256) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  rw [show (L.core.product.drop 256).length=2 by simp [hw.core.product]] at hU
  simp [Acc.Valid,Acc.step,sortedItems,accCRaw,posTop,nafMinusOneItems,List.filter_cons]
  generalize regValue (L.core.product.drop 128) t=T at hT ⊢
  generalize regValue (L.core.product.drop 256) t=U at hU ⊢
  omega

theorem top_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) (j : Nat) (hj : j≤128) :
    regValue (topSlice L j) t*2^(128-j)≤regValue (L.core.product.drop 128) t := by
  rw [topSlice,L.productTakeDrop_value hw t P hP j (by omega),L.product_drop_value hw t P hP 128 (by omega),
    Nat.mod_eq_of_lt hb]
  have e : 256-j=128+(128-j) := by omega
  rw [e,pow_add,←Nat.div_div_eq_div_mul]
  exact Nat.div_mul_le_self _ _

theorem top_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) (j : Nat) (hj : j≤128) :
    regValue (topSlice L j) t=regValue (L.core.product.drop 128) t/2^(128-j) := by
  rw [topSlice,L.productTakeDrop_value hw t P hP j (by omega),L.product_drop_value hw t P hP 128 (by omega),
    Nat.mod_eq_of_lt hb]
  have e : 256-j=128+(128-j) := by omega
  rw [e,pow_add,←Nat.div_div_eq_div_mul]

theorem plain_view (L : CuccaroStreamedSquareWideLayout) (t : BasisState) (neg : Bool)
    (xs : List MeasuredSquareFold) (hc : ∀f∈xs,∀q,f.src.count q≤L.core.product.count q)
    (ho : ∀f∈xs,TermOK f) (hv : Acc.Valid t 163 0 xs) : AccView L t ⟨neg,[],xs,xs⟩ := by
  refine ⟨fun f hf q => ?_,ho,by simp,by simp,by simp [Acc.Valid],hv,?_⟩
  · have h := hc f hf q; simp only [List.count_append]; omega
  · intro t' ht' _
    have vc := Acc.valid_congr t t' 163 xs (fun f hf => regValue_congr _ _ _ (fun q hq => by
      have pos := List.count_pos_iff.mpr hq
      have b := hc f hf q
      exact (ht' q (List.count_pos_iff.mp (by omega))).symm)) 0
    exact ⟨vc.1.mp hv,vc.2.symm⟩

theorem validB (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) :
    Acc.Valid t 163 0 (sortedItems false (accBRaw L)) := by
  have hT := regValue_lt (L.core.product.drop 128) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  have l (j : Nat) (hj : j≤32) := topSlice_length L hw j (by omega)
  have b4 := regValue_lt (topSlice L 4) t
  have b6 := regValue_lt (topSlice L 6) t
  have b10 := regValue_lt (topSlice L 10) t
  have b32 := regValue_lt (topSlice L 32) t
  rw [l 4 (by omega)] at b4
  rw [l 6 (by omega)] at b6
  rw [l 10 (by omega)] at b10
  rw [l 32 (by omega)] at b32
  have r4 := top_rel L hw t P hP hb 4 (by omega)
  have r6 := top_rel L hw t P hP hb 6 (by omega)
  have r10 := top_rel L hw t P hP hb 10 (by omega)
  have r32 := top_rel L hw t P hP hb 32 (by omega)
  simp [Acc.Valid,Acc.step,sortedItems,accBRaw,nafMinusOneItems,List.filter_cons]
  norm_num at r4 r6 r10 r32 b4 b6 b10 b32 hT
  generalize regValue (L.core.product.drop 128) t=D at *
  generalize regValue (topSlice L 4) t=a at *
  generalize regValue (topSlice L 6) t=b at *
  generalize regValue (topSlice L 10) t=c at *
  generalize regValue (topSlice L 32) t=d at *
  omega

theorem termsB_facts (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) (hf : f∈termsB L) :
    (f.src=L.core.product.drop 128 ∨ f.src=wTemp L) ∧ 4≤f.shift ∧ f.shift≤32 := by
  have h := (sorted_perm _ _).subset hf
  simp only [List.mem_append] at h
  rcases h with h|h
  · obtain ⟨e,sh⟩ := naf_facts false _ f h; exact ⟨Or.inl e,by omega,by omega⟩
  · obtain ⟨e,sh⟩ := naf_facts true _ f h; exact ⟨Or.inr e,by omega,by omega⟩

theorem accB_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) (t' : BasisState)
    (ht' : ∀q∈L.core.product,t' q=t q) (hwv : regValue (wTemp L) t'=Acc.accVal t 0 (preW L)) :
    Acc.Valid t' 163 0 (termsB L) ∧ Acc.accVal t' 0 (termsB L)=Acc.accVal t 0 (sortedItems false (accBRaw L)) := by
  have hH' : regValue (L.core.product.drop 128) t'=regValue (L.core.product.drop 128) t :=
    regValue_congr _ _ _ (fun q hq => ht' q (List.mem_of_mem_drop hq))
  have hT := regValue_lt (L.core.product.drop 128) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  have hH : regValue (L.core.product.drop 128) t<2^128 := by
    rw [L.product_drop_value hw t P hP 128 (by omega)]
    exact Nat.div_lt_of_lt_mul (by have e : (2:ℕ)^128*2^128=2^256 := by norm_num
                                   rw [e]; exact hb)
  have r4 := top_rel L hw t P hP hb 4 (by omega)
  have r6 := top_rel L hw t P hP hb 6 (by omega)
  have r10 := top_rel L hw t P hP hb 10 (by omega)
  have r32 := top_rel L hw t P hP hb 32 (by omega)
  have s4 : regValue (topSlice L 4) t*4≤regValue (L.core.product.drop 128) t :=
    le_trans (Nat.mul_le_mul_left _ (by norm_num)) r4
  have s10 : regValue (topSlice L 10) t*4≤regValue (L.core.product.drop 128) t :=
    le_trans (Nat.mul_le_mul_left _ (by norm_num)) r10
  have s32 : regValue (topSlice L 32) t*4≤regValue (L.core.product.drop 128) t :=
    le_trans (Nat.mul_le_mul_left _ (by norm_num)) r32
  have m610 : regValue (topSlice L 6) t≤regValue (topSlice L 10) t := by
    rw [top_eq L hw t P hP hb 6 (by omega),top_eq L hw t P hP hb 10 (by omega)]
    exact Nat.div_le_div_left (by norm_num) (by norm_num)
  simp [Acc.Valid,Acc.accVal,Acc.step,termsB,sortedItems,accBRaw,preW,nafMinusOneItems,List.filter_cons] at hwv ⊢
  rw [hH',hwv]
  norm_num at r4 r6 r10 r32 hH ⊢
  generalize regValue (L.core.product.drop 128) t=D at *
  generalize regValue (topSlice L 4) t=a at *
  generalize regValue (topSlice L 6) t=b at *
  generalize regValue (topSlice L 10) t=c at *
  generalize regValue (topSlice L 32) t=d at *
  omega

theorem accB_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) :
    AccView L t ⟨false,preW L,termsB L,sortedItems false (accBRaw L)⟩ := by
  have dl : (L.core.product.drop 128).length=130 := by simp [hw.core.product]
  have wl := (acc_lengths L hw).2.2.2
  have l (j : Nat) (hj : j≤32) := topSlice_length L hw j (by omega)
  refine ⟨?_,?_,?_,?_,?_,validB L hw t P hP hb,fun t' ht' hwv => accB_value L hw t P hP hb t' ht' hwv⟩
  · intro f hf q
    have dc := L.productDrop_count 128 q
    simp only [SrcOK,List.count_append]
    rcases (termsB_facts L f hf).1 with e|e <;> rw [e] <;> omega
  · intro f hf
    obtain ⟨e,s1,s2⟩ := termsB_facts L f hf
    simp only [TermOK]
    rcases e with e|e <;> rw [e] <;> simp only [dl,wl] <;> omega
  · intro f hf q
    simp only [preW,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl <;> exact topSlice_count L _ q
  · intro f hf
    simp only [preW,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl <;> simp only [TermOK33,l 32 (by omega),l 10 (by omega),l 4 (by omega),
      l 6 (by omega)] <;> omega
  · have e6 := top_eq L hw t P hP hb 6 (by omega)
    have e10 := top_eq L hw t P hP hb 10 (by omega)
    have b4 := regValue_lt (topSlice L 4) t
    have b10 := regValue_lt (topSlice L 10) t
    have b32 := regValue_lt (topSlice L 32) t
    rw [l 4 (by omega)] at b4
    rw [l 10 (by omega)] at b10
    rw [l 32 (by omega)] at b32
    simp [Acc.Valid,Acc.step,preW]
    norm_num at e6 e10 b4 b10 b32 ⊢
    generalize regValue (L.core.product.drop 128) t=D at *
    generalize regValue (topSlice L 4) t=a at *
    generalize regValue (topSlice L 6) t=b at *
    generalize regValue (topSlice L 10) t=c at *
    generalize regValue (topSlice L 32) t=d at *
    subst e6 e10
    omega

theorem accA_mixSum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    mixSignedSum t (accAMix L)=measuredSignedSum t L.measuredAItems := by
  have cast := Acc.accVal_cast t 163 (sortedItems false (accARaw L)) 0 (validA L hw t)
  rw [signedSum_perm t (sorted_perm _ _)] at cast
  simp only [accAMix,mixSignedSum,mixSignedPayload,mixNeg,mixPayload,cast]
  simp [measuredAItems,accARaw,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,rot128F,negP,nafMinusOneItems]
  ring

theorem accB_mixSum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) :
    mixSignedSum t (accBMix L)=measuredSignedSum t L.measuredBItems := by
  have cast := Acc.accVal_cast t 163 (sortedItems false (accBRaw L)) 0 (validB L hw t P hP hb)
  rw [signedSum_perm t (sorted_perm _ _)] at cast
  simp only [accBMix,mixSignedSum,mixSignedPayload,mixNeg,mixPayload,cast]
  simp [measuredBItems,accBRaw,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,measuredSignedSum_append,
    rot128F,negP,rotF,rotC,topSlice,nafMinusOneItems,shiftedProductItems]
  ring

theorem accC_mixSum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    mixSignedSum t (accCMix L)=measuredSignedSum t L.measuredCItems := by
  have cast := Acc.accVal_cast t 163 (sortedItems false (accCRaw L)) 0 (validC L hw t)
  rw [signedSum_perm t (sorted_perm _ _)] at cast
  simp only [accCMix,mixSignedSum,mixSignedPayload,mixNeg,mixPayload,cast]
  simp [measuredCItems,accCRaw,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,measuredSignedSum_append,
    negRot,posTop,nafMinusOneItems]
  ring

theorem accA_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    ∀i∈accAMix L,MixView L t i := by
  intro i hi
  simp only [accAMix,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl
  · exact L.measuredA_views hw t M hM hp _ (by simp [measuredAItems,rot128F])
  · have st := sorted_static L hw (accARaw L) (fun f hf => raw_static L hw f (Or.inl hf))
    exact plain_view L t false _ st.1 st.2 (validA L hw t)
  · exact L.measuredA_views hw t M hM hp _ (by simp [measuredAItems,negP])

theorem square_mod8 (M : Nat) : M^2%8≠5 ∧ M^2%8≠6 ∧ M^2%8≠7 := by
  have h : M^2%8=(M%8)^2%8 := Nat.pow_mod M 2 8
  have lt := Nat.mod_lt M (show 8>0 by norm_num)
  rw [h]
  interval_cases (M%8) <;> decide

/-- A square below 2^256 rotated by 32 is already below p: the low 224 bits
cannot be among the three largest residues, which are 5, 6, 7 mod 8. -/
theorem rot32_canonical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    regValue (rotateFull (L.core.product.take 256) 32) t*2^0<SquareReduction.p := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  rw [L.rotateFull_value hw t (M^2) hp 32 (by omega),Nat.mod_eq_of_lt hb]
  have m8 := square_mod8 M
  have e : M^2%2^(256-32)%8=M^2%8 := Nat.mod_mod_of_dvd _ (by norm_num)
  have hH : M^2/2^(256-32)<2^32 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc M^2<2^256 := hb
      _ = 2^32*2^(256-32) := by norm_num
  have hL := Nat.mod_lt (M^2) (show 2^(256-32)>0 by positivity)
  generalize M^2/2^(256-32)=H at hH ⊢
  generalize hX : M^2%2^(256-32)=X at hL e ⊢
  rw [←e] at m8
  norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at hH hL ⊢
  omega

theorem accB_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    ∀i∈accBMix L,MixView L t i := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have hbm : M*M<2^256 := by simpa [sq] using hb
  have rc (neg : Bool) (j : Nat) (hj : j≤256)
      (hcan : (M*M)/2^(256-j)+2^j*((M*M)%2^(256-j))<SquareReduction.p)
      (hmem : rotF L neg j∈L.measuredBItems) : MixView L t (.inl (rotC L neg j)) := by
    have base := L.measuredB_views hw t M hM hp (rotF L neg j) hmem
    refine ⟨base.count,base.span,fun _ => ?_⟩
    have hv := L.rotateFull_value hw t (M^2) hp j hj
    change regValue (rotateFull (L.core.product.take 256) j) t*2^0<SquareReduction.p
    rw [hv, pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hb, sq]
    exact hcan
  intro i hi
  simp only [accBMix,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact L.measuredB_views hw t M hM hp _ (by simp [measuredBItems,shiftedProductItems,negP])
  · exact rc true 4 (by omega) (rot4_canonical M hbm)
      (by simp [measuredBItems,shiftedProductItems,rotF])
  · exact rc true 10 (by omega) (rot10_canonical M hbm)
      (by simp [measuredBItems,shiftedProductItems,rotF])
  · have v := L.measuredB_views hw t M hM hp (rotF L true 32)
      (by simp [measuredBItems,shiftedProductItems,rotF])
    exact ⟨v.count,v.span,fun _ => rot32_canonical L hw t M hM hp⟩
  · exact rc false 6 (by omega) (rot6_canonical M hbm)
      (by simp [measuredBItems,shiftedProductItems,rotF])
  · exact L.measuredB_views hw t M hM hp _ (by simp [measuredBItems,rot128F])
  · exact accB_view L hw t (M^2) hp hb

theorem accC_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hp : regValue L.core.product t=M^2) :
    ∀i∈accCMix L,MixView L t i := by
  intro i hi
  simp only [accCMix,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl
  · exact L.measuredC_views hw t M hp _ (by simp [measuredCItems,negRot])
  · have st := sorted_static L hw (accCRaw L) (fun f hf => raw_static L hw f (Or.inr hf))
    exact plain_view L t true _ st.1 st.2 (validC L hw t)

theorem acc_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈accAMix L,MixStatic L i) ∧ (∀i∈accBMix L,MixStatic L i) ∧ (∀i∈accCMix L,MixStatic L i) := by
  let z : BasisState := fun _ => false
  have hz : regValue L.core.product z=0^2 := by
    simpa using (regValue_zero L.core.product z).mpr (fun _ _ => rfl)
  have conv (i : MixItem) (h : MixView L z i) : MixStatic L i := by
    cases i with
    | inl f => exact h.count
    | inr a => exact ⟨h.count,h.ok,h.preCount,h.preOk⟩
  exact ⟨fun i hi => conv i (accA_views L hw z 0 (by decide) hz i hi),
    fun i hi => conv i (accB_views L hw z 0 (by decide) hz i hi),
    fun i hi => conv i (accC_views L hw z 0 hz i hi)⟩

theorem accBranchA_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (accBranchA L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchA L control) records s).basis=
      resA ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchA L control) records s).basis q=s.basis q := by
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
  have result := withMixed_contribution L hw control hn L.core.low (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) false (accAMix L) s records hc dstZero
    O (M^2) (resA (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp => accA_views L hw t M mb hp)
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accA_mixSum L hw t).trans (L.measuredA_sum hw t (M^2) hp pb))
    (ofCast_lt _ _) (by
      rw [(acc_orientations L).1]
      exact cast_ofCast _ _)
  exact result

theorem accBranchB_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (accBranchB L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchB L control) records s).basis=
      resB ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchB L control) records s).basis q=s.basis q := by
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
  have result := withMixed_contribution L hw control hn L.core.high (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) true (accBMix L) s records hc dstZero
    O (M^2) (resB (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp => accB_views L hw t M mb hp)
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accB_mixSum L hw t (M^2) hp pb).trans (L.measuredB_sum hw t (M^2) hp pb))
    (ofCast_lt _ _) (by
      rw [(acc_orientations L).2.1]
      exact cast_ofCast _ _)
  exact result

theorem accMiddleC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (accMiddleC L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accMiddleC L control) records s).basis=
      resC ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accMiddleC L control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have result := withMixed_contribution L hw control hn L.core.sum L.core.product srcCount
    (fun _ => le_rfl) (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) false (accCMix L) s records hc hp0
    O (M^2) (resC (M^2) O) hO ho (by rw [hs])
    (fun _ hp _ => hp) (fun t hp => accC_views L hw t M hp)
    (-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)
    (fun t hp => (accC_mixSum L hw t).trans (L.measuredC_sum hw t (M^2) hp))
    (ofCast_lt _ _) (by
      rw [(acc_orientations L).2.2]
      exact cast_ofCast _ _)
  exact result

theorem accBranchC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis) :
    (run (accBranchC L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchC L control) records s).basis=
      resC ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchC L control) records s).basis q=s.basis q := by
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
  let middle := accMiddleC L control
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
  have used := accMiddleC_correct L hw control hn (A+B) O hO u
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
  simpa [accBranchC,middle,u,v,out,run_append,prepM] using final

theorem accProgram_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (accProgram L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accProgram L control) records s).basis=
      (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (accProgram L control) records s).basis q=s.basis q := by
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
  let restA := records.drop (measurementCount (accBranchA L control))
  let restB := restA.drop (measurementCount (accBranchB L control))
  let restC := restB.drop (measurementCount (accBranchC L control))
  let u := run (accBranchA L control) (records.take (measurementCount (accBranchA L control))) s
  let v := run (accBranchB L control) (restA.take (measurementCount (accBranchB L control))) u
  let w := run (accBranchC L control) (restB.take (measurementCount (accBranchC L control))) v
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
  have ea := accBranchA_correct L hw control hn A O hO s
    (records.take (measurementCount (accBranchA L control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := accBranchB_correct L hw control hn B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (accBranchB L control))) highU ea.2.1 productU cleanU
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
  have ec := accBranchC_correct L hw control hn A B OB (ofCast_lt _ _) v
    (restB.take (measurementCount (accBranchC L control))) lowV sumV sumBound eb.2.1 productV cleanV
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
  simpa [accProgram,u,v,w,out,restA,restB,restC,enabled,run_append,Nat.add_assoc] using final

theorem accPrefix_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (accPrefix L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accPrefix L control) records s).basis=
      SquareReduction.p-1-(O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (accPrefix L control) records s).basis q=s.basis q := by
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
  let restA := records.drop (measurementCount (accBranchA L control))
  let restB := restA.drop (measurementCount (accBranchB L control))
  let u := run (accBranchA L control) (records.take (measurementCount (accBranchA L control))) s
  let v := run (accBranchB L control) (restA.take (measurementCount (accBranchB L control))) u
  let w := run (accBranchC L control) restB v
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
  have ea := accBranchA_correct L hw control hn A O hO s
    (records.take (measurementCount (accBranchA L control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := accBranchB_correct L hw control hn B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (accBranchB L control))) highU ea.2.1 productU cleanU
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
  have ec := accBranchC_correct L hw control hn A B OB (ofCast_lt _ _) v
    restB lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have ocBound : OC<SquareReduction.p := ofCast_lt _ _
  have fullValue : regValue L.core.out w.basis=
      SquareReduction.p-1-(O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := fast_complete_exact enabled A B O
    rw [split] at exactResult
    unfold subModValue at exactResult
    change SquareReduction.p-1-OC=_ at exactResult
    rw [ec.2.1]
    change OC=_
    omega
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      SquareReduction.p-1-(O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ec.1.trans (eb.1.trans ea.1),fullValue,sameW⟩
  simpa [accPrefix,u,v,w,restA,restB,enabled,run_append,Nat.add_assoc] using final

theorem acc_item_prices (L : CuccaroStreamedSquareWideLayout) :
    (mixFoldsT false (accAMix L)=4200 ∧ mixFoldsM false (accAMix L)=4200) ∧
    (mixFoldsT true (accBMix L)=9868 ∧ mixFoldsM true (accBMix L)=9868) ∧
    (mixFoldsT false (accCMix L)=3245 ∧ mixFoldsM false (accCMix L)=3245) := by
  norm_num [mixFoldsT,mixFoldsM,mixNeg,accAMix,accBMix,accCMix,rot128F,negP,negRot,rotF,rotC,posTop,
    accARaw,accBRaw,accCRaw,sortedItems,nafMinusOneItems,List.filter_cons,Acc.buildT,Acc.sbuildT,preW,termsB,accPrice]

theorem accProgram_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (accProgram L control)=69408 ∧ measurementCount (accProgram L control)=68896 := by
  have st := acc_static L hw
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := L.withMeasuredSquare_counts hw control L.core.low (L.core.product.take 256)
    (mixFolds L false (accAMix L)) (by omega) (by omega) (by omega)
  have b := L.withMeasuredSquare_counts hw control L.core.high (L.core.product.take 256)
    (mixFolds L true (accBMix L)) (by omega) (by omega) (by omega)
  have c := L.withMeasuredSquare_counts hw control L.core.sum L.core.product
    (mixFolds L false (accCMix L)) (by omega) (by omega) (by rw [hw.core.product,su])
  have fa := mixFolds_counts L hw false (accAMix L) st.1
  have fb := mixFolds_counts L hw true (accBMix L) st.2.1
  have fc := mixFolds_counts L hw false (accCMix L) st.2.2
  have prices := acc_item_prices L
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  rw [prices.2.2.1,prices.2.2.2] at fc
  have reflection := (L.measured_small_operation_counts hw).2.2
  have sum := L.core.sum_counts hw.core
  simp only [accProgram,accBranchA,accBranchB,accBranchC,accMiddleC,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    reflection.1,reflection.2,sum.1.1,sum.1.2,sum.2.1,sum.2.2,lo,hi,su,p256,hw.core.product]
  norm_num [signedSquareRowsCount]

theorem accProgram_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (accProgram L control)⊆(control::L.wires).toFinset := by
  have st := acc_static L hw
  have a := mixFolds_support L hw hn control false (accAMix L) st.1
  have b := mixFolds_support L hw hn control true (accBMix L) st.2.1
  have c := mixFolds_support L hw hn control false (accCMix L) st.2.2
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sa : ECDSAAdd.wires (accBranchA L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.low (L.core.product.take 256)
    (mixFolds L false (accAMix L)) (by omega) (by omega) (by omega)
    (by intro q hq; simp [CuccaroStreamedSquareLayout.low] at hq; exact List.mem_append_left _ (List.mem_of_mem_take hq))
    (fun _ hq => List.mem_of_mem_take hq) a
  have sb : ECDSAAdd.wires (accBranchB L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.high (L.core.product.take 256)
    (mixFolds L true (accBMix L)) (by omega) (by omega) (by omega)
    (by intro q hq; exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
    (fun _ hq => List.mem_of_mem_take hq) b
  have sc : ECDSAAdd.wires (accMiddleC L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.sum L.core.product
    (mixFolds L false (accCMix L)) (by omega) (by omega) (by rw [hw.core.product,sum])
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
  simpa only [accProgram,accBranchC,
    wires_append,Finset.union_subset_iff] using And.intro (And.intro (And.intro sa sb)
      (And.intro (And.intro prep sc) unprep)) reflection

theorem accProgram_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (accProgram L control) := by
  have nd := (List.nodup_cons.mp hn).2
  have st := acc_static L hw
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
    (mixFolds_physical L hw nd false (accAMix L) st.1)
  have b := L.withMeasuredSquare_physical control hn _ _ hb hp _
    (mixFolds_physical L hw nd true (accBMix L) st.2.1)
  have c := L.withMeasuredSquare_physical control hn _ _ hs (fun _ => le_rfl) _
    (mixFolds_physical L hw nd false (accCMix L) st.2.2)
  have prep := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).1.1)
  have clear := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).2.1)
  simp only [accProgram,accBranchA,accBranchB,accBranchC,accMiddleC,gatePhysical_append]
  exact ⟨⟨⟨a,b⟩,⟨prep,c⟩,clear⟩,L.reflectOutput_physical nd⟩

theorem accProgram_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : Challenge.gateSlots (accProgram L control) ≤ 5000000 := by
  have st := acc_static L hw
  have bd (items : List MixItem) (h : items=accAMix L ∨ items=accBMix L ∨ items=accCMix L) :
      ∀i∈items,∀a,i=.inr a → a.terms.length≤20 ∧ a.pre.length≤4 := by
    intro i hi a e
    subst e
    rcases h with rfl|rfl|rfl <;>
      simp [accAMix,accBMix,accCMix] at hi <;> rw [hi] <;>
      simp [sortedItems,accARaw,accBRaw,accCRaw,termsB,preW,nafMinusOneItems,List.filter_cons,posTop]
  have ha := mixFolds_gateSlots L hw false (accAMix L) st.1 20 (bd _ (Or.inl rfl))
  have hb := mixFolds_gateSlots L hw true (accBMix L) st.2.1 20 (bd _ (Or.inr (Or.inl rfl)))
  have hc := mixFolds_gateSlots L hw false (accCMix L) st.2.2 20 (bd _ (Or.inr (Or.inr rfl)))
  have la : (accAMix L).length = 3 := rfl
  have lb : (accBMix L).length = 7 := rfl
  have lc : (accCMix L).length = 2 := rfl
  rw [la] at ha
  rw [lb] at hb
  rw [lc] at hc
  have hd : (L.core.product.take 256).length ≤ 258 := by
    simp only [List.length_take]; omega
  have a := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.low _
    (mixFolds L false (accAMix L)) hd
  have b := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.high _
    (mixFolds L true (accBMix L)) hd
  have c := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.sum L.core.product
    (mixFolds L false (accCMix L)) (by rw [hw.core.product])
  have hp := Baselines.cuccaroAdd_gateSlots_le (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin
  have hl := L.core.low_length hw.core
  simp only [List.length_append, List.length_cons, List.length_nil, hl] at hp
  change Challenge.gateSlots L.core.prepareSum ≤ _ at hp
  have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
  simp only [accProgram,accBranchA,accBranchB,accBranchC,accMiddleC,
    CuccaroStreamedSquareLayout.clearSum, Challenge.gateSlots_append, Baselines.reverse_gateSlots]
  omega

theorem accPrefix_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (accPrefix L control)=69153 ∧ measurementCount (accPrefix L control)=68641 := by
  have full := accProgram_counts L hw control
  have r := (L.measured_small_operation_counts hw).2.2
  rw [accProgram_split,toffoliCount_append,measurementCount_append] at full
  omega

theorem accPrefix_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (accPrefix L control)⊆(control::L.wires).toFinset := by
  have full := accProgram_support L hw hn control
  rw [accProgram_split,wires_append] at full
  exact Finset.union_subset_left full

theorem accPrefix_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (accPrefix L control) := by
  have full := accProgram_physical L hw control hn
  rw [accProgram_split,gatePhysical_append] at full
  exact full.1

theorem accPrefix_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : Challenge.gateSlots (accPrefix L control) ≤ 5000000 := by
  have full := accProgram_gateSlots_le L hw control
  rw [accProgram_split,Challenge.gateSlots_append] at full
  omega

end ECDSAAdd.Entrant

end

section
-- ===== FastSquare =====
/-! Point-layout binding of the sign-grouped streamed square, with the same
pool relabeling as the Skywalk Step 4 square. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic ControlledPointLayout Secp256k1 CompressedPointSquare

def fastCandidate (L : ControlledPointLayout) : Program :=
  accPrefix L.dialogStreamedSquareWide L.core.generic

theorem fastCandidate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastCandidate L)=69153 ∧ measurementCount (fastCandidate L)=68641 :=
  accPrefix_counts L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) L.core.generic

theorem fastCandidate_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (fastCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
  have support := accPrefix_support L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn) L.core.generic
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro q hq
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hq
      exact List.mem_of_mem_take hq
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp : q∈L.dialogPool.take 775 → q∈L.dialogPool.take 776 := fun h => small h
    tauto
  exact support.trans embed

theorem fastCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCandidate L) m s).basis=
      p-1-(X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (fastCandidate L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have kernel := accPrefix_correct K hwK L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean
  simpa only [fastCandidate,hb,hp,pow_two] using kernel

theorem fastCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (fastCandidate L) := by
  apply accPrefix_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢; omega

/-- Computable relabeled square: the emitted Step 4 program. -/
def fastSquare (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (fastCandidate L)

noncomputable def fastSquareN (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (fastCandidate L)

theorem fastSquare_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    fastSquare L=fastSquareN L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

private theorem pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

private theorem pull_injective' (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

section StateEq
attribute [local irreducible] run wires fastCandidate

theorem fastSquare_state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (fastSquare L) m s=run (fastCandidate L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (fastCandidate L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (pool_away_x' L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (fastCandidate L) m s) cleanOut
  rw [fastSquare_eq L hw hn,fastSquareN]
  apply pull_injective' e
  have semantic := run_rename e e.injective (fastCandidate L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

theorem fastSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastSquare L) m s).basis=
      p-1-(X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (fastSquare L) m s).basis q=s.basis q := by
  rw [fastSquare_state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc

theorem fastSquare_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastSquare L)=69153 ∧ measurementCount (fastSquare L)=68641 := by
  have renamed := renameProgram_counts (labelFn L.core.poolWire) (fastCandidate L)
  have old := fastCandidate_counts L hw
  rw [fastSquare]
  exact ⟨renamed.1.trans old.1,renamed.2.trans old.2⟩

theorem fastSquare_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (fastSquare L)⊆(residents L++sharedPool L).toFinset := by
  rw [fastSquare_eq L hw hn]
  intro q hq
  rw [fastSquareN,renameProgram_support] at hq
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  have supp := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at supp
  have res : old∈residents L ∨ old∈L.dialogPool.take 776 := by
    simp only [residents,PointAddLayout.pointWires,inPlaceFlags,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false]
    tauto
  rcases res with res|mem
  · rw [resident_fixed L hw hn old res]
    exact List.mem_toFinset.mpr (List.mem_append_left _ res)
  · have prefixView : L.dialogPool.take 776=wireBlock L.core.poolWire 0 776 := by
      simp only [dialogPool,List.take_take,Nat.min_eq_left (show 776 ≤ 2613 by omega)]
      exact (L.core.pool_prefix hw 776 (by omega)).symm
    rw [prefixView] at mem
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) (L.core.poolWire i)=
      L.core.poolWire (indexPermutation i) from
        wire_apply L.core.poolWire (layout_bounded_injective L hw hn) i (by omega)]
    apply List.mem_toFinset.mpr
    apply List.mem_append_right
    rcases prefix_allowed i bound with lo|hi
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr
        ⟨indexPermutation i,by simp [List.mem_range'_1]; omega,rfl⟩))
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨indexPermutation i,by simp [List.mem_range'_1]; omega,rfl⟩))

end StateEq

theorem fastSquare_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact fastCandidate_physical L hw hn

theorem fastSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (fastSquare L) ≤ 5000000 := by
  simpa only [fastSquare,Baselines.rename_gateSlots,fastCandidate]
    using accPrefix_gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) L.core.generic

end ECDSAAdd.Entrant

end

section
-- ===== ZeroFlag =====
/-! Infinity tests read the finite flag.

Under the canonical encoding, `R = O` exactly when the finite flag of `R` is
clear (infinity is encoded with a clear flag, every finite point with a set
flag).  The two full-register comparisons against `pointCode 0` used by the
Skywalk classification are therefore replaced by a single controlled flag test
`t ^= c ∧ ¬finite`, which has the same effect on every boundary state. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout

/-- `t ^= c ∧ ¬f`. -/
def zeroFlag (f c t : Wire) : Program := [.X f, .CCX c f t, .X f]

theorem zeroFlag_run (f c t : Wire) (hcf : c ≠ f) (hft : f ≠ t)
    (s : State) (m : List Bool) :
    run (zeroFlag f c t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis f))⟩ := by
  simp only [zeroFlag, run]
  congr 1
  funext q
  by_cases hq : q = t
  · subst q
    simp [writeBit, Function.update, hft.symm, hcf]
  · by_cases hqf : q = f
    · subst q
      simp [writeBit, Function.update, hft]
    · simp [writeBit, Function.update, hq, hqf]

theorem pointEqual_zero (R : Point) : pointEqual R 0 = !pointFinite R := by
  cases R with
  | zero =>
    have h0 : pointEqual WeierstrassCurve.Affine.Point.zero 0 = true := (pointEqual_true_iff _ _).mpr rfl
    rw [h0]
    rfl
  | some h =>
    have hne : (WeierstrassCurve.Affine.Point.some h : Point) ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero h
    have hf : pointEqual (WeierstrassCurve.Affine.Point.some h) 0 = false := by
      cases hh : pointEqual (WeierstrassCurve.Affine.Point.some h) 0
      · rfl
      · exact absurd ((pointEqual_true_iff _ _).mp hh) hne
    rw [hf]
    simp [pointFinite, coordinates]

section
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem zeroFlag_boundary (R : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (zeroFlag L.point.finite c t)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R 0)))) := by
  have hnd := L.dialogPointZero_nodup hn c t hct hc ht
  simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
    List.mem_append, not_or] at hnd
  have hcf : c ≠ L.point.finite := hnd.1.2.1
  have hft : L.point.finite ≠ t := fun h => hnd.2.1.1 h.symm
  intro s m v
  have hh := zeroFlag_run L.point.finite c t hcf hft s m
  have hfin : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  rw [hfin, ← pointEqual_zero] at hh
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem zeroFlag_equalO (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.infinitySelect)
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R 0)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem zeroFlag_equalI (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.genericSelect)
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R 0)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

end

end ECDSAAdd.Entrant

end

section
-- ===== ShortEqual =====
/-! Short point comparison.

On the curve, two finite points with the same abscissa have ordinates `y` and
`±y`; since `p` is odd, `y` and `p - y` differ in parity unless `y = 0`.  So a
valid encoded point is determined by its finite flag, its full `x` register and
the lowest bit of `y`.  `shortEqual` compares only those 257 wires against the
matching prefix of the classical constant, using the unchanged `equalConstant`
gadget on the first 257 zero ports of the shared pool. -/
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines

/-- `x` and the low bit of `y` (the finite flag is implied: no curve point has `x = 0`). -/
def shortSrc (L : ControlledPointLayout) : List Wire :=
  L.point.x ++ L.point.y.take 1

/-- The matching prefix of `pointCode`. -/
def shortCode (R : Point) : Nat :=
  pointX R + 2^256 * (pointY R % 2)

/-- `t ^= c ∧ (point = C)` on 257 compared wires. -/
def shortEqual (L : ControlledPointLayout) (c t : Wire) (C : Point) : Program :=
  equalConstant c t (zeroPorts (shortSrc L) (L.dialogPool.take 257)) (shortCode C)

theorem seven_lit : (7 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem seven_pow : (7 : Fp) ^ ((p - 1) / 2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by
    norm_num [p]
  have he : (p - 1) / 2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
    rw [← hp]
  rw [he]
  have h := hp ▸ seven_lit
  exact h

theorem x_ne_zero {x y : Fp} (h : curve.toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  subst hx
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp [curve, curveA, curveB] at heq
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y ≠ 0 := by
    rintro rfl
    have h7 : ((7 : ℕ) : Fp) = 0 := by exact_mod_cast heq.symm.trans (by ring)
    rw [ZMod.natCast_eq_zero_iff] at h7
    norm_num [p] at h7
  have h1 : y ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hy
  have hodd : p - 1 = 2 * ((p - 1) / 2) := by norm_num [p]
  rw [hodd, pow_mul, heq, seven_pow] at h1
  have h2 : ((2 : ℕ) : Fp) = 0 := by
    have : (-1 : Fp) + 1 = 1 + 1 := by rw [h1]
    rw [neg_add_cancel] at this
    exact_mod_cast (by rw [this]; norm_num : (2 : Fp) = 0)
  rw [ZMod.natCast_eq_zero_iff] at h2
  norm_num [p] at h2

theorem neg_seven_pow_third_ne : (-7 : Fp) ^ (p / 3) ≠ 1 := by
  unfold Fp p
  reduce_mod_char
  try decide

/-- `-7` is not a cube mod `p`, so no point of `y² = x³ + 7` has `y = 0`. -/
theorem curve_y_ne_zero {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : cy ≠ 0 := by
  intro h0
  have hx0 := x_ne_zero hc
  have he := hc.1
  rw [curve.toAffine.equation_iff] at he
  subst h0
  have h7 : cx ^ 3 = -7 := by
    have h := he
    simp [curve, curveA, curveB] at h
    first
      | exact h
      | exact h.symm
      | linear_combination h
      | linear_combination -h
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hferm : cx ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hp : 3 * (p / 3) = p - 1 := by norm_num [p]
  apply neg_seven_pow_third_ne
  rw [← h7, ← pow_mul, hp, hferm]

theorem cy_ne_neg {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : decide (cy ≠ -cy) = true := by
  apply decide_eq_true
  intro h
  have hy0 := curve_y_ne_zero hc
  have hv : (-cy).val = p - cy.val := by rw [ZMod.neg_val, if_neg hy0]
  have hlt := ZMod.val_lt cy
  have hpos : cy.val ≠ 0 := fun e => hy0 ((ZMod.val_eq_zero cy).mp e)
  have hp2 : p % 2 = 1 := by norm_num [p]
  have hh := congrArg ZMod.val h
  omega

theorem shortCode_lt (R : Point) : shortCode R < 2 * 2^256 := by
  have hp : p < 2^256 := by norm_num [p]
  have hx := (point_coordinates_lt R).1
  have hy : pointY R % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold shortCode
  rcases Nat.lt_succ_iff.mp hy |>.lt_or_eq with h | h
  · have : pointY R % 2 = 0 := by omega
    rw [this]; omega
  · rw [h]; omega

theorem shortCode_eq_iff (R C : Point) : shortCode R = shortCode C ↔ R = C := by
  constructor
  · intro h
    have hp : p < 2^256 := by norm_num [p]
    have hxr := (point_coordinates_lt R).1
    have hxc := (point_coordinates_lt C).1
    have hyr : pointY R % 2 < 2 := Nat.mod_lt _ (by decide)
    have hyc : pointY C % 2 < 2 := Nat.mod_lt _ (by decide)
    have hxy : pointX R = pointX C ∧ pointY R % 2 = pointY C % 2 := by
      unfold shortCode at h
      omega
    cases R with
    | zero =>
      cases C with
      | zero => rfl
      | @some u v hc =>
        exfalso
        have h0 : (0 : Fp).val = u.val := hxy.1
        exact x_ne_zero hc (ZMod.val_injective p (by rw [← h0])).symm
    | @some x y hr =>
      cases C with
      | zero =>
        exfalso
        have h0 : x.val = (0 : Fp).val := hxy.1
        exact x_ne_zero hr (ZMod.val_injective p h0)
      | @some u v hc =>
        have heX : x = u := ZMod.val_injective p hxy.1
        have hpar : y.val % 2 = v.val % 2 := hxy.2
        have heY : y = v := by
          by_cases hyv : y = -v
          · by_cases hv0 : v = 0
            · rw [hyv, hv0, neg_zero]
            · exfalso
              have hneg : y.val = p - v.val := by
                rw [hyv, ZMod.neg_val, if_neg hv0]
              have hvl : v.val < p := ZMod.val_lt v
              have hodd : p % 2 = 1 := by norm_num [p]
              omega
          · exact y_eq_of_x_eq_of_not_inverse hr hc heX hyv
        subst u; subst v; rfl
  · rintro rfl; rfl

theorem regValue_take_one (y : List Wire) (s : BasisState) :
    regValue (y.take 1) s = regValue y s % 2 := by
  cases y with
  | nil => simp [regValue]
  | cons w ys =>
    simp only [List.take_succ_cons, List.take_zero]
    change (if s w then 1 else 0) + 2 * 0 = ((if s w then 1 else 0) + 2 * regValue ys s) % 2
    split <;> omega

theorem shortSrc_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : regValue (shortSrc L) s = shortCode R := by
  have hv := (point_holds L.point R s).mp hp
  rw [shortSrc, regValue_append, show L.point.x.length = 256 from hw.inputX, regValue_take_one,
    hv.2.1, hv.2.2]
  rfl

theorem shortSrc_length (L : ControlledPointLayout) (hw : L.Widths) :
    (shortSrc L).length = 257 := by
  simp [shortSrc, show L.point.x.length = 256 from hw.inputX,
    show L.point.y.length = 256 from hw.inputY]

theorem shortWork_length (L : ControlledPointLayout) (hw : L.Widths) :
    (L.dialogPool.take 257).length = 257 := by
  simp [L.dialogPool_length hw]

theorem short_sublist_inner (L : ControlledPointLayout) :
    (shortSrc L ++ L.dialogPool.take 257).Sublist
      (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) := by
  have h1 : (shortSrc L).Sublist (PointAddLayout.pointWires L.point) := by
    simp only [shortSrc, PointAddLayout.pointWires, List.cons_append]
    exact ((List.Sublist.refl _).append (List.take_sublist 1 _)).cons _
  have h2 : (L.dialogPool.take 257).Sublist (L.dialogPool.take 513) := by
    have he : L.dialogPool.take 257 = (L.dialogPool.take 513).take 257 := by
      rw [List.take_take]; rfl
    rw [he]; exact List.take_sublist _ _
  exact h1.append h2

theorem short_sublist (L : ControlledPointLayout) (c t : Wire) :
    (c :: t :: shortSrc L ++ L.dialogPool.take 257).Sublist
      (c :: t :: PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) :=
  ((short_sublist_inner L).cons_cons t).cons_cons c

theorem short_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) (c t : Wire) (hct : c ≠ t)
    (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags) :
    (c :: t :: shortSrc L ++ L.dialogPool.take 257).Nodup :=
  (L.dialogPointZero_nodup hn c t hct hc ht).sublist (short_sublist L c t)

theorem shortEqual_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hct : c ≠ t) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
    (R C : Point) (s : State) (m : List Bool) (hp : Holds.holds s.basis L.point R)
    (hz : regValue (L.dialogPool.take 257) s.basis = 0) :
    run (shortEqual L c t C) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && pointEqual R C))⟩ := by
  have hh := equalPorts_correct c t (shortSrc L) (L.dialogPool.take 257) (shortCode C)
    ((shortSrc_length L hw).trans (shortWork_length L hw).symm) (short_nodup L hn c t hct hc ht)
    (by rw [shortSrc_length L hw, show (257:ℕ) = 256 + 1 from rfl, Nat.pow_succ, mul_comm]
        exact shortCode_lt C) s m hz
  rw [shortSrc_value L hw R s.basis hp] at hh
  have he : decide (shortCode R = shortCode C) = pointEqual R C := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, shortCode_eq_iff, pointEqual_true_iff]
  rw [he] at hh
  exact hh

/-- Support of the short comparison is inside the support of the full comparison. -/
theorem shortEqual_wires_subset (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire)
    (C : Point) (k : Nat) :
    wires (shortEqual L c t C) ⊆ wires (equalConstant c t L.dialogPointZero k) := by
  have hpl : (PointAddLayout.pointWires L.point).length = (L.dialogPool.take 513).length := by
    simp [PointAddLayout.pointWires, L.dialogPool_length hw,
      show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]
  have hsl := (shortSrc_length L hw).trans (shortWork_length L hw).symm
  rw [shortEqual, equalConstant_wires, equalConstant_wires]
  intro q hq
  simp only [List.mem_toFinset, List.mem_cons] at hq ⊢
  rcases hq with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have hm := (zeroPorts_perm _ _ hsl).subset h
    exact Or.inr (Or.inr ((zeroPorts_perm _ _ hpl).symm.subset ((short_sublist_inner L).subset hm)))

theorem shortEqual_counts (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    toffoliCount (shortEqual L c t C) = 257 ∧ measurementCount (shortEqual L c t C) = 257 := by
  have hl : (zeroPorts (shortSrc L) (L.dialogPool.take 257)).length = 257 := by
    have he := (zeroPorts_maps (shortSrc L) (L.dialogPool.take 257)
      ((shortSrc_length L hw).trans (shortWork_length L hw).symm)).1
    simpa only [List.length_map, shortSrc_length L hw] using congrArg List.length he
  have h := equalConstant_counts c t (zeroPorts (shortSrc L) (L.dialogPool.take 257)) (shortCode C)
  rw [hl] at h
  exact h

theorem shortEqual_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hct : c ≠ t) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
    (C : Point) : GatePhysical (shortEqual L c t C) := by
  have hsl := (shortSrc_length L hw).trans (shortWork_length L hw).symm
  apply equalConstant_physical
  have hperm := ((zeroPorts_perm _ _ hsl).cons t).cons c
  exact hperm.nodup_iff.mpr (short_nodup L hn c t hct hc ht)

theorem shortEqual_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire)
    (C : Point) : gateSlots (shortEqual L c t C) ≤ 2314 := by
  have hl : (zeroPorts (shortSrc L) (L.dialogPool.take 257)).length = 257 := by
    have he := (zeroPorts_maps (shortSrc L) (L.dialogPool.take 257)
      ((shortSrc_length L hw).trans (shortWork_length L hw).symm)).1
    simpa only [List.length_map, shortSrc_length L hw] using congrArg List.length he
  have h := Baselines.equalConstant_gateSlots_le c t
    (zeroPorts (shortSrc L) (L.dialogPool.take 257)) (shortCode C)
  rw [hl] at h
  exact h

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem shortBoundary_equal (R C : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (shortEqual L c t C)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R C)))) := by
  intro s m v
  have hclean : regValue (L.dialogPool.take 257) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := shortEqual_correct L hw hn c t hct hc ht R C s m v.point hclean
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  refine ⟨by rw [hh],v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem shortFlag_equalO (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.control L.infinitySelect C)
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R C)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem shortFlag_equalD (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.core.double L.doubleSelect C)
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ (K && pointEqual R C)) I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) K
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.2.2)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

theorem shortFlag_equalI (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.control L.genericSelect C)
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R C)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

theorem shortFlag_equalH (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.core.equalX L.core.equalNegY C)
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ (E && pointEqual R C)) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) E
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.1)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

end

end ECDSAAdd.Entrant

end

section
-- ===== PairEqual =====
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paired point comparison against `C` and `-C`.

`C` and `-C` share the abscissa, and (by `shortCode_eq_iff`)
the low bit of `y` then decides which of the two a valid point equals.  The
256-wire abscissa test is computed once by the zero-detection AND chain,
both targets read the chain output together with the low `y` bit, and only then
is the chain erased by measurement.  Each target costs one Toffoli instead of a
separate 258-Toffoli comparison. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum

/-- The two chain steps of `ZeroControl` (`t := c ∧ ¬a`, and its measured erase). -/
def chainAnd (c a t : Wire) : Program := [.X a, .CCX c a t, .X a]

def chainErase (c a t : Wire) : Program :=
  [.X a, .measureX t [] [.CZ c a], .X a]

theorem chainAnd_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (s : State) (m : List Bool) :
    run (chainAnd c a t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis a))⟩ := by
  simp only [chainAnd, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=a
  · subst w; simp [writeBit, hca, hat]
  · by_cases ht : w=t
    · subst w; simp [writeBit, hca, Ne.symm hat]
    · simp [writeBit, hw, ht, hca]

theorem chainErase_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (hct : c≠t) (s : State) (m : List Bool)
    (hq : s.basis t = (s.basis c && !s.basis a)) :
    run (chainErase c a t) m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [chainErase, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, hca, hat, hat.symm, hct, hq]
  all_goals
    funext w
    by_cases hw : w=a
    · subst w; simp [hat]
    · simp [Function.update_apply, hw]

/-- `t ^= w ∧ (y = a)`. -/
def bitTest (w y t : Wire) (a : Bool) : Program :=
  if a then [.CCX w y t] else zeroFlag y w t

theorem bitTest_run (w y t : Wire) (a : Bool) (hwy : w≠y) (hyt : y≠t) (hwt : w≠t)
    (s : State) (m : List Bool) :
    run (bitTest w y t a) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis w && (s.basis y == a)))⟩ := by
  cases a with
  | false =>
    simp only [bitTest, Bool.false_eq_true, if_false]
    rw [zeroFlag_run y w t hwy hyt s m]
    cases s.basis y <;> rfl
  | true =>
    simp only [bitTest, if_true, run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=t
    · subst q; cases s.basis y <;> simp [writeBit]
    · simp [writeBit, hq]

/-- Both enabled targets read the chain output `w` and the low `y` bit. -/
def plainTail (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) : Program :=
  (if e₁ then bitTest w y t₁ a₁ else []) ++ (if e₂ then bitTest w y t₂ a₂ else [])

/-- One Toffoli for both targets when the target bits are complementary:
`t₂ ^= t₁`, `t₁ ^= w ∧ (y = a)`, `t₂ ^= t₁`, `t₂ ^= w` leaves `t₂ ^= w ∧ (y = !a)`. -/
def fusedTail (y t₁ t₂ : Wire) (a : Bool) (w : Wire) : Program :=
  .CX t₁ t₂ :: (bitTest w y t₁ a ++ [.CX t₁ t₂, .CX w t₂])

def tailFused (e₁ a₁ e₂ a₂ : Bool) : Bool := e₁ && e₂ && (a₂ == !a₁)

def tailCost (e₁ a₁ e₂ a₂ : Bool) : Nat :=
  if tailFused e₁ a₁ e₂ a₂ then 1 else e₁.toNat + e₂.toNat

theorem tailCost_le (e₁ a₁ e₂ a₂ : Bool) : tailCost e₁ a₁ e₂ a₂ ≤ 2 := by
  cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;> decide

def pairTail (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) : Program :=
  if tailFused e₁ a₁ e₂ a₂ then fusedTail y t₁ t₂ a₁ w else plainTail y t₁ t₂ e₁ a₁ e₂ a₂ w

def pairEffect (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (v : Bool) (s : BasisState) : BasisState :=
  writeBit (writeBit s t₁ (s t₁ ^^ (e₁ && v && (s y == a₁)))) t₂
    (s t₂ ^^ (e₂ && v && (s y == a₂)))

theorem pairTail_counts (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) :
    toffoliCount (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) = tailCost e₁ a₁ e₂ a₂ ∧
    measurementCount (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) = 0 := by
  cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
    simp [pairTail, plainTail, fusedTail, tailFused, tailCost, bitTest, zeroFlag,
      toffoliCount, measurementCount]

theorem plainTail_run (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire)
    (hwy : w≠y) (hw1 : w≠t₁) (hw2 : w≠t₂) (hy1 : y≠t₁) (hy2 : y≠t₂) (h12 : t₁≠t₂)
    (s : State) (m : List Bool) :
    run (plainTail y t₁ t₂ e₁ a₁ e₂ a₂ w) m s =
      ⟨s.phase, pairEffect y t₁ t₂ e₁ a₁ e₂ a₂ (s.basis w) s.basis⟩ := by
  have hfirst : run (if e₁ then bitTest w y t₁ a₁ else []) m s =
      ⟨s.phase, writeBit s.basis t₁ (s.basis t₁ ^^ (e₁ && s.basis w && (s.basis y == a₁)))⟩ := by
    cases e₁
    · simp only [Bool.false_eq_true, if_false, run, Bool.false_and, Bool.xor_false]
      cases s; simp [writeBit]
    · simp only [if_true, Bool.true_and]
      exact bitTest_run w y t₁ a₁ hwy hy1 hw1 s m
  have hm1 : measurementCount (if e₁ then bitTest w y t₁ a₁ else []) = 0 := by
    cases e₁ <;> cases a₁ <;> simp [bitTest, zeroFlag, measurementCount]
  rw [plainTail, run_append, run_take, hfirst, hm1, List.drop_zero]
  cases e₂
  · simp only [Bool.false_eq_true, if_false, run]
    congr 1
    funext q
    simp only [pairEffect, writeBit, Function.update_apply, Bool.false_and, Bool.xor_false]
    by_cases hq2 : q = t₂
    · subst hq2; simp [Ne.symm h12]
    · simp [hq2]
  · simp only [if_true]
    rw [bitTest_run w y t₂ a₂ hwy hy2 hw2]
    congr 1
    funext q
    simp only [pairEffect, writeBit, Function.update_apply, Bool.true_and]
    by_cases hq2 : q=t₂
    · subst q; simp [Ne.symm h12, Ne.symm hw1, hy1.symm, hw1, hy1]
    · by_cases hq1 : q=t₁
      · subst q; simp [h12, hw1, hy1]
      · simp [hq1, hq2]

theorem fusedTail_run (y t₁ t₂ : Wire) (a : Bool) (w : Wire)
    (hwy : w≠y) (hw1 : w≠t₁) (hw2 : w≠t₂) (hy1 : y≠t₁) (hy2 : y≠t₂) (h12 : t₁≠t₂)
    (s : State) (m : List Bool) :
    run (fusedTail y t₁ t₂ a w) m s =
      ⟨s.phase, pairEffect y t₁ t₂ true a true (!a) (s.basis w) s.basis⟩ := by
  cases a <;>
  · simp only [fusedTail, bitTest, zeroFlag, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append, run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq2 : q = t₂
    · subst q
      cases hsw : s.basis w <;> cases hsy : s.basis y <;> cases h1 : s.basis t₁ <;>
        cases h2 : s.basis t₂ <;>
        simp [pairEffect, writeBit, Function.update_apply, hsw, hsy, h1, h2, h12, Ne.symm h12,
          hw1, hw2, hy1, hy2, hwy, Ne.symm hw1, Ne.symm hw2, Ne.symm hy1, Ne.symm hy2, Ne.symm hwy]
    · by_cases hq1 : q = t₁
      · subst q
        cases hsw : s.basis w <;> cases hsy : s.basis y <;> cases h1 : s.basis t₁ <;>
          cases h2 : s.basis t₂ <;>
          simp [pairEffect, writeBit, Function.update_apply, hsw, hsy, h1, h2, h12, Ne.symm h12,
            hw1, hw2, hy1, hy2, hwy, Ne.symm hw1, Ne.symm hw2, Ne.symm hy1, Ne.symm hy2, Ne.symm hwy]
      · by_cases hqy : q = y
        · subst q
          cases hsy : s.basis y <;>
            simp [pairEffect, writeBit, Function.update_apply, hsy, hy1, hy2, hwy, Ne.symm hwy]
        · simp [pairEffect, writeBit, Function.update_apply, hq1, hq2, hqy]

theorem pairTail_run (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire)
    (hwy : w≠y) (hw1 : w≠t₁) (hw2 : w≠t₂) (hy1 : y≠t₁) (hy2 : y≠t₂) (h12 : t₁≠t₂)
    (s : State) (m : List Bool) :
    run (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) m s =
      ⟨s.phase, pairEffect y t₁ t₂ e₁ a₁ e₂ a₂ (s.basis w) s.basis⟩ := by
  by_cases hf : tailFused e₁ a₁ e₂ a₂ = true
  · obtain ⟨rfl, rfl, rfl⟩ : e₁ = true ∧ e₂ = true ∧ a₂ = !a₁ := by
      revert hf; cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;> simp [tailFused]
    rw [pairTail, if_pos hf]
    exact fusedTail_run y t₁ t₂ a₁ w hwy hw1 hw2 hy1 hy2 h12 s m
  · rw [pairTail, if_neg hf]
    exact plainTail_run y t₁ t₂ e₁ a₁ e₂ a₂ w hwy hw1 hw2 hy1 hy2 h12 s m

/-- Zero chain whose innermost step is `T` applied to the chain output. -/
def zeroWith (T : Wire → Program) (c : Wire) : List ZeroBit → Program
  | [] => T c
  | b::bs => chainAnd c b.input b.work ++ zeroWith T b.work bs ++ chainErase c b.input b.work

theorem zeroWith_counts (T : Wire → Program) (n : Nat)
    (hT : ∀ w, toffoliCount (T w) = n ∧ measurementCount (T w) = 0) (c : Wire) (bs : List ZeroBit) :
    toffoliCount (zeroWith T c bs) = bs.length + n ∧
    measurementCount (zeroWith T c bs) = bs.length := by
  induction bs generalizing c with
  | nil => simpa [zeroWith] using hT c
  | cons b bs ih =>
    have h := ih b.work
    simp only [zeroWith, chainAnd, chainErase, toffoliCount_append, measurementCount_append,
      List.length_cons]
    simp [toffoliCount, measurementCount] at h ⊢
    omega

theorem zeroWith_pair_run (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit)
    (hnd : (c::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b∈bs, s.basis b.work=false) :
    run (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) m s =
      ⟨s.phase, pairEffect y t₁ t₂ e₁ a₁ e₂ a₂
        (s.basis c && bs.all (fun b => !s.basis b.input)) s.basis⟩ := by
  induction bs generalizing c s m with
  | nil =>
    have hni := hnd
    simp only [List.flatMap_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      or_false] at hni
    obtain ⟨⟨hcy, hc1, hc2⟩, ⟨hy1, hy2⟩, h12, -⟩ := hni
    simp only [zeroWith, List.all_nil, Bool.and_true]
    exact pairTail_run y t₁ t₂ e₁ a₁ e₂ a₂ c hcy hc1 hc2 hy1 hy2 h12 s m
  | cons b bs ih =>
    have hnames : (c::y::t₁::t₂::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    obtain ⟨⟨hcy, hc1, hc2, hci, hcw, hcR⟩, ⟨hy1, hy2, hyi, hyw, hyR⟩, ⟨h12, h1i, h1w, h1R⟩,
      ⟨h2i, h2w, h2R⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
    have hchild : (b.work::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨Ne.symm hyw, Ne.symm h1w, Ne.symm h2w, hwR⟩, ⟨hy1, hy2, hyR⟩, ⟨h12, h1R⟩, h2R, hR⟩
    let q := s.basis c && !s.basis b.input
    let t : State := ⟨s.phase, writeBit s.basis b.work q⟩
    have hp : run (chainAnd c b.input b.work) m s=t := by
      rw [chainAnd_run c b.input b.work hci hiw]
      simp [t, q, hz b (by simp), writeBit]
    have htail (d : ZeroBit) (hd : d∈bs) : d.work≠b.work ∧ d.input≠b.work := by
      constructor <;> intro he <;> apply hwR <;>
        apply List.mem_flatMap.mpr <;> refine ⟨d,hd,?_⟩ <;> simp [ZeroBit.wires, he]
    have hz' : ∀ d∈bs, t.basis d.work=false := by
      intro d hd
      simpa [t, writeBit, (htail d hd).1] using hz d (by simp [hd])
    have hall : bs.all (fun d => !t.basis d.input) = bs.all (fun d => !s.basis d.input) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro h d hd <;> simpa [t, writeBit, (htail d hd).2] using h d hd
    have hcnt := (zeroWith_counts (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) (tailCost e₁ a₁ e₂ a₂)
      (pairTail_counts y t₁ t₂ e₁ a₁ e₂ a₂) b.work bs).2
    change run (chainAnd c b.input b.work ++ zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) b.work bs ++
      chainErase c b.input b.work) m s = _
    rw [run_append, run_take, run_append, run_take]
    simp only [measurementCount_append, hcnt,
      show measurementCount (chainAnd c b.input b.work)=0 from rfl, Nat.zero_add, List.drop_zero]
    rw [hp, ih b.work hchild t m hz']
    rw [chainErase_run c b.input b.work hci hiw hcw _ _ (by
      simp only [pairEffect, t, writeBit, Function.update_apply]
      simp [Ne.symm h1w, Ne.symm h2w, hcw, hc1, hc2, hiw, Ne.symm h1i, Ne.symm h2i, q])]
    simp only [hall, List.all_cons]
    apply congrArg (State.mk s.phase)
    funext w
    simp only [pairEffect, writeBit, Function.update_apply]
    by_cases hw2 : w=t₂
    · subst w
      simp [h2w, Ne.symm h12, hyw, t, q, writeBit, Function.update_apply, Bool.and_assoc]
    · by_cases hw1 : w=t₁
      · subst w
        simp [hw2, h1w, hyw, t, q, writeBit, Function.update_apply, Bool.and_assoc]
      · by_cases hww : w=b.work
        · subst w
          simp [hw1, hw2, hz b (by simp)]
        · simp [hww, hw1, hw2, t, writeBit, Function.update_apply]


/-! ### Layout instance -/

/-- The abscissa (the part shared by `C` and `-C`). -/
def pairSrc (L : ControlledPointLayout) : List Wire := L.point.x

def pairCode (R : Point) : Nat := pointX R

def pairPorts (L : ControlledPointLayout) : List ZeroBit :=
  zeroPorts (pairSrc L) (L.dialogPool.take 256)

/-- The low bit of the in-place `y` register. -/
def yLow (L : ControlledPointLayout) : Wire := L.point.y.headD L.control

def yBit (R : Point) : Bool := decide (pointY R % 2 = 1)

/-- Negation flips the low bit of `y` (no point has `y = 0`, and `p` is odd). -/
theorem yBit_neg {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    yBit (-(WeierstrassCurve.Affine.Point.some hc : Point)) = !yBit (.some hc) := by
  rw [WeierstrassCurve.Affine.Point.neg_some hc]
  have hy0 := curve_y_ne_zero hc
  have hv : (-cy).val = p - cy.val := by rw [ZMod.neg_val, if_neg hy0]
  have hlt := ZMod.val_lt cy
  have hpos : cy.val ≠ 0 := fun e => hy0 ((ZMod.val_eq_zero cy).mp e)
  have hp2 : p % 2 = 1 := by norm_num [p]
  show decide ((curve.toAffine.negY cx cy).val % 2 = 1) = !decide (cy.val % 2 = 1)
  rw [negY_eq_neg, hv]
  by_cases h : cy.val % 2 = 1
  · have h' : (p - cy.val) % 2 = 0 := by omega
    simp [h, h']
  · have h' : (p - cy.val) % 2 = 1 := by omega
    simp [h, h']

/-- `t₁ ^= e₁ ∧ control ∧ point = C` and `t₂ ^= e₂ ∧ control ∧ point = D`, where `D`
must share the flag/abscissa code of `C` (used with `D = -C`). -/
def pairEqual (L : ControlledPointLayout) (t₁ t₂ : Wire) (e₁ e₂ : Bool) (C D : Point) : Program :=
  xorConstant (pairSrc L) (pairCode C) ++
  zeroWith (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L) ++
  xorConstant (pairSrc L) (pairCode C)

theorem pairCode_lt (R : Point) : pairCode R < 2^256 := by
  have hp : p < 2^256 := by norm_num [p]
  exact (point_coordinates_lt R).1.trans hp

theorem pairCode_neg (C : Point) : pairCode (-C) = pairCode C := by
  cases C with
  | zero => rfl
  | @some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    rfl

theorem shortCode_pair (R : Point) : shortCode R = pairCode R + 2^256 * (pointY R % 2) := by
  rfl

theorem pair_value_eq (R C : Point) :
    (decide (pairCode R = pairCode C) && (yBit R == yBit C)) = pointEqual R C := by
  apply Bool.eq_iff_iff.mpr
  rw [pointEqual_true_iff, ← shortCode_eq_iff, shortCode_pair, shortCode_pair]
  have h1 := pairCode_lt R
  have h2 := pairCode_lt C
  have hyR : pointY R % 2 < 2 := Nat.mod_lt _ (by decide)
  have hyC : pointY C % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, yBit]
  constructor
  · rintro ⟨ha, hb⟩
    rw [ha]
    have : pointY R % 2 = pointY C % 2 := by
      by_cases hr : pointY R % 2 = 1 <;> by_cases hc : pointY C % 2 = 1 <;>
        simp_all <;> omega
    rw [this]
  · intro h
    have ha : pairCode R = pairCode C := by omega
    have hb : pointY R % 2 = pointY C % 2 := by omega
    exact ⟨ha, by rw [hb]⟩

theorem pairSrc_length (L : ControlledPointLayout) (hw : L.Widths) : (pairSrc L).length = 256 := by
  simp [pairSrc, show L.point.x.length = 256 from hw.inputX]

theorem pairWork_length (L : ControlledPointLayout) (hw : L.Widths) :
    (L.dialogPool.take 256).length = 256 := by
  simp [L.dialogPool_length hw]

theorem pairSrc_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : regValue (pairSrc L) s = pairCode R := by
  exact ((point_holds L.point R s).mp hp).2.1

theorem yLow_mem (L : ControlledPointLayout) (hw : L.Widths) : yLow L ∈ L.point.y := by
  have hl : L.point.y.length = 256 := hw.inputY
  unfold yLow
  cases hy : L.point.y with
  | nil => rw [hy] at hl; simp at hl
  | cons w ys => simp

theorem yLow_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : s (yLow L) = yBit R := by
  have hv := (point_holds L.point R s).mp hp
  have hl : L.point.y.length = 256 := hw.inputY
  have hy := hv.2.2
  unfold yLow yBit
  cases hc : L.point.y with
  | nil => rw [hc] at hl; simp at hl
  | cons w ys =>
    rw [hc] at hy
    change (if s w then 1 else 0) + 2 * regValue ys s = pointY R at hy
    simp only [List.headD_cons]
    rw [← hy]
    cases s w <;> simp <;> omega

theorem pair_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂) :
    (L.control :: yLow L :: t₁ :: t₂ :: (pairSrc L ++ L.dialogPool.take 256)).Nodup := by
  have sep := dialogFlag_separation L hn
  have hc1 : L.control ≠ t₁ := fun h => (List.nodup_cons.mp sep).1 (h ▸ ht1)
  have hc2 : L.control ≠ t₂ := fun h => (List.nodup_cons.mp sep).1 (h ▸ ht2)
  have hA : (L.control :: t₁ :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).Nodup := by
    simpa only [List.cons_append] using L.dialogPointZero_nodup hn L.control t₁ hc1 (Or.inl rfl) ht1
  have hB : (L.control :: t₂ :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).Nodup := by
    simpa only [List.cons_append] using L.dialogPointZero_nodup hn L.control t₂ hc2 (Or.inl rfl) ht2
  have a1 := (List.nodup_cons.mp hA).1
  have a2 := (List.nodup_cons.mp (List.nodup_cons.mp hA).2).1
  have b2 := (List.nodup_cons.mp (List.nodup_cons.mp hB).2).1
  have hPP := (List.nodup_cons.mp (List.nodup_cons.mp hA).2).2
  have hsub : (pairSrc L ++ L.dialogPool.take 256).Sublist
      (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) := by
    have h1 : (pairSrc L).Sublist (PointAddLayout.pointWires L.point) := by
      simp only [pairSrc, PointAddLayout.pointWires, List.cons_append]
      exact (List.sublist_append_left _ _).cons _
    have h2 : (L.dialogPool.take 256).Sublist (L.dialogPool.take 513) := by
      have he : L.dialogPool.take 256 = (L.dialogPool.take 513).take 256 := by
        rw [List.take_take]; rfl
      rw [he]; exact List.take_sublist _ _
    exact h1.append h2
  have sub := hsub.subset
  have hyPW : yLow L ∈ PointAddLayout.pointWires L.point := by
    simp [PointAddLayout.pointWires, yLow_mem L hw]
  have hyP : yLow L ∈ PointAddLayout.pointWires L.point ++ L.dialogPool.take 513 :=
    List.mem_append.mpr (Or.inl hyPW)
  have hPWnd := (List.nodup_append.mp hPP)
  have hy_notsrc : yLow L ∉ pairSrc L := by
    intro h
    have hnd : (pairSrc L ++ L.point.y).Nodup := by
      have h0 := hPWnd.1
      simp only [PointAddLayout.pointWires, List.cons_append] at h0
      exact (List.nodup_cons.mp h0).2
    exact (List.nodup_append.mp hnd).2.2 _ h _ (yLow_mem L hw) rfl
  have h2' : (L.dialogPool.take 256).Sublist (L.dialogPool.take 513) := by
    have he : L.dialogPool.take 256 = (L.dialogPool.take 513).take 256 := by
      rw [List.take_take]; rfl
    rw [he]; exact List.take_sublist _ _
  have hy_notwork : yLow L ∉ L.dialogPool.take 256 := fun h =>
    hPWnd.2.2 _ hyPW _ (h2'.subset h) rfl
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
    List.nodup_cons.mpr ⟨?_, hPP.sublist hsub⟩⟩⟩⟩
  · intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    · exact a1 (List.mem_cons_of_mem _ (h ▸ hyP))
    · exact hc1 h
    · exact hc2 h
    · exact a1 (List.mem_cons_of_mem _ (sub h))
  · intro h
    simp only [List.mem_cons, List.mem_append] at h
    rcases h with h | h | h | h
    · exact a2 (h ▸ hyP)
    · exact b2 (h ▸ hyP)
    · exact hy_notsrc h
    · exact hy_notwork h
  · intro h
    simp only [List.mem_cons] at h
    rcases h with h | h
    · exact h12 h
    · exact a2 (sub h)
  · exact fun h => b2 (sub h)

theorem pairPorts_maps (L : ControlledPointLayout) (hw : L.Widths) :
    (pairPorts L).map ZeroBit.input = pairSrc L ∧
    (pairPorts L).map ZeroBit.work = L.dialogPool.take 256 :=
  zeroPorts_maps _ _ ((pairSrc_length L hw).trans (pairWork_length L hw).symm)

theorem pairPorts_length (L : ControlledPointLayout) (hw : L.Widths) : (pairPorts L).length = 256 := by
  have h := congrArg List.length (pairPorts_maps L hw).1
  simpa only [List.length_map, pairSrc_length L hw] using h

theorem pairEqual_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ : Bool) (C D R : Point) (s : State) (m : List Bool)
    (hp : Holds.holds s.basis L.point R) (hz : regValue (L.dialogPool.take 256) s.basis = 0) :
    run (pairEqual L t₁ t₂ e₁ e₂ C D) m s =
      ⟨s.phase, pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
        (s.basis L.control && decide (pairCode R = pairCode C)) s.basis⟩ := by
  have hnd := pair_nodup L hw hn t₁ t₂ ht1 ht2 h12
  have hn4 := hnd
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at hn4
  obtain ⟨⟨hcy, hc1, hc2, hcs, hcw⟩, ⟨hy1, hy2, hys, hyw⟩, ⟨h12', h1s, h1w⟩, ⟨h2s, h2w⟩, hsw⟩ := hn4
  have hsrc : (pairSrc L).Nodup := (List.nodup_append.mp hsw).1
  have hdisj : ∀ q ∈ L.dialogPool.take 256, q ∉ pairSrc L := by
    intro q hq hs
    exact (List.nodup_append.mp hsw).2.2 q hs q hq rfl
  have hmaps := pairPorts_maps L hw
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 256)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hchain : (L.control :: yLow L :: t₁ :: t₂ :: (pairPorts L).flatMap ZeroBit.wires).Nodup :=
    ((((hperm.cons _).cons _).cons _).cons _).nodup_iff.mpr hnd
  have hk : pairCode C < 2^(pairSrc L).length := by
    rw [pairSrc_length L hw]
    exact pairCode_lt C
  have hval : regValue (pairSrc L) s.basis = pairCode R := pairSrc_value L hw R s.basis hp
  obtain ⟨hup, hue, huv⟩ := xorConstant_correct (pairSrc L) hsrc (pairCode C) hk s m
  generalize hu : run (xorConstant (pairSrc L) (pairCode C)) m s = u at hup hue huv
  have hwork (b : ZeroBit) (hb : b ∈ pairPorts L) : b.work ∈ L.dialogPool.take 256 := by
    rw [← hmaps.2]; exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have huz : ∀ b ∈ pairPorts L, u.basis b.work = false := by
    intro b hb
    rw [hue _ (hdisj _ (hwork b hb))]
    exact (regValue_zero _ _).mp hz _ (hwork b hb)
  have hh := zeroWith_pair_run (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
    hchain u m huz
  have hall : (pairPorts L).all (fun b => !u.basis b.input) =
      decide (regValue (pairSrc L) s.basis = pairCode C) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true]
    simp only [Bool.not_eq_true']
    have heq : (∀ b ∈ pairPorts L, u.basis b.input = false) ↔ regValue (pairSrc L) u.basis = 0 := by
      rw [regValue_zero, ← hmaps.1]
      simp
    rw [heq, huv]
    simp
  have hcu : u.basis L.control = s.basis L.control := hue _ hcs
  rw [hall, hcu, hval] at hh
  have hcnt := (zeroWith_counts (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) (tailCost e₁ (yBit C) e₂ (yBit D))
    (pairTail_counts (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L)).2
  rw [pairPorts_length L hw] at hcnt
  rw [pairEqual, run_append, run_take, run_append, run_take]
  simp only [measurementCount_append, (xorConstant_counts _ _).2, hcnt, Nat.zero_add, List.drop_zero]
  rw [hu, hh]
  generalize hvdef : (⟨u.phase, pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
    (s.basis L.control && decide (pairCode R = pairCode C)) u.basis⟩ : State) = v
  have hvb : v.basis = pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
      (s.basis L.control && decide (pairCode R = pairCode C)) u.basis := by rw [← hvdef]
  have hvph : v.phase = u.phase := by rw [← hvdef]
  obtain ⟨hvp, hve, hvv⟩ := xorConstant_correct (pairSrc L) hsrc (pairCode C) hk v (m.drop 256)
  have hvs : regValue (pairSrc L) v.basis = regValue (pairSrc L) u.basis := by
    rw [hvb]
    apply regValue_congr
    intro w hw'
    have hw1 : w ≠ t₁ := fun he => h1s (he ▸ hw')
    have hw2 : w ≠ t₂ := fun he => h2s (he ▸ hw')
    simp [pairEffect, writeBit, Function.update_apply, hw1, hw2]
  have hrestore : regValue (pairSrc L) (run (xorConstant (pairSrc L) (pairCode C)) (m.drop 256) v).basis =
      regValue (pairSrc L) s.basis := by
    rw [hvv, hvs, huv, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  apply (show ∀ a b : State, a.phase = b.phase → a.basis = b.basis → a = b from
    fun ⟨ap, ab⟩ ⟨bp, bb⟩ hp hb => by cases hp; cases hb; rfl)
  · rw [hvp, hvph, hup]
  · funext w
    by_cases hw' : w ∈ pairSrc L
    · rw [(regValue_eq_iff (pairSrc L) _ _).mp hrestore w hw']
      have hw1 : w ≠ t₁ := fun he => h1s (he ▸ hw')
      have hw2 : w ≠ t₂ := fun he => h2s (he ▸ hw')
      simp [pairEffect, writeBit, Function.update_apply, hw1, hw2]
    · rw [hve w hw', hvb]
      have hyu : u.basis (yLow L) = s.basis (yLow L) := hue _ hys
      have h1u : u.basis t₁ = s.basis t₁ := hue _ h1s
      have h2u : u.basis t₂ = s.basis t₂ := hue _ h2s
      have hwu : u.basis w = s.basis w := hue _ hw'
      simp only [pairEffect, writeBit, Function.update_apply, hyu, h1u, h2u]
      split_ifs <;> simp [hwu]

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pairBoundary (R C : Point) (b : Bool) (f : BasisState) (t₁ t₂ : Wire)
    (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ B₁ B₂ : Bool) (hB₁ : B₁ = (b && e₁)) (hB₂ : B₂ = (b && e₂)) :
    Triple (PointDialogBoundary L R b f) (pairEqual L t₁ t₂ e₁ e₂ C (-C))
      (PointDialogBoundary L R b (writeBit (writeBit f t₁ (f t₁ ^^ (B₁ && pointEqual R C))) t₂
        (f t₂ ^^ (B₂ && pointEqual R (-C))))) := by
  intro s m v
  have hclean : regValue (L.dialogPool.take 256) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := pairEqual_correct L hw hn t₁ t₂ ht1 ht2 h12 e₁ e₂ C (-C) R s m v.point hclean
  have hy := yLow_value L hw R s.basis v.point
  have hb := v.control
  have k1 : (e₁ && (s.basis L.control && decide (pairCode R = pairCode C)) &&
      (s.basis (yLow L) == yBit C)) = (B₁ && pointEqual R C) := by
    rw [hB₁, hy, hb, ← pair_value_eq R C]
    generalize decide (pairCode R = pairCode C) = d
    generalize (yBit R == yBit C) = g
    cases e₁ <;> cases b <;> cases d <;> cases g <;> rfl
  have k2 : (e₂ && (s.basis L.control && decide (pairCode R = pairCode C)) &&
      (s.basis (yLow L) == yBit (-C))) = (B₂ && pointEqual R (-C)) := by
    rw [hB₂, hy, hb, ← pair_value_eq R (-C), pairCode_neg]
    generalize decide (pairCode R = pairCode C) = d
    generalize (yBit R == yBit (-C)) = g
    cases e₂ <;> cases b <;> cases d <;> cases g <;> rfl
  have hfin : (run (pairEqual L t₁ t₂ e₁ e₂ C (-C)) m s).basis =
      writeBit (writeBit s.basis t₁ (s.basis t₁ ^^ (B₁ && pointEqual R C))) t₂
        (s.basis t₂ ^^ (B₂ && pointEqual R (-C))) := by
    rw [hh]
    simp only [pairEffect]
    rw [k1, k2]
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hfin]
    simp only [writeBit, Function.update_apply]
    by_cases q2 : q = t₂
    · subst q2; simp [v.flags _ ht2]
    · by_cases q1 : q = t₁
      · subst q1; simp [q2, v.flags _ ht1]
      · simp [q1, q2, v.flags q hq]
  · intro q hq
    rw [hfin]
    have q1 : q ≠ t₁ := fun he => hq (he ▸ ht1)
    have q2 : q ≠ t₂ := fun he => hq (he ▸ ht2)
    simp [writeBit, q1, q2]

/-- Input side: `double ^= K ∧ R = C` and `genericSelect ^= b ∧ R = -C`. -/
theorem pairFlag_input (R C : Point) (cy : Fp) (b O D I G E H K : Bool)
    (hK : K = (b && decide (cy ≠ -cy))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pairEqual L L.doubleSelect L.genericSelect (decide (cy ≠ -cy)) true C (-C))
      (PointDialogBoundary L R b
        (dialogFlagState L O (D ^^ (K && pointEqual R C)) (I ^^ (b && pointEqual R (-C))) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn R C b (dialogFlagState L O D I G E H K) L.doubleSelect L.genericSelect
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    (decide (cy ≠ -cy)) true K b hK (by simp)
  simp only [hr.2.1, hr.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (D ^^ (K && pointEqual R C))).2.1
  have u2 := (dialogFlagState_update L hn O (D ^^ (K && pointEqual R C)) I G E H K
    (I ^^ (b && pointEqual R (-C)))).2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

/-- Output side: `infinitySelect ^= b ∧ S = C` and `equalNegY ^= E ∧ S = -C`. -/
theorem pairFlag_output (S C : Point) (en : Bool) (b O D I G E H K : Bool)
    (hE : E = (b && en)) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (pairEqual L L.infinitySelect L.core.equalNegY true en C (-C))
      (PointDialogBoundary L S b
        (dialogFlagState L (O ^^ (b && pointEqual S C)) D I G E (H ^^ (E && pointEqual S (-C))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn S C b (dialogFlagState L O D I G E H K) L.infinitySelect L.core.equalNegY
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    true en b E (by simp) hE
  simp only [hr.1, hr.2.2.2.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (O ^^ (b && pointEqual S C))).1
  have u2 := (dialogFlagState_update L hn (O ^^ (b && pointEqual S C)) D I G E H K
    (H ^^ (E && pointEqual S (-C)))).2.2.2.2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

end

theorem pairEqual_counts (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire) (e₁ e₂ : Bool)
    (C D : Point) :
    toffoliCount (pairEqual L t₁ t₂ e₁ e₂ C D) = 256 + tailCost e₁ (yBit C) e₂ (yBit D) ∧
    measurementCount (pairEqual L t₁ t₂ e₁ e₂ C D) = 256 := by
  have h := zeroWith_counts (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) (tailCost e₁ (yBit C) e₂ (yBit D))
    (pairTail_counts (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L)
  rw [pairPorts_length L hw] at h
  have x := xorConstant_counts (pairSrc L) (pairCode C)
  simp only [pairEqual, toffoliCount_append, measurementCount_append, x.1, x.2, h.1, h.2]
  refine ⟨?_, ?_⟩
  · omega
  · simp

theorem pairTail_wires (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) :
    wires (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) ⊆ ({w, y, t₁, t₂} : Finset Wire) := by
  intro q hq
  cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
    simp [pairTail, plainTail, fusedTail, tailFused, bitTest, zeroFlag, wires, Instr.wires,
      wires_append] at hq ⊢ <;> tauto

theorem zeroWith_pair_wires (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit) :
    wires (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) ⊆
      (c :: y :: t₁ :: t₂ :: bs.flatMap ZeroBit.wires).toFinset := by
  induction bs generalizing c with
  | nil =>
    intro q hq
    have := pairTail_wires y t₁ t₂ e₁ a₁ e₂ a₂ c (by simpa [zeroWith] using hq)
    simp at this ⊢; tauto
  | cons b bs ih =>
    intro q hq
    simp only [zeroWith, wires_append, Finset.mem_union] at hq
    have hsub := @ih b.work q
    simp [chainAnd, chainErase, wires, Instr.wires, correctionWires, ZeroBit.wires] at hq hsub ⊢
    rcases hq with ((h | h | h) | h) | (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rcases hsub h with h' | h' | h' | h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h')))))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem pairEqual_wires (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire) (e₁ e₂ : Bool)
    (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆
      (L.control :: yLow L :: t₁ :: t₂ :: (pairSrc L ++ L.dialogPool.take 256)).toFinset := by
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 256)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hx := xorConstant_wires_subset (pairSrc L) (pairCode C)
  have hz := zeroWith_pair_wires (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
  intro q hq
  simp only [pairEqual, wires_append, Finset.mem_union] at hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
  rcases hq with (h | h) | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_toFinset.mp (hx h))))))
  · have h' := hz h
    simp only [List.mem_toFinset, List.mem_cons] at h'
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_append.mp (hperm.subset h')))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_toFinset.mp (hx h))))))

theorem pairEqual_sites (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire)
    (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (CompressedPointDialog.sites L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  have hpool := CompressedPointDialog.prefix_small L hw 256 (by decide)
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  simp only [CompressedPointDialog.sites, CompressedPointSquare.residents,
    PointAddLayout.pointWires, List.mem_toFinset, List.mem_append, List.mem_cons]
  rcases h with rfl | rfl | rfl | rfl | h | h
  · simp
  · simp [hy]
  · simp [ht1]
  · simp [ht2]
  · simp [h]
  · exact Or.inr (hpool h)

theorem pairEqual_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ : Bool) (C D : Point) : GatePhysical (pairEqual L t₁ t₂ e₁ e₂ C D) := by
  have hnd := pair_nodup L hw hn t₁ t₂ ht1 ht2 h12
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 256)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hchain : (L.control :: yLow L :: t₁ :: t₂ :: (pairPorts L).flatMap ZeroBit.wires).Nodup :=
    ((((hperm.cons _).cons _).cons _).cons _).nodup_iff.mpr hnd
  simp only [pairEqual, gatePhysical_append]
  refine ⟨⟨xorConstant_physical _ _, ?_⟩, xorConstant_physical _ _⟩
  clear hnd hperm
  generalize L.control = c at hchain ⊢
  generalize pairPorts L = bs at hchain ⊢
  generalize yLow L = y at hchain ⊢
  induction bs generalizing c with
  | nil =>
    simp only [List.flatMap_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      or_false] at hchain
    obtain ⟨⟨hcy, hc1, hc2⟩, ⟨hy1, hy2⟩, h12', -⟩ := hchain
    simp only [zeroWith]
    cases e₁ <;> cases e₂ <;> cases (yBit C) <;> cases (yBit D) <;>
      simp [pairTail, plainTail, fusedTail, tailFused, bitTest, zeroFlag, GatePhysical, PhysicalInstr,
        ProperGate, gatePhysical_append, hc1, hc2, hy1, hy2, h12]
  | cons b bs ih =>
    have hnames : (c::y::t₁::t₂::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hchain
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    obtain ⟨⟨hcy, hc1, hc2, hci, hcw, hcR⟩, ⟨hy1, hy2, hyi, hyw, hyR⟩, ⟨h12, h1i, h1w, h1R⟩,
      ⟨h2i, h2w, h2R⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
    have hchild : (b.work::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨Ne.symm hyw, Ne.symm h1w, Ne.symm h2w, hwR⟩, ⟨hy1, hy2, hyR⟩, ⟨h12, h1R⟩, h2R, hR⟩
    simp only [zeroWith, gatePhysical_append]
    exact ⟨⟨by simp [chainAnd, GatePhysical, PhysicalInstr, ProperGate, hcw, hiw], ih b.work hchild⟩,
      by simp [chainErase, GatePhysical, PhysicalInstr, ProperGate]⟩

theorem zeroWith_pair_slots (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit) :
    gateSlots (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) ≤ 7 * bs.length + 6 := by
  induction bs generalizing c with
  | nil =>
    cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
      simp [zeroWith, pairTail, plainTail, fusedTail, tailFused, bitTest, zeroFlag, gateSlots_append,
        gateSlots_cons, instructionSlots]
  | cons b bs ih =>
    have h := ih b.work
    simp only [zeroWith, chainAnd, chainErase, gateSlots_append, List.length_cons]
    simp only [gateSlots_cons, gateSlots_nil, instructionSlots, List.length_nil, List.length_cons] at h ⊢
    omega

theorem pairEqual_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire)
    (e₁ e₂ : Bool) (C D : Point) : gateSlots (pairEqual L t₁ t₂ e₁ e₂ C D) ≤ 2319 := by
  have hx := Baselines.xorConstant_gateSlots_le (pairSrc L) (pairCode C)
  have hz := zeroWith_pair_slots (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
  rw [pairSrc_length L hw] at hx
  rw [pairPorts_length L hw] at hz
  simp only [pairEqual, gateSlots_append]
  omega

end ECDSAAdd.Entrant

end

section
-- ===== FastConst =====
/-! Compare-first controlled constant modular addition.

`fastAdd` maps `x ↦ x + g·k mod p` and `fastNeg` maps `x ↦ g ? (k - x mod p) : x`.
Each computes its reduction flag with one comparison against a masked
constant, performs one plain addition of a flag-selected constant, and erases
the flag with one measured comparison.  Every scratch wire is restored. -/
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant
open Arithmetic

namespace FastConst

/-- Controlled complement: one CX from `g` onto every wire of `r`. -/
def maskedNot (g : Wire) (r : List Wire) : Program := maskedConstant g r (2^r.length-1)

theorem xorConstant_all (r : List Wire) : xorConstant r (2^r.length-1)=notRegister r := by
  induction r with
  | nil => rfl
  | cons w ws ih =>
    have hp : 0<2^ws.length := Nat.two_pow_pos _
    have e : 2^(ws.length+1)=2*2^ws.length := by rw [Nat.pow_succ]; ring
    have h1 : (2^(ws.length+1)-1)%2=1 := by rw [e]; omega
    have h2 : (2^(ws.length+1)-1)/2=2^ws.length-1 := by rw [e]; omega
    simp only [List.length_cons,xorConstant,h1,if_true,h2,ih,notRegister,List.map_cons]
    rfl

theorem maskedNot_run (g : Wire) (r : List Wire) (hg : g∉r) (s : State) (m : List Bool) :
    run (maskedNot g r) m s=if s.basis g then run (notRegister r) m s else s := by
  rw [maskedNot,maskedConstant_run g r _ hg,xorConstant_all]

variable (K : MeasuredCanonicalModLayout) (g : Wire)

def mutable : List Wire := K.src++K.out++[K.flag]

def Frame (base : BasisState) (S O : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue K.src s=S ∧ regValue K.out s=O ∧ s K.flag=F ∧ ∀q,q∉mutable K → s q=base q

/-- `x ↦ x + g·k mod p` using `3n-2` Toffolis. -/
def fastAdd (c k : Nat) : Program :=
  maskedConstant g K.src (c+k)++notRegister K.src++
  compareLt none K.src K.out K.carry K.cin K.flag++
  notRegister K.src++maskedConstant g K.src (c+k)++
  maskedConstant g K.src k++maskedConstant K.flag K.src k++maskedConstant K.flag K.src (k+c)++
  mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin++
  maskedConstant K.flag K.src (k+c)++maskedConstant K.flag K.src k++
  eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag++
  maskedConstant g K.src k

/-- `x ↦ g ? (k - x mod p) : x` using `3n-2` Toffolis. -/
def fastNeg (p k : Nat) : Program :=
  maskedConstant g K.src (2^K.out.length-1-k)++notRegister K.src++
  compareLt none K.src K.out K.carry K.cin K.flag++
  notRegister K.src++maskedConstant g K.src (2^K.out.length-1-k)++
  maskedNot g K.out++
  maskedConstant g K.src (k+1)++maskedConstant K.flag K.src (k+1)++
  maskedConstant K.flag K.src ((k+1+p)%2^K.out.length)++
  mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin++
  maskedConstant K.flag K.src ((k+1+p)%2^K.out.length)++maskedConstant K.flag K.src (k+1)++
  maskedConstant g K.src (k+1)++
  maskedConstant g K.src (2^K.out.length-1-k)++notRegister K.src++
  eraseLtChain K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag++
  notRegister K.src++maskedConstant g K.src (2^K.out.length-1-k)


/-- `x ↦ g ? (k - x mod p) : (p - 1 - x)` using `3n-2` Toffolis. -/
def fastRefl (p k : Nat) : Program :=
  maskedConstant g K.src (2^K.out.length-1-k)++notRegister K.src++
  compareLt none K.src K.out K.carry K.cin K.flag++
  notRegister K.src++maskedConstant g K.src (2^K.out.length-1-k)++
  notRegister K.out++
  xorConstant K.src p++maskedConstant g K.src p++
  maskedConstant g K.src (k+1)++maskedConstant K.flag K.src (k+1)++
  maskedConstant K.flag K.src ((k+1+p)%2^K.out.length)++
  mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin++
  maskedConstant K.flag K.src ((k+1+p)%2^K.out.length)++maskedConstant K.flag K.src (k+1)++
  maskedConstant g K.src (k+1)++
  maskedConstant g K.src p++xorConstant K.src p++
  maskedConstant g K.src (2^K.out.length-1-k)++notRegister K.src++
  eraseLtChain K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag++
  notRegister K.src++maskedConstant g K.src (2^K.out.length-1-k)

section Facts
variable {K g}

private theorem cnt (hn : (g::K.wires).Nodup) (q : Wire) :
    ((g::K.wires).count q) ≤ 1 := List.nodup_iff_count_le_one.mp hn q

theorem src_nodup (hn : (g::K.wires).Nodup) : K.src.Nodup := by
  apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
  omega

theorem out_nodup (hn : (g::K.wires).Nodup) : K.out.Nodup := by
  apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
  omega

theorem g_not_mutable (hn : (g::K.wires).Nodup) : g∉mutable K := by
  intro bad; have h := cnt hn g; have b := List.count_pos_iff.mpr bad
  simp only [mutable,MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,
    List.count_nil,beq_self_eq_true,if_true] at h b
  omega

theorem g_not_src (hn : (g::K.wires).Nodup) : g∉K.src :=
  fun h => g_not_mutable hn (by simp [mutable,h])

theorem g_not_out (hn : (g::K.wires).Nodup) : g∉K.out :=
  fun h => g_not_mutable hn (by simp [mutable,h])

theorem flag_not_src (hn : (g::K.wires).Nodup) : K.flag∉K.src := by
  intro bad; have h := cnt hn K.flag; have b := List.count_pos_iff.mpr bad
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,
    List.count_nil,beq_self_eq_true,if_true] at h b
  omega

theorem flag_not_out (hn : (g::K.wires).Nodup) : K.flag∉K.out := by
  intro bad; have h := cnt hn K.flag; have b := List.count_pos_iff.mpr bad
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,
    List.count_nil,beq_self_eq_true,if_true] at h b
  omega

theorem out_not_src (hn : (g::K.wires).Nodup) (q : Wire) (hq : q∈K.out) : q∉K.src := by
  intro bad; have h := cnt hn q; have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
  omega

theorem fixed_not_mutable (hn : (g::K.wires).Nodup) (q : Wire) (hq : q∈K.carry++[K.high,K.cin]) :
    q∉mutable K := by
  intro bad; have h := cnt hn q; have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [mutable,MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,
    List.count_nil] at h a b
  omega

theorem compare_nodup (hn : (g::K.wires).Nodup) :
    (K.flag::K.cin::(K.src++K.out++K.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem erase_nodup (hn : (g::K.wires).Nodup) (j : Nat) :
    (K.flag::K.cin::(K.out++K.src++K.carry.take j)).Nodup ∧
      (K.flag::K.cin::(K.src++K.out++K.carry.take j)).Nodup := by
  constructor <;>
  · apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
    have t := (List.take_sublist j K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega

theorem add_nodup (hn : (g::K.wires).Nodup) (j : Nat) :
    (K.cin::(K.out++K.carry.take j)).Nodup ∧
      ∀q∈mappedWires (mappedRead K.src false),q∉K.cin::(K.out++K.carry.take j) := by
  rw [mappedRead_wires]
  constructor
  · apply List.nodup_iff_count.mpr; intro q; have h := cnt hn q
    have t := (List.take_sublist j K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega
  · intro q hq bad; have h := cnt hn q; have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have t := (List.take_sublist j K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h b t
    omega

end Facts

section Steps
variable {K g}
variable (hn : (g::K.wires).Nodup) (n : Nat) (hw : K.Widths n)
include hn hw

theorem step_mask_g (base : BasisState) (S O : Nat) (F : Bool) (v : Nat) (hv : v<2^n) :
    Triple (Frame K base S O F) (maskedConstant g K.src v)
      (Frame K base (S^^^(if base g then v else 0)) O F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct g K.src v (src_nodup hn) (g_not_src hn)
    (by rw [hw.src]; exact hv) s m
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2.2 g (g_not_mutable hn)]
  · rw [regValue_congr _ _ _ (fun q hq => he q (out_not_src hn q hq))]; exact h.2.1
  · rw [he _ (flag_not_src hn)]; exact h.2.2.1
  · intro q hq; rw [he q (fun hs => hq (by simp [mutable,hs]))]; exact h.2.2.2 q hq

theorem step_mask_flag (base : BasisState) (S O : Nat) (F : Bool) (v : Nat) (hv : v<2^n) :
    Triple (Frame K base S O F) (maskedConstant K.flag K.src v)
      (Frame K base (S^^^(if F then v else 0)) O F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct K.flag K.src v (src_nodup hn) (flag_not_src hn)
    (by rw [hw.src]; exact hv) s m
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2.1]
  · rw [regValue_congr _ _ _ (fun q hq => he q (out_not_src hn q hq))]; exact h.2.1
  · rw [he _ (flag_not_src hn)]; exact h.2.2.1
  · intro q hq; rw [he q (fun hs => hq (by simp [mutable,hs]))]; exact h.2.2.2 q hq

theorem step_not_src (base : BasisState) (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F) (notRegister K.src) (Frame K base (2^n-1-S) O F) := by
  intro s m h
  rw [notRegister_correct K.src (src_nodup hn)]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · change regValue K.src (fun w => if w∈K.src then !s.basis w else s.basis w)=_
    rw [regValue_congr K.src _ (fun w => !s.basis w) (by intro w hw; simp [hw]),
      regValue_complement,h.1,hw.src]
  · change regValue K.out (fun w => if w∈K.src then !s.basis w else s.basis w)=_
    rw [regValue_congr K.out _ s.basis (by intro w hw; simp [out_not_src hn w hw])]
    exact h.2.1
  · change (if K.flag∈K.src then !s.basis K.flag else s.basis K.flag)=_
    simp [flag_not_src hn,h.2.2.1]
  · intro q hq
    change (if q∈K.src then !s.basis q else s.basis q)=_
    have : q∉K.src := fun hs => hq (by simp [mutable,hs])
    simp [this,h.2.2.2 q hq]

theorem step_not_out (base : BasisState) (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F) (maskedNot g K.out)
      (Frame K base S (if base g then 2^n-1-O else O) F) := by
  intro s m h
  rw [maskedNot_run g K.out (g_not_out hn)]
  have hg : s.basis g=base g := h.2.2.2 g (g_not_mutable hn)
  rw [hg]
  cases base g
  · exact ⟨rfl,h⟩
  · rw [notRegister_correct K.out (out_nodup hn)]
    refine ⟨rfl,?_,?_,?_,?_⟩
    · change regValue K.src (fun w => if w∈K.out then !s.basis w else s.basis w)=_
      rw [regValue_congr K.src _ s.basis (by
        intro w hw; have : w∉K.out := fun h => out_not_src hn w h hw
        simp [this])]
      exact h.1
    · change regValue K.out (fun w => if w∈K.out then !s.basis w else s.basis w)=_
      rw [regValue_congr K.out _ (fun w => !s.basis w) (by intro w hw; simp [hw]),
        regValue_complement,h.2.1,hw.out]
      simp
    · change (if K.flag∈K.out then !s.basis K.flag else s.basis K.flag)=_
      simp [flag_not_out hn,h.2.2.1]
    · intro q hq
      change (if q∈K.out then !s.basis q else s.basis q)=_
      have : q∉K.out := fun hs => hq (by simp [mutable,hs])
      simp [this,h.2.2.2 q hq]

theorem step_xor_src (base : BasisState) (S O : Nat) (F : Bool) (v : Nat) (hv : v<2^n) :
    Triple (Frame K base S O F) (xorConstant K.src v) (Frame K base (S^^^v) O F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := xorConstant_correct K.src (src_nodup hn) v (by rw [hw.src]; exact hv) s m
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [hval,h.1]
  · rw [regValue_congr _ _ _ (fun q hq => he q (out_not_src hn q hq))]; exact h.2.1
  · rw [he _ (flag_not_src hn)]; exact h.2.2.1
  · intro q hq; rw [he q (fun hs => hq (by simp [mutable,hs]))]; exact h.2.2.2 q hq

theorem step_not_out_all (base : BasisState) (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F) (notRegister K.out) (Frame K base S (2^n-1-O) F) := by
  intro s m h
  rw [notRegister_correct K.out (out_nodup hn)]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · change regValue K.src (fun w => if w∈K.out then !s.basis w else s.basis w)=_
    rw [regValue_congr K.src _ s.basis (by
      intro w hw; have : w∉K.out := fun h => out_not_src hn w h hw
      simp [this])]
    exact h.1
  · change regValue K.out (fun w => if w∈K.out then !s.basis w else s.basis w)=_
    rw [regValue_congr K.out _ (fun w => !s.basis w) (by intro w hw; simp [hw]),
      regValue_complement,h.2.1,hw.out]
  · change (if K.flag∈K.out then !s.basis K.flag else s.basis K.flag)=_
    simp [flag_not_out hn,h.2.2.1]
  · intro q hq
    change (if q∈K.out then !s.basis q else s.basis q)=_
    have : q∉K.out := fun hs => hq (by simp [mutable,hs])
    simp [this,h.2.2.2 q hq]

variable (base : BasisState) (hcarry : ∀q∈K.carry,base q=false) (hcin : base K.cin=false)
include hcarry hcin

theorem step_compare (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F) (compareLt none K.src K.out K.carry K.cin K.flag)
      (Frame K base S O (F^^decide (S<O))) := by
  intro s m h
  have cl (q : Wire) (hq : q∈K.carry) : s.basis q=false :=
    (h.2.2.2 q (fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have ci : s.basis K.cin=false :=
    (h.2.2.2 K.cin (fixed_not_mutable hn K.cin (by simp))).trans hcin
  obtain ⟨hp,he,hv⟩ := compareLt_correct none K.src K.out K.carry K.cin K.flag (compare_nodup hn)
    (by simp) (by rw [hw.src,hw.out]) (by rw [hw.carry,hw.out]) s m ci cl
  have ne (q : Wire) (hq : q∈K.src∨q∈K.out) : q≠K.flag := by
    rintro rfl; rcases hq with hq|hq
    · exact flag_not_src hn hq
    · exact flag_not_out hn hq
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ _ (fun q hq => he q (ne q (Or.inl hq)))]; exact h.1
  · rw [regValue_congr _ _ _ (fun q hq => he q (ne q (Or.inr hq)))]; exact h.2.1
  · rw [hv,h.2.2.1,h.1,h.2.1]; simp [controlValue]
  · intro q hq
    rw [he q (fun e => hq (by simp [mutable,e]))]; exact h.2.2.2 q hq

theorem step_add (npos : 0<n) (S O : Nat) (F : Bool) :
    Triple (Frame K base S O F)
      (mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin)
      (Frame K base S ((S+O)%2^n) F) := by
  intro s m h
  have cl (q : Wire) (hq : q∈K.carry.take (K.out.length-1)) : s.basis q=false := by
    have hq' := List.mem_of_mem_take hq
    exact (h.2.2.2 q (fixed_not_mutable hn q (by simp [hq']))).trans (hcarry q hq')
  have ci : s.basis K.cin=false :=
    (h.2.2.2 K.cin (fixed_not_mutable hn K.cin (by simp))).trans hcin
  have nd := add_nodup hn (K.out.length-1)
  obtain ⟨hp,he,hv⟩ := mappedAdd_correct (mappedRead K.src false) K.out
    (K.carry.take (K.out.length-1)) K.cin nd.1 nd.2
    (by rw [mappedRead_length,hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega) s m cl
  refine ⟨hp,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ _ (fun q hq => he q (fun ho => out_not_src hn q ho hq))]; exact h.1
  · rw [hv,mappedRead_value,h.1,h.2.1,ci,hw.out]; simp
  · rw [he _ (flag_not_out hn)]; exact h.2.2.1
  · intro q hq
    rw [he q (fun e => hq (by simp [mutable,e]))]; exact h.2.2.2 q hq

theorem step_erase_os (npos : 0<n) (S O : Nat) (F : Bool) (hF : F=decide (O<S)) :
    Triple (Frame K base S O F)
      (eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag)
      (Frame K base S O false) := by
  intro s m h
  have cl (q : Wire) (hq : q∈K.carry.take (K.out.length-1)) : s.basis q=false := by
    have hq' := List.mem_of_mem_take hq
    exact (h.2.2.2 q (fixed_not_mutable hn q (by simp [hq']))).trans (hcarry q hq')
  have ci : s.basis K.cin=false :=
    (h.2.2.2 K.cin (fixed_not_mutable hn K.cin (by simp))).trans hcin
  have r := eraseLtChain_correct K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
    (erase_nodup hn _).1 (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out,hw.src]; omega) s m cl
    (by rw [h.2.2.1,h.1,h.2.1,ci,hF]; simp)
  rw [r]
  have ne (q : Wire) (hq : q∈K.src∨q∈K.out) : q≠K.flag := by
    rintro rfl; rcases hq with hq|hq
    · exact flag_not_src hn hq
    · exact flag_not_out hn hq
  refine ⟨rfl,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,ne q (Or.inl hq)])]; exact h.1
  · rw [regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,ne q (Or.inr hq)])]; exact h.2.1
  · simp [writeBit]
  · intro q hq
    have : q≠K.flag := fun e => hq (by simp [mutable,e])
    simp [writeBit,this,h.2.2.2 q hq]

theorem step_erase_so (npos : 0<n) (S O : Nat) (F : Bool) (hF : F=decide (S<O)) :
    Triple (Frame K base S O F)
      (eraseLtChain K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag)
      (Frame K base S O false) := by
  intro s m h
  have cl (q : Wire) (hq : q∈K.carry.take (K.out.length-1)) : s.basis q=false := by
    have hq' := List.mem_of_mem_take hq
    exact (h.2.2.2 q (fixed_not_mutable hn q (by simp [hq']))).trans (hcarry q hq')
  have ci : s.basis K.cin=false :=
    (h.2.2.2 K.cin (fixed_not_mutable hn K.cin (by simp))).trans hcin
  have r := eraseLtChain_correct K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag
    (erase_nodup hn _).2 (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega) s m cl
    (by rw [h.2.2.1,h.1,h.2.1,ci,hF]; simp)
  rw [r]
  have ne (q : Wire) (hq : q∈K.src∨q∈K.out) : q≠K.flag := by
    rintro rfl; rcases hq with hq|hq
    · exact flag_not_src hn hq
    · exact flag_not_out hn hq
  refine ⟨rfl,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,ne q (Or.inl hq)])]; exact h.1
  · rw [regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,ne q (Or.inr hq)])]; exact h.2.1
  · simp [writeBit]
  · intro q hq
    have : q≠K.flag := fun e => hq (by simp [mutable,e])
    simp [writeBit,this,h.2.2.2 q hq]

end Steps


section Main
variable {K g}
variable (hn : (g::K.wires).Nodup) (n : Nat) (hw : K.Widths n) (npos : 0<n)
  (base : BasisState) (hcarry : ∀q∈K.carry,base q=false) (hcin : base K.cin=false)
include hn hw npos hcarry hcin

theorem fastAdd_triple (c p k : Nat) (hpc : p+c=2^n) (hk : k<p) (X : Nat) (hX : X<p) :
    Triple (Frame K base 0 X false) (fastAdd K g c k)
      (Frame K base 0 ((X+(if base g then k else 0))%p) false) := by
  have hck : c+k<2^n := by omega
  have hk2 : k<2^n := by omega
  have hkc : k+c<2^n := by omega
  unfold fastAdd
  refine Triple.conseq (fun _ h => h) (((((((((((((
    step_mask_g hn n hw base 0 X false (c+k) hck).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_compare hn n hw base hcarry hcin _ _ _)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ (c+k) hck)).seq
    (step_mask_g hn n hw base _ _ _ k hk2)).seq
    (step_mask_flag hn n hw base _ _ _ k hk2)).seq
    (step_mask_flag hn n hw base _ _ _ (k+c) hkc)).seq
    (step_add hn n hw base hcarry hcin npos _ _ _)).seq
    (step_mask_flag hn n hw base _ _ _ (k+c) hkc)).seq
    (step_mask_flag hn n hw base _ _ _ k hk2)).seq
    (step_erase_os hn n hw base hcarry hcin npos _ _ _ ?hF)).seq
    (step_mask_g hn n hw base _ _ _ k hk2)) ?post
  case hF =>
    cases hG : base g
    · simp; omega
    · have e1 : 2^n-1-(2^n-1-(c+k))=c+k := by omega
      by_cases hP : 2^n-1-(c+k)<X
      · have w : (k+c+X)%2^n=X+k-p := by
          rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega
        simp [hP,e1,w]; omega
      · have w : (k+X)%2^n=X+k := by rw [Nat.mod_eq_of_lt (by omega)]; omega
        simp [hP,e1,w]
  case post =>
    intro s h
    refine ⟨h.1.trans ?_,h.2.1.trans ?_,h.2.2.1,h.2.2.2⟩
    · cases hG : base g
      · simp
      · by_cases hP : 2^n-1-(c+k)<X <;> simp [hP] <;> omega
    · cases hG : base g
      · have hP : ¬2^n-1<X := by omega
        simp [hP,Nat.mod_eq_of_lt hX,Nat.mod_eq_of_lt (show X<2^n by omega)]
      · have e1 : 2^n-1-(2^n-1-(c+k))=c+k := by omega
        by_cases hP : 2^n-1-(c+k)<X
        · have w : (k+c+X)%2^n=X+k-p := by
            rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega
          have v : (X+k)%p=X+k-p := by
            rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
          simp [hP,e1,w,v]
        · have w : (k+X)%2^n=X+k := by rw [Nat.mod_eq_of_lt (by omega)]; omega
          have v : (X+k)%p=X+k := Nat.mod_eq_of_lt (by omega)
          simp [hP,e1,w,v]

theorem fastNeg_triple (p k : Nat) (hp : p<2^n) (hk : k<p) (X : Nat) (hX : X<p) :
    Triple (Frame K base 0 X false) (fastNeg K g p k)
      (Frame K base 0 (if base g then (k+p-X)%p else X) false) := by
  have hN : K.out.length=n := hw.out
  have hA : 2^K.out.length-1-k<2^n := by rw [hN]; omega
  have hk1 : k+1<2^n := by omega
  have he : (k+1+p)%2^K.out.length<2^n := by rw [hN]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold fastNeg
  refine Triple.conseq (fun _ h => h) ((((((((((((((((((
    step_mask_g hn n hw base 0 X false _ hA).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_compare hn n hw base hcarry hcin _ _ _)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)).seq
    (step_not_out hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ _ hk1)).seq
    (step_mask_flag hn n hw base _ _ _ _ hk1)).seq
    (step_mask_flag hn n hw base _ _ _ _ he)).seq
    (step_add hn n hw base hcarry hcin npos _ _ _)).seq
    (step_mask_flag hn n hw base _ _ _ _ he)).seq
    (step_mask_flag hn n hw base _ _ _ _ hk1)).seq
    (step_mask_g hn n hw base _ _ _ _ hk1)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_erase_so hn n hw base hcarry hcin npos _ _ _ ?hF)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)) ?post
  case hF =>
    rw [hN]
    cases hG : base g
    · simp; omega
    · have e1 : 2^n-1-(2^n-1-k)=k := by omega
      have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
      by_cases hP : k<X
      · have w : ((k+1+p)%2^n+(2^n-1-X))%2^n=k+p-X := by
          rw [Nat.mod_add_mod,show k+1+p+(2^n-1-X)=(k+p-X)+2^n by omega,Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        simp [hP,e1,e2,w]; omega
      · have w : (k+1+(2^n-1-X))%2^n=k-X := by
          rw [show k+1+(2^n-1-X)=(k-X)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
        simp [hP,e1,e2,w]
  case post =>
    intro s h
    refine ⟨h.1.trans ?_,h.2.1.trans ?_,h.2.2.1,h.2.2.2⟩
    · rw [hN]
      cases hG : base g
      · simp
      · have e1 : 2^n-1-(2^n-1-k)=k := by omega
        have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
        by_cases hP : k<X <;> simp [hP,e1,e2]
    · rw [hN]
      cases hG : base g
      · have hP : ¬2^n-1<X := by omega
        simp [hP,Nat.mod_eq_of_lt (show X<2^n by omega)]
      · have e1 : 2^n-1-(2^n-1-k)=k := by omega
        have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
        by_cases hP : k<X
        · have w : ((k+1+p)%2^n+(2^n-1-X))%2^n=k+p-X := by
            rw [Nat.mod_add_mod,show k+1+p+(2^n-1-X)=(k+p-X)+2^n by omega,Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          have v : (k+p-X)%p=k+p-X := Nat.mod_eq_of_lt (by omega)
          simp [hP,e1,e2,w,v]
        · have w : (k+1+(2^n-1-X))%2^n=k-X := by
            rw [show k+1+(2^n-1-X)=(k-X)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
          have v : (k+p-X)%p=k-X := by
            rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega
          simp [hP,e1,e2,w,v]

theorem fastRefl_triple (p k : Nat) (hp : p<2^n) (hk : k<p) (X : Nat) (hX : X<p) :
    Triple (Frame K base 0 X false) (fastRefl K g p k)
      (Frame K base 0 (if base g then (k+p-X)%p else p-1-X) false) := by
  have hN : K.out.length=n := hw.out
  have hA : 2^K.out.length-1-k<2^n := by rw [hN]; omega
  have hk1 : k+1<2^n := by omega
  have he : (k+1+p)%2^K.out.length<2^n := by rw [hN]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold fastRefl
  refine Triple.conseq (fun _ h => h) ((((((((((((((((((((((
    step_mask_g hn n hw base 0 X false _ hA).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_compare hn n hw base hcarry hcin _ _ _)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)).seq
    (step_not_out_all hn n hw base _ _ _)).seq
    (step_xor_src hn n hw base _ _ _ _ hp)).seq
    (step_mask_g hn n hw base _ _ _ _ hp)).seq
    (step_mask_g hn n hw base _ _ _ _ hk1)).seq
    (step_mask_flag hn n hw base _ _ _ _ hk1)).seq
    (step_mask_flag hn n hw base _ _ _ _ he)).seq
    (step_add hn n hw base hcarry hcin npos _ _ _)).seq
    (step_mask_flag hn n hw base _ _ _ _ he)).seq
    (step_mask_flag hn n hw base _ _ _ _ hk1)).seq
    (step_mask_g hn n hw base _ _ _ _ hk1)).seq
    (step_mask_g hn n hw base _ _ _ _ hp)).seq
    (step_xor_src hn n hw base _ _ _ _ hp)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_erase_so hn n hw base hcarry hcin npos _ _ _ ?hF)).seq
    (step_not_src hn n hw base _ _ _)).seq
    (step_mask_g hn n hw base _ _ _ _ hA)) ?post
  case hF =>
    rw [hN]
    cases hG : base g
    · have w : (p+(2^n-1-X))%2^n=p-1-X := by
        rw [show p+(2^n-1-X)=(p-1-X)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
      have hP : ¬2^n-1<X := by omega
      simp [hP,w]; omega
    · have e1 : 2^n-1-(2^n-1-k)=k := by omega
      have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
      by_cases hP : k<X
      · have w : ((k+1+p)%2^n+(2^n-1-X))%2^n=k+p-X := by
          rw [Nat.mod_add_mod,show k+1+p+(2^n-1-X)=(k+p-X)+2^n by omega,Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        simp [hP,e1,e2,w]; omega
      · have w : (k+1+(2^n-1-X))%2^n=k-X := by
          rw [show k+1+(2^n-1-X)=(k-X)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
        simp [hP,e1,e2,w]
  case post =>
    intro s h
    refine ⟨h.1.trans ?_,h.2.1.trans ?_,h.2.2.1,h.2.2.2⟩
    · rw [hN]
      cases hG : base g
      · have hP : ¬2^n-1<X := by omega
        simp [hP]
      · have e1 : 2^n-1-(2^n-1-k)=k := by omega
        have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
        by_cases hP : k<X <;> simp [hP,e1,e2]
    · rw [hN]
      cases hG : base g
      · have w : (p+(2^n-1-X))%2^n=p-1-X := by
          rw [show p+(2^n-1-X)=(p-1-X)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
        have hP : ¬2^n-1<X := by omega
        simp [hP,w]
      · have e1 : 2^n-1-(2^n-1-k)=k := by omega
        have e2 : 2^n-1-(2^n-1-(2^n-1-k))=2^n-1-k := by omega
        by_cases hP : k<X
        · have w : ((k+1+p)%2^n+(2^n-1-X))%2^n=k+p-X := by
            rw [Nat.mod_add_mod,show k+1+p+(2^n-1-X)=(k+p-X)+2^n by omega,Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          have v : (k+p-X)%p=k+p-X := Nat.mod_eq_of_lt (by omega)
          simp [hP,e1,e2,w,v]
        · have w : (k+1+(2^n-1-X))%2^n=k-X := by
            rw [show k+1+(2^n-1-X)=(k-X)+2^n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
          have v : (k+p-X)%p=k-X := by
            rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega
          simp [hP,e1,e2,w,v]

end Main

section Wrappers
variable {K g}

/-- Run-form contract from a frame triple: phase, output value, and every
non-output site restored. -/
theorem run_of_triple (P : Program) (X Y : Nat) (s : State)
    (hT : Triple (Frame K s.basis 0 X false) P (Frame K s.basis 0 Y false))
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X) (hf : s.basis K.flag=false)
    (m : List Bool) :
    (run P m s).phase=s.phase ∧ regValue K.out (run P m s).basis=Y ∧
      ∀q,q∉K.out → (run P m s).basis q=s.basis q := by
  obtain ⟨hp,h⟩ := hT s m ⟨hs,hx,hf,fun _ _ => rfl⟩
  refine ⟨hp,h.2.1,?_⟩
  intro q hq
  by_cases hsrc : q∈K.src
  · rw [(regValue_zero _ _).mp h.1 q hsrc,(regValue_zero _ _).mp hs q hsrc]
  · by_cases hfl : q=K.flag
    · subst q; rw [h.2.2.1,hf]
    · exact h.2.2.2 q (by simp [mutable,hsrc,hq,hfl])

theorem fastAdd_correct (hn : (g::K.wires).Nodup) (n c p k : Nat) (hw : K.Widths n) (npos : 0<n)
    (hpc : p+c=2^n) (hk : k<p) (X : Nat) (hX : X<p) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (fastAdd K g c k) m s).phase=s.phase ∧
    regValue K.out (run (fastAdd K g c k) m s).basis=(X+(if s.basis g then k else 0))%p ∧
    ∀q,q∉K.out → (run (fastAdd K g c k) m s).basis q=s.basis q :=
  run_of_triple _ X _ s (fastAdd_triple hn n hw npos s.basis hc hi c p k hpc hk X hX) hs hx hf m

theorem fastNeg_correct (hn : (g::K.wires).Nodup) (n p k : Nat) (hw : K.Widths n) (npos : 0<n)
    (hp : p<2^n) (hk : k<p) (X : Nat) (hX : X<p) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (fastNeg K g p k) m s).phase=s.phase ∧
    regValue K.out (run (fastNeg K g p k) m s).basis=(if s.basis g then (k+p-X)%p else X) ∧
    ∀q,q∉K.out → (run (fastNeg K g p k) m s).basis q=s.basis q :=
  run_of_triple _ X _ s (fastNeg_triple hn n hw npos s.basis hc hi p k hp hk X hX) hs hx hf m

theorem fastAdd_counts (n c k : Nat) (hw : K.Widths n) (npos : 0<n) :
    toffoliCount (fastAdd K g c k)=3*n-2 ∧ measurementCount (fastAdd K g c k)=3*n-1 := by
  have m1 := maskedConstant_counts g K.src (c+k)
  have m2 := maskedConstant_counts g K.src k
  have m3 := maskedConstant_counts K.flag K.src k
  have m4 := maskedConstant_counts K.flag K.src (k+c)
  have nr := notRegister_counts K.src
  have cmp := (compareLt_counts none K.src K.out K.carry K.cin K.flag (by rw [hw.src,hw.out])
    (by rw [hw.carry,hw.out]))
  have ad := mappedAdd_counts (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by rw [mappedRead_length,hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega)
  have er := eraseLtChain_counts K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
    (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out,hw.src]; omega)
  simp only [fastAdd,toffoliCount_append,measurementCount_append,m1.1,m1.2,m2.1,m2.2,m3.1,m3.2,
    m4.1,m4.2,nr.1,nr.2,cmp.1,cmp.2.1,ad.1,ad.2,er.1,er.2]
  simp only [hw.src,hw.out,Option.isSome_none,Bool.false_eq_true,if_false]
  omega

theorem fastNeg_counts (n p k : Nat) (hw : K.Widths n) (npos : 0<n) :
    toffoliCount (fastNeg K g p k)=3*n-2 ∧ measurementCount (fastNeg K g p k)=3*n-1 := by
  have m1 := maskedConstant_counts g K.src (2^K.out.length-1-k)
  have m2 := maskedConstant_counts g K.src (k+1)
  have m3 := maskedConstant_counts K.flag K.src (k+1)
  have m4 := maskedConstant_counts K.flag K.src ((k+1+p)%2^K.out.length)
  have m5 := maskedConstant_counts g K.out (2^K.out.length-1)
  have nr := notRegister_counts K.src
  have cmp := (compareLt_counts none K.src K.out K.carry K.cin K.flag (by rw [hw.src,hw.out])
    (by rw [hw.carry,hw.out]))
  have ad := mappedAdd_counts (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by rw [mappedRead_length,hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega)
  have er := eraseLtChain_counts K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag
    (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega)
  simp only [fastNeg,maskedNot,toffoliCount_append,measurementCount_append,m1.1,m1.2,m2.1,m2.2,
    m3.1,m3.2,m4.1,m4.2,m5.1,m5.2,nr.1,nr.2,cmp.1,cmp.2.1,ad.1,ad.2,er.1,er.2]
  simp only [hw.src,hw.out,Option.isSome_none,Bool.false_eq_true,if_false]
  omega

theorem fastRefl_correct (hn : (g::K.wires).Nodup) (n p k : Nat) (hw : K.Widths n) (npos : 0<n)
    (hp : p<2^n) (hk : k<p) (X : Nat) (hX : X<p) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hx : regValue K.out s.basis=X) (hf : s.basis K.flag=false)
    (hc : ∀q∈K.carry,s.basis q=false) (hi : s.basis K.cin=false) :
    (run (fastRefl K g p k) m s).phase=s.phase ∧
    regValue K.out (run (fastRefl K g p k) m s).basis=(if s.basis g then (k+p-X)%p else p-1-X) ∧
    ∀q,q∉K.out → (run (fastRefl K g p k) m s).basis q=s.basis q :=
  run_of_triple _ X _ s (fastRefl_triple hn n hw npos s.basis hc hi p k hp hk X hX) hs hx hf m

theorem fastRefl_counts (n p k : Nat) (hw : K.Widths n) (npos : 0<n) :
    toffoliCount (fastRefl K g p k)=3*n-2 ∧ measurementCount (fastRefl K g p k)=3*n-1 := by
  have m1 := maskedConstant_counts g K.src (2^K.out.length-1-k)
  have m2 := maskedConstant_counts g K.src (k+1)
  have m3 := maskedConstant_counts K.flag K.src (k+1)
  have m4 := maskedConstant_counts K.flag K.src ((k+1+p)%2^K.out.length)
  have m6 := maskedConstant_counts g K.src p
  have x1 := xorConstant_counts K.src p
  have nr := notRegister_counts K.src
  have no := notRegister_counts K.out
  have cmp := (compareLt_counts none K.src K.out K.carry K.cin K.flag (by rw [hw.src,hw.out])
    (by rw [hw.carry,hw.out]))
  have ad := mappedAdd_counts (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by rw [mappedRead_length,hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega)
  have er := eraseLtChain_counts K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag
    (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out]; omega)
  simp only [fastRefl,toffoliCount_append,measurementCount_append,m1.1,m1.2,m2.1,m2.2,
    m3.1,m3.2,m4.1,m4.2,m6.1,m6.2,x1.1,x1.2,nr.1,nr.2,no.1,no.2,cmp.1,cmp.2.1,ad.1,ad.2,er.1,er.2]
  simp only [hw.src,hw.out,Option.isSome_none,Bool.false_eq_true,if_false]
  omega

theorem parts_support (hw : ∃ n, K.Widths n) :
    (∀ c'∈g::K.wires,∀ v,wires (maskedConstant c' K.src v)⊆(g::K.wires).toFinset) ∧
    (∀ v,wires (maskedConstant g K.out v)⊆(g::K.wires).toFinset) ∧
    wires (notRegister K.src)⊆(g::K.wires).toFinset ∧
    wires (compareLt none K.src K.out K.carry K.cin K.flag)⊆(g::K.wires).toFinset ∧
    wires (mappedAdd (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin)⊆
      (g::K.wires).toFinset ∧
    wires (eraseLtChain K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag)⊆
      (g::K.wires).toFinset ∧
    wires (eraseLtChain K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag)⊆
      (g::K.wires).toFinset := by
  obtain ⟨n,hw⟩ := hw
  have tk (q : Wire) (h : q∈K.carry.take (K.out.length-1)) : q∈K.carry := List.mem_of_mem_take h
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro c' hc' v q hq
    have h' := List.mem_toFinset.mp (maskedConstant_wires_subset c' K.src v hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_cons] at h'
    rcases h' with rfl|h'
    · exact hc'
    · simp [MeasuredCanonicalModLayout.wires,h']
  · intro v q hq
    have h' := List.mem_toFinset.mp (maskedConstant_wires_subset g K.out v hq)
    apply List.mem_toFinset.mpr
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append] at h' ⊢
    tauto
  · intro q hq
    rw [notRegister_wires] at hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset] at hq
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append]
    tauto
  · intro q hq
    rw [(compareLt_wires none K.src K.out K.carry K.cin K.flag (by rw [hw.src,hw.out])
      (by rw [hw.carry,hw.out])).1] at hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,Option.toList_none,List.nil_append,List.mem_cons,
      List.mem_append] at hq
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false]
    tauto
  · intro q hq
    have h' := List.mem_toFinset.mp (mappedAdd_wires_subset _ _ _ _ hq)
    rw [mappedRead_wires] at h'
    apply List.mem_toFinset.mpr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h'
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false]
    have := tk q
    tauto
  · intro q hq
    have h' := List.mem_toFinset.mp (eraseLtChain_wires_subset _ _ _ _ _ hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h'
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false]
    have := tk q
    tauto
  · intro q hq
    have h' := List.mem_toFinset.mp (eraseLtChain_wires_subset _ _ _ _ _ hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h'
    simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
      or_false]
    have := tk q
    tauto

theorem fastAdd_support (c k : Nat) (hw : ∃ n, K.Widths n) :
    wires (fastAdd K g c k)⊆(g::K.wires).toFinset := by
  obtain ⟨hm,_,hnr,hc,ha,he,_⟩ := parts_support (K:=K) (g:=g) hw
  have hg : g∈g::K.wires := List.mem_cons_self ..
  have hf : K.flag∈g::K.wires := by simp [MeasuredCanonicalModLayout.wires]
  simp only [fastAdd,wires_append]
  repeat' (first | exact hm _ hg _ | exact hm _ hf _ | exact hnr | exact hc | exact ha | exact he | apply Finset.union_subset)

theorem fastNeg_support (p k : Nat) (hw : ∃ n, K.Widths n) :
    wires (fastNeg K g p k)⊆(g::K.wires).toFinset := by
  obtain ⟨hm,ho,hnr,hc,ha,_,he⟩ := parts_support (K:=K) (g:=g) hw
  have hg : g∈g::K.wires := List.mem_cons_self ..
  have hf : K.flag∈g::K.wires := by simp [MeasuredCanonicalModLayout.wires]
  simp only [fastNeg,maskedNot,wires_append]
  repeat' (first | exact hm _ hg _ | exact hm _ hf _ | exact ho _ | exact hnr | exact hc | exact ha | exact he | apply Finset.union_subset)

theorem fastRefl_support (p k : Nat) (hw : ∃ n, K.Widths n) :
    wires (fastRefl K g p k)⊆(g::K.wires).toFinset := by
  obtain ⟨hm,_,hnr,hc,ha,_,he⟩ := parts_support (K:=K) (g:=g) hw
  have hg : g∈g::K.wires := List.mem_cons_self ..
  have hf : K.flag∈g::K.wires := by simp [MeasuredCanonicalModLayout.wires]
  have hx (v : Nat) : wires (xorConstant K.src v)⊆(g::K.wires).toFinset := by
    intro q hq
    have h' := List.mem_toFinset.mp (xorConstant_wires_subset K.src v hq)
    simp [MeasuredCanonicalModLayout.wires,h']
  have ho : wires (notRegister K.out)⊆(g::K.wires).toFinset := by
    intro q hq
    rw [notRegister_wires] at hq
    have h' := List.mem_toFinset.mp hq
    simp [MeasuredCanonicalModLayout.wires,h']
  simp only [fastRefl,wires_append]
  repeat' (first | exact hm _ hg _ | exact hm _ hf _ | exact hx _ | exact ho | exact hnr | exact hc | exact ha | exact he | apply Finset.union_subset)

theorem fastAdd_physical (hn : (g::K.wires).Nodup) (c k : Nat) : GatePhysical (fastAdd K g c k) := by
  have m1 := maskedConstant_physical g K.src (c+k) (g_not_src hn)
  have m2 := maskedConstant_physical g K.src k (g_not_src hn)
  have m3 := maskedConstant_physical K.flag K.src k (flag_not_src hn)
  have m4 := maskedConstant_physical K.flag K.src (k+c) (flag_not_src hn)
  have nr := notRegister_physical K.src
  have cp := compareLt_physical none K.src K.out K.carry K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega) (by simp)
  have nd := add_nodup hn (K.out.length-1)
  have ap := mappedAdd_physical (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by simpa using nd.1) (by
      intro b hb q hq
      apply nd.2 q
      simp only [mappedWires,List.mem_flatMap]
      exact ⟨b,hb,by simpa using hq⟩)
  have ep := eraseLtChain_physical K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    have t := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega)
  simp only [fastAdd,gatePhysical_append]
  tauto

theorem fastNeg_physical (hn : (g::K.wires).Nodup) (p k : Nat) : GatePhysical (fastNeg K g p k) := by
  have m1 := maskedConstant_physical g K.src (2^K.out.length-1-k) (g_not_src hn)
  have m2 := maskedConstant_physical g K.src (k+1) (g_not_src hn)
  have m3 := maskedConstant_physical K.flag K.src (k+1) (flag_not_src hn)
  have m4 := maskedConstant_physical K.flag K.src ((k+1+p)%2^K.out.length) (flag_not_src hn)
  have m5 := maskedConstant_physical g K.out (2^K.out.length-1) (g_not_out hn)
  have nr := notRegister_physical K.src
  have cp := compareLt_physical none K.src K.out K.carry K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega) (by simp)
  have nd := add_nodup hn (K.out.length-1)
  have ap := mappedAdd_physical (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by simpa using nd.1) (by
      intro b hb q hq
      apply nd.2 q
      simp only [mappedWires,List.mem_flatMap]
      exact ⟨b,hb,by simpa using hq⟩)
  have ep := eraseLtChain_physical K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    have t := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega)
  simp only [fastNeg,maskedNot,gatePhysical_append]
  tauto

theorem fastRefl_physical (hn : (g::K.wires).Nodup) (p k : Nat) : GatePhysical (fastRefl K g p k) := by
  have m1 := maskedConstant_physical g K.src (2^K.out.length-1-k) (g_not_src hn)
  have m2 := maskedConstant_physical g K.src (k+1) (g_not_src hn)
  have m3 := maskedConstant_physical K.flag K.src (k+1) (flag_not_src hn)
  have m4 := maskedConstant_physical K.flag K.src ((k+1+p)%2^K.out.length) (flag_not_src hn)
  have m6 := maskedConstant_physical g K.src p (g_not_src hn)
  have x1 := xorConstant_physical K.src p
  have nr := notRegister_physical K.src
  have no := notRegister_physical K.out
  have cp := compareLt_physical none K.src K.out K.carry K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega) (by simp)
  have nd := add_nodup hn (K.out.length-1)
  have ap := mappedAdd_physical (mappedRead K.src false) K.out (K.carry.take (K.out.length-1)) K.cin
    (by simpa using nd.1) (by
      intro b hb q hq
      apply nd.2 q
      simp only [mappedWires,List.mem_flatMap]
      exact ⟨b,hb,by simpa using hq⟩)
  have ep := eraseLtChain_physical K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag (by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count_le_one.mp hn q
    have t := (List.take_sublist (K.out.length-1) K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h t ⊢
    omega)
  simp only [fastRefl,gatePhysical_append]
  tauto

theorem fastRefl_gateSlots_le (n p k : Nat) (hw : K.Widths n) :
    Challenge.gateSlots (fastRefl K g p k) ≤ 80*n+8 := by
  have m1 := Baselines.maskedConstant_gateSlots_le g K.src (2^K.out.length-1-k)
  have m2 := Baselines.maskedConstant_gateSlots_le g K.src (k+1)
  have m3 := Baselines.maskedConstant_gateSlots_le K.flag K.src (k+1)
  have m4 := Baselines.maskedConstant_gateSlots_le K.flag K.src ((k+1+p)%2^K.out.length)
  have m6 := Baselines.maskedConstant_gateSlots_le g K.src p
  have x1 := Baselines.xorConstant_gateSlots_le K.src p
  have cp := Baselines.compareLt_gateSlots_le none K.src K.out K.carry K.cin K.flag
  have ap := Baselines.mappedAdd_gateSlots_le (mappedRead K.src false) K.out
    (K.carry.take (K.out.length-1)) K.cin
  have ep := Baselines.eraseLt_gateSlots_le K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag
  rw [mappedRead_length] at ap
  simp only [fastRefl,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
  have no : K.out.length=n := hw.out
  have cp2 := cp.trans (le_of_eq (show 10*K.src.length+2*K.out.length+4=12*n+4 by
    rw [hw.src,hw.out]; ring))
  rw [hw.src] at m1 m2 m3 m4 m6 x1 ap ep ⊢
  omega

theorem fastAdd_gateSlots_le (n c k : Nat) (hw : K.Widths n) :
    Challenge.gateSlots (fastAdd K g c k) ≤ 60*n+8 := by
  have m1 := Baselines.maskedConstant_gateSlots_le g K.src (c+k)
  have m2 := Baselines.maskedConstant_gateSlots_le g K.src k
  have m3 := Baselines.maskedConstant_gateSlots_le K.flag K.src k
  have m4 := Baselines.maskedConstant_gateSlots_le K.flag K.src (k+c)
  have cp := Baselines.compareLt_gateSlots_le none K.src K.out K.carry K.cin K.flag
  have ap := Baselines.mappedAdd_gateSlots_le (mappedRead K.src false) K.out
    (K.carry.take (K.out.length-1)) K.cin
  have ep := Baselines.eraseLt_gateSlots_le K.out K.src (K.carry.take (K.out.length-1)) K.cin K.flag
  rw [mappedRead_length] at ap
  simp only [fastAdd,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
  have ep2 := ep.trans (le_of_eq (show 14*K.out.length=14*n by rw [hw.out]))
  have cp2 := cp.trans (le_of_eq (show 10*K.src.length+2*K.out.length+4=12*n+4 by
    rw [hw.src,hw.out]; ring))
  rw [hw.src] at m1 m2 m3 m4 ap ⊢
  omega

theorem fastNeg_gateSlots_le (n p k : Nat) (hw : K.Widths n) :
    Challenge.gateSlots (fastNeg K g p k) ≤ 70*n+8 := by
  have m1 := Baselines.maskedConstant_gateSlots_le g K.src (2^K.out.length-1-k)
  have m2 := Baselines.maskedConstant_gateSlots_le g K.src (k+1)
  have m3 := Baselines.maskedConstant_gateSlots_le K.flag K.src (k+1)
  have m4 := Baselines.maskedConstant_gateSlots_le K.flag K.src ((k+1+p)%2^K.out.length)
  have m5 := Baselines.maskedConstant_gateSlots_le g K.out (2^K.out.length-1)
  have cp := Baselines.compareLt_gateSlots_le none K.src K.out K.carry K.cin K.flag
  have ap := Baselines.mappedAdd_gateSlots_le (mappedRead K.src false) K.out
    (K.carry.take (K.out.length-1)) K.cin
  have ep := Baselines.eraseLt_gateSlots_le K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag
  rw [mappedRead_length] at ap
  simp only [fastNeg,maskedNot,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
  have m52 := m5.trans (le_of_eq (show K.out.length=n by rw [hw.out]))
  have cp2 := cp.trans (le_of_eq (show 10*K.src.length+2*K.out.length+4=12*n+4 by
    rw [hw.src,hw.out]; ring))
  rw [hw.src] at m1 m2 m3 m4 ap ep ⊢
  omega

end Wrappers

end FastConst
end ECDSAAdd.Entrant

end

section
-- ===== FastGeneric =====
/-! The Skywalk generic stage with every classical coordinate correction done
by the compare-first constant adder of `FastConst`.  The final reflection and
abscissa correction are fused into one `x ↦ cx - x` step, and the square's
final output reflection is absorbed into the `3cx` correction. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog

def fastConstAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  FastConst.fastAdd (L.recoveryConstant r) L.core.generic SquareReduction.c k.val

def fastConstNeg (L : ControlledPointLayout) (k : Fp) : Program :=
  FastConst.fastNeg (L.recoveryConstant L.point.x) L.core.generic p k.val

def fastConstRefl (L : ControlledPointLayout) (k : Fp) : Program :=
  FastConst.fastRefl (L.recoveryConstant L.point.x) L.core.generic p k.val

def fastGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  fastConstAdd L L.point.x (-cx) ++ fastConstAdd L L.point.y (-cy) ++
  pointCompressedArithmetic L false ++
  fastSquare L ++
  fastConstRefl L (3*cx-1) ++
  pointCompressedArithmetic L true ++
  fastConstNeg L cx ++ fastConstAdd L L.point.y (-cy)

private theorem sub_val' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
private theorem scratch_clean (r : List Wire) (s : State) (hc : regValue L.dialogPool s.basis=0) :
    let K := L.recoveryConstant r
    regValue K.src s.basis=0 ∧ s.basis K.flag=false ∧ (∀q∈K.carry,s.basis q=false) ∧
      s.basis K.cin=false := by
  intro K
  have aux (q : Wire) (hq : q∈K.src++K.carry++[K.high,K.cin,K.flag]) : s.basis q=false := by
    change q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag] at hq
    rw [L.recoveryConstant_pool hw r] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  exact ⟨(regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq])),aux _ (by simp),
    fun q hq => aux q (by simp [hq]),aux _ (by simp)⟩

theorem fastConstAdd_correct (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (X : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue r s.basis=X) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastConstAdd L r k) m s).phase=s.phase ∧
    regValue r (run (fastConstAdd L r k) m s).basis=(X+(if B then k.val else 0))%p ∧
    ∀q,q∉r → (run (fastConstAdd L r k) m s).basis q=s.basis q := by
  have len : r.length=256 := by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY
  have cl := scratch_clean L hw r s hc
  have result := FastConst.fastAdd_correct (L.recoveryConstant_nodup hw hn r hr) 256
    SquareReduction.c p k.val (L.recoveryConstant_widths hw r len) (by decide)
    (by norm_num [p,SquareReduction.c]) k.isLt X hX s m cl.1 hx cl.2.1 cl.2.2.1 cl.2.2.2
  simpa only [fastConstAdd,hb] using result

theorem fastConstNeg_correct (k : Fp) (X : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastConstNeg L k) m s).phase=s.phase ∧
    regValue L.point.x (run (fastConstNeg L k) m s).basis=(if B then (k.val+p-X)%p else X) ∧
    ∀q,q∉L.point.x → (run (fastConstNeg L k) m s).basis q=s.basis q := by
  have cl := scratch_clean L hw L.point.x s hc
  have result := FastConst.fastNeg_correct (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) 256
    p k.val (L.recoveryConstant_widths hw L.point.x hw.inputX) (by decide)
    (by norm_num [p]) k.isLt X hX s m cl.1 hx cl.2.1 cl.2.2.1 cl.2.2.2
  simpa only [fastConstNeg,hb] using result

theorem fastConstRefl_correct (k : Fp) (X : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastConstRefl L k) m s).phase=s.phase ∧
    regValue L.point.x (run (fastConstRefl L k) m s).basis=(if B then (k.val+p-X)%p else p-1-X) ∧
    ∀q,q∉L.point.x → (run (fastConstRefl L k) m s).basis q=s.basis q := by
  have cl := scratch_clean L hw L.point.x s hc
  have result := FastConst.fastRefl_correct (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) 256
    p k.val (L.recoveryConstant_widths hw L.point.x hw.inputX) (by decide)
    (by norm_num [p]) k.isLt X hX s m cl.1 hx cl.2.1 cl.2.2.1 cl.2.2.2
  simpa only [fastConstRefl,hb] using result

variable (X Y : Fp) (G : Bool) (base : BasisState)

theorem fastStep_addX (k : Fp) :
    Triple (PointDialogValues L X Y G base) (fastConstAdd L L.point.x k)
      (PointDialogValues L (X+(if G then k else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl)
    k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt X)] using hx

theorem fastStep_addY (k : Fp) :
    Triple (PointDialogValues L X Y G base) (fastConstAdd L L.point.y k)
      (PointDialogValues L X (Y+(if G then k else 0)) G base) := by
  intro s m v
  obtain ⟨hp,hy,hf⟩ := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl)
    k Y.val G Y.isLt s m v.generic v.y v.clean
  refine ⟨hp,v.withY hn ?_ hf⟩
  cases G <;> simpa [ZMod.val_add,Nat.mod_eq_of_lt (ZMod.val_lt Y)] using hy

theorem fastStep_negX (k : Fp) :
    Triple (PointDialogValues L X Y G base) (fastConstNeg L k)
      (PointDialogValues L (if G then k-X else X) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastConstNeg_correct L hw hn k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G
  · simpa using hx
  · simp only [if_true]; rw [sub_val']; simpa using hx

omit hw hn in
private theorem refl_val (V : Fp) : (-1-V).val=p-1-V.val := by
  have hl : V.val<p := ZMod.val_lt V
  have hp : 1≤p := by norm_num [p]
  have cast : ((p-1-V.val : Nat) : Fp)=-1-V := by
    rw [Nat.cast_sub (by omega : V.val≤p-1),Nat.cast_sub hp]
    simp only [ZMod.natCast_self,Nat.cast_one,zero_sub,ZMod.natCast_zmod_val]
  rw [← cast,ZMod.val_natCast_of_lt (by omega)]

theorem fastStep_refl (k : Fp) :
    Triple (PointDialogValues L X Y G base) (fastConstRefl L k)
      (PointDialogValues L (if G then k-X else -1-X) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastConstRefl_correct L hw hn k X.val G X.isLt s m v.generic v.x v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  cases G
  · simp only [Bool.false_eq_true,if_false] at hx ⊢; rw [refl_val]; exact hx
  · simp only [if_true] at hx ⊢; rw [sub_val']; exact hx

end Correct

section SquareStep
attribute [local irreducible] run fastSquare fastCandidate
private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

theorem fast_step_square (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (fastSquare L)
      (PointDialogValues L (-1-(X-(if G then Y*Y else 0))) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastSquare_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  rw [refl_val,sub_val']
  cases G
  · simpa using hx
  · simpa [ZMod.val_mul] using hx

end SquareStep


section Generic
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
attribute [local irreducible] run pointCompressedArithmetic CompressedPointSquare.computableProgram fastSquare fastCandidate
  pointMeasuredSquareCandidate fastConstAdd fastConstNeg fastConstRefl

theorem fast_generic_true (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (fastGeneric L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := fastStep_addX L hw hn X Y true base (-cx)
  have h2 := fastStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := step_arithmetic L hw hn (X-cx) (Y-cy) true base false (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := fast_step_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := fastStep_refl L hw hn (-1-((X-cx)-a*a)) a true base (3*cx-1)
  simp only [if_true] at h5
  have hd5 : 3*cx-1-(-1-((X-cx)-a*a))=d := by
    have e := hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [← e]; ring
  rw [hd5] at h5
  have h6 := step_arithmetic L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have h7 := fastStep_negX L hw hn d (a*d) true base cx
  simp only [if_true] at h7
  have h8 := fastStep_addY L hw hn (cx-d) (a*d) true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h8
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at h7 h8
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h8
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simpa only [fastGeneric,List.append_assoc] using h

theorem fast_generic_false (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (fastGeneric L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := fastStep_addX L hw hn X Y false base (-cx)
  have h2 := fastStep_addY L hw hn X Y false base (-cy)
  have h3 := step_arithmetic L hw hn X Y false base false (by simp)
  have h4 := fast_step_square L hw hn X Y false base
  have h5 := fastStep_refl L hw hn (-1-X) Y false base (3*cx-1)
  have h6 := step_arithmetic L hw hn X Y false base true (by simp)
  have h7 := fastStep_negX L hw hn X Y false base cx
  have h8 := fastStep_addY L hw hn X Y false base (-cy)
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 h7 h8
  rw [show -1-(-1-X)=X by ring] at h5
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simpa only [fastGeneric,List.append_assoc] using h

theorem fast_boundary_generic (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (fastGeneric L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    obtain ⟨phase,hv⟩ := fast_generic_false L hw hn _ _ cx cy s.basis s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      obtain ⟨phase,hv⟩ := fast_generic_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end Generic

section Resources
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem fastConstAdd_counts (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (fastConstAdd L r k)=766 ∧ measurementCount (fastConstAdd L r k)=767 := by
  have len : r.length=256 := by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY
  exact FastConst.fastAdd_counts 256 _ _ (L.recoveryConstant_widths hw r len) (by decide)

omit hn in
theorem fastConstNeg_counts (k : Fp) :
    toffoliCount (fastConstNeg L k)=766 ∧ measurementCount (fastConstNeg L k)=767 :=
  FastConst.fastNeg_counts 256 _ _ (L.recoveryConstant_widths hw L.point.x hw.inputX) (by decide)

omit hn in
theorem fastConstRefl_counts (k : Fp) :
    toffoliCount (fastConstRefl L k)=766 ∧ measurementCount (fastConstRefl L k)=767 :=
  FastConst.fastRefl_counts 256 _ _ (L.recoveryConstant_widths hw L.point.x hw.inputX) (by decide)

omit hn in
theorem fastGeneric_counts (cx cy : Fp) :
    toffoliCount (fastGeneric L cx cy)=2180993 ∧
    measurementCount (fastGeneric L cx cy)=1521548 := by
  have a k := fastConstAdd_counts L hw L.point.x (Or.inl rfl) k
  have b k := fastConstAdd_counts L hw L.point.y (Or.inr rfl) k
  have c := fastConstNeg_counts L hw cx
  have r := fastConstRefl_counts L hw (3*cx-1)
  have arith := pointCompressedArithmetic_counts L
  have square := fastSquare_counts L hw
  simp only [fastGeneric,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,c.1,c.2,r.1,r.2,arith.1,arith.2.1,arith.2.2.1,arith.2.2.2,
    square.1,square.2]
  norm_num

omit hn in
theorem fastConst_sites (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).toFinset⊆(sites L).toFinset := by
  intro q hq
  have small := prefix_small L hw 515 (Nat.le_refl 515)
  have pool := L.recoveryConstant_pool hw r
  have hq' := List.mem_toFinset.mp hq
  have inpool (h : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ h
  apply List.mem_toFinset.mpr
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at hq'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at hq'
  have pl : q∈L.dialogPool.take 515 → q∈CompressedPointSquare.sharedPool L := fun h => small h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  simp only [sites,CompressedPointSquare.residents,PointAddLayout.pointWires,inPlaceFlags,
    List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
  rcases hr with rfl|rfl <;> tauto

theorem fastGeneric_support (cx cy : Fp) :
    wires (fastGeneric L cx cy)⊆(sites L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (fastConstAdd L r k)⊆(sites L).toFinset :=
    (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩).trans
      (fastConst_sites L hw r hr)
  have cn : wires (fastConstNeg L cx)⊆(sites L).toFinset :=
    (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConst_sites L hw L.point.x (Or.inl rfl))
  have arith (b : Bool) := pointCompressedArithmetic_support L hw b
  have cr : wires (fastConstRefl L (3*cx-1))⊆(sites L).toFinset :=
    (FastConst.fastRefl_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConst_sites L hw L.point.x (Or.inl rfl))
  have square := fastSquare_support L hw hn
  simpa only [fastGeneric,wires_append,Finset.union_subset_iff,sites] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (And.intro
      (ca L.point.x (Or.inl rfl) (-cx)) (ca L.point.y (Or.inr rfl) (-cy)))
      (arith false)) square) cr) (arith true)) cn)
      (ca L.point.y (Or.inr rfl) (-cy))

theorem fastGeneric_physical (cx cy : Fp) : GatePhysical (fastGeneric L cx cy) := by
  have ax (k : Fp) := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c k.val
  have ay (k : Fp) := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) SquareReduction.c k.val
  have ng := FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have di := pointCompressedArithmetic_physical L hw hn false
  have mu := pointCompressedArithmetic_physical L hw hn true
  have rf := FastConst.fastRefl_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p (3*cx-1).val
  have sq := fastSquare_physical L hw hn
  simp only [fastGeneric,fastConstAdd,fastConstNeg,fastConstRefl,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di⟩,sq⟩,rf⟩,mu⟩,ng⟩,ay _⟩

omit hn in
theorem fastGeneric_gateSlots_le (cx cy : Fp) :
    Challenge.gateSlots (fastGeneric L cx cy) ≤ 46300000 := by
  have ax (r : List Wire) (hr : r.length=256) (k : Fp) :=
    FastConst.fastAdd_gateSlots_le (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw r hr)
  have ng := FastConst.fastNeg_gateSlots_le (g:=L.core.generic) 256 p cx.val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a1 := ax L.point.x hw.inputX (-cx)
  have a2 := ax L.point.y hw.inputY (-cy)
  have a3 := FastConst.fastRefl_gateSlots_le (g:=L.core.generic) 256 p (3*cx-1).val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have d := Baselines.pointCompressedArithmetic_gateSlots_le L false
  have e := Baselines.pointCompressedArithmetic_gateSlots_le L true
  have f := fastSquare_gateSlots_le L hw
  simp only [fastGeneric,fastConstAdd,fastConstNeg,fastConstRefl,Challenge.gateSlots_append]
  omega

end Resources

end ECDSAAdd.Entrant

end

section
-- ===== Program =====
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
    toffoliCount (finiteProgram L C cx cy)≤2182025 ∧
    measurementCount (finiteProgram L C cx cy)=1522574 := by
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
  have t1 := tailCost_le (decide (cy≠-cy)) (yBit C) true (yBit (-C))
  have t2 := tailCost_le true (yBit C) (exceptionBit C) (yBit (-C))
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

end

section
-- ===== ArithAvoid =====
/-! The mapped Skywalk arithmetic never touches the logical labels `769`,
`2313` or `2401`–`2408`.

The published support certificate for the arithmetic (`controlled_support`)
places it inside the full 1,899-label inventory.  The arithmetic's actual
gates come from the integer universe (labels below 1,798), from the field
sites (`fieldSite`) and from the history packets, all relocated by the
allocation permutations, which only move labels inside the work/hole region.
None of these is one of the labels above, so their physical images (the
auxiliary carry-in and eight classification/control metadata sites) are not
in the arithmetic's support. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation Secp256k1
attribute [local irreducible] wires OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] dblInPlace halfInPlace copyRegister
attribute [local irreducible] addInPlace subInPlace compareLt
attribute [local irreducible] compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
  NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse

/-- Logical labels avoided by the arithmetic. -/
def badIdx (q : Nat) : Prop := q = 769 ∨ q = 2313 ∨ (2401 ≤ q ∧ q ≤ 2408)

/-- A physical wire that is not the image (under `base`) of a bad label. -/
def goodW (q : Wire) : Prop := ¬ (q = 769 + 16 ∨ q = 2313 + 16 ∨ (2401 + 16 ≤ q ∧ q ≤ 2408 + 16))

def Avoid (P : Program) : Prop := ∀ q ∈ wires P, goodW q

theorem avoid_append {P Q : Program} : Avoid (P ++ Q) ↔ Avoid P ∧ Avoid Q := by
  simp only [Avoid, wires_append, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · intro h q hq; rcases hq with hq | hq
    · exact h.1 q hq
    · exact h.2 q hq

theorem avoid_sub {P Q : Program} (h : wires P ⊆ wires Q) (hq : Avoid Q) : Avoid P :=
  fun q hp => hq q (h hp)

theorem avoid_nil : Avoid [] := by intro q hq; simp [wires] at hq

theorem base_good (q : Nat) (h : ¬ badIdx q) : goodW (base q) := by
  show ¬ (q + 16 = 769 + 16 ∨ q + 16 = 2313 + 16 ∨ (2401 + 16 ≤ q + 16 ∧ q + 16 ≤ 2408 + 16))
  unfold badIdx at h; omega

theorem bad_not_zero (q : Nat) (h : badIdx q) : ¬ zeroRegion q := by
  unfold badIdx at h; unfold zeroRegion workRegion holeRegion; omega

theorem pi0_good (q : Nat) (h : ¬ badIdx q) : ¬ badIdx (pi0 q) := by
  intro hb
  have fix := pi0_outside (pi0 q) (bad_not_zero _ hb)
  have := pi0.injective fix
  exact h (this ▸ hb)

theorem pi_good (j q : Nat) (hj : j < 170) (h : ¬ badIdx q) : ¬ badIdx (pi j q) := by
  intro hb
  have fix := pi_outside j (pi j q) hj (bad_not_zero _ hb)
  have := (pi j).injective fix
  exact h (this ▸ hb)

theorem allPlaced_good (q : Nat) (h : ¬ badIdx q) : goodW (allPlaced q) :=
  base_good _ (pi0_good q h)

theorem placed_good (j q : Nat) (hj : j < 170) (h : ¬ badIdx q) : goodW (placed j q) :=
  base_good _ (pi_good j q hj h)

theorem shared_not_bad (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : ¬ badIdx q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold badIdx
  omega

theorem packet_not_bad (j q : Nat) (hj : j < 170) (h : q∈packetSites j) : ¬ badIdx q := by
  simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold badIdx; unfold H at h
  omega

theorem inventory_not_bad (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) : ¬ badIdx q := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact shared_not_bad q h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    unfold badIdx; omega
  · exact packet_not_bad j q hj h

/-! Field side. -/

theorem cell_avoid (divide : Bool) (j i : Nat) (hj : j < 170)
    (hi0 : 3*j ≤ i) (hi : i < 3*j+3) :
    Avoid (renameProgram (placed j) (logicalCell divide i)) := by
  have g : i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have s : 1028+i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    unfold H
    omega
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 (groupInventory j).toFinset
    (by intro q hq; simp only [groupInventory,List.mem_toFinset,List.mem_append];
        exact Or.inl (Or.inl (List.mem_toFinset.mp hq)))
    (by simp [groupInventory]) (by simp [groupInventory,g])
    (by simp [groupInventory,s]) (by simp [groupInventory])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈groupInventory j := by
    cases divide
    · exact List.mem_toFinset.mp (body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw))
    · exact List.mem_toFinset.mp (body.1 (by simpa only [logicalCell,if_true] using hraw))
  exact placed_good j old hj (inventory_not_bad j old hj belongs)

theorem codec_avoid (j : Nat) (hj : j < 170) :
    Avoid (compressedHistoryEncode (placed j) (3*j)) ∧
    Avoid (compressedHistoryDecode (placed j) (3*j)) := by
  constructor
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inl rfl) q hq
    exact placed_good j _ hj (packet_not_bad j _ hj (history_packet j u))
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inr rfl) q hq
    exact placed_good j _ hj (packet_not_bad j _ hj (history_packet j u))

theorem group_avoid (divide : Bool) (j : Nat) (hj : j < 170) : Avoid (mappedGroup divide j) := by
  have codec := codec_avoid j hj
  have a := cell_avoid divide j (3*j) hj (by omega) (by omega)
  have b := cell_avoid divide j (3*j+1) hj (by omega) (by omega)
  have c := cell_avoid divide j (3*j+2) hj (by omega) (by omega)
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,avoid_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem groups_avoid (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    Avoid (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp only [mappedGroups]; exact avoid_nil
  | succ n ih =>
    have current := group_avoid divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,avoid_append]
    · exact ⟨rest,current⟩
    · exact ⟨current,rest⟩

theorem tail_avoid (divide : Bool) (i : Nat) (hi : i=510 ∨ i=511) :
    Avoid (renameProgram allPlaced (logicalCell divide i)) := by
  let W := (CompressedFieldSupport.sharedSites id 2409++[2400,2410,i,1028+i]).toFinset
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 W
    (by intro q hq; simp only [W,List.mem_toFinset,List.mem_append]; exact Or.inl (List.mem_toFinset.mp hq))
    (by simp [W]) (by simp [W]) (by simp [W]) (by simp [W])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈W := by
    cases divide
    · exact body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw)
    · exact body.1 (by simpa only [logicalCell,if_true] using hraw)
  simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,or_assoc] at belongs
  apply allPlaced_good
  rcases belongs with h|rfl|rfl|rfl|rfl
  · exact shared_not_bad old h
  all_goals unfold badIdx; omega

theorem mappedReplay_avoid (divide : Bool) : Avoid (mappedReplay divide) := by
  have groups := groups_avoid divide 0 170 (by omega)
  have a := tail_avoid divide 510 (by omega)
  have b := tail_avoid divide 511 (by omega)
  cases divide <;> simp only [mappedReplay,Bool.false_eq_true,if_false,if_true,avoid_append]
  · exact ⟨⟨b,a⟩,groups⟩
  · exact ⟨⟨groups,a⟩,b⟩

theorem convert_not_bad (target : Bool) (q : Nat)
    (h : q∈(if target then balancedSharedTargetConvert id else balancedSharedSourceConvert id).wires) :
    ¬ badIdx q := by
  cases target <;> simp only [Bool.false_eq_true,if_false,if_true,
    balancedSharedTargetConvert,balancedSharedSourceConvert,BalancedConvert.Layout.wires,
    wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  all_goals dsimp only [id] at h; unfold badIdx; omega

theorem converters_avoid (canonical : Bool) :
    Avoid (renameProgram allPlaced (converterPair canonical)) := by
  have target := BalancedConvert.support (balancedSharedTargetConvert id)
  have source := BalancedConvert.support (balancedSharedSourceConvert id)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have nb : ¬ badIdx old := by
    cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at hraw
    · rcases hraw with h|h
      · exact convert_not_bad true old (List.mem_toFinset.mp (target.1 h))
      · exact convert_not_bad false old (List.mem_toFinset.mp (source.1 h))
    · rcases hraw with h|h
      · exact convert_not_bad true old (List.mem_toFinset.mp (target.2 h))
      · exact convert_not_bad false old (List.mem_toFinset.mp (source.2 h))
  exact allPlaced_good old nb

theorem copy_avoid : Avoid (renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) := by
  have zword : (skywalkSharedField id).z=wireBlock id 2056 257 := skywalkShared_field_z id
  have aword : (skywalkSharedField id).a=wireBlock id 770 257 := rfl
  have cp := copyRegister_wires_subset none (skywalkSharedField id).z (skywalkSharedField id).a
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member := cp hraw
  rw [zword,aword] at member
  simp only [List.mem_toFinset,Option.toList_none,List.nil_append,wireBlock,List.map_id,
    List.mem_append,List.mem_range'_1] at member
  exact allPlaced_good old (by unfold badIdx; omega)

theorem terminalFieldSegment_avoid (divide : Bool) :
    Avoid (EntryMappedFieldSegmentTrim.terminalFieldSegment divide) := by
  have rp : Avoid (EntryMappedFieldSegmentTrim.terminalReplay divide) :=
    avoid_sub ((EntryMappedFieldSegmentTrim.terminalReplay_support_sub divide).trans
      (EntryMappedFieldSegmentTrim.replay_support_sub divide)) (mappedReplay_avoid divide)
  have a := converters_avoid false
  have b := converters_avoid true
  cases divide <;> simp only [EntryMappedFieldSegmentTrim.terminalFieldSegment,Bool.false_eq_true,
    if_false,if_true,avoid_append]
  · exact ⟨⟨⟨⟨copy_avoid,a⟩,rp⟩,b⟩,avoid_nil⟩
  · exact ⟨⟨⟨⟨avoid_nil,a⟩,rp⟩,b⟩,copy_avoid⟩

theorem selectedFieldSegment_avoid (divide : Bool) : Avoid (selectedFieldSegment divide) :=
  avoid_sub (PenultimateMapped.fieldSegment_support_sub divide) (terminalFieldSegment_avoid divide)

/-! Integer side. -/

theorem integer_good (q : Nat) (h : q < 1798) (h' : q ≠ 769) : goodW (base q) := by
  apply base_good; unfold badIdx; omega

theorem tick_layout_avoid (i : Nat) (hi : i < 512) :
    ∀ q ∈ (compactSkywalkTickLayout base i).wires.toFinset, goodW q := by
  have width := compactSkywalkTick_width_bounds i hi
  have view : (compactSkywalkTickLayout base i).wires =
      ([skywalkPoolPreviousId i,1028+i,i+compactSkywalkTickPreWidth i,i,770]++
      List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
      List.range' 771 (compactSkywalkTickPreWidth i-1)++
      List.range' 1540 (compactSkywalkTickPreWidth i-1)).map base := by
    change base (skywalkPoolPreviousId i)::base (1028+i)::
      base (i+compactSkywalkTickPreWidth i)::base i::base 770::
      ((compactSkywalkTickLayout base i).ah++(compactSkywalkTickLayout base i).bh++
      wireBlock base 1540 (compactSkywalkTickPreWidth i-1)) = _
    rw [compactSkywalkTick_ah base i hi,compactSkywalkTick_bh base i hi]
    simp [wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [List.mem_toFinset,view] at hq
  obtain ⟨old,h,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  by_cases hz : i=0
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; exact integer_good _ (by omega) (by omega)
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; exact integer_good _ (by omega) (by omega)

theorem ticks_avoid (i : Nat) (hi : i < 512) :
    Avoid (compactSkywalkTick base i) ∧ Avoid (compactSkywalkReverseTick base i) :=
  ⟨fun q hq => tick_layout_avoid i hi q (compactSkywalkTick_support base i hi base_pool_nodup hq),
   fun q hq => tick_layout_avoid i hi q (compactSkywalkReverseTick_support base i hi base_pool_nodup hq)⟩

theorem base_codec_avoid (start : Nat) (hs : start+3 ≤ 512) :
    Avoid (compressedHistoryEncode base start) ∧ Avoid (compressedHistoryDecode base start) := by
  have lift (P : Program) (he : P=compressedHistoryEncode base start ∨
      P=compressedHistoryDecode base start) : Avoid P := by
    intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above start hs P he q hq
    have region := compressedHistoryId_region start hs u
    exact integer_good _ (by omega) (by omega)
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem delayed_codec_avoid (i : Nat) (hi : i < 512) :
    Avoid (compressedPackAfter base i) ∧ Avoid (compressedDecodeBefore base i) := by
  cases h : compressedPackDue i
  · simp only [compressedPackAfter,compressedDecodeBefore,h,Bool.false_eq_true,if_false]
    exact ⟨avoid_nil, avoid_nil⟩
  · have due := compressedPackDue_true i h
    have support := base_codec_avoid (i-3) (by omega)
    simpa only [compressedPackAfter,compressedDecodeBefore,h,if_true] using support

theorem integer_avoid (i n : Nat) (h : i+n ≤ 512) :
    Avoid (compressedCompactForward base i n) ∧ Avoid (compressedCompactReverse base i n) := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse]; exact ⟨avoid_nil, avoid_nil⟩
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := ticks_avoid i (by omega)
    have codec := delayed_codec_avoid i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,avoid_append]
    exact ⟨⟨⟨tick.1,codec.1⟩,rest.1⟩,⟨⟨rest.2,codec.2⟩,tick.2⟩⟩

theorem prefixSites_avoid : ∀ q ∈ (NativeFirstDirect.prefixSites base).toFinset, goodW q := by
  intro q hq
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      exact integer_good _ (by omega) (by omega)
    | exact integer_good _ (by omega) (by omega)

theorem clear_avoid : Avoid (skywalkArithmeticClear base) := by
  intro q hq
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact integer_good _ (by omega) (by omega)

theorem kernel_avoid (divide : Bool) : Avoid (kernel divide) := by
  have native := NativeFirstDirect.prefix_support base
  have integer := integer_avoid 1 511 (by omega)
  have known := NativeFirstKnown.inverse_support base
  simp only [kernel,avoid_append]
  exact ⟨⟨⟨⟨⟨⟨fun q hq => prefixSites_avoid q (native.1 hq),integer.1⟩,clear_avoid⟩,
    selectedFieldSegment_avoid divide⟩,clear_avoid⟩,integer.2⟩,
    fun q hq => prefixSites_avoid q (known hq)⟩

/-! The zero-divisor wrapper never uses its auxiliary carry-in. -/

theorem zeroCompare_avoid (x x' : Wire) (xs : List Wire) (c : Wire) (cs : List Wire) (cin target : Wire)
    (good : ∀ q ∈ x :: x' :: xs ++ c :: cs ++ [target], goodW q) :
    Avoid (ZeroSeededConstantCompare.program (x::x'::xs) (c::cs) cin target) := by
  intro q hq
  simp only [ZeroSeededConstantCompare.program, wires_append, Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · simp [ZeroSeededConstantCompare.prepare, wires, Instr.wires] at h
    rcases h with rfl|rfl <;> exact good _ (by simp)
  · have h' := List.mem_toFinset.mp (compareConstantLt_wires_subset _ _ _ _ _ h)
    apply good
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
    tauto
  · simp [ZeroSeededConstantCompare.release, wires, Instr.wires] at h
    rcases h with rfl|rfl <;> exact good _ (by simp)

theorem controlled_avoid (divide : Bool) : Avoid (controlled divide) := by
  have xs : wireBlock base 770 256 = base 770 :: base 771 :: wireBlock base 772 254 := by
    simp [wireBlock, List.range'_succ]
  have cs : wireBlock base 0 255 = base 0 :: wireBlock base 1 254 := by
    simp [wireBlock, List.range'_succ]
  have good : ∀ q ∈ base 770 :: base 771 :: wireBlock base 772 254 ++ base 0 :: wireBlock base 1 254 ++
      [base 2411], goodW q := by
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, wireBlock, List.mem_map,
      List.mem_range'_1] at hq
    rcases hq with ((rfl|rfl|⟨i,hi,rfl⟩)|(rfl|⟨i,hi,rfl⟩))|rfl
    all_goals apply base_good; unfold badIdx; omega
  have cmp := zeroCompare_avoid _ _ _ _ _ (base 2313) (base 2411) good
  have mask : Avoid (maskedConstant (base 2411) (wireBlock base 770 256) 1) := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ hq)
    rw [xs] at h
    exact good q (by simp only [List.mem_cons, List.mem_append] at h ⊢; tauto)
  simp only [controlled, directZeroControlled, directZeroDivisorEnter, directZeroDivisorLeave,
    avoid_append, xs, cs]
  rw [xs] at mask
  exact ⟨⟨cmp, mask⟩, kernel_avoid divide, mask, cmp⟩

end ECDSAAdd.Entrant

end

section
-- ===== QSupport =====
/-! Pool site 1801 is never touched.

The published Skywalk support certificate charges the five pool sites
1800–1804 to the arithmetic.  Site 1801 is the image of logical label 2313,
which the arithmetic avoids (`controlled_avoid`).  Every other block works on
resident sites, on a short pool prefix, or (the square) on relabelled sites
below 945.  So the whole finite-addend program lives in the certified site
inventory with site 1801 removed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout
attribute [local irreducible] wires controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection

/-- The certified pool inventory without site 1801. -/
def sharedPoolQ (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515 ++ wireBlock L.core.poolWire 684 858 ++
    [L.core.poolWire 1800] ++ wireBlock L.core.poolWire 1802 3

def sitesQ (L : ControlledPointLayout) : List Wire :=
  CompressedPointSquare.residents L ++ sharedPoolQ L

theorem sitesQ_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesQ L).length = 1898 := by
  simp only [sitesQ, sharedPoolQ, List.length_append, wireBlock_length, List.length_cons,
    List.length_nil, CompressedPointSquare.residents_length L hw]

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem pool_block (n : Nat) (hn' : n ≤ 2613) : L.dialogPool.take n = wireBlock L.core.poolWire 0 n := by
  simp only [dialogPool, List.take_take, Nat.min_eq_left hn']
  exact (L.core.pool_prefix hw n (by omega)).symm

theorem pool_inj (i j : Nat) (hi : i < 2613) (hj : j < 2613)
    (h : L.core.poolWire i = L.core.poolWire j) : i = j := by
  have nd : (wireBlock L.core.poolWire 0 2613).Nodup := by
    rw [← pool_block L hw 2613 (le_refl _)]
    exact (List.take_sublist _ _).nodup (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.1
  have := List.inj_on_of_nodup_map nd (x := i) (y := j)
    (by simp [List.mem_range'_1]; omega) (by simp [List.mem_range'_1]; omega) h
  exact this

omit hn in
theorem p1801_pool : L.core.poolWire 1801 ∈ L.dialogPool := by
  have : L.core.poolWire 1801 ∈ L.dialogPool.take 2613 := by
    rw [pool_block L hw 2613 (le_refl _)]
    exact List.mem_map.mpr ⟨1801, by simp [List.mem_range'_1], rfl⟩
  exact List.mem_of_mem_take this

theorem p1801_not_resident : L.core.poolWire 1801 ∉ CompressedPointSquare.residents L := by
  intro h
  have dis := (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.2
  exact dis _ (by simpa [dialogUsedWires, CompressedPointSquare.residents] using h) _
    (p1801_pool L hw) rfl

theorem p1801_not_take (k : Nat) (hk : k ≤ 1801) : L.core.poolWire 1801 ∉ L.dialogPool.take k := by
  rw [pool_block L hw k (by omega)]
  intro h
  obtain ⟨i, hi, he⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hi
  have := pool_inj L hw hn i 1801 (by omega) (by omega) he
  omega

/-- Any block confined to residents and a short pool prefix avoids site 1801. -/
theorem p1801_of_subset (P : Program) (k : Nat) (hk : k ≤ 1801)
    (h : wires P ⊆ (CompressedPointSquare.residents L ++ L.dialogPool.take k).toFinset) :
    L.core.poolWire 1801 ∉ wires P := by
  intro hp
  have := List.mem_toFinset.mp (h hp)
  rcases List.mem_append.mp this with h1 | h1
  · exact p1801_not_resident L hw hn h1
  · exact p1801_not_take L hw hn k hk h1

theorem p1801_arith (multiply : Bool) :
    L.core.poolWire 1801 ∉ wires (pointCompressedArithmetic L multiply) := by
  intro hq
  rw [pointCompressedArithmetic, renameProgram_support] at hq
  obtain ⟨old, used, he⟩ := Finset.mem_image.mp hq
  have hslot := controlled_support (!multiply) used
  have hgood := controlled_avoid (!multiply) old used
  have hbase : base 2313 ∈ slots.toFinset := by
    apply slot_mem
    · unfold live; omega
    · unfold CompressedAllocation.omitted; omega
  have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
    simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
    simp [skywalkDirectMap, skywalkPointWire]
  have := pointWireFn_injective_slots L hw hn old hslot (base 2313) hbase (he.trans himg.symm)
  subst this
  exact hgood (by simp [base])

theorem p1801_square : L.core.poolWire 1801 ∉ wires (CompressedPointSquare.computableProgram L) := by
  rw [CompressedPointSquare.computableProgram_eq L hw hn]
  intro hq
  rw [CompressedPointSquare.program, renameProgram_support] at hq
  obtain ⟨old, used, he⟩ := Finset.mem_image.mp hq
  have supp := pointMeasuredSquareCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at supp
  have res : old ∈ CompressedPointSquare.residents L ∨ old ∈ L.dialogPool.take 776 := by
    simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  rcases res with res | mem
  · rw [CompressedPointSquare.resident_fixed L hw hn old res] at he
    subst he
    exact p1801_not_resident L hw hn res
  · rw [pool_block L hw 776 (by omega)] at mem
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)] at he
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have := pool_inj L hw hn _ 1801 (by omega) (by omega) he
    omega

theorem p1801_constAdd (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (k : Fp) :
    L.core.poolWire 1801 ∉ wires (pointDialogConstantAdd L r k) := by
  apply p1801_of_subset L hw hn _ 515 (by omega)
  intro q hq
  have h := List.mem_toFinset.mp (pointRecoveryConstantAdd_support L hw r k hq)
  apply List.mem_toFinset.mpr
  simp only [List.mem_cons, List.mem_append] at h
  simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl <;> tauto

theorem p1801_recovery (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (pointRecoveryStage L cx cy) := by
  apply p1801_of_subset L hw hn _ 515 (by omega)
  intro q hq
  have h := List.mem_toFinset.mp (pointRecoveryStage_support L hw cx cy hq)
  apply List.mem_toFinset.mpr
  simp only [recoveryStageSites, List.mem_append] at h
  simp only [CompressedPointSquare.residents, List.mem_append]
  tauto

theorem p1801_generic (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (pointCompressedDialogGeneric L cx cy) := by
  have a1 := p1801_constAdd L hw hn L.point.x (Or.inl rfl) (-cx)
  have a2 := p1801_constAdd L hw hn L.point.y (Or.inr rfl) (-cy)
  have a3 := p1801_constAdd L hw hn L.point.x (Or.inl rfl) (3*cx)
  have d := p1801_arith L hw hn false
  have m := p1801_arith L hw hn true
  have s := p1801_square L hw hn
  have r := p1801_recovery L hw hn cx cy
  simp only [pointCompressedDialogGeneric, wires_append, Finset.mem_union, not_or]
  exact ⟨⟨⟨⟨⟨⟨a1, a2⟩, d⟩, s⟩, a3⟩, m⟩, r⟩

omit hw hn in
/-- A site of the original inventory other than pool site 1801 is in `sitesQ`. -/
theorem sitesQ_of_sites (q : Wire) (hq : q ∈ CompressedPointDialog.sites L)
    (hne : q ≠ L.core.poolWire 1801) : q ∈ sitesQ L := by
  simp only [CompressedPointDialog.sites, sitesQ, CompressedPointSquare.sharedPool, sharedPoolQ,
    List.mem_append] at hq ⊢
  rcases hq with h | ((h | h) | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · have h' : q ∈ [L.core.poolWire 1800, L.core.poolWire 1801, L.core.poolWire 1802,
        L.core.poolWire 1803, L.core.poolWire 1804] := by
      simpa [wireBlock, List.range'_succ] using h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inr (Or.inl (Or.inr (by simp [h'])))
    · exact absurd h' hne
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))

end

end ECDSAAdd.Entrant

end

section
-- ===== EKFree =====
/-! Classification without the two enable flag wires.

The exception enable `E` and the doubling enable `K` are the control bit
masked by classical facts about `C`.  Instead of materialising them on the
`equalX` and `double` wires, the two comparisons they gated are driven by the
control wire and emitted only when the classical fact holds (the paired
comparisons already take these facts as classical bits).  The two wires then
stay idle, and with the arithmetic avoidance proof (`ArithAvoid.lean`) no block
touches them. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

/-- `t ^= b ∧ (point = P)`, emitted only when the classical enable holds. -/
def gatedShort (L : ControlledPointLayout) (en : Bool) (t : Wire) (P : Point) : Program :=
  if en then shortEqual L L.control t P else []

/-- The finite-addend program around an arbitrary generic-branch block `Gen`. -/
def finiteProgramEG (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  zeroFlag L.point.finite L.control L.infinitySelect ++
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  gatedShort L (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C) ++
  pointDialogGenericFlag L ++ Gen ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  pairEqual L L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C) ++
  gatedShort L (decide (cy≠-cy)) L.doubleSelect (C+C) ++
  zeroFlag L.point.finite L.control L.genericSelect

/-- Contract of a generic-branch block, as proved for the Skywalk block by
`CompressedPointDialog.boundary_generic`. -/
def GenericOK (L : ControlledPointLayout) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (Gen : Program) : Prop :=
  ∀ (R : Point) (b : Bool) (f : BasisState),
    (f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) →
    Triple (PointDialogBoundary L R b f) Gen
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f)

section Flags
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem gatedShort_flag (R P : Point) (en : Bool) (t : Wire) (ht : t ∈ L.inPlaceFlags)
    (b : Bool) (f : BasisState) :
    Triple (PointDialogBoundary L R b f) (gatedShort L en t P)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ ((b && en) && pointEqual R P)))) := by
  have sep := dialogFlag_separation L hn
  have hct : L.control ≠ t := fun h => (List.nodup_cons.mp sep).1 (h ▸ ht)
  cases en
  · intro s m v
    have hw' : writeBit f t (f t ^^ ((b && false) && pointEqual R P)) = f := by
      funext q; by_cases h : q = t
      · subst q; simp [writeBit]
      · simp [writeBit, h]
    rw [hw']
    exact ⟨rfl, v⟩
  · have hh := shortBoundary_equal L hw hn R P b f L.control t (Or.inl rfl) ht hct b (by simp)
    simpa only [gatedShort, if_true, Bool.and_true] using hh

theorem pairFlag_inputE (R C : Point) (cy : Fp) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pairEqual L L.doubleSelect L.genericSelect (decide (cy ≠ -cy)) true C (-C))
      (PointDialogBoundary L R b
        (dialogFlagState L O (D ^^ ((b && decide (cy ≠ -cy)) && pointEqual R C))
          (I ^^ (b && pointEqual R (-C))) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn R C b (dialogFlagState L O D I G E H K) L.doubleSelect L.genericSelect
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    (decide (cy ≠ -cy)) true (b && decide (cy ≠ -cy)) b rfl (by simp)
  simp only [hr.2.1, hr.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K
    (D ^^ ((b && decide (cy ≠ -cy)) && pointEqual R C))).2.1
  have u2 := (dialogFlagState_update L hn O (D ^^ ((b && decide (cy ≠ -cy)) && pointEqual R C)) I G E H K
    (I ^^ (b && pointEqual R (-C)))).2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

theorem pairFlag_outputE (S C : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (pairEqual L L.infinitySelect L.core.equalNegY true en C (-C))
      (PointDialogBoundary L S b
        (dialogFlagState L (O ^^ (b && pointEqual S C)) D I G E (H ^^ ((b && en) && pointEqual S (-C))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn S C b (dialogFlagState L O D I G E H K) L.infinitySelect L.core.equalNegY
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    true en b (b && en) (by simp) rfl
  simp only [hr.1, hr.2.2.2.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (O ^^ (b && pointEqual S C))).1
  have u2 := (dialogFlagState_update L hn (O ^^ (b && pointEqual S C)) D I G E H K
    (H ^^ ((b && en) && pointEqual S (-C)))).2.2.2.2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

theorem gatedFlag_H (R P : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (gatedShort L en L.core.equalNegY P)
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ ((b && en) && pointEqual R P)) K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := gatedShort_flag L hw hn R P en L.core.equalNegY (by simp [inPlaceFlags]) b
    (dialogFlagState L O D I G E H K)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

theorem gatedFlag_D (R P : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (gatedShort L en L.doubleSelect P)
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ ((b && en) && pointEqual R P)) I G E H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := gatedShort_flag L hw hn R P en L.doubleSelect (by simp [inPlaceFlags]) b
    (dialogFlagState L O D I G E H K)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

end Flags

section Spec
attribute [local irreducible] run wires shortEqual pairEqual gatedShort pointCompressedDialogGeneric
  pointDialogGeneric MappedCompressed.pointCompressedArithmetic CompressedPointSquare.computableProgram

private theorem equal_simpE [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgramEG_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgramEG L (.some hc) cy Gen)
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
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simpE,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simpE]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simpE]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simpE]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simpE]
  have h2 := zeroFlag_equalO L hn R b false false false false false false false
  rw [hO,Bool.false_xor] at h2
  have h3 := pairFlag_inputE L hw hn R C cy b O false false false false false false
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := gatedFlag_H L hw hn R (dialogExceptionPoint C) (exceptionBit C) b O D I false false false false
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false false H false
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G false H false
  have h7 := hGen R b (dialogFlagState L O D I G false H false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := dialogBoundary_corners L hw hn R C hC b (dialogFlagState L O D I G false H false)
    read.1 read.2.1 read.2.2.1 read.2.2.2.2.2.1
  have h9 := dialogFlag_generic L hw hn S b O D I G false H false
  have hgclear : (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H)=false := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hgclear] at h9
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [E,H,S,dialogExceptionEnabled,equal_simpE] using hf.2.2.2
  have h10 := pairFlag_outputE L hw hn S C (exceptionBit C) b O D I false false H false
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simpE] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := gatedFlag_D L hw hn S (C+C) (decide (cy≠-cy)) b false D I false false false false
  have hdo : ((b && decide (cy≠-cy)) && pointEqual S (C+C))=D := by
    change (K && pointEqual S (C+C)) = D
    rw [hK]; simpa only [equal_simpE] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := zeroFlag_equalI L hn S b false false I false false false false
  simp only [equal_simpE] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h := ((((((((h2.seq h3).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12
  simpa only [finiteProgramEG,List.append_assoc,dialogFlagState_zero] using h

/-- The Skywalk generic block satisfies the contract. -/
theorem skywalkGeneric_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (pointCompressedDialogGeneric L cx cy) :=
  fun R b f hg => boundary_generic L hw hn R b f hc hg

end Spec

end ECDSAAdd.Entrant

end

section
-- ===== FlagG =====
/-! The generic flag wire doubles as the infinity flag.

The generic flag is `b ∧ finite ⊕ D ⊕ I ⊕ H` (the four corner cases are
mutually exclusive and finite points are exactly the non-infinity points).
The generic-branch block keeps the finite flag of the point, so the same
formula clears the generic flag right after the block.  The infinity flag is
only needed by the corners and the output tests; it is computed into the then
idle generic wire just before the corners.  The separate infinity-select wire
is no longer used. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

/-- `generic ^= (b ∧ finite) ⊕ D ⊕ I ⊕ H`. -/
def genericFlag2 (L : ControlledPointLayout) : Program :=
  [.CCX L.control L.point.finite L.core.generic, .CX L.doubleSelect L.core.generic,
   .CX L.genericSelect L.core.generic, .CX L.core.equalNegY L.core.generic]

/-- The Skywalk corner writes with the infinity corner controlled by the generic wire. -/
def corners2 (L : ControlledPointLayout) (C : Point) : Program :=
  maskedPointConstant L.core.generic L.point C ++
  maskedPointConstant L.doubleSelect L.point C ++
  maskedPointConstant L.doubleSelect L.point (C+C) ++
  maskedPointConstant L.genericSelect L.point (-C) ++
  maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C) ++
  maskedPointConstant L.core.equalNegY L.point (-C)

def finiteProgramFG (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  gatedShort L (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C) ++
  genericFlag2 L ++ Gen ++ genericFlag2 L ++
  zeroFlag L.point.finite L.control L.core.generic ++
  corners2 L C ++
  pairEqual L L.core.generic L.core.equalNegY true (exceptionBit C) C (-C) ++
  gatedShort L (decide (cy≠-cy)) L.doubleSelect (C+C) ++
  chainErase L.control L.point.finite L.genericSelect

section Lemmas
/-- Clearing a flag known to equal `control ∧ ¬finite` by measurement. -/
theorem chainErase_equalI (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (R : Point) (b O D I G E H K : Bool)
    (hI : I = (b && !pointFinite R)) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (chainErase L.control L.point.finite L.genericSelect)
      (PointDialogBoundary L R b (dialogFlagState L O D false G E H K)) := by
  have sep0 := dialogFlag_separation (L:=L) hn
  have hr := dialogFlagState_read L hn O D I G E H K
  have ht : L.genericSelect ∈ L.inPlaceFlags := by simp [inPlaceFlags]
  have hct : L.control ≠ L.genericSelect := fun h => (List.nodup_cons.mp sep0).1 (h ▸ ht)
  have hnd := L.dialogPointZero_nodup hn L.control L.genericSelect hct (Or.inl rfl) ht
  simp only [PointAddLayout.pointWires,List.cons_append,List.nodup_cons,List.mem_cons,
    List.mem_append,not_or] at hnd
  have hcf : L.control ≠ L.point.finite := hnd.1.2.1
  have hft : L.point.finite ≠ L.genericSelect := fun h => hnd.2.1.1 h.symm
  intro s m v
  have hg : s.basis L.genericSelect = I := (v.flags _ ht).trans hr.2.2.1
  have hb : s.basis L.control = b := v.control
  have hfn : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have hq : s.basis L.genericSelect = (s.basis L.control && !s.basis L.point.finite) := by
    rw [hg,hb,hfn,hI]
  have hh := chainErase_run L.control L.point.finite L.genericSelect hcf hft hct s m hq
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hqflag
    rw [hh]
    by_cases hqt : q = L.genericSelect
    · subst q
      simp [writeBit, (dialogFlagState_read L hn O D false G E H K).2.2.1]
    · simp only [writeBit,Function.update_apply,hqt,if_false]
      rw [v.flags q hqflag]
      have hu := (dialogFlagState_update L hn O D I G E H K false).2.2.1 q hqflag
      simpa only [writeBit,Function.update_apply,hqt,if_false] using hu
  · intro q hqflag
    rw [hh]
    have hqt : q ≠ L.genericSelect := fun h => hqflag (h ▸ ht)
    simp [writeBit,hqt]

variable (L : ControlledPointLayout)

theorem flags_distinct (hn : L.wires.Nodup) :
    L.control ≠ L.core.generic ∧ L.point.finite ≠ L.core.generic ∧ L.doubleSelect ≠ L.core.generic ∧
    L.genericSelect ≠ L.core.generic ∧ L.core.equalNegY ≠ L.core.generic ∧ L.control ≠ L.point.finite := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hfin : L.point.finite ∉ L.control :: L.inPlaceFlags := by
    have hh := List.nodup_iff_count_le_one.mp (L.dialogUsed_nodup hn) L.point.finite
    have hp : 1 ≤ (PointAddLayout.pointWires L.point).count L.point.finite :=
      List.count_pos_iff.mpr (by simp [PointAddLayout.pointWires])
    simp only [dialogUsedWires, List.count_append] at hh
    have hc : (L.control :: L.inPlaceFlags).count L.point.finite = 0 := by
      show ([L.control] ++ L.inPlaceFlags).count _ = 0
      rw [List.count_append]; omega
    exact List.count_eq_zero.mp hc
  simp only [inPlaceFlags, List.mem_cons, not_or] at hfin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto

theorem genericFlag2_run (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    run (genericFlag2 L) m s = ⟨s.phase, writeBit s.basis L.core.generic
      ((((s.basis L.core.generic ^^ (s.basis L.control && s.basis L.point.finite)) ^^
        s.basis L.doubleSelect) ^^ s.basis L.genericSelect) ^^ s.basis L.core.equalNegY)⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := flags_distinct L hn
  simp only [genericFlag2, run]
  congr 1
  funext q
  by_cases hq : q = L.core.generic
  · subst hq; simp [writeBit, h1, h2, h3, h4, h5]
  · simp [writeBit, hq]

variable (hw : L.Widths) (hn : L.wires.Nodup)
include hn

theorem genericFlag2_flag (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K)) (genericFlag2 L)
      (PointDialogBoundary L R b (dialogFlagState L O D I
        ((((G ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) E H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  intro s m v
  have hh := genericFlag2_run L hn s m
  have hfin : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have rd (q : Wire) (hq : q ∈ L.inPlaceFlags) : s.basis q = dialogFlagState L O D I G E H K q := v.flags q hq
  have eG := rd L.core.generic (by simp [inPlaceFlags])
  have eD := rd L.doubleSelect (by simp [inPlaceFlags])
  have eI := rd L.genericSelect (by simp [inPlaceFlags])
  have eH := rd L.core.equalNegY (by simp [inPlaceFlags])
  rw [hr.2.2.2.1] at eG; rw [hr.2.1] at eD; rw [hr.2.2.1] at eI; rw [hr.2.2.2.2.2.1] at eH
  rw [eG, eD, eI, eH, hfin, v.control] at hh
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    have u := (dialogFlagState_update L hn O D I G E H K
      ((((G ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H)).2.2.2.1 q hq
    rw [← u]
    by_cases he : q = L.core.generic
    · subst he; simp [writeBit]
    · simp [writeBit, he, rd q hq]
  · intro q hq
    rw [hh]
    have hqt : q ≠ L.core.generic := fun he => hq (he ▸ by simp [inPlaceFlags])
    simp [writeBit, hqt]

theorem zeroFlag_flagG (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.core.generic)
      (PointDialogBoundary L R b (dialogFlagState L O D I (G ^^ (b && pointEqual R 0)) E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.core.generic
    (Or.inl rfl) (by simp [inPlaceFlags]) (by tauto) b (by simp)
  simp only [hr.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.1)

include hw

theorem pairFlag_outputG (S C : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (pairEqual L L.core.generic L.core.equalNegY true en C (-C))
      (PointDialogBoundary L S b
        (dialogFlagState L O D I (G ^^ (b && pointEqual S C)) E (H ^^ ((b && en) && pointEqual S (-C))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn S C b (dialogFlagState L O D I G E H K) L.core.generic L.core.equalNegY
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    true en b (b && en) (by simp) rfl
  simp only [hr.2.2.2.1, hr.2.2.2.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (G ^^ (b && pointEqual S C))).2.2.2.1
  have u2 := (dialogFlagState_update L hn O D I (G ^^ (b && pointEqual S C)) E H K
    (H ^^ ((b && en) && pointEqual S (-C)))).2.2.2.2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

theorem corners2_effect (C : Point) (s : State) (m : List Bool) :
    PointEffect L.point
      ((((((s.basis L.core.generic && pointFinite C) ^^ (s.basis L.doubleSelect && pointFinite C)) ^^
        (s.basis L.doubleSelect && pointFinite (C+C))) ^^ (s.basis L.genericSelect && pointFinite (-C))) ^^
        (s.basis L.core.equalNegY && pointFinite (dialogExceptionPoint C))) ^^
        (s.basis L.core.equalNegY && pointFinite (-C)))
      ((((((if s.basis L.core.generic then pointX C else 0) ^^^ (if s.basis L.doubleSelect then pointX C else 0)) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointX (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (-C) else 0))
      ((((((if s.basis L.core.generic then pointY C else 0) ^^^ (if s.basis L.doubleSelect then pointY C else 0)) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointY (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (-C) else 0))
      s (run (corners2 L C) m s) := by
  have hr : (PointAddLayout.pointWires L.point).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hh := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    simp only [List.count_append] at hh
    omega
  have away (q : Wire) (hq : q∈L.inPlaceFlags) : q∉PointAddLayout.pointWires L.point := by
    intro hp
    have hh := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hp
    simp only [List.count_append] at hh
    omega
  have ho := away L.core.generic (by simp [inPlaceFlags])
  have hd := away L.doubleSelect (by simp [inPlaceFlags])
  have hi := away L.genericSelect (by simp [inPlaceFlags])
  have hh' := away L.core.equalNegY (by simp [inPlaceFlags])
  let u := run (maskedPointConstant L.core.generic L.point C) m s
  have e0 := maskedPointConstant_correct _ _ C hr ho hw.inputX hw.inputY s m
  have ud : u.basis L.doubleSelect=s.basis L.doubleSelect := e0.outside _ hd
  let v := run (maskedPointConstant L.doubleSelect L.point C) m u
  have e1 := maskedPointConstant_correct _ _ C hr hd hw.inputX hw.inputY u m
  have vd : v.basis L.doubleSelect=s.basis L.doubleSelect := (e0.trans e1).outside _ hd
  let w := run (maskedPointConstant L.doubleSelect L.point (C+C)) m v
  have e2 := maskedPointConstant_correct _ _ (C+C) hr hd hw.inputX hw.inputY v m
  have wi : w.basis L.genericSelect=s.basis L.genericSelect := ((e0.trans e1).trans e2).outside _ hi
  let x := run (maskedPointConstant L.genericSelect L.point (-C)) m w
  have e3 := maskedPointConstant_correct _ _ (-C) hr hi hw.inputX hw.inputY w m
  have xh : x.basis L.core.equalNegY=s.basis L.core.equalNegY := (((e0.trans e1).trans e2).trans e3).outside _ hh'
  let y := run (maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C)) m x
  have e4 := maskedPointConstant_correct _ _ (dialogExceptionPoint C) hr hh' hw.inputX hw.inputY x m
  have yh : y.basis L.core.equalNegY=s.basis L.core.equalNegY :=
    ((((e0.trans e1).trans e2).trans e3).trans e4).outside _ hh'
  have e5 := maskedPointConstant_correct _ _ (-C) hr hh' hw.inputX hw.inputY y m
  have he := ((((e0.trans e1).trans e2).trans e3).trans e4).trans e5
  rw [corners2,run_append,run_take,run_append,run_take,run_append,run_take,run_append,run_take,
    run_append,run_take]
  simp only [measurementCount_append,(maskedPointConstant_counts _ _ _).2,Nat.zero_add,List.drop_zero]
  simpa only [ud,vd,wi,xh,yh] using he

theorem corners2_boundary [DecidableEq Point] (R C : Point) (hc : C≠0) (b : Bool) (f : BasisState)
    (ho : f L.core.generic=dialogInfinity b R)
    (hd : f L.doubleSelect=dialogDouble b R C)
    (hi : f L.genericSelect=dialogInversePoint b R C)
    (hh : f L.core.equalNegY=dialogException b R C) :
    Triple (PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f)
      (corners2 L C) (PointDialogBoundary L (if b then R+C else R) b f) := by
  intro s m v
  have he := corners2_effect L hw hn C s m
  have vo := (v.flags _ (by simp [inPlaceFlags])).trans ho
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hd
  have vi := (v.flags _ (by simp [inPlaceFlags])).trans hi
  have vh := (v.flags _ (by simp [inPlaceFlags])).trans hh
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨he.phase,v.withPoint hn ((point_holds _ _ _).mpr ⟨?_,?_,?_⟩) he.outside⟩
  · rw [he.finite,hp.1,vo,vd,vi,vh]
    have h := dialogCorners_bool b R C hc pointFinite (by rfl)
    have bool_if (a b : Bool) : (if a then b else false)=(a && b) := by cases a <;> rfl
    simpa only [bool_if,Bool.xor_assoc] using h
  · rw [he.x,hp.2.1,vo,vd,vi,vh]
    simpa only [Nat.xor_assoc] using dialogCorners_nat b R C hc pointX (by rfl)
  · rw [he.y,hp.2.2,vo,vd,vi,vh]
    simpa only [Nat.xor_assoc] using dialogCorners_nat b R C hc pointY (by rfl)

end Lemmas

end ECDSAAdd.Entrant

namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

section SpecFG
attribute [local irreducible] run wires shortEqual pairEqual gatedShort genericFlag2 corners2

private theorem equal_simpG [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgramFG_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgramFG L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  let R1 := if G then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simpG,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simpG]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simpG]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simpG]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simpG]
  have hfin (P : Point) : (b && pointFinite P) = (b ^^ (b && pointEqual P 0)) := by
    rw [pointEqual_zero]; cases b <;> cases pointFinite P <;> rfl
  have hGv : ((((false ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) = G := by
    rw [hfin, hO]; simp only [G, dialogOrdinary, O, D, I, H, Bool.false_xor]
  have hgen := (dialogOrdinary_true b R C hC)
  have hR1fin : (b && pointFinite R1) = (b && pointFinite R) := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have f1 : pointFinite (R+C) = true := by
        have t := pointEqual_zero (R+C)
        have e2 : pointEqual (R+C) 0 = false := by
          cases h : pointEqual (R+C) 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) hs
        rw [e2] at t
        cases h : pointFinite (R+C)
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      have f2 : pointFinite R = true := by
        have t := pointEqual_zero R
        have e2 : pointEqual R 0 = false := by
          cases h : pointEqual R 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) h0
        rw [e2] at t
        cases h : pointFinite R
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      simp only [R1, hg, if_true, f1, f2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg]
  have hR1O : (b && pointEqual R1 0) = O := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have e1 : pointEqual (R+C) 0 = false := by
        cases h : pointEqual (R+C) 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) hs
      have e2 : pointEqual R 0 = false := by
        cases h : pointEqual R 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) h0
      rw [← hO]; simp only [R1, hg, if_true, e1, e2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg, hO]
  have h3 := pairFlag_inputE L hw hn R C cy b false false false false false false false
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := gatedFlag_H L hw hn R (dialogExceptionPoint C) (exceptionBit C) b false D I false false false false
  rw [hH,Bool.false_xor] at h5
  have h6 := genericFlag2_flag L hn R b false D I false false H false
  rw [hGv] at h6
  have read := dialogFlagState_read L hn false D I G false H false
  have h7 := hGen R b (dialogFlagState L false D I G false H false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h9 := genericFlag2_flag L hn R1 b false D I G false H false
  have hclr : ((((G ^^ (b && pointFinite R1)) ^^ D) ^^ I) ^^ H) = false := by
    rw [hR1fin]
    have hG' := hGv
    simp only [Bool.false_xor] at hG'
    rw [← hG']
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hclr] at h9
  have h10a := zeroFlag_flagG L hn R1 b false D I false false H false
  rw [hR1O, Bool.false_xor] at h10a
  have readO := dialogFlagState_read L hn false D I O false H false
  have h8 := corners2_boundary L hw hn R C hC b (dialogFlagState L false D I O false H false)
    readO.2.2.2.1 readO.2.1 readO.2.2.1 readO.2.2.2.2.2.1
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [H,S,dialogExceptionEnabled,equal_simpG] using hf.2.2.2
  have h10 := pairFlag_outputG L hw hn S C (exceptionBit C) b false D I O false H false
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simpG] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := gatedFlag_D L hw hn S (C+C) (decide (cy≠-cy)) b false D I false false false false
  have hdo : ((b && decide (cy≠-cy)) && pointEqual S (C+C))=D := by
    change (K && pointEqual S (C+C)) = D
    rw [hK]; simpa only [equal_simpG] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have hzero : decide (S=0) = !pointFinite S := by
    rw [← equal_simpG]
    exact pointEqual_zero S
  have h12 := chainErase_equalI L hn S b false false (dialogInversePoint b R C)
    false false false false (by rw [← hf.2.2.1, hzero])
  have h := ((((((((h3.seq h5).seq h6).seq h7).seq h9).seq h10a).seq h8).seq h10).seq h11).seq h12
  simpa only [finiteProgramFG,List.append_assoc,dialogFlagState_zero] using h

end SpecFG

end ECDSAAdd.Entrant

end

section
-- ===== OBSigma =====
/-! One-bank field, part 1: late signs in narrowed carry slots.

Tick `k` of the integer walk writes its sign to label `1028+k` and uses the
carry labels `[1540, 1540+min(257,513-k))`.  For `k ≥ 257` the carry label
`2053-k` is never a carry again in the forward walk, so from tick `k` on the
sign of tick `k` is stored there instead.  `obSig i` is the placement in force
for tick `i`: it exchanges `base (1028+k)` and `base (2053-k)` for every
`257 ≤ k ≤ i`.  The exchanges are disjoint, so `obSig i` is an involution and
the identity for `i ≤ 256`.  Placements change only at tick boundaries, where
both exchanged labels are zero, so no gate is emitted for the change. -/
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed

/-- Wires `base 1285 .. base (1028+i)` and `base (2053-i) .. base 1796`
exchange as `q ↦ 3113 - q` (`base a + base b = 3113` when `a + b = 3081`). -/
def obSig (i : Nat) (q : Wire) : Wire :=
  if (1301 ≤ q ∧ q ≤ 1044+i) ∨ (2069 ≤ q+i ∧ q ≤ 1812) then 3113-q else q

/-- Forward integer ticks `i .. i+n-1`, tick `k` placed by `obSig k`. -/
def obForward (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (obSig i) (compactSkywalkTick base i ++ compressedPackAfter base i) ++
      obForward (i+1) n

/-- Reverse integer ticks, untick `k` placed by `obSig k`. -/
def obReverse (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => obReverse (i+1) n ++
      renameProgram (obSig i) (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i)

/-- Physical labels that the one-bank arithmetic never touches. -/
def obRemoved (q : Wire) : Prop := 1301 ≤ q ∧ q < 1556

end ECDSAAdd.Entrant

end

section
-- ===== OBInteger =====
/-! One-bank field, part 1: the integer passes with late signs in narrowed
carry slots.

`obForward` and `obReverse` emit the certified compact integer ticks, packs and
decodes, each renamed by the placement `obSig k` in force for its tick.  Between
ticks `k-1` and `k` the placement changes by the exchange of `base (1028+k)`
(the sign site of tick `k`, still clean) and `base (2053-k)` (a carry site,
clean between ticks).  Both are zero in every compressed stage state, so the
change needs no gate (`pullState_zero_swap`).  The renamed passes are therefore
run-equal to the certified ones up to the final placement `obSig 511`, and the
reverse pass returns to the identity placement. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1
attribute [local irreducible] compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

/-! ## The placements -/

/-- `obSig` on natural numbers (`Wire` is not unfolded by `omega`). -/
def obNat (i q : Nat) : Nat :=
  if (1301 ≤ q ∧ q ≤ 1044+i) ∨ (2069 ≤ q+i ∧ q ≤ 1812) then 3113-q else q

theorem obSig_nat (i : Nat) (q : Wire) : obSig i q = obNat i q := rfl

theorem obSig_invol (i : Nat) (hi : i ≤ 511) (q : Wire) : obSig i (obSig i q) = q := by
  show obNat i (obNat i q) = (q : Nat)
  unfold obNat
  split_ifs <;> omega

theorem obSig_injective (i : Nat) (hi : i ≤ 511) : Function.Injective (obSig i) := by
  intro a b h
  rw [← obSig_invol i hi a, ← obSig_invol i hi b, h]

theorem obSig_zero (q : Wire) : obSig 0 q = q := by
  show obNat 0 q = (q : Nat)
  unfold obNat
  split_ifs <;> omega

theorem obSig_base (k l : Nat) (hk : k ≤ 511) : obSig k (base l) =
    base (if (1285 ≤ l ∧ l ≤ 1028+k) ∨ (2053 ≤ l+k ∧ l ≤ 1796) then 3081-l else l) := by
  show obNat k (l+16) =
    ((if (1285 ≤ l ∧ l ≤ 1028+k) ∨ (2053 ≤ l+k ∧ l ≤ 1796) then 3081-l else l) + 16 : Nat)
  unfold obNat
  split_ifs <;> omega

/-- Consecutive placements differ only on the two exchanged sites of tick `i`. -/
theorem obNat_step (i : Nat) (hi : i ≤ 511) (q : Nat) :
    obNat (i-1) q = obNat i q ∨
    (257 ≤ i ∧ (obNat (i-1) q = 1044+i ∨ obNat (i-1) q = 2069-i) ∧
      (obNat i q = 1044+i ∨ obNat i q = 2069-i)) := by
  unfold obNat
  split_ifs <;> omega

theorem obPull_invol (i : Nat) (hi : i ≤ 511) (s : State) :
    pullState (obSig i) (pullState (obSig i) s) = s := by
  apply State.extensionality
  · rfl
  · funext q
    show s.basis (obSig i (obSig i q)) = s.basis q
    rw [obSig_invol i hi]

/-- A block renamed by `obSig i` acts on the placed state as the block on the
logical state. -/
theorem obRun_rename (i : Nat) (hi : i ≤ 511) (P : Program) (m : List Bool) (t : State) :
    run (renameProgram (obSig i) P) m (pullState (obSig i) t) =
      pullState (obSig i) (run P m t) := by
  have h := run_rename (obSig i) (obSig_injective i hi) P m (pullState (obSig i) t)
  rw [obPull_invol i hi t] at h
  rw [← h, obPull_invol i hi]

/-- The placement change before tick `i` is gate-free when its two sites are clean. -/
theorem obPull_step (i : Nat) (hi : i ≤ 511) (t : State)
    (h1 : t.basis (base (1028+i)) = false) (h2 : 257 ≤ i → t.basis (base (2053-i)) = false) :
    pullState (obSig (i-1)) t = pullState (obSig i) t := by
  apply State.extensionality
  · rfl
  · funext q
    show t.basis (obSig (i-1) q) = t.basis (obSig i q)
    have b1 : base (1028+i) = 1044+i := by show 1028+i+16 = 1044+i; omega
    have b2 : base (2053-i) = 2069-i := by show 2053-i+16 = 2069-i; omega
    rw [b1] at h1
    rw [b2] at h2
    rw [obSig_nat, obSig_nat]
    rcases obNat_step i hi q with e | ⟨big, e1, e2⟩
    · rw [e]
    · have z2 := h2 big
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rw [e1, e2] <;> simp only [h1, z2]

/-! ## Zero facts at tick boundaries -/

theorem obEncodePrefix_mem (n : Nat) (hn : n ≤ 512) (q : Wire)
    (hq : q ∈ wires (compressedEncodePrefix base n)) :
    ∃ j, q = base j ∧ (j+2 ≤ n ∨ (1028 ≤ j ∧ j+2 ≤ 1028+n)) := by
  induction n with
  | zero => simp [compressedEncodePrefix, wires] at hq
  | succ n ih =>
    rw [compressedEncodePrefix, wires_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · obtain ⟨j, rfl, hj⟩ := ih (by omega) hq
      exact ⟨j, rfl, by omega⟩
    · cases hd : compressedPackDue n
      · simp [compressedPackAfter, hd, wires] at hq
      · have h3 := compressedPackDue_true n hd
        rw [compressedPackAfter, if_pos hd] at hq
        obtain ⟨u, rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above (n-3)
          (by omega) _ (Or.inl rfl) q hq
        refine ⟨_, rfl, ?_⟩
        have hu := u.isLt
        unfold compressedHistoryId
        split <;> omega

/-- The encode prefix before tick `i` never touches labels at or above `1027+i`. -/
theorem obPrefix_keep (i : Nat) (hi : i ≤ 512) (raw : State) (l : Nat) (hl : 1027+i ≤ l) :
    (run (compressedEncodePrefix base i) [] raw).basis (base l) = raw.basis (base l) := by
  apply run_preserves_outside
  intro hm
  obtain ⟨j, hj, hr⟩ := obEncodePrefix_mem i hi _ hm
  have := base_injective hj
  omega

theorem obStage_zero (x i : Nat) (hi : i < 512) (b : BasisState)
    (h : CompressedCompactStage base x p i b) :
    b (base (1028+i)) = false ∧ (257 ≤ i → b (base (2053-i)) = false) := by
  obtain ⟨raw, hraw, rfl⟩ := h
  have virt : ∀ l, 1028 ≤ l → compactSkywalkStageVirtual base i raw.basis (base l) =
      raw.basis (base l) := by
    intro l hl
    have ex := compactSkywalkStage_expanded base i (by omega)
    apply compactSkywalkStage_virtual_outside
    · intro hm
      have hm' : base l ∈ (compactSkywalkSignPoolA base i).expanded :=
        List.mem_append_right _ hm
      rw [ex.1] at hm'
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
      have := base_injective he
      simp only [List.mem_range'_1] at hj
      omega
    · intro hm
      have hm' : base l ∈ (compactSkywalkSignPoolB base i).expanded :=
        List.mem_append_right _ hm
      rw [ex.2] at hm'
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
      have := base_injective he
      simp only [List.mem_range'_1] at hj
      omega
  have stage := hraw.1
  have fut := (stage.2.2.2.2.1 i (Nat.le_refl i) hi).2
  have carry := (regValue_zero _ _).mp stage.2.2.2.2.2.1
  constructor
  · rw [obPrefix_keep i (by omega) raw (1028+i) (by omega), ← virt (1028+i) (by omega)]
    exact fut
  · intro big
    rw [obPrefix_keep i (by omega) raw (2053-i) (by omega), ← virt (2053-i) (by omega)]
    apply carry
    exact List.mem_map.mpr ⟨2053-i, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩

theorem obStage_one (x : Nat) (s : State)
    (hs : CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    CompressedCompactStage base x p 1 s.basis := by
  refine ⟨s, hs, ?_⟩
  have e : compressedEncodePrefix base 1 = [] := by
    show compressedEncodePrefix base (0+1) = []
    rw [compressedEncodePrefix, compressedEncodePrefix]
    simp [compressedPackAfter, compressedPackDue]
  rw [e]
  rfl

theorem obPrime_facts (x : Nat) (hx0 : 0 < x) (hx : x < p) :
    0 < p ∧ p%2 = 1 ∧ p < 2^256 ∧ x.Coprime p := by
  refine ⟨by norm_num [p], by norm_num [p], by norm_num [p], ?_⟩
  apply Nat.Coprime.symm
  apply p_prime.coprime_iff_not_dvd.mpr
  intro hd
  exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)

/-! ## Forward pass -/

theorem obForward_gen (x : Nat) (hx0 : 0 < x) (hx : x < p) (n : Nat) :
    ∀ i, 1 ≤ i → i+n ≤ 512 → ∀ (t : State) (m : List Bool),
    CompressedCompactStage base x p i t.basis →
    run (obForward i n) m (pullState (obSig (i-1)) t) =
      pullState (obSig (i+n-1)) (run (compressedCompactForward base i n) m t) := by
  obtain ⟨hp0, hpo, hp, cop⟩ := obPrime_facts x hx0 hx
  induction n with
  | zero =>
    intro i _ _ t m _
    simp only [obForward, compressedCompactForward, run, Nat.add_zero]
  | succ n ih =>
    intro i h1 hb t m ht
    have hi : i ≤ 511 := by omega
    have z := obStage_zero x i (by omega) t.basis ht
    rw [obPull_step i hi t z.1 z.2]
    have e1 : obForward i (n+1) = renameProgram (obSig i)
        (compactSkywalkTick base i ++ compressedPackAfter base i) ++ obForward (i+1) n := by
      rw [obForward]
    have e2 : compressedCompactForward base i (n+1) =
        (compactSkywalkTick base i ++ compressedPackAfter base i) ++
          compressedCompactForward base (i+1) n := by
      rw [compressedCompactForward]
    have cnt := (renameProgram_counts (obSig i)
      (compactSkywalkTick base i ++ compressedPackAfter base i)).2
    rw [e1, e2, run_append, run_append, cnt, obRun_rename i hi]
    have ht' := (compressedCompactStage_step base base_pool_nodup base_above x p i hp0 hx0 hpo hp hx
      cop (by omega) t (m.take (measurementCount
        (compactSkywalkTick base i ++ compressedPackAfter base i))) ht).2
    have step := ih (i+1) (by omega) (by omega) _ (m.drop (measurementCount
        (compactSkywalkTick base i ++ compressedPackAfter base i))) ht'
    rw [show i+1-1 = i by omega] at step
    rw [step, show i+1+n-1 = i+(n+1)-1 by omega]

theorem obForward_run (x : Nat) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hs : CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (obForward 1 511) m s = pullState (obSig 511) (run (compressedCompactForward base 1 511) m s) := by
  have h := obForward_gen x hx0 hx 511 1 (Nat.le_refl 1) (by omega) s m (obStage_one x s hs)
  have e : pullState (obSig (1-1)) s = s := by
    apply State.extensionality
    · rfl
    · funext q
      show s.basis (obSig 0 q) = s.basis q
      rw [obSig_zero]
  rw [e, show 1+511-1 = 511 from rfl] at h
  exact h

/-! ## Counts -/

theorem obCounts_gen (i n : Nat) :
    toffoliCount (obForward i n) = toffoliCount (compressedCompactForward base i n) ∧
    measurementCount (obForward i n) = measurementCount (compressedCompactForward base i n) ∧
    Challenge.gateSlots (obForward i n) = Challenge.gateSlots (compressedCompactForward base i n) ∧
    toffoliCount (obReverse i n) = toffoliCount (compressedCompactReverse base i n) ∧
    measurementCount (obReverse i n) = measurementCount (compressedCompactReverse base i n) ∧
    Challenge.gateSlots (obReverse i n) = Challenge.gateSlots (compressedCompactReverse base i n) := by
  induction n generalizing i with
  | zero => simp [obForward, obReverse, compressedCompactForward, compressedCompactReverse]
  | succ n ih =>
    have r := ih (i+1)
    have f := renameProgram_counts (obSig i) (compactSkywalkTick base i ++ compressedPackAfter base i)
    have b := renameProgram_counts (obSig i)
      (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i)
    have fs := Baselines.rename_gateSlots (obSig i)
      (compactSkywalkTick base i ++ compressedPackAfter base i)
    have bs := Baselines.rename_gateSlots (obSig i)
      (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i)
    rw [obForward, obReverse, compressedCompactForward, compressedCompactReverse]
    simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append] at f b fs bs ⊢
    omega

theorem obForward_counts :
    toffoliCount (obForward 1 511) = toffoliCount (compressedCompactForward base 1 511) ∧
    measurementCount (obForward 1 511) = measurementCount (compressedCompactForward base 1 511) ∧
    Challenge.gateSlots (obForward 1 511) = Challenge.gateSlots (compressedCompactForward base 1 511) :=
  let h := obCounts_gen 1 511
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem obReverse_counts :
    toffoliCount (obReverse 1 511) = toffoliCount (compressedCompactReverse base 1 511) ∧
    measurementCount (obReverse 1 511) = measurementCount (compressedCompactReverse base 1 511) ∧
    Challenge.gateSlots (obReverse 1 511) = Challenge.gateSlots (compressedCompactReverse base 1 511) :=
  let h := obCounts_gen 1 511
  ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ## Reverse pass -/

/-- One compressed tick followed by its decode and inverse tick is the identity
on every compressed stage state. -/
theorem obOneStep_roundtrip (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (t : State) (ht : CompressedCompactStage base x p i t.basis) (m1 m2 : List Bool) :
    run (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i) m2
      (run (compactSkywalkTick base i ++ compressedPackAfter base i) m1 t) = t := by
  obtain ⟨hp0, hpo, hp, cop⟩ := obPrime_facts x hx0 hx
  obtain ⟨raw, hraw, hbits⟩ := ht
  have hnxt := compactSkywalkStageStep base base_pool_nodup x p i hp0 hx0 hpo hp hx cop hi
    raw [] hraw
  have hd := compressedPrefix_disjoint_compactTick base base_pool_nodup base_above i i
    (Nat.le_refl i) hi
  have hcomm := run_disjoint_commute (compressedEncodePrefix base i) (compactSkywalkTick base i)
    hd [] [] raw
  have hb0 := run_basis_records (compactSkywalkTick base i) t
    (run (compressedEncodePrefix base i) [] raw)
    (m1.take (measurementCount (compactSkywalkTick base i))) [] hbits
  have hb : (run (compactSkywalkTick base i) (m1.take (measurementCount (compactSkywalkTick base i))) t).basis =
      (run (compressedEncodePrefix base i) [] (run (compactSkywalkTick base i) [] raw)).basis :=
    hb0.trans (congrArg State.basis hcomm.symm)
  generalize hact : run (compactSkywalkTick base i)
    (m1.take (measurementCount (compactSkywalkTick base i))) t = actual at hb
  have dp : run (compressedDecodeBefore base i) []
      (run (compressedPackAfter base i) (m1.drop (measurementCount (compactSkywalkTick base i)))
        actual) = actual := by
    cases he : compressedPackDue i
    · simp only [compressedPackAfter, compressedDecodeBefore, he, Bool.false_eq_true, if_false, run]
    · have h3 := compressedPackDue_true i he
      have same (j : Fin 6) : actual.basis (compressedHistoryMap base (i-3) j) =
          (run (compactSkywalkTick base i) [] raw).basis (compressedHistoryMap base (i-3) j) := by
        rw [hb]
        exact compressedPrefix_raw_next base base_pool_nodup base_above i hi he _ [] j
      have legal := compressedCompactHistory_legal base base_pool_nodup x p (i+1) (i-3) hp0 hpo
        (by omega) (by omega) _ hnxt.2
      have actualLegal :
          (actual.basis (compressedHistoryMap base (i-3) 0) &&
            actual.basis (compressedHistoryMap base (i-3) 1)) = false ∧
          (actual.basis (compressedHistoryMap base (i-3) 2) &&
            actual.basis (compressedHistoryMap base (i-3) 3)) = false ∧
          (actual.basis (compressedHistoryMap base (i-3) 4) &&
            actual.basis (compressedHistoryMap base (i-3) 5)) = false := by
        rw [same 0, same 1, same 2, same 3, same 4, same 5]
        exact legal
      have dc := TranscriptCodec3.decode_encode (compressedHistoryMap base (i-3))
        (compressedHistoryMap_injective base base_pool_nodup (i-3) (by omega))
        (compressedHistoryMap_above base (i-3) (by omega) base_above) actual
        (m1.drop (measurementCount (compactSkywalkTick base i))) [] actualLegal
      simpa only [compressedPackAfter, compressedDecodeBefore, he, if_true,
        compressedHistoryEncode, compressedHistoryDecode] using dc
  have loc := compactSkywalkStage_local_input base base_pool_nodup x p i hp0 hx0 hpo hp hx cop hi
    raw hraw
  have width := compactSkywalkTick_width_bounds i hi
  have hh : t.basis (compactSkywalkTickLayout base i).history = false := by
    change t.basis (base (1028+i)) = false
    rw [hbits, obPrefix_keep i (by omega) raw (1028+i) (by omega)]
    exact loc.2.2.2.2.1
  have hc : regValue (compactSkywalkTickLayout base i).carry t.basis = 0 := by
    have e := regValue_congr (compactSkywalkTickLayout base i).carry t.basis raw.basis (by
      intro q hq
      change q ∈ wireBlock base 1540 (compactSkywalkTickPreWidth i - 1) at hq
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hl
      rw [hbits, obPrefix_keep i (by omega) raw l (by omega)])
    rw [e]
    exact loc.2.2.2.2.2
  have rt := compactSkywalkReverseTick_roundtrip base i hi base_pool_nodup t
    (m1.take (measurementCount (compactSkywalkTick base i))) m2 hh hc
  rw [hact] at rt
  have dz := (compressedPackAfter_counts base i).2.2.2
  rw [run_append, run_append, dz, List.take_zero, List.drop_zero, hact, dp, rt]

theorem obPool_agree (P : Program) (hP : wires P ⊆ (skywalkPoolWires base).toFinset)
    (m : List Bool) (s t : State)
    (h : ∀ q ∈ skywalkPoolWires base, s.basis q = t.basis q) :
    ∀ q ∈ skywalkPoolWires base, (run P m s).basis q = (run P m t).basis q := by
  have e : (run P m s).basis = (run P m (⟨t.phase, s.basis⟩ : State)).basis :=
    run_basis_records P s _ m m rfl
  have a := pool_run_agrees P _ hP m ⟨t.phase, s.basis⟩ t rfl
    (fun q hq => h q (List.mem_toFinset.mp hq))
  intro q hq
  rw [e]
  exact a.2 q (List.mem_toFinset.mpr hq)

theorem obUntick_pool (i : Nat) (hi : i < 512) :
    wires (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i) ⊆
      (skywalkPoolWires base).toFinset := by
  have h := compressedCompactReverse_support base base_pool_nodup base_above i (0+1) (by omega)
  rw [compressedCompactReverse, compressedCompactReverse, List.nil_append] at h
  exact h

theorem obBase_pool (l : Nat) (hl : l < 1798) : base l ∈ skywalkPoolWires base :=
  List.mem_map.mpr ⟨l, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩

theorem obReverse_gen (x : Nat) (hx0 : 0 < x) (hx : x < p) (n : Nat) :
    ∀ i, 1 ≤ i → i+n ≤ 512 → ∀ (t : State) (m2 : List Bool) (v : State) (m : List Bool),
    CompressedCompactStage base x p i t.basis →
    (∀ q ∈ skywalkPoolWires base,
      v.basis q = (run (compressedCompactForward base i n) m2 t).basis q) →
    run (obReverse i n) m (pullState (obSig (i+n-1)) v) =
      pullState (obSig (i-1)) (run (compressedCompactReverse base i n) m v) ∧
    ∀ q ∈ skywalkPoolWires base, (run (compressedCompactReverse base i n) m v).basis q = t.basis q := by
  obtain ⟨hp0, hpo, hp, cop⟩ := obPrime_facts x hx0 hx
  induction n with
  | zero =>
    intro i _ _ t m2 v m _ hv
    refine ⟨?_, ?_⟩
    · simp only [obReverse, compressedCompactReverse, run, Nat.add_zero]
    · intro q hq
      have h := hv q hq
      simpa only [compressedCompactReverse, compressedCompactForward, run] using h
  | succ n ih =>
    intro i h1 hb t m2 v m ht hv
    have hi : i ≤ 511 := by omega
    have e1 : obReverse i (n+1) = obReverse (i+1) n ++ renameProgram (obSig i)
        (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i) := by
      rw [obReverse]
    have e2 : compressedCompactReverse base i (n+1) = compressedCompactReverse base (i+1) n ++
        (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i) := by
      rw [compressedCompactReverse, List.append_assoc]
    have e3 : compressedCompactForward base i (n+1) =
        (compactSkywalkTick base i ++ compressedPackAfter base i) ++
          compressedCompactForward base (i+1) n := by
      rw [compressedCompactForward]
    rw [e3, run_append] at hv
    have ht' := (compressedCompactStage_step base base_pool_nodup base_above x p i hp0 hx0 hpo hp hx
      cop (by omega) t (m2.take (measurementCount
        (compactSkywalkTick base i ++ compressedPackAfter base i))) ht).2
    have cntR := (obCounts_gen (i+1) n).2.2.2.2.1
    obtain ⟨r1, r2⟩ := ih (i+1) (by omega) (by omega) _ _ v
      (m.take (measurementCount (compressedCompactReverse base (i+1) n))) ht' hv
    rw [show i+1-1 = i by omega, show i+1+n-1 = i+(n+1)-1 by omega] at r1
    have rt := obOneStep_roundtrip x hx0 hx i (by omega) t ht
      (m2.take (measurementCount (compactSkywalkTick base i ++ compressedPackAfter base i)))
      (m.drop (measurementCount (compressedCompactReverse base (i+1) n)))
    have agree := obPool_agree _ (obUntick_pool i (by omega))
      (m.drop (measurementCount (compressedCompactReverse base (i+1) n))) _ _ r2
    rw [rt] at agree
    have z := obStage_zero x i (by omega) t.basis ht
    have hz1 : (run (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i)
        (m.drop (measurementCount (compressedCompactReverse base (i+1) n)))
        (run (compressedCompactReverse base (i+1) n)
          (m.take (measurementCount (compressedCompactReverse base (i+1) n))) v)).basis
        (base (1028+i)) = false :=
      (agree _ (obBase_pool (1028+i) (by omega))).trans z.1
    have hz2 : 257 ≤ i → (run (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i)
        (m.drop (measurementCount (compressedCompactReverse base (i+1) n)))
        (run (compressedCompactReverse base (i+1) n)
          (m.take (measurementCount (compressedCompactReverse base (i+1) n))) v)).basis
        (base (2053-i)) = false := fun big =>
      (agree _ (obBase_pool (2053-i) (by omega))).trans (z.2 big)
    rw [e1, e2, run_append, run_append, cntR, r1, obRun_rename i hi,
      ← obPull_step i hi _ hz1 hz2]
    exact ⟨rfl, agree⟩

theorem obReverse_run (x : Nat) (hx0 : 0 < x) (hx : x < p) (s : State) (m2 : List Bool)
    (hs : CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis)
    (v : State)
    (hv : ∀ q ∈ skywalkPoolWires base,
      v.basis q = (run (compressedCompactForward base 1 511) m2 s).basis q)
    (m : List Bool) :
    run (obReverse 1 511) m (pullState (obSig 511) v) = run (compressedCompactReverse base 1 511) m v := by
  have h := (obReverse_gen x hx0 hx 511 1 (Nat.le_refl 1) (by omega) s m2 v m
    (obStage_one x s hs) hv).1
  have e : ∀ u : State, pullState (obSig (1-1)) u = u := by
    intro u
    apply State.extensionality
    · rfl
    · funext q
      show u.basis (obSig 0 q) = u.basis q
      rw [obSig_zero]
  rw [e, show 1+511-1 = 511 from rfl] at h
  exact h

/-! ## Support -/

/-- Physical wires of the one-bank integer passes. -/
abbrev OBGood (q : Wire) : Prop := q ∈ slots.toFinset ∧ ¬ obRemoved q ∧ goodW q

theorem obGood_label (l : Nat) (h : l < 515 ∨ (770 ≤ l ∧ l < 1285) ∨ (1540 ≤ l ∧ l < 1797)) :
    OBGood (base l) := by
  refine ⟨slot_mem l (by unfold live; omega) (by unfold CompressedAllocation.omitted; omega), ?_, ?_⟩
  · show ¬ (1301 ≤ l+16 ∧ l+16 < 1556)
    omega
  · show ¬ (l+16 = 769+16 ∨ l+16 = 2313+16 ∨ (2401+16 ≤ l+16 ∧ l+16 ≤ 2408+16))
    omega

theorem obGood_placed (k l : Nat) (hk : k ≤ 511)
    (hl : l < 515 ∨ (770 ≤ l ∧ l ≤ 1028+k) ∨ (1540 ≤ l ∧ l < 1797 ∧ l+k < 2053)) :
    OBGood (obSig k (base l)) := by
  rw [obSig_base k l hk]
  apply obGood_label
  split_ifs <;> omega

theorem obTick_labels (i : Nat) (hi : i < 512) (h1 : 1 ≤ i) (q : Wire)
    (hq : q ∈ (compactSkywalkTickLayout base i).wires.toFinset) :
    ∃ l, q = base l ∧
      (l < 515 ∨ (770 ≤ l ∧ l ≤ 1028+i) ∨ (1540 ≤ l ∧ l < 1797 ∧ l+i < 2053)) := by
  have width := compactSkywalkTick_width_bounds i hi
  have view : (compactSkywalkTickLayout base i).wires =
      ([skywalkPoolPreviousId i,1028+i,i+compactSkywalkTickPreWidth i,i,770]++
      List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
      List.range' 771 (compactSkywalkTickPreWidth i-1)++
      List.range' 1540 (compactSkywalkTickPreWidth i-1)).map base := by
    change base (skywalkPoolPreviousId i)::base (1028+i)::
      base (i+compactSkywalkTickPreWidth i)::base i::base 770::
      ((compactSkywalkTickLayout base i).ah++(compactSkywalkTickLayout base i).bh++
      wireBlock base 1540 (compactSkywalkTickPreWidth i-1)) = _
    rw [compactSkywalkTick_ah base i hi,compactSkywalkTick_bh base i hi]
    simp [wireBlock,List.map_append,List.append_assoc]
  rw [List.mem_toFinset, view] at hq
  obtain ⟨old, h, rfl⟩ := List.mem_map.mp hq
  refine ⟨old, rfl, ?_⟩
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  have hz : i ≠ 0 := by omega
  simp only [skywalkPoolPreviousId,if_neg hz] at h
  omega

theorem obCodec_labels (i : Nat) (hi : i < 512) (q : Wire)
    (hq : q ∈ wires (compressedPackAfter base i) ∨ q ∈ wires (compressedDecodeBefore base i)) :
    ∃ l, q = base l ∧ (l < 515 ∨ (770 ≤ l ∧ l ≤ 1028+i)) := by
  cases hd : compressedPackDue i
  · simp [compressedPackAfter, compressedDecodeBefore, hd, wires] at hq
  · have h3 := compressedPackDue_true i hd
    rw [compressedPackAfter, compressedDecodeBefore, if_pos hd, if_pos hd] at hq
    have mem : ∃ u : Fin 6, q = base (compressedHistoryId (i-3) u) := by
      rcases hq with hq | hq
      · exact compressedHistory_gate_mem base base_pool_nodup base_above (i-3)
          (by omega) _ (Or.inl rfl) q hq
      · exact compressedHistory_gate_mem base base_pool_nodup base_above (i-3)
          (by omega) _ (Or.inr rfl) q hq
    obtain ⟨u, rfl⟩ := mem
    refine ⟨_, rfl, ?_⟩
    have hu := u.isLt
    unfold compressedHistoryId
    split <;> omega

theorem obBlocks_good (i : Nat) (hi : i < 512) (h1 : 1 ≤ i) :
    (∀ q ∈ wires (renameProgram (obSig i)
      (compactSkywalkTick base i ++ compressedPackAfter base i)), OBGood q) ∧
    (∀ q ∈ wires (renameProgram (obSig i)
      (compressedDecodeBefore base i ++ compactSkywalkReverseTick base i)), OBGood q) := by
  have tick : ∀ q ∈ (compactSkywalkTickLayout base i).wires.toFinset, OBGood (obSig i q) := by
    intro q hq
    obtain ⟨l, rfl, hl⟩ := obTick_labels i hi h1 q hq
    exact obGood_placed i l (by omega) hl
  have codec : ∀ q, (q ∈ wires (compressedPackAfter base i) ∨
      q ∈ wires (compressedDecodeBefore base i)) → OBGood (obSig i q) := by
    intro q hq
    obtain ⟨l, rfl, hl⟩ := obCodec_labels i hi q hq
    exact obGood_placed i l (by omega) (by omega)
  constructor
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨old, hraw, rfl⟩ := Finset.mem_image.mp hq
    rw [wires_append, Finset.mem_union] at hraw
    rcases hraw with h | h
    · exact tick old (compactSkywalkTick_support base i hi base_pool_nodup h)
    · exact codec old (Or.inl h)
  · intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨old, hraw, rfl⟩ := Finset.mem_image.mp hq
    rw [wires_append, Finset.mem_union] at hraw
    rcases hraw with h | h
    · exact codec old (Or.inr h)
    · exact tick old (compactSkywalkReverseTick_support base i hi base_pool_nodup h)

theorem obSupport_gen (i n : Nat) (h1 : 1 ≤ i) (hb : i+n ≤ 512) :
    (∀ q ∈ wires (obForward i n), OBGood q) ∧ (∀ q ∈ wires (obReverse i n), OBGood q) := by
  induction n generalizing i with
  | zero => simp [obForward, obReverse, wires]
  | succ n ih =>
    have rest := ih (i+1) (by omega) (by omega)
    have blocks := obBlocks_good i (by omega) h1
    rw [obForward, obReverse]
    constructor
    · intro q hq
      rw [wires_append, Finset.mem_union] at hq
      rcases hq with h | h
      · exact blocks.1 q h
      · exact rest.1 q h
    · intro q hq
      rw [wires_append, Finset.mem_union] at hq
      rcases hq with h | h
      · exact rest.2 q h
      · exact blocks.2 q h

theorem obForward_support :
    ∀ q ∈ wires (obForward 1 511), q ∈ slots.toFinset ∧ ¬ obRemoved q ∧ goodW q :=
  (obSupport_gen 1 511 (Nat.le_refl 1) (by omega)).1

theorem obReverse_support :
    ∀ q ∈ wires (obReverse 1 511), q ∈ slots.toFinset ∧ ¬ obRemoved q ∧ goodW q :=
  (obSupport_gen 1 511 (Nat.le_refl 1) (by omega)).2

/-! ## Physical gates -/

theorem obPhysical_gen (i n : Nat) (hb : i+n ≤ 512) :
    GatePhysical (obForward i n) ∧ GatePhysical (obReverse i n) := by
  induction n generalizing i with
  | zero => simp [obForward, obReverse, GatePhysical]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := compactTicks_physical base i (by omega) base_pool_nodup
    have codec := transcriptCodec_physical (compressedHistoryMap base (i-3))
    have pack : GatePhysical (compressedPackAfter base i) := by
      unfold compressedPackAfter
      split
      · rw [compressedHistoryEncode]; exact codec.1
      · simp [GatePhysical]
    have unpack : GatePhysical (compressedDecodeBefore base i) := by
      unfold compressedDecodeBefore
      split
      · rw [compressedHistoryDecode]; exact codec.2
      · simp [GatePhysical]
    have inj := obSig_injective i (by omega)
    have f := gatePhysical_rename _ inj _
      ((gatePhysical_append (compactSkywalkTick base i) (compressedPackAfter base i)).mpr
        ⟨tick.1, pack⟩)
    have b := gatePhysical_rename _ inj _
      ((gatePhysical_append (compressedDecodeBefore base i) (compactSkywalkReverseTick base i)).mpr
        ⟨unpack, tick.2⟩)
    rw [obForward, obReverse, gatePhysical_append, gatePhysical_append]
    exact ⟨⟨f, rest.1⟩, ⟨rest.2, b⟩⟩

theorem obForward_physical : GatePhysical (obForward 1 511) :=
  (obPhysical_gen 1 511 (by omega)).1

theorem obReverse_physical : GatePhysical (obReverse 1 511) :=
  (obPhysical_gen 1 511 (by omega)).2

end ECDSAAdd.Entrant

end

section
-- ===== OBCell =====
/-! One-bank field, part 2: the single-carry-bank field segment (programs).

The current field segment runs every cell kernel on two carry banks: the
balanced core uses bank 1 (labels `1540..1795`, parity `1796`) and the offset
cleanup uses bank 2 (`512..764`, `766..768`).  After the late signs of the
integer walk move into the narrowed carry slots, the labels `1542..1796` hold
signs during the field, so the field may not touch them.

Here every kernel is the already proved single-bank `BalancedCircuit` /
`BalancedInverse` program on `obPorts`: its 256 carries are the bank-2 labels
`512..764` plus `1540`, `1541` and `1026`, and its parity is `2312`.  The two
boundary converter pairs are the old converters with their carry/flag labels
rebound by the involution `obConvSigma` (`1542+k ↔ 512+k`, `1796 ↔ 1026`).
Codec, copy and the cell-zero swap are unchanged. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation CompressedFieldSupport

/-- Single-bank kernel ports.  Words, sign, `lower`, `one` and the four
selector scalars are those of `balancedSharedPorts`; only the carry ladder
and the parity move. -/
def obPorts (w : Nat → Wire) (sign : Wire) : BalancedCircuit.Layout :=
  { r0:=w 2056,rtail:=wireBlock w 2057 254,rmsb:=w 2311,
    ylow:=wireBlock w 770 255,ymsb:=w 1025,
    carry:=wireBlock w 512 253++[w 1540,w 1541,w 1026],
    sign:=sign,parity:=w 2312,lower:=w 1797,one:=w 1027,
    sourceGuard:=w 765,cout:=w 768,minus:=w 767,plus:=w 766 }

/-- Logical (identity-frame) single-bank cell `i`. -/
def obLogicalCell (divide : Bool) (i : Nat) : Program :=
  let unit := mixedTranscriptUnitTrace.getD i (false,false)
  if divide then balancedTranscriptCell (obPorts id 2409) 2400 i (1028+i) 2410 unit.1 unit.2
  else balancedInverseTranscriptCell (obPorts id 2409) 2400 i (1028+i) 2410 unit.1 unit.2

/-- Kernel with its sign-polarity wrapper. -/
def obHalf (divide : Bool) (L : BalancedCircuit.Layout) : Program :=
  [.X L.sign]++(if divide then BalancedCircuit.program L else BalancedInverse.program L)++[.X L.sign]

/-- Endpoint cell 510: the G-selected kernel without the S window. -/
def obEndpoint (divide : Bool) : Program :=
  transcriptSelectWindow 2400 510 2409 (mixedTranscriptUnitTrace.getD 510 (false,false)).1
    (obHalf divide (obPorts id 2409))

/-- Converter label rebinding: `1542+k ↔ 512+k` (`k < 253`) and `1796 ↔ 1026`. -/
def obConvFn (q : Nat) : Nat :=
  if 1542 ≤ q ∧ q ≤ 1794 then q-1030
  else if 512 ≤ q ∧ q ≤ 764 then q+1030
  else if q=1796 then 1026
  else if q=1026 then 1796 else q

theorem obConvFn_invol : Function.Involutive obConvFn := by
  intro q
  unfold obConvFn
  split_ifs <;> omega

def obConvSigma : Equiv.Perm Nat := obConvFn_invol.toPerm

/-- Rebound converter pair (logical frame). -/
def obConverterPair (canonical : Bool) : Program :=
  renameProgram obConvSigma (converterPair canonical)

def obMappedGroup (divide : Bool) (j : Nat) : Program :=
  compressedHistoryDecode (placed j) (3*j) ++
  (if divide then renameProgram (placed j) (obLogicalCell divide (3*j)) ++
      renameProgram (placed j) (obLogicalCell divide (3*j+1)) ++
      renameProgram (placed j) (obLogicalCell divide (3*j+2))
   else renameProgram (placed j) (obLogicalCell divide (3*j+2)) ++
      renameProgram (placed j) (obLogicalCell divide (3*j+1)) ++
      renameProgram (placed j) (obLogicalCell divide (3*j))) ++
  compressedHistoryEncode (placed j) (3*j)

def obMappedGroups (divide : Bool) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if divide then obMappedGroup divide j++obMappedGroups divide (j+1) n
    else obMappedGroups divide (j+1) n++obMappedGroup divide j

def obFirstGroup (divide : Bool) : Program :=
  compressedHistoryDecode (placed 0) 0 ++
  (if divide then renameProgram (placed 0) EntryMappedFieldSegmentTrim.logicalZero ++
      renameProgram (placed 0) (obLogicalCell divide 1) ++
      renameProgram (placed 0) (obLogicalCell divide 2)
   else renameProgram (placed 0) (obLogicalCell divide 2) ++
      renameProgram (placed 0) (obLogicalCell divide 1) ++
      renameProgram (placed 0) EntryMappedFieldSegmentTrim.logicalZero) ++
  compressedHistoryEncode (placed 0) 0

def obReplay (divide : Bool) : Program :=
  if divide then obFirstGroup divide ++ obMappedGroups divide 1 169 ++
      renameProgram allPlaced (obEndpoint divide)
  else renameProgram allPlaced (obEndpoint divide) ++
      obMappedGroups divide 1 169 ++ obFirstGroup divide

/-- The one-bank field segment: `selectedFieldSegment` with every block that
touches labels `1542..1796` replaced. -/
def obFieldSegment (divide : Bool) : Program :=
  (if divide then [] else renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) ++
  renameProgram allPlaced (obConverterPair false) ++ obReplay divide ++
  renameProgram allPlaced (obConverterPair true) ++
  (if divide then renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) else [])

/-! ## Layout facts -/

def obIds : List Nat := [765,768,767,766,2312,1797,1027,2311,1025,2056]++
  List.range' 2057 254++List.range' 770 255++List.range' 512 253++[1540,1541,1026]

theorem obIds_nodup : obIds.Nodup := by decide

theorem obIds_bound (j : Nat) (hj : j∈obIds) : j<2314 := by
  simp only [obIds,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
  omega

theorem obPorts_widths (w : Nat → Wire) (sign : Wire) : (obPorts w sign).Widths := by
  simp [BalancedCircuit.Layout.Widths,BalancedCleanup.Layout.Widths,obPorts,wireBlock]

theorem obPorts_ylow (w : Nat → Wire) (sign : Wire) : (obPorts w sign).ylow≠[] := by
  intro h
  have len := (obPorts_widths w sign).2.1
  rw [h] at len
  contradiction

theorem obPorts_r (w : Nat → Wire) (sign : Wire) :
    (obPorts w sign).r=(balancedSharedPorts w sign).r := rfl
theorem obPorts_y (w : Nat → Wire) (sign : Wire) :
    (obPorts w sign).y=(balancedSharedPorts w sign).y := rfl
theorem obPorts_sign (w : Nat → Wire) (sign : Wire) : (obPorts w sign).sign=sign := rfl

theorem obPorts_nodup (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hs : sign∉obIds.map w) :
    (obPorts w sign).wires.Nodup := by
  have mapped : (obIds.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkShared_index_inj w hn i j (obIds_bound i hi) (obIds_bound j hj) he
    · exact obIds_nodup
  have all : (sign::obIds.map w).Nodup := List.nodup_cons.mpr ⟨hs,mapped⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp all q
  simp only [obPorts,obIds,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,wireBlock,List.map_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

def obWorkIds : List Nat := [765,768,767,766,2312,1797,1027]++List.range' 512 253++[1540,1541,1026]

theorem obPorts_work (w : Nat → Wire) (sign : Wire) :
    BalancedCircuit.work (obPorts w sign)=obWorkIds.map w := by
  simp [BalancedCircuit.work,obPorts,obWorkIds,wireBlock]

private def availableIds : List Nat :=
  List.range' 1540 257++List.range' 1798 256++[1797]++List.range' 512 257++
    [2313,769,1027,2054,2055]

private theorem obWork_split : ∀ j∈obWorkIds, j=2312 ∨ j=1026 ∨ j∈availableIds := by decide

theorem obWork_bound (j : Nat) (hj : j∈obWorkIds) : j<2314 := by
  simp only [obWorkIds,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
  omega

theorem obPorts_work_shared (w : Nat → Wire) (sign : Wire) (q : Wire)
    (hq : q∈BalancedCircuit.work (obPorts w sign)) : q∈skywalkSharedWires w := by
  rw [obPorts_work] at hq
  exact balancedSharedLayout_mapSubset w obWorkIds obWork_bound hq

/-- All single-bank scratch is clean under the caller environment and a
clean y-extension site `2312`. -/
theorem obPorts_clean (w : Nat → Wire) (sign : Wire) (base : BasisState)
    (he : OffsetBorrowedCanonical.Env w base) (hz : base (w 2312)=false) :
    ∀q∈BalancedCircuit.work (obPorts w sign),base q=false := by
  have available : (skywalkSharedField w).work++skywalkSharedUnused w=availableIds.map w := by
    simp [skywalkSharedField,skywalkSharedUnused,ModInPlaceLayout.work,
      ModAddCoreLayout.work,availableIds,wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [obPorts_work] at hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  rcases obWork_split j hj with h|h|h
  · subst h; exact hz
  · subst h; exact he.2.2
  · have mem : w j∈(skywalkSharedField w).work++skywalkSharedUnused w := by
      rw [available]; exact List.mem_map_of_mem h
    rcases List.mem_append.mp mem with m|m
    · exact (regValue_zero _ _).mp he.1 _ m
    · exact (regValue_zero _ _).mp he.2.1 _ m

theorem obPorts_transcript (w : Nat → Wire) (b g swap sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w) :
    BalancedTranscriptLayout (obPorts w sign) b g swap effS where
  widths := obPorts_widths w sign
  kernel := obPorts_nodup w sign hn
    (fun h => ho (balancedSharedLayout_mapSubset w obIds obIds_bound h))
  controls := hl.controls
  outside := hl.outside
  scratch := ⟨fun h => ho (obPorts_work_shared w sign _ h),
    fun h => hoS (obPorts_work_shared w sign _ h)⟩
  swapND := hl.swapND

/-! ## Relabeling naturality -/

section Natural
open FieldRename
attribute [local irreducible] literalConstAdd compareLt rotateLeft rotateRight signComplement
  addInPlace subInPlace mappedAdd mappedSub swapRegisters transcriptSelectWindow
  BalancedCircuit.coreProgram

theorem ob_cleanup_natural (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    renameProgram f (BalancedCleanup.program L)=BalancedCleanup.program (mapCleanup f L) := by
  simp only [BalancedCleanup.program,BalancedCleanup.normalize,BalancedCleanup.unnormalize,
    BalancedCleanup.prepareCompare,rename_append,rename_reverse,prepareSign_natural,
    literalConstAdd_natural,rotateLeft_natural,signComplement_natural,compareLt_natural,
    low_map,r_map,y_map,List.map_take]
  rfl

theorem ob_circuit_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow≠[]) :
    renameProgram f (BalancedCircuit.program L)=BalancedCircuit.program (mapCircuit f L) := by
  rw [BalancedCircuit.program_eq_core,BalancedCircuit.program_eq_core]
  simp only [rename_append,coreProgram_natural f L hy,ob_cleanup_natural]
  rfl

theorem ob_inverse_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow≠[]) :
    renameProgram f (BalancedInverse.program L)=BalancedInverse.program (mapCircuit f L) := by
  simp only [BalancedInverse.program,BalancedInverse.recoverParity,rename_append,rename_reverse,
    ob_cleanup_natural,recoverSelectors_natural,rotateLeft_natural,rawTarget_map,undoFold_natural,
    undoPreparation_natural,rawSubtract_natural,seedViews_natural f L hy]
  rfl

theorem ob_circuit_r (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (mapCircuit f L).r=L.r.map f := r_map f L.toLayout
theorem ob_circuit_y (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (mapCircuit f L).y=L.y.map f := y_map f L.toLayout

theorem ob_half_natural (f : Wire → Wire) (divide : Bool) (L : BalancedCircuit.Layout)
    (hy : L.ylow≠[]) : renameProgram f (obHalf divide L)=obHalf divide (mapCircuit f L) := by
  cases divide <;> simp only [obHalf,Bool.false_eq_true,if_false,if_true,rename_append,
    ob_circuit_natural f L hy,ob_inverse_natural f L hy] <;> rfl

theorem ob_cell_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow≠[])
    (b g swap effS : Wire) (ig is : Bool) :
    renameProgram f (balancedTranscriptCell L b g swap effS ig is)=
      balancedTranscriptCell (mapCircuit f L) (f b) (f g) (f swap) (f effS) ig is := by
  simp only [balancedTranscriptCell,balancedTranscriptBody,selectWindow_natural,rename_append,
    ob_circuit_natural f L hy,swapRegisters_natural,ob_circuit_r,ob_circuit_y]
  rfl

theorem ob_inverse_cell_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow≠[])
    (b g swap effS : Wire) (ig is : Bool) :
    renameProgram f (balancedInverseTranscriptCell L b g swap effS ig is)=
      balancedInverseTranscriptCell (mapCircuit f L) (f b) (f g) (f swap) (f effS) ig is := by
  simp only [balancedInverseTranscriptCell,balancedInverseTranscriptBody,selectWindow_natural,
    rename_append,ob_inverse_natural f L hy,swapRegisters_natural,ob_circuit_r,ob_circuit_y]
  rfl

theorem obPorts_map (f w : Wire → Wire) (sign : Wire) :
    mapCircuit f (obPorts w sign)=obPorts (f ∘ w) (f sign) := by
  simp only [mapCircuit,mapCleanup,obPorts,wireBlock_map,List.map_append,List.map_cons,
    List.map_nil,Function.comp_def]

theorem obLogicalCell_natural (f : Wire → Wire) (divide : Bool) (i : Nat) :
    renameProgram f (obLogicalCell divide i)=
      (if divide then balancedTranscriptCell (obPorts f (f 2409)) (f 2400) (f i) (f (1028+i))
          (f 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2
       else balancedInverseTranscriptCell (obPorts f (f 2409)) (f 2400) (f i) (f (1028+i))
          (f 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2) := by
  cases divide <;> simp only [obLogicalCell,Bool.false_eq_true,if_false,if_true,
    ob_cell_natural f _ (obPorts_ylow id 2409),ob_inverse_cell_natural f _ (obPorts_ylow id 2409),
    obPorts_map,Function.comp_id]

theorem obEndpoint_natural (f : Wire → Wire) (divide : Bool) :
    renameProgram f (obEndpoint divide)=
      transcriptSelectWindow (f 2400) (f 510) (f 2409)
        (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (obHalf divide (obPorts f (f 2409))) := by
  simp only [obEndpoint,selectWindow_natural,ob_half_natural f divide _ (obPorts_ylow id 2409),
    obPorts_map,Function.comp_id]

end Natural

end ECDSAAdd.Entrant

end

section
-- ===== OBFGroup =====
/-! One-bank field, part 3: packets 1..169 are state-equal to the current ones.

Every one-bank packet satisfies the same encoded-frame contract as the current
packet (same payload update, phase kept).  Encoded field frames with equal
payload and phase are equal States, so the two packets agree as complete
States for every pair of record streams. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation CompressedFieldSupport Secp256k1 BalancedField
attribute [local irreducible] run obLogicalCell compressedHistoryEncode compressedHistoryDecode
  balancedTranscriptCell balancedInverseTranscriptCell logicalCell

/-- The field contract's caller hypotheses, bundled. -/
structure ObCtx (origin : BasisState) : Prop where
  hn : (skywalkSharedWires base).Nodup
  hlo : CompressedHistoryAbove base
  ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base
  hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base
  hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)
  hg0 : origin (base 2409)=false
  hs0 : origin (base 2410)=false
  env : OffsetBorrowedCanonical.Env base origin
  legal : RawGroupLegal base 170 origin
  hr : origin (base 2312)=false

/-- Complete-State equality for every pair of record streams, on a domain. -/
def ObEquiv (I : State → Prop) (P Q : Program) : Prop :=
  ∀ s,I s → ∀ m n : List Bool,run P m s=run Q n s

theorem obEquiv_append {I J : State → Prop} {A A' B B' : Program}
    (ha : ObEquiv I A' A) (post : ∀ s m,I s → J (run A m s)) (hb : ObEquiv J B' B) :
    ObEquiv I (A'++B') (A++B) := by
  intro s hs m n
  rw [run_append,run_append,ha s hs _ (n.take (measurementCount A))]
  exact hb _ (post s _ hs) _ _

theorem obEquiv_zero (I : State → Prop) (P : Program) (h : measurementCount P=0) :
    ObEquiv I P P := by
  intro s _ m n
  exact OffsetBorrowedCanonical.zero_records P h s m n

/-- Some encoded field frame (any payload). -/
def ObEnc (origin : BasisState) (s : State) : Prop :=
  ∃ X Y : Fp,EncodedFieldFrame base (base 2409) origin X Y s

/-! ## Generic clean rebinding -/

theorem ob_pull_zero (e : Equiv.Perm Wire) (Z : Wire → Prop) (fix : ∀ q,¬Z q → e q=q)
    (t : State) (hz : ∀ q,Z q → t.basis q=false) : pullState e t=t := by
  apply State.extensionality
  · rfl
  · funext q
    change t.basis (e q)=t.basis q
    by_cases hq : Z q
    · have he : Z (e q) := by
        by_contra bad
        have eq := e.injective (fix (e q) bad)
        exact bad (eq.symm ▸ hq)
      rw [hz _ he,hz _ hq]
    · rw [fix q hq]

/-- Rebinding a program's clean scratch: if a permutation moves only labels
that are zero before and after the original program, the renamed program
produces the identical complete State (all records, all phases). -/
theorem ob_rebind_run (e : Equiv.Perm Wire) (Z : Wire → Prop) (fix : ∀ q,¬Z q → e q=q)
    (P : Program) (s : State) (m : List Bool)
    (hin : ∀ q,Z q → s.basis q=false) (hout : ∀ q,Z q → (run P m s).basis q=false) :
    run (renameProgram e P) m s=run P m s := by
  apply pullState_perm_injective e
  rw [run_rename _ e.injective,ob_pull_zero e Z fix s hin,ob_pull_zero e Z fix _ hout]

theorem ob_shifted_state_eq (e : Equiv.Perm Nat) (fix : ∀ q,¬zeroRegion q → e q=q)
    (P : Program) (s : State) (m : List Bool)
    (hin : ∀ q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀ q,zeroRegion q → (run P m s).basis (base q)=false) :
    run (renameProgram (shifted e) P) m s=run P m s := by
  apply pullState_perm_injective (shifted e)
  rw [run_rename _ (shifted e).injective,shifted_zero_boundary e fix s hin,
    shifted_zero_boundary e fix _ hout]

/-! ## Support of a one-bank cell inside its packet -/

theorem obPorts_wires_perm (w : Nat → Wire) (sign : Wire) :
    (obPorts w sign).wires.Perm (sign::obIds.map w) := by
  apply List.perm_iff_count.mpr
  intro q
  simp only [obPorts,obIds,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,wireBlock,List.map_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil]
  omega

def obSharedIds : List Nat := [765,1026]++balancedSharedIds++List.range' 512 253++[766,767,768]

theorem sharedSites_perm (w : Nat → Wire) (sign : Wire) :
    (sharedSites w sign).Perm (sign::sign::obSharedIds.map w) := by
  apply List.perm_iff_count.mpr
  intro q
  simp only [sharedSites,balancedSharedPorts,balancedSharedIds,obSharedIds,
    OffsetCleanupBorrowedCaller.carry,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,wireBlock,List.map_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil]
  omega

theorem obIds_shared (j : Nat) (hj : j∈obIds) : j=2312 ∨ j∈obSharedIds := by
  simp only [obIds,obSharedIds,balancedSharedIds,List.mem_append,List.mem_cons,
    List.not_mem_nil,List.mem_range'_1,or_false] at hj ⊢
  omega

theorem obPorts_site (w : Nat → Wire) (sign : Wire) (q : Wire) (hq : q∈(obPorts w sign).wires) :
    q∈sharedSites w sign ∨ q=w 2312 := by
  rcases List.mem_cons.mp ((obPorts_wires_perm w sign).mem_iff.mp hq) with h|h
  · left; subst h; simp [sharedSites]
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    rcases obIds_shared j hj with e|e
    · right; rw [e]
    · left
      exact (sharedSites_perm w sign).mem_iff.mpr
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem e)))

theorem ob_hist_sites (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (j t : Nat) (hj : j < 170) (ht : t < 3) :
    base (3*j+t)∈wires (compressedHistoryEncode base (3*j)) ∧
    base (1028+(3*j+t))∈wires (compressedHistoryEncode base (3*j)) := by
  have pool := skywalkShared_integer_nodup base hn
  have a := compressedHistory_site_mem base pool hlo (3*j) (by omega) ⟨2*t,by omega⟩
  have b := compressedHistory_site_mem base pool hlo (3*j) (by omega) ⟨2*t+1,by omega⟩
  have ea : compressedHistoryId (3*j) ⟨2*t,by omega⟩=3*j+t := by
    show (if (2*t)%2=0 then 3*j+(2*t)/2 else 1028+3*j+(2*t)/2)=3*j+t
    split <;> omega
  have eb : compressedHistoryId (3*j) ⟨2*t+1,by omega⟩=1028+(3*j+t) := by
    show (if (2*t+1)%2=0 then 3*j+(2*t+1)/2 else 1028+3*j+(2*t+1)/2)=1028+(3*j+t)
    split <;> omega
  simp only [compressedHistoryMap,ea,eb] at a b
  exact ⟨a,b⟩

/-- A one-bank cell reads only shared field sites, the packet's own six raw
history sites, the activation and selection flags, and the parity `2312`. -/
theorem obCell_support (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (j t : Nat) (hj : j < 170) (ht : t < 3) :
    ∀ q∈wires (renameProgram base (obLogicalCell divide (3*j+t))),
      q∈groupReadSites base (base 2400) (base 2409) (base 2410) (3*j) ∨ q=base 2312 := by
  intro q hq
  have hw := obPorts_widths base (base 2409)
  have sup : q∈([base 2400,base (3*j+t),base (1028+(3*j+t)),base 2410]++
      (obPorts base (base 2409)).wires).toFinset := by
    cases divide <;> simp only [obLogicalCell_natural,Bool.false_eq_true,if_false,if_true] at hq
    · exact balancedInverseTranscriptCell_support _ _ _ _ _ _ _ hw hq
    · exact balancedTranscriptCell_support _ _ _ _ _ _ _ hw hq
  have hs := ob_hist_sites hn hlo j t hj ht
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at sup
  rcases sup with (h|h|h|h)|h
  · left; subst h; simp [groupReadSites]
  · left; subst h; simp [groupReadSites,hs.1]
  · left; subst h; simp [groupReadSites,hs.2]
  · left; subst h; simp [groupReadSites]
  · rcases obPorts_site base (base 2409) q h with h|h
    · left; simp [groupReadSites,h]
    · right; exact h

/-! ## Codec conjugation with the extended read set -/

private theorem ob_current_records (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (hlo : CompressedHistoryAbove w) (j : Nat) (hj : j < 170) (s : State) (m : List Bool)
    (legal : RawGroupLegal w 170 s.basis) :
    run (compressedHistoryEncode w (3*j)) m s=run (compressedHistoryEncode w (3*j)) [] s := by
  have a := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s m (legal j hj)
  have z := TranscriptCodec3.placement_correct (compressedHistoryMap w (3*j))
    (compressedHistoryMap_injective w hn (3*j) (by omega))
    (compressedHistoryMap_above w (3*j) (by omega) hlo) s [] (legal j hj)
  apply State.extensionality
  · simpa only [compressedHistoryEncode] using a.1.trans z.1.symm
  · exact run_basis_records _ s s m [] rfl

/-- `EntrySelectedSwapFrame.encoded_window_step`, with the body allowed to
read the additional site `w 2312`. -/
theorem ob_encoded_window_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (j : Nat) (hj : j < 170) (origin : BasisState) (legal : RawGroupLegal w 170 origin)
    (X Y A B : Fp) (body : Program)
    (support : ∀ q∈wires body,q∈groupReadSites w b sign eff (3*j) ∨ q=w 2312)
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame w sign origin X Y s) :
    let out := run (compressedHistoryDecode w (3*j)++body++compressedHistoryEncode w (3*j)) m s
    out.phase=s.phase ∧ EncodedFieldFrame w sign origin A B out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have hs := hp sign (by simp)
  have leg := frame_history_legal w sign hn hs origin raw.basis _ _ legal frame
  have factor := allGroupEncode_factor w pool hlo 170 j (by decide) hj raw
  have hE := otherGroupEncode_disjoint w pool hlo 170 j (by decide) hj
  have hB : Disjoint (wires (otherGroupEncode w j 170)) (wires body) := by
    apply Finset.disjoint_left.mpr
    intro q hq hbody
    obtain ⟨k,hk,ne,member⟩ := otherGroupEncode_member w 170 j q hq
    rcases support q hbody with h|h
    · have dis := other_encoder_disjoint w b sign eff hn hlo (hp b (by simp)) hs
        (hp eff (by simp)) (3*k) (3*j) (by omega) (by omega) (by omega) [.X q] (by
          intro x hx
          have hxq : x=q := by simpa [wires,Instr.wires] using hx
          subst hxq; exact h)
      exact Finset.disjoint_left.mp dis member (by simp [wires,Instr.wires])
    · obtain ⟨u,hu⟩ := compressedHistory_gate_mem w pool hlo (3*k) (by omega) _
        (Or.inl rfl) q member
      have bound := compressedHistoryId_bound (3*k) (by omega) u
      rw [h] at hu
      have same := skywalkShared_index_inj w hn 2312 _ (by omega) (by omega) hu
      omega
  let rawOut := run body m raw
  have result := correct raw m frame
  have outLegal := frame_history_legal w sign hn hs origin rawOut.basis _ _ legal result.2
  have transport := window_transport_other w (3*j) pool hlo (by omega)
    (otherGroupEncode w j 170) body hE hB raw [] [] [] m
    (m.drop (measurementCount body)) (leg j hj)
  rw [ob_current_records w pool hlo j hj rawOut _ outLegal] at transport
  have back := allGroupEncode_factor w pool hlo 170 j (by decide) hj rawOut
  rw [←back] at transport
  have actual : run (compressedHistoryDecode w (3*j)++body++compressedHistoryEncode w (3*j)) m s=
      run (allGroupEncode w 170) [] rawOut := by
    rw [eq,factor]
    have zero := (compressedHistory_counts w (3*j)).2.2.2
    simp only [List.append_assoc]
    rw [run_append,zero,List.take_zero,List.drop_zero,run_append,run_take]
    exact transport
  dsimp only
  rw [actual]
  have encPhase := allGroupEncode_phase w pool hlo 170 (by decide) rawOut [] outLegal
  exact ⟨encPhase.trans (result.1.trans phase),rawOut,encPhase.symm,result.2,rfl⟩

/-! ## One-bank packets -/

def obGroupBody (divide : Bool) (j : Nat) : Program :=
  if divide then renameProgram base (obLogicalCell divide (3*j)) ++
      renameProgram base (obLogicalCell divide (3*j+1)) ++
      renameProgram base (obLogicalCell divide (3*j+2))
  else renameProgram base (obLogicalCell divide (3*j+2)) ++
      renameProgram base (obLogicalCell divide (3*j+1)) ++
      renameProgram base (obLogicalCell divide (3*j))

def obBaseGroup (divide : Bool) (j : Nat) : Program :=
  compressedHistoryDecode base (3*j)++obGroupBody divide j++compressedHistoryEncode base (3*j)

theorem obMappedGroup_eq_rename (divide : Bool) (j : Nat) (hj : j < 170) :
    obMappedGroup divide j=renameProgram (shifted (pi j)) (obBaseGroup divide j) := by
  have codec := shifted_current_codec j hj
  have append (f : Wire → Wire) (p q : Program) :
      renameProgram f (p++q)=renameProgram f p++renameProgram f q := by
    simp only [renameProgram,List.map_append]
  cases divide <;>
    simp only [obMappedGroup,obBaseGroup,obGroupBody,Bool.false_eq_true,if_false,if_true,
      append,codec.1,codec.2,shifted_cell]

theorem obGroupBody_replay (divide : Bool) (j : Nat) (hj : j < 170) :
    obGroupBody divide j=
      (if divide then balancedTranscriptReplay (obPorts base (base 2409)) (base 2400) (base 2410)
          (packetLetters j)
       else balancedInverseTranscriptReplay (obPorts base (base 2409)) (base 2400) (base 2410)
          (packetLetters j)) := by
  have a := mixedTape_base_getD (3*j) (by omega)
  have c := mixedTape_base_getD (3*j+1) (by omega)
  have d := mixedTape_base_getD (3*j+2) (by omega)
  cases divide <;> simp only [obGroupBody,packetLetters,a,c,d,obLogicalCell_natural,
    balancedTranscriptReplay,balancedInverseTranscriptReplay,Bool.false_eq_true,if_false,if_true,
    List.append_nil,List.nil_append,List.append_assoc]

theorem obGroupBody_support (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (j : Nat) (hj : j < 170) :
    ∀ q∈wires (obGroupBody divide j),
      q∈groupReadSites base (base 2400) (base 2409) (base 2410) (3*j) ∨ q=base 2312 := by
  have a := obCell_support divide hn hlo j 0 hj (by omega)
  have b := obCell_support divide hn hlo j 1 hj (by omega)
  have c := obCell_support divide hn hlo j 2 hj (by omega)
  simp only [Nat.add_zero] at a
  intro q hq
  cases divide <;> simp only [obGroupBody,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.mem_union] at hq
  · rcases hq with (h|h)|h
    · exact c q h
    · exact b q h
    · exact a q h
  · rcases hq with (h|h)|h
    · exact a q h
    · exact b q h
    · exact c q h

theorem obGroupBody_frame (divide : Bool) (j : Nat) (hj : j < 170) (origin : BasisState)
    (ctx : ObCtx origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (obGroupBody divide j)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (directionalPayload (!divide)
          (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).1)
        (centerWord (directionalPayload (!divide)
          (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).2)) := by
  have hf := packet_layouts (base 2400) (base 2409) (base 2410) ctx.hf j hj
  have hl : BalancedTranscriptReplayLayout (obPorts base (base 2409)) (base 2400) (base 2410)
      (packetLetters j) := fun l hm =>
    obPorts_transcript base _ _ _ _ _ ctx.hn
      (balancedSharedTranscriptLayout_direct base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        (hf l hm) ctx.ho) (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have hc := obPorts_clean base (base 2409) origin ctx.env ctx.hr
  rw [obGroupBody_replay divide j hj]
  cases divide
  · have tr := balancedInverseTranscriptReplay_frame _ _ _ _ hl origin ctx.hg0 ctx.hs0 hc X Y
    simpa only [directionalPayload,Bool.not_false,if_true,Bool.false_eq_true,if_false] using tr
  · have tr := balancedTranscriptReplay_frame _ _ _ _ hl origin ctx.hg0 ctx.hs0 hc X Y
    simpa only [directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,if_true] using tr

theorem obMappedGroup_step (divide : Bool) (j : Nat) (hj : j < 170) (origin : BasisState)
    (ctx : ObCtx origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (obMappedGroup divide j) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).2
      out := by
  have ref := ob_encoded_window_step base (base 2400) (base 2409) (base 2410) ctx.hn ctx.hlo ctx.hp
    j hj origin ctx.legal X Y _ _ (obGroupBody divide j) (obGroupBody_support divide ctx.hn ctx.hlo j hj)
    (obGroupBody_frame divide j hj origin ctx X Y) s m input
  change (run (obBaseGroup divide j) m s).phase=s.phase ∧ _ at ref
  have cleanIn := encoded_zero_region base (base 2409) ctx.hn ctx.hlo origin ctx.env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) ctx.hn ctx.hlo origin ctx.env _ _ _ ref.2
  have same : run (obMappedGroup divide j) m s=run (obBaseGroup divide j) m s := by
    rw [obMappedGroup_eq_rename divide j hj]
    exact ob_shifted_state_eq (pi j) (fun q hq => pi_outside j q hj hq) _ s m cleanIn cleanOut
  dsimp only
  rw [same]
  exact ref

theorem obMappedGroup_equiv (divide : Bool) (j : Nat) (hj : j < 170) (origin : BasisState)
    (ctx : ObCtx origin) : ObEquiv (ObEnc origin) (obMappedGroup divide j) (mappedGroup divide j) := by
  rintro s ⟨X,Y,input⟩ m n
  have a := obMappedGroup_step divide j hj origin ctx X Y s m input
  have b := mappedGroup_encoded_step divide j hj ctx.hn ctx.hlo ctx.ho ctx.hp
    (packet_layouts _ _ _ ctx.hf j hj) origin ctx.hg0 ctx.hs0 ctx.env ctx.legal X Y s n input
  exact EntryMappedFieldSegmentTrim.encoded_field_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

theorem obMappedGroups_equiv (divide : Bool) (origin : BasisState) (ctx : ObCtx origin)
    (j n : Nat) (bound : j+n ≤ 170) :
    ObEquiv (ObEnc origin) (obMappedGroups divide j n) (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero =>
    intro s _ m n
    simp only [obMappedGroups,mappedGroups,run]
  | succ n ih =>
    have grp := obMappedGroup_equiv divide j (by omega) origin ctx
    have postG : ∀ s m,ObEnc origin s → ObEnc origin (run (mappedGroup divide j) m s) := by
      rintro s m ⟨X,Y,h⟩
      exact ⟨_,_,(mappedGroup_encoded_step divide j (by omega) ctx.hn ctx.hlo ctx.ho ctx.hp
        (packet_layouts _ _ _ ctx.hf j (by omega)) origin ctx.hg0 ctx.hs0 ctx.env ctx.legal
        X Y s m h).2⟩
    have postR : ∀ s m,ObEnc origin s → ObEnc origin (run (mappedGroups divide (j+1) n) m s) := by
      rintro s m ⟨X,Y,h⟩
      exact ⟨_,_,(mappedGroups_frame divide (j+1) n (by omega) ctx.hn ctx.hlo ctx.ho ctx.hp
        (packet_layouts _ _ _ ctx.hf) origin ctx.hg0 ctx.hs0 ctx.env ctx.legal X Y s m h).2.2⟩
    have rest := ih (j+1) (by omega)
    cases divide
    · simp only [obMappedGroups,mappedGroups,Bool.false_eq_true,if_false]
      exact obEquiv_append rest postR grp
    · simp only [obMappedGroups,mappedGroups,if_true]
      exact obEquiv_append grp postG rest

end ECDSAAdd.Entrant

end

section
-- ===== OBFFirst =====
/-! One-bank field, part 4: the first packet (cell zero keeps only its S swap).

The one-bank first packet runs the retained selected swap of cell zero and
two single-bank cells.  It satisfies the same encoded-frame contract as the
current first packet, so the two agree as complete States. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation CompressedFieldSupport Secp256k1 BalancedField
attribute [local irreducible] run obLogicalCell compressedHistoryEncode compressedHistoryDecode
  balancedTranscriptCell balancedInverseTranscriptCell logicalCell

def obFirstBody (divide : Bool) : Program :=
  if divide then renameProgram base EntryMappedFieldSegmentTrim.logicalZero ++
      renameProgram base (obLogicalCell divide 1) ++ renameProgram base (obLogicalCell divide 2)
  else renameProgram base (obLogicalCell divide 2) ++
      renameProgram base (obLogicalCell divide 1) ++
      renameProgram base EntryMappedFieldSegmentTrim.logicalZero

def obBaseFirstGroup (divide : Bool) : Program :=
  compressedHistoryDecode base 0++obFirstBody divide++compressedHistoryEncode base 0

theorem obFirstGroup_eq_rename (divide : Bool) :
    obFirstGroup divide=renameProgram (shifted (pi 0)) (obBaseFirstGroup divide) := by
  have codec := shifted_current_codec 0 (by decide)
  have append (f : Wire → Wire) (p q : Program) :
      renameProgram f (p++q)=renameProgram f p++renameProgram f q := by
    simp only [renameProgram,List.map_append]
  cases divide <;> simp only [obFirstGroup,obBaseFirstGroup,obFirstBody,Bool.false_eq_true,
    if_false,if_true,append,Nat.mul_zero,codec.1,codec.2,shifted_cell]

private theorem ob_zero_natural : renameProgram base EntryMappedFieldSegmentTrim.logicalZero =
    EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028) (base 2409) (base 2410)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 := by
  have rmap : (balancedSharedPorts base (base 2409)).r=
      (balancedSharedPorts id 2409).r.map base := by
    simpa only [Function.comp_id] using FieldRename.shared_r_map base id 2409
  have ymap : (balancedSharedPorts base (base 2409)).y=
      (balancedSharedPorts id 2409).y.map base := by
    simpa only [Function.comp_id] using FieldRename.shared_y_map base id 2409
  simp only [EntryMappedFieldSegmentTrim.logicalZero,EntryFieldSeedCancellation.selectedSwap,
    FieldRename.selectWindow_natural,FieldRename.swapRegisters_natural,rmap,ymap]

private theorem ob_payload_zero (g sw : Bool) (Y : Fp) :
    skywalkPayloadCell g sw (2*Y,0)=(if sw then 0 else Y,if sw then Y else 0) := by
  have two : (2:Fp)≠0 := by decide
  have half : (2*Y)/2=Y := mul_div_cancel_left₀ Y two
  simp only [skywalkPayloadCell,neg_zero,ite_self,add_zero,half]
  cases sw <;> rfl

/-- Letters 1 and 2 of packet zero satisfy the single-bank transcript layout. -/
private theorem ob_rest_layout (origin : BasisState) (ctx : ObCtx origin) :
    BalancedTranscriptReplayLayout (obPorts base (base 2409)) (base 2400) (base 2410)
      [(mixedTranscriptTape base).getD 1 ((0,0),(false,false)),
       (mixedTranscriptTape base).getD 2 ((0,0),(false,false))] := by
  have hf := packet_layouts (base 2400) (base 2409) (base 2410) ctx.hf 0 (by decide)
  intro l hm
  have hm' : l∈packetLetters 0 := by
    simp only [packetLetters,Nat.mul_zero,Nat.zero_add,List.mem_cons,List.not_mem_nil,or_false]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    exact Or.inr hm
  exact obPorts_transcript base _ _ _ _ _ ctx.hn
    (balancedSharedTranscriptLayout_direct base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
      (hf l hm') ctx.ho) (ctx.ho _ (by simp)) (ctx.ho _ (by simp))

private theorem ob_zero_layout (origin : BasisState) (ctx : ObCtx origin) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409)) (base 2400) (base 0)
      (base 1028) (base 2410) := by
  have hf := packet_layouts (base 2400) (base 2409) (base 2410) ctx.hf 0 (by decide)
  let a := (mixedTranscriptTape base).getD 0 ((0,0),(false,false))
  have aEq := mixedTape_base_getD 0 (by decide)
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) a.1.1 a.1.2
    (base 2409) (base 2410) (hf a (by simp [a,packetLetters])) ctx.ho
  rw [show a=((base 0,base 1028),mixedTranscriptUnitTrace.getD 0 (false,false)) from aEq] at layout
  exact layout

theorem obFirstBody_forward_frame (origin : BasisState) (ctx : ObCtx origin) (Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord Y) (centerWord 0)) (obFirstBody true)
      (PairFrame (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y origin
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)).1)
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)).2)) := by
  let a := (mixedTranscriptTape base).getD 0 ((0,0),(false,false))
  let c := (mixedTranscriptTape base).getD 1 ((0,0),(false,false))
  let d := (mixedTranscriptTape base).getD 2 ((0,0),(false,false))
  have aEq := mixedTape_base_getD 0 (by decide)
  have cEq := mixedTape_base_getD 1 (by decide)
  have dEq := mixedTape_base_getD 2 (by decide)
  have sw := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (ob_zero_layout origin ctx) origin ctx.hs0 Y 0
  let A := if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then 0 else Y
  let B := if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then Y else 0
  have hc := obPorts_clean base (base 2409) origin ctx.env ctx.hr
  have rest := balancedTranscriptReplay_frame _ _ _ [c,d] (ob_rest_layout origin ctx) origin
    ctx.hg0 ctx.hs0 hc A B
  have result := sw.seq rest
  have bodyEq : obFirstBody true=EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028)
      (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 ++
      balancedTranscriptReplay (obPorts base (base 2409)) (base 2400) (base 2410) [c,d] := by
    simp only [obFirstBody,ob_zero_natural,balancedTranscriptReplay,obLogicalCell_natural,
      if_true,List.append_nil,c,d,cEq,dEq,List.append_assoc]
  rw [bodyEq]
  simpa only [packetLetters,Nat.mul_zero,Nat.zero_add,mixedTranscriptControls,List.map_cons,
    List.map_nil,skywalkPayloadReplay,aEq,ob_payload_zero,A,B,a,c,d] using result

theorem obFirstBody_inverse_frame (origin : BasisState) (ctx : ObCtx origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord X) (centerWord Y)) (obFirstBody false)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (EntryMappedFieldSegmentTrim.inverseZeroPayload origin X Y).1)
        (centerWord (EntryMappedFieldSegmentTrim.inverseZeroPayload origin X Y).2)) := by
  let c := (mixedTranscriptTape base).getD 1 ((0,0),(false,false))
  let d := (mixedTranscriptTape base).getD 2 ((0,0),(false,false))
  let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) [c,d]) (X,Y)
  have cEq := mixedTape_base_getD 1 (by decide)
  have dEq := mixedTape_base_getD 2 (by decide)
  have hc := obPorts_clean base (base 2409) origin ctx.env ctx.hr
  have rest := balancedInverseTranscriptReplay_frame _ _ _ [c,d] (ob_rest_layout origin ctx) origin
    ctx.hg0 ctx.hs0 hc X Y
  have sw := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (ob_zero_layout origin ctx) origin ctx.hs0 Q.1 Q.2
  have result := rest.seq sw
  have bodyEq : obFirstBody false=
      balancedInverseTranscriptReplay (obPorts base (base 2409)) (base 2400) (base 2410) [c,d]++
      EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028)
        (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2 := by
    simp only [obFirstBody,ob_zero_natural,balancedInverseTranscriptReplay,obLogicalCell_natural,
      Bool.false_eq_true,if_false,List.append_nil,List.nil_append,c,d,cEq,dEq,List.append_assoc]
  rw [bodyEq]
  cases bit : mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 <;>
    simpa only [EntryMappedFieldSegmentTrim.inverseZeroPayload,bit,if_true,if_false,
      Bool.false_eq_true,Q,c,d] using result

theorem obFirstBody_support (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) :
    ∀ q∈wires (obFirstBody divide),
      q∈groupReadSites base (base 2400) (base 2409) (base 2410) (3*0) ∨ q=base 2312 := by
  have pool := skywalkShared_integer_nodup base hn
  have site (k : Fin 6) := compressedHistory_site_mem base pool hlo 0 (by decide) k
  have z : wires (renameProgram base EntryMappedFieldSegmentTrim.logicalZero) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) 0 := by
    have sub : wires (renameProgram base EntryMappedFieldSegmentTrim.logicalZero) ⊆
        wires (renameProgram base (logicalCell divide 0)) := by
      rw [renameProgram_support,renameProgram_support]
      exact Finset.image_mono base (EntryMappedFieldSegmentTrim.logicalZero_support_sub divide)
    exact sub.trans (EntryBodySupport.renamed_logical_support base divide 0 0
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 0)
      (by simpa only [compressedHistoryMap,compressedHistoryId] using site 1))
  have b := obCell_support divide hn hlo 0 1 (by decide) (by decide)
  have c := obCell_support divide hn hlo 0 2 (by decide) (by decide)
  simp only [Nat.mul_zero,Nat.zero_add] at b c ⊢
  intro q hq
  cases divide <;> simp only [obFirstBody,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.mem_union] at hq
  · rcases hq with (h|h)|h
    · exact c q h
    · exact b q h
    · exact Or.inl (z h)
  · rcases hq with (h|h)|h
    · exact Or.inl (z h)
    · exact b q h
    · exact c q h

/-- Encoded step of the one-bank first packet for any body frame. -/
theorem obFirstGroup_step (divide : Bool) (origin : BasisState) (ctx : ObCtx origin) (X Y A B : Fp)
    (frame : Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord X) (centerWord Y)) (obFirstBody divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    (run (obFirstGroup divide) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A B (run (obFirstGroup divide) m s) := by
  have ref := ob_encoded_window_step base (base 2400) (base 2409) (base 2410) ctx.hn ctx.hlo ctx.hp
    0 (by decide) origin ctx.legal X Y A B (obFirstBody divide)
    (obFirstBody_support divide ctx.hn ctx.hlo) frame s m input
  change (run (obBaseFirstGroup divide) m s).phase=s.phase ∧ _ at ref
  have cleanIn := encoded_zero_region base (base 2409) ctx.hn ctx.hlo origin ctx.env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) ctx.hn ctx.hlo origin ctx.env _ _ _ ref.2
  have same : run (obFirstGroup divide) m s=run (obBaseFirstGroup divide) m s := by
    rw [obFirstGroup_eq_rename divide]
    exact ob_shifted_state_eq (pi 0) (fun q hq => pi_outside 0 q (by decide) hq) _ s m cleanIn cleanOut
  rw [same]
  exact ref

/-- Some encoded field frame with zero second word. -/
def ObEnc0 (origin : BasisState) (s : State) : Prop :=
  ∃ Y : Fp,EncodedFieldFrame base (base 2409) origin Y 0 s

theorem obFirstGroup_forward_equiv (origin : BasisState) (ctx : ObCtx origin) :
    ObEquiv (ObEnc0 origin) (obFirstGroup true) (EntryMappedFieldSegmentTrim.firstGroup true) := by
  rintro s ⟨Y,input⟩ m n
  have a := obFirstGroup_step true origin ctx Y 0 _ _ (obFirstBody_forward_frame origin ctx Y) s m input
  have b := EntryMappedFieldSegmentTrim.firstGroup_forward_step ctx.hn ctx.hlo ctx.ho ctx.hp
    (packet_layouts _ _ _ ctx.hf 0 (by decide)) origin ctx.hg0 ctx.hs0 ctx.env ctx.legal Y s n input
  dsimp only at b
  exact EntryMappedFieldSegmentTrim.encoded_field_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

theorem obFirstGroup_inverse_equiv (origin : BasisState) (ctx : ObCtx origin) :
    ObEquiv (ObEnc origin) (obFirstGroup false) (EntryMappedFieldSegmentTrim.firstGroup false) := by
  rintro s ⟨X,Y,input⟩ m n
  have a := obFirstGroup_step false origin ctx X Y _ _ (obFirstBody_inverse_frame origin ctx X Y)
    s m input
  have b := EntryMappedFieldSegmentTrim.firstGroup_inverse_step ctx.hn ctx.hlo ctx.ho ctx.hp
    (packet_layouts _ _ _ ctx.hf 0 (by decide)) origin ctx.hg0 ctx.hs0 ctx.env ctx.legal X Y s n input
  exact EntryMappedFieldSegmentTrim.encoded_field_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

/-- The current first packet keeps some encoded frame. -/
theorem firstGroup_post (divide : Bool) (origin : BasisState) (ctx : ObCtx origin) (s : State)
    (m : List Bool) (h : if divide then ObEnc0 origin s else ObEnc origin s) :
    ObEnc origin (run (EntryMappedFieldSegmentTrim.firstGroup divide) m s) := by
  cases divide
  · obtain ⟨X,Y,input⟩ := h
    exact ⟨_,_,(EntryMappedFieldSegmentTrim.firstGroup_inverse_step ctx.hn ctx.hlo ctx.ho ctx.hp
      (packet_layouts _ _ _ ctx.hf 0 (by decide)) origin ctx.hg0 ctx.hs0 ctx.env ctx.legal
      X Y s m input).2⟩
  · obtain ⟨Y,input⟩ := h
    have b := EntryMappedFieldSegmentTrim.firstGroup_forward_step ctx.hn ctx.hlo ctx.ho ctx.hp
      (packet_layouts _ _ _ ctx.hf 0 (by decide)) origin ctx.hg0 ctx.hs0 ctx.env ctx.legal Y s m input
    dsimp only at b
    exact ⟨_,_,b.2⟩

end ECDSAAdd.Entrant

end

section
-- ===== OBFEdge =====
/-! One-bank field, part 5: the raw endpoint cell 510.

Both the one-bank endpoint and the current endpoint are the G-selected
kernel without the S window.  Each has the same raw pair-frame contract for
every input payload, both are disjoint from the packet encoders, and both
move only clean labels under the placement, so they agree as complete
States on every encoded field frame. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation CompressedFieldSupport Secp256k1 BalancedField
attribute [local irreducible] run compressedHistoryEncode compressedHistoryDecode allGroupEncode
  otherGroupEncode BalancedCircuit.program BalancedInverse.program OffsetBorrowedField.program
  OffsetBorrowedInverse.program logicalCell mixedTranscriptUnitTrace mixedTranscriptTape

/-! ## Generic encoded tail step -/

/-- A raw program disjoint from the packet encoders acts on an encoded field
frame exactly as on its raw pair frame. -/
theorem ob_tail_step (P : Program) (origin : BasisState) (ctx : ObCtx origin) (X Y A B : Fp)
    (dis : Disjoint (wires (allGroupEncode base 170)) (wires P))
    (correct : Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord X) (centerWord Y)) P
      (PairFrame (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    (run P m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin A B (run P m s) := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup base ctx.hn
  have hs := ctx.hp (base 2409) (by simp)
  let rawOut := run P m raw
  have result := correct raw m frame
  have outLegal := frame_history_legal base (base 2409) ctx.hn hs origin rawOut.basis _ _
    ctx.legal result.2
  have commute := (run_disjoint_commute (allGroupEncode base 170) P dis [] m raw).symm
  have encPhase := allGroupEncode_phase base pool ctx.hlo 170 (by decide) rawOut [] outLegal
  have actual : run P m s=run (allGroupEncode base 170) [] rawOut := by
    rw [eq]
    exact commute
  rw [actual]
  exact ⟨encPhase.trans (result.1.trans phase),rawOut,encPhase.symm,result.2,rfl⟩

theorem ob_allPlaced_eq (P : Program) (s : State) (m : List Bool)
    (hin : ∀ q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀ q,zeroRegion q → (run (renameProgram base P) m s).basis (base q)=false) :
    run (renameProgram allPlaced P) m s=run (renameProgram base P) m s := by
  have rename : renameProgram allPlaced P=renameProgram (shifted pi0) (renameProgram base P) := by
    rw [renameProgram_comp]
    congr 1
  rw [rename]
  exact ob_shifted_state_eq pi0 pi0_outside _ s m hin hout

/-- The same step, moved to the global placement. -/
theorem ob_mapped_tail_step (P : Program) (origin : BasisState) (ctx : ObCtx origin) (X Y A B : Fp)
    (dis : Disjoint (wires (allGroupEncode base 170)) (wires (renameProgram base P)))
    (correct : Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord X) (centerWord Y))
      (renameProgram base P)
      (PairFrame (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    (run (renameProgram allPlaced P) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin A B (run (renameProgram allPlaced P) m s) := by
  have ref := ob_tail_step _ origin ctx X Y A B dis correct s m input
  have cleanIn := encoded_zero_region base (base 2409) ctx.hn ctx.hlo origin ctx.env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) ctx.hn ctx.hlo origin ctx.env A B _ ref.2
  rw [ob_allPlaced_eq P s m cleanIn cleanOut]
  exact ref

/-! ## Endpoint layout and support -/

theorem ob_edge_layout (origin : BasisState) (ctx : ObCtx origin) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409)) (base 2400) (base 510)
      (base 1538) (base 2410) := by
  have layout : MixedTranscriptFieldLayout base (base 2400) (base 510) (base 1538)
      (base 2409) (base 2410) := by
    simpa only [mixedTape_base_getD 510 (by decide),Nat.reduceAdd] using
      mixedTape_getD_layout base (base 2400) (base 2409) (base 2410) ctx.hf 510 (by decide)
  exact balancedSharedTranscriptLayout_direct base (base 2400) (base 510)
    (base 1538) (base 2409) (base 2410) layout ctx.ho

private theorem ob_flags (w : Nat → Wire) (b g swap sign effS : Wire)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS) :
    [b,g,sign].Nodup ∧
    (b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y) ∧
    (g∉(balancedSharedPorts w sign).r ∧ g∉(balancedSharedPorts w sign).y) ∧
    (sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y) := by
  have ctrl := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ctrl
  refine ⟨?_,hl.outside b (by simp),hl.outside g (by simp),
    hl.outside sign (by simp [balancedSharedPorts])⟩
  simp [List.nodup_cons]
  tauto

private theorem ob_select_support (b source flag : Wire) (v : Bool) (p : Program) :
    wires (transcriptSelectWindow b source flag v p)⊆
      [b,source,flag].toFinset ∪ wires p := by
  intro q hq
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil] at hq ⊢ <;> tauto

/-- The one-bank endpoint touches its two window controls, the shared field
sites (including its sign) and the parity `2312`. -/
theorem obEndpoint_sites (divide : Bool) (q : Wire)
    (hq : q∈wires (renameProgram base (obEndpoint divide))) :
    q=base 2400 ∨ q=base 510 ∨ q∈sharedSites base (base 2409) ∨ q=base 2312 := by
  have signSite : base 2409∈sharedSites base (base 2409) :=
    (sharedSites_perm base (base 2409)).mem_iff.mpr (List.mem_cons_self ..)
  rw [obEndpoint_natural] at hq
  have h := ob_select_support (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (obHalf divide (obPorts base (base 2409))) hq
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with (h|h|h)|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · subst h; exact Or.inr (Or.inr (Or.inl signSite))
  · have hw := obPorts_widths base (base 2409)
    have k : q∈(obPorts base (base 2409)).wires.toFinset ∨ q=base 2409 := by
      cases divide <;> simp only [obHalf,obPorts_sign,Bool.false_eq_true,if_false,if_true,
        wires_append,Finset.mem_union] at h
      · rcases h with (h|h)|h
        · right; simpa [wires,Instr.wires] using h
        · exact Or.inl (BalancedInverse.support _ hw h)
        · right; simpa [wires,Instr.wires] using h
      · rcases h with (h|h)|h
        · right; simpa [wires,Instr.wires] using h
        · exact Or.inl (BalancedCircuit.support _ hw h)
        · right; simpa [wires,Instr.wires] using h
    rcases k with k|k
    · rcases obPorts_site base (base 2409) q (List.mem_toFinset.mp k) with h|h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · subst k; exact Or.inr (Or.inr (Or.inl signSite))

private theorem ob_encoder_member (w : Nat → Wire) (q : Wire)
    (h : q ∈ wires (allGroupEncode w 170)) :
    ∃ k,k < 170 ∧ q ∈ wires (compressedHistoryEncode w (3*k)) := by
  rw [←otherGroupEncode_outside w 170 170 (Nat.le_refl _)] at h
  obtain ⟨k,hk,_,hm⟩ := otherGroupEncode_member w 170 170 q h
  exact ⟨k,hk,hm⟩

theorem obEndpoint_disjoint (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base) :
    Disjoint (wires (allGroupEncode base 170)) (wires (renameProgram base (obEndpoint divide))) := by
  apply Finset.disjoint_left.mpr
  intro q hq hW
  obtain ⟨k,hk,hm⟩ := ob_encoder_member base q hq
  obtain ⟨j,rfl⟩ := compressedHistory_gate_mem base (skywalkShared_integer_nodup base hn) hlo
    (3*k) (by omega) _ (Or.inl rfl) q hm
  have bound : compressedHistoryId (3*k) j < 1798 := compressedHistoryId_bound (3*k) (by omega) j
  have own : base (compressedHistoryId (3*k) j) ∈ skywalkPoolWires base := by
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨_,by omega,rfl⟩
  have active := history_active_away base (base 2409) hn (hp (base 2409) (by simp)) (3*k) (by omega) j
  rcases obEndpoint_sites divide _ hW with h|h|h|h
  · apply hp (base 2400) (by simp)
    rw [←h]
    exact own
  · have eq := skywalkShared_index_inj base hn _ 510 (by omega) (by omega) h
    have hj := j.isLt
    unfold compressedHistoryId at eq
    split_ifs at eq <;> omega
  · exact active h
  · have eq := skywalkShared_index_inj base hn _ 2312 (by omega) (by omega) h
    omega

theorem oldEndpoint_disjoint (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base) :
    Disjoint (wires (allGroupEncode base 170))
      (wires (renameProgram base (PenultimateSwapIdentity.cell divide))) := by
  let unit := mixedTranscriptUnitTrace.getD 510 (false,false)
  have letter : tapeLetter 510=((base 510,base 1538),unit) := by
    simp only [tapeLetter,mixedTape_base_getD 510 (by decide),Nat.reduceAdd,unit]
  have aligned : IndexedLetters base 510 [tapeLetter 510] := by
    simp only [letter,IndexedLetters]
    exact ⟨trivial,trivial⟩
  have dis := tail_replay_disjoint base (base 2400) (base 2409) (base 2410)
    hn hlo hp 510 [tapeLetter 510] (by omega) (by simp) aligned
  have oldDis : Disjoint (wires (allGroupEncode base 170))
      (wires (renameProgram base (logicalCell divide 510))) := by
    rw [FieldRename.logical_cell_natural]
    cases divide
    · simpa only [OffsetBorrowedInverseCanonical.replay,letter,List.append_nil,List.nil_append,
        Bool.false_eq_true,if_false,Nat.reduceAdd] using dis.2
    · simpa only [OffsetBorrowedCanonical.replay,letter,List.append_nil,List.nil_append,
        if_true,Nat.reduceAdd] using dis.1
  have sub : wires (renameProgram base (PenultimateSwapIdentity.cell divide))⊆
      wires (renameProgram base (logicalCell divide 510)) := by
    rw [renameProgram_support,renameProgram_support]
    exact Finset.image_mono base (PenultimateMappedCellProof.logical_support_subset divide)
  exact oldDis.mono_right sub

/-! ## Raw contracts -/

/-- Common endpoint output word. -/
def obEdgeValue (divide : Bool) (origin : BasisState) (X Y : Fp) : Fp :=
  if divide then (X+(if mixedTranscriptBit origin (base 2400) (base 510)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 then Y else -Y))/2
  else 2*X+(if mixedTranscriptBit origin (base 2400) (base 510)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 then -Y else Y)

theorem oldEndpoint_raw_frame (divide : Bool) (origin : BasisState) (ctx : ObCtx origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord X) (centerWord Y))
      (renameProgram base (PenultimateSwapIdentity.cell divide))
      (PairFrame (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y origin
        (centerWord (obEdgeValue divide origin X Y)) (centerWord Y)) := by
  have f := ob_flags base _ _ _ _ _ (ob_edge_layout origin ctx)
  have old := EndpointSwapTrim.partial_frame divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 ctx.hn (ctx.ho _ (by simp))
    f.1 f.2.1 f.2.2.1 f.2.2.2 origin ctx.hg0 ctx.env X Y
  rw [PenultimateMappedCellProof.cell_natural]
  exact old

theorem obEndpoint_raw_frame (divide : Bool) (origin : BasisState) (ctx : ObCtx origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin (centerWord X) (centerWord Y))
      (renameProgram base (obEndpoint divide))
      (PairFrame (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y origin
        (centerWord (obEdgeValue divide origin X Y)) (centerWord Y)) := by
  have hl := ob_edge_layout origin ctx
  have f := ob_flags base _ _ _ _ _ hl
  have kn := (obPorts_transcript base _ _ _ _ _ ctx.hn hl (ctx.ho _ (by simp))
    (ctx.ho _ (by simp))).kernel
  have env := OffsetBorrowedCanonical.env_write base (base 2409) (ctx.ho _ (by simp)) origin
    (mixedTranscriptBit origin (base 2400) (base 510)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1) ctx.env
  have z : (mixedTranscriptBase origin (base 2400) (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1) (base 2312)=false := by
    simp only [mixedTranscriptBase,writeBit]
    rw [Function.update_of_ne (by simp [base])]
    exact ctx.hr
  have hc := obPorts_clean base (base 2409) _ env z
  rw [obEndpoint_natural]
  cases divide
  · have body := balancedTranscriptDouble_frame (obPorts base (base 2409)) (obPorts_widths _ _) kn
      _ hc X Y
    simp only [mixedTranscriptBase,writeBit,obPorts_sign,Function.update_self] at body
    have window := transcriptSelectWindow_pairFrame (base 2400) (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1
      (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      f.1 f.2.1 f.2.2.1 f.2.2.2 origin ctx.hg0 _ _ _ _ _ body
    simpa only [obHalf,obEdgeValue,obPorts_sign,Bool.false_eq_true,if_false] using window
  · have body := balancedTranscriptHalf_frame (obPorts base (base 2409)) (obPorts_widths _ _) kn
      _ hc X Y
    simp only [mixedTranscriptBase,writeBit,obPorts_sign,Function.update_self] at body
    have window := transcriptSelectWindow_pairFrame (base 2400) (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1
      (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      f.1 f.2.1 f.2.2.1 f.2.2.2 origin ctx.hg0 _ _ _ _ _ body
    simpa only [obHalf,obEdgeValue,obPorts_sign,if_true] using window

/-! ## Mapped endpoint equivalence -/

theorem obEndpoint_equiv (divide : Bool) (origin : BasisState) (ctx : ObCtx origin) :
    ObEquiv (ObEnc origin) (renameProgram allPlaced (obEndpoint divide))
      (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) := by
  rintro s ⟨X,Y,input⟩ m n
  have a := ob_mapped_tail_step (obEndpoint divide) origin ctx X Y _ _
    (obEndpoint_disjoint divide ctx.hn ctx.hlo ctx.hp) (obEndpoint_raw_frame divide origin ctx X Y)
    s m input
  have b := ob_mapped_tail_step (PenultimateSwapIdentity.cell divide) origin ctx X Y _ _
    (oldEndpoint_disjoint divide ctx.hn ctx.hlo ctx.hp) (oldEndpoint_raw_frame divide origin ctx X Y)
    s n input
  exact EntryMappedFieldSegmentTrim.encoded_field_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

theorem oldEndpoint_post (divide : Bool) (origin : BasisState) (ctx : ObCtx origin) (s : State)
    (m : List Bool) (h : ObEnc origin s) :
    ObEnc origin (run (renameProgram allPlaced (PenultimateSwapIdentity.cell divide)) m s) := by
  obtain ⟨X,Y,input⟩ := h
  exact ⟨_,_,(ob_mapped_tail_step (PenultimateSwapIdentity.cell divide) origin ctx X Y _ _
    (oldEndpoint_disjoint divide ctx.hn ctx.hlo ctx.hp) (oldEndpoint_raw_frame divide origin ctx X Y)
    s m input).2⟩

end ECDSAAdd.Entrant

end

section
-- ===== OBFConv =====
/-! One-bank field, part 6: the rebound boundary converters.

The one-bank converters are the current converters with their carry and
flag labels rebound by `obConvSigma`.  Every rebound label is clean on the
encoded frames before and after the converters, so the generic clean
rebinding lemma `ob_rebind_run` makes the two programs produce the identical
complete State. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation CompressedFieldSupport Secp256k1 BalancedField
attribute [local irreducible] run compressedHistoryEncode compressedHistoryDecode allGroupEncode
  otherGroupEncode mixedTranscriptUnitTrace mixedTranscriptTape BalancedConvert.center
  BalancedConvert.canonical

/-- Labels moved by `obConvSigma`. -/
def obConvMoved (i : Nat) : Prop :=
  (512 ≤ i ∧ i ≤ 764) ∨ (1542 ≤ i ∧ i ≤ 1794) ∨ i=1026 ∨ i=1796

theorem obConvSigma_fix (i : Nat) (h : ¬obConvMoved i) : obConvSigma i=i := by
  change obConvFn i=i
  unfold obConvFn
  unfold obConvMoved at h
  split_ifs <;> omega

theorem obConv_rename (c : Bool) :
    renameProgram allPlaced (obConverterPair c)=
      renameProgram (shifted pi0) (renameProgram (shifted obConvSigma) (converterPairAt base c)) := by
  rw [←converterPair_natural base c,obConverterPair,renameProgram_comp,renameProgram_comp,
    renameProgram_comp]
  congr 1

/-- Converter rebinding: on states where every rebound label is clean before
and after the current converter (and the placement boundary is clean), the
rebound converter produces the identical complete State. -/
theorem obConv_state_eq (c : Bool) (s : State) (m : List Bool)
    (zin : ∀ q,zeroRegion q → s.basis (base q)=false)
    (zout : ∀ q,zeroRegion q → (run (converterPairAt base c) m s).basis (base q)=false)
    (cin : ∀ i,obConvMoved i → s.basis (base i)=false)
    (cout : ∀ i,obConvMoved i → (run (converterPairAt base c) m s).basis (base i)=false) :
    run (renameProgram allPlaced (obConverterPair c)) m s=run (converterPairAt base c) m s := by
  have fix : ∀ q,¬(∃ i,obConvMoved i ∧ q=base i) → shifted obConvSigma q=q := by
    intro q hq
    change shiftedFn obConvSigma q=q
    unfold shiftedFn
    split_ifs with h
    · rfl
    · have le : 16 ≤ q := Nat.le_of_not_lt h
      have e : q=base (q-16) := (Nat.sub_add_cancel le).symm
      have keep : obConvSigma (q-16)=q-16 :=
        obConvSigma_fix _ (fun hm => hq ⟨q-16,hm,e⟩)
      rw [keep]
      exact Nat.sub_add_cancel le
  have inner : run (renameProgram (shifted obConvSigma) (converterPairAt base c)) m s=
      run (converterPairAt base c) m s :=
    ob_rebind_run (shifted obConvSigma) (fun q => ∃ i,obConvMoved i ∧ q=base i) fix _ s m
      (by rintro q ⟨i,hi,rfl⟩; exact cin i hi) (by rintro q ⟨i,hi,rfl⟩; exact cout i hi)
  rw [obConv_rename,ob_shifted_state_eq pi0 pi0_outside _ s m zin (by rw [inner]; exact zout),inner]

/-! ## The rebound labels are clean on encoded frames -/

def obConvAvail : List Nat :=
  List.range' 1540 257++List.range' 1798 256++[1797]++List.range' 512 257++
    [2313,769,1027,2054,2055]

theorem obConv_raw_zero (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (st : BasisState) (X Y : Nat)
    (frame : PairFrame (balancedSharedPorts base (base 2409)).r
      (balancedSharedPorts base (base 2409)).y origin X Y st)
    (i : Nat) (hi : obConvMoved i) : st (base i)=false := by
  have nr : base i∉(balancedSharedPorts base (base 2409)).r := by
    rw [balancedSharedPorts_r]
    intro h
    obtain ⟨k,hk,e⟩ := List.mem_map.mp h
    have same := base_injective e
    simp only [List.mem_range'_1] at hk
    unfold obConvMoved at hi
    omega
  have ny : base i∉(balancedSharedPorts base (base 2409)).y := by
    rw [balancedSharedPorts_y]
    intro h
    obtain ⟨k,hk,e⟩ := List.mem_map.mp h
    have same := base_injective e
    simp only [List.mem_range'_1] at hk
    unfold obConvMoved at hi
    omega
  rw [frame.2.2 _ nr ny]
  by_cases one : i=1026
  · subst one; exact env.2.2
  · have available : (skywalkSharedField base).work++skywalkSharedUnused base=obConvAvail.map base := by
      simp [skywalkSharedField,skywalkSharedUnused,ModInPlaceLayout.work,
        ModAddCoreLayout.work,obConvAvail,wireBlock,List.map_append,List.append_assoc]
    have member : i∈obConvAvail := by
      simp only [obConvAvail,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,
        or_false]
      unfold obConvMoved at hi
      omega
    have mem : base i∈(skywalkSharedField base).work++skywalkSharedUnused base := by
      rw [available]; exact List.mem_map_of_mem member
    rcases List.mem_append.mp mem with m|m
    · exact (regValue_zero _ _).mp env.1 _ m
    · exact (regValue_zero _ _).mp env.2.1 _ m

theorem obConv_encoder_away (i : Nat) (hi : obConvMoved i) :
    base i∉wires (allGroupEncode base 170) := by
  have hist := compressedPrefix_history_support base base_pool_nodup base_above 512 (by decide)
  rw [encode_prefix_512] at hist
  intro used
  have mem := List.mem_toFinset.mp (hist used)
  unfold obConvMoved at hi
  rcases List.mem_append.mp mem with mem|mem
  all_goals
    obtain ⟨k,hk,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hk
    have same := base_injective eq
    omega

theorem obConv_field_zero (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame base (base 2409) origin X Y s)
    (i : Nat) (hi : obConvMoved i) : s.basis (base i)=false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  rw [encoded]
  exact (run_preserves_outside (allGroupEncode base 170) [] raw _ (obConv_encoder_away i hi)).trans
    (obConv_raw_zero origin env raw.basis _ _ rawFrame i hi)

private theorem ob_port_split (sign : Wire) :
    (skywalkSharedField base).z=(balancedSharedPorts base sign).r++[base 2312] ∧
    (skywalkSharedField base).a=(balancedSharedPorts base sign).y++[base 1026] := by
  rw [skywalkShared_field_z,balancedSharedPorts_r,balancedSharedPorts_y]
  constructor
  · have split := wireBlock_append base 2056 256 1
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using split.symm
  · have split := wireBlock_append base 770 256 1
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using split.symm

private theorem ob_value_bound (X : Fp) : X.val < 2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])

theorem obConv_canonical_zero (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X Y : Fp) (s : State) (frame : EncodedCanonicalFrame origin X Y s)
    (i : Nat) (hi : obConvMoved i) : s.basis (base i)=false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have split := ob_port_split (base 2409)
  rw [split.1,split.2] at rawFrame
  have narrow := balancedPair_narrow (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y (base 2312) (base 1026) origin raw.basis
    X.val Y.val (by simpa only [balancedSharedPorts_r,wireBlock_length] using ob_value_bound X)
    (by simpa only [balancedSharedPorts_y,wireBlock_length] using ob_value_bound Y) rawFrame hr hy
  rw [encoded]
  exact (run_preserves_outside (allGroupEncode base 170) [] raw _ (obConv_encoder_away i hi)).trans
    (obConv_raw_zero origin env raw.basis _ _ narrow i hi)

/-! ## Converter equivalences -/

/-- Caller facts used only by the converters. -/
structure ObConvCtx (origin : BasisState) : Prop where
  hw : regValue (skywalkSharedField base).work origin=0
  hu : regValue (skywalkSharedUnused base) origin=0
  hy : origin (base 1026)=false

def ObCanon (origin : BasisState) (s : State) : Prop :=
  ∃ X Y : Fp,EncodedCanonicalFrame origin X Y s

theorem obCenter_equiv (origin : BasisState) (ctx : ObCtx origin) (cc : ObConvCtx origin) :
    ObEquiv (ObCanon origin) (renameProgram allPlaced (obConverterPair false))
      (renameProgram allPlaced (converterPair false)) := by
  rintro s ⟨X,Y,input⟩ m n
  rw [converterPair_placement false]
  have a := encoded_center_pair ctx.hn origin cc.hw cc.hu ctx.hr cc.hy X Y s m input
  have b := encoded_center_pair ctx.hn origin cc.hw cc.hu ctx.hr cc.hy X Y s n input
  have same := obConv_state_eq false s m
    (encoded_canonical_zero_region ctx.hn ctx.hlo origin cc.hw cc.hu X Y s input)
    (encoded_zero_region base (base 2409) ctx.hn ctx.hlo origin ctx.env X Y _ a.2)
    (obConv_canonical_zero origin ctx.env ctx.hr cc.hy X Y s input)
    (obConv_field_zero origin ctx.env X Y _ a.2)
  rw [same]
  exact EntryMappedFieldSegmentTrim.encoded_field_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

theorem obCanonical_equiv (origin : BasisState) (ctx : ObCtx origin) (cc : ObConvCtx origin) :
    ObEquiv (ObEnc origin) (renameProgram allPlaced (obConverterPair true))
      (renameProgram allPlaced (converterPair true)) := by
  rintro s ⟨X,Y,input⟩ m n
  rw [converterPair_placement true]
  have a := encoded_canonical_pair ctx.hn origin cc.hw cc.hu ctx.hr cc.hy X Y s m input
  have b := encoded_canonical_pair ctx.hn origin cc.hw cc.hu ctx.hr cc.hy X Y s n input
  have same := obConv_state_eq true s m
    (encoded_zero_region base (base 2409) ctx.hn ctx.hlo origin ctx.env X Y s input)
    (encoded_canonical_zero_region ctx.hn ctx.hlo origin cc.hw cc.hu X Y _ a.2)
    (obConv_field_zero origin ctx.env X Y s input)
    (obConv_canonical_zero origin ctx.env ctx.hr cc.hy X Y _ a.2)
  rw [same]
  exact EntryMappedFieldSegmentTrim.encoded_canonical_unique origin _ _ _ _ a.2 b.2
    (a.1.trans b.1.symm)

end ECDSAAdd.Entrant

end

section
-- ===== OBFRes =====
/-! One-bank field, part 7: resources, gate slots, physical gates and support
of `obFieldSegment`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation CompressedFieldSupport Secp256k1 Challenge
  Baselines RecordedQuantum
attribute [local irreducible] mixedTranscriptUnitTrace mixedTranscriptTape

private theorem renameT (f : Wire → Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem renameM (f : Wire → Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

/-! ## Exact Toffoli and measurement counts -/

private theorem ob_swap_nd : (2410::(obPorts id 2409).r++(obPorts id 2409).y).Nodup := by
  rw [obPorts_r,obPorts_y,balancedSharedPorts_r,balancedSharedPorts_y]
  simp only [wireBlock,List.map_id]
  apply List.nodup_cons.mpr
  constructor
  · intro h
    rcases List.mem_append.mp h with h|h
    all_goals have bound := List.mem_range'_1.mp h; omega
  · apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hr hy
    simp only [List.mem_range'_1] at hr hy
    omega

theorem obLogicalCell_counts (divide : Bool) (i : Nat) :
    toffoliCount (obLogicalCell divide i)=1535 ∧ measurementCount (obLogicalCell divide i)=1279 := by
  have hw := obPorts_widths id 2409
  cases divide <;> simp only [obLogicalCell,Bool.false_eq_true,if_false,if_true]
  · exact balancedInverseTranscriptCell_counts _ _ _ _ _ _ _ hw ob_swap_nd
  · exact balancedTranscriptCell_counts _ _ _ _ _ _ _ hw ob_swap_nd

theorem obMappedGroup_counts (divide : Bool) (j : Nat) :
    toffoliCount (obMappedGroup divide j)=4612 ∧ measurementCount (obMappedGroup divide j)=3838 := by
  have codec := compressedHistory_counts (placed j) (3*j)
  have a := obLogicalCell_counts divide (3*j)
  have b := obLogicalCell_counts divide (3*j+1)
  have c := obLogicalCell_counts divide (3*j+2)
  cases divide <;> simp only [obMappedGroup,Bool.false_eq_true,if_false,if_true,toffoliCount_append,
    measurementCount_append,renameT,renameM,a.1,a.2,b.1,b.2,c.1,c.2,codec.1,codec.2.1,codec.2.2.1,
    codec.2.2.2] <;> norm_num

theorem obMappedGroups_counts (divide : Bool) (j n : Nat) :
    toffoliCount (obMappedGroups divide j n)=4612*n ∧
      measurementCount (obMappedGroups divide j n)=3838*n := by
  induction n generalizing j with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have g := obMappedGroup_counts divide j
    have r := ih (j+1)
    cases divide <;> simp only [obMappedGroups,Bool.false_eq_true,if_false,if_true,toffoliCount_append,
      measurementCount_append,g.1,g.2,r.1,r.2] <;> omega

theorem obFirstGroup_counts (divide : Bool) :
    toffoliCount (obFirstGroup divide)=3334 ∧ measurementCount (obFirstGroup divide)=2560 := by
  have codec := compressedHistory_counts (placed 0) 0
  have z := EntryMappedFieldSegmentTrim.logicalZero_counts
  have a := obLogicalCell_counts divide 1
  have b := obLogicalCell_counts divide 2
  cases divide <;> simp only [obFirstGroup,Bool.false_eq_true,if_false,if_true,toffoliCount_append,
    measurementCount_append,renameT,renameM,a.1,a.2,b.1,b.2,z.1,z.2,codec.1,codec.2.1,codec.2.2.1,
    codec.2.2.2] <;> norm_num

theorem obEndpoint_counts (divide : Bool) :
    toffoliCount (obEndpoint divide)=1278 ∧ measurementCount (obEndpoint divide)=1278 := by
  have hw := obPorts_widths id 2409
  have f := BalancedCircuit.counts (obPorts id 2409) hw
  have i := BalancedInverse.counts (obPorts id 2409) hw
  have win := transcriptSelectWindow_counts 2400 510 2409
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (obHalf divide (obPorts id 2409))
  simp only [obEndpoint,win.1,win.2]
  cases divide <;> simp only [obHalf,Bool.false_eq_true,if_false,if_true,toffoliCount_append,
    measurementCount_append,f.1,f.2,i.1,i.2] <;> norm_num [toffoliCount,measurementCount]

theorem obConverterPair_counts (c : Bool) :
    toffoliCount (obConverterPair c)=1530 ∧ measurementCount (obConverterPair c)=1530 := by
  have h := converterPair_counts c
  simp only [obConverterPair,renameT,renameM,h.1,h.2,and_self]

theorem obCopy_counts :
    toffoliCount (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)=0 ∧
    measurementCount (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)=0 := by
  have len : (skywalkSharedField id).z.length=(skywalkSharedField id).a.length := by
    rw [skywalkShared_field_z]
    change (wireBlock id 2056 257).length=(wireBlock id 770 257).length
    simp [wireBlock]
  have copy := copyRegister_counts none (skywalkSharedField id).z (skywalkSharedField id).a len
  simpa using copy

theorem obFieldSegment_counts :
    toffoliCount (obFieldSegment true)=787100 ∧ measurementCount (obFieldSegment true)=655520 ∧
    toffoliCount (obFieldSegment false)=787100 ∧ measurementCount (obFieldSegment false)=655520 := by
  have cp := obCopy_counts
  have c0 := obConverterPair_counts false
  have c1 := obConverterPair_counts true
  have ft := obFirstGroup_counts true
  have ff := obFirstGroup_counts false
  have gt := obMappedGroups_counts true 1 169
  have gf := obMappedGroups_counts false 1 169
  have et := obEndpoint_counts true
  have ef := obEndpoint_counts false
  simp only [obFieldSegment,obReplay,if_true,Bool.false_eq_true,if_false,List.nil_append,
    List.append_nil,toffoliCount_append,measurementCount_append,renameT,renameM,cp.1,cp.2,c0.1,c0.2,
    c1.1,c1.2,ft.1,ft.2,ff.1,ff.2,gt.1,gt.2,gf.1,gf.2,et.1,et.2,ef.1,ef.2]
  norm_num

/-! ## Gate slots -/

theorem obCleanup_gateSlots_le (L : BalancedCleanup.Layout) (hw : L.Widths) :
    gateSlots (BalancedCleanup.program L) ≤ 13000 := by
  have w := BalancedCleanup.widths L hw
  have a := literalAdd_gateSlots_le L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.negativeLiteral
  have b := literalAdd_gateSlots_le L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.positiveLiteral
  have r := (rotate_gateSlots_le L.r).2
  have c := compareLt_gateSlots_le none L.y L.r L.carry L.one L.parity
  rw [w.1] at a b
  rw [w.2.1] at r
  rw [w.2.1,w.2.2.1] at c
  simp only [BalancedCleanup.program,BalancedCleanup.prepareSign,BalancedCleanup.normalize,
    BalancedCleanup.unnormalize,BalancedCleanup.prepareCompare,gateSlots_append,reverse_gateSlots,
    signComplement_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,w.2.1,w.2.2.1]
  omega

theorem obKernel_gateSlots_le (L : BalancedCircuit.Layout) (hw : L.Widths) :
    gateSlots (BalancedCircuit.program L) ≤ 24000 ∧ gateSlots (BalancedInverse.program L) ≤ 25000 := by
  have core := balancedCore_gateSlots_le L hw
  have cl := obCleanup_gateSlots_le L.toLayout hw
  constructor
  · rw [BalancedCircuit.program_eq_core]
    simp only [gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]
    omega
  · have t := core.2
    simp only [OffsetBorrowedInverse.tail,gateSlots_append] at t
    simp only [BalancedInverse.program,BalancedInverse.recoverParity,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots]
    omega

private theorem ob_swap_gateSlots :
    gateSlots (swapRegisters 2410 (obPorts id 2409).r (obPorts id 2409).y) ≤ 768 := by
  have len := (BalancedCleanup.widths (obPorts id 2409).toLayout (obPorts_widths id 2409)).2.1
  rw [swapRegisters_gateSlots]
  change 3*min (obPorts id 2409).toLayout.r.length _ ≤ 768
  rw [len]
  omega

theorem obLogicalCell_gateSlots_le (divide : Bool) (i : Nat) :
    gateSlots (obLogicalCell divide i) ≤ 26000 := by
  have k := obKernel_gateSlots_le (obPorts id 2409) (obPorts_widths id 2409)
  have sw := ob_swap_gateSlots
  cases divide <;> simp only [obLogicalCell,Bool.false_eq_true,if_false,if_true]
  · have body : gateSlots (balancedInverseTranscriptBody (obPorts id 2409) 2410) ≤ 25770 := by
      simp only [balancedInverseTranscriptBody,gateSlots_append,gateSlots_cons,gateSlots_nil,
        instructionSlots]
      omega
    have b := selectWindow_gateSlots_le 2400 (1028+i) 2410
      (mixedTranscriptUnitTrace.getD i (false,false)).2
      (balancedInverseTranscriptBody (obPorts id 2409) 2410)
    simp only [balancedInverseTranscriptCell]
    refine (selectWindow_gateSlots_le _ _ _ _ _).trans ?_
    omega
  · have body : gateSlots (balancedTranscriptBody (obPorts id 2409) 2410) ≤ 25770 := by
      simp only [balancedTranscriptBody,gateSlots_append,gateSlots_cons,gateSlots_nil,
        instructionSlots]
      omega
    have b := selectWindow_gateSlots_le 2400 (1028+i) 2410
      (mixedTranscriptUnitTrace.getD i (false,false)).2
      (balancedTranscriptBody (obPorts id 2409) 2410)
    simp only [balancedTranscriptCell]
    refine (selectWindow_gateSlots_le _ _ _ _ _).trans ?_
    omega

theorem obMappedGroup_gateSlots_le (divide : Bool) (j : Nat) :
    gateSlots (obMappedGroup divide j) ≤ 78400 := by
  have a := obLogicalCell_gateSlots_le divide (3*j)
  have b := obLogicalCell_gateSlots_le divide (3*j+1)
  have c := obLogicalCell_gateSlots_le divide (3*j+2)
  have h := codec_gateSlots_le (placed j) (3*j)
  cases divide <;> simp only [obMappedGroup,Bool.false_eq_true,if_false,if_true,
    gateSlots_append,rename_gateSlots] <;> omega

theorem obMappedGroups_gateSlots_le (divide : Bool) (j n : Nat) :
    gateSlots (obMappedGroups divide j n) ≤ n*78400 := by
  induction n generalizing j with
  | zero => simp only [obMappedGroups,gateSlots_nil,Nat.zero_mul,Nat.le_refl]
  | succ n ih =>
    have h := obMappedGroup_gateSlots_le divide j
    have ht := ih (j+1)
    cases divide <;> simp only [obMappedGroups,Bool.false_eq_true,if_false,if_true,
      gateSlots_append,Nat.succ_mul] <;> omega

private theorem ob_zero_gateSlots : gateSlots EntryMappedFieldSegmentTrim.logicalZero ≤ 800 := by
  have h := selectWindow_gateSlots_le 2400 1028 2410
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)
  have hl := (BalancedCleanup.widths (balancedSharedPorts id 2409).toLayout
    (balancedSharedPorts_widths id 2409)).2.1
  rw [swapRegisters_gateSlots] at h
  change _ ≤ 3*min (balancedSharedPorts id 2409).toLayout.r.length _ + 8 at h
  rw [hl] at h
  have hb : gateSlots (transcriptSelectWindow 2400 1028 2410
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2
      (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)) ≤ 800 := by
    omega
  simpa only [EntryMappedFieldSegmentTrim.logicalZero,EntryFieldSeedCancellation.selectedSwap] using hb

theorem obFirstGroup_gateSlots_le (divide : Bool) : gateSlots (obFirstGroup divide) ≤ 54000 := by
  have a := obLogicalCell_gateSlots_le divide 1
  have b := obLogicalCell_gateSlots_le divide 2
  have hc := codec_gateSlots_le (placed 0) 0
  have hz := ob_zero_gateSlots
  cases divide <;> simp only [obFirstGroup,Bool.false_eq_true,if_false,if_true,
    gateSlots_append,rename_gateSlots] <;> omega

theorem obEndpoint_gateSlots_le (divide : Bool) : gateSlots (obEndpoint divide) ≤ 26000 := by
  have k := obKernel_gateSlots_le (obPorts id 2409) (obPorts_widths id 2409)
  have h : gateSlots (obHalf divide (obPorts id 2409)) ≤ 25002 := by
    cases divide <;> simp only [obHalf,Bool.false_eq_true,if_false,if_true,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots] <;> omega
  have w := selectWindow_gateSlots_le 2400 510 2409
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (obHalf divide (obPorts id 2409))
  simp only [obEndpoint]
  omega

theorem obFieldSegment_gateSlots (divide : Bool) : gateSlots (obFieldSegment divide) ≤ 13400000 := by
  have g := obMappedGroups_gateSlots_le divide 1 169
  have f := obFirstGroup_gateSlots_le divide
  have e := obEndpoint_gateSlots_le divide
  have a := converterPair_gateSlots_le false
  have b := converterPair_gateSlots_le true
  have hcopy : gateSlots (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) ≤ 257 := by
    rw [copyRegister_gateSlots]
    have hl : (skywalkSharedField id).z.length = 257 := by
      simp only [ModInPlaceLayout.z,ModAddCoreLayout.z,skywalkSharedField,List.length_append,
        List.length_singleton,wireBlock_length]
    rw [hl]; omega
  have segmentEq (P Q R S T U : Program) (d : Bool) :
      gateSlots ((if d then [] else P)++Q++(if d then R++S++T else T++S++R)++U++
        (if d then P else []))=
        gateSlots P+gateSlots Q+gateSlots R+gateSlots S+gateSlots T+gateSlots U := by
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte,gateSlots_append,gateSlots_nil] <;> omega
  rw [obFieldSegment,obReplay,segmentEq]
  simp only [rename_gateSlots,obConverterPair]
  omega

/-! ## Physical gates -/

theorem obKernels_physical :
    GatePhysical (BalancedCircuit.program (obPorts id 2409)) ∧
    GatePhysical (BalancedInverse.program (obPorts id 2409)) := by
  constructor
  · apply physicalGateCheck_correct
    decide +kernel
  · apply physicalGateCheck_correct
    decide +kernel

theorem obLogicalCell_physical (divide : Bool) (i : Nat) (hi : i<512) :
    GatePhysical (obLogicalCell divide i) := by
  have x : GatePhysical [.X 2409] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  have k := obKernels_physical
  have sw : GatePhysical (swapRegisters 2410 (obPorts id 2409).r (obPorts id 2409).y) := by
    rw [obPorts_r,obPorts_y]
    exact fixedFieldSwap_physical
  have fb : GatePhysical (balancedTranscriptBody (obPorts id 2409) 2410) := by
    simp only [balancedTranscriptBody,gatePhysical_append,obPorts_sign]
    exact ⟨⟨⟨x,k.1⟩,x⟩,sw⟩
  have ib : GatePhysical (balancedInverseTranscriptBody (obPorts id 2409) 2410) := by
    simp only [balancedInverseTranscriptBody,gatePhysical_append,obPorts_sign]
    exact ⟨⟨⟨sw,x⟩,k.2⟩,x⟩
  have outerB : (2400 : Wire) ≠ 2409 := by decide
  have outerS : (i : Wire) ≠ 2409 := by omega
  have innerB : (2400 : Wire) ≠ 2410 := by decide
  have innerS : (1028+i : Wire) ≠ 2410 := by
    exact Nat.ne_of_lt ((Nat.add_lt_add_left hi 1028).trans (by decide))
  cases divide <;> simp only [obLogicalCell,Bool.false_eq_true,if_false,if_true,
    balancedTranscriptCell,balancedInverseTranscriptCell,obPorts_sign]
  · exact transcriptWindow_physical _ _ _ _ _ outerB outerS
      (transcriptWindow_physical _ _ _ _ _ innerB innerS ib)
  · exact transcriptWindow_physical _ _ _ _ _ outerB outerS
      (transcriptWindow_physical _ _ _ _ _ innerB innerS fb)

theorem obMappedGroup_physical (divide : Bool) (j : Nat) (hj : j<170) :
    GatePhysical (obMappedGroup divide j) := by
  have codec := transcriptCodec_physical (compressedHistoryMap (placed j) (3*j))
  have a := gatePhysical_rename _ (placed_injective j) _ (obLogicalCell_physical divide (3*j) (by omega))
  have b := gatePhysical_rename _ (placed_injective j) _ (obLogicalCell_physical divide (3*j+1) (by omega))
  have c := gatePhysical_rename _ (placed_injective j) _ (obLogicalCell_physical divide (3*j+2) (by omega))
  cases divide <;> simp only [obMappedGroup,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem obMappedGroups_physical (divide : Bool) (j n : Nat) (hj : j+n≤170) :
    GatePhysical (obMappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp [obMappedGroups,GatePhysical]
  | succ n ih =>
    have head := obMappedGroup_physical divide j (by omega)
    have tail := ih (j+1) (by omega)
    cases divide <;> simp only [obMappedGroups,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem obFirstGroup_physical (divide : Bool) : GatePhysical (obFirstGroup divide) := by
  have zero : GatePhysical EntryMappedFieldSegmentTrim.logicalZero :=
    transcriptWindow_physical _ _ _ _ _ (by decide) (by decide) fixedFieldSwap_physical
  have z := gatePhysical_rename _ (placed_injective 0) _ zero
  have a := gatePhysical_rename _ (placed_injective 0) _ (obLogicalCell_physical divide 1 (by decide))
  have b := gatePhysical_rename _ (placed_injective 0) _ (obLogicalCell_physical divide 2 (by decide))
  have codec := transcriptCodec_physical (compressedHistoryMap (placed 0) 0)
  cases divide <;> simp only [obFirstGroup,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨codec.2,⟨⟨b,a⟩,z⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨z,a⟩,b⟩⟩,codec.1⟩

theorem obEndpoint_physical (divide : Bool) : GatePhysical (obEndpoint divide) := by
  have x : GatePhysical [.X 2409] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  have k := obKernels_physical
  simp only [obEndpoint]
  apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
  cases divide <;> simp only [obHalf,Bool.false_eq_true,if_false,if_true,gatePhysical_append,
    obPorts_sign]
  · exact ⟨⟨x,k.2⟩,x⟩
  · exact ⟨⟨x,k.1⟩,x⟩

theorem obFieldSegment_physical (divide : Bool) : GatePhysical (obFieldSegment divide) := by
  have cp := gatePhysical_rename _ allPlaced_injective _ fixedCopy_physical
  have cent := gatePhysical_rename _ allPlaced_injective _
    (gatePhysical_rename _ obConvSigma.injective _ (fixedConverters_physical false))
  have canon := gatePhysical_rename _ allPlaced_injective _
    (gatePhysical_rename _ obConvSigma.injective _ (fixedConverters_physical true))
  have first := obFirstGroup_physical divide
  have groups := obMappedGroups_physical divide 1 169 (by decide)
  have last := gatePhysical_rename _ allPlaced_injective _ (obEndpoint_physical divide)
  have empty : GatePhysical [] := by simp [GatePhysical]
  cases divide <;> simp only [obFieldSegment,obReplay,obConverterPair,Bool.false_eq_true,if_false,
    if_true,gatePhysical_append]
  · exact ⟨⟨⟨⟨cp,cent⟩,⟨⟨last,groups⟩,first⟩⟩,canon⟩,empty⟩
  · exact ⟨⟨⟨⟨empty,cent⟩,⟨⟨first,groups⟩,last⟩⟩,canon⟩,cp⟩


/-! ## Support -/

section Support
attribute [local irreducible] wires BalancedConvert.center BalancedConvert.canonical
  BalancedCircuit.program BalancedInverse.program

/-- The three facts the caller needs about every one-bank field wire. -/
def ObSite (q : Wire) : Prop := q ∈ slots.toFinset ∧ ¬ (1558 ≤ q ∧ q < 1813) ∧ goodW q

def ObOK (P : Program) : Prop := ∀ q ∈ wires P, ObSite q

theorem obOK_append {P Q : Program} : ObOK (P++Q) ↔ ObOK P ∧ ObOK Q := by
  simp only [ObOK,wires_append,Finset.mem_union]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq),fun q hq => h q (Or.inr hq)⟩
  · intro h q hq; rcases hq with hq|hq
    · exact h.1 q hq
    · exact h.2 q hq

theorem obOK_nil : ObOK [] := by intro q hq; simp [wires] at hq

/-- Logical labels allowed for globally placed one-bank blocks. -/
def obLabel (i : Nat) : Prop := fieldSite i ∧ ¬(1542 ≤ i ∧ i < 1797) ∧ ¬badIdx i

/-- Logical labels allowed inside packet `j`. -/
def obPacketLabel (j i : Nat) : Prop :=
  (fieldSite i ∨ i∈packetSites j) ∧ ¬(1542 ≤ i ∧ i < 1797) ∧ ¬badIdx i

theorem ob_perm_far (e : Equiv.Perm Nat) (fix : ∀ q,¬zeroRegion q → e q=q) (i : Nat)
    (h : ¬(1542 ≤ i ∧ i < 1797)) : ¬(1542 ≤ e i ∧ e i < 1797) := by
  intro hr
  have nz : ¬zeroRegion (e i) := by
    unfold zeroRegion workRegion holeRegion
    omega
  have same := e.injective (fix _ nz)
  rw [same] at hr
  exact h hr

theorem ob_allPlaced_site (i : Nat) (h : obLabel i) : ObSite (allPlaced i) := by
  refine ⟨allPlaced_field_mem i h.1,?_,allPlaced_good i h.2.2⟩
  have far := ob_perm_far pi0 pi0_outside i h.2.1
  change ¬(1558 ≤ pi0 i+16 ∧ pi0 i+16 < 1813)
  omega

theorem ob_placed_site (j : Nat) (hj : j<170) (i : Nat) (h : obPacketLabel j i) :
    ObSite (placed j i) := by
  refine ⟨?_,?_,placed_good j i hj h.2.2⟩
  · rcases h.1 with f|f
    · exact placed_field_mem j i hj f
    · exact placed_packet_mem j i hj f
  · have far := ob_perm_far (pi j) (fun q hq => pi_outside j q hj hq) i h.2.1
    change ¬(1558 ≤ pi j i+16 ∧ pi j i+16 < 1813)
    omega

theorem obOK_allPlaced (P : Program) (h : ∀ l : Nat,l∈wires P → obLabel l) :
    ObOK (renameProgram allPlaced P) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hq
  exact ob_allPlaced_site l (h l hl)

theorem obOK_placed (j : Nat) (hj : j<170) (P : Program)
    (h : ∀ l : Nat,l∈wires P → obPacketLabel j l) :
    ObOK (renameProgram (placed j) P) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hq
  exact ob_placed_site j hj l (h l hl)

theorem obPorts_label (l : Nat) (h : l∈(obPorts id 2409).wires) : obLabel l := by
  simp only [obPorts,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold obLabel fieldSite badIdx
  omega

private theorem ob_window_support (b source flag : Wire) (v : Bool) (p : Program) :
    wires (transcriptSelectWindow b source flag v p)⊆
      [b,source,flag].toFinset ∪ wires p := by
  intro q hq
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil] at hq ⊢ <;> tauto

theorem obHalf_support (divide : Bool) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    wires (obHalf divide L) ⊆ L.wires.toFinset := by
  have sg : L.sign∈L.wires.toFinset := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have xs : wires [Instr.X L.sign] ⊆ L.wires.toFinset := by
    intro q hq
    simp only [wires,Instr.wires,List.foldr,Finset.mem_union,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    subst hq
    exact sg
  intro q hq
  cases divide <;> simp only [obHalf,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.mem_union] at hq
  · rcases hq with (h|h)|h
    · exact xs h
    · exact BalancedInverse.support L hw h
    · exact xs h
  · rcases hq with (h|h)|h
    · exact xs h
    · exact BalancedCircuit.support L hw h
    · exact xs h

theorem obCell_label (divide : Bool) (j i : Nat) (hj : j<170) (hi0 : 3*j ≤ i) (hi : i<3*j+3)
    (l : Nat) (h : l∈wires (obLogicalCell divide i)) : obPacketLabel j l := by
  have hw := obPorts_widths id 2409
  have sup : l∈([2400,i,1028+i,2410]++(obPorts id 2409).wires).toFinset := by
    cases divide <;> simp only [obLogicalCell,Bool.false_eq_true,if_false,if_true] at h
    · exact balancedInverseTranscriptCell_support _ _ _ _ _ _ _ hw h
    · exact balancedTranscriptCell_support _ _ _ _ _ _ _ hw h
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at sup
  unfold obPacketLabel
  rcases sup with (e|e|e|e)|e
  · subst e
    exact ⟨Or.inl (by unfold fieldSite; decide),by decide,by unfold badIdx; decide⟩
  · subst e
    refine ⟨Or.inr ?_,by omega,by unfold badIdx; omega⟩
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  · subst e
    refine ⟨Or.inr ?_,by omega,by unfold badIdx; omega⟩
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    unfold H
    omega
  · subst e
    exact ⟨Or.inl (by unfold fieldSite; decide),by decide,by unfold badIdx; decide⟩
  · have p := obPorts_label l e
    exact ⟨Or.inl p.1,p.2.1,p.2.2⟩

theorem obOK_codec (j : Nat) (hj : j<170) :
    ObOK (compressedHistoryEncode (placed j) (3*j)) ∧
    ObOK (compressedHistoryDecode (placed j) (3*j)) := by
  have far (u : Fin 6) : ¬(1542 ≤ compressedHistoryId (3*j) u ∧ compressedHistoryId (3*j) u < 1797) := by
    have hp := history_packet j u
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false] at hp
    unfold H at hp
    omega
  constructor
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inl rfl) q hq
    exact ob_placed_site j hj _ ⟨Or.inr (history_packet j u),far u,
      packet_not_bad j _ hj (history_packet j u)⟩
  · intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem (placed j) (placed_pool_nodup j)
      (placed_above j) (3*j) (by omega) _ (Or.inr rfl) q hq
    exact ob_placed_site j hj _ ⟨Or.inr (history_packet j u),far u,
      packet_not_bad j _ hj (history_packet j u)⟩

theorem obOK_group (divide : Bool) (j : Nat) (hj : j<170) : ObOK (obMappedGroup divide j) := by
  have codec := obOK_codec j hj
  have a := obOK_placed j hj _ (obCell_label divide j (3*j) hj (by omega) (by omega))
  have b := obOK_placed j hj _ (obCell_label divide j (3*j+1) hj (by omega) (by omega))
  have c := obOK_placed j hj _ (obCell_label divide j (3*j+2) hj (by omega) (by omega))
  cases divide <;> simp only [obMappedGroup,Bool.false_eq_true,if_false,if_true,obOK_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem obOK_groups (divide : Bool) (j n : Nat) (h : j+n ≤ 170) : ObOK (obMappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp only [obMappedGroups]; exact obOK_nil
  | succ n ih =>
    have current := obOK_group divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [obMappedGroups,Bool.false_eq_true,if_false,if_true,obOK_append]
    · exact ⟨rest,current⟩
    · exact ⟨current,rest⟩

theorem obZero_label (l : Nat) (h : l∈wires EntryMappedFieldSegmentTrim.logicalZero) :
    obPacketLabel 0 l := by
  have len := (BalancedCleanup.widths (balancedSharedPorts id 2409).toLayout
    (balancedSharedPorts_widths id 2409)).2
  have sw := swapRegisters_wires 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y
    (len.1.trans len.2.1.symm)
  have hw := ob_window_support 2400 1028 2410 (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)
  have h' : l∈wires (transcriptSelectWindow 2400 1028 2410
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2
      (swapRegisters 2410 (balancedSharedPorts id 2409).r (balancedSharedPorts id 2409).y)) := by
    simpa only [EntryMappedFieldSegmentTrim.logicalZero,EntryFieldSeedCancellation.selectedSwap] using h
  have member := hw h'
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at member
  unfold obPacketLabel
  rcases member with (e|e|e)|e
  · subst e
    unfold fieldSite badIdx
    decide
  · subst e
    refine ⟨Or.inr ?_,by decide,by unfold badIdx; decide⟩
    simp [packetSites]
  · subst e
    unfold fieldSite badIdx
    decide
  · have m := List.mem_toFinset.mp (sw e)
    rw [balancedSharedPorts_r,balancedSharedPorts_y] at m
    rcases List.mem_cons.mp m with m|m
    · subst m
      exact ⟨Or.inl (by unfold fieldSite; decide),by decide,by unfold badIdx; decide⟩
    · unfold wireBlock at m
      have hk : ∃ k : Nat,((2056 ≤ k ∧ k < 2312) ∨ (770 ≤ k ∧ k < 1026)) ∧ k=l := by
        rcases List.mem_append.mp m with m|m
        · obtain ⟨k,hk,he⟩ := List.mem_map.mp m
          have r := List.mem_range'_1.mp hk
          exact ⟨k,Or.inl (by omega),he⟩
        · obtain ⟨k,hk,he⟩ := List.mem_map.mp m
          have r := List.mem_range'_1.mp hk
          exact ⟨k,Or.inr (by omega),he⟩
      obtain ⟨k,hk,rfl⟩ := hk
      refine ⟨Or.inl ?_,?_,?_⟩
      · unfold fieldSite
        omega
      · omega
      · unfold badIdx
        omega

theorem obOK_first (divide : Bool) : ObOK (obFirstGroup divide) := by
  have codec := obOK_codec 0 (by decide)
  simp only [Nat.mul_zero] at codec
  have z := obOK_placed 0 (by decide) _ obZero_label
  have a := obOK_placed 0 (by decide) _ (obCell_label divide 0 1 (by decide) (by omega) (by omega))
  have b := obOK_placed 0 (by decide) _ (obCell_label divide 0 2 (by decide) (by omega) (by omega))
  cases divide <;> simp only [obFirstGroup,Bool.false_eq_true,if_false,if_true,obOK_append]
  · exact ⟨⟨codec.2,⟨⟨b,a⟩,z⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨z,a⟩,b⟩⟩,codec.1⟩

theorem ob_allPlaced_510 : ObSite (allPlaced 510) := by
  have fix : pi0 510=510 := pi0_outside 510 (by unfold zeroRegion workRegion holeRegion; omega)
  have eq : allPlaced 510=base 510 := by
    change pi0 510+16=510+16
    rw [fix]
  rw [eq]
  refine ⟨slot_mem 510 (by unfold live; omega) (by unfold omitted; omega),?_,
    base_good 510 (by unfold badIdx; omega)⟩
  show ¬((1558:Nat) ≤ 526 ∧ (526:Nat) < 1813)
  decide

theorem obEdge_label (divide : Bool) (l : Nat) (hl : l∈wires (obEndpoint divide)) :
    l=510 ∨ obLabel l := by
  have hw := obPorts_widths id 2409
  have hl' : l∈wires (transcriptSelectWindow 2400 510 2409
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (obHalf divide (obPorts id 2409))) := by
    simpa only [obEndpoint] using hl
  have m := ob_window_support 2400 510 2409 (mixedTranscriptUnitTrace.getD 510 (false,false)).1
    (obHalf divide (obPorts id 2409)) hl'
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with (e|e|e)|e
  · right
    subst e
    unfold obLabel fieldSite badIdx
    decide
  · left
    exact e
  · right
    subst e
    unfold obLabel fieldSite badIdx
    decide
  · right
    exact obPorts_label l (List.mem_toFinset.mp (obHalf_support divide _ hw e))

theorem obOK_endpoint (divide : Bool) : ObOK (renameProgram allPlaced (obEndpoint divide)) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hq
  rcases obEdge_label divide l hl with e|e
  · rw [e]
    exact ob_allPlaced_510
  · exact ob_allPlaced_site l e

theorem obConvFn_label (old : Nat)
    (mem : old∈(balancedSharedTargetConvert id).wires ∨ old∈(balancedSharedSourceConvert id).wires) :
    obLabel (obConvFn old) := by
  simp only [balancedSharedTargetConvert,balancedSharedSourceConvert,BalancedConvert.Layout.wires,
    wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
    or_false] at mem
  dsimp only [id] at mem
  unfold obLabel fieldSite badIdx obConvFn
  split_ifs <;> omega

theorem obConv_label (c : Bool) (l : Nat) (h : l∈wires (obConverterPair c)) : obLabel l := by
  rw [obConverterPair,renameProgram_support] at h
  obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp h
  have target := BalancedConvert.support (balancedSharedTargetConvert id)
  have source := BalancedConvert.support (balancedSharedSourceConvert id)
  have mem : old∈(balancedSharedTargetConvert id).wires ∨ old∈(balancedSharedSourceConvert id).wires := by
    cases c <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at hold
    · rcases hold with e|e
      · exact Or.inl (List.mem_toFinset.mp (target.1 e))
      · exact Or.inr (List.mem_toFinset.mp (source.1 e))
    · rcases hold with e|e
      · exact Or.inl (List.mem_toFinset.mp (target.2 e))
      · exact Or.inr (List.mem_toFinset.mp (source.2 e))
  exact obConvFn_label old mem

theorem obOK_copy : ObOK (renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)) := by
  have zword : (skywalkSharedField id).z=wireBlock id 2056 257 := skywalkShared_field_z id
  have aword : (skywalkSharedField id).a=wireBlock id 770 257 := rfl
  have cp := copyRegister_wires_subset none (skywalkSharedField id).z (skywalkSharedField id).a
  apply obOK_allPlaced
  intro l hl
  have member := cp hl
  rw [zword,aword] at member
  simp only [List.mem_toFinset,Option.toList_none,List.nil_append,wireBlock,List.map_id,
    List.mem_append,List.mem_range'_1] at member
  unfold obLabel fieldSite badIdx
  omega

end Support

theorem obFieldSegment_support (divide : Bool) :
    ∀ q ∈ wires (obFieldSegment divide), q ∈ slots.toFinset ∧ ¬ (1558 ≤ q ∧ q < 1813) ∧ goodW q := by
  have cp := obOK_copy
  have a := obOK_allPlaced _ (obConv_label false)
  have b := obOK_allPlaced _ (obConv_label true)
  have first := obOK_first divide
  have groups := obOK_groups divide 1 169 (by decide)
  have last := obOK_endpoint divide
  have whole : ObOK (obFieldSegment divide) := by
    cases divide <;> simp only [obFieldSegment,obReplay,Bool.false_eq_true,if_false,if_true,
      obOK_append]
    · exact ⟨⟨⟨⟨cp,a⟩,⟨⟨last,groups⟩,first⟩⟩,b⟩,obOK_nil⟩
    · exact ⟨⟨⟨⟨obOK_nil,a⟩,⟨⟨first,groups⟩,last⟩⟩,b⟩,cp⟩
  exact whole

end ECDSAAdd.Entrant

end

section
-- ===== OBField =====
/-! One-bank field, part 8: the one-bank field segment equals the current
selected field segment as a complete State, for every pair of record streams.

Each one-bank block agrees with the corresponding current block on every
state its predecessor (in the current segment) can produce; chaining these
block equalities gives the whole segment.  No payload algebra is repeated:
the current blocks' own encoded-frame contracts carry the invariant. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation CompressedFieldSupport Secp256k1 BalancedField
attribute [local irreducible] run compressedHistoryEncode compressedHistoryDecode allGroupEncode
  otherGroupEncode mixedTranscriptUnitTrace mixedTranscriptTape

theorem obEquiv_mono {I J : State → Prop} {P Q : Program} (h : ObEquiv J P Q)
    (sub : ∀ s,I s → J s) : ObEquiv I P Q :=
  fun s hs m n => h s (sub s hs) m n

/-- Canonical encoded frames with zero second word (the field input). -/
def ObCanon0 (origin : BasisState) (s : State) : Prop :=
  ∃ Y : Fp,EncodedCanonicalFrame origin Y 0 s

private theorem ob_copy_records :
    measurementCount (renameProgram allPlaced
      (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))=0 := by
  have len : (skywalkSharedField id).z.length=(skywalkSharedField id).a.length := by
    rw [skywalkShared_field_z]
    change (wireBlock id 2056 257).length=(wireBlock id 770 257).length
    simp [wireBlock]
  rw [(renameProgram_counts _ _).2]
  exact (copyRegister_counts none _ _ len).2

private theorem ob_center_post (origin : BasisState) (ctx : ObCtx origin) (cc : ObConvCtx origin)
    (s : State) (m : List Bool) (X Y : Fp) (h : EncodedCanonicalFrame origin X Y s) :
    EncodedFieldFrame base (base 2409) origin X Y
      (run (renameProgram allPlaced (converterPair false)) m s) := by
  rw [converterPair_placement false]
  exact (encoded_center_pair ctx.hn origin cc.hw cc.hu ctx.hr cc.hy X Y s m h).2

private theorem ob_groups_post (divide : Bool) (origin : BasisState) (ctx : ObCtx origin)
    (s : State) (m : List Bool) (h : ObEnc origin s) :
    ObEnc origin (run (mappedGroups divide 1 169) m s) := by
  obtain ⟨X,Y,input⟩ := h
  exact ⟨_,_,(mappedGroups_frame divide 1 169 (by decide) ctx.hn ctx.hlo ctx.ho ctx.hp
    (packet_layouts _ _ _ ctx.hf) origin ctx.hg0 ctx.hs0 ctx.env ctx.legal X Y s m input).2.2⟩

private def obCopy : Program :=
  renameProgram allPlaced (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)

theorem ob_forward_equiv (origin : BasisState) (ctx : ObCtx origin) (cc : ObConvCtx origin) :
    ObEquiv (ObCanon0 origin) (obFieldSegment true) (selectedFieldSegment true) := by
  have shapeNew : obFieldSegment true=renameProgram allPlaced (obConverterPair false)++
      (obFirstGroup true++(obMappedGroups true 1 169++(renameProgram allPlaced (obEndpoint true)++
      (renameProgram allPlaced (obConverterPair true)++obCopy)))) := by
    simp only [obFieldSegment,obReplay,obCopy,if_true,List.nil_append,List.append_assoc]
  have shapeOld : selectedFieldSegment true=renameProgram allPlaced (converterPair false)++
      (EntryMappedFieldSegmentTrim.firstGroup true++(mappedGroups true 1 169++
      (renameProgram allPlaced (PenultimateSwapIdentity.cell true)++
      (renameProgram allPlaced (converterPair true)++obCopy)))) := by
    simp only [selectedFieldSegment,PenultimateMapped.fieldSegment,PenultimateMapped.replay,obCopy,
      if_true,List.nil_append,List.append_assoc]
  rw [shapeNew,shapeOld]
  have center := obEquiv_mono (obCenter_equiv origin ctx cc)
    (fun s (h : ObCanon0 origin s) => by obtain ⟨Y,h⟩ := h; exact ⟨Y,0,h⟩)
  have postCenter : ∀ s m,ObCanon0 origin s →
      ObEnc0 origin (run (renameProgram allPlaced (converterPair false)) m s) := by
    rintro s m ⟨Y,h⟩
    exact ⟨Y,ob_center_post origin ctx cc s m Y 0 h⟩
  have first := obFirstGroup_forward_equiv origin ctx
  have postFirst : ∀ s m,ObEnc0 origin s →
      ObEnc origin (run (EntryMappedFieldSegmentTrim.firstGroup true) m s) :=
    fun s m h => firstGroup_post true origin ctx s m h
  have groups := obMappedGroups_equiv true origin ctx 1 169 (by decide)
  have postGroups := fun s m (h : ObEnc origin s) => ob_groups_post true origin ctx s m h
  have edge := obEndpoint_equiv true origin ctx
  have postEdge := fun s m (h : ObEnc origin s) => oldEndpoint_post true origin ctx s m h
  have canon := obCanonical_equiv origin ctx cc
  have postCanon : ∀ s m,ObEnc origin s →
      (fun _ => True) (run (renameProgram allPlaced (converterPair true)) m s) :=
    fun _ _ _ => trivial
  have copy := obEquiv_zero (fun _ => True) obCopy ob_copy_records
  exact obEquiv_append center postCenter (obEquiv_append first postFirst
    (obEquiv_append groups postGroups (obEquiv_append edge postEdge
      (obEquiv_append (J:=fun _ => True) canon postCanon copy))))

theorem ob_inverse_equiv (origin : BasisState) (ctx : ObCtx origin) (cc : ObConvCtx origin) :
    ObEquiv (ObCanon0 origin) (obFieldSegment false) (selectedFieldSegment false) := by
  have shapeNew : obFieldSegment false=obCopy++(renameProgram allPlaced (obConverterPair false)++
      (renameProgram allPlaced (obEndpoint false)++(obMappedGroups false 1 169++
      (obFirstGroup false++renameProgram allPlaced (obConverterPair true))))) := by
    simp only [obFieldSegment,obReplay,obCopy,Bool.false_eq_true,if_false,List.append_nil,
      List.append_assoc]
  have shapeOld : selectedFieldSegment false=obCopy++(renameProgram allPlaced (converterPair false)++
      (renameProgram allPlaced (PenultimateSwapIdentity.cell false)++(mappedGroups false 1 169++
      (EntryMappedFieldSegmentTrim.firstGroup false++renameProgram allPlaced (converterPair true))))) := by
    simp only [selectedFieldSegment,PenultimateMapped.fieldSegment,PenultimateMapped.replay,obCopy,
      Bool.false_eq_true,if_false,List.append_nil,List.append_assoc]
  rw [shapeNew,shapeOld]
  have copy := obEquiv_zero (ObCanon0 origin) obCopy ob_copy_records
  have postCopy : ∀ s m,ObCanon0 origin s → ObCanon origin (run obCopy m s) := by
    rintro s m ⟨Y,h⟩
    exact ⟨Y,Y,(mapped_copy_fill ctx.hn origin Y s m h).2⟩
  have center := obCenter_equiv origin ctx cc
  have postCenter : ∀ s m,ObCanon origin s →
      ObEnc origin (run (renameProgram allPlaced (converterPair false)) m s) := by
    rintro s m ⟨X,Y,h⟩
    exact ⟨X,Y,ob_center_post origin ctx cc s m X Y h⟩
  have edge := obEndpoint_equiv false origin ctx
  have postEdge := fun s m (h : ObEnc origin s) => oldEndpoint_post false origin ctx s m h
  have groups := obMappedGroups_equiv false origin ctx 1 169 (by decide)
  have postGroups := fun s m (h : ObEnc origin s) => ob_groups_post false origin ctx s m h
  have first := obFirstGroup_inverse_equiv origin ctx
  have postFirst : ∀ s m,ObEnc origin s →
      ObEnc origin (run (EntryMappedFieldSegmentTrim.firstGroup false) m s) :=
    fun s m h => firstGroup_post false origin ctx s m h
  have canon := obCanonical_equiv origin ctx cc
  exact obEquiv_append copy postCopy (obEquiv_append center postCenter
    (obEquiv_append edge postEdge (obEquiv_append groups postGroups
      (obEquiv_append first postFirst canon))))

/-- The one-bank field segment produces the identical complete State as the
current selected field segment, for every pair of record streams, under the
hypotheses of `selectedFieldSegment_spec`. -/
theorem obFieldSegment_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : OffsetBorrowedCanonical.Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m n : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    run (obFieldSegment divide) m s = run (selectedFieldSegment divide) n s := by
  have ctx : ObCtx origin := ⟨hn,hlo,ho,hp,hf,hg0,hs0,env,legal,hr⟩
  have cc : ObConvCtx origin := ⟨hw,hu,hy⟩
  cases divide
  · exact ob_inverse_equiv origin ctx cc s ⟨Y,input⟩ m n
  · exact ob_forward_equiv origin ctx cc s ⟨Y,input⟩ m n

end ECDSAAdd.Entrant

end

section
-- ===== OBKernel =====
/-! One-bank field, assembly: the Stage 2/5 kernel with the late signs in the
narrowed carry slots and the single-bank field segment.

`obKernel` runs the certified first tick, the forward ticks under the moving
placements `obSig k`, the certified terminal clear, the one-bank field segment
under the final placement `obSig 511`, the clear again, the reverse ticks and
the certified first-tick inverse.  On the certified caller domain every
intermediate State is the certified one read through the current placement, so
the certified strong port contract (`NativeFirstDirect.kernel_states`)
transfers unchanged. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 DirectSkywalk CompressedFieldSupport

def obKernel (divide : Bool) : Program :=
  NativeFirstDirect.forward base ++ obForward 1 511 ++ skywalkArithmeticClear base ++
  renameProgram (obSig 511) (obFieldSegment divide) ++ skywalkArithmeticClear base ++
  obReverse 1 511 ++ NativeFirstKnown.inverse base

def obControlled (divide : Bool) : Program :=
  directZeroControlled (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (obKernel divide)

/-! Placement transport. -/

theorem pullState_invol (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (t : State) :
    pullState f (pullState f t) = t := by
  apply State.extensionality
  · rfl
  · funext q
    simp only [pullState, hf]

theorem run_rename_invol (f : Wire → Wire) (hf : ∀ q, f (f q) = q) (P : Program)
    (m : List Bool) (s : State) :
    run (renameProgram f P) m (pullState f s) = pullState f (run P m s) := by
  have inj : Function.Injective f := fun a b h => by rw [← hf a, h, hf b]
  have h := run_rename f inj P m (pullState f s)
  rw [pullState_invol f hf] at h
  rw [← h, pullState_invol f hf]

theorem obSig_clear :
    renameProgram (obSig 511) (skywalkArithmeticClear base) = skywalkArithmeticClear base := by
  simp [skywalkArithmeticClear, skywalkTerminalClear, renameProgram, renameInstr, obSig, base]

/-! Strong port contract. -/

section Spec
attribute [local irreducible] run measurementCount NativeFirstDirect.forward NativeFirstKnown.inverse
  literalSkywalkSeed compressedCompactForward compressedCompactReverse selectedFieldSegment
  skywalkArithmeticClear obForward obReverse obFieldSegment allGroupEncode

private theorem obKernel_states (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (n1 n2 n3 n4 n5 n6 n7 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 s = n1)
    (h2 : run (obForward 1 511) m2 n1 = n2)
    (h3 : run (skywalkArithmeticClear base) m3 n2 = n3)
    (h4 : run (renameProgram (obSig 511) (obFieldSegment divide)) m4 n3 = n4)
    (h5 : run (skywalkArithmeticClear base) m5 n4 = n5)
    (h6 : run (obReverse 1 511) m6 n5 = n6)
    (h7 : run (NativeFirstKnown.inverse base) m7 n6 = n7) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s n7 := by
  obtain ⟨s2, hs2⟩ : ∃ t, run (compressedCompactForward base 1 511) m2 n1 = t := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ t, run (skywalkArithmeticClear base) m3 s2 = t := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ t, run (selectedFieldSegment divide) m4 s3 = t := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ t, run (skywalkArithmeticClear base) m5 s4 = t := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ t, run (compressedCompactReverse base 1 511) m6 s5 = t := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ t, run (NativeFirstKnown.inverse base) m7 s6 = t := ⟨_, rfl⟩
  have old := NativeFirstDirect.kernel_states divide hn hlo ho hf x Y hx0 hx s
    m1 m2 m3 m4 m5 m6 m7 hin hg0 hs0 n1 s2 s3 s4 s5 s6 s7 h1 hs2 hs3 hs4 hs5 hs6 hs7
  suffices same : n7 = s7 by rw [same]; exact old
  have inv : ∀ q, obSig 511 (obSig 511 q) = q := obSig_invol 511 (le_refl _)
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  rw [h1] at first
  have e2 : n2 = pullState (obSig 511) s2 := by
    rw [← h2, ← hs2]; exact obForward_run x hx0 hx n1 m2 first
  have e3 : n3 = pullState (obSig 511) s3 := by
    have t := run_rename_invol _ inv (skywalkArithmeticClear base) m3 s2
    rw [obSig_clear] at t
    rw [← h3, e2, ← hs3, t]
  -- the certified field-entry facts for `s3`
  have pool := skywalkShared_integer_nodup base hn
  have ready := NativeFirstDirect.caller_ready base hn x Y.val s.basis hin
  obtain ⟨oldSeed, seedEq, fullEq⟩ := NativeFirstDirect.forward_terminal_states base pool x hx
    s n1 s2 m1 m2 ready.1 ready.2 h1 hs2
  obtain ⟨origin, facts, _, _, entry⟩ := compressedPreparation_facts hn hlo ho x Y hx0 hx s
    [] (List.replicate 257 false ++ m2) m3 hin oldSeed s2 s3 seedEq fullEq hs3
  have selectorPool : ∀ q ∈ [base 2400,base 2409,base 2410], q ∉ skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409) = false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410) = false := (facts.controls _ (by simp)).trans hs0
  have fieldEq := obFieldSegment_eq divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    x hx0 hx facts.trace Y s3 m4 m4 entry
  have e4 : n4 = pullState (obSig 511) s4 := by
    rw [← h4, e3, run_rename_invol _ inv, fieldEq, hs4]
  have e5 : n5 = pullState (obSig 511) s5 := by
    have t := run_rename_invol _ inv (skywalkArithmeticClear base) m5 s4
    rw [obSig_clear] at t
    rw [← h5, e4, ← hs5, t]
  have keeps := selectedFieldSegment_pool_frame divide hn hlo ho selectorPool hf origin.basis hg hs
    facts.env facts.legal facts.workZero facts.unusedZero facts.targetHigh facts.sourceHigh
    facts.sourceZero x hx0 hx facts.trace Y s3 m4 entry
  rw [hs4] at keeps
  have recovered := clear_after_pool_update hn s2 s4 m3 m5
    (by rw [hs3]; exact keeps.1) (by intro q hq; rw [hs3]; exact keeps.2 q hq)
  rw [hs5] at recovered
  have e6 : n6 = s6 := by
    rw [← h6, e5, ← hs6]
    exact obReverse_run x hx0 hx n1 m2 first s5 (fun q hq => by rw [hs2]; exact recovered.2 q hq) m6
  rw [← h7, e6, hs7]

theorem obKernel_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (obKernel divide) m s) := by
  let P : State → State → Prop := fun initial out =>
    initial = s → DirectSkywalkArithmeticStrong divide base (base 2400) x Y s out
  have all := skywalkRunSeven (NativeFirstDirect.forward base) (obForward 1 511)
    (skywalkArithmeticClear base) (renameProgram (obSig 511) (obFieldSegment divide))
    (skywalkArithmeticClear base) (obReverse 1 511) (NativeFirstKnown.inverse base) P
    (by
      intro initial n1 n2 n3 n4 n5 n6 n7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 same
      subst same
      exact obKernel_states divide hn hlo ho hf x Y hx0 hx initial m1 m2 m3 m4 m5 m6 m7
        hin hg0 hs0 n1 n2 n3 n4 n5 n6 n7 h1 h2 h3 h4 h5 h6 h7) s m
  simpa only [obKernel, List.append_assoc] using all rfl

end Spec

/-! Zero-divisor wrapper. -/

section Controlled
attribute [local irreducible] run measurementCount obKernel
  directZeroDivisorEnter directZeroDivisorLeave

private theorem ob_port_nodup :
    (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255++
      wireBlock base 2056 256)).Nodup := by
  have first : (List.range' 770 256++List.range' 0 255).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hx hc
    simp only [List.mem_range'_1] at hx hc
    omega
  have words : (List.range' 770 256++List.range' 0 255++List.range' 2056 256).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨first,List.nodup_range',List.disjoint_left.mpr ?_⟩
    intro q hxy hz
    simp only [List.mem_append,List.mem_range'_1] at hxy hz
    omega
  have ids : (2411::2313::(List.range' 770 256++List.range' 0 255++List.range' 2056 256)).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
    · apply List.nodup_cons.mpr
      constructor
      · simp only [List.mem_append,List.mem_range'_1]
        omega
      · exact words
  change ((2411::2313::(List.range' 770 256++List.range' 0 255++
    List.range' 2056 256)).map base).Nodup
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact ids

private theorem ob_flag_outside : base 2411 ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hi
  have same := base_injective eq
  omega

/-- The certified strong port contract of `MappedCompressed.controlled`, for
the one-bank stage. -/
theorem obControlled_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (zeroBranch : x = 0 → s.basis (base 2400) = false)
    (hflag : s.basis (base 2411) = false)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (obControlled divide) m s) := by
  let D := directDivisor x
  let R := (directSkywalkResult divide (s.basis (base 2400)) x Y).val
  have positive : 0 < D := Nat.pos_of_ne_zero (directDivisor_ne_zero x)
  have bound : D < p := by
    by_cases zero : x = 0
    · simp only [D,directDivisor,zero,if_true]
      norm_num [p]
    · simpa only [D,directDivisor,zero,if_false] using hx
  have sameResult : directSkywalkResult divide (s.basis (base 2400)) D Y =
      directSkywalkResult divide (s.basis (base 2400)) x Y := by
    by_cases zero : x = 0
    · simp only [directSkywalkResult,zeroBranch zero,Bool.false_eq_true,if_false]
    · simp only [D,directDivisor,zero,if_false]
  have cin : s.basis (base 2313) = false :=
    arith_input_bit base hn x Y.val s.basis hin 2313 (by omega) (by omega) (by omega)
  have carry : ∀ q ∈ wireBlock base 0 255,s.basis q = false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact arith_input_bit base hn x Y.val s.basis hin i (by omega) (by omega) (by omega)
  have callback : ∀ (t : State) (ms : List Bool),
      regValue (wireBlock base 770 256) t.basis = directDivisor (regValue (wireBlock base 770 256) s.basis) →
      regValue (wireBlock base 2056 256) t.basis = regValue (wireBlock base 2056 256) s.basis →
      t.basis (base 2411) = decide (regValue (wireBlock base 770 256) s.basis = 0) →
      (∀ q,q ≠ base 2411 → q ∉ wireBlock base 770 256 → t.basis q = s.basis q) →
      (run (obKernel divide) ms t).phase = t.phase ∧
      regValue (wireBlock base 2056 256) (run (obKernel divide) ms t).basis = R ∧
      ∀ q,q ∉ wireBlock base 2056 256 → (run (obKernel divide) ms t).basis q = t.basis q := by
    intro t ms divisor numerator _ frame
    have input : SkywalkArithmeticInput base D Y.val t.basis := by
      refine ⟨divisor.trans (congrArg directDivisor hin.1),numerator.trans hin.2.1,?_⟩
      intro q hq hdx hdy
      have ne : q ≠ base 2411 := fun eq => ob_flag_outside (eq ▸ hq)
      exact (frame q ne hdx).trans (hin.2.2 q hq hdx hdy)
    have controls (q : Wire) (hq : q ∈ [base 2400,base 2409,base 2410]) :
        t.basis q = s.basis q := by
      have ne : q ≠ base 2411 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl
        all_goals intro eq; have same := base_injective eq; omega
      have away : q ∉ wireBlock base 770 256 :=
        fun bad => ho q hq (arith_block_subset_shared base 770 256 (by omega) bad)
      exact frame q ne away
    have strong := obKernel_spec divide hn hlo ho hf D Y positive bound t ms input
      ((controls _ (by simp)).trans hg0) ((controls _ (by simp)).trans hs0)
    unfold DirectSkywalkArithmeticStrong at strong
    rw [controls (base 2400) (by simp),sameResult] at strong
    exact strong
  have width : (wireBlock base 0 255).length+1 = (wireBlock base 770 256).length := by
    simp only [wireBlock_length]
  have records := directZeroControlled_states (wireBlock base 770 256) (wireBlock base 2056 256)
    (wireBlock base 0 255) (base 2313) (base 2411) ob_port_nodup width (obKernel divide) s
    (m.take (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411))))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).take (measurementCount (obKernel divide)))
    ((m.drop (measurementCount (directZeroDivisorEnter (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411)))).drop (measurementCount (obKernel divide)))
    R cin hflag carry callback
  simpa only [DirectSkywalkArithmeticStrong,obControlled,directZeroControlled,run_append,
    skywalkArithmeticNumerator,R] using records

end Controlled

/-! Support: every wire is a certified slot, avoids the labels unused by the
certified arithmetic, and avoids the removed range `base [1285,1540)`. -/

def obGood (q : Wire) : Prop := q ∈ slots.toFinset ∧ ¬ obRemoved q ∧ goodW q

section Support
attribute [local irreducible] obForward obReverse obFieldSegment NativeFirstDirect.forward
  NativeFirstKnown.inverse kernel controlled obKernel directZeroDivisorEnter directZeroDivisorLeave

theorem obRemoved_base (i : Nat) (h : i < 1285 ∨ 1540 ≤ i) : ¬ obRemoved (base i) := by
  show ¬ (1301 ≤ i + 16 ∧ i + 16 < 1556); omega

private theorem prefix_good (q : Wire) (hq : q ∈ (NativeFirstDirect.prefixSites base).toFinset) :
    ¬ obRemoved q := by
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((⟨i,hi,rfl⟩|⟨i,hi,rfl⟩)|⟨i,hi,rfl⟩)|(rfl|rfl)
  all_goals exact obRemoved_base _ (by omega)

private theorem old_kernel_good (divide : Bool) (q : Wire) (hq : q ∈ wires (kernel divide)) :
    q ∈ slots.toFinset ∧ goodW q :=
  ⟨kernel_support divide hq, kernel_avoid divide q hq⟩

private theorem field_good (divide : Bool) (q : Wire)
    (hq : q ∈ wires (renameProgram (obSig 511) (obFieldSegment divide))) : obGood q := by
  rw [renameProgram_support] at hq
  obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨slot,late,good⟩ := obFieldSegment_support divide old hold
  unfold obGood obRemoved
  by_cases range : 1301 ≤ old ∧ old ≤ 1555
  · have image : obSig 511 old = base (3097-old) := by
      simp only [obSig, base]; rw [if_pos (Or.inl ⟨range.1,by unfold Wire at *; omega⟩)]
      unfold Wire at *; omega
    rw [image]
    refine ⟨?_,?_,?_⟩
    · apply slot_mem (3097-old)
      · unfold live; unfold Wire at *; omega
      · unfold CompressedAllocation.omitted; unfold Wire at *; omega
    · show ¬ (1301 ≤ 3097-old+16 ∧ 3097-old+16 < 1556); unfold Wire at *; omega
    · show ¬ (3097-old+16 = 769 + 16 ∨ 3097-old+16 = 2313 + 16 ∨
        (2401 + 16 ≤ 3097-old+16 ∧ 3097-old+16 ≤ 2408 + 16)); unfold Wire at *; omega
  · have image : obSig 511 old = old := by
      simp only [obSig]; rw [if_neg (by unfold Wire at *; omega)]
    rw [image]
    exact ⟨slot,by unfold Wire at *; omega,good⟩

theorem obKernel_support (divide : Bool) : ∀ q ∈ wires (obKernel divide), obGood q := by
  have sub (P : Program) (hP : ∀ q ∈ wires P, q ∈ wires (kernel divide))
      (hr : ∀ q ∈ wires P, ¬ obRemoved q) : ∀ q ∈ wires P, obGood q := fun q hq =>
    ⟨(old_kernel_good divide q (hP q hq)).1, hr q hq, (old_kernel_good divide q (hP q hq)).2⟩
  have kw : wires (kernel divide) = wires (NativeFirstDirect.forward base) ∪
      wires (compressedCompactForward base 1 511) ∪ wires (skywalkArithmeticClear base) ∪
      wires (selectedFieldSegment divide) ∪ wires (skywalkArithmeticClear base) ∪
      wires (compressedCompactReverse base 1 511) ∪ wires (NativeFirstKnown.inverse base) := by
    simp only [kernel,wires_append]
  have first := sub (NativeFirstDirect.forward base)
    (fun q hq => by
      rw [kw]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hq))))))
    (fun q hq => prefix_good q ((NativeFirstDirect.prefix_support base).1 hq))
  have last := sub (NativeFirstKnown.inverse base)
    (fun q hq => by rw [kw]; exact Finset.mem_union_right _ hq)
    (fun q hq => prefix_good q (NativeFirstKnown.inverse_support base hq))
  have clear := sub (skywalkArithmeticClear base)
    (fun q hq => by
      rw [kw]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ hq)))))
    (by
      intro q hq
      rw [skywalkArithmeticClear,skywalkTerminalClear_wires] at hq
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl
      all_goals exact obRemoved_base _ (by omega))
  intro q hq
  rw [obKernel,wires_append,wires_append,wires_append,wires_append,wires_append,wires_append] at hq
  rcases Finset.mem_union.mp hq with hq|h
  · rcases Finset.mem_union.mp hq with hq|h
    · rcases Finset.mem_union.mp hq with hq|h
      · rcases Finset.mem_union.mp hq with hq|h
        · rcases Finset.mem_union.mp hq with hq|h
          · rcases Finset.mem_union.mp hq with h|h
            · exact first q h
            · exact obForward_support q h
          · exact clear q h
        · exact field_good divide q h
      · exact clear q h
    · exact obReverse_support q h
  · exact last q h

theorem obControlled_support (divide : Bool) : ∀ q ∈ wires (obControlled divide), obGood q := by
  have wrap (q : Wire) (hq : q ∈ wires (directZeroDivisorEnter (wireBlock base 770 256)
      (wireBlock base 0 255) (base 2313) (base 2411)) ∪ wires (directZeroDivisorLeave
      (wireBlock base 770 256) (wireBlock base 0 255) (base 2313) (base 2411))) : obGood q := by
    have inOld : q ∈ wires (controlled divide) := by
      rw [controlled, directZeroControlled, wires_append, wires_append]
      rcases Finset.mem_union.mp hq with h|h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
    have sites := directZeroDivisor_wires (wireBlock base 770 256) (wireBlock base 0 255)
      (base 2313) (base 2411) (by rw [wires_append]; exact hq)
    refine ⟨controlled_support divide inOld,?_,controlled_avoid divide q inOld⟩
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,wireBlock,List.mem_map,
      List.mem_range'_1] at sites
    rcases sites with rfl|rfl|(⟨i,hi,rfl⟩|⟨i,hi,rfl⟩)
    all_goals exact obRemoved_base _ (by omega)
  intro q hq
  rw [obControlled, directZeroControlled, wires_append, wires_append] at hq
  rcases Finset.mem_union.mp hq with h|h
  · exact wrap q (Finset.mem_union_left _ h)
  · rcases Finset.mem_union.mp h with h|h
    · exact obKernel_support divide q h
    · exact wrap q (Finset.mem_union_right _ h)

end Support

/-! Resources. -/

theorem obKernel_counts (divide : Bool) :
    toffoliCount (obKernel divide) + toffoliCount (selectedFieldSegment divide) =
      toffoliCount (kernel divide) + toffoliCount (obFieldSegment divide) ∧
    measurementCount (obKernel divide) + measurementCount (selectedFieldSegment divide) =
      measurementCount (kernel divide) + measurementCount (obFieldSegment divide) := by
  have f := obForward_counts
  have r := obReverse_counts
  have field := renameProgram_counts (obSig 511) (obFieldSegment divide)
  simp only [obKernel,kernel,toffoliCount_append,measurementCount_append,f.1,f.2.1,r.1,r.2.1,
    field.1,field.2]
  constructor <;> omega

theorem obControlled_counts (divide : Bool) :
    toffoliCount (obControlled divide) + toffoliCount (selectedFieldSegment divide) =
      toffoliCount (controlled divide) + toffoliCount (obFieldSegment divide) ∧
    measurementCount (obControlled divide) + measurementCount (selectedFieldSegment divide) =
      measurementCount (controlled divide) + measurementCount (obFieldSegment divide) := by
  have width : (wireBlock base 0 255).length+1=(wireBlock base 770 256).length := by
    simp [wireBlock]
  have fresh := directZeroControlled_counts (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (obKernel divide) width
  have old := directZeroControlled_counts (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (kernel divide) width
  have core := obKernel_counts divide
  simp only [obControlled,controlled] at ⊢
  rw [fresh.1,fresh.2,old.1,old.2]
  constructor <;> omega

theorem obControlled_gateSlots (divide : Bool) :
    Challenge.gateSlots (obControlled divide) ≤ 20600000 - 14100000 + 13400000 := by
  have hn := Baselines.nativeFirst_gateSlots_le base
  have hi := Baselines.compactLoops_gateSlots_le base 1 511 (by omega)
  have hf := obFieldSegment_gateSlots divide
  have f := obForward_counts
  have r := obReverse_counts
  have hz := Baselines.zeroCompare_gateSlots_le (wireBlock base 770 256)
    (wireBlock base 0 255) (base 2313) (base 2411)
  have hm := Baselines.maskedConstant_gateSlots_le (base 2411) (wireBlock base 770 256) 1
  have hc : Challenge.gateSlots (skywalkArithmeticClear base) = 3 := rfl
  simp only [wireBlock_length] at hz hm
  simp only [obControlled,obKernel,directZeroControlled,directZeroDivisorEnter,directZeroDivisorLeave,
    Challenge.gateSlots_append,Baselines.rename_gateSlots,hc,f.2.2,r.2.2]
  omega

theorem obKernel_physical (divide : Bool) : GatePhysical (obKernel divide) := by
  have first := (NativeFirstDirect.programs_physical base base_pool_nodup).1
  have last := NativeFirstKnown.inverse_physical base base_pool_nodup
  have field := gatePhysical_rename (obSig 511) (obSig_injective 511 (le_refl _)) _
    (obFieldSegment_physical divide)
  simp only [obKernel,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨first,obForward_physical⟩,mappedClear_physical⟩,field⟩,mappedClear_physical⟩,
    obReverse_physical⟩,last⟩

theorem obControlled_physical (divide : Bool) : GatePhysical (obControlled divide) := by
  apply directZero_physical _ _ _ _ _ _ (obKernel_physical divide)
  decide +kernel

end ECDSAAdd.Entrant

end

section
-- ===== Arith2 =====
/-! The Skywalk arithmetic placement with two logical labels exchanged.

Label `769` is never touched by the arithmetic (`controlled_avoid`); its pool
site is, however, needed by the square stage.  Exchanging labels `769` and
`1797` before placement makes the arithmetic use that already-needed site for
label `1797`, and leaves the site previously behind `1797` idle.  The placement
facts used by the correctness transfer are unchanged by the exchange. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation Secp256k1 ControlledPointLayout DirectSkywalk
attribute [local irreducible] run controlled toffoliCount measurementCount
  mixedTranscriptUnitTrace SkywalkTrace.next Nat.iterate

/-- Exchange of the wires `base 769` and `base 1797`. -/
def swap2 (q : Wire) : Wire :=
  if q = base 769 then base 1797 else if q = base 1797 then base 769 else q

def wireFn2 (L : ControlledPointLayout) (q : Wire) : Wire := pointWireFn L (swap2 q)

theorem swap2_involutive (q : Wire) : swap2 (swap2 q) = q := by
  have hb : base 769 ≠ base 1797 := by decide
  unfold swap2
  by_cases h1 : q = base 769
  · subst h1; simp [hb, hb.symm]
  · by_cases h2 : q = base 1797
    · subst h2; simp [hb, hb.symm]
    · simp [h1, h2]

theorem m769 : base 769 ∈ slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem m1797 : base 1797 ∈ slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem swap2_slots (q : Wire) (h : q ∈ slots.toFinset) : swap2 q ∈ slots.toFinset := by
  have a := m769
  have b := m1797
  unfold swap2; split_ifs <;> assumption

theorem swap2_fix (q : Wire) (h1 : q ≠ base 769) (h2 : q ≠ base 1797) : swap2 q = q := by
  simp [swap2, h1, h2]

private theorem logical_shared_nodup2 : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

private theorem logical_scalar_outside2 (i : Nat) (hi : 2314 ≤ i) :
    base i ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hj
  have same := base_injective eq
  omega

private theorem logical_selectors_outside2 :
    ∀ q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base := by
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact logical_scalar_outside2 _ (by omega)

private theorem logical_mixed_layout2 :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base) := by
  have scalar : [base 2400,base 2409,base 2410].Nodup := by simp [base]
  have disjoint : [base 2400,base 2409,base 2410].Disjoint (skywalkSharedWires base) :=
    List.disjoint_left.mpr (fun q hq => logical_selectors_outside2 q hq)
  have hall := List.nodup_append'.mpr ⟨scalar,logical_shared_nodup2,disjoint⟩
  have unused : skywalkSharedUnused base⊆skywalkSharedWires base := by
    intro q hq
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals exact arith_mem base 0 2314 _ (by omega) (by omega)
  apply mixedTranscriptTape_layout
  intro r hr
  have pair := (List.nodup_cons.mp (skywalkShared_tape_layout base logical_shared_nodup2
    (base 2400) (logical_selectors_outside2 _ (by simp)) r hr)).2
  have sub : (r.2::r.1::(skywalkSharedField base).wires)⊆skywalkSharedWires base := by
    intro q hq
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).2
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).1
    · exact retained_field_subset_shared base hq
  constructor
  · exact logical_shared_nodup2
  · apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hall q
    have hp := List.nodup_iff_count.mp pair q
    have hle : (r.2::r.1::(skywalkSharedField base).wires).count q≤
        (skywalkSharedWires base).count q := by
      by_cases hm : q∈r.2::r.1::(skywalkSharedField base).wires
      · have positive := List.count_pos_iff.mpr (sub hm); omega
      · rw [List.count_eq_zero.mpr hm]; omega
    simp only [List.count_append,List.count_cons,List.count_nil] at hh hp hle ⊢
    omega
  · exact fun h => logical_selectors_outside2 _ (by simp) (fusedSharedSites_subset base h)
  · exact fun h => logical_selectors_outside2 _ (by simp) (unused h)
  · exact fun h => logical_selectors_outside2 _ (by simp) (unused h)

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem placement2 : PointArithmeticPlacement L (wireFn2 L) := by
  have base' := pointPlacement L hw hn
  rcases base' with ⟨inj, dmap, nmap, cmap, swork, sg, ss, sz⟩
  have blockfix (a n : Nat) (h : 1797 < a ∨ a + n ≤ 769 ∨ (769 < a ∧ a + n ≤ 1797)) :
      (wireBlock base a n).map (wireFn2 L) = (wireBlock base a n).map (pointWireFn L) := by
    apply List.map_congr_left
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [wireFn2]
    rw [swap2_fix (base i) (fun h => by have h' : i + 16 = 769 + 16 := h; omega)
      (fun h => by have h' : i + 16 = 1797 + 16 := h; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb e
    have := inj _ (swap2_slots a ha) _ (swap2_slots b hb) e
    rw [← swap2_involutive a, this, swap2_involutive]
  · rw [blockfix 770 256 (by omega)]; exact dmap
  · rw [blockfix 2056 256 (by omega)]; exact nmap
  · simp only [wireFn2]; rw [swap2_fix (base 2400) (by decide) (by decide)]; exact cmap
  · intro q hq hs hx hy
    simp only [wireFn2]
    by_cases h1 : q = base 769
    · subst h1
      rw [show swap2 (base 769) = base 1797 by simp [swap2]]
      apply swork
      · exact List.mem_map.mpr ⟨1797, by simp [List.mem_range'_1], rfl⟩
      · exact m1797
      · intro h; obtain ⟨i, hi, he⟩ := List.mem_map.mp h; simp only [List.mem_range'_1] at hi
        have he' : i + 16 = _ := he; simp only [base] at he'; omega
      · intro h; obtain ⟨i, hi, he⟩ := List.mem_map.mp h; simp only [List.mem_range'_1] at hi
        have he' : i + 16 = _ := he; simp only [base] at he'; omega
    · by_cases h2 : q = base 1797
      · subst h2
        rw [show swap2 (base 1797) = base 769 by simp only [swap2, base]; simp]
        apply swork
        · exact List.mem_map.mpr ⟨769, by simp [List.mem_range'_1], rfl⟩
        · exact m769
        · intro h; obtain ⟨i, hi, he⟩ := List.mem_map.mp h; simp only [List.mem_range'_1] at hi
          have he' : i + 16 = _ := he; simp only [base] at he'; omega
        · intro h; obtain ⟨i, hi, he⟩ := List.mem_map.mp h; simp only [List.mem_range'_1] at hi
          have he' : i + 16 = _ := he; simp only [base] at he'; omega
      · rw [swap2_fix _ h1 h2]; exact swork q hq hs hx hy
  · simp only [wireFn2]; rw [swap2_fix (base 2409) (by decide) (by decide)]; exact sg
  · simp only [wireFn2]; rw [swap2_fix (base 2410) (by decide) (by decide)]; exact ss
  · simp only [wireFn2]; rw [swap2_fix (base 2411) (by decide) (by decide)]; exact sz

end

end ECDSAAdd.Entrant

end

section
-- ===== OBArith =====
/-! One-bank field, placement: the one-bank Stage 2/5 arithmetic under the
`wireFn2` placement of `Arith2.lean`.  Correctness is the certified point
transfer (`MappedCompressedPointTransfer.lean`), applied to `obControlled`
over the same slot domain.  Every gate is the placement of a slot label that
is not avoided by `ArithAvoid.lean` and not in `base [1285,1540)`, so the
pool sites `poolWire [1029,1284)` behind those labels are idle. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation Secp256k1 ControlledPointLayout DirectSkywalk
attribute [local irreducible] run obControlled toffoliCount measurementCount
  mixedTranscriptUnitTrace SkywalkTrace.next Nat.iterate

def obArith (L : ControlledPointLayout) (multiply : Bool) : Program :=
  renameProgram (wireFn2 L) (obControlled (!multiply))

section Transfer

private def obInput (domain : Finset Wire) (f : Wire → Wire) (s : State) : State :=
  ⟨s.phase,fun q => if q∈domain then s.basis (f q) else false⟩

private theorem ob_divisor_sites : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))
private theorem ob_numerator_sites : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
private theorem ob_control_site : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

private theorem ob_reg_map_agree (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- `MappedCompressed.pointTransfer_core`, verbatim. -/
private theorem ob_transfer_core (L : ControlledPointLayout) (f : Wire → Wire)
    (domain : Finset Wire) (divide : Bool)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (zeroFlag : f (base 2411)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (bSite : base 2400∈domain)
    (X : Nat) (Y : Fp) (B : Bool) (hx0 : B=true → X≠0)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (P : Program) (programSites : wires P⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      (X=0 → t.basis (base 2400)=false) →
      t.basis (base 2411)=false → t.basis (base 2409)=false → t.basis (base 2410)=false →
      DirectSkywalkArithmeticStrong divide base (base 2400) X Y t (run P records t)) :
    let out := run (renameProgram f P) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=(directSkywalkResult divide B X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let t := obInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,obInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [ob_reg_map_agree f _ t.basis s.basis (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [ob_reg_map_agree f _ t.basis s.basis (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,obInput,if_neg used]
  have control : t.basis (base 2400)=B := by
    rw [inputBits _ bSite,controlMap,hb]
  have zeroBranch : X=0 → t.basis (base 2400)=false := by
    intro eq
    rw [control]
    cases B
    · rfl
    · exact False.elim ((hx0 rfl) eq)
  have strong := P_spec t m input zeroBranch
    (zero _ zeroFlag) (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective
    P programSites m t s rfl inputBits
  unfold DirectSkywalkArithmeticStrong at strong
  rw [control] at strong
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (ob_reg_map_agree f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q outside
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      have away : a∉skywalkArithmeticNumerator base := by
        intro mem
        apply outside
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨a,mem,rfl⟩
      exact (transfer.2 a ha).trans ((strong.2.2 a away).trans (inputBits a ha))
    · exact run_rename_pool_outside f domain P
        programSites m s q image

private theorem ob_shared_nodup : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

private theorem ob_scalar_outside (i : Nat) (hi : 2314 ≤ i) :
    base i ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hj
  have same := base_injective eq
  omega

private theorem ob_selectors_outside :
    ∀ q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base := by
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact ob_scalar_outside _ (by omega)

private theorem ob_mixed_layout :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base) := by
  have scalar : [base 2400,base 2409,base 2410].Nodup := by simp [base]
  have disjoint : [base 2400,base 2409,base 2410].Disjoint (skywalkSharedWires base) :=
    List.disjoint_left.mpr (fun q hq => ob_selectors_outside q hq)
  have hall := List.nodup_append'.mpr ⟨scalar,ob_shared_nodup,disjoint⟩
  have unused : skywalkSharedUnused base⊆skywalkSharedWires base := by
    intro q hq
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals exact arith_mem base 0 2314 _ (by omega) (by omega)
  apply mixedTranscriptTape_layout
  intro r hr
  have pair := (List.nodup_cons.mp (skywalkShared_tape_layout base ob_shared_nodup
    (base 2400) (ob_selectors_outside _ (by simp)) r hr)).2
  have sub : (r.2::r.1::(skywalkSharedField base).wires)⊆skywalkSharedWires base := by
    intro q hq
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).2
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).1
    · exact retained_field_subset_shared base hq
  constructor
  · exact ob_shared_nodup
  · apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hall q
    have hp := List.nodup_iff_count.mp pair q
    have hle : (r.2::r.1::(skywalkSharedField base).wires).count q≤
        (skywalkSharedWires base).count q := by
      by_cases hm : q∈r.2::r.1::(skywalkSharedField base).wires
      · have positive := List.count_pos_iff.mpr (sub hm); omega
      · rw [List.count_eq_zero.mpr hm]; omega
    simp only [List.count_append,List.count_cons,List.count_nil] at hh hp hle ⊢
    omega
  · exact fun h => ob_selectors_outside _ (by simp) (fusedSharedSites_subset base h)
  · exact fun h => ob_selectors_outside _ (by simp) (unused h)
  · exact fun h => ob_selectors_outside _ (by simp) (unused h)

theorem obArith_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (obArith L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (obArith L multiply) m s).basis=V ∧
    ∀ q,q∉L.point.y → (run (obArith L multiply) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨inj, dmap, nmap, cmap, swork, sg, ss, sz⟩
  have result := ob_transfer_core L (wireFn2 L) slots.toFinset (!multiply) inj dmap nmap cmap
    swork sg ss sz ob_divisor_sites ob_numerator_sites ob_control_site
    X (Y:Fp) B hX0 s m hb hx (hy.trans yValue.symm) hc (obControlled (!multiply))
    (fun q hq => (obControlled_support (!multiply) q hq).1)
    (fun t records input zeroBranch hflag hg hs =>
      obControlled_spec (!multiply) ob_shared_nodup base_above ob_selectors_outside ob_mixed_layout
        X (Y:Fp) hX t records input zeroBranch hflag hg hs)
  cases B <;> cases multiply <;>
    simpa only [obArith,directSkywalkResult,skywalkArithmeticResult,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,yValue] using result

end Transfer

theorem obArith_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (multiply : Bool) : GatePhysical (obArith L multiply) := by
  apply gatePhysical_rename_support (wireFn2 L) (obControlled (!multiply))
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (obControlled_support (!multiply) a ha).1 b
      (obControlled_support (!multiply) b hb).1 eq
  · exact obControlled_physical _

/-- Every arithmetic gate is the placement of a good label. -/
theorem obArith_wire (L : ControlledPointLayout) (multiply : Bool) (q : Wire)
    (hq : q ∈ wires (obArith L multiply)) :
    ∃ old, obGood old ∧ q = pointWireFn L (swap2 old) := by
  rw [obArith, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨old, obControlled_support (!multiply) old used, rfl⟩

/-- The labels behind the idle pool sites. -/
theorem pointWireFn_late (L : ControlledPointLayout) (k : Nat) (h1 : 1026 ≤ k) (h2 : k < 1798) :
    pointWireFn L (base k) = L.core.poolWire (k-256) := by
  rw [pointWireFn_base]
  simp only [pointIndexWire, show k < 2314 by omega, if_true, skywalkDirectMap, skywalkPointWire,
    show ¬ (770 ≤ k ∧ k < 1026) by omega, show ¬ (2056 ≤ k ∧ k < 2312) by omega, if_false,
    show 1026 ≤ k from h1, show ¬ 2312 ≤ k by omega, if_true, Nat.sub_zero]

/-- No arithmetic gate touches the pool sites behind `base [1285,1540)`. -/
theorem obArith_idle (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (multiply : Bool) (j : Nat) (hj : 1029 ≤ j ∧ j < 1284) :
    L.core.poolWire j ∉ wires (obArith L multiply) := by
  intro hq
  obtain ⟨old, ⟨slot, removed, _⟩, eq⟩ := obArith_wire L multiply _ hq
  have label : base (j+256) ∈ slots.toFinset := by
    apply slot_mem
    · unfold live; omega
    · unfold CompressedAllocation.omitted; omega
  have image : pointWireFn L (base (j+256)) = L.core.poolWire j := by
    rw [pointWireFn_late L (j+256) (by omega) (by omega), Nat.add_sub_cancel]
  have same := pointWireFn_injective_slots L hw hn _ (swap2_slots old slot) _ label
    (eq.symm.trans image.symm)
  unfold swap2 at same
  split_ifs at same with h1 h2
  · have e : (1797:Nat) + 16 = j + 256 + 16 := same
    omega
  · have e : (769:Nat) + 16 = j + 256 + 16 := same
    omega
  · apply removed
    rw [same]
    show 1301 ≤ j+256+16 ∧ j+256+16 < 1556
    omega

theorem obArith_counts (L : ControlledPointLayout) :
    toffoliCount (obArith L false)=1183800 ∧ measurementCount (obArith L false)=854076 ∧
    toffoliCount (obArith L true)=1183800 ∧ measurementCount (obArith L true)=854076 := by
  have c1 := obControlled_counts true
  have c2 := obControlled_counts false
  have o1 := controlled_counts true
  have o2 := controlled_counts false
  have f1 := selectedFieldSegment_counts true
  have f2 := selectedFieldSegment_counts false
  have n := obFieldSegment_counts
  have r1 := renameProgram_counts (wireFn2 L) (obControlled true)
  have r2 := renameProgram_counts (wireFn2 L) (obControlled false)
  simp only [if_true, Bool.false_eq_true, if_false] at o1 o2 f1 f2
  simp only [obArith, Bool.not_false, Bool.not_true]
  omega

theorem obArith_gateSlots (L : ControlledPointLayout) (multiply : Bool) :
    Challenge.gateSlots (obArith L multiply) ≤ 20600000 - 14100000 + 13400000 := by
  simpa only [obArith, Baselines.rename_gateSlots] using obControlled_gateSlots (!multiply)

def obBackend : PointArithmeticBackend where
  program := obArith
  correct := obArith_correct
  support L hw hn multiply := by
    intro q hq
    obtain ⟨old, ⟨hs, _, _⟩, rfl⟩ := obArith_wire L multiply q hq
    have := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, swap2_slots old hs, rfl⟩)
    exact List.mem_toFinset.mpr (PointArithmeticBackend.shared_subset L hw (List.mem_toFinset.mp this))

end ECDSAAdd.Entrant

end

section
-- ===== EKSupport =====
/-! Support, frame, resources and validity of `finiteProgramE`.

The program lives in `sitesE`: the point, the control, the five classification
flags still in use, and the certified pool inventory without site 1801. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

def flagsE (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.genericSelect, L.core.generic, L.core.equalNegY]

/-- The certified pool inventory without sites 1541, 1801 and the sites
`[1029,1284)` that the one-bank arithmetic leaves idle. -/
def sharedPoolF (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515 ++
    (wireBlock L.core.poolWire 684 345 ++ wireBlock L.core.poolWire 1284 257) ++
    [L.core.poolWire 1800] ++ wireBlock L.core.poolWire 1802 3

def sitesE (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsE L ++ sharedPoolF L

theorem sitesE_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesE L).length = 1639 := by
  simp [sitesE, flagsE, sharedPoolF, PointAddLayout.pointWires, wireBlock_length,
    show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]

section Support
attribute [local irreducible] wires shortEqual pairEqual controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

theorem point_E (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesE L := by
  simp [sitesE, hq]

theorem control_E : L.control ∈ sitesE L := by simp [sitesE]

theorem flag_E (t : Wire) (ht : t ∈ flagsE L) : t ∈ sitesE L := by
  simp only [sitesE, List.mem_append]; exact Or.inl (Or.inr ht)

theorem x_E (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesE L :=
  point_E L q (by simp [PointAddLayout.pointWires, hq])
theorem y_E (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesE L :=
  point_E L q (by simp [PointAddLayout.pointWires, hq])
theorem generic_E : L.core.generic ∈ sitesE L := flag_E L _ (by simp [flagsE])

theorem poolQ_E (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ sitesE L := by
  simp only [sitesE, List.mem_append]; exact Or.inr hq

theorem sharedPool_F (q : Wire) (hq : q ∈ CompressedPointSquare.sharedPool L)
    (hne : q ≠ L.core.poolWire 1801) (hne' : q ≠ L.core.poolWire 1541)
    (hidle : ∀ j, 1029 ≤ j → j < 1284 → q ≠ L.core.poolWire j) : q ∈ sharedPoolF L := by
  simp only [CompressedPointSquare.sharedPool, sharedPoolF, List.mem_append] at hq ⊢
  rcases hq with (h1 | h1) | h1
  · exact Or.inl (Or.inl (Or.inl h1))
  · simp only [wireBlock, List.mem_map, List.mem_range'_1] at h1 ⊢
    obtain ⟨i, hi, rfl⟩ := h1
    have : i ≠ 1541 := fun e => hne' (by rw [e])
    by_cases low : i < 1029
    · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨i, by omega, rfl⟩)))
    · have : ¬ i < 1284 := fun h => hidle i (by omega) h rfl
      exact Or.inl (Or.inl (Or.inr (Or.inr ⟨i, by omega, rfl⟩)))
  · have h' : q ∈ [L.core.poolWire 1800, L.core.poolWire 1801, L.core.poolWire 1802,
        L.core.poolWire 1803, L.core.poolWire 1804] := by
      simpa [wireBlock, List.range'_succ] using h1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl (Or.inr (by simp [h']))
    · exact absurd h' hne
    · exact Or.inr (by simp [wireBlock, List.range'_succ, h'])
    · exact Or.inr (by simp [wireBlock, List.range'_succ, h'])
    · exact Or.inr (by simp [wireBlock, List.range'_succ, h'])

include hw

theorem pool_lowE (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesE L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_E
  simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

include hn

omit hw hn in
theorem E_of_sites (q : Wire) (hq : q ∈ CompressedPointSquare.residents L ++ CompressedPointSquare.sharedPool L)
    (h1 : q ≠ L.core.poolWire 1801) (h1' : q ≠ L.core.poolWire 1541)
    (h2 : q ≠ L.core.equalX) (h3 : q ≠ L.core.double) (h4 : q ≠ L.infinitySelect)
    (hidle : ∀ j, 1029 ≤ j → j < 1284 → q ≠ L.core.poolWire j) :
    q ∈ sitesE L := by
  rcases List.mem_append.mp hq with hr | hp
  · simp only [CompressedPointSquare.residents, inPlaceFlags, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (hp | hc) | hf
    · exact point_E L q hp
    · rw [hc]; exact control_E L
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h4
      · exact flag_E L _ (by simp [flagsE])
      · exact flag_E L _ (by simp [flagsE])
      · exact flag_E L _ (by simp [flagsE])
      · exact absurd rfl h2
      · exact flag_E L _ (by simp [flagsE])
      · exact absurd rfl h3
  · exact poolQ_E L q (sharedPool_F L q hp h1 h1' hidle)

omit hn in
theorem pairE (t₁ t₂ : Wire) (h1 : t₁ ∈ flagsE L) (h2 : t₂ ∈ flagsE L) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (sitesE L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | rfl | rfl | h | h
  · exact control_E L
  · exact y_E L _ hy
  · exact flag_E L _ h1
  · exact flag_E L _ h2
  · exact x_E L _ h
  · exact pool_lowE L hw 256 (by omega) q h

omit hn in
theorem gatedE (en : Bool) (t : Wire) (ht : t ∈ flagsE L) (P : Point) :
    wires (gatedShort L en t P) ⊆ (sitesE L).toFinset := by
  cases en
  · simp [gatedShort, wires]
  · intro q hq
    simp only [gatedShort, if_true] at hq
    have h := shortEqual_wires_subset L hw L.control t P (pointCode P) hq
    rw [equalConstant_wires] at h
    have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp [PointAddLayout.pointWires, L.dialogPool_length hw,
        show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]))
    simp only [List.mem_toFinset, List.mem_cons] at h
    apply List.mem_toFinset.mpr
    rcases h with rfl | rfl | h
    · exact control_E L
    · exact flag_E L _ ht
    · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h' | h'
      · exact point_E L _ h'
      · exact pool_lowE L hw 513 (by omega) _ h'

omit hw hn in
theorem zeroFlagE (t : Wire) (ht : t ∈ flagsE L) :
    wires (zeroFlag L.point.finite L.control t) ⊆ (sitesE L).toFinset := by
  rw [zeroFlag_wires]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl
  · exact point_E L _ (by simp [PointAddLayout.pointWires])
  · exact control_E L
  · exact flag_E L _ ht

omit hw hn in
theorem genericFlagE : wires (genericFlag2 L) ⊆ (sitesE L).toFinset := by
  intro q hq
  simp [genericFlag2, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [sitesE, flagsE, PointAddLayout.pointWires]

omit hw hn in
theorem cornersE (C : Point) : wires (corners2 L C) ⊆ (sitesE L).toFinset := by
  have m (c : Wire) (hc : c ∈ flagsE L) (P : Point) :
      wires (maskedPointConstant c L.point P) ⊆ (sitesE L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedPointConstant_support c L.point P hq)
    apply List.mem_toFinset.mpr
    rcases List.mem_cons.mp h with rfl | h
    · exact flag_E L _ hc
    · exact point_E L _ h
  simp only [corners2, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨m _ (by simp [flagsE]) _, m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩,
    m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩, m _ (by simp [flagsE]) _⟩

omit hw hn in
theorem chainEraseE (t : Wire) (ht : t ∈ flagsE L) :
    wires (chainErase L.control L.point.finite t) ⊆ (sitesE L).toFinset := by
  intro q hq
  have hw' : wires (chainErase L.control L.point.finite t) = {L.control, L.point.finite, t} := by
    ext q
    simp only [chainErase, wires, Instr.wires, correctionWires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  rw [hw'] at hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact List.mem_toFinset.mpr (control_E L)
  · exact List.mem_toFinset.mpr (point_E L L.point.finite (by simp [PointAddLayout.pointWires]))
  · exact List.mem_toFinset.mpr (flag_E L _ ht)

omit hn in
theorem finiteProgramFG_support (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (sitesE L).toFinset) :
    wires (finiteProgramFG L C cy Gen) ⊆ (sitesE L).toFinset := by
  have fS : flagsE L = [L.doubleSelect, L.genericSelect, L.core.generic, L.core.equalNegY] := rfl
  simp only [finiteProgramFG, wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨pairE L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _, gatedE L hw _ _ (by simp [fS]) _⟩,
    genericFlagE L⟩, hG⟩, genericFlagE L⟩, zeroFlagE L _ (by simp [fS])⟩, cornersE L _⟩,
    pairE L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _⟩, gatedE L hw _ _ (by simp [fS]) _⟩,
    chainEraseE L _ (by simp [fS])⟩

/-! The Skywalk generic block. -/

theorem arithE (multiply : Bool) :
    wires (obArith L multiply) ⊆ (sitesE L).toFinset := by
  intro q hq
  have idle := obArith_idle L hw hn multiply
  obtain ⟨old, ⟨hslot, _, hgood⟩, rfl⟩ := obArith_wire L multiply q hq
  have hs2 := swap2_slots old hslot
  have inv := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, hs2, rfl⟩)
  have avoid (k : Nat) (hk : base k ∈ slots.toFinset) (hb : pointWireFn L (base k) = pointWireFn L (swap2 old)) :
      old = swap2 (base k) := by
    have := pointWireFn_injective_slots L hw hn _ hs2 (base k) hk hb.symm
    rw [← this, swap2_involutive]
  have mem (k : Nat) (hk : k ∈ indices) : base k ∈ slots.toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hidx (k : Nat) (h : k = 2313 ∨ k = 2406 ∨ k = 2408 ∨ k = 769 ∨ k = 2403) : k ∈ indices := by
    simp only [indices, List.mem_append, List.mem_range'_1]; omega
  apply List.mem_toFinset.mpr
  apply E_of_sites L _ (List.mem_toFinset.mp inv)
  · intro e
    have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
      simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 2313 (mem _ (hidx 2313 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 1797) = L.core.poolWire 1541 := by
      simp only [pointWireFn_base, pointIndexWire, show (1797:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 1797 m1797 (himg.trans e.symm)
    rw [show swap2 (base 1797) = base 769 by simp only [swap2, base]; simp] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2406) = L.core.equalX := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.1
    have := avoid 2406 (mem _ (hidx 2406 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2408) = L.core.double := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.2.1
    have := avoid 2408 (mem _ (hidx 2408 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2403) = L.infinitySelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.1
    have := avoid 2403 (mem _ (hidx 2403 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro j h1 h2 e
    rw [e] at hq
    exact idle j ⟨h1, h2⟩ hq

theorem squareE : wires (CompressedPointSquare.computableProgram L) ⊆ (sitesE L).toFinset := by
  rw [CompressedPointSquare.computableProgram_eq L hw hn]
  intro q hq
  rw [CompressedPointSquare.program, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have supp := pointMeasuredSquareCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at supp
  apply List.mem_toFinset.mpr
  rcases supp with h | h | h | h
  · rw [h, CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      inPlaceFlags])]
    exact generic_E L
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact y_E L _ h
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact x_E L _ h
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)]
    apply poolQ_E
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have ha := CompressedPointSquare.prefix_allowed i bound
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨_, by omega, rfl⟩)))

attribute [local irreducible] fastCandidate in
theorem fastSquareE : wires (fastSquare L) ⊆ (sitesE L).toFinset := by
  rw [fastSquare_eq L hw hn]
  intro q hq
  rw [fastSquareN, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have supp := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at supp
  apply List.mem_toFinset.mpr
  rcases supp with h | h | h | h
  · rw [h, CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      inPlaceFlags])]
    exact generic_E L
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact y_E L _ h
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact x_E L _ h
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)]
    apply poolQ_E
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have ha := CompressedPointSquare.prefix_allowed i bound
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨_, by omega, rfl⟩)))

omit hn in
theorem constAddE (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (k : Fp) :
    wires (pointDialogConstantAdd L r k) ⊆ (sitesE L).toFinset := by
  intro q hq
  have h := List.mem_toFinset.mp (pointRecoveryConstantAdd_support L hw r k hq)
  apply List.mem_toFinset.mpr
  simp only [List.mem_cons, List.mem_append, or_assoc] at h
  rcases h with h | h | h
  · rw [h]; exact generic_E L
  · rcases hr with rfl | rfl
    · exact x_E L _ h
    · exact y_E L _ h
  · exact pool_lowE L hw 515 (by omega) _ h

omit hn in
theorem recoveryE (cx cy : Fp) : wires (pointRecoveryStage L cx cy) ⊆ (sitesE L).toFinset := by
  have neg : wires (pointRecoveryReflection L) ⊆ (sitesE L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (pointRecoveryReflection_support L hw hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_cons, List.mem_append, or_assoc] at h
    rcases h with h | h | h
    · rw [h]; exact generic_E L
    · exact x_E L _ h
    · exact pool_lowE L hw 258 (by omega) _ h
  simp only [pointRecoveryStage, pointDialogConstantAdd, wires_append, Finset.union_subset_iff]
  exact ⟨⟨neg, constAddE L hw _ (Or.inl rfl) _⟩, constAddE L hw _ (Or.inr rfl) _⟩

omit hn in
theorem sharedPool_Q_sub (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ L.dialogPool := by
  have big : q ∈ L.dialogPool.take 2613 := by
    rw [pool_block L hw 2613 (le_refl _)]
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [wireBlock, List.mem_map, List.mem_range'_1]
    rcases hq with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨1800, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩
  exact List.mem_of_mem_take big

omit hn in
theorem sitesE_used : (sitesE L).toFinset ⊆ L.dialogUsedWires.toFinset := by
  intro q hq
  have h := List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [sitesE, flagsE, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [dialogUsedWires, inPlaceFlags, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · tauto
  · exact Or.inr (sharedPool_Q_sub L hw q h)

end Support

end ECDSAAdd.Entrant

end

section
-- ===== EKMain =====
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

theorem finiteProgramFG_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) {cx : Fp} (hc : curve.toAffine.Nonsingular cx cy) (hC : C = .some hc) :
    toffoliCount (finiteProgramFG L C cy Gen) ≤ 1031 + toffoliCount Gen ∧
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
  have z1 := zeroFlag_counts L.point.finite L.control L.core.generic
  have z2 : toffoliCount (chainErase L.control L.point.finite L.genericSelect) = 0 ∧
      measurementCount (chainErase L.control L.point.finite L.genericSelect) = 1 := by
    simp [chainErase, toffoliCount, measurementCount]
  have f := genericFlag2_counts L
  have c := (show toffoliCount (corners2 L C) = 0 ∧ measurementCount (corners2 L C) = 0 by
    simp only [corners2, toffoliCount_append, measurementCount_append,
      (maskedPointConstant_counts _ _ _).1, (maskedPointConstant_counts _ _ _).2]; decide)
  simp only [finiteProgramFG, toffoliCount_append, measurementCount_append]
  omega

theorem finiteProgramFG_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : GatePhysical Gen) :
    GatePhysical (finiteProgramFG L C cy Gen) := by
  have sep := dialogFlag_separation (L:=L) hn
  have hz (t : Wire) (ht : t∈L.inPlaceFlags) : GatePhysical (zeroFlag L.point.finite L.control t) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    have hnd := L.dialogPointZero_nodup hn L.control t hct (Or.inl rfl) ht
    simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
      List.mem_append, not_or] at hnd
    exact zeroFlag_physical _ _ _ (fun h => hnd.2.1.1 h.symm) hct
  have hg (en : Bool) (t : Wire) (ht : t∈L.inPlaceFlags) (P : Point) : GatePhysical (gatedShort L en t P) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    cases en
    · simp [gatedShort, GatePhysical]
    · simpa only [gatedShort, if_true] using shortEqual_physical L hw hn L.control t hct (Or.inl rfl) ht P
  have z1 := hz L.core.generic (by simp [inPlaceFlags])
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
  have hzf (t : Wire) : gateSlots (zeroFlag L.point.finite L.control t) = 3 := rfl
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
  simp only [finiteProgramFG, corners2, gateSlots_append, hf, hzf, hze]
  omega

end Resources

end ECDSAAdd.Entrant

end

section
-- ===== FastGeneric2 =====
/-! The compare-first generic block with the one-bank arithmetic `obArith` (`OBArith.lean`).
Every other block is the one of `fastGeneric`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog

def fastGeneric2 (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  fastConstAdd L L.point.x (-cx) ++ fastConstAdd L L.point.y (-cy) ++
  obArith L false ++
  fastSquare L ++
  fastConstRefl L (3*cx-1) ++
  obArith L true ++
  fastConstNeg L cx ++ fastConstAdd L L.point.y (-cy)

section Generic
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
attribute [local irreducible] run obArith CompressedPointSquare.computableProgram fastSquare fastCandidate
  pointMeasuredSquareCandidate fastConstAdd fastConstNeg fastConstRefl

theorem fast2_generic_true (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (fastGeneric2 L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := fastStep_addX L hw hn X Y true base (-cx)
  have h2 := fastStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := ParametricPointDialog.step_arithmetic obBackend L hw hn (X-cx) (Y-cy) true base false
    (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := fast_step_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := fastStep_refl L hw hn (-1-((X-cx)-a*a)) a true base (3*cx-1)
  simp only [if_true] at h5
  have hd5 : 3*cx-1-(-1-((X-cx)-a*a))=d := by
    have e := hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [← e]; ring
  rw [hd5] at h5
  have h6 := ParametricPointDialog.step_arithmetic obBackend L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have h7 := fastStep_negX L hw hn d (a*d) true base cx
  simp only [if_true] at h7
  have h8 := fastStep_addY L hw hn (cx-d) (a*d) true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h8
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at h7 h8
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h8
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simpa only [fastGeneric2,obBackend,List.append_assoc] using h

theorem fast2_generic_false (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (fastGeneric2 L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := fastStep_addX L hw hn X Y false base (-cx)
  have h2 := fastStep_addY L hw hn X Y false base (-cy)
  have h3 := ParametricPointDialog.step_arithmetic obBackend L hw hn X Y false base false (by simp)
  have h4 := fast_step_square L hw hn X Y false base
  have h5 := fastStep_refl L hw hn (-1-X) Y false base (3*cx-1)
  have h6 := ParametricPointDialog.step_arithmetic obBackend L hw hn X Y false base true (by simp)
  have h7 := fastStep_negX L hw hn X Y false base cx
  have h8 := fastStep_addY L hw hn X Y false base (-cy)
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 h7 h8
  rw [show -1-(-1-X)=X by ring] at h5
  have h := ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8
  simpa only [fastGeneric2,obBackend,List.append_assoc] using h

theorem fast2_boundary_generic (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (fastGeneric2 L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    obtain ⟨phase,hv⟩ := fast2_generic_false L hw hn _ _ cx cy s.basis s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      obtain ⟨phase,hv⟩ := fast2_generic_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end Generic

section Resources
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw

theorem fastGeneric2_counts (cx cy : Fp) :
    toffoliCount (fastGeneric2 L cx cy)=2440583 ∧
    measurementCount (fastGeneric2 L cx cy)=1780628 := by
  have a k := fastConstAdd_counts L hw L.point.x (Or.inl rfl) k
  have b k := fastConstAdd_counts L hw L.point.y (Or.inr rfl) k
  have c := fastConstNeg_counts L hw cx
  have r := fastConstRefl_counts L hw (3*cx-1)
  have arith := obArith_counts L
  have square := fastSquare_counts L hw
  simp only [fastGeneric2,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,c.1,c.2,r.1,r.2,arith.1,arith.2.1,arith.2.2.1,arith.2.2.2,
    square.1,square.2]
  norm_num

include hn in
theorem fastGeneric2_physical (cx cy : Fp) : GatePhysical (fastGeneric2 L cx cy) := by
  have ax (k : Fp) := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c k.val
  have ay (k : Fp) := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) SquareReduction.c k.val
  have ng := FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have di := obArith_physical L hw hn false
  have mu := obArith_physical L hw hn true
  have rf := FastConst.fastRefl_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p (3*cx-1).val
  have sq := fastSquare_physical L hw hn
  simp only [fastGeneric2,fastConstAdd,fastConstNeg,fastConstRefl,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨ax _,ay _⟩,di⟩,sq⟩,rf⟩,mu⟩,ng⟩,ay _⟩

theorem fastGeneric2_gateSlots_le (cx cy : Fp) :
    Challenge.gateSlots (fastGeneric2 L cx cy) ≤ 44900000 := by
  have ax (r : List Wire) (hr : r.length=256) (k : Fp) :=
    FastConst.fastAdd_gateSlots_le (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw r hr)
  have ng := FastConst.fastNeg_gateSlots_le (g:=L.core.generic) 256 p cx.val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a1 := ax L.point.x hw.inputX (-cx)
  have a2 := ax L.point.y hw.inputY (-cy)
  have a3 := FastConst.fastRefl_gateSlots_le (g:=L.core.generic) 256 p (3*cx-1).val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have d := obArith_gateSlots L false
  have e := obArith_gateSlots L true
  have f := fastSquare_gateSlots_le L hw
  simp only [fastGeneric2,fastConstAdd,fastConstNeg,fastConstRefl,Challenge.gateSlots_append]
  omega

end Resources

end ECDSAAdd.Entrant

end

section
-- ===== FastE =====
/-! The compare-first generic block lives in `sitesE` and satisfies the
generic-block contract. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog
attribute [local irreducible] wires controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw

theorem fastConstE (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).toFinset ⊆ (sitesE L).toFinset := by
  intro q hq
  have pool := L.recoveryConstant_pool hw r
  have hq' := List.mem_toFinset.mp hq
  have inpool (h : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ h
  apply List.mem_toFinset.mpr
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at hq'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at hq'
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  rcases hq' with h | (((h | h) | h) | h | h | h)
  · rw [h]; exact generic_E L
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inl (Or.inl h)))
  · rcases hr with rfl | rfl
    · exact x_E L _ h
    · exact y_E L _ h
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inl (Or.inr h)))
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inr (Or.inl h)))
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inl h))))
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inr h))))

include hn

theorem fastGenericE (cx cy : Fp) : wires (fastGeneric2 L cx cy) ⊆ (sitesE L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (fastConstAdd L r k) ⊆ (sitesE L).toFinset :=
    (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩).trans
      (fastConstE L hw r hr)
  have cn : wires (fastConstNeg L cx) ⊆ (sitesE L).toFinset :=
    (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstE L hw L.point.x (Or.inl rfl))
  have cr : wires (fastConstRefl L (3*cx-1)) ⊆ (sitesE L).toFinset :=
    (FastConst.fastRefl_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstE L hw L.point.x (Or.inl rfl))
  simp only [fastGeneric2, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _, ca _ (Or.inr rfl) _⟩, arithE L hw hn false⟩, fastSquareE L hw hn⟩,
    cr⟩, arithE L hw hn true⟩, cn⟩, ca _ (Or.inr rfl) _⟩

theorem fastGeneric_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (fastGeneric2 L cx cy) :=
  fun R b f hg => fast2_boundary_generic L hw hn R b f hc hg

end

end ECDSAAdd.Entrant

end

section
-- ===== FlagMerge =====
/-! Flag merge on top of `FlagG`.

* While the generic-branch block runs, its control bit is held in
  `genericSelect`: `genFlagN` folds `(b ∧ finite) ⊕ D ⊕ H` into the
  inverse-point flag (the classes are exclusive, so the result is the generic
  bit), the block runs with `core.generic` and `genericSelect` exchanged, and
  the same gates restore the flag.
* The infinity flag of the output stage (`FlagG` keeps it on `core.generic`)
  lives on pool site 514 instead: that stage is relabelled with
  `core.generic ↔ poolWire 514`.  The stage uses only the first 256 pool sites.

Neither `core.generic` nor `infinitySelect` is used, which removes one more site. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

/-- Exchange of `core.generic` and `genericSelect`. -/
def tauM (L : ControlledPointLayout) (q : Wire) : Wire :=
  if q = L.core.generic then L.genericSelect else if q = L.genericSelect then L.core.generic else q

/-- The pool site that carries the output-stage infinity flag. -/
def parkWire (L : ControlledPointLayout) : Wire := L.core.poolWire 514

/-- Exchange of `core.generic` and the park site. -/
def sigP (L : ControlledPointLayout) (q : Wire) : Wire :=
  if q = L.core.generic then parkWire L else if q = parkWire L then L.core.generic else q

/-- A pool site used only by the generic block; it is relabelled onto
`equalNegY`, which is cleared while the block runs. -/
def spareWire (L : ControlledPointLayout) : Wire := L.core.poolWire 684

/-- Exchange of `equalNegY` and the spare site. -/
def swapE (L : ControlledPointLayout) (q : Wire) : Wire :=
  if q = L.core.equalNegY then spareWire L else if q = spareWire L then L.core.equalNegY else q

/-- `control ^= H`, `double ^= H`, then `H ^= ¬control ∧ double` clears `H`
(the exception class implies `b` and excludes the doubling class). -/
def foldH (L : ControlledPointLayout) : Program :=
  [.CX L.core.equalNegY L.control, .CX L.core.equalNegY L.doubleSelect, .X L.control,
   .CCX L.control L.doubleSelect L.core.equalNegY, .X L.control]

def unfoldH (L : ControlledPointLayout) : Program :=
  [.X L.control, .CCX L.control L.doubleSelect L.core.equalNegY, .X L.control,
   .CX L.core.equalNegY L.doubleSelect, .CX L.core.equalNegY L.control]

/-- `genericSelect ^= (b ∧ finite) ⊕ D ⊕ H`. -/
def genFlagN (L : ControlledPointLayout) : Program :=
  [.CCX L.control L.point.finite L.genericSelect, .CX L.doubleSelect L.genericSelect,
   .CX L.core.equalNegY L.genericSelect]

/-- The output stage of `finiteProgramFG` that holds the infinity flag. -/
def outStage (L : ControlledPointLayout) (C : Point) : Program :=
  zeroFlag L.point.finite L.control L.core.generic ++ corners2 L C ++
  pairEqual L L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)

def finiteProgramN (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  gatedShort L (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C) ++
  genFlagN L ++ foldH L ++ renameProgram (swapE L) (renameProgram (tauM L) Gen) ++ unfoldH L ++
  genFlagN L ++
  renameProgram (sigP L) (outStage L C) ++
  gatedShort L (decide (cy≠-cy)) L.doubleSelect (C+C) ++
  chainErase L.control L.point.finite L.genericSelect

def flagsN (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.genericSelect, L.core.equalNegY]

/-- The pool inventory without the spare site 684. -/
def sharedPoolF2 (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515 ++
    (wireBlock L.core.poolWire 685 344 ++ wireBlock L.core.poolWire 1284 257) ++
    [L.core.poolWire 1800] ++ wireBlock L.core.poolWire 1802 3

def sitesN (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsN L ++ sharedPoolF2 L

/-- Sites of the relabelled generic block before the spare exchange. -/
def sitesNx (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ [L.doubleSelect, L.genericSelect] ++ sharedPoolF L

def flagsG (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.core.generic]

/-- Sites of the generic block: it never touches `genericSelect`. -/
def sitesG (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsG L ++ sharedPoolF L

theorem sitesN_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesN L).length = 1637 := by
  simp [sitesN, flagsN, sharedPoolF2, PointAddLayout.pointWires, wireBlock_length,
    show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]

section Tau
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem generic_ne_select : L.core.generic ≠ L.genericSelect := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  tauto

theorem tauM_invol (q : Wire) : tauM L (tauM L q) = q := by
  have ne := generic_ne_select L hn
  unfold tauM
  by_cases h1 : q = L.core.generic
  · subst h1; simp [ne, ne.symm]
  · by_cases h2 : q = L.genericSelect
    · subst h2; simp [ne, ne.symm]
    · simp [h1, h2]

theorem tauM_injective : Function.Injective (tauM L) := by
  intro a b h
  have := congrArg (tauM L) h
  rwa [tauM_invol L hn, tauM_invol L hn] at this

omit hn in
theorem tauM_fix (q : Wire) (hq : q ∉ L.inPlaceFlags) : tauM L q = q := by
  have h1 : q ≠ L.core.generic := fun h => hq (by simp [h, inPlaceFlags])
  have h2 : q ≠ L.genericSelect := fun h => hq (by simp [h, inPlaceFlags])
  simp [tauM, h1, h2]

omit hn in
theorem tauM_flag (q : Wire) (hq : q ∈ L.inPlaceFlags) : tauM L q ∈ L.inPlaceFlags := by
  unfold tauM
  split_ifs
  · simp [inPlaceFlags]
  · simp [inPlaceFlags]
  · exact hq

theorem boundary_tau {R : Point} {b : Bool} {f s : BasisState} (v : PointDialogBoundary L R b f s) :
    PointDialogBoundary L R b (fun q => f (tauM L q)) (fun q => s (tauM L q)) :=
  v.withFlags hn (fun q hq => v.flags _ (tauM_flag L q hq)) (fun q hq => by rw [tauM_fix L q hq])

/-- The relabelled generic block, controlled by `genericSelect`. -/
theorem genericM_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (Gen : Program)
    (hGen : GenericOK L hc Gen) (R : Point) (b : Bool) (f : BasisState)
    (hg : f L.genericSelect = true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (renameProgram (tauM L) Gen)
      (PointDialogBoundary L (if f L.genericSelect then R+.some hc else R) b f) := by
  intro s m v
  have tg : tauM L L.core.generic = L.genericSelect := by simp [tauM]
  have h := hGen R b (fun q => f (tauM L q)) (by intro e; apply hg; simpa only [tg] using e)
    (pullState (tauM L) s) m (boundary_tau L hn v)
  rw [← run_rename (tauM L) (tauM_injective L hn)] at h
  simp only [tg] at h
  refine ⟨h.1, ?_⟩
  have back := boundary_tau L hn h.2
  simp only [pullState, tauM_invol L hn] at back
  exact back

end Tau

section Park
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem park_pool : parkWire L ∈ L.dialogPool := by
  have h : parkWire L ∈ L.dialogPool.take 515 := by
    rw [pool_block L hw 515 (by omega)]
    simp [parkWire, wireBlock, List.mem_map, List.mem_range'_1]
    exact ⟨514, by omega, rfl⟩
  exact List.mem_of_mem_take h

theorem park_away : parkWire L ∉ PointAddLayout.pointWires L.point ∧ parkWire L ≠ L.control ∧
    parkWire L ∉ L.inPlaceFlags := by
  have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) (parkWire L)
  have hp := List.count_pos_iff.mpr (park_pool L hw)
  simp only [dialogUsedWires, List.count_append] at used
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := List.count_pos_iff.mpr h; omega
  · have : 0 < List.count (parkWire L) [L.control] := List.count_pos_iff.mpr (by simp [h])
    omega
  · have := List.count_pos_iff.mpr h; omega

theorem park_ne_generic : parkWire L ≠ L.core.generic :=
  fun h => (park_away L hw hn).2.2 (by simp [h, inPlaceFlags])

theorem sigP_invol (q : Wire) : sigP L (sigP L q) = q := by
  have ne := park_ne_generic L hw hn
  unfold sigP
  by_cases h1 : q = L.core.generic
  · subst h1; simp [ne, ne.symm]
  · by_cases h2 : q = parkWire L
    · subst h2; simp [ne, ne.symm]
    · simp [h1, h2]

theorem sigP_injective : Function.Injective (sigP L) := by
  intro a b h
  have := congrArg (sigP L) h
  rwa [sigP_invol L hw hn, sigP_invol L hw hn] at this

/-- Relabelling the park site keeps the boundary when the generic flag is clear. -/
theorem boundary_sig {R : Point} {b : Bool} {f s : BasisState} (v : PointDialogBoundary L R b f s)
    (hf : f L.core.generic = false) :
    PointDialogBoundary L R b f (fun q => s (sigP L q)) := by
  have aw := park_away L hw hn
  have ng := park_ne_generic L hw hn
  have fix (q : Wire) (h1 : q ≠ L.core.generic) (h2 : q ≠ parkWire L) : sigP L q = q := by
    simp [sigP, h1, h2]
  have gpt : L.core.generic ∉ PointAddLayout.pointWires L.point := by
    intro h
    have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
    have a := List.count_pos_iff.mpr h
    have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
    simp only [dialogUsedWires, List.count_append] at used
    omega
  have hpt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : sigP L q = q :=
    fix q (fun e => gpt (e ▸ hq)) (fun e => aw.1 (e ▸ hq))
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨(point_holds _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpt _ (by simp [PointAddLayout.pointWires])]; exact hp.1
  · rw [regValue_congr L.point.x _ s (fun q hq => by
      rw [hpt q (by simp [PointAddLayout.pointWires, hq])])]; exact hp.2.1
  · rw [regValue_congr L.point.y _ s (fun q hq => by
      rw [hpt q (by simp [PointAddLayout.pointWires, hq])])]; exact hp.2.2
  · have sep := dialogFlag_separation L hn
    have cg : L.control ≠ L.core.generic := by
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep; tauto
    show s (sigP L L.control) = b
    rw [fix _ cg (fun e => aw.2.1 e.symm)]; exact v.control
  · intro q hq
    show s (sigP L q) = f q
    by_cases hg : q = L.core.generic
    · subst hg
      simp only [sigP, if_true]
      rw [hf]
      exact (regValue_zero _ _).mp v.clean _ (park_pool L hw)
    · rw [fix q hg (fun e => aw.2.2 (e ▸ hq))]; exact v.flags q hq
  · apply (regValue_zero _ _).mpr
    intro q hq
    show s (sigP L q) = false
    by_cases hk : q = parkWire L
    · subst hk
      simp only [sigP, if_neg (park_ne_generic L hw hn), if_true]
      rw [v.flags _ (by simp [inPlaceFlags]), hf]
    · have hg : q ≠ L.core.generic := by
        intro e; subst e
        have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
        have a := List.count_pos_iff.mpr hq
        have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
        simp only [dialogUsedWires, List.count_append] at used
        omega
      rw [fix q hg hk]
      exact (regValue_zero _ _).mp v.clean q hq

theorem park_triple (X : Program) (R R' : Point) (b : Bool) (f f' : BasisState)
    (hf : f L.core.generic = false) (hf' : f' L.core.generic = false)
    (hX : Triple (PointDialogBoundary L R b f) X (PointDialogBoundary L R' b f')) :
    Triple (PointDialogBoundary L R b f) (renameProgram (sigP L) X) (PointDialogBoundary L R' b f') := by
  intro s m v
  have h := hX (pullState (sigP L) s) m (boundary_sig L hw hn v hf)
  rw [← run_rename (sigP L) (sigP_injective L hw hn)] at h
  refine ⟨h.1, ?_⟩
  have back := boundary_sig L hw hn h.2 hf'
  simp only [pullState, sigP_invol L hw hn] at back
  exact back

end Park

section Spare
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem spare_pool : spareWire L ∈ L.dialogPool := by
  apply sharedPool_Q_sub L hw
  simp [spareWire, sharedPoolF, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inr (Or.inl ⟨684, by omega, rfl⟩)

theorem spare_away : spareWire L ∉ PointAddLayout.pointWires L.point ∧ spareWire L ≠ L.control ∧
    spareWire L ∉ L.inPlaceFlags := by
  have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) (spareWire L)
  have hp := List.count_pos_iff.mpr (spare_pool L hw)
  simp only [dialogUsedWires, List.count_append] at used
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := List.count_pos_iff.mpr h; omega
  · have : 0 < List.count (spareWire L) [L.control] := List.count_pos_iff.mpr (by simp [h])
    omega
  · have := List.count_pos_iff.mpr h; omega

theorem spare_ne_exc : spareWire L ≠ L.core.equalNegY :=
  fun h => (spare_away L hw hn).2.2 (by simp [h, inPlaceFlags])

theorem swapE_invol (q : Wire) : swapE L (swapE L q) = q := by
  have ne := spare_ne_exc L hw hn
  unfold swapE
  by_cases h1 : q = L.core.equalNegY
  · subst h1; simp [ne, ne.symm]
  · by_cases h2 : q = spareWire L
    · subst h2; simp [ne, ne.symm]
    · simp [h1, h2]

theorem swapE_injective : Function.Injective (swapE L) := by
  intro a b h
  have := congrArg (swapE L) h
  rwa [swapE_invol L hw hn, swapE_invol L hw hn] at this

/-- Relabelling the park site keeps the boundary when the generic flag is clear. -/
theorem boundary_swapE {R : Point} {b : Bool} {f s : BasisState} (v : PointDialogBoundary L R b f s)
    (hf : f L.core.equalNegY = false) :
    PointDialogBoundary L R b f (fun q => s (swapE L q)) := by
  have aw := spare_away L hw hn
  have ng := spare_ne_exc L hw hn
  have fix (q : Wire) (h1 : q ≠ L.core.equalNegY) (h2 : q ≠ spareWire L) : swapE L q = q := by
    simp [swapE, h1, h2]
  have gpt : L.core.equalNegY ∉ PointAddLayout.pointWires L.point := by
    intro h
    have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
    have a := List.count_pos_iff.mpr h
    have c : 0 < List.count L.core.equalNegY L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
    simp only [dialogUsedWires, List.count_append] at used
    omega
  have hpt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : swapE L q = q :=
    fix q (fun e => gpt (e ▸ hq)) (fun e => aw.1 (e ▸ hq))
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨(point_holds _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpt _ (by simp [PointAddLayout.pointWires])]; exact hp.1
  · rw [regValue_congr L.point.x _ s (fun q hq => by
      rw [hpt q (by simp [PointAddLayout.pointWires, hq])])]; exact hp.2.1
  · rw [regValue_congr L.point.y _ s (fun q hq => by
      rw [hpt q (by simp [PointAddLayout.pointWires, hq])])]; exact hp.2.2
  · have sep := dialogFlag_separation L hn
    have cg : L.control ≠ L.core.equalNegY := by
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep; tauto
    show s (swapE L L.control) = b
    rw [fix _ cg (fun e => aw.2.1 e.symm)]; exact v.control
  · intro q hq
    show s (swapE L q) = f q
    by_cases hg : q = L.core.equalNegY
    · subst hg
      simp only [swapE, if_true]
      rw [hf]
      exact (regValue_zero _ _).mp v.clean _ (spare_pool L hw)
    · rw [fix q hg (fun e => aw.2.2 (e ▸ hq))]; exact v.flags q hq
  · apply (regValue_zero _ _).mpr
    intro q hq
    show s (swapE L q) = false
    by_cases hk : q = spareWire L
    · subst hk
      simp only [swapE, if_neg (spare_ne_exc L hw hn), if_true]
      rw [v.flags _ (by simp [inPlaceFlags]), hf]
    · have hg : q ≠ L.core.equalNegY := by
        intro e; subst e
        have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
        have a := List.count_pos_iff.mpr hq
        have c : 0 < List.count L.core.equalNegY L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
        simp only [dialogUsedWires, List.count_append] at used
        omega
      rw [fix q hg hk]
      exact (regValue_zero _ _).mp v.clean q hq

theorem spare_triple (X : Program) (R R' : Point) (b : Bool) (f f' : BasisState)
    (hf : f L.core.equalNegY = false) (hf' : f' L.core.equalNegY = false)
    (hX : Triple (PointDialogBoundary L R b f) X (PointDialogBoundary L R' b f')) :
    Triple (PointDialogBoundary L R b f) (renameProgram (swapE L) X) (PointDialogBoundary L R' b f') := by
  intro s m v
  have h := hX (pullState (swapE L) s) m (boundary_swapE L hw hn v hf)
  rw [← run_rename (swapE L) (swapE_injective L hw hn)] at h
  refine ⟨h.1, ?_⟩
  have back := boundary_swapE L hw hn h.2 hf'
  simp only [pullState, swapE_invol L hw hn] at back
  exact back

/-- The generic block, relabelled onto `genericSelect` and the cleared exception wire. -/
theorem genericE_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (Gen : Program)
    (hGen : GenericOK L hc Gen) (R : Point) (b : Bool) (f : BasisState)
    (hg : f L.genericSelect = true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc))
    (hx : f L.core.equalNegY = false) :
    Triple (PointDialogBoundary L R b f) (renameProgram (swapE L) (renameProgram (tauM L) Gen))
      (PointDialogBoundary L (if f L.genericSelect then R+.some hc else R) b f) :=
  spare_triple L hw hn _ R _ b f f hx hx (genericM_ok L hn hc Gen hGen R b f hg)

end Spare

section Flags
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem genFlagN_run (s : State) (m : List Bool) :
    run (genFlagN L) m s = ⟨s.phase, writeBit s.basis L.genericSelect
      (((s.basis L.genericSelect ^^ (s.basis L.control && s.basis L.point.finite)) ^^
        s.basis L.doubleSelect) ^^ s.basis L.core.equalNegY)⟩ := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hfin : L.point.finite ∉ L.control :: L.inPlaceFlags := by
    have hh := List.nodup_iff_count_le_one.mp (L.dialogUsed_nodup hn) L.point.finite
    have hp : 1 ≤ (PointAddLayout.pointWires L.point).count L.point.finite :=
      List.count_pos_iff.mpr (by simp [PointAddLayout.pointWires])
    simp only [dialogUsedWires, List.count_append] at hh
    have hc : (L.control :: L.inPlaceFlags).count L.point.finite = 0 := by
      show ([L.control] ++ L.inPlaceFlags).count _ = 0
      rw [List.count_append]; omega
    exact List.count_eq_zero.mp hc
  simp only [inPlaceFlags, List.mem_cons, not_or] at hfin
  have h1 : L.control ≠ L.genericSelect := by tauto
  have h2 : L.point.finite ≠ L.genericSelect := by tauto
  have h3 : L.doubleSelect ≠ L.genericSelect := by tauto
  have h5 : L.core.equalNegY ≠ L.genericSelect := by tauto
  simp only [genFlagN, run]
  congr 1
  funext q
  by_cases hq : q = L.genericSelect
  · subst hq; simp [writeBit, h1, h2, h3, h5]
  · simp [writeBit, hq]

theorem genFlagN_flag (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K)) (genFlagN L)
      (PointDialogBoundary L R b (dialogFlagState L O D
        (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) G E H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  intro s m v
  have hh := genFlagN_run L hn s m
  have hfin : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have rd (q : Wire) (hq : q ∈ L.inPlaceFlags) : s.basis q = dialogFlagState L O D I G E H K q := v.flags q hq
  have eD := rd L.doubleSelect (by simp [inPlaceFlags])
  have eI := rd L.genericSelect (by simp [inPlaceFlags])
  have eH := rd L.core.equalNegY (by simp [inPlaceFlags])
  rw [hr.2.1] at eD; rw [hr.2.2.1] at eI; rw [hr.2.2.2.2.2.1] at eH
  rw [eD, eI, eH, hfin, v.control] at hh
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    have u := (dialogFlagState_update L hn O D I G E H K
      (((I ^^ (b && pointFinite R)) ^^ D) ^^ H)).2.2.1 q hq
    rw [← u]
    by_cases he : q = L.genericSelect
    · subst he; simp [writeBit]
    · simp [writeBit, he, rd q hq]
  · intro q hq
    rw [hh]
    have hqt : q ≠ L.genericSelect := fun he => hq (he ▸ by simp [inPlaceFlags])
    simp [writeBit, hqt]

end Flags

section Fold
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem fold_distinct : L.core.equalNegY ≠ L.control ∧ L.core.equalNegY ≠ L.doubleSelect ∧
    L.control ≠ L.doubleSelect := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  refine ⟨?_, ?_, ?_⟩ <;> intro e <;> simp_all

theorem foldH_run (s : State) (m : List Bool) :
    run (foldH L) m s = ⟨s.phase, fun q =>
      if q = L.control then (s.basis L.control ^^ s.basis L.core.equalNegY)
      else if q = L.doubleSelect then (s.basis L.doubleSelect ^^ s.basis L.core.equalNegY)
      else if q = L.core.equalNegY then (s.basis L.core.equalNegY ^^
        (!(s.basis L.control ^^ s.basis L.core.equalNegY) &&
          (s.basis L.doubleSelect ^^ s.basis L.core.equalNegY)))
      else s.basis q⟩ := by
  obtain ⟨h1, h2, h3⟩ := fold_distinct L hn
  simp only [foldH, run]
  congr 1
  funext q
  by_cases hc : q = L.control <;> by_cases hd : q = L.doubleSelect <;>
    by_cases he : q = L.core.equalNegY <;>
    simp_all [writeBit, Function.update_apply, eq_comm]

theorem unfoldH_run (s : State) (m : List Bool) :
    run (unfoldH L) m s = ⟨s.phase, fun q =>
      let e := (s.basis L.core.equalNegY ^^ (!s.basis L.control && s.basis L.doubleSelect))
      if q = L.control then (s.basis L.control ^^ e)
      else if q = L.doubleSelect then (s.basis L.doubleSelect ^^ e)
      else if q = L.core.equalNegY then e
      else s.basis q⟩ := by
  obtain ⟨h1, h2, h3⟩ := fold_distinct L hn
  simp only [unfoldH, run]
  congr 1
  funext q
  by_cases hc : q = L.control <;> by_cases hd : q = L.doubleSelect <;>
    by_cases he : q = L.core.equalNegY <;>
    simp_all [writeBit, Function.update_apply, eq_comm]

/-- A state that changes only control and flags keeps the point and the pool. -/
theorem boundary_upd {R : Point} {b b' : Bool} {f f' s t : BasisState}
    (v : PointDialogBoundary L R b f s)
    (ht : ∀ q, q ≠ L.control → q ∉ L.inPlaceFlags → t q = s q) (hc : t L.control = b')
    (hf : ∀ q ∈ L.inPlaceFlags, t q = f' q) : PointDialogBoundary L R b' f' t := by
  have pt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ≠ L.control ∧ q ∉ L.inPlaceFlags := by
    have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have a := List.count_pos_iff.mpr hq
    simp only [dialogUsedWires, List.count_append] at used
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have : 0 < List.count q [L.control] := List.count_pos_iff.mpr (by simp [e])
      omega
    · have := List.count_pos_iff.mpr e; omega
  have pl (q : Wire) (hq : q ∈ L.dialogPool) : q ≠ L.control ∧ q ∉ L.inPlaceFlags := by
    have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have a := List.count_pos_iff.mpr hq
    simp only [dialogUsedWires, List.count_append] at used
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have : 0 < List.count q [L.control] := List.count_pos_iff.mpr (by simp [e])
      omega
    · have := List.count_pos_iff.mpr e; omega
  have hpt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : t q = s q :=
    ht q (pt q hq).1 (pt q hq).2
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨(point_holds _ _ _).mpr ⟨?_, ?_, ?_⟩, hc, hf, ?_⟩
  · rw [hpt _ (by simp [PointAddLayout.pointWires])]; exact hp.1
  · rw [regValue_congr L.point.x t s (fun q hq => hpt q (by simp [PointAddLayout.pointWires, hq]))]
    exact hp.2.1
  · rw [regValue_congr L.point.y t s (fun q hq => hpt q (by simp [PointAddLayout.pointWires, hq]))]
    exact hp.2.2
  · rw [regValue_congr L.dialogPool t s (fun q hq => ht q (pl q hq).1 (pl q hq).2)]
    exact v.clean

omit hn in
theorem state_other (D D' G H H' : Bool) (q : Wire)
    (hd : q ≠ L.doubleSelect) (he : q ≠ L.core.equalNegY) :
    dialogFlagState L false D G false false H false q = dialogFlagState L false D' G false false H' false q := by
  simp only [dialogFlagState, writeBit, Function.update_apply, hd, he, if_false]

theorem foldH_flag (R : Point) (b D G H : Bool) (hH : H = true → b = true ∧ D = false)
    (hD : D = true → b = true) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false)) (foldH L)
      (PointDialogBoundary L R (b ^^ H) (dialogFlagState L false (D ^^ H) G false false false false)) := by
  intro s m v
  have hr := dialogFlagState_read L hn false D G false false H false
  have hr' := dialogFlagState_read L hn false (D ^^ H) G false false false false
  have vc := v.control
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.1
  have ve := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.2.2.2.2.1
  obtain ⟨h1, h2, h3⟩ := fold_distinct L hn
  rw [foldH_run L hn]
  refine ⟨rfl, boundary_upd L hn v ?_ ?_ ?_⟩
  · intro q hc hf
    have hd : q ≠ L.doubleSelect := fun e => hf (e ▸ by simp [inPlaceFlags])
    have he : q ≠ L.core.equalNegY := fun e => hf (e ▸ by simp [inPlaceFlags])
    simp [hc, hd, he]
  · simp [vc, ve]
  · intro q hq
    by_cases hc : q = L.control
    · exact absurd (hc ▸ hq) (by
        have sep := dialogFlag_separation L hn
        exact (List.nodup_cons.mp sep).1)
    by_cases hd : q = L.doubleSelect
    · subst hd; simp only [h3.symm, if_false, if_true, vd, ve]; rw [hr'.2.1]
    by_cases he : q = L.core.equalNegY
    · subst he
      simp only [h1, h2, if_false, if_true, vc, vd, ve]
      rw [hr'.2.2.2.2.2.1]
      clear vc vd ve v hr hr'
      cases H <;> cases b <;> cases D <;> simp at hH hD ⊢
    · simp only [hc, hd, he, if_false]
      rw [v.flags q hq]
      exact state_other L D (D ^^ H) G H false q hd he

theorem unfoldH_flag (R : Point) (b D G H : Bool) (hH : H = true → b = true ∧ D = false)
    (hD : D = true → b = true) :
    Triple (PointDialogBoundary L R (b ^^ H) (dialogFlagState L false (D ^^ H) G false false false false))
      (unfoldH L)
      (PointDialogBoundary L R b (dialogFlagState L false D G false false H false)) := by
  intro s m v
  have hr := dialogFlagState_read L hn false (D ^^ H) G false false false false
  have hr' := dialogFlagState_read L hn false D G false false H false
  have vc := v.control
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.1
  have ve := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.2.2.2.2.1
  have key : (false ^^ (!(b ^^ H) && (D ^^ H))) = H := by
    cases H <;> cases b <;> cases D <;> simp at hH hD ⊢
  obtain ⟨h1, h2, h3⟩ := fold_distinct L hn
  rw [unfoldH_run L hn]
  refine ⟨rfl, boundary_upd L hn v ?_ ?_ ?_⟩
  · intro q hc hf
    have hd : q ≠ L.doubleSelect := fun e => hf (e ▸ by simp [inPlaceFlags])
    have he : q ≠ L.core.equalNegY := fun e => hf (e ▸ by simp [inPlaceFlags])
    simp [hc, hd, he]
  · simp only [if_true, vc, vd, ve, key]; cases b <;> cases H <;> rfl
  · intro q hq
    by_cases hc : q = L.control
    · exact absurd (hc ▸ hq) (by
        have sep := dialogFlag_separation L hn
        exact (List.nodup_cons.mp sep).1)
    by_cases hd : q = L.doubleSelect
    · subst hd; simp only [h3.symm, if_false, if_true, vc, vd, ve, key]; rw [hr'.2.1]
      cases D <;> cases H <;> rfl
    by_cases he : q = L.core.equalNegY
    · subst he
      simp only [h1, h2, if_false, if_true, vc, vd, ve, key]
      rw [hr'.2.2.2.2.2.1]
    · simp only [hc, hd, he, if_false]
      rw [v.flags q hq]
      exact state_other L (D ^^ H) D G false H q hd he

end Fold

section SpecN
attribute [local irreducible] run wires shortEqual pairEqual gatedShort genericFlag2 corners2 genFlagN

private theorem equal_simpN [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgramN_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgramN L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  let R1 := if G then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simpN,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simpN]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simpN]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simpN]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simpN]
  have hfin (P : Point) : (b && pointFinite P) = (b ^^ (b && pointEqual P 0)) := by
    rw [pointEqual_zero]; cases b <;> cases pointFinite P <;> rfl
  have hGv : ((((false ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) = G := by
    rw [hfin, hO]; simp only [G, dialogOrdinary, O, D, I, H, Bool.false_xor]
  have hgen := (dialogOrdinary_true b R C hC)
  have hR1fin : (b && pointFinite R1) = (b && pointFinite R) := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have f1 : pointFinite (R+C) = true := by
        have t := pointEqual_zero (R+C)
        have e2 : pointEqual (R+C) 0 = false := by
          cases h : pointEqual (R+C) 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) hs
        rw [e2] at t
        cases h : pointFinite (R+C)
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      have f2 : pointFinite R = true := by
        have t := pointEqual_zero R
        have e2 : pointEqual R 0 = false := by
          cases h : pointEqual R 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) h0
        rw [e2] at t
        cases h : pointFinite R
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      simp only [R1, hg, if_true, f1, f2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg]
  have hR1O : (b && pointEqual R1 0) = O := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have e1 : pointEqual (R+C) 0 = false := by
        cases h : pointEqual (R+C) 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) hs
      have e2 : pointEqual R 0 = false := by
        cases h : pointEqual R 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) h0
      rw [← hO]; simp only [R1, hg, if_true, e1, e2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg, hO]
  have hG1 : (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) = G := by
    rw [← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have hI1 : (((G ^^ (b && pointFinite R1)) ^^ D) ^^ H) = I := by
    rw [hR1fin, ← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have h3 := pairFlag_inputE L hw hn R C cy b false false false false false false false
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := gatedFlag_H L hw hn R (dialogExceptionPoint C) (exceptionBit C) b false D I false false false false
  rw [hH,Bool.false_xor] at h5
  have h6 := genFlagN_flag L hn R b false D I false false H false
  rw [hG1] at h6
  have hHx : H = true → b = true ∧ D = false := by
    intro h
    dsimp only [H, D, dialogException, dialogDouble] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, _, hne, _⟩, hR⟩ := h
    refine ⟨hb, ?_⟩
    simp [hR, hne]
  have hDx : D = true → b = true := by
    intro h
    dsimp only [D, dialogDouble] at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have hf1 := foldH_flag L hn R b D G H hHx hDx
  have read := dialogFlagState_read L hn false (D ^^ H) G false false false false
  have h7 := genericE_ok L hw hn hc Gen hGen R (b ^^ H)
    (dialogFlagState L false (D ^^ H) G false false false false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.1.symm.trans hg)).2) read.2.2.2.2.2.1
  rw [read.2.2.1] at h7
  have hu := unfoldH_flag L hn R1 b D G H hHx hDx
  have h9 := genFlagN_flag L hn R1 b false D G false false H false
  rw [hI1] at h9
  have h10a := zeroFlag_flagG L hn R1 b false D I false false H false
  rw [hR1O, Bool.false_xor] at h10a
  have readO := dialogFlagState_read L hn false D I O false H false
  have h8 := corners2_boundary L hw hn R C hC b (dialogFlagState L false D I O false H false)
    readO.2.2.2.1 readO.2.1 readO.2.2.1 readO.2.2.2.2.2.1
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [H,S,dialogExceptionEnabled,equal_simpN] using hf.2.2.2
  have h10 := pairFlag_outputG L hw hn S C (exceptionBit C) b false D I O false H false
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simpN] at h10
  rw [hf.1,Bool.xor_self] at h10
  have hout := park_triple L hw hn (outStage L C) R1 S b
    (dialogFlagState L false D I false false H false) (dialogFlagState L false D I false false false false)
    (dialogFlagState_read L hn false D I false false H false).2.2.2.1
    (dialogFlagState_read L hn false D I false false false false).2.2.2.1
    (by simpa only [outStage, List.append_assoc] using (h10a.seq h8).seq h10)
  have h11 := gatedFlag_D L hw hn S (C+C) (decide (cy≠-cy)) b false D I false false false false
  have hdo : ((b && decide (cy≠-cy)) && pointEqual S (C+C))=D := by
    change (K && pointEqual S (C+C)) = D
    rw [hK]; simpa only [equal_simpN] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have hzero : decide (S=0) = !pointFinite S := by
    rw [← equal_simpN]
    exact pointEqual_zero S
  have h12 := chainErase_equalI L hn S b false false (dialogInversePoint b R C)
    false false false false (by rw [← hf.2.2.1, hzero])
  have h := (((((((((h3.seq h5).seq h6).seq hf1).seq h7).seq hu).seq h9).seq hout).seq h11).seq h12)
  simpa only [finiteProgramN,List.append_assoc,dialogFlagState_zero] using h

end SpecN

/-! Supports. -/
section Support
attribute [local irreducible] wires shortEqual pairEqual controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

theorem point_G (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesG L := by
  simp [sitesG, hq]
theorem control_G : L.control ∈ sitesG L := by simp [sitesG]
theorem flag_G (t : Wire) (ht : t ∈ flagsG L) : t ∈ sitesG L := by simp [sitesG, ht]
theorem x_G (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesG L :=
  point_G L q (by simp [PointAddLayout.pointWires, hq])
theorem y_G (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesG L :=
  point_G L q (by simp [PointAddLayout.pointWires, hq])
theorem generic_G : L.core.generic ∈ sitesG L := flag_G L _ (by simp [flagsG])
theorem poolQ_G (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ sitesG L := by
  simp only [sitesG, List.mem_append]; exact Or.inr hq

theorem point_N (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesN L := by
  simp [sitesN, hq]
theorem control_N : L.control ∈ sitesN L := by simp [sitesN]
theorem flag_N (t : Wire) (ht : t ∈ flagsN L) : t ∈ sitesN L := by simp [sitesN, ht]
theorem x_N (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesN L :=
  point_N L q (by simp [PointAddLayout.pointWires, hq])
theorem y_N (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesN L :=
  point_N L q (by simp [PointAddLayout.pointWires, hq])
theorem poolQ_N (q : Wire) (hq : q ∈ sharedPoolF2 L) : q ∈ sitesN L := by
  simp only [sitesN, List.mem_append]; exact Or.inr hq

include hw

theorem pool_lowG (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesG L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_G
  simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

theorem pool_lowN (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesN L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_N
  simp only [sharedPoolF2, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

omit hw in
theorem G_of_sites (q : Wire) (hq : q ∈ CompressedPointSquare.residents L ++ CompressedPointSquare.sharedPool L)
    (h1 : q ≠ L.core.poolWire 1801) (h1' : q ≠ L.core.poolWire 1541)
    (h2 : q ≠ L.core.equalX) (h3 : q ≠ L.core.double) (h4 : q ≠ L.infinitySelect)
    (h5 : q ≠ L.genericSelect) (h6 : q ≠ L.core.equalNegY)
    (hidle : ∀ j, 1029 ≤ j → j < 1284 → q ≠ L.core.poolWire j) :
    q ∈ sitesG L := by
  rcases List.mem_append.mp hq with hr | hp
  · simp only [CompressedPointSquare.residents, inPlaceFlags, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (hp | hc) | hf
    · exact point_G L q hp
    · rw [hc]; exact control_G L
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h4
      · exact flag_G L _ (by simp [flagsG])
      · exact absurd rfl h5
      · exact flag_G L _ (by simp [flagsG])
      · exact absurd rfl h2
      · exact absurd rfl h6
      · exact absurd rfl h3
  · exact poolQ_G L q (sharedPool_F L q hp h1 h1' hidle)

theorem fastConstG (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).toFinset ⊆ (sitesG L).toFinset := by
  intro q hq
  have pool := L.recoveryConstant_pool hw r
  have hq' := List.mem_toFinset.mp hq
  have inpool (h : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ h
  apply List.mem_toFinset.mpr
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at hq'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at hq'
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  rcases hq' with h | (((h | h) | h) | h | h | h)
  · rw [h]; exact generic_G L
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inl (Or.inl h)))
  · rcases hr with rfl | rfl
    · exact x_G L _ h
    · exact y_G L _ h
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inl (Or.inr h)))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inl h)))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inl h))))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inr h))))

include hn

theorem arithG (multiply : Bool) :
    wires (obArith L multiply) ⊆ (sitesG L).toFinset := by
  intro q hq
  have idle := obArith_idle L hw hn multiply
  obtain ⟨old, ⟨hslot, _, hgood⟩, rfl⟩ := obArith_wire L multiply q hq
  have hs2 := swap2_slots old hslot
  have inv := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, hs2, rfl⟩)
  have avoid (k : Nat) (hk : base k ∈ slots.toFinset) (hb : pointWireFn L (base k) = pointWireFn L (swap2 old)) :
      old = swap2 (base k) := by
    have := pointWireFn_injective_slots L hw hn _ hs2 (base k) hk hb.symm
    rw [← this, swap2_involutive]
  have mem (k : Nat) (hk : k ∈ indices) : base k ∈ slots.toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hidx (k : Nat) (h : k = 2313 ∨ k = 2403 ∨ k = 2405 ∨ k = 2406 ∨ k = 2407 ∨ k = 2408 ∨ k = 769) : k ∈ indices := by
    simp only [indices, List.mem_append, List.mem_range'_1]; omega
  apply List.mem_toFinset.mpr
  apply G_of_sites L _ (List.mem_toFinset.mp inv)
  · intro e
    have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
      simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 2313 (mem _ (hidx 2313 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 1797) = L.core.poolWire 1541 := by
      simp only [pointWireFn_base, pointIndexWire, show (1797:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 1797 m1797 (himg.trans e.symm)
    rw [show swap2 (base 1797) = base 769 by simp only [swap2, base]; simp] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2406) = L.core.equalX := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.1
    have := avoid 2406 (mem _ (hidx 2406 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2408) = L.core.double := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.2.1
    have := avoid 2408 (mem _ (hidx 2408 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2403) = L.infinitySelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.1
    have := avoid 2403 (mem _ (hidx 2403 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2405) = L.genericSelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.1
    have := avoid 2405 (mem _ (hidx 2405 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2407) = L.core.equalNegY := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.1
    have := avoid 2407 (mem _ (hidx 2407 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro j h1 h2 e
    rw [e] at hq
    exact idle j ⟨h1, h2⟩ hq


attribute [local irreducible] fastCandidate in
theorem fastSquareG : wires (fastSquare L) ⊆ (sitesG L).toFinset := by
  rw [fastSquare_eq L hw hn]
  intro q hq
  rw [fastSquareN, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have supp := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at supp
  apply List.mem_toFinset.mpr
  rcases supp with h | h | h | h
  · rw [h, CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      inPlaceFlags])]
    exact generic_G L
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact y_G L _ h
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact x_G L _ h
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)]
    apply poolQ_G
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have ha := CompressedPointSquare.prefix_allowed i bound
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨_, by omega, rfl⟩)))

theorem fastGenericG (cx cy : Fp) : wires (fastGeneric2 L cx cy) ⊆ (sitesG L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (fastConstAdd L r k) ⊆ (sitesG L).toFinset :=
    (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩).trans
      (fastConstG L hw r hr)
  have cn : wires (fastConstNeg L cx) ⊆ (sitesG L).toFinset :=
    (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstG L hw L.point.x (Or.inl rfl))
  have cr : wires (fastConstRefl L (3*cx-1)) ⊆ (sitesG L).toFinset :=
    (FastConst.fastRefl_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstG L hw L.point.x (Or.inl rfl))
  simp only [fastGeneric2, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _, ca _ (Or.inr rfl) _⟩, arithG L hw hn false⟩, fastSquareG L hw hn⟩,
    cr⟩, arithG L hw hn true⟩, cn⟩, ca _ (Or.inr rfl) _⟩

/-- The relabelled block lives in `sitesN`. -/
theorem renamedG (Gen : Program) (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (renameProgram (tauM L) Gen) ⊆ (sitesNx L).toFinset := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have h := List.mem_toFinset.mp (hG used)
  apply List.mem_toFinset.mpr
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  by_cases hg : old = L.core.generic
  · rw [hg, show tauM L L.core.generic = L.genericSelect by simp [tauM]]
    simp [sitesNx]
  · have hs : old ≠ L.genericSelect := by
      intro e
      subst e
      simp only [sitesG, flagsG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.genericSelect
      have cG : 0 < List.count L.genericSelect L.inPlaceFlags :=
        List.count_pos_iff.mpr (by simp [inPlaceFlags])
      rcases h with ((hp | hc) | hf) | hp
      · have := List.count_pos_iff.mpr hp
        simp only [dialogUsedWires, List.count_append] at used
        omega
      · exact absurd hc.symm (by tauto)
      · rcases hf with e | e
        · exact absurd e.symm (by tauto)
        · exact hg e
      · have := List.count_pos_iff.mpr (sharedPool_Q_sub L hw _ hp)
        simp only [dialogUsedWires, List.count_append] at used
        omega
    rw [show tauM L old = old by simp [tauM, hg, hs]]
    simp only [sitesG, flagsG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [sitesNx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

/-- The doubly relabelled block lives in `sitesN`. -/
theorem renamedE (Gen : Program) (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ⊆ (sitesN L).toFinset := by
  have h0 := renamedG L hw hn Gen hG
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have h := List.mem_toFinset.mp (h0 used)
  apply List.mem_toFinset.mpr
  have aw := spare_away L hw hn
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  by_cases hk : old = spareWire L
  · rw [hk, show swapE L (spareWire L) = L.core.equalNegY by
      simp [swapE, (spare_ne_exc L hw hn)]]
    exact flag_N L _ (by simp [flagsN])
  · have he : old ≠ L.core.equalNegY := by
      intro e
      subst e
      simp only [sitesNx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
      have cG : 0 < List.count L.core.equalNegY L.inPlaceFlags :=
        List.count_pos_iff.mpr (by simp [inPlaceFlags])
      rcases h with ((hp | hc) | hf) | hp
      · have := List.count_pos_iff.mpr hp
        simp only [dialogUsedWires, List.count_append] at used
        omega
      · exact absurd hc.symm (by tauto)
      · rcases hf with e | e
        · exact absurd e.symm (by tauto)
        · exact absurd e.symm (by tauto)
      · have := List.count_pos_iff.mpr (sharedPool_Q_sub L hw _ hp)
        simp only [dialogUsedWires, List.count_append] at used
        omega
    rw [show swapE L old = old by simp [swapE, he, hk]]
    simp only [sitesNx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with ((hp | hc) | hf) | hp
    · exact point_N L _ hp
    · rw [hc]; exact control_N L
    · rcases hf with rfl | rfl <;> exact flag_N L _ (by simp [flagsN])
    · apply poolQ_N
      simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1,
        List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [sharedPoolF2, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1,
        List.mem_cons, List.not_mem_nil, or_false]
      rcases hp with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | e) | ⟨i, hi, rfl⟩
      · exact Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))
      · have : i ≠ 684 := by rintro rfl; exact hk rfl
        exact Or.inl (Or.inl (Or.inr (Or.inl ⟨i, by omega, rfl⟩)))
      · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨i, hi, rfl⟩)))
      · exact Or.inl (Or.inr e)
      · exact Or.inr ⟨i, hi, rfl⟩

omit hn in
/-- Wires of the output stage, before relabelling. -/
theorem outStage_wires (C : Point) (q : Wire) (hq : q ∈ wires (outStage L C)) :
    q ∈ PointAddLayout.pointWires L.point ∨ q = L.control ∨ q = L.core.generic ∨ q ∈ flagsN L ∨
      q ∈ L.dialogPool.take 256 := by
  simp only [outStage, wires_append, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · rw [zeroFlag_wires] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl (by simp [PointAddLayout.pointWires])
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · simp only [corners2, wires_append, Finset.mem_union] at h
    have m (c : Wire) (P : Point) (hm : q ∈ wires (maskedPointConstant c L.point P)) :
        q = c ∨ q ∈ PointAddLayout.pointWires L.point := by
      have := List.mem_toFinset.mp (maskedPointConstant_support c L.point P hm)
      simpa using this
    rcases h with ((((h | h) | h) | h) | h) | h
    · rcases m _ _ h with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inl e
    all_goals first
      | (rcases m _ _ h with e | e
         · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [flagsN, e]))))
         · exact Or.inl e)
  · have hh := pairEqual_wires L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C) h
    have hy := yLow_mem L hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at hh
    rcases hh with rfl | rfl | rfl | rfl | h' | h'
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (by simp [PointAddLayout.pointWires, hy])
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [flagsN]))))
    · exact Or.inl (by simp [PointAddLayout.pointWires, h'])
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

theorem outStageN (C : Point) :
    wires (renameProgram (sigP L) (outStage L C)) ⊆ (sitesN L).toFinset := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  apply List.mem_toFinset.mpr
  have aw := park_away L hw hn
  have pk : parkWire L ∉ L.dialogPool.take 256 := by
    rw [pool_block L hw 256 (by omega)]
    intro h
    obtain ⟨i, hi, e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hi
    have := pool_inj L hw hn i 514 (by omega) (by omega) e
    omega
  have parkN : parkWire L ∈ sitesN L := by
    apply poolQ_N
    simp [parkWire, sharedPoolF2, wireBlock, List.mem_map, List.mem_range'_1]
    exact Or.inl ⟨514, by omega, rfl⟩
  rcases outStage_wires L hw C old used with h | h | h | h | h
  · have hg : old ≠ L.core.generic := by
      intro e; subst e
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
      have a := List.count_pos_iff.mpr h
      have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
      simp only [dialogUsedWires, List.count_append] at used
      omega
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => aw.1 (e ▸ h)
      simp [sigP, hg, hk]]
    exact point_N L _ h
  · subst h
    have sep := dialogFlag_separation L hn
    have cg : L.control ≠ L.core.generic := by
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep; tauto
    rw [show sigP L L.control = L.control by
      have hk : L.control ≠ parkWire L := fun e => aw.2.1 e.symm
      simp [sigP, cg, hk]]
    exact control_N L
  · subst h; simpa [sigP] using parkN
  · have hfl : old ∈ L.inPlaceFlags := by
      simp only [flagsN, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [inPlaceFlags]
    have hg : old ≠ L.core.generic := by
      intro e; subst e
      have sep := dialogFlag_separation L hn
      simp only [flagsN, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
      rcases h with e | e | e
      · exact absurd e.symm (by tauto)
      · exact absurd e.symm (by tauto)
      · exact absurd e (by tauto)
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => aw.2.2 (e ▸ hfl)
      simp [sigP, hg, hk]]
    exact flag_N L _ h
  · have hg : old ≠ L.core.generic := by
      intro e; subst e
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
      have a := List.count_pos_iff.mpr (List.mem_of_mem_take h)
      have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
      simp only [dialogUsedWires, List.count_append] at used
      omega
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => pk (e ▸ h)
      simp [sigP, hg, hk]]
    exact pool_lowN L hw 256 (by omega) _ h

omit hn in
theorem pairN (t₁ t₂ : Wire) (h1 : t₁ ∈ flagsN L) (h2 : t₂ ∈ flagsN L) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (sitesN L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | rfl | rfl | h | h
  · exact control_N L
  · exact y_N L _ hy
  · exact flag_N L _ h1
  · exact flag_N L _ h2
  · exact x_N L _ h
  · exact pool_lowN L hw 256 (by omega) q h

omit hn in
theorem gatedN (en : Bool) (t : Wire) (ht : t ∈ flagsN L) (P : Point) :
    wires (gatedShort L en t P) ⊆ (sitesN L).toFinset := by
  cases en
  · simp [gatedShort, wires]
  · intro q hq
    simp only [gatedShort, if_true] at hq
    have h := shortEqual_wires_subset L hw L.control t P (pointCode P) hq
    rw [equalConstant_wires] at h
    have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp [PointAddLayout.pointWires, L.dialogPool_length hw,
        show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]))
    simp only [List.mem_toFinset, List.mem_cons] at h
    apply List.mem_toFinset.mpr
    rcases h with rfl | rfl | h
    · exact control_N L
    · exact flag_N L _ ht
    · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h' | h'
      · exact point_N L _ h'
      · exact pool_lowN L hw 513 (by omega) _ h'

omit hw hn in
theorem zeroFlagN (t : Wire) (ht : t ∈ flagsN L) :
    wires (zeroFlag L.point.finite L.control t) ⊆ (sitesN L).toFinset := by
  rw [zeroFlag_wires]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl
  · exact point_N L _ (by simp [PointAddLayout.pointWires])
  · exact control_N L
  · exact flag_N L _ ht

omit hw hn in
theorem chainEraseN (t : Wire) (ht : t ∈ flagsN L) :
    wires (chainErase L.control L.point.finite t) ⊆ (sitesN L).toFinset := by
  intro q hq
  have hw' : wires (chainErase L.control L.point.finite t) = {L.control, L.point.finite, t} := by
    ext q
    simp only [chainErase, wires, Instr.wires, correctionWires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  rw [hw'] at hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact List.mem_toFinset.mpr (control_N L)
  · exact List.mem_toFinset.mpr (point_N L L.point.finite (by simp [PointAddLayout.pointWires]))
  · exact List.mem_toFinset.mpr (flag_N L _ ht)

omit hw hn in
theorem foldH_support : wires (foldH L) ⊆ (sitesN L).toFinset := by
  intro q hq
  simp [foldH, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl <;> simp [sitesN, flagsN]

omit hw hn in
theorem unfoldH_support : wires (unfoldH L) ⊆ (sitesN L).toFinset := by
  intro q hq
  simp [unfoldH, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl <;> simp [sitesN, flagsN]

omit hw hn in
theorem genFlagN_support : wires (genFlagN L) ⊆ (sitesN L).toFinset := by
  intro q hq
  simp [genFlagN, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl | rfl | rfl
  all_goals simp [sitesN, flagsN, PointAddLayout.pointWires]

theorem finiteProgramN_support (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (finiteProgramN L C cy Gen) ⊆ (sitesN L).toFinset := by
  have fS : flagsN L = [L.doubleSelect, L.genericSelect, L.core.equalNegY] := rfl
  simp only [finiteProgramN, wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨pairN L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _,
    gatedN L hw _ _ (by simp [fS]) _⟩, genFlagN_support L⟩, foldH_support L⟩, renamedE L hw hn Gen hG⟩,
    unfoldH_support L⟩, genFlagN_support L⟩,
    outStageN L hw hn C⟩, gatedN L hw _ _ (by simp [fS]) _⟩, chainEraseN L _ (by simp [fS])⟩

omit hw hn in
theorem sitesN_sub (q : Wire) (hq : q ∈ sitesN L) : q ∈ sitesE L := by
  simp only [sitesN, flagsN, sitesE, flagsE, sharedPoolF2, sharedPoolF, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, wireBlock, List.mem_map, List.mem_range'_1] at hq ⊢
  rcases hq with ((hp | hc) | hf) | ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | e) | ⟨i, hi, rfl⟩
  · exact Or.inl (Or.inl (Or.inl hp))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr (by tauto))
  · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl ⟨i, by omega, rfl⟩))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr ⟨i, hi, rfl⟩))))
  · exact Or.inr (Or.inl (Or.inr e))
  · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)

omit hn in
theorem sitesN_used : (sitesN L).toFinset ⊆ L.dialogUsedWires.toFinset := by
  intro q hq
  exact sitesE_used L hw (List.mem_toFinset.mpr (sitesN_sub L q (List.mem_toFinset.mp hq)))

end Support

/-! Frame, resources and validity. -/
section Frame
attribute [local irreducible] run wires

private theorem boundary_frame_valuesN (L : ControlledPointLayout) (P : Program)
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

private theorem boundary_work_subsetN (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_pointN (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

theorem finiteProgramN_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) (hG : wires Gen ⊆ (sitesG L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} finiteProgramN L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work_subsetN L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finiteProgramN_spec L hw hn R hc b Gen hGen s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (finiteProgramN_support L hw hn (.some hc) cy Gen hG).trans (sitesN_used L hw)
  rw [boundary_frame_valuesN L _ hsup R _ b s m hi ho q (work_not_pointN L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end Frame

section Resources
open Challenge Baselines

theorem finiteProgramN_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) {cx : Fp} (hc : curve.toAffine.Nonsingular cx cy) (hC : C = .some hc) :
    toffoliCount (finiteProgramN L C cy Gen) ≤ 1033 + toffoliCount Gen ∧
    measurementCount (finiteProgramN L C cy Gen) ≤ 1027 + measurementCount Gen := by
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
  have z1 := zeroFlag_counts L.point.finite L.control L.core.generic
  have z2 : toffoliCount (chainErase L.control L.point.finite L.genericSelect) = 0 ∧
      measurementCount (chainErase L.control L.point.finite L.genericSelect) = 1 := by
    simp [chainErase, toffoliCount, measurementCount]
  have f : toffoliCount (genFlagN L) = 1 ∧ measurementCount (genFlagN L) = 0 := by
    simp [genFlagN, toffoliCount, measurementCount]
  have r := renameProgram_counts (tauM L) Gen
  have r' := renameProgram_counts (swapE L) (renameProgram (tauM L) Gen)
  have fo : toffoliCount (foldH L) = 1 ∧ measurementCount (foldH L) = 0 := by
    simp [foldH, toffoliCount, measurementCount]
  have uf : toffoliCount (unfoldH L) = 1 ∧ measurementCount (unfoldH L) = 0 := by
    simp [unfoldH, toffoliCount, measurementCount]
  have r2 := renameProgram_counts (sigP L) (outStage L C)
  have c := (show toffoliCount (corners2 L C) = 0 ∧ measurementCount (corners2 L C) = 0 by
    simp only [corners2, toffoliCount_append, measurementCount_append,
      (maskedPointConstant_counts _ _ _).1, (maskedPointConstant_counts _ _ _).2]; decide)
  simp only [outStage, toffoliCount_append, measurementCount_append] at r2
  simp only [finiteProgramN, outStage, toffoliCount_append, measurementCount_append]
  omega

theorem finiteProgramN_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : GatePhysical Gen) :
    GatePhysical (finiteProgramN L C cy Gen) := by
  have sep := dialogFlag_separation (L:=L) hn
  have hz (t : Wire) (ht : t∈L.inPlaceFlags) : GatePhysical (zeroFlag L.point.finite L.control t) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    have hnd := L.dialogPointZero_nodup hn L.control t hct (Or.inl rfl) ht
    simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
      List.mem_append, not_or] at hnd
    exact zeroFlag_physical _ _ _ (fun h => hnd.2.1.1 h.symm) hct
  have hg (en : Bool) (t : Wire) (ht : t∈L.inPlaceFlags) (P : Point) : GatePhysical (gatedShort L en t P) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    cases en
    · simp [gatedShort, GatePhysical]
    · simpa only [gatedShort, if_true] using shortEqual_physical L hw hn L.control t hct (Or.inl rfl) ht P
  have z1 := hz L.core.generic (by simp [inPlaceFlags])
  have z2 : GatePhysical (chainErase L.control L.point.finite L.genericSelect) := by
    intro i hi
    simp only [chainErase, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals trivial
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
  have rn0 := gatePhysical_rename (tauM L) (tauM_injective L hn) Gen hG
  have rn := gatePhysical_rename (swapE L) (swapE_injective L hw hn) _ rn0
  obtain ⟨fd1, fd2, fd3⟩ := fold_distinct L hn
  have fo : GatePhysical (foldH L) := by
    intro i hi
    simp only [foldH, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact fd1
    · exact fd2
    · trivial
    · exact ⟨fd1.symm, fd2.symm⟩
    · trivial
  have uf : GatePhysical (unfoldH L) := by
    intro i hi
    simp only [unfoldH, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact ⟨fd1.symm, fd2.symm⟩
    · trivial
    · exact fd2
    · exact fd1
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hfin : L.point.finite ≠ L.genericSelect := by
    intro e
    exact away L.genericSelect (by simp [inPlaceFlags]) (e ▸ by simp [PointAddLayout.pointWires])
  have fl : GatePhysical (genFlagN L) := by
    intro i hi
    simp only [genFlagN, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨by tauto, hfin⟩
    · exact (by tauto : L.doubleSelect ≠ L.genericSelect)
    · exact (by tauto : L.core.equalNegY ≠ L.genericSelect)
  have q3 := hg (exceptionBit C) L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have q5 := hg (decide (cy≠-cy)) L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have p1 := pairEqual_physical L hw hn L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_physical L hw hn L.core.generic L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) true (exceptionBit C) C (-C)
  have os : GatePhysical (outStage L C) := by
    simp only [outStage, gatePhysical_append]
    exact ⟨⟨z1, co⟩, p2⟩
  have rs := gatePhysical_rename (sigP L) (sigP_injective L hw hn) _ os
  simp only [finiteProgramN, gatePhysical_append]
  tauto

theorem finiteProgramN_gateSlots (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) : gateSlots (finiteProgramN L C cy Gen) ≤ 20000 + gateSlots Gen := by
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have hf : gateSlots (genFlagN L) = 3 := rfl
  have hzf (t : Wire) : gateSlots (zeroFlag L.point.finite L.control t) = 3 := rfl
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
  have hze : gateSlots (chainErase L.control L.point.finite L.genericSelect) = 4 := rfl
  have rs := rename_gateSlots (tauM L) Gen
  have rs' := rename_gateSlots (swapE L) (renameProgram (tauM L) Gen)
  have hfo : gateSlots (foldH L) = 5 := rfl
  have huf : gateSlots (unfoldH L) = 5 := rfl
  have rs2 := rename_gateSlots (sigP L) (outStage L C)
  simp only [finiteProgramN, gateSlots_append, hf, hzf, hze, hfo, huf, rs', rs, rs2]
  simp only [outStage, corners2, gateSlots_append, hzf]
  omega

end Resources

end ECDSAAdd.Entrant

end

section
-- ===== Main =====
/-! Entrant: Skywalk with flag-only infinity tests (`ZeroFlag.lean`), short and
paired point comparisons (`ShortEqual.lean`, `PairEqual.lean`), compare-first
constant additions (`FastConst.lean`, `FastGeneric.lean`), enable-free
classification (`EKFree.lean`), a one-bank Stage 2/5 field whose late integer
signs live in retired carry slots (`OBSigma` .. `OBArith`), and a static site
bound that excludes the sites no block touches (`ArithAvoid.lean`,
`QSupport.lean`, `EKSupport.lean`).
All semantics and metric definitions remain in the protected challenge. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 Challenge Baselines

/-- Infinity addend emits no gates; a finite addend runs `finiteProgramN`
around the compare-first generic-branch block. -/
def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      finiteProgramN layout C cy (fastGeneric2 layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)

def bounds : Challenge.Bounds := ⟨2441616, 1781655, 1637, 45600000⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program, run, ← WeierstrassCurve.Affine.Point.zero_def, add_zero, ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have hG := fastGenericG layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _ (finiteProgramN_full_spec layout layout_widths layout_nodup R hc b _
        (fastGeneric_ok layout layout_widths layout_nodup hc) hG)
      ((finiteProgramN_support layout layout_widths layout_nodup _ cy _ hG).trans
        (sitesN_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2441616 := by
  cases C with
  | zero => simp [program, toffoliCount]
  | @some cx cy hc =>
    have h := (finiteProgramN_counts layout layout_widths (.some hc) cy
      (fastGeneric2 layout cx cy) hc rfl).1
    have g := (fastGeneric2_counts layout layout_widths cx cy).1
    change toffoliCount (finiteProgramN layout (.some hc) cy (fastGeneric2 layout cx cy)) ≤ _
    omega

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1781655 := by
  cases C with
  | zero => simp [program, measurementCount]
  | @some cx cy hc =>
    have h := (finiteProgramN_counts layout layout_widths (.some hc) cy
      (fastGeneric2 layout cx cy) hc rfl).2
    have g := (fastGeneric2_counts layout layout_widths cx cy).2
    change measurementCount (finiteProgramN layout (.some hc) cy (fastGeneric2 layout cx cy)) ≤ _
    omega

theorem io_subset_sitesN : ioWires ⊆ (sitesN layout).toFinset := by
  intro w hw
  have h := io_partition w hw
  apply List.mem_toFinset.mpr
  rcases h with hp | hc
  · exact point_N layout w hp
  · rw [hc]; exact control_N layout

/-- Static support: point, control, five classification flags, and the
certified pool inventory without its idle site; `core.generic` and
`infinitySelect` are both unused (`FlagMerge.lean`). -/
theorem program_qubits (C : Point) : qubits (program C) ≤ 1637 := by
  cases C with
  | zero =>
    change qubits [] ≤ 1637
    rw [qubits_empty]
    decide
  | @some cx cy hc =>
    have support := finiteProgramN_support layout layout_widths layout_nodup (.some hc) cy _
      (fastGenericG layout layout_widths layout_nodup cx cy)
    have card := Finset.card_le_card (Finset.union_subset io_subset_sitesN support)
    exact card.trans ((List.toFinset_card_le _).trans_eq (sitesN_length layout layout_widths))

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program, GatePhysical]
  | @some cx cy hc =>
    exact finiteProgramN_physical layout layout_widths layout_nodup _ cy _
      (fastGeneric2_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 45600000 := by
  cases C with
  | zero => simp [program, gateSlots]
  | @some cx cy hc =>
    have h := finiteProgramN_gateSlots layout layout_widths (.some hc) cy
      (fastGeneric2 layout cx cy)
    have g := fastGeneric2_gateSlots_le layout layout_widths cx cy
    change gateSlots (finiteProgramN layout (.some hc) cy (fastGeneric2 layout cx cy)) ≤ _
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1781655
    rw [normalize_measurements]
    exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1637
    rw [normalize_qubits]
    exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 45600000
    rw [normalize_slots]
    exact program_gateSlots C

end ECDSAAdd.Entrant

end
