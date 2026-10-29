import ECDSAAdd.Arithmetic.MeasuredStreamedSquare
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.TriangularSquareProof
import ECDSAAdd.Baselines.SlotAlgebra

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

end ECDSAAdd.Entrant.Acc
