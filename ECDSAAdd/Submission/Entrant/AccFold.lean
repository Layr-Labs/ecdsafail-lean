import ECDSAAdd.Submission.Entrant.AccBuild
import ECDSAAdd.Submission.Entrant.SquareFolds

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
