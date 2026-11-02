import ECDSAAdd.Submission.Entrant.Prelude

-- ===== merged module ECDSAAdd.Submission.Entrant.NoThreeTorsion =====
section
namespace ECDSAAdd.Entrant.NoThreeTorsion
open Arithmetic Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

theorem negative21 :
    ((-21 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^
      57896044618658097711785492504343953926634992332820282019728792003954417335831)=-1 := by
  reduce_mod_char

theorem not_square (y : Fp) : y^2≠-21 := by
  intro sq
  have hp : p=115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    norm_num [p]
  have h := negative21
  rw [←hp] at h
  change (-21 : Fp)^((p-1)/2)=-1 at h
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [hz] at sq
    norm_num at sq
    exact (by decide : (21 : Fp)≠0) sq
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have exp : p-1=2*((p-1)/2) := by norm_num [p]
  rw [exp,pow_mul,sq,h] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

theorem double_x_ne {x y : Fp} (hc : curve.toAffine.Nonsingular x y) : doubleX x y≠x := by
  intro he
  have hyneg : y≠-y := of_decide_eq_true (cy_ne_neg hc)
  have hy : y≠0 := by intro hz; apply hyneg; simp [hz]
  have h2 : (2 : Fp)≠0 := by decide
  have h3 : (3 : Fp)≠0 := by decide
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have sq : y^2=x^3+7 := by simpa [curve,curveA,curveB] using equation
  unfold doubleX doubleSlope doubleNumerator doubleDenominator at he
  field_simp [hy] at he
  have product : 3*x*(x^3+28)=0 := by linear_combination -he - 12*x*sq
  have cubic := (mul_eq_zero.mp product).resolve_left (mul_ne_zero h3 (curve_x_ne_zero hc))
  apply not_square y
  linear_combination sq+cubic

theorem enabled {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    exceptionBit (.some hc)=true := by
  classical
  let C : Point := .some hc
  have hy : y≠-y := of_decide_eq_true (cy_ne_neg hc)
  have hzero : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hdouble : C+C≠0 := by
    rw [show C+C=doublePoint hc hy from (doublePoint_correct hc hy).symm]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hneg : C+C≠-C := by
    intro eq
    have e : (.some (double_nonsingular hc hy) : Point)=-C := by
      change doublePoint hc hy=-C
      rw [doublePoint_correct hc hy]
      exact eq
    exact double_x_ne hc ((sameX_iff_eq_or_neg (double_nonsingular hc hy) hc).mpr (Or.inr e))
  have hself : C+C≠C := by
    intro eq
    have e : C+C=C+0 := eq.trans (add_zero C).symm
    exact hzero (add_left_cancel e)
  have a : dialogExceptionPoint C≠0 := by
    intro eq
    exact hdouble (neg_eq_zero.mp eq)
  have b : dialogExceptionPoint C≠C := by
    intro eq
    exact hneg (neg_eq_iff_eq_neg.mp eq)
  have c : dialogExceptionPoint C≠-C := by
    intro eq
    exact hself (neg_injective eq)
  have pe (A B : Point) : pointEqual A B=decide (A=B) := by
    simp only [pointEqual,pointCode_injective.eq_iff]
  change exceptionBit C=true
  simp only [exceptionBit,pe]
  simp [a,b,c]

end ECDSAAdd.Entrant.NoThreeTorsion
end

-- ===== merged module ECDSAAdd.Submission.Entrant.MeasuredDH =====
section
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.MeasuredDH
open Arithmetic RecordedQuantum Baselines
open MeasuredCodec5 (bitRun safe)

def joint (erase cx cy : Bool) : Program :=
  [.CCX 3 0 8,.CX 5 8] ++
  (if erase then
    DHGadget.flipIf (!cy) 2 ++ [.measureX 4 [] [.CZ 8 2,.CZ 6 2]] ++ DHGadget.flipIf (!cy) 2 ++
    DHGadget.flipIf cx 1 ++ [.measureX 6 [] [.CZ 8 1]] ++ DHGadget.flipIf cx 1
   else
    DHGadget.flipIf cx 1 ++ [.CCX 8 1 6] ++ DHGadget.flipIf cx 1 ++ [.CX 6 8] ++
    DHGadget.flipIf (!cy) 2 ++ [.CCX 8 2 4] ++ DHGadget.flipIf (!cy) 2 ++ [.CX 6 8]) ++
  [.measureX 8 [] [.CZ 3 0,.Z 5]]

def replacement (erase enD enH cx cy : Bool) : Program := if enD && enH then joint erase cx cy else
  [.CCX 3 0 8, .CX 5 8] ++
  (if enD then
    DHGadget.flipIf (!cx) 1 ++ [.CCX 8 1 9] ++ DHGadget.flipIf (!cx) 1 ++
    DHGadget.flipIf (!cy) 2 ++
      (if erase then [.measureX 4 [] [.CZ 9 2]] else [.CCX 9 2 4]) ++
    DHGadget.flipIf (!cy) 2 ++
    DHGadget.flipIf (!cx) 1 ++ [.measureX 9 [] [.CZ 8 1]] ++ DHGadget.flipIf (!cx) 1
   else []) ++
  (if enH then DHGadget.flipIf cx 1 ++
      (if erase then [.measureX 6 [] [.CZ 8 1]] else [.CCX 8 1 6]) ++
    DHGadget.flipIf cx 1 else []) ++
  [.measureX 8 [] [.CZ 3 0, .Z 5]]

def original (enD enH cx cy : Bool) : Program :=
  DHGadget.gadget 3 0 5 4 6 1 2 7 8 9 enD enH cx cy

def clean (x : Nat) : Bool := !x.testBit 7 && !x.testBit 8 && !x.testBit 9
def covered (x : Nat) : Bool := !x.testBit 5 || (x.testBit 3 && x.testBit 0)
def clears (enD enH cx cy : Bool) (x : Nat) : Bool :=
  let y := bitRun (original enD enH cx cy) x
  !y.testBit 4 && !y.testBit 6

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem finite_equivalence : ∀ erase enD enH cx cy : Bool, ∀ x : Fin 1024,
    clean x.val = true → covered x.val = true →
    (erase = true → clears enD enH cx cy x.val = true) →
    (erase = false → x.val.testBit 4=false ∧ x.val.testBit 6=false) →
    safe (replacement erase enD enH cx cy) x.val = true ∧
      bitRun (replacement erase enD enH cx cy) x.val = bitRun (original enD enH cx cy) x.val := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem original_safe : ∀ enD enH cx cy : Bool, ∀ x < 1024,
    clean x = true → safe (original enD enH cx cy) x = true := by
  decide +kernel

theorem run_local (erase enD enH cx cy : Bool) (x : Nat) (hx : x<1024)
    (hc : clean x=true) (hg : covered x=true)
    (he : erase=true → clears enD enH cx cy x=true)
    (hr : erase=false → x.testBit 4=false ∧ x.testBit 6=false)
    (phase : Bool) (newRecord oldRecord : List Bool) :
    run (replacement erase enD enH cx cy) newRecord ⟨phase,MeasuredCodec5.bitsOf x⟩ =
      run (original enD enH cx cy) oldRecord ⟨phase,MeasuredCodec5.bitsOf x⟩ := by
  have h := finite_equivalence erase enD enH cx cy ⟨x,hx⟩ hc hg he hr
  rw [MeasuredCodec5.run_sim,MeasuredCodec5.sim_safe _ x h.1,
    MeasuredCodec5.run_sim,MeasuredCodec5.sim_safe _ x (original_safe enD enH cx cy x hx hc),h.2]

theorem support (erase enD enH cx cy : Bool) :
    wires (replacement erase enD enH cx cy) ⊆ Finset.range 10 ∧
    wires (original enD enH cx cy) ⊆ Finset.range 10 := by
  cases erase <;> cases enD <;> cases enH <;> cases cx <;> cases cy <;> decide

private theorem model (P : Program) (hs : wires P⊆Finset.range 10)
    (s : State) (m : List Bool) (x : Nat) (hx : ∀q<10,s.basis q=MeasuredCodec5.bitsOf x q)
    (hp : safe P x=true) :
    ∀q<10,(run P m s).basis q=MeasuredCodec5.bitsOf (bitRun P x) q := by
  have agree := pool_run_agrees P (Finset.range 10) hs m s
    ⟨s.phase,MeasuredCodec5.bitsOf x⟩ rfl (fun q hq => hx q (Finset.mem_range.mp hq))
  have modeled := MeasuredCodec5.run_sim P m s.phase x
  rw [MeasuredCodec5.sim_safe P x hp m s.phase] at modeled
  intro q hq
  exact (agree.2 q (Finset.mem_range.mpr hq)).trans
    (congrArg (fun t : State => t.basis q) modeled)

private def rawCode (s : BasisState) : Nat :=
  MeasuredCodec5.pack10 (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7) (s 8) (s 9)

private theorem rawCode_bit (s : BasisState) (q : Nat) (hq : q<10) :
    (rawCode s).testBit q=s q := by
  rw [rawCode,MeasuredCodec5.pack10_bits _ _ _ _ _ _ _ _ _ _ q hq]
  interval_cases q <;> simp [MeasuredCodec5.raw]

theorem run_eq (erase enD enH cx cy : Bool) (s : State) (m : List Bool)
    (hz : s.basis 7=false ∧ s.basis 8=false ∧ s.basis 9=false)
    (hg : s.basis 5=true → s.basis 3=true ∧ s.basis 0=true)
    (he : erase=true → (run (original enD enH cx cy) m s).basis 4=false ∧
      (run (original enD enH cx cy) m s).basis 6=false)
    (hr : erase=false → s.basis 4=false ∧ s.basis 6=false) :
    run (replacement erase enD enH cx cy) m s=run (original enD enH cx cy) m s := by
  let x := rawCode s.basis
  have hx : x<1024 := MeasuredCodec5.pack10_lt _ _ _ _ _ _ _ _ _ _
  have hb (q : Nat) (hq : q<10) : s.basis q=MeasuredCodec5.bitsOf x q :=
    (rawCode_bit s.basis q hq).symm
  have hc : clean x=true := by
    simp only [clean]
    change (!MeasuredCodec5.bitsOf x 7 && !MeasuredCodec5.bitsOf x 8 &&
      !MeasuredCodec5.bitsOf x 9)=true
    rw [←hb 7 (by decide),←hb 8 (by decide),←hb 9 (by decide),hz.1,hz.2.1,hz.2.2]
    rfl
  have cov : covered x=true := by
    simp only [covered]
    change (!MeasuredCodec5.bitsOf x 5 ||
      (MeasuredCodec5.bitsOf x 3 && MeasuredCodec5.bitsOf x 0))=true
    rw [←hb 5 (by decide),←hb 3 (by decide),←hb 0 (by decide)]
    cases h : s.basis 5
    · rfl
    · simp [h,(hg h).1,(hg h).2]
  have hp := support erase enD enH cx cy
  have eqzero : erase=true → clears enD enH cx cy x=true := by
    intro er
    have hm := model _ hp.2 s m x hb (original_safe enD enH cx cy x hx hc)
    have h4 := (hm 4 (by decide)).symm.trans (he er).1
    have h6 := (hm 6 (by decide)).symm.trans (he er).2
    change (bitRun (original enD enH cx cy) x).testBit 4=false at h4
    change (bitRun (original enD enH cx cy) x).testBit 6=false at h6
    simp only [clears,h4,h6]
    rfl
  apply FirstNonzeroCodec.run_eq_of_model _ _ hp.1 hp.2 s m x
    (fun q hq => hb q (Finset.mem_range.mp hq))
  have restore : erase=false → x.testBit 4=false ∧ x.testBit 6=false := by
    intro er
    exact ⟨(hb 4 (by decide)).symm.trans (hr er).1,(hb 6 (by decide)).symm.trans (hr er).2⟩
  exact run_local erase enD enH cx cy x hx hc cov eqzero restore s.phase m m

open MeasuredCodec5 (label)

theorem run_at_eq (f : Fin 10→Wire) (hf : Function.Injective f)
    (erase enD enH cx cy : Bool) (s : State) (m : List Bool)
    (hz : s.basis (f 7)=false ∧ s.basis (f 8)=false ∧ s.basis (f 9)=false)
    (hg : s.basis (f 5)=true → s.basis (f 3)=true ∧ s.basis (f 0)=true)
    (he : erase=true →
      (run (renameProgram (label f) (original enD enH cx cy)) m s).basis (f 4)=false ∧
      (run (renameProgram (label f) (original enD enH cx cy)) m s).basis (f 6)=false)
    (hr : erase=false → s.basis (f 4)=false ∧ s.basis (f 6)=false) :
    run (renameProgram (label f) (replacement erase enD enH cx cy)) m s=
      run (renameProgram (label f) (original enD enH cx cy)) m s := by
  have hp := support erase enD enH cx cy
  apply FirstNonzeroCodec.renamed_eq f hf _ _ hp.1 hp.2
  apply run_eq erase enD enH cx cy
  · exact hz
  · exact hg
  · intro er
    have pp := run_rename_pool (label f) (Finset.range 10)
      (FirstNonzeroCodec.label_inj' f hf) (original enD enH cx cy) hp.2 m
      ⟨s.phase,fun q => s.basis (label f q)⟩ s rfl (fun _ _ => rfl)
    exact ⟨(pp.2 4 (by decide)).symm.trans (he er).1,
      (pp.2 6 (by decide)).symm.trans (he er).2⟩
  · exact hr

open Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog

def ports (L : ControlledPointLayout) (k : Nat) : Fin 10→Wire :=
  ![L.point.finite,L.point.x.getD k 0,yLow L,L.control,L.doubleSelect,L.genericSelect,
    L.core.equalNegY,L.core.poolWire 0,L.core.poolWire 1,L.core.poolWire 2]

theorem ports_injective (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k<256) : Function.Injective (ports L k) := by
  have nd := dh_nodup L hw hn k hk
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd
  intro a b eq
  fin_cases a <;> fin_cases b <;> simp_all [ports,eq_comm]

theorem original_at (f : Fin 10→Wire) (enD enH cx cy : Bool) :
    renameProgram (label f) (original enD enH cx cy)=
      DHGadget.gadget (f 3) (f 0) (f 5) (f 4) (f 6) (f 1) (f 2) (f 7) (f 8) (f 9)
        enD enH cx cy := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;> rfl

def program (L : ControlledPointLayout) (C : Point) (cy : Fp) (erase : Bool) : Program :=
  renameProgram (label (ports L (DHClass.kx C)))
    (replacement erase (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C))

theorem boundary_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (erase : Bool) (R : Point) (b D G H : Bool)
    (cov : G=true → b=true ∧ pointFinite R=true)
    (restore : erase=false → D=false ∧ H=false) (s : State) (m : List Bool)
    (v : PointDialogBoundary L R b (dialogFlagState L false D G false false H false) s.basis)
    (he : erase=true → (run (clrDH L C cy) m s).basis L.doubleSelect=false ∧
      (run (clrDH L C cy) m s).basis L.core.equalNegY=false) :
    run (program L C cy erase) m s=run (clrDH L C cy) m s := by
  have old : renameProgram (label (ports L (DHClass.kx C)))
      (original (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C))=clrDH L C cy :=
    original_at _ _ _ _ _
  rw [program,←old]
  apply run_at_eq _ (ports_injective L hw hn _ (DHClass.kx_lt C))
  · have zero (i : Nat) (hi : i<3) : s.basis (L.core.poolWire i)=false := by
      apply (regValue_zero _ _).mp v.clean
      apply List.mem_of_mem_take (i:=3)
      rw [pool_block L hw 3 (by omega)]
      exact List.mem_map.mpr ⟨i,List.mem_range'_1.mpr ⟨by omega,by omega⟩,rfl⟩
    exact ⟨zero 0 (by decide),zero 1 (by decide),zero 2 (by decide)⟩
  · have hr := dialogFlagState_read L hn false D G false false H false
    have vg : s.basis L.genericSelect=G :=
      (v.flags _ (by simp [inPlaceFlags])).trans hr.2.2.1
    intro hg
    have hc := cov (vg.symm.trans hg)
    exact ⟨v.control.trans hc.1,((point_holds _ _ _).mp v.point).1.trans hc.2⟩
  · simpa only [old] using he
  · intro er
    have hr := dialogFlagState_read L hn false D G false false H false
    exact ⟨((v.flags _ (by simp [inPlaceFlags])).trans hr.2.1).trans (restore er).1,
      ((v.flags _ (by simp [inPlaceFlags])).trans hr.2.2.2.2.2.1).trans (restore er).2⟩

theorem boundary_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (erase : Bool) (R : Point) (b D G H D' H' : Bool)
    (cov : G=true → b=true ∧ pointFinite R=true)
    (clear : erase=true → D'=false ∧ H'=false)
    (restore : erase=false → D=false ∧ H=false)
    (old : Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (clrDH L C cy)
      (PointDialogBoundary L R b (dialogFlagState L false D' G false false H' false))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (program L C cy erase)
      (PointDialogBoundary L R b (dialogFlagState L false D' G false false H' false)) := by
  intro s m v
  have ho := old s m v
  rw [boundary_eq L hw hn C cy erase R b D G H cov restore s m v ?_]
  · exact ho
  · intro er
    have hr := dialogFlagState_read L hn false D' G false false H' false
    exact ⟨((ho.2.flags _ (by simp [inPlaceFlags])).trans hr.2.1).trans (clear er).1,
      ((ho.2.flags _ (by simp [inPlaceFlags])).trans hr.2.2.2.2.2.1).trans (clear er).2⟩

theorem program_support (L : ControlledPointLayout) (C : Point) (cy : Fp) (erase : Bool) :
    wires (program L C cy erase)⊆wires (clrDH L C cy) := by
  have localSub (enD enH cx cy : Bool) :
      wires (replacement erase enD enH cx cy)⊆wires (original enD enH cx cy) := by
    cases erase <;> cases enD <;> cases enH <;> cases cx <;> cases cy <;> decide
  have h := Finset.image_subset_image (f:=label (ports L (DHClass.kx C)))
    (localSub (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C))
  simpa only [program,←renameProgram_support,original_at] using h

private def physicalBool : Instr→Bool
  | .X _ => true
  | .CX a b => decide (a≠b)
  | .CCX a b c => decide (a≠b ∧ a≠c ∧ b≠c)
  | .measureX _ _ _ => true

theorem replacement_physical (erase enD enH cx cy : Bool) :
    GatePhysical (replacement erase enD enH cx cy) := by
  have all : (replacement erase enD enH cx cy).all physicalBool=true := by
    cases erase <;> cases enD <;> cases enH <;> cases cx <;> cases cy <;> decide
  intro i hi
  have h := List.all_eq_true.mp all i hi
  cases i <;> simp_all [physicalBool,PhysicalInstr,ProperGate]

theorem program_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (erase : Bool) : GatePhysical (program L C cy erase) := by
  have inj := FirstNonzeroCodec.label_inj' _ (ports_injective L hw hn _ (DHClass.kx_lt C))
  exact gatePhysical_rename_support _ _
    (fun a ha b hb eq => inj a ((support _ _ _ _ _).1 ha) b ((support _ _ _ _ _).1 hb) eq)
    (replacement_physical _ _ _ _ _)

theorem pair_counts (cx cy : Bool) :
    toffoliCount (replacement true true true cx cy)+
      toffoliCount (replacement false true true cx cy)+6≤2*toffoliCount (original true true cx cy) ∧
    measurementCount (replacement true true true cx cy)+
      measurementCount (replacement false true true cx cy)+2≤2*measurementCount (original true true cx cy) ∧
    Challenge.gateSlots (replacement true true true cx cy)+
      Challenge.gateSlots (replacement false true true cx cy)+11≤2*Challenge.gateSlots (original true true cx cy) := by
  cases cx <;> cases cy <;> decide

def wrapper (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  renameProgram (Wrapper5.U L) (Edges.finiteProgramWith L C cy (renameProgram (Wrapper5.U L) Gen)
    (program L C cy true) (program L C cy false))

theorem wrapper_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (wrapper L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  have hs := Edges.finite_specWith L hw hn R hc b (renameProgram (Wrapper5.U L) Gen)
    (Wrapper5.genericOK_relabel L hw hc Gen hGen) (program L (.some hc) cy true)
    (program L (.some hc) cy false)
    (fun R b D G H cov old => boundary_step L hw hn _ cy true R b D G H false false cov
      (fun _ => ⟨rfl,rfl⟩) (by simp) old)
    (fun R b G D H cov old => boundary_step L hw hn _ cy false R b false G false D H cov
      (by simp) (fun _ => ⟨rfl,rfl⟩) old)
  intro s m hi
  have h := hs s m hi
  unfold wrapper
  rw [Square5Placement.pool_relabel_state_eq L (Wrapper5.U L) (Wrapper5.U_pool L hw)
    (Wrapper5.U_outside L hw) _ s m hi.clean h.2.clean]
  exact h

theorem wrapper_support (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
    wires (wrapper L C cy Gen)⊆wires (Edges.wrapper L C cy Gen) := by
  have hc := program_support L C cy true
  have hr := program_support L C cy false
  simp only [wrapper,Edges.wrapper,Edges.finiteProgramWith,Edges.finiteProgram,
    wires_append,renameProgram_support]
  repeat' first
    | exact hc
    | exact hr
    | exact Finset.Subset.refl _
    | apply Finset.union_subset_union
    | apply Finset.image_subset_image

theorem wrapper_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hGen : GatePhysical Gen) :
    GatePhysical (wrapper L C cy Gen) := by
  apply gatePhysical_rename _ (Wrapper5.U L).injective
  have old := Edges.finite_physical L hw hn C cy (renameProgram (Wrapper5.U L) Gen)
    (gatePhysical_rename _ (Wrapper5.U L).injective Gen hGen)
  have hc := program_physical L hw hn C cy true
  have hr := program_physical L hw hn C cy false
  simp only [Edges.finiteProgramWith,Edges.finiteProgram,gatePhysical_append] at old ⊢
  tauto

theorem wrapper_counts (L : ControlledPointLayout) (Gen : Program) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapper L (.some hc) cy Gen)+6≤toffoliCount (Edges.wrapper L (.some hc) cy Gen) ∧
    measurementCount (wrapper L (.some hc) cy Gen)+2≤measurementCount (Edges.wrapper L (.some hc) cy Gen) ∧
    Challenge.gateSlots (wrapper L (.some hc) cy Gen)+11≤Challenge.gateSlots (Edges.wrapper L (.some hc) cy Gen) := by
  have old := original_at (ports L (DHClass.kx (.some hc))) true (exceptionBit (.some hc))
    (DHClass.cxk (.some hc)) (yBit (.some hc))
  have hd : decide (cy≠-cy)=true := by rw [cy_ne_neg hc]
  have hp := pair_counts (DHClass.cxk (.some hc)) (yBit (.some hc))
  have ot := (renameProgram_counts (label (ports L (DHClass.kx (.some hc))))
    (original true (exceptionBit (.some hc)) (DHClass.cxk (.some hc)) (yBit (.some hc))))
  have os := rename_gateSlots (label (ports L (DHClass.kx (.some hc))))
    (original true (exceptionBit (.some hc)) (DHClass.cxk (.some hc)) (yBit (.some hc)))
  rw [old] at ot os
  have oldEq : DHGadget.gadget (ports L (DHClass.kx (.some hc)) 3)
      (ports L (DHClass.kx (.some hc)) 0) (ports L (DHClass.kx (.some hc)) 5)
      (ports L (DHClass.kx (.some hc)) 4) (ports L (DHClass.kx (.some hc)) 6)
      (ports L (DHClass.kx (.some hc)) 1) (ports L (DHClass.kx (.some hc)) 2)
      (ports L (DHClass.kx (.some hc)) 7) (ports L (DHClass.kx (.some hc)) 8)
      (ports L (DHClass.kx (.some hc)) 9) true (exceptionBit (.some hc))
      (DHClass.cxk (.some hc)) (yBit (.some hc))=clrDH L (.some hc) cy := by
    simp only [clrDH,hd]; rfl
  rw [oldEq] at ot os
  have he := NoThreeTorsion.enabled hc
  simp only [he,Bool.toNat_true] at hp ot os
  simp only [wrapper,Edges.wrapper,Edges.finiteProgramWith,Edges.finiteProgram,program,
    toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,renameProgram_counts,
    rename_gateSlots,hd,he]
  omega

theorem boundary_work (L : ControlledPointLayout) : L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,
    List.count_cons,List.count_nil] at h1 ht ⊢
  omega

theorem boundary_unique (L : ControlledPointLayout) (P Q : Program)
    (hp : wires P⊆L.dialogUsedWires.toFinset) (hq : wires Q⊆L.dialogUsedWires.toFinset)
    (s : State) (m : List Bool) (R : Point) (b : Bool)
    (pv : PointDialogBoundary L R b (fun _ => false) (run P m s).basis)
    (qv : PointDialogBoundary L R b (fun _ => false) (run Q m s).basis)
    (phase : (run P m s).phase=(run Q m s).phase) : run P m s=run Q m s := by
  apply State.extensionality
  · exact phase
  funext w
  have ppoint := (point_holds _ _ _).mp pv.point
  have qpoint := (point_holds _ _ _).mp qv.point
  by_cases hf : w=L.point.finite
  · subst w; exact ppoint.1.trans qpoint.1.symm
  by_cases hx : w∈L.point.x
  · exact (regValue_eq_iff _ _ _).mp (ppoint.2.1.trans qpoint.2.1.symm) w hx
  by_cases hy : w∈L.point.y
  · exact (regValue_eq_iff _ _ _).mp (ppoint.2.2.trans qpoint.2.2.symm) w hy
  by_cases hc : w=L.control
  · subst w; exact pv.control.trans qv.control.symm
  by_cases hflags : w∈L.inPlaceFlags
  · exact (pv.flags w hflags).trans (qv.flags w hflags).symm
  by_cases hw : w∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (pv.clean.trans qv.clean.symm) w hw
  have outside : w∉L.dialogUsedWires.toFinset := by
    simp [dialogUsedWires,PointAddLayout.pointWires,hf,hx,hy,hc,hflags,hw]
  exact (run_preserves_outside P m s w (fun used => outside (hp used))).trans
    (run_preserves_outside Q m s w (fun used => outside (hq used))).symm

theorem full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen)
    (hG : wires Gen⊆(OB5Support.genericSites L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} wrapper L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (boundary_work L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  have old := Edges.wrapper_spec L hw hn R hc b Gen hGen s m hi
  have new := wrapper_spec L hw hn R hc b Gen hGen s m hi
  have oldSupport := (Edges.wrapper_support L hw hn (.some hc) cy Gen hG).trans
    (WrapperOB5.support_used L hw)
  rw [boundary_unique L _ _ ((wrapper_support L (.some hc) cy Gen).trans oldSupport)
    oldSupport s m _ b new.2 old.2 (new.1.trans old.1.symm)]
  exact Edges.full_spec L hw hn R hc b Gen hGen hG s m hs

end ECDSAAdd.Entrant.MeasuredDH
end

-- ===== merged module ECDSAAdd.Submission.Entrant.LocalWireModel =====
section
namespace ECDSAAdd.Entrant.LocalWireModel
open Arithmetic MeasuredCodec5

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

theorem reg_bit (r : List Wire) (s : BasisState) (q : Nat) (hq : q<r.length) :
    (regValue r s).testBit q=s (r.getD q 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq,←regValue_bit r q 0 s hq]
  cases s (r.getD q 0) <;> rfl

theorem range_bit (n : Nat) (s : BasisState) (q : Nat) (hq : q<n) :
    (regValue (List.range n) s).testBit q=s q := by
  rw [reg_bit _ _ _ (by simpa using hq)]
  simp [List.getD_eq_getElem?_getD,hq]

theorem model_eq (n : Nat) (P Q : Program) (hP : wires P⊆Finset.range n)
    (hQ : wires Q⊆Finset.range n) (s : State) (m : List Bool) (x : Nat)
    (hb : ∀q∈Finset.range n,s.basis q=bitsOf x q)
    (h : run P m ⟨s.phase,bitsOf x⟩=run Q m ⟨s.phase,bitsOf x⟩) :
    run P m s=run Q m s := by
  have p:=pool_run_agrees P (Finset.range n) hP m s ⟨s.phase,bitsOf x⟩ rfl hb
  have q:=pool_run_agrees Q (Finset.range n) hQ m s ⟨s.phase,bitsOf x⟩ rfl hb
  apply State.extensionality
  · exact p.1.trans ((congrArg State.phase h).trans q.1.symm)
  · funext w
    by_cases hw:w∈Finset.range n
    · exact (p.2 w hw).trans ((congrArg (fun t : State => t.basis w) h).trans (q.2 w hw).symm)
    · exact (run_preserves_outside P m s w (fun hp=>hw (hP hp))).trans
        (run_preserves_outside Q m s w (fun hq=>hw (hQ hq))).symm

def label {n : Nat} (f : Fin n→Wire) (q : Wire) : Wire := if h:q<n then f ⟨q,h⟩ else q

theorem label_injective {n : Nat} (f : Fin n→Wire) (hf : Function.Injective f) :
    ∀a∈Finset.range n,∀b∈Finset.range n,label f a=label f b → a=b := by
  intro a ha b hb e
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have eq : f ⟨a,ha'⟩=f ⟨b,hb'⟩ := by simpa only [label,dif_pos ha',dif_pos hb'] using e
  exact congrArg Fin.val (hf eq)

theorem renamed_eq {n : Nat} (f : Fin n→Wire) (hf : Function.Injective f)
    (P Q : Program) (hp:wires P⊆Finset.range n) (hq:wires Q⊆Finset.range n)
    (s : State) (m : List Bool)
    (he:run P m ⟨s.phase,fun q=>s.basis (label f q)⟩=
        run Q m ⟨s.phase,fun q=>s.basis (label f q)⟩) :
    run (renameProgram (label f) P) m s=run (renameProgram (label f) Q) m s := by
  let t:State:=⟨s.phase,fun q=>s.basis (label f q)⟩
  have pp:=run_rename_pool (label f) (Finset.range n) (label_injective f hf) P hp m t s rfl (fun _ _=>rfl)
  have qq:=run_rename_pool (label f) (Finset.range n) (label_injective f hf) Q hq m t s rfl (fun _ _=>rfl)
  apply State.extensionality
  · exact pp.1.trans ((congrArg State.phase he).trans qq.1.symm)
  · funext z
    by_cases hz:z∈(Finset.range n).image (label f)
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hz
      exact (pp.2 q hq).trans ((congrArg (fun st:State=>st.basis q) he).trans (qq.2 q hq).symm)
    · have absent (R : Program) (hr : wires R⊆Finset.range n) : z∉wires (renameProgram (label f) R) := by
        rw [renameProgram_support]
        intro hh
        obtain ⟨q,hqin,eq⟩:=Finset.mem_image.mp hh
        exact hz (Finset.mem_image.mpr ⟨q,hr hqin,eq⟩)
      exact (run_preserves_outside _ m s z (absent P hp)).trans
        (run_preserves_outside _ m s z (absent Q hq)).symm

theorem run_write_outside (p : Program) (port : Wire) (hp : port∉wires p)
    (s : State) (b : Bool) (m : List Bool) :
    run p m ⟨s.phase,writeBit s.basis port b⟩=
      ⟨(run p m s).phase,writeBit (run p m s).basis port b⟩ := by
  have loc := pool_run_agrees p (wires p) (by rfl) m
    ⟨s.phase,writeBit s.basis port b⟩ s rfl (by
      intro w hw
      exact Function.update_of_ne (show w≠port from fun he => hp (he ▸ hw)) _ _)
  apply State.extensionality
  · exact loc.1
  · funext w
    by_cases hw : w∈wires p
    · change _ = writeBit (run p m s).basis port b w
      rw [show writeBit (run p m s).basis port b w=(run p m s).basis w from
        Function.update_of_ne (show w≠port from fun he => hp (he ▸ hw)) _ _]
      exact loc.2 w hw
    · rw [run_preserves_outside p m _ w hw]
      by_cases he : w=port
      · subst w; simp [writeBit]
      · simp only [writeBit,Function.update_of_ne he]
        exact (run_preserves_outside p m s w hw).symm

theorem rename_toggle {n : Nat} (f : Fin n→Wire) (hf : Function.Injective f)
    (P : Program) (hp : wires P⊆Finset.range n) (target : Fin n) (s : State) (m : List Bool) (z : Bool)
    (he : run P m ⟨s.phase,fun q=>s.basis (label f q)⟩=
      ⟨s.phase,writeBit (fun q=>s.basis (label f q)) target.val (s.basis (f target) ^^ z)⟩) :
    run (renameProgram (label f) P) m s=
      ⟨s.phase,writeBit s.basis (f target) (s.basis (f target) ^^ z)⟩ := by
  have pp := run_rename_pool (label f) (Finset.range n) (label_injective f hf) P hp m
    ⟨s.phase,fun q=>s.basis (label f q)⟩ s rfl (fun _ _=>rfl)
  rw [he] at pp
  apply State.extensionality
  · exact pp.1
  · funext w
    by_cases hw : w∈(Finset.range n).image (label f)
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hw
      have ht : label f target.val=f target := by simp [label,target.isLt]
      have same : label f q=f target ↔ q=target.val := by
        constructor
        · intro e
          exact label_injective f hf q hq target.val (Finset.mem_range.mpr target.isLt) (e.trans ht.symm)
        · intro e; subst q; exact ht
      rw [pp.2 q hq]
      simp only [writeBit,Function.update_apply]
      by_cases eq : q=target.val
      · simp [eq,ht]
      · simp [eq,show label f q≠f target from fun h=>eq (same.mp h)]
    · have noP : w∉wires (renameProgram (label f) P) := by
        rw [renameProgram_support]
        intro h
        obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
        exact hw (Finset.mem_image.mpr ⟨q,hp hq,e⟩)
      have ne : w≠f target := by
        intro e
        apply hw
        refine Finset.mem_image.mpr ⟨target.val,Finset.mem_range.mpr target.isLt,?_⟩
        simpa [label,target.isLt] using e.symm
      rw [run_preserves_outside _ m s w noP]
      simp [writeBit,ne]

theorem listPorts_injective (r : List Wire) (hn : r.Nodup) {n : Nat} (hl : r.length=n) :
    Function.Injective (fun q : Fin n => r.getD q.val 0) := by
  intro a b eq
  have ha : a.val<r.length := by rw [hl]; exact a.isLt
  have hb : b.val<r.length := by rw [hl]; exact b.isLt
  dsimp only at eq
  rw [List.getD_eq_getElem _ _ ha,List.getD_eq_getElem _ _ hb] at eq
  exact Fin.ext (hn.getElem_inj_iff.mp eq)

end ECDSAAdd.Entrant.LocalWireModel
end

-- ===== merged module ECDSAAdd.Submission.Entrant.TrimSq3 =====
section
/-! TrimSquare3 (debias): the first signed-row lowest carry of every plain `tsq2` leaf square is a copy
(make and clear), proved against the library; used for the two plain leaves of each `kg` group. -/

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.TrimSquare3
open ECDSAAdd ECDSAAdd.Arithmetic RecordedQuantum

/-- `addInPlace` whose lowest majority/erase pair is a copy of the lowest source bit. -/
def addDrop : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
      [.CX a c]++addInPlace (a'::as) (b'::bs) cs c++[.CX a c]++[.CX a b,.CX cin b]
  | x, y, carry, cin => addInPlace x y carry cin

theorem carryBit_of_copy (A Y C : Bool) (h : ((Y^^A) && (C^^A))=false) : carryBit A Y C=A := by
  cases A <;> cases Y <;> cases C <;> simp_all [carryBit]

def insF (K : Nat) (l : List Bool) : List Bool := (l++List.replicate K false).take K++false::l.drop K

theorem insF_take (K : Nat) (l : List Bool) : (insF K l).take K=(l++List.replicate K false).take K := by
  have : ((l++List.replicate K false).take K).length=K := by simp
  simp [insF,List.take_append_of_le_length (le_of_eq this.symm),this]

theorem insF_drop (K : Nat) (l : List Bool) : (insF K l).drop K=false::l.drop K := by
  have : ((l++List.replicate K false).take K).length=K := by simp
  simp [insF,List.drop_append_of_le_length (le_of_eq this.symm),this]

theorem insF_length (K : Nat) (l : List Bool) (h : K≤l.length) : (insF K l).length=l.length+1 := by
  simp [insF]; omega

theorem run_padTake (P : Program) (l : List Bool) (K : Nat) (s : State) (hK : measurementCount P=K) :
    run P ((l++List.replicate K false).take K) s=run P l s := by
  rw [← hK,run_take,run_pad_false]

theorem td (L1 L2 : List Bool) (n : Nat) (h : L1.length=n) :
    (L1++L2).take n=L1 ∧ (L1++L2).drop n=L2 := by subst h; simp

theorem glue (Pre X X' Post : Program) (K : Nat) (hK : K≤measurementCount X)
    (hm : measurementCount X'=measurementCount X+1) (s : State)
    (h : ∀ rP rX, run X rX (run Pre rP s)=run X' (insF K rX) (run Pre rP s)) (r : List Bool) :
    ∃ R, run (Pre++X++Post) r s=run (Pre++X'++Post) R s := by
  rw [← run_pad_false _ r (measurementCount Pre+measurementCount X)]
  generalize hr0 : r++List.replicate (measurementCount Pre+measurementCount X) false=r0
  have hl : measurementCount Pre+measurementCount X≤r0.length := by rw [← hr0]; simp
  have ta : (r0.take (measurementCount Pre)).length=measurementCount Pre := by simp; omega
  have hrX : ((r0.drop (measurementCount Pre)).take (measurementCount X)).length=measurementCount X := by
    simp; omega
  have li := insF_length K ((r0.drop (measurementCount Pre)).take (measurementCount X)) (by omega)
  refine ⟨r0.take (measurementCount Pre)++
    (insF K ((r0.drop (measurementCount Pre)).take (measurementCount X))++
      r0.drop (measurementCount Pre+measurementCount X)),?_⟩
  rw [List.append_assoc Pre,List.append_assoc Pre,run_append Pre,run_append Pre,run_append X,run_append X',
    (td _ _ _ ta).1,(td _ _ _ ta).2,hm,(td _ _ _ (by rw [li,hrX])).1,(td _ _ _ (by rw [li,hrX])).2,
    List.drop_drop,h]

theorem cx_run (a c : Wire) (m : List Bool) (s : State) :
    run [.CX a c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis a)⟩ := rfl

theorem addDrop_run (a a' b b' c cin : Wire) (as bs cs : List Wire) (hnd : [a,b,cin,c].Nodup)
    (hrec : (c::((a'::as)++(b'::bs)++cs)).Nodup) (hl : (a'::as).length=(b'::bs).length)
    (hcl : cs.length+1=(b'::bs).length) (ha : a∉b'::bs) (rX : List Bool) (s : State)
    (hcopy : ((s.basis b^^s.basis a) && (s.basis cin^^s.basis a))=false)
    (hc0 : s.basis c=false) (hclean : ∀q∈cs,s.basis q=false) :
    run (addDrop (a::a'::as) (b::b'::bs) (c::cs) cin) rX s=
      run (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin)
        (insF (measurementCount (addInPlace (a'::as) (b'::bs) cs c)) rX) s := by
  have hm : run (majority a b cin c) [] s=run [.CX a c] [] s := by
    rw [majority_correct a b cin c hnd,cx_run,carryBit_of_copy _ _ _ hcopy]
  have m0 : measurementCount (majority a b cin c)=0 := by simp [majority,measurementCount]
  set REC := addInPlace (a'::as) (b'::bs) cs c
  set K := measurementCount REC
  simp only [addDrop,addInPlace]
  rw [show [Instr.CX a c]++REC++[Instr.CX a c]++[Instr.CX a b,Instr.CX cin b]=
      ([Instr.CX a c]++REC)++([Instr.CX a c]++[Instr.CX a b,Instr.CX cin b]) by simp only [List.append_assoc],
    show majority a b cin c++REC++eraseCarry a b cin c++[Instr.CX a b,Instr.CX cin b]=
      (majority a b cin c++REC)++(eraseCarry a b cin c++[Instr.CX a b,Instr.CX cin b]) by
      simp only [List.append_assoc]]
  have mK1 : measurementCount ([Instr.CX a c]++REC)=K := rfl
  have mK2 : measurementCount (majority a b cin c++REC)=K := by
    rw [measurementCount_append,m0,Nat.zero_add]
  rw [run_append ([Instr.CX a c]++REC),run_append (majority a b cin c++REC),mK1,mK2,insF_take,insF_drop,
    run_padTake _ _ _ _ mK2,← run_take (majority a b cin c++REC),mK2]
  rw [run_append (majority a b cin c) REC,run_append [Instr.CX a c] REC,m0,List.take_zero,List.drop_zero,hm]
  have m1 : measurementCount [Instr.CX a c]=0 := rfl
  rw [m1,List.take_zero,List.drop_zero]
  generalize hu : run [Instr.CX a c] [] s=u
  have uc : u.basis c=s.basis a := by rw [← hu]; simp [run,writeBit,hc0]
  have hac : a≠c := by simp at hnd; tauto
  have ua : u.basis a=s.basis a := by
    rw [← hu]; simp [run,writeBit,Function.update,hac]
  have ucl : ∀q∈cs,u.basis q=false := by
    intro q hq; rw [← hu]
    have : q≠c := by intro e; subst e; simp at hrec; tauto
    simp [run,writeBit,Function.update,this,hclean q hq]
  have nd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := hrec
  generalize hw : run REC (rX.take K) u=w
  have pres := (addInPlace_correct (a'::as) (b'::bs) cs c nd' hl hcl u (rX.take K) ucl).2.1
  have wc : w.basis c=s.basis a := by
    rw [← hw,pres c (by simp at hrec ⊢; tauto),uc]
  have wa : w.basis a=s.basis a := by rw [← hw,pres a ha,ua]
  have e1 : eraseCarry a b cin c=[.measureX c [] [.CZ a b,.CZ a cin,.CZ b cin]] := rfl
  rw [e1]
  have key : run [Instr.CX a c] [] w=run [Instr.measureX c [] [.CZ a b,.CZ a cin,.CZ b cin]] [false] w := by
    simp only [run,List.headD_cons,List.tail_cons,measureAndCorrect,correct,Bool.false_and,Bool.xor_false,
      Bool.false_eq_true,if_false]
    congr 1
    simp [writeBit,wc,wa]
  rw [run_append [Instr.CX a c],run_append [Instr.measureX c [] [.CZ a b,.CZ a cin,.CZ b cin]]]
  simp only [measurementCount,List.take_zero,List.drop_zero,List.take_succ_cons,List.drop_succ_cons,
    List.take_zero,Nat.add_zero]
  rw [key]

theorem top_keep (xs dst : List Wire) (m : List Bool) (s : State) (q : Wire) (hq : q∉dst) :
    (run (signedSquareTop xs dst) m s).basis q=s.basis q := by
  induction xs generalizing dst with
  | nil => rfl
  | cons x xs ih =>
    match xs, dst with
    | [], [] => rfl
    | [], [_] => rfl
    | [], _::z::_ =>
      simp only [signedSquareTop,run,writeBit]
      have : q≠z := by intro e; subst e; simp at hq
      simp [Function.update,this]
    | _::_, [] => rfl
    | _::_, [_] => rfl
    | y::ys, a::b::dst =>
      simp only [signedSquareTop]
      exact ih _ (by intro h; exact hq (by simp [h]))

theorem sub_nodup (c : Wire) (xs D dst pad carry : List Wire) (hD : D.Sublist dst)
    (h : (c::xs++dst++pad++carry).Nodup) : (c::xs++D++pad++carry).Nodup :=
  (((((List.Sublist.refl (c::xs)).append hD).append (List.Sublist.refl pad)).append
    (List.Sublist.refl carry))).nodup h

theorem rowClear_keep (c : Wire) (xs D pad carry : List Wire)
    (hnd : (c::xs++D++pad++carry).Nodup) (hd : D.length=xs.length+1) (hp : 1≤pad.length)
    (hc : xs.length≤carry.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) (q : Wire) (hq : q∉D) :
    (run (signedSquareRowClear c xs D pad carry) m s).basis q=s.basis q := by
  have ndc : (c::D).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have Dn : D.Nodup := (List.nodup_cons.mp ndc).2
  have cD : c∉D := (List.nodup_cons.mp ndc).1
  have cDt : c∉D.take xs.length := fun h => cD (List.mem_of_mem_take h)
  have Dtn : (D.take xs.length).Nodup := (List.take_sublist _ _).nodup Dn
  have nda : (c::((xs++pad.take 1)++D++carry.take xs.length)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    have t1 := (List.take_sublist 1 pad).count_le w
    have t2 := (List.take_sublist xs.length carry).count_le w
    simp only [List.count_cons,List.count_append] at h t1 t2 ⊢
    omega
  have carryD : ∀w∈carry,w∉D := by
    intro w hw hD
    have h := List.nodup_iff_count.mp hnd w
    have a := List.count_pos_iff.mpr hw
    have b := List.count_pos_iff.mpr hD
    simp only [List.count_cons,List.count_append] at h; omega
  have hs : (xs++pad.take 1).length=D.length := by simp [hd]; omega
  have hk : (carry.take xs.length).length+1=D.length := by simp [hd]; omega
  let P : State → Prop := fun st => ∀ w, w∉D → st.basis w=s.basis w
  have pX (E : List Wire) (hE : E.Sublist D) (st : State) (r : List Bool) (h : P st) :
      P (run (xorWhenFalse c E) r st) := by
    intro w hw
    rw [xorWhenFalse_outside c E (hE.nodup Dn) (fun h => cD (hE.subset h)) st r w
      (fun h => hw (hE.subset h))]
    exact h w hw
  have pN (st : State) (r : List Bool) (h : P st) : P (run (notRegister D) r st) := by
    intro w hw; rw [notRegister_correct D Dn]; simp only [hw,if_false]; exact h w hw
  have pA (st : State) (r : List Bool) (h : P st) :
      P (run (addInPlace (xs++pad.take 1) D (carry.take xs.length) c) r st) := by
    have ac := addInPlace_correct (xs++pad.take 1) D (carry.take xs.length) c nda hs hk st r
      (fun w hw => by rw [h w (carryD w (List.mem_of_mem_take hw))]; exact hclean w (List.mem_of_mem_take hw))
    intro w hw; rw [ac.2.1 w hw]; exact h w hw
  have p0 : P s := fun _ _ => rfl
  unfold signedSquareRowClear
  rw [run_append,run_append,run_append,run_append]
  exact pX _ (List.take_sublist _ _) _ _ (pN _ _ (pA _ _ (pN _ _ (pX D (List.Sublist.refl D) _ _ p0)))) q hq

theorem rowsClear_keep (xs dst pad carry : List Wire) (hnd : (xs++dst++pad++carry).Nodup)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) (q : Wire) (hq : q∉dst) :
    (run (signedSquareRowsClear xs dst pad carry) m s).basis q=s.basis q := by
  induction xs generalizing dst s m q with
  | nil => rfl
  | cons c xs ih =>
    match xs, hnd, hd, hc with
    | [], _, _, _ => rfl
    | d::tail, hnd, hd, hc =>
      simp only [List.length_cons] at hd hc
      have hD : ((dst.drop 1).take ((d::tail).length+1)).Sublist dst :=
        (List.take_sublist _ _).trans (List.drop_sublist _ _)
      have nd2 : ((d::tail)++dst.drop 2++pad++carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := List.nodup_iff_count.mp hnd w
        have t := (List.drop_sublist 2 dst).count_le w
        simp only [List.count_cons,List.count_append] at h t ⊢
        omega
      have nd1 : (c::(d::tail)++(dst.drop 1).take ((d::tail).length+1)++pad++carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := List.nodup_iff_count.mp hnd w
        have t := hD.count_le w
        simp only [List.count_cons,List.count_append] at h t ⊢
        omega
      have carryD : ∀w∈carry,w∉dst := by
        intro w hw hD'
        have h := List.nodup_iff_count.mp hnd w
        have a := List.count_pos_iff.mpr hw
        have b := List.count_pos_iff.mpr hD'
        simp only [List.count_cons,List.count_append] at h; omega
      simp only [signedSquareRowsClear]
      rw [run_append]
      have keep1 (w : Wire) (hw : w∉dst) := ih (dst.drop 2) nd2 (by simp; omega) (by simp; omega) s
        (m.take (measurementCount (signedSquareRowsClear (d::tail) (dst.drop 2) pad carry))) hclean w
        (fun h => hw (List.mem_of_mem_drop h))
      rw [rowClear_keep c (d::tail) _ pad carry nd1 (by simp; omega) hp (by simp; omega) _ _
        (fun w hw => by rw [keep1 w (carryD w hw)]; exact hclean w hw) q (fun h => hq (hD.subset h)),
        keep1 q hq]

theorem bit1_of_diag (y0 y1 x0 x1 : Wire) (ys xt : List Wire) (st : BasisState) (X : Nat)
    (hX : regValue (x0::x1::xt) st=X)
    (h : regValue (y0::y1::ys) st=(X^2+signedDiagValue X (x0::x1::xt).length)%2^(y0::y1::ys).length) :
    st y1=(st x0 ^^ st x1) := by
  have ey : regValue (y0::y1::ys) st=(st y0).toNat+2*((st y1).toNat+2*regValue ys st) := by
    cases h0 : st y0 <;> cases h1 : st y1 <;> simp [regValue,h0,h1]
  have ex : X=(st x0).toNat+2*((st x1).toNat+2*regValue xt st) := by
    rw [← hX]; cases h0 : st x0 <;> cases h1 : st x1 <;> simp [regValue,h0,h1]
  have d4 : 4∣2^(y0::y1::ys).length := by
    have : 2^(y0::y1::ys).length=4*2^ys.length := by
      simp only [List.length_cons,pow_succ]; ring
    rw [this]; exact Nat.dvd_mul_right 4 _
  have dg : signedDiagValue X (x0::x1::xt).length%4=X%4 := by
    unfold signedDiagValue
    simp only [List.length_cons,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false]
    generalize (2^(xt.length+1+1-1)-1-X%2^(xt.length+1+1-1))=M
    have : 2^(xt.length+1+1)=4*2^xt.length := by simp only [pow_succ]; ring
    rw [this,show M*(4*2^xt.length)=4*(M*2^xt.length) by ring,Nat.add_mul_mod_self_left]
  have xm : X%4=(st x0).toNat+2*(st x1).toNat := by
    rw [ex]; cases st x0 <;> cases st x1 <;> simp <;> omega
  have sq : X^2%4=(st x0).toNat := by
    rw [Nat.pow_mod,xm]; cases st x0 <;> cases st x1 <;> rfl
  have vm : regValue (y0::y1::ys) st%4=(st y0).toNat+2*(st y1).toNat := by
    rw [ey]; cases st y0 <;> cases st y1 <;> simp <;> omega
  have key : regValue (y0::y1::ys) st%4=(X^2+X)%4 := by
    rw [h,Nat.mod_mod_of_dvd _ d4,Nat.add_mod,dg,← Nat.add_mod]
  rw [vm,Nat.add_mod,sq,xm] at key
  cases h0 : st x0 <;> cases h1 : st x1 <;> cases hy0 : st y0 <;> cases hy1 : st y1 <;>
    simp_all

def row3 (c : Wire) (xs D pad carry : List Wire) : Program :=
  xorWhenFalse c (D.take xs.length)++addDrop (xs++pad.take 1) D (carry.take xs.length) c++xorWhenFalse c D

def rows3 : List Wire → List Wire → List Wire → List Wire → Program
  | c::d::tail, dst, pad, carry =>
      row3 c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry++
        signedSquareRows (d::tail) (dst.drop 2) pad carry
  | xs, dst, pad, carry => signedSquareRows xs dst pad carry

def rowClear3 (c : Wire) (xs D pad carry : List Wire) : Program :=
  xorWhenFalse c D++(notRegister D++(addDrop (xs++pad.take 1) D (carry.take xs.length) c++
    (notRegister D++xorWhenFalse c (D.take xs.length))))

def rowsClear3 : List Wire → List Wire → List Wire → List Wire → Program
  | c::d::tail, dst, pad, carry =>
      signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++
        rowClear3 c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry
  | xs, dst, pad, carry => signedSquareRowsClear xs dst pad carry

/-- Square make with both dead lowest carries (first signed row and diagonal) copied. -/
def tsq3 (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  rows3 xs dst pad carry++signedSquareTop xs dst++
    (notRegister dst++TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++notRegister dst)

def tsqc3 (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++signedSquareTop xs dst++
    rowsClear3 xs dst pad carry

/-- Shapes of the first signed row's operands. -/
theorem row_shape (x0 x1 : Wire) (xt dst pad carry : List Wire)
    (hd : dst.length=2*(x0::x1::xt).length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    ∃ y0 y1 y2 Dt a' as c0 cs, (∃ yr, dst=y0::y1::y2::yr) ∧
      (dst.drop 1).take ((x1::xt).length+1)=y1::y2::Dt ∧ (y1::y2::Dt).Sublist (dst.drop 1) ∧
      (x1::xt)++pad.take 1=x1::a'::as ∧ carry.take (x1::xt).length=c0::cs ∧
      (a'::as).length=(y2::Dt).length ∧ cs.length+1=(y2::Dt).length := by
  obtain ⟨y0,y1,y2,yr,rfl⟩ : ∃ y0 y1 y2 yr, dst=y0::y1::y2::yr := by
    match dst, hd with
    | y0::y1::y2::yr, _ => exact ⟨y0,y1,y2,yr,rfl⟩
    | [], h => simp at h
    | [_], h => simp at h; try omega
    | [_,_], h => simp at h; try omega
  obtain ⟨p0,pt,rfl⟩ : ∃ p0 pt, pad=p0::pt := by
    match pad, hp with
    | p0::pt, _ => exact ⟨p0,pt,rfl⟩
  obtain ⟨c0,cr,rfl⟩ : ∃ c0 cr, carry=c0::cr := by
    match carry, hc with
    | c0::cr, _ => exact ⟨c0,cr,rfl⟩
    | [], h => simp at h hd
  obtain ⟨a',as,has⟩ : ∃ a' as, xt++[p0]=a'::as := by
    cases xt with
    | nil => exact ⟨p0,[],rfl⟩
    | cons x xs => exact ⟨x,xs++[p0],rfl⟩
  simp only [List.length_cons] at hd hc
  refine ⟨y0,y1,y2,yr.take xt.length,a',as,c0,cr.take xt.length,⟨yr,rfl⟩,?_,?_,?_,?_,?_,?_⟩
  · simp
  · simp only [List.drop_one,List.tail_cons]
    exact List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.take_sublist _ _))
  · simp [has]
  · simp
  · have := congrArg List.length has
    simp at this ⊢; omega
  · simp at hc ⊢; omega

theorem tsq3_exists (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hc0 : regValue carry s.basis=0) :
    ∃ R, run (tsq3 xs dst pad carry cin) records s=run (TrimSquare.tsq2 xs dst pad carry cin) R s := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt, xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,Dt,a',as,c0,cs,hy0,hD,hDs,hsrc,hcy,hl,hcl⟩ := row_shape x0 x1 xt dst pad carry hd hp hc
  have hDsub : (y1::y2::Dt).Sublist dst := hDs.trans (List.drop_sublist _ _)
  have hcsub : (c0::cs).Sublist carry := by rw [← hcy]; exact List.take_sublist _ _
  have y1d : y1∈dst := hDsub.subset List.mem_cons_self
  have cnt := fun w => List.nodup_iff_count.mp hn w
  -- the four control wires are distinct
  have m1 : x1∈x0::x1::xt := by simp
  have m0 : x0∈x0::x1::xt := by simp
  have mc0 : c0∈carry := hcsub.subset List.mem_cons_self
  have disj (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈dst) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h a; omega
  have disjc (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h a; omega
  have disjdc (w : Wire) (h1 : w∈dst) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h; omega
  have x01 : x0≠x1 := by
    intro e; have h := cnt x0; simp only [List.count_cons,List.count_append,e] at h; simp at h; omega
  have n1 : x1≠y1 := fun e => disj x1 m1 (by rw [e]; exact y1d)
  have n2 : x1≠x0 := Ne.symm x01
  have n3 : x1≠c0 := fun e => disjc x1 m1 (by rw [e]; exact mc0)
  have n4 : y1≠x0 := fun e => disj x0 m0 (by rw [← e]; exact y1d)
  have n5 : y1≠c0 := fun e => disjdc y1 y1d (by rw [e]; exact mc0)
  have n6 : x0≠c0 := fun e => disjc x0 m0 (by rw [e]; exact mc0)
  have hnd4 : [x1,y1,x0,c0].Nodup := by
    simp [List.nodup_cons,n1,n2,n3,n4,n5,n6]
  have hrec : (c0::((a'::as)++(y2::Dt)++cs)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := cnt w
    have t1 := hcsub.count_le w
    have t2 := ((List.sublist_cons_self y1 (y2::Dt)).trans hDsub).count_le w
    have t3 : (a'::as).count w≤xt.count w+pad.count w := by
      have e : (x1::xt)++pad.take 1=x1::a'::as := hsrc
      have := congrArg (List.count w) e
      have tp := (List.take_sublist 1 pad).count_le w
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    simp only [List.count_cons,List.count_append] at h t1 t2 t3 ⊢
    omega
  have ha : x1∉y2::Dt := fun h => disj _ m1 (((List.sublist_cons_self y1 (y2::Dt)).trans hDsub).subset h)
  have carry0 : ∀q∈carry,s.basis q=false := (regValue_zero _ _).mp hc0
  have dst0 : ∀q∈dst,s.basis q=false := (regValue_zero _ _).mp h0
  set D := (dst.drop 1).take ((x1::xt).length+1)
  have Dn : D.Nodup := by
    rw [hD]; exact hDsub.nodup (by
      apply List.nodup_iff_count.mpr; intro w; have h := cnt w
      simp only [List.count_cons,List.count_append] at h; omega)
  have x0D : x0∉D := fun h => disj _ m0 (hDsub.subset (hD ▸ h))
  set Pre := xorWhenFalse x0 (D.take (x1::xt).length)
  set Post := xorWhenFalse x0 D++(signedSquareRows (x1::xt) (dst.drop 2) pad carry++
    (signedSquareTop (x0::x1::xt) dst++(notRegister dst++
      (TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++notRegister dst))))
  set K := measurementCount (addInPlace (a'::as) (y2::Dt) cs c0)
  have e3 : tsq3 (x0::x1::xt) dst pad carry cin=
      Pre++addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [tsq3,rows3,row3,Pre,Post,D,List.append_assoc]
  have e2 : TrimSquare.tsq2 (x0::x1::xt) dst pad carry cin=
      Pre++addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [TrimSquare.tsq2,signedSquareRows,signedSquareRow,Pre,Post,D,List.append_assoc]
  rw [e3,e2]
  apply glue _ _ _ _ K
  · rw [hsrc,hD,hcy]; simp [addDrop,measurementCount_append,K,measurementCount]
  · rw [hsrc,hD,hcy]; simp [addDrop,addInPlace,measurementCount_append,K,majority,eraseCarry,measurementCount]
  · intro rP rX
    have u := xorWhenFalse_correct x0 (D.take (x1::xt).length) ((List.take_sublist _ _).nodup Dn)
      (fun h => x0D (List.mem_of_mem_take h)) s rP
    rw [show xorWhenFalse x0 (D.take (x1::xt).length)=Pre from rfl] at u
    rw [u,hsrc]
    rw [hD,hcy]
    have inL (w : Wire) (h : w∈(y1::y2::Dt).take (x1::xt).length) : w∈dst :=
      hDsub.subset (List.mem_of_mem_take h)
    have y1t : y1∈(y1::y2::Dt).take (x1::xt).length := by simp
    have nx1 : x1∉(y1::y2::Dt).take (x1::xt).length := fun h => disj _ m1 (inL _ h)
    have nx0 : x0∉(y1::y2::Dt).take (x1::xt).length := fun h => disj _ m0 (inL _ h)
    apply addDrop_run x1 a' y1 y2 c0 x0 as Dt cs hnd4 hrec hl hcl ha rX
    · simp only [xorFalseBasis,y1t,nx1,nx0,if_true,if_false,dst0 y1 y1d]
      cases s.basis x0 <;> cases s.basis x1 <;> rfl
    · have : c0∉(y1::y2::Dt).take (x1::xt).length := fun h => disjdc _ (inL _ h) mc0
      simp only [xorFalseBasis,this,if_false]; exact carry0 c0 mc0
    · intro q hq
      have qc : q∈carry := hcsub.subset (List.mem_cons_of_mem _ hq)
      have : q∉(y1::y2::Dt).take (x1::xt).length := fun h => disjdc _ (inL _ h) qc
      simp only [xorFalseBasis,this,if_false]; exact carry0 q qc

theorem tsqc3_exists (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) (hi0 : s.basis cin=false) :
    ∃ R, run (tsqc3 xs dst pad carry cin) records s=run (TrimSquare.tsqc2 xs dst pad carry cin) R s := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt, xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,Dt,a',as,c0,cs,⟨yr,hdst⟩,hD,hDs,hsrc,hcy,hl,hcl⟩ := row_shape x0 x1 xt dst pad carry hd hp hc
  have hDsub : (y1::y2::Dt).Sublist dst := hDs.trans (List.drop_sublist _ _)
  have hcsub : (c0::cs).Sublist carry := by rw [← hcy]; exact List.take_sublist _ _
  have y1d : y1∈dst := hDsub.subset List.mem_cons_self
  have cnt := fun w => List.nodup_iff_count.mp hn w
  have m1 : x1∈x0::x1::xt := by simp
  have m0 : x0∈x0::x1::xt := by simp
  have mc0 : c0∈carry := hcsub.subset List.mem_cons_self
  have disj (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈dst) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h a; omega
  have disjc (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h a; omega
  have disjdc (w : Wire) (h1 : w∈dst) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h; omega
  have disjp (w : Wire) (h1 : w∈dst) (h2 : w∈pad) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h; omega
  have cind (w : Wire) (h1 : w∈dst) : w≠cin := by
    intro e; subst e; have h := cnt w; have b := List.count_pos_iff.mpr h1
    simp only [List.count_cons,List.count_append] at h; simp at h; omega
  have x01 : x0≠x1 := by
    intro e; have h := cnt x0; simp only [List.count_cons,List.count_append,e] at h; simp at h; omega
  have n1 : x1≠y1 := fun e => disj x1 m1 (by rw [e]; exact y1d)
  have n2 : x1≠x0 := Ne.symm x01
  have n3 : x1≠c0 := fun e => disjc x1 m1 (by rw [e]; exact mc0)
  have n4 : y1≠x0 := fun e => disj x0 m0 (by rw [← e]; exact y1d)
  have n5 : y1≠c0 := fun e => disjdc y1 y1d (by rw [e]; exact mc0)
  have n6 : x0≠c0 := fun e => disjc x0 m0 (by rw [e]; exact mc0)
  have hnd4 : [x1,y1,x0,c0].Nodup := by simp [List.nodup_cons,n1,n2,n3,n4,n5,n6]
  have hrec : (c0::((a'::as)++(y2::Dt)++cs)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := cnt w
    have t1 := hcsub.count_le w
    have t2 := ((List.sublist_cons_self y1 (y2::Dt)).trans hDsub).count_le w
    have t3 : (a'::as).count w≤xt.count w+pad.count w := by
      have := congrArg (List.count w) hsrc
      have tp := (List.take_sublist 1 pad).count_le w
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    simp only [List.count_cons,List.count_append] at h t1 t2 t3 ⊢
    omega
  have ha : x1∉y2::Dt := fun h => disj _ m1 (((List.sublist_cons_self y1 (y2::Dt)).trans hDsub).subset h)
  have carry0 : ∀q∈carry,s.basis q=false := (regValue_zero _ _).mp hc0
  set D := (dst.drop 1).take ((x1::xt).length+1)
  have Dn : D.Nodup := by
    rw [hD]; exact hDsub.nodup (by
      apply List.nodup_iff_count.mpr; intro w; have h := cnt w
      simp only [List.count_cons,List.count_append] at h; omega)
  have x0D : x0∉D := fun h => disj _ m0 (hDsub.subset (hD ▸ h))
  have inD (w : Wire) (h : w∈D) : w∈dst := hDsub.subset (hD ▸ h)
  have y1D : y1∈D := by rw [hD]; exact List.mem_cons_self
  -- the diagonal add, as the library program
  have ndDiag : (cin::(x0::x1::xt)++dst++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have h := cnt w
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have diagE : ∀ r1, ∃ r1', run (TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst
      (carry.take (dst.length-1)) cin) r1 s=run (mappedDiagAdd (x0::x1::xt) dst carry cin) r1' s := by
    intro r1
    obtain ⟨z0,b',bits,y,y',ys,c,cs',hz0,hdiag,hdst',hcar,_⟩ := TrimSquare.diag_shape (x0::x1::xt) dst carry hx hd hc
    rw [show z0=x0 by simpa using hz0.symm] at hdiag
    subst hdst'
    obtain ⟨hnd4',hrec',hsrc',hl',hcl',ha',hmem',hcin'⟩ :=
      TrimSquare.diag_side cin x0 (x1::xt) y y' ys pad carry b' bits c cs' hn hd hdiag hcar hc
    have sy := TrimSquare.bit0_of_square y x0 (y'::ys) (x1::xt) s.basis hval
    unfold mappedDiagAdd; rw [hdiag,hcar]
    exact ⟨_,TrimSquare.drop2_run x0 y y' c cin b' bits ys cs' hnd4' hrec' hsrc' hl' hcl' ha' r1 s
      (by rw [sy]; simp) (carry0 c (hmem' c List.mem_cons_self))
      (fun q hq => carry0 q (hmem' q (List.mem_cons_of_mem _ hq)))⟩
  set Pre := TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++
    (signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 D++notRegister D)))
  set Post := notRegister D++xorWhenFalse x0 (D.take (x1::xt).length)
  set K := measurementCount (addInPlace (a'::as) (y2::Dt) cs c0)
  have e3 : tsqc3 (x0::x1::xt) dst pad carry cin=
      Pre++addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [tsqc3,rowsClear3,rowClear3,Pre,Post,D,List.append_assoc]
  have e2 : TrimSquare.tsqc2 (x0::x1::xt) dst pad carry cin=
      Pre++addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [TrimSquare.tsqc2,signedSquareRowsClear,signedSquareRowClear,Pre,Post,D,List.append_assoc]
  rw [e3,e2]
  apply glue _ _ _ _ K
  · rw [hsrc,hD,hcy]; simp [addDrop,measurementCount_append,K,measurementCount]
  · rw [hsrc,hD,hcy]; simp [addDrop,addInPlace,measurementCount_append,K,majority,eraseCarry,measurementCount]
  · intro rP rX
    simp only [Pre]
    rw [run_append,run_append,run_append,run_append]
    generalize hr1 : List.take _ rP=r1
    obtain ⟨r1',e1⟩ := diagE r1
    rw [e1]
    have dc := mappedDiagAdd_correct cin (x0::x1::xt) dst carry ndDiag (by simp) hd hc s r1' hc0 hi0
    generalize hv1 : run (mappedDiagAdd (x0::x1::xt) dst carry cin) r1' s=v1
    rw [hv1] at dc
    have k1 (w : Wire) (hw : w∉dst) : v1.basis w=s.basis w := dc.2.2 w hw
    have b1 : v1.basis y1=(s.basis x0 ^^ s.basis x1) := by
      have xsame : regValue (x0::x1::xt) v1.basis=regValue (x0::x1::xt) s.basis :=
        regValue_congr _ _ _ (fun q hq => k1 q (fun h => disj q hq h))
      have val := dc.2.1
      rw [hval,hdst] at val
      have := bit1_of_diag y0 y1 x0 x1 (y2::yr) xt v1.basis (regValue (x0::x1::xt) s.basis) xsame
        (by rw [val])
      rw [this,k1 x0 (fun h => disj _ m0 h),k1 x1 (fun h => disj _ m1 h)]
    generalize hv2 : run (signedSquareTop (x0::x1::xt) dst) _ v1=v2
    have k2 (w : Wire) (hw : w∉dst) : v2.basis w=s.basis w := by rw [← hv2,top_keep _ _ _ _ w hw,k1 w hw]
    have b2 : v2.basis y1=v1.basis y1 := by
      rw [← hv2]
      apply run_preserves_outside
      rw [hdst]
      change y1∉wires (signedSquareTop (x1::xt) (y2::yr))
      intro h
      have := signedSquareTop_wires_subset (x1::xt) (y2::yr) h
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at this
      have nd := hn; rw [hdst] at nd
      simp only [List.cons_append,List.nodup_cons,List.nodup_append,List.mem_append,List.mem_cons,not_or] at nd
      grind
    have hd2 : (dst.drop 2).length=2*(x1::xt).length := by simp [hd]; omega
    have nd2 : ((x1::xt)++dst.drop 2++pad++carry).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have h := cnt w
      have t := (List.drop_sublist 2 dst).count_le w
      simp only [List.count_cons,List.count_append] at h t ⊢; omega
    generalize hv3 : run (signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry) _ v2=v3
    have k3 (w : Wire) (hw : w∉dst) : v3.basis w=s.basis w := by
      rw [← hv3,rowsClear_keep (x1::xt) (dst.drop 2) pad carry nd2 hd2 hp (by simp at hd hc ⊢; omega) v2 _
        (fun q hq => by rw [k2 q (fun h => disjdc q h hq)]; exact carry0 q hq) w
        (fun h => hw (List.mem_of_mem_drop h)),k2 w hw]
    have b3 : v3.basis y1=v2.basis y1 := by
      rw [← hv3]
      apply run_preserves_outside
      intro h
      have := (signedSquareRows_wires_subset (x1::xt) (dst.drop 2) pad carry hd2 (Or.inr hp)
        (by simp at hd hc ⊢; omega)).2 h
      simp only [List.mem_toFinset,List.mem_append] at this
      rcases this with ((h1|h1)|h1)|h1
      · exact disj y1 (List.mem_cons_of_mem _ h1) y1d
      · rw [hdst] at h1 hn; simp at h1
        simp only [List.cons_append,List.nodup_cons,List.nodup_append,List.mem_append,List.mem_cons,not_or] at hn
        grind
      · exact disjp y1 y1d h1
      · exact disjdc y1 y1d h1
    generalize hv4 : run (xorWhenFalse x0 D) _ v3=v4
    have xw : ∀ r, run (xorWhenFalse x0 D) r v3=⟨v3.phase,xorFalseBasis x0 D v3.basis⟩ :=
      fun r => xorWhenFalse_correct x0 D Dn x0D v3 r
    rw [xw] at hv4
    generalize hv5 : run (notRegister D) _ v4=v5
    rw [notRegister_correct D Dn] at hv5
    have k5 (w : Wire) (hw : w∉dst) : v5.basis w=s.basis w := by
      have wD : w∉D := fun h => hw (inD w h)
      rw [← hv5]; simp only [wD,if_false]; rw [← hv4]; simp only [xorFalseBasis,wD,if_false]; exact k3 w hw
    have b5 : v5.basis y1=s.basis x1 := by
      rw [← hv5]; simp only [y1D,if_true]; rw [← hv4]; simp only [xorFalseBasis,y1D,if_true]
      rw [b3,b2,b1,k3 x0 (fun h => disj _ m0 h)]
      cases s.basis x0 <;> cases s.basis x1 <;> rfl
    rw [hsrc,hD,hcy]
    apply addDrop_run x1 a' y1 y2 c0 x0 as Dt cs hnd4 hrec hl hcl ha rX
    · rw [b5,k5 x1 (fun h => disj _ m1 h),k5 x0 (fun h => disj _ m0 h)]; simp
    · rw [k5 c0 (fun h => disjdc _ h mc0)]; exact carry0 c0 mc0
    · intro q hq
      have qc : q∈carry := hcsub.subset (List.mem_cons_of_mem _ hq)
      rw [k5 q (fun h => disjdc _ h qc)]; exact carry0 q qc

theorem addDrop_gen (x y carry : List Wire) (cin : Wire) :
    addDrop x y carry cin=addInPlace x y carry cin ∨
    ∃ a a' as b b' bs c cs, x=a::a'::as ∧ y=b::b'::bs ∧ carry=c::cs := by
  unfold addDrop
  split
  · rename_i a a' as b b' bs c cs
    right; exact ⟨a,a',as,b,b',bs,c,cs,rfl,rfl,rfl⟩
  · left; rfl

theorem addDrop_physical_gen (x y carry : List Wire) (cin : Wire)
    (h : GatePhysical (addInPlace x y carry cin)) : GatePhysical (addDrop x y carry cin) := by
  rcases addDrop_gen x y carry cin with e|⟨a,a',as,b,b',bs,c,cs,rfl,rfl,rfl⟩
  · rw [e]; exact h
  · have hac : GatePhysical [Instr.CX a c] := by
      simp only [addInPlace,gatePhysical_append] at h
      intro i hi
      simp only [List.mem_singleton] at hi; subst hi
      exact h.1.1.1 _ (by simp [majority])
    simp only [addDrop,addInPlace,gatePhysical_append] at h ⊢
    exact ⟨⟨⟨hac,h.1.1.2⟩,hac⟩,h.2⟩

theorem addDrop_wires_gen (x y carry : List Wire) (cin : Wire) :
    wires (addDrop x y carry cin)⊆wires (addInPlace x y carry cin) := by
  rcases addDrop_gen x y carry cin with e|⟨a,a',as,b,b',bs,c,cs,rfl,rfl,rfl⟩
  · rw [e]
  · simp only [addDrop,addInPlace,wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    rcases hq with ((hq|hq)|hq)|hq
    · left; left; left; simp [wires,majority,Instr.wires] at hq ⊢; tauto
    · exact Or.inl (Or.inl (Or.inr hq))
    · left; left; left; simp [wires,majority,Instr.wires] at hq ⊢; tauto
    · exact Or.inr hq

theorem addDrop_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addDrop x y carry cin)≤Challenge.gateSlots (addInPlace x y carry cin) := by
  rcases addDrop_gen x y carry cin with e|⟨a,a',as,b,b',bs,c,cs,rfl,rfl,rfl⟩
  · rw [e]
  · simp only [addDrop,addInPlace,Challenge.gateSlots_append]
    simp [Challenge.gateSlots,Challenge.instructionSlots,majority,eraseCarry]
    omega

theorem tsq3_form (xs dst pad carry : List Wire) (cin : Wire) :
    (tsq3 xs dst pad carry cin=TrimSquare.tsq2 xs dst pad carry cin ∧
      tsqc3 xs dst pad carry cin=TrimSquare.tsqc2 xs dst pad carry cin) ∨
    ∃ A B A' B' x y cy c,
      tsq3 xs dst pad carry cin=A++addDrop x y cy c++B ∧
      TrimSquare.tsq2 xs dst pad carry cin=A++addInPlace x y cy c++B ∧
      tsqc3 xs dst pad carry cin=A'++addDrop x y cy c++B' ∧
      TrimSquare.tsqc2 xs dst pad carry cin=A'++addInPlace x y cy c++B' := by
  match xs with
  | [] => left; exact ⟨rfl,rfl⟩
  | [_] => left; exact ⟨rfl,rfl⟩
  | c::d::tail =>
    right
    refine ⟨xorWhenFalse c (((dst.drop 1).take ((d::tail).length+1)).take (d::tail).length),
      xorWhenFalse c ((dst.drop 1).take ((d::tail).length+1))++signedSquareRows (d::tail) (dst.drop 2) pad carry++
        signedSquareTop (c::d::tail) dst++(notRegister dst++
          TrimSquare.drop2 (mappedDiagonal (c::d::tail)) dst (carry.take (dst.length-1)) cin++notRegister dst),
      TrimSquare.drop2 (mappedDiagonal (c::d::tail)) dst (carry.take (dst.length-1)) cin++
        signedSquareTop (c::d::tail) dst++signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++
        xorWhenFalse c ((dst.drop 1).take ((d::tail).length+1))++notRegister ((dst.drop 1).take ((d::tail).length+1)),
      notRegister ((dst.drop 1).take ((d::tail).length+1))++
        xorWhenFalse c (((dst.drop 1).take ((d::tail).length+1)).take (d::tail).length),
      (d::tail)++pad.take 1,(dst.drop 1).take ((d::tail).length+1),carry.take (d::tail).length,c,
      ?_,?_,?_,?_⟩
    · simp only [tsq3,rows3,row3,List.append_assoc]
    · simp only [TrimSquare.tsq2,signedSquareRows,signedSquareRow,List.append_assoc]
    · simp only [tsqc3,rowsClear3,rowClear3,List.append_assoc]
    · simp only [TrimSquare.tsqc2,signedSquareRowsClear,signedSquareRowClear,List.append_assoc]

theorem tsq3_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsq3 xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsq3 xs dst pad carry cin) records s).basis=(regValue xs s.basis)^2 ∧
    ∀q,q∉dst → (run (tsq3 xs dst pad carry cin) records s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := tsq3_exists cin xs dst pad carry hn hx hd hp hc s records h0 hc0
  rw [hR]
  exact TrimSquare.tsq2_correct cin xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0 hi0

theorem tsqc3_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsqc3 xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsqc3 xs dst pad carry cin) records s).basis=0 ∧
    ∀q,q∉dst → (run (tsqc3 xs dst pad carry cin) records s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := tsqc3_exists cin xs dst pad carry hn hx hd hp hc s records hval hc0 hi0
  rw [hR]
  exact TrimSquare.tsqc2_correct cin xs dst pad carry hn hx hd hp hc s R hval hp0 hc0 hi0

theorem tsq3_counts (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    (toffoliCount (tsq3 xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3 ∧
      measurementCount (tsq3 xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3) ∧
    (toffoliCount (tsqc3 xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3 ∧
      measurementCount (tsqc3 xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3) := by
  have h := TrimSquare.tsq2_counts xs dst pad carry cin hx hd hp hc
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt, xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,Dt,a',as,c0,cs,_,hD,_,hsrc,hcy,_,_⟩ := row_shape x0 x1 xt dst pad carry hd hp hc
  have cA : toffoliCount (addDrop (x1::a'::as) (y1::y2::Dt) (c0::cs) x0)+1=
      toffoliCount (addInPlace (x1::a'::as) (y1::y2::Dt) (c0::cs) x0) ∧
      measurementCount (addDrop (x1::a'::as) (y1::y2::Dt) (c0::cs) x0)+1=
      measurementCount (addInPlace (x1::a'::as) (y1::y2::Dt) (c0::cs) x0) := by
    simp only [addDrop,addInPlace,toffoliCount_append,measurementCount_append]
    simp [majority,eraseCarry,toffoliCount,measurementCount]; omega
  have e1 : tsq3 (x0::x1::xt) dst pad carry cin=
      xorWhenFalse x0 (((dst.drop 1).take ((x1::xt).length+1)).take (x1::xt).length)++
        addDrop ((x1::xt)++pad.take 1) ((dst.drop 1).take ((x1::xt).length+1)) (carry.take (x1::xt).length) x0++
        (xorWhenFalse x0 ((dst.drop 1).take ((x1::xt).length+1))++(signedSquareRows (x1::xt) (dst.drop 2) pad carry++
        (signedSquareTop (x0::x1::xt) dst++(notRegister dst++
          (TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++notRegister dst))))) := by
    simp only [tsq3,rows3,row3,List.append_assoc]
  have e2 : TrimSquare.tsq2 (x0::x1::xt) dst pad carry cin=
      xorWhenFalse x0 (((dst.drop 1).take ((x1::xt).length+1)).take (x1::xt).length)++
        addInPlace ((x1::xt)++pad.take 1) ((dst.drop 1).take ((x1::xt).length+1)) (carry.take (x1::xt).length) x0++
        (xorWhenFalse x0 ((dst.drop 1).take ((x1::xt).length+1))++(signedSquareRows (x1::xt) (dst.drop 2) pad carry++
        (signedSquareTop (x0::x1::xt) dst++(notRegister dst++
          (TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++notRegister dst))))) := by
    simp only [TrimSquare.tsq2,signedSquareRows,signedSquareRow,List.append_assoc]
  have f1 : tsqc3 (x0::x1::xt) dst pad carry cin=
      TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++
      (signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 ((dst.drop 1).take ((x1::xt).length+1))++(notRegister ((dst.drop 1).take ((x1::xt).length+1))++
      (addDrop ((x1::xt)++pad.take 1) ((dst.drop 1).take ((x1::xt).length+1)) (carry.take (x1::xt).length) x0++
      (notRegister ((dst.drop 1).take ((x1::xt).length+1))++
        xorWhenFalse x0 (((dst.drop 1).take ((x1::xt).length+1)).take (x1::xt).length))))))) := by
    simp only [tsqc3,rowsClear3,rowClear3,List.append_assoc]
  have f2 : TrimSquare.tsqc2 (x0::x1::xt) dst pad carry cin=
      TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++
      (signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 ((dst.drop 1).take ((x1::xt).length+1))++(notRegister ((dst.drop 1).take ((x1::xt).length+1))++
      (addInPlace ((x1::xt)++pad.take 1) ((dst.drop 1).take ((x1::xt).length+1)) (carry.take (x1::xt).length) x0++
      (notRegister ((dst.drop 1).take ((x1::xt).length+1))++
        xorWhenFalse x0 (((dst.drop 1).take ((x1::xt).length+1)).take (x1::xt).length))))))) := by
    simp only [TrimSquare.tsqc2,signedSquareRowsClear,signedSquareRowClear,List.append_assoc]
  rw [e1,f1]; rw [e2,f2] at h
  rw [hsrc,hD,hcy] at h ⊢
  simp only [toffoliCount_append,measurementCount_append] at h ⊢
  omega

theorem tsq3_physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin :: xs ++ dst ++ pad ++ carry).Nodup) :
    GatePhysical (tsq3 xs dst pad carry cin) ∧ GatePhysical (tsqc3 xs dst pad carry cin) := by
  have h := TrimSquare.tsq2_physical xs dst pad carry cin hn
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact h
  · rw [e2,e4] at h; rw [e1,e3]
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨⟨h.1.1.1,addDrop_physical_gen _ _ _ _ h.1.1.2⟩,h.1.2⟩,
      ⟨⟨h.2.1.1,addDrop_physical_gen _ _ _ _ h.2.1.2⟩,h.2.2⟩⟩

theorem tsq3_wires_subset (xs dst pad carry : List Wire) (cin : Wire)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    wires (tsq3 xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset ∧
    wires (tsqc3 xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
  have h := TrimSquare.tsq2_wires_subset xs dst pad carry cin hd hp hc
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact h
  · rw [e2,e4] at h; rw [e1,e3]
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨⟨h.1.1.1,(addDrop_wires_gen _ _ _ _).trans h.1.1.2⟩,h.1.2⟩,
      ⟨⟨h.2.1.1,(addDrop_wires_gen _ _ _ _).trans h.2.1.2⟩,h.2.2⟩⟩

theorem tsq3_gateSlots_le (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsq3 xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 ∧
    Challenge.gateSlots (tsqc3 xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 := by
  have h := TrimSquare.tsq2_gateSlots_le xs dst pad carry cin
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact h
  · rw [e2,e4] at h; rw [e1,e3]
    have d := addDrop_slots x y cy c
    simp only [Challenge.gateSlots_append] at h ⊢
    omega

theorem tsq3_wires_le (xs dst pad carry : List Wire) (cin : Wire) :
    wires (tsq3 xs dst pad carry cin)⊆wires (TrimSquare.tsq2 xs dst pad carry cin) ∧
    wires (tsqc3 xs dst pad carry cin)⊆wires (TrimSquare.tsqc2 xs dst pad carry cin) := by
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨subset_refl _,subset_refl _⟩
  · rw [e1,e2,e3,e4]
    have d := addDrop_wires_gen x y cy c
    simp only [wires_append]
    constructor
    · exact Finset.union_subset_union (Finset.union_subset_union (subset_refl _) d) (subset_refl _)
    · exact Finset.union_subset_union (Finset.union_subset_union (subset_refl _) d) (subset_refl _)

theorem tsq3_physical_of (xs dst pad carry : List Wire) (cin : Wire)
    (h1 : GatePhysical (TrimSquare.tsq2 xs dst pad carry cin))
    (h2 : GatePhysical (TrimSquare.tsqc2 xs dst pad carry cin)) :
    GatePhysical (tsq3 xs dst pad carry cin) ∧ GatePhysical (tsqc3 xs dst pad carry cin) := by
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨h1,h2⟩
  · rw [e2] at h1; rw [e4] at h2; rw [e1,e3]
    simp only [gatePhysical_append] at h1 h2 ⊢
    exact ⟨⟨⟨h1.1.1,addDrop_physical_gen _ _ _ _ h1.1.2⟩,h1.2⟩,
      ⟨⟨h2.1.1,addDrop_physical_gen _ _ _ _ h2.1.2⟩,h2.2⟩⟩

end ECDSAAdd.Entrant.TrimSquare3

namespace ECDSAAdd.Entrant
open Arithmetic

theorem sq_plain3_make (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqMake xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsq3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsq3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,trivial,fun q h _ => r.2.2 q h⟩

theorem sq_plain3_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsqc3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsqc3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩

end ECDSAAdd.Entrant
end

-- ===== merged module ECDSAAdd.Submission.Entrant.TickMerged =====
section
/-! Ticks 509 and 510 of the integer walk as one forced block (terrapinelf, submission f753049b,
ported by e-man07 in e1b7db22 and a6dcb576).  This module carries the donor section unchanged. -/

section

/-! Ticks `509` and `510` as one block.

On the forced input of tick `509` (`u+v ≤ 4`, eighteen basis states) the function
space spanned by the forward outputs of ticks `509`–`510` exceeds the input-affine
functions by two dimensions, and both missing directions are products of
input-affine functions: `base 511·base 772` and `base 508·(base 510 ⊕ base 771)`.
The merged forward block computes these two products, maps the state affinely to the
outputs plus five garbage letters, and erases the letters by measurement with
quadratic corrections (two Toffolis instead of three).  The merged reverse block
rebuilds the inputs with five products of available affine functions and erases two
garbage letters (five Toffolis instead of six); its last two measurements act on
clean wires, so both blocks keep the measurement counts of the original ticks. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 History5

/-- Gate list of `W.ReverseCarry.compactReceiverTick base 509`. -/
def tick509ExR : Program :=
  [.CX 788 789, .CX 528 529, .CX 524 525, .CX 1553 789, .X 1553, .CX 528 1553, .CX 788 1553,
   .X 786, .X 787, .X 788, .CX 1553 526, .CX 1553 527, .CX 1553 528, .CX 526 786, .CX 526 1553,
   .CCX 786 1553 1556, .CX 526 1556, .CX 526 1553, .CX 526 786,
   .measureX 788 [] [.CZ 527 787, .CZ 527 1556, .CZ 787 1556], .CX 528 788, .CX 527 787,
   .CX 1556 787, .measureX 1556 [] [.CZ 526 786, .CZ 526 1553, .CZ 786 1553], .CX 526 786,
   .CX 1553 786, .CX 1553 526, .CX 1553 527, .CX 1553 528, .X 786, .X 787, .X 788, .X 1553,
   .CX 528 1553, .CX 788 1553, .CX 528 529, .CX 525 786, .CX 787 526, .CX 788 527, .CX 789 528,
   .CCX 525 526 787, .CCX 525 527 788, .CCX 525 528 789, .CX 787 526, .CX 788 527, .CX 789 528]

/-- Ticks `509` and `510` forward on the forced input of tick `509`. -/
def tickMF : Program :=
  [.CCX 527 788 1556, .CX 787 526, .CCX 524 526 1557, .CX 1557 1554, .CX 1557 788, .CX 1557 787,
   .CX 1557 528, .CX 1556 1553, .CX 1556 789, .CX 1556 527, .CX 1554 1557, .CX 1554 789,
   .CX 1554 788, .CX 1554 528, .CX 1557 1554, .CX 1553 1556, .CX 1553 527, .CX 1556 1553,
   .CX 789 1557, .CX 789 528, .CX 1557 789, .CX 788 789, .CX 789 788, .CX 787 1557, .CX 787 1553,
   .CX 787 529, .CX 787 528, .CX 787 526, .CX 529 787, .CX 787 529, .CX 528 1557, .CX 528 1554,
   .CX 1554 528, .CX 527 1556, .CX 1556 527, .CX 526 1554, .CX 526 1553, .CX 526 786,
   .CX 526 529, .CX 526 527, .CX 525 1554, .CX 525 1553, .CX 525 527, .CX 525 526, .CX 524 1554,
   .CX 524 1553, .CX 524 786, .CX 524 527, .CX 524 526, .CX 524 525, .X 527, .X 529, .X 786,
   .X 1553, .X 1554, .X 1556,
   .measureX 789 [] [.CZ 786 1557, .Z 1553, .CZ 525 527, .CZ 527 1556, .Z 1554],
   .measureX 1556 [] [.CZ 524 1553, .CZ 525 1557, .CZ 527 528, .CZ 525 527, .Z 526],
   .measureX 528 [] [.Z 524, .CZ 524 529],
   .measureX 529 [] [.CZ 526 1553, .CZ 525 1554, .Z 1554, .Z 525],
   .measureX 1557 [] [.CZ 524 1553, .CZ 524 1554]]

/-- Reverse ticks `510` and `509` on the merged forward outputs. -/
def tickMR : Program :=
  [.CCX 525 526 528, .CX 1554 1553, .CCX 524 1553 529, .CX 526 525, .CCX 1553 525 787,
   .CX 528 525, .CCX 524 525 788, .CX 528 524, .CX 787 524, .CX 788 526, .CX 1554 526,
   .CCX 524 526 789, .CX 1556 786, .CX 1554 1553, .CX 1554 787, .CX 1554 786, .CX 1554 529,
   .CX 1554 527, .CX 1554 525, .CX 1554 524, .CX 1553 1554, .CX 1553 529, .CX 1553 526,
   .CX 789 1554, .CX 789 1553, .CX 789 788, .CX 789 786, .CX 789 529, .CX 789 527, .CX 789 526,
   .CX 789 525, .CX 788 1553, .CX 1553 788, .CX 787 1553, .CX 787 788, .CX 787 786, .CX 787 527,
   .CX 787 525, .CX 787 524, .CX 786 1556, .CX 1556 786, .CX 529 1554, .CX 529 1553, .CX 529 789,
   .CX 529 526, .CX 789 529, .CX 528 1556, .CX 528 1554, .CX 528 527, .CX 528 526, .CX 528 524,
   .CX 1554 528, .CX 527 1556, .CX 527 1554, .CX 527 787, .CX 527 526, .CX 527 525, .CX 526 1553,
   .CX 526 788, .CX 526 529, .CX 526 527, .CX 527 526, .CX 525 786, .CX 525 527, .CX 525 526,
   .CX 524 1554, .CX 524 788, .CX 524 787, .CX 524 786, .CX 524 529, .CX 524 527, .CX 524 526,
   .CX 524 525, .X 525, .X 529, .X 788, .X 1553, .X 1554, .X 1556,
   .measureX 529 [] [.CZ 527 788, .Z 788], .measureX 1554 [] [.CZ 524 526, .Z 528, .CZ 526 786],
   .measureX 1556 [] [], .measureX 529 [] []]

/-- The fourteen physical wires of ticks `509` and `510`. -/
def sitesM : List Wire := [524, 525, 526, 527, 528, 529, 786, 787, 788, 789, 1553, 1554, 1556, 1557]

theorem tick509ExR_explicit : W.ReverseCarry.compactReceiverTick base 509 = tick509ExR := by
  decide +kernel
theorem tickMF_wires : wires tickMF ⊆ sitesM.toFinset := by decide +kernel
theorem tickMR_wires : wires tickMR ⊆ sitesM.toFinset := by decide +kernel
theorem pairF_wires : wires (tick509ExF ++ tick510ExF) ⊆ sitesM.toFinset := by decide +kernel
theorem pairR_wires : wires (tick510ExR ++ tick509ExR) ⊆ sitesM.toFinset := by decide +kernel
theorem tickMF_sub : wires tickMF ⊆ wires (tick509ExF ++ tick510ExF) := by decide +kernel
theorem sitesM_pool : ∀ q ∈ sitesM, q ∈ skywalkPoolWires base := by decide +kernel
theorem tickMR_sub : wires tickMR ⊆ wires (tick510ExR ++ tick509ExR) := by decide +kernel

theorem tickM_counts :
    toffoliCount tickMF = 2 ∧ measurementCount tickMF = 5 ∧
    toffoliCount (tick509ExF ++ tick510ExF) = 8 ∧ measurementCount (tick509ExF ++ tick510ExF) = 5 ∧
    toffoliCount tickMR = 5 ∧ measurementCount tickMR = 4 ∧
    toffoliCount (tick510ExR ++ tick509ExR) = 7 ∧ measurementCount (tick510ExR ++ tick509ExR) = 4 := by
  decide +kernel

theorem tickM_slots :
    Challenge.gateSlots tickMF ≤ Challenge.gateSlots (tick509ExF ++ tick510ExF) ∧
    Challenge.gateSlots tickMR ≤ Challenge.gateSlots (tick510ExR ++ tick509ExR) := by decide +kernel

theorem tickM_physical : GatePhysical tickMF ∧ GatePhysical tickMR := by
  constructor <;> simp [tickMF, tickMR, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]

/-- All measurement records of length at most `n`. -/
def recsUpTo : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => [] :: ((recsUpTo n).map (false :: ·) ++ (recsUpTo n).map (true :: ·))

theorem take_recsUpTo (n : Nat) (m : List Bool) : m.take n ∈ recsUpTo n := by
  induction n generalizing m with
  | zero => simp [recsUpTo]
  | succ n ih =>
    rcases m with _ | ⟨b, m⟩
    · simp [recsUpTo]
    · have h := ih m
      cases b <;> simp [recsUpTo, h]

theorem concMF : ∀ G S : Bool, ∀ uv ∈ pairs509, ∀ c ∈ recsUpTo 5,
    (run (tick509ExF ++ tick510ExF) c ⟨false, pre509 G S uv.1 uv.2⟩).phase =
      (run tickMF c ⟨false, pre509 G S uv.1 uv.2⟩).phase ∧
    ∀ q ∈ sitesM,
      (run (tick509ExF ++ tick510ExF) c ⟨false, pre509 G S uv.1 uv.2⟩).basis q =
        (run tickMF c ⟨false, pre509 G S uv.1 uv.2⟩).basis q := by
  decide +kernel

theorem concMR : ∀ G S : Bool, ∀ uv ∈ pairs509, ∀ c ∈ recsUpTo 4,
    (run (tick510ExR ++ tick509ExR) c
        ⟨false, (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis⟩).phase =
      (run tickMR c ⟨false, (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis⟩).phase ∧
    ∀ q ∈ sitesM,
      (run (tick510ExR ++ tick509ExR) c
          ⟨false, (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis⟩).basis q =
        (run tickMR c ⟨false, (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis⟩).basis q := by
  decide +kernel

theorem pack509_nil : History5.packAfter base 509 = [] := by decide +kernel
theorem decode509_nil : History5.decodeBefore base 509 = [] := by decide +kernel

attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix

/-- The tick-`510` history and the carry site exchanged by `OB5.sig 510` are clean
on the compressed stage before tick `509`. -/
theorem stage509_clean (x : Nat) (s : State)
    (stage : W.CompressedCompactStage5 base x p 509 s.basis) :
    s.basis (base 1538) = false ∧ s.basis (base 1543) = false := by
  obtain ⟨raw, hraw, hbits⟩ := stage
  have fields := (W.compactSkywalkStage_fields_iff base _ 509 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨-, -, -, -, future, carry, -, -, -⟩ := fields
  have k1 := StackOB5Base.prefix_keep 509 (by omega) raw 1538 (by omega)
  have k2 := StackOB5Base.prefix_keep 509 (by omega) raw 1543 (by omega)
  rw [hbits, k1, k2]
  exact ⟨(future 510 (by omega) (by omega)).2,
    (regValue_zero _ _).mp carry _ (List.mem_map.mpr ⟨1543, by simp, rfl⟩)⟩

/-- The compressed stage before tick `509` pins the fourteen merged wires. -/
theorem stage509_bitsM (x : Nat) (hx0 : 0 < x) (hx : x < p) (s : State)
    (stage : W.CompressedCompactStage5 base x p 509 s.basis) :
    ∃ G S : Bool, ∃ uv ∈ pairs509, ∀ q ∈ sitesM, s.basis q = pre509 G S uv.1 uv.2 q := by
  obtain ⟨G, S, uv, huv, bits⟩ := stage509_bits x hx0 hx s stage
  have cl := stage509_clean x s stage
  refine ⟨G, S, uv, huv, ?_⟩
  intro q hq
  by_cases h : q = 1554
  · subst h
    exact cl.1
  · apply bits q
    simp only [sitesM, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact absurd rfl h | decide

/-- Forward ticks `509` and `510` on a compressed stage state are the merged block. -/
theorem tickMF_forced (x : Nat) (hx0 : 0 < x) (hx : x < p) (t : State)
    (ht : W.CompressedCompactStage5 base x p 509 t.basis) (m : List Bool) :
    run tickMF m t = run (W.repairedTick base 509 ++ W.repairedTick base 510) m t := by
  obtain ⟨G, S, uv, huv, bits⟩ := stage509_bitsM x hx0 hx t ht
  rw [tick509ExF_explicit, tick510ExF_explicit]
  symm
  exact forced_eqN (tick509ExF ++ tick510ExF) tickMF sitesM (pre509 G S uv.1 uv.2) 5 (recsUpTo 5)
    (take_recsUpTo 5) pairF_wires tickMF_wires (le_of_eq tickM_counts.2.2.2.1) (le_of_eq tickM_counts.2.1)
    (fun c hc => concMF G S uv huv c hc) t bits m

/-- After ticks `509`, `510` and the pack, decoding and the merged reverse block agree
with decoding and the original reverse ticks `510`, `509`. -/
theorem blockM_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (t : State)
    (ht : W.CompressedCompactStage5 base x p 509 t.basis) (m1 m2 : List Bool) :
    run (History5.decodeBefore base 510 ++ tickMR) m2
        (run ((W.repairedTick base 509 ++ W.repairedTick base 510) ++ History5.packAfter base 510) m1 t) =
      run (History5.decodeBefore base 510 ++
          (W.ReverseCarry.compactReceiverTick base 510 ++ W.ReverseCarry.compactReceiverTick base 509)) m2
        (run ((W.repairedTick base 509 ++ W.repairedTick base 510) ++ History5.packAfter base 510) m1 t) := by
  obtain ⟨hp0, hpo, hp, cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  obtain ⟨G, S, uv, huv, bits⟩ := stage509_bitsM x hx0 hx t ht
  have due : History5.packDue 510 = true := by decide
  have rep : W.repairedTick base 510 = W.compactSkywalkTick base 510 := by
    rw [tick510ExF_explicit, tick510ExF_compact]
  set k := measurementCount (W.repairedTick base 509 ++ W.repairedTick base 510) with hk
  set k9 := measurementCount (W.repairedTick base 509) with hk9
  set d := measurementCount (History5.decodeBefore base 510) with hd
  set b := run (W.repairedTick base 509) ((m1.take k).take k9) t with hb
  set a := run (W.repairedTick base 509 ++ W.repairedTick base 510) (m1.take k) t with ha
  have bStage : W.CompressedCompactStage5 base x p 510 b.basis := by
    have h := (Stack5.step_spec base base_pool_nodup StackOB5.historyAbove x p 509 hp0 hx0 hpo hp hpGap hx
      cop (by omega) t ((m1.take k).take k9) ht).2
    rw [pack509_nil, List.append_nil] at h
    exact h
  have aSplit : a = run (W.repairedTick base 510) ((m1.take k).drop k9) b := by
    rw [ha, hb, run_append, ← hk9]
  have legal := Stack5.tick_pack_legal base base_pool_nodup x p 510 hp0 hx0 hpo hp hpGap hx cop
    (by omega) b ((m1.take k).drop k9) bStage due
  rw [← rep, ← aSplit] at legal
  have dp : run (History5.decodeBefore base 510) (m2.take d)
      (run (History5.packAfter base 510) (m1.drop k) a) = a := by
    simpa only [History5.packAfter, History5.decodeBefore, due, if_true, History5.encode,
      History5.decode] using
      MeasuredCodec5.roundtripAt (History5.historyMap base (510-5))
        (History5.historyMap_injective base base_pool_nodup (510-5) (by omega)) a (m1.drop k)
        (m2.take d) legal
  have abits : ∀ q ∈ sitesM, a.basis q =
      (run (tick509ExF ++ tick510ExF) [] ⟨false, pre509 G S uv.1 uv.2⟩).basis q := by
    intro q hq
    rw [ha, tick509ExF_explicit, tick510ExF_explicit,
      site_run (tick509ExF ++ tick510ExF) sitesM pairF_wires t ⟨false, pre509 G S uv.1 uv.2⟩ bits
        (m1.take k) q hq]
    exact congrFun (run_basis_records (tick509ExF ++ tick510ExF) _ _ (m1.take k) [] rfl) q
  rw [run_append (W.repairedTick base 509 ++ W.repairedTick base 510),
    run_append (History5.decodeBefore base 510) tickMR,
    run_append (History5.decodeBefore base 510), ← hk, ← hd, ← ha, dp,
    tick510ExR_explicit, tick509ExR_explicit]
  symm
  exact forced_eqN (tick510ExR ++ tick509ExR) tickMR sitesM _ 4 (recsUpTo 4) (take_recsUpTo 4)
    pairR_wires tickMR_wires (le_of_eq tickM_counts.2.2.2.2.2.2.2) (le_of_eq tickM_counts.2.2.2.2.2.1)
    (fun c hc => concMR G S uv huv c hc) a abits (m2.drop d)

end ECDSAAdd.Entrant
end

/-! ### Record counts of the merged blocks against the original tick programs -/
section
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1

theorem tickMF_records : measurementCount tickMF=
    measurementCount (W.repairedTick base 509)+measurementCount (W.repairedTick base 510) := by
  obtain ⟨_,c2,_,c4,_,_,_,_⟩ := tickM_counts
  rw [tick509ExF_explicit,tick510ExF_explicit,←measurementCount_append,c2,c4]

theorem tickMR_records : measurementCount tickMR=
    measurementCount (W.ReverseCarry.compactReceiverTick base 510)+
      measurementCount (W.ReverseCarry.compactReceiverTick base 509) := by
  obtain ⟨_,_,_,_,_,c6,_,c8⟩ := tickM_counts
  rw [tick510ExR_explicit,tick509ExR_explicit,←measurementCount_append,c6,c8]

end ECDSAAdd.Entrant
end
end

-- ===== merged module ECDSAAdd.Submission.Entrant.FusedFlags =====
section
namespace ECDSAAdd.Entrant.FusedFlags
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem rename_append (f : Wire→Wire) (P Q : Program) :
    renameProgram f (P++Q)=renameProgram f P++renameProgram f Q := List.map_append

def gen : Program := [.CCX 3 0 5,.CX 4 5,.CX 6 5]
def merge : Program := [.CX 5 10,.CCX 3 0 5,.CX 5 10,.CX 3 10,.CX 4 5,.CX 6 5]

def clearPrefix (cx cy : Bool) : Program :=
  [.CX 5 8,.CX 4 8,.CX 6 8] ++ gen ++ (MeasuredDH.joint true cx cy).drop 2

def restoreSuffix (cx cy : Bool) : Program :=
  (MeasuredDH.joint false cx cy).dropLast ++
  [.CX 5 10,.CX 8 10,.CX 3 10,.CX 5 8,.CX 8 5,.CX 4 5,.CX 6 5,
    .measureX 8 [] [.CZ 3 0]]

theorem clear_equivalence : ∀cx cy : Bool, ∀x : Fin 2048,
    MeasuredDH.clean x.val=true →
    MeasuredDH.covered (bitRun gen x.val)=true →
    MeasuredDH.clears true true cx cy (bitRun gen x.val)=true →
    safe (clearPrefix cx cy) x.val=true ∧
      bitRun (clearPrefix cx cy) x.val=bitRun (gen++MeasuredDH.original true true cx cy) x.val := by
  decide +kernel

theorem restore_equivalence : ∀cx cy : Bool, ∀x : Fin 2048,
    MeasuredDH.clean x.val=true → MeasuredDH.covered x.val=true →
    x.val.testBit 4=false → x.val.testBit 6=false →
    safe (restoreSuffix cx cy) x.val=true ∧
      bitRun (restoreSuffix cx cy) x.val=bitRun (MeasuredDH.original true true cx cy++merge) x.val := by
  decide +kernel

theorem original_safe : ∀cx cy : Bool, ∀x : Fin 2048,
    MeasuredDH.clean x.val=true →
    safe (gen++MeasuredDH.original true true cx cy) x.val=true ∧
    safe (MeasuredDH.original true true cx cy++merge) x.val=true := by decide +kernel

theorem restore_run (cx cy : Bool) (x : Fin 2048)
    (clean : MeasuredDH.clean x.val=true) (covered : MeasuredDH.covered x.val=true)
    (d : x.val.testBit 4=false) (h : x.val.testBit 6=false)
    (phase : Bool) (newRecord oldRecord : List Bool) :
    run (restoreSuffix cx cy) newRecord ⟨phase,bitsOf x.val⟩=
      run (MeasuredDH.original true true cx cy++merge) oldRecord ⟨phase,bitsOf x.val⟩ := by
  have replacement := restore_equivalence cx cy x clean covered d h
  rw [run_sim,sim_safe _ x.val replacement.1,run_sim,
    sim_safe _ x.val (original_safe cx cy x clean).2,replacement.2]

theorem counts (cx cy : Bool) :
    toffoliCount (clearPrefix cx cy)=1 ∧ toffoliCount (restoreSuffix cx cy)=3 ∧
    measurementCount (clearPrefix cx cy)=3 ∧ measurementCount (restoreSuffix cx cy)=1 := by
  cases cx <;> cases cy <;> decide

def adapter (erase cx cy : Bool) : Program :=
  if erase then gen.reverse++clearPrefix cx cy else restoreSuffix cx cy++merge.reverse

theorem adapter_finite : ∀erase cx cy : Bool, ∀x : Fin 2048,
    MeasuredDH.clean x.val=true → MeasuredDH.covered x.val=true →
    (erase=true → MeasuredDH.clears true true cx cy x.val=true) →
    (erase=false → x.val.testBit 4=false ∧ x.val.testBit 6=false) →
    safe (adapter erase cx cy) x.val=true ∧
      bitRun (adapter erase cx cy) x.val=bitRun (MeasuredDH.original true true cx cy) x.val := by
  decide +kernel

theorem adapter_original_safe : ∀cx cy : Bool, ∀x : Fin 2048,
    MeasuredDH.clean x.val=true → safe (MeasuredDH.original true true cx cy) x.val=true := by
  decide +kernel

theorem adapter_support (erase cx cy : Bool) : wires (adapter erase cx cy)⊆Finset.range 11 ∧
    wires (MeasuredDH.original true true cx cy)⊆Finset.range 11 := by
  cases erase <;> cases cx <;> cases cy <;> decide

theorem adapter_run (erase cx cy : Bool) (s : State) (m : List Bool)
    (hz : s.basis 7=false ∧ s.basis 8=false ∧ s.basis 9=false)
    (hg : s.basis 5=true → s.basis 3=true ∧ s.basis 0=true)
    (he : erase=true → (run (MeasuredDH.original true true cx cy) m s).basis 4=false ∧
      (run (MeasuredDH.original true true cx cy) m s).basis 6=false)
    (hr : erase=false → s.basis 4=false ∧ s.basis 6=false) :
    run (adapter erase cx cy) m s=run (MeasuredDH.original true true cx cy) m s := by
  let x : Fin 2048 := ⟨regValue (List.range 11) s.basis,by
    simpa only [List.length_range] using regValue_lt (List.range 11) s.basis⟩
  have hb (q : Nat) (hq : q<11) : s.basis q=bitsOf x.val q :=
    (LocalWireModel.range_bit 11 s.basis q hq).symm
  have clean : MeasuredDH.clean x.val=true := by
    change (!bitsOf x.val 7 && !bitsOf x.val 8 && !bitsOf x.val 9)=true
    rw [←hb 7 (by decide),←hb 8 (by decide),←hb 9 (by decide),hz.1,hz.2.1,hz.2.2]
    rfl
  have cov : MeasuredDH.covered x.val=true := by
    change (!bitsOf x.val 5 || (bitsOf x.val 3 && bitsOf x.val 0))=true
    rw [←hb 5 (by decide),←hb 3 (by decide),←hb 0 (by decide)]
    cases h : s.basis 5
    · rfl
    · simp [(hg h).1,(hg h).2]
  have hp := adapter_support erase cx cy
  have oldSafe := adapter_original_safe cx cy x clean
  have clear : erase=true → MeasuredDH.clears true true cx cy x.val=true := by
    intro er
    have modeled := pool_run_agrees (MeasuredDH.original true true cx cy) (Finset.range 11) hp.2 m s
      ⟨s.phase,bitsOf x.val⟩ rfl (fun q hq => hb q (Finset.mem_range.mp hq))
    rw [run_sim,sim_safe _ x.val oldSafe] at modeled
    have h4 := (modeled.2 4 (by decide)).symm.trans (he er).1
    have h6 := (modeled.2 6 (by decide)).symm.trans (he er).2
    change (bitRun (MeasuredDH.original true true cx cy) x.val).testBit 4=false at h4
    change (bitRun (MeasuredDH.original true true cx cy) x.val).testBit 6=false at h6
    simp only [MeasuredDH.clears,h4,h6]
    rfl
  have restore : erase=false → x.val.testBit 4=false ∧ x.val.testBit 6=false := by
    intro er
    exact ⟨(hb 4 (by decide)).symm.trans (hr er).1,(hb 6 (by decide)).symm.trans (hr er).2⟩
  have eq := adapter_finite erase cx cy x clean cov clear restore
  apply LocalWireModel.model_eq 11 _ _ hp.1 hp.2 s m x.val
    (fun q hq => hb q (Finset.mem_range.mp hq))
  rw [run_sim,sim_safe _ x.val eq.1,run_sim,sim_safe _ x.val oldSafe,eq.2]

theorem adapter_at_run (f : Fin 11→Wire) (hf : Function.Injective f)
    (erase cx cy : Bool) (s : State) (m : List Bool)
    (hz : s.basis (f 7)=false ∧ s.basis (f 8)=false ∧ s.basis (f 9)=false)
    (hg : s.basis (f 5)=true → s.basis (f 3)=true ∧ s.basis (f 0)=true)
    (he : erase=true →
      (run (renameProgram (LocalWireModel.label f) (MeasuredDH.original true true cx cy)) m s).basis (f 4)=false ∧
      (run (renameProgram (LocalWireModel.label f) (MeasuredDH.original true true cx cy)) m s).basis (f 6)=false)
    (hr : erase=false → s.basis (f 4)=false ∧ s.basis (f 6)=false) :
    run (renameProgram (LocalWireModel.label f) (adapter erase cx cy)) m s=
      run (renameProgram (LocalWireModel.label f) (MeasuredDH.original true true cx cy)) m s := by
  have hp := adapter_support erase cx cy
  apply LocalWireModel.renamed_eq f hf _ _ hp.1 hp.2
  apply adapter_run erase cx cy
  · exact hz
  · exact hg
  · intro er
    have pp := run_rename_pool (LocalWireModel.label f) (Finset.range 11)
      (LocalWireModel.label_injective f hf) (MeasuredDH.original true true cx cy) hp.2 m
      ⟨s.phase,fun q => s.basis (LocalWireModel.label f q)⟩ s rfl (fun _ _ => rfl)
    exact ⟨(pp.2 4 (by decide)).symm.trans (he er).1,
      (pp.2 6 (by decide)).symm.trans (he er).2⟩
  · exact hr

open Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog

def ports (L : ControlledPointLayout) (k : Nat) : Fin 11→Wire :=
  ![L.point.finite,L.point.x.getD k 0,yLow L,L.control,L.doubleSelect,L.genericSelect,
    L.core.equalNegY,L.core.poolWire 0,L.core.poolWire 1,L.core.poolWire 2,parkWire L]

theorem ports_injective (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k<256) : Function.Injective (ports L k) := by
  have hxk : L.point.x.getD k 0∈L.point.x := by
    have hl : k<L.point.x.length := by rw [show L.point.x.length=256 from hw.inputX]; exact hk
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hy0 : yLow L∈L.point.y := by
    have hl : 0<L.point.y.length := by rw [show L.point.y.length=256 from hw.inputY]; decide
    unfold yLow
    cases hy : L.point.y with
    | nil => rw [hy] at hl; simp at hl
    | cons a t => simp
  have p1 : [L.point.finite,L.point.x.getD k 0,yLow L].Sublist (PointAddLayout.pointWires L.point) := by
    simp only [PointAddLayout.pointWires]
    exact List.Sublist.cons₂ _ ((List.singleton_sublist.mpr hxk).append (List.singleton_sublist.mpr hy0))
  have p2 : [L.doubleSelect,L.genericSelect,L.core.equalNegY].Sublist L.inPlaceFlags := by
    simp only [inPlaceFlags]
    exact .cons _ (.cons₂ _ (.cons₂ _ (.cons _ (.cons _ (.cons₂ _ (.cons _ .slnil))))))
  have p3 : [L.core.poolWire 0,L.core.poolWire 1,L.core.poolWire 2,parkWire L].Sublist L.dialogPool := by
    have h : ([0,1,2,514] : List Nat).Sublist (List.range' 0 515) := by decide +kernel
    have sub : [L.core.poolWire 0,L.core.poolWire 1,L.core.poolWire 2,parkWire L].Sublist
        (L.dialogPool.take 515) := by
      rw [pool_block L hw 515 (by omega)]
      simpa only [parkWire,wireBlock,List.map_cons,List.map_nil] using h.map L.core.poolWire
    exact sub.trans (List.take_sublist _ _)
  have sub := ((p1.append (List.Sublist.refl [L.control])).append p2).append p3
  have nd : [L.point.finite,L.point.x.getD k 0,yLow L,L.control,L.doubleSelect,L.genericSelect,
      L.core.equalNegY,L.core.poolWire 0,L.core.poolWire 1,L.core.poolWire 2,parkWire L].Nodup := by
    have fullSub : [L.point.finite,L.point.x.getD k 0,yLow L,L.control,L.doubleSelect,L.genericSelect,
        L.core.equalNegY,L.core.poolWire 0,L.core.poolWire 1,L.core.poolWire 2,parkWire L].Sublist L.dialogUsedWires := by
      simpa only [dialogUsedWires,List.cons_append,List.nil_append,List.singleton_append,List.append_assoc] using sub
    exact (L.dialogUsed_nodup hn).sublist fullSub
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd
  intro a b eq
  fin_cases a <;> fin_cases b <;> simp_all [ports,eq_comm]

def adapterProgram (L : ControlledPointLayout) (C : Point) (erase : Bool) : Program :=
  renameProgram (LocalWireModel.label (ports L (DHClass.kx C))) (adapter erase (DHClass.cxk C) (yBit C))

theorem original_at (L : ControlledPointLayout) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    renameProgram (LocalWireModel.label (ports L (DHClass.kx (.some hc))))
      (MeasuredDH.original true true (DHClass.cxk (.some hc)) (yBit (.some hc)))=clrDH L (.some hc) cy := by
  have hd : decide (cy≠-cy)=true := by rw [cy_ne_neg hc]
  have he := NoThreeTorsion.enabled hc
  unfold clrDH
  rw [hd,he]
  cases DHClass.cxk (.some hc) <;> cases yBit (.some hc) <;> rfl

theorem boundary_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (erase : Bool)
    (R : Point) (b D G H : Bool) (cov : G=true → b=true ∧ pointFinite R=true)
    (restore : erase=false → D=false ∧ H=false) (s : State) (m : List Bool)
    (v : PointDialogBoundary L R b (dialogFlagState L false D G false false H false) s.basis)
    (he : erase=true → (run (clrDH L (.some hc) cy) m s).basis L.doubleSelect=false ∧
      (run (clrDH L (.some hc) cy) m s).basis L.core.equalNegY=false) :
    run (adapterProgram L (.some hc) erase) m s=run (clrDH L (.some hc) cy) m s := by
  rw [←original_at L hc]
  apply adapter_at_run (ports L (DHClass.kx (.some hc)))
    (ports_injective L hw hn _ (DHClass.kx_lt (.some hc))) erase (DHClass.cxk (.some hc)) (yBit (.some hc))
  · have zero (i : Nat) (hi : i<3) : s.basis (L.core.poolWire i)=false := by
      apply (regValue_zero _ _).mp v.clean
      apply List.mem_of_mem_take (i:=3)
      rw [pool_block L hw 3 (by omega)]
      exact List.mem_map.mpr ⟨i,List.mem_range'_1.mpr ⟨by omega,by omega⟩,rfl⟩
    exact ⟨zero 0 (by decide),zero 1 (by decide),zero 2 (by decide)⟩
  · have hr := dialogFlagState_read L hn false D G false false H false
    have vg : s.basis L.genericSelect=G := (v.flags _ (by simp [inPlaceFlags])).trans hr.2.2.1
    intro hg
    have hh := cov (vg.symm.trans hg)
    exact ⟨v.control.trans hh.1,((point_holds _ _ _).mp v.point).1.trans hh.2⟩
  · simpa only [original_at] using he
  · intro er
    have hr := dialogFlagState_read L hn false D G false false H false
    exact ⟨((v.flags _ (by simp [inPlaceFlags])).trans hr.2.1).trans (restore er).1,
      ((v.flags _ (by simp [inPlaceFlags])).trans hr.2.2.2.2.2.1).trans (restore er).2⟩

theorem boundary_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (erase : Bool)
    (R : Point) (b D G H D' H' : Bool) (cov : G=true → b=true ∧ pointFinite R=true)
    (clear : erase=true → D'=false ∧ H'=false) (restore : erase=false → D=false ∧ H=false)
    (old : Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (clrDH L (.some hc) cy)
      (PointDialogBoundary L R b (dialogFlagState L false D' G false false H' false))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (adapterProgram L (.some hc) erase)
      (PointDialogBoundary L R b (dialogFlagState L false D' G false false H' false)) := by
  intro s m v
  have ho := old s m v
  rw [boundary_eq L hw hn hc erase R b D G H cov restore s m v ?_]
  · exact ho
  · intro er
    have hr := dialogFlagState_read L hn false D' G false false H' false
    exact ⟨((ho.2.flags _ (by simp [inPlaceFlags])).trans hr.2.1).trans (clear er).1,
      ((ho.2.flags _ (by simp [inPlaceFlags])).trans hr.2.2.2.2.2.1).trans (clear er).2⟩

def cycle (first : Bool) : Program := if first then gen++gen.reverse else merge.reverse++merge

theorem cycle_finite : ∀first : Bool, ∀x : Fin 2048,
    safe (cycle first) x.val=true ∧ bitRun (cycle first) x.val=x.val := by decide +kernel

theorem cycle_support (first : Bool) : wires (cycle first)⊆Finset.range 11 := by cases first <;> decide
theorem cycle_measurements (first : Bool) : measurementCount (cycle first)=0 := by cases first <;> rfl

theorem cycle_run (first : Bool) (s : State) (m : List Bool) : run (cycle first) m s=s := by
  let x : Fin 2048 := ⟨regValue (List.range 11) s.basis,by
    simpa only [List.length_range] using regValue_lt (List.range 11) s.basis⟩
  have h := LocalWireModel.model_eq 11 (cycle first) [] (cycle_support first) (by simp [wires]) s m x.val
    (by intro q hq; exact (LocalWireModel.range_bit 11 s.basis q (Finset.mem_range.mp hq)).symm) (by
      have finite := cycle_finite first x
      rw [run_sim,sim_safe _ x.val finite.1,finite.2]
      rfl)
  exact h

theorem cycle_at_run (f : Fin 11→Wire) (hf : Function.Injective f)
    (first : Bool) (s : State) (m : List Bool) :
    run (renameProgram (LocalWireModel.label f) (cycle first)) m s=s := by
  have h := LocalWireModel.renamed_eq f hf (cycle first) [] (cycle_support first) (by simp [wires]) s m
    (cycle_run first _ m)
  exact h

def prefixProgram (L : ControlledPointLayout) (C : Point) : Program :=
  renameProgram (LocalWireModel.label (ports L (DHClass.kx C))) (clearPrefix (DHClass.cxk C) (yBit C))
def suffixProgram (L : ControlledPointLayout) (C : Point) : Program :=
  renameProgram (LocalWireModel.label (ports L (DHClass.kx C))) (restoreSuffix (DHClass.cxk C) (yBit C))

theorem gen_at (L : ControlledPointLayout) (k : Nat) :
    renameProgram (LocalWireModel.label (ports L k)) gen=genFlagN L := rfl
theorem merge_at (L : ControlledPointLayout) (k : Nat) :
    renameProgram (LocalWireModel.label (ports L k)) merge=mergeFlagsN L := rfl

theorem prefix_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    run (genFlagN L++adapterProgram L C true) m s=run (prefixProgram L C) m s := by
  have shape : genFlagN L++adapterProgram L C true=
      renameProgram (LocalWireModel.label (ports L (DHClass.kx C))) (cycle true)++prefixProgram L C := by
    simp only [cycle,if_true,adapterProgram,adapter,rename_append,gen_at,prefixProgram,List.append_assoc]
  rw [shape,LocalWireModel.run_concat,(renameProgram_counts _ _).2,cycle_measurements,List.drop_zero,
    cycle_at_run _ (ports_injective L hw hn _ (DHClass.kx_lt C))]

theorem suffix_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    run (adapterProgram L C false++mergeFlagsN L) m s=run (suffixProgram L C) m s := by
  have shape : adapterProgram L C false++mergeFlagsN L=suffixProgram L C++
      renameProgram (LocalWireModel.label (ports L (DHClass.kx C))) (cycle false) := by
    simp only [cycle,Bool.false_eq_true,if_false,adapterProgram,adapter,rename_append,merge_at,
      suffixProgram,List.append_assoc]
  rw [shape,LocalWireModel.run_concat,cycle_at_run _ (ports_injective L hw hn _ (DHClass.kx_lt C))]

theorem prefix_measurements (L : ControlledPointLayout) (C : Point) :
    measurementCount (genFlagN L++adapterProgram L C true)=measurementCount (prefixProgram L C) := by
  simp only [measurementCount_append,adapterProgram,prefixProgram,(renameProgram_counts _ _).2,
    adapter,if_true,show measurementCount (genFlagN L)=0 from rfl,
    show measurementCount gen.reverse=0 from rfl,Nat.zero_add]

theorem suffix_measurements (L : ControlledPointLayout) (C : Point) :
    measurementCount (adapterProgram L C false++mergeFlagsN L)=measurementCount (suffixProgram L C) := by
  simp only [measurementCount_append,adapterProgram,suffixProgram,(renameProgram_counts _ _).2,
    adapter,Bool.false_eq_true,if_false,show measurementCount (mergeFlagsN L)=0 from rfl,
    show measurementCount merge.reverse=0 from rfl,Nat.add_zero]

theorem same_context (P Q A B : Program)
    (hm : measurementCount P=measurementCount Q)
    (eq : ∀s m,run P m s=run Q m s) (s : State) (m : List Bool) :
    run (A++P++B) m s=run (A++Q++B) m s := by
  simp only [LocalWireModel.run_concat,measurementCount_append,hm,eq]

def finiteProgram (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  inputClass L C cy ++ prefixProgram L C ++
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ++ suffixProgram L C ++
  renameProgram (sigP L) (corners2 L C++Edges.sharedM L C) ++
  chainErase L.control L.point.finite L.genericSelect

theorem finite_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (s : State) (m : List Bool) :
    run (Edges.finiteProgramWith L C cy Gen (adapterProgram L C true) (adapterProgram L C false)) m s=
      run (finiteProgram L C cy Gen) m s := by
  let G := renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen))
  let T := renameProgram (sigP L) (corners2 L C++Edges.sharedM L C)++
    chainErase L.control L.point.finite L.genericSelect
  have a := same_context (genFlagN L++adapterProgram L C true) (prefixProgram L C)
    (inputClass L C cy) (G++(adapterProgram L C false++mergeFlagsN L)++T)
    (prefix_measurements L C) (prefix_run L hw hn C) s m
  have b := same_context (adapterProgram L C false++mergeFlagsN L) (suffixProgram L C)
    (inputClass L C cy++prefixProgram L C++G) T
    (suffix_measurements L C) (suffix_run L hw hn C) s m
  have a' : run (Edges.finiteProgramWith L C cy Gen (adapterProgram L C true) (adapterProgram L C false)) m s=
      run ((inputClass L C cy++prefixProgram L C++G)++(adapterProgram L C false++mergeFlagsN L)++T) m s := by
    simpa only [Edges.finiteProgramWith,G,T,List.append_assoc] using a
  exact a'.trans (by simpa only [finiteProgram,G,T,List.append_assoc] using b)

def wrapper (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram L C cy (renameProgram (Wrapper5.U L) Gen))

theorem wrapper_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (wrapper L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  have hs := Edges.finite_specWith L hw hn R hc b (renameProgram (Wrapper5.U L) Gen)
    (Wrapper5.genericOK_relabel L hw hc Gen hGen) (adapterProgram L (.some hc) true)
    (adapterProgram L (.some hc) false)
    (fun R b D G H cov old => boundary_step L hw hn hc true R b D G H false false cov
      (fun _ => ⟨rfl,rfl⟩) (by simp) old)
    (fun R b G D H cov old => boundary_step L hw hn hc false R b false G false D H cov
      (by simp) (fun _ => ⟨rfl,rfl⟩) old)
  intro s m hi
  have h := hs s m hi
  rw [finite_run L hw hn] at h
  unfold wrapper
  rw [Square5Placement.pool_relabel_state_eq L (Wrapper5.U L) (Wrapper5.U_pool L hw)
    (Wrapper5.U_outside L hw) _ s m hi.clean h.2.clean]
  exact h

theorem part_support (L : ControlledPointLayout) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    wires (prefixProgram L (.some hc))⊆wires (genFlagN L++clrDH L (.some hc) cy) ∧
    wires (suffixProgram L (.some hc))⊆wires (clrDH L (.some hc) cy++mergeFlagsN L) := by
  have localSub (cx cy : Bool) :
      wires (clearPrefix cx cy)⊆wires (gen++MeasuredDH.original true true cx cy) ∧
      wires (restoreSuffix cx cy)⊆wires (MeasuredDH.original true true cx cy++merge) := by
    cases cx <;> cases cy <;> decide
  have h := localSub (DHClass.cxk (.some hc)) (yBit (.some hc))
  have a := Finset.image_subset_image (f:=LocalWireModel.label (ports L (DHClass.kx (.some hc)))) h.1
  have b := Finset.image_subset_image (f:=LocalWireModel.label (ports L (DHClass.kx (.some hc)))) h.2
  simpa only [←renameProgram_support,rename_append,gen_at,merge_at,original_at,
    prefixProgram,suffixProgram] using And.intro a b

section
attribute [local irreducible] wires

theorem wrapper_support (L : ControlledPointLayout) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) (Gen : Program) :
    wires (wrapper L (.some hc) cy Gen)⊆wires (Edges.wrapper L (.some hc) cy Gen) := by
  have h := part_support L hc
  simp only [wrapper,Edges.wrapper,renameProgram_support]
  apply Finset.image_subset_image
  intro q hq
  simp only [finiteProgram,Edges.finiteProgram,wires_append,Finset.mem_union] at hq ⊢
  have a : q∈wires (prefixProgram L (.some hc)) →
      q∈wires (genFlagN L) ∨ q∈wires (clrDH L (.some hc) cy) := by
    intro ha
    simpa only [wires_append,Finset.mem_union] using h.1 ha
  have b : q∈wires (suffixProgram L (.some hc)) →
      q∈wires (clrDH L (.some hc) cy) ∨ q∈wires (mergeFlagsN L) := by
    intro hb
    simpa only [wires_append,Finset.mem_union] using h.2 hb
  tauto

end

private def physicalBool : Instr→Bool
  | .X _ => true
  | .CX a b => decide (a≠b)
  | .CCX a b c => decide (a≠b ∧ a≠c ∧ b≠c)
  | .measureX _ _ _ => true

theorem part_physical (cx cy : Bool) : GatePhysical (clearPrefix cx cy) ∧ GatePhysical (restoreSuffix cx cy) := by
  have all : (clearPrefix cx cy).all physicalBool=true ∧ (restoreSuffix cx cy).all physicalBool=true := by
    cases cx <;> cases cy <;> decide
  have lift (P : Program) (h : P.all physicalBool=true) : GatePhysical P := by
    intro i hi
    have hh := List.all_eq_true.mp h i hi
    cases i <;> simp_all [physicalBool,PhysicalInstr,ProperGate]
  exact ⟨lift _ all.1,lift _ all.2⟩

theorem part_support_range (cx cy : Bool) :
    wires (clearPrefix cx cy)⊆Finset.range 11 ∧ wires (restoreSuffix cx cy)⊆Finset.range 11 := by
  cases cx <;> cases cy <;> decide

theorem wrapper_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hGen : GatePhysical Gen) : GatePhysical (wrapper L C cy Gen) := by
  apply gatePhysical_rename _ (Wrapper5.U L).injective
  have old := Edges.finite_physical L hw hn C cy (renameProgram (Wrapper5.U L) Gen)
    (gatePhysical_rename _ (Wrapper5.U L).injective Gen hGen)
  have inj := LocalWireModel.label_injective _ (ports_injective L hw hn _ (DHClass.kx_lt C))
  have p := part_physical (DHClass.cxk C) (yBit C)
  have supp := part_support_range (DHClass.cxk C) (yBit C)
  have a : GatePhysical (prefixProgram L C) := gatePhysical_rename_support _ _
    (fun a ha b hb eq => inj a (supp.1 ha) b (supp.1 hb) eq) p.1
  have b : GatePhysical (suffixProgram L C) := gatePhysical_rename_support _ _
    (fun a ha b hb eq => inj a (supp.2 ha) b (supp.2 hb) eq) p.2
  simp only [finiteProgram,Edges.finiteProgram,gatePhysical_append] at old ⊢
  tauto

theorem pair_counts (cx cy : Bool) :
    toffoliCount (clearPrefix cx cy)+toffoliCount (restoreSuffix cx cy)+8≤
      toffoliCount gen+2*toffoliCount (MeasuredDH.original true true cx cy)+toffoliCount merge ∧
    measurementCount (clearPrefix cx cy)+measurementCount (restoreSuffix cx cy)+2≤
      measurementCount gen+2*measurementCount (MeasuredDH.original true true cx cy)+measurementCount merge ∧
    Challenge.gateSlots (clearPrefix cx cy)+Challenge.gateSlots (restoreSuffix cx cy)+10≤
      Challenge.gateSlots gen+2*Challenge.gateSlots (MeasuredDH.original true true cx cy)+Challenge.gateSlots merge := by
  cases cx <;> cases cy <;> decide

theorem wrapper_counts (L : ControlledPointLayout) (Gen : Program) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapper L (.some hc) cy Gen)+8≤toffoliCount (Edges.wrapper L (.some hc) cy Gen) ∧
    measurementCount (wrapper L (.some hc) cy Gen)+2≤measurementCount (Edges.wrapper L (.some hc) cy Gen) ∧
    Challenge.gateSlots (wrapper L (.some hc) cy Gen)+10≤Challenge.gateSlots (Edges.wrapper L (.some hc) cy Gen) := by
  have ot := renameProgram_counts (LocalWireModel.label (ports L (DHClass.kx (.some hc))))
    (MeasuredDH.original true true (DHClass.cxk (.some hc)) (yBit (.some hc)))
  have os := rename_gateSlots (LocalWireModel.label (ports L (DHClass.kx (.some hc))))
    (MeasuredDH.original true true (DHClass.cxk (.some hc)) (yBit (.some hc)))
  rw [original_at] at ot os
  have gt := renameProgram_counts (LocalWireModel.label (ports L (DHClass.kx (.some hc)))) gen
  have gs := rename_gateSlots (LocalWireModel.label (ports L (DHClass.kx (.some hc)))) gen
  have mt := renameProgram_counts (LocalWireModel.label (ports L (DHClass.kx (.some hc)))) merge
  have ms := rename_gateSlots (LocalWireModel.label (ports L (DHClass.kx (.some hc)))) merge
  rw [gen_at] at gt gs
  rw [merge_at] at mt ms
  have h := pair_counts (DHClass.cxk (.some hc)) (yBit (.some hc))
  simp only [wrapper,Edges.wrapper,finiteProgram,Edges.finiteProgram,prefixProgram,suffixProgram,
    toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen)
    (hG : wires Gen⊆(OB5Support.genericSites L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} wrapper L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (MeasuredDH.boundary_work L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  have old := Edges.wrapper_spec L hw hn R hc b Gen hGen s m hi
  have new := wrapper_spec L hw hn R hc b Gen hGen s m hi
  have oldSupport := (Edges.wrapper_support L hw hn (.some hc) cy Gen hG).trans
    (WrapperOB5.support_used L hw)
  rw [MeasuredDH.boundary_unique L _ _ ((wrapper_support L hc Gen).trans oldSupport)
    oldSupport s m _ b new.2 old.2 (new.1.trans old.1.symm)]
  exact Edges.full_spec L hw hn R hc b Gen hGen hG s m hs

end ECDSAAdd.Entrant.FusedFlags
end
