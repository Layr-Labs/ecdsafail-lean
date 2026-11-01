import ECDSAAdd.Submission.Entrant.NoThreeTorsion

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
