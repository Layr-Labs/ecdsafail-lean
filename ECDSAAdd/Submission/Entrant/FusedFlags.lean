import ECDSAAdd.Submission.Entrant.MeasuredDH
import ECDSAAdd.Submission.Entrant.LocalWireModel

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
  renameProgram (sigP L) (corners2 L C++Edges.shared L C) ++
  chainErase L.control L.point.finite L.genericSelect

theorem finite_run (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (s : State) (m : List Bool) :
    run (Edges.finiteProgramWith L C cy Gen (adapterProgram L C true) (adapterProgram L C false)) m s=
      run (finiteProgram L C cy Gen) m s := by
  let G := renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen))
  let T := renameProgram (sigP L) (corners2 L C++Edges.shared L C)++
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
