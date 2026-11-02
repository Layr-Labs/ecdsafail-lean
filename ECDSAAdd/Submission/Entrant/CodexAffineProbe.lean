import ECDSAAdd.Submission.Entrant.FusedBoundaryFinal
import ECDSAAdd.Submission.Entrant.CodexAffineMath
import ECDSAAdd.Submission.Entrant.CodexAffineGadget

/-! A reversible affine view combines the two low probe bits into their equality.
The arithmetic backend and public encoding are inherited unchanged. -/
namespace ECDSAAdd.Entrant.CodexAffineProbe
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def a (L : ControlledPointLayout) : Wire := FiniteFlagInterval.probeControl L
def b (L : ControlledPointLayout) : Wire := (FiniteFlagInterval.probeTail L).headD 0
def rest (L : ControlledPointLayout) : List Wire := (FiniteFlagInterval.probeTail L).tail
def work (L : ControlledPointLayout) : List Wire := L.dialogPool.take 246
def literal : Nat := 2^246-1
def finiteBit (v : Nat) : Bool := decide (¬ CodexAffineMath.matchesX v)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
theorem tail_cons : FiniteFlagInterval.probeTail L = b L :: rest L := by
  have h := FiniteFlagInterval.probeTail_length L hw
  unfold b rest
  cases e : FiniteFlagInterval.probeTail L with
  | nil => simp [e] at h
  | cons q qs => rfl

include hw in
theorem lengths : (rest L).length=246 ∧ (work L).length=246 := by
  simp [rest,work,FiniteFlagInterval.probeTail_length L hw,L.dialogPool_length hw]

theorem work_subset : work L ⊆ L.dialogPool.take 247 := by
  have h : work L=(L.dialogPool.take 247).take 246 := by
    simp only [work,List.take_take]; rfl
  rw [h]
  exact List.take_subset _ _

include hw hn in
theorem ports_nodup : (a L :: b L :: L.point.finite :: (rest L ++ work L)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (FiniteFlagInterval.probe_nodup L hw hn) q
  have hp : (work L).count q ≤ (L.dialogPool.take 247).count q := by
    have sub : (work L).Sublist (L.dialogPool.take 247) := by
      have e : work L=(L.dialogPool.take 247).take 246 := by
        simp only [work,List.take_take]; rfl
      rw [e]; exact List.take_sublist _ _
    exact sub.count_le q
  rw [tail_cons L hw] at h
  simp only [a,List.count_cons,List.count_append] at h ⊢
  omega

include hw in
theorem inputs_mem : a L∈L.point.x ∧ b L∈L.point.x ∧ ∀q∈rest L,q∈L.point.x := by
  refine ⟨FiniteFlagInterval.probeControl_mem L hw,?_,?_⟩
  · apply FiniteFlagInterval.probeTail_mem L
    rw [tail_cons L hw]; simp
  · intro q hq
    exact FiniteFlagInterval.probeTail_mem L q (List.mem_of_mem_tail hq)

include hw in
theorem hit (s : BasisState) :
    (!(s (b L) ^^ s (a L)) && decide (regValue (rest L) s=literal)) =
      decide (CodexAffineMath.matchesX (regValue L.point.x s)) := by
  have h := FiniteFlagInterval.probe_value L hw s
  rw [FiniteFlagInterval.probe_cons L hw,tail_cons L hw] at h
  exact CodexAffineMath.probe_bridge (s (a L)) (s (b L))
    (regValue (rest L) s) (regValue L.point.x s) h

def clrF : Program := CodexAffineGadget.program (a L) (b L) L.point.finite (rest L) (work L) literal
def clearF : Program := CodexAffineGadget.clearProgram (a L) (b L) L.point.finite (rest L) (work L) literal

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0) :
    run (clrF L) m s = ⟨s.phase,writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ finiteBit (regValue L.point.x s.basis))⟩ := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have hk : literal < 2^(rest L).length := by rw [(lengths L hw).1]; decide
  rw [clrF,CodexAffineGadget.program_run _ _ _ _ _ _ (ports_nodup L hw hn) hl hk s m hz,
    hit L hw s.basis]
  simp only [finiteBit,decide_not]

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  exact CodexAffineGadget.clearProgram_eq _ _ _ _ _ _ (ports_nodup L hw hn)
    ((lengths L hw).1.trans (lengths L hw).2.symm)
    (by rw [(lengths L hw).1]; decide) s m hz hzero

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite=base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite∉L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [←v.x]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit,this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [←v.y]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit,this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit,Ne.symm (fin_ne_generic L hn),v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [←v.clean]; apply regValue_congr; intro q hq
    have : q≠L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit,this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q=writeBit base L.point.finite _ q
    by_cases hqf : q=L.point.finite
    · subst hqf; simp [writeBit,hfs,v.x]
    · simp [writeBit,hqf,v.rest q hq]

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=finiteBit X.val) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz]
    simp [writeBit,v.x,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

include hw in
theorem clrF_support_old : wires (clrF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [FiniteFlagInterval.old_clrF_support L hw]
  intro q hq
  have h := CodexAffineGadget.program_support (a L) (b L) L.point.finite (rest L) (work L) literal
    ((lengths L hw).1.trans (lengths L hw).2.symm) hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  have inputs := inputs_mem L hw
  rcases h with rfl | rfl | rfl | h | h
  · tauto
  · tauto
  · tauto
  · exact Or.inr (Or.inl (inputs.2.2 q h))
  · apply Or.inr; apply Or.inr
    have sub : L.dialogPool.take 247 ⊆ L.dialogPool.take 255 := by
      have e : L.dialogPool.take 247=(L.dialogPool.take 255).take 247 := by rw [List.take_take]; rfl
      rw [e]; exact List.take_subset _ _
    exact sub (work_subset L h)

include hw in
theorem clearF_support_old : wires (clearF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) :=
  (CodexAffineGadget.clearProgram_support (a L) (b L) L.point.finite (rest L) (work L) literal).trans
    (clrF_support_old L hw)

include hw in
theorem counts :
    toffoliCount (clrF L)=246 ∧ measurementCount (clrF L)=246 ∧
    toffoliCount (clearF L)=245 ∧ measurementCount (clearF L)=246 := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have p := CodexAffineGadget.program_counts (a L) (b L) L.point.finite (rest L) (work L) literal hl
  have c := CodexAffineGadget.clearProgram_counts (a L) (b L) L.point.finite (rest L) (work L) literal hl
  simpa only [(lengths L hw).1,clrF,clearF] using And.intro p.1 (And.intro p.2 c)

include hw hn in
theorem physical : GatePhysical (clrF L) ∧ GatePhysical (clearF L) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  exact ⟨CodexAffineGadget.program_physical _ _ _ _ _ _ hl (ports_nodup L hw hn),
    CodexAffineGadget.clearProgram_physical _ _ _ _ _ _ hl (ports_nodup L hw hn)⟩

abbrev zrep := FiniteFlagInterval.zrep
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L

theorem sentinel_finiteBit : finiteBit FiniteFlagInterval.sentinel=false := by
  have eq : FiniteFlagInterval.sentinel=p-1 := by norm_num [FiniteFlagInterval.sentinel,p]
  simp [finiteBit,eq,CodexAffineMath.sentinel_matches]

include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : finiteBit X.val = fin) (h2 : finiteBit X'.val = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val))
        L.point.finite ^^ finiteBit X'.val) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := FiniteFlagInterval.zrep_step L hw hn 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (FiniteFlagInterval.sentinel : Fp) 0 (FiniteFlagInterval.sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (FiniteFlagInterval.sentinel : Fp) 0 cx cy base' FiniteFlagInterval.sentinel_ne_zero) hfin
      (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit) (by rw [FiniteFlagInterval.sentinel_val]; exact sentinel_finiteBit)
    have z2 := FiniteFlagInterval.zrep_step L hw hn (FiniteFlagInterval.sentinel : Fp) 0 0 false s.basis (by rw [hfin, FiniteFlagInterval.sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : finiteBit x.val = true := decide_eq_true (CodexAffineMath.curve_x_not_matches hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := FiniteFlagInterval.zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : finiteBit (genericX x y cx cy).val = true :=
        decide_eq_true (CodexAffineMath.curve_x_not_matches (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := FiniteFlagInterval.zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := FiniteFlagInterval.zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))


omit hw hn

include hw in
theorem gen_support_subset (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) := by
  intro q used
  have hz : q∈wires (zrep L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => FiniteFlagInterval.zrep_support_old L hw h
  have hc : q∈wires (clrF L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clrF_support_old L hw h
  have he : q∈wires (clearF L) → q∈wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clearF_support_old L hw h
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,
    generic,wires_append,Finset.mem_union] at used ⊢
  tauto

include hw hn in
theorem gen_sites (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (ReflectionE1TickGapLow48.gen_sites L hw hn cx cy)

attribute [local irreducible] toffoliCount measurementCount gateSlots ReflectionE1TickGapLow48.generic

include hw in
theorem gen_counts (cx cy : Fp) :
    toffoliCount (gen L cx cy)+2=toffoliCount (FiniteFlagInterval.gen L cx cy) ∧
    measurementCount (gen L cx cy)+2=measurementCount (FiniteFlagInterval.gen L cx cy) := by
  have n := counts L hw
  have o := FiniteFlagInterval.clrF_counts L hw
  have e := FiniteFlagInterval.clearF_counts L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,toffoliCount_append,measurementCount_append,n.1,n.2.1,n.2.2.1,n.2.2.2,
    o.1,o.2,e.1,e.2]
  omega

include hw in
theorem gen_slots (cx cy : Fp) : gateSlots (gen L cx cy)≤gateSlots (FiniteFlagInterval.gen L cx cy) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have n := CodexAffineGadget.program_slots (a L) (b L) L.point.finite (rest L) (work L) literal hl
  have e := CodexAffineGadget.clearProgram_slots (a L) (b L) L.point.finite (rest L) (work L) literal hl
  rw [(lengths L hw).1] at n e
  change gateSlots (clrF L)≤9*246+6 at n
  change gateSlots (clearF L)≤9*246+6 at e
  have o := FiniteFlagInterval.clrF_slots_exact L hw
  have c := FiniteFlagInterval.clearF_slots L hw
  simp only [gen,mid,FiniteFlagInterval.gen,FiniteFlagInterval.mid,FiniteFlagInterval.generic,
    generic,zrep,gateSlots_append]
  omega

include hw hn in
theorem gen_physical (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := FiniteFlagInterval.zrep_physical L hn
  have c := (physical L hw hn).1
  have e := (physical L hw hn).2
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic,zrep] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

include hw in
theorem wrapper_counts (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+2=
      toffoliCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+2=
      measurementCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy))≤
      gateSlots (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) := by
  have h := gen_counts L hw cx cy
  have s := gen_slots L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 := by
  have h := FiniteFlagInterval.wrapper_support_mono layout C cy _ _
    (gen_support_subset layout layout_widths cx cy)
  exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
    (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151533,1499140,1587,50174866⟩

theorem program_correct (C : Point) (control : Bool) (R : Point) :
    Triple (encodes control R) (program C) (encodes control (if control then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ control R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc control _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151533 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤2151533
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1499140 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤1499140
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1587 := by
  cases C with
  | zero => change qubits []≤1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50174866 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.2
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=4581 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤50174866
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499140
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50174866
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.CodexAffineProbe
