import ECDSAAdd.Submission.Entrant.MainPart06

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Generic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square

/-! Keep the checked E1 entries and TickGap tails. Replace only the reflected square prefix. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def squareEntry (L : ControlledPointLayout) (k : Fp) : Program :=
  R2SqEp760.program760 L++E1ReflectedPlacement.entryR L k

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  squareEntry L k++ReflectionE1TickGap.restX L++exitY L cy


theorem squareEntry_base (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m1 m2 : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) m1 s=
      run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++
        E1QubitPlacement.tickF L) m2 s := by
  let n1:=measurementCount (R2SqEp760.program760 L)
  let n2:=measurementCount (SquareCarryLoan719BF.program L)
  obtain ⟨a,ha⟩ : ∃a : State,run (R2SqEp760.program760 L) (m1.take n1) s=a := ⟨_,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : State,run (SquareCarryLoan719BF.program L) (m2.take n2) s=r := ⟨_,rfl⟩
  have fresh:=R2SqEp760.program760_boundary L hw hn X Y G origin s (m1.take n1) v
  have prior:=SquareCarryLoan719BF.step L hw hn X Y G origin s (m2.take n2) v
  rw [ha] at fresh
  rw [hr] at prior
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  let R:=p-1-Z.val
  have ppos : 0<p := by norm_num [p]
  have rp : R<p := by
    change p-1-Z.val<p
    omega
  have ax : regValue L.point.x a.basis=R:=fresh.2.1
  have ag : a.basis L.core.generic=G :=
    (fresh.2.2 _ (((E1QubitPlacement.lay L hw hn _).2.2 rfl).1)).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ s.basis
      (fun q hq=>fresh.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).1)),v.clean]
  have involution (n : Nat) (bound : n<p) : n=p-1-(p-1-n) := by omega
  have rx : regValue L.point.x r.basis=p-1-R := by
    have value : regValue L.point.x r.basis=Z.val:=prior.2.x
    exact value.trans (involution Z.val Z.isLt)
  have outside (q : Wire) (hq : q∉L.point.x) : r.basis q=a.basis q := by
    have oldFrame : r.basis q=s.basis q := by
      by_cases hy : q∈L.point.y
      · exact (regValue_eq_iff _ _ _).mp (prior.2.y.trans v.y.symm) q hy
      · have away : q∉L.point.x++L.point.y:=by simp only [List.mem_append,not_or];exact ⟨hq,hy⟩
        exact (prior.2.rest q away).trans (v.rest q away).symm
    exact oldFrame.trans (fresh.2.2 q hq).symm
  have eq:=E1ReflectedPlacement.entryR_eq L hw hn k a r R rp G ax ag ac
    (prior.1.trans fresh.1.symm) rx outside (m1.drop n1) (m2.drop n2)
  simpa only [squareEntry,run_append,n1,n2,ha,hr,List.append_assoc] using eq

theorem squareEntry_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (mNew mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) mNew s=run (ReflectionE1.squareEntry L k) mOld s :=
  (squareEntry_base L hw hn k X Y G origin s mNew [] v).trans
    (ReflectionE1.squareEntry_eq L hw hn k X Y G origin s mOld [] v).symm

section CorrectStages
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  have prior:=ReflectionE1TickGap.secondStage_step L hw hn X Y k cy G origin hx
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k) (B:=ReflectionE1.squareEntry L k)
    (R:=ReflectionE1TickGap.restX L++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [ReflectionE1TickGap.secondStage,List.append_assoc] using prior

end CorrectStages

/-- The second stage with the last reverse tick and the trailing constant negation merged. -/
def secondStageX (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  squareEntry L k++ExitMergeKernel.restXX L cx.val++exitY L cy

section CorrectStagesX
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem secondStageX_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageX L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=ExitMergeKernel.fusedMultiplyX_step L hw hn
    (FrontierEntry1591Callers.exit (ExitMergeKernel.kernelX cx.val) L) cx
    (ExitMergeKernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageX,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ExitMergeKernel.restXX L cx.val++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ExitMergeKernel.exit_splitX,List.append_assoc,Z] using prior

end CorrectStagesX

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ReflectionE1TickGap.entryStage L (-cx) (-cy)++secondStageX L (ReflectionE1.correction cx) cy cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=ReflectionE1TickGap.entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageX_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=ReflectionE1TickGap.entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageX_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second


theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
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
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Correct

attribute [local irreducible] squareEntry secondStage generic mid gen
  ReflectionE1.squareEntry ReflectionE1Square.program ReflectionE1Low48Square.program
  ReflectionE1TickGap.entryStage ReflectionE1TickGap.secondStage ReflectionE1TickGap.restX
  ReflectionE1TickGap.generic ReflectionE1TickGap.gen

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (P Q : Program) : Prop :=
  toffoliCount P+494=toffoliCount Q ∧ measurementCount P+333=measurementCount Q ∧
    gateSlots P≤gateSlots Q+22000

private def context (A P B : Program) : Program := A++(P++B)

private theorem context_facts2 (A P Q B B' : Program)
    (h : toffoliCount P+243=toffoliCount Q ∧ measurementCount P+85=measurementCount Q ∧
      gateSlots P≤gateSlots Q)
    (h' : toffoliCount B+251=toffoliCount B' ∧ measurementCount B+248=measurementCount B' ∧
      gateSlots B≤gateSlots B'+22000) :
    Facts (context A P B) (context A Q B') := by
  rcases h with ⟨ht,hm,hs⟩
  rcases h' with ⟨ht',hm',hs'⟩
  simp only [Facts,context,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem context_wires (A P Q B : Program) :
    wires (context A P B)⊆wires (context A Q B)∪wires P := by
  intro q hq
  simp only [context,wires_append,Finset.mem_union] at hq ⊢
  tauto

private def suffix (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  E1ReflectedPlacement.entryR L (ReflectionE1.correction cx)++ReflectionE1TickGap.restX L++
    exitY L cy++fastConstNeg L cx

/-- The new suffix: the multiplication kernel ends in the merged exit, no trailing negation. -/
private def suffixX (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  E1ReflectedPlacement.entryR L (ReflectionE1.correction cx)++ExitMergeKernel.restXX L cx.val++
    exitY L cy

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=context (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (R2SqEp760.program760 L) (suffixX L cx cy) := by
  unfold generic secondStageX squareEntry context suffixX
  simp only [List.append_assoc]

private theorem suffix_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (suffixX L cx cy)+251=toffoliCount (suffix L cx cy) ∧
    measurementCount (suffixX L cx cy)+248=measurementCount (suffix L cx cy) ∧
    gateSlots (suffixX L cx cy)≤gateSlots (suffix L cx cy)+22000 := by
  have r := ExitMergeKernel.restXX_metrics L cx.val
  have n := fastConstNeg_counts L hw cx
  simp only [suffixX,suffix,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1TickGap.generic L cx cy=context (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (ReflectionE1Square.program L) (suffix L cx cy) := by
  unfold ReflectionE1TickGap.generic ReflectionE1TickGap.secondStage ReflectionE1.squareEntry context suffix
  simp only [List.append_assoc]

private theorem generic_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Facts (generic L cx cy) (ReflectionE1TickGap.generic L cx cy) := by
  exact relation_of_shapes Facts _ _ _ _ (generic_shape L cx cy) (old_generic_shape L cx cy)
    (context_facts2 (ReflectionE1TickGap.entryStage L (-cx) (-cy)) _ _ (suffixX L cx cy) (suffix L cx cy)
      ⟨(R2SqEp760.counts_diff760 L hw).1,(R2SqEp760.counts_diff760 L hw).2,R2SqEp760.slots_le760 L hw⟩
      (suffix_facts L hw cx cy))

/-- The new square adds its host site; the merged exit adds only its placed circuit. -/
theorem generic_support_envelope (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1TickGap.generic L cx cy)∪wires (R2SqEp760.program760 L)∪
      wires (renameProgram (wireFn2 L) (renameProgram Rolling1588Lifetime.phaseHost
        (ExitMergeKernel.x1 cx.val))) := by
  rw [generic_shape,old_generic_shape]
  intro q hq
  have rx := ExitMergeKernel.restXX_support L cx.val
  simp only [context,suffixX,suffix,wires_append,Finset.mem_union] at hq ⊢
  rcases hq with h|h|(h|h)|h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl h))))))
  · rcases Finset.mem_union.mp (rx h) with h'|h'
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h'))))))
    · exact Or.inr h'
  · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr h)))))

private def logicalTargetX (i : Nat) : Nat :=
  if i=1800 then 2312 else if i=770 then 1026 else if i=1285 then 1541 else
    if i=1286 then 1542 else if i=769 then 1797 else i

private theorem target_factsX (L : ControlledPointLayout) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    wireFn2 L (base (logicalTargetX i))=L.core.poolWire i ∧
    base (logicalTargetX i)∈OB5Support.logicalSites ∧
    logicalTargetX i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨rfl,?_,by decide⟩
  all_goals
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    simp only [logicalTargetX,OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    norm_num

private theorem placedX1_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (renameProgram (wireFn2 L) (renameProgram Rolling1588Lifetime.phaseHost
      (ExitMergeKernel.x1 k))) := by
  obtain ⟨map,logical,target⟩:=target_factsX L i hi
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩:=Finset.mem_image.mp used
  have same : wireFn2 L q=wireFn2 L (base (logicalTargetX i)):=eq.trans map.symm
  have back:=(placement2 L hw hn).injectiveOnSlots q
    (ArithmeticOB5.logical_sub_old (ExitMergeKernel.hostedX1_logical k hq)) (base (logicalTargetX i))
    (ArithmeticOB5.logical_sub_old logical) same
  rw [back] at hq
  obtain ⟨j,e,hj⟩ := ExitMergeKernel.hostedX1_labels k _ hq
  exact E1QubitPlacement.sw_avoid j hj (base_injective e ▸ target)

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_envelope L cx cy).trans (Finset.union_subset (Finset.union_subset
    (ReflectionE1TickGap.generic_sites L hw hn cx cy) (R2SqEp760.program760_support L hw hn))
    (ExitMergeKernel.placedX1_sites L hw cx.val))

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) := by
  intro used
  rcases Finset.mem_union.mp (generic_support_envelope L cx cy used) with old|x
  · rcases Finset.mem_union.mp old with old|sq
    · exact ReflectionE1TickGap.generic_free L hw hn cx cy i hi old
    · exact R2SqEp760.program760_free_old L hw hn i hi sq
  · exact placedX1_free L hw hn cx.val i hi x

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old:=fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1TickGap.generic_physical L hw hn cx cy)
  have rx := ExitMergeKernel.restXX_physical L hw hn cx.val
  simp only [context,suffix,gatePhysical_append] at old
  rw [generic_shape]
  simp only [context,suffixX,gatePhysical_append]
  exact ⟨old.1,R2SqEp760.program760_physical L hw hn,⟨old.2.2.1.1.1,rx⟩,old.2.2.1.2⟩

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program) (h : Facts P Q) :
    Facts (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs⟩
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Facts (gen L cx cy) (ReflectionE1TickGap.gen L cx cy) := by
  apply relation_of_shapes Facts _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1TickGap.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1TickGap.gen ReflectionE1TickGap.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L hw cx cy)

theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+494=toffoliCount (ReflectionE1TickGap.gen L cx cy) ∧
    measurementCount (gen L cx cy)+333=measurementCount (ReflectionE1TickGap.gen L cx cy) ∧
    gateSlots (gen L cx cy)≤gateSlots (ReflectionE1TickGap.gen L cx cy)+22000 :=
  ⟨(gen_facts L hw cx cy).1,(gen_facts L hw cx cy).2.1,(gen_facts L hw cx cy).2.2⟩

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts P Q) :
    toffoliCount (Edges.wrapper L C cy P)+494=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)+333=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P)≤gateSlots (Edges.wrapper L C cy Q)+22000 := by
  rcases h with ⟨ht,hm,hs⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2151070 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout layout_widths cx cy)).1
  have old:=ReflectionE1TickGap.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1498883 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout layout_widths cx cy)).2.1
  have old:=ReflectionE1TickGap.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50211199+Rolling1588.slotGrowth := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout layout_widths cx cy)).2.2
  have old:=ReflectionE1TickGap.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end -- original module boundary

-- ===== R2 (retired poolWire 760) =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000


/-! ### R2: the retired pool wire `poolWire 760` is absent from the final generic point program. -/
namespace ECDSAAdd.Entrant.R2Final760
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] wires

theorem logical760 : base 760∈OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨760,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  omega

theorem placed_760 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (K : Program) (ks : wires K⊆OB5Support.logicalSites) (kf : base 760∉wires K) :
    L.core.poolWire 760∉wires (renameProgram (wireFn2 L) K) := by
  have map : wireFn2 L (base 760)=L.core.poolWire 760 := rfl
  rw [renameProgram_support]
  intro used
  obtain ⟨old,oldUsed,eq⟩:=Finset.mem_image.mp used
  have mapped : wireFn2 L old=wireFn2 L (base 760) := by rw [map];exact eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (ks oldUsed)) (base 760)
    (ArithmeticOB5.logical_sub_old logical760) mapped
  exact kf (back ▸ oldUsed)

private theorem sw_rho_760 (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
      j=721 ∨ j=722 ∨ j=2400) :
    E1QubitPlacement.sw (E1QubitPlacement.rhoN j)≠760 := by
  have range:=E1QubitPlacement.rhoN_range j hj
  generalize E1QubitPlacement.rhoN j=i at range ⊢
  unfold E1QubitPlacement.Rng at range
  unfold E1QubitPlacement.sw
  split_ifs <;> omega

theorem entryM_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    L.core.poolWire 760∉wires (E1QubitPlacement.entryM L k) := by
  rw [E1QubitPlacement.entryM_eq]
  apply placed_760 L hw hn _ (E1QubitPlacement.logicalM k.val)
  intro h
  obtain ⟨j,e,hj⟩ := E1QubitPlacement.merged_labels k.val (base 760) h
  exact sw_rho_760 j hj (base_injective e).symm

private theorem reflected_logical (k : Nat) :
    wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k)))⊆OB5Support.logicalSites := by
  intro q hq
  simp only [renameProgram_support,Finset.mem_image] at hq
  obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩:=hq
  obtain ⟨j,rfl,hj⟩:=E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k hb)
  rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range j hj)

theorem entryR_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    L.core.poolWire 760∉wires (E1ReflectedPlacement.entryR L k) := by
  have logicalFree : base 760∉wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k.val))) := by
    intro h
    simp only [renameProgram_support,Finset.mem_image] at h
    obtain ⟨a,⟨b,hb,rfl⟩,eq⟩ := h
    obtain ⟨j,rfl,hj⟩ := E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k.val hb)
    rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base] at eq
    exact sw_rho_760 j hj (base_injective eq)
  have h:=placed_760 L hw hn _ (reflected_logical k.val) logicalFree
  simpa only [E1ReflectedPlacement.entryR,renameProgram_comp,E1QubitPlacement.pmapR,
    E1QubitPlacement.pmap,Function.comp_def] using h

private theorem suffix_free (P Q R : Program) (q : Wire) (shape : P=Q++R) (free : q∉wires P) :
    q∉wires R := by
  rw [shape,wires_append] at free
  exact fun h => free (Finset.mem_union_right _ h)

theorem restE_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (kernel : base 760∉wires Rolling1588TickGap.entryKernel) :
    L.core.poolWire 760∉wires (ReflectionE1TickGap.restE L) :=
  suffix_free _ _ _ _ (ReflectionE1TickGap.entry_split L)
    (placed_760 L hw hn _ Rolling1588TickGap.entryKernel_support kernel)

theorem restX_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (kernel : base 760∉wires Rolling1588TickGap.exitKernel) :
    L.core.poolWire 760∉wires (ReflectionE1TickGap.restX L) :=
  suffix_free _ _ _ _ (ReflectionE1TickGap.exit_split L)
    (placed_760 L hw hn _ Rolling1588TickGap.exitKernel_support kernel)

theorem generic_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryK : base 760∉wires Rolling1588TickGap.entryKernel)
    (_exitK : base 760∉wires Rolling1588TickGap.exitKernel)
    (square : L.core.poolWire 760∉wires (R2SqEp760.program760 L)) (cx cy : Fp) :
    L.core.poolWire 760∉wires (ReflectionE1TickGapLow48.generic L cx cy) := by
  have bounds : 515≤760 ∧ 760<2613 := by omega
  have y := ExitGenericQ5.constant_ports_avoid_large L hw hn 760 bounds L.point.y (Or.inr rfl)
  have ey := exitY_support L hw cy
  have fy := fusedY_support L hw (-cy)
  have rx : L.core.poolWire 760∉wires (ExitMergeKernel.restXX L cx.val) :=
    suffix_free _ _ _ _ (ExitMergeKernel.exit_splitX L cx.val)
      (placed_760 L hw hn _ (ExitMergeKernel.kernelX_support cx.val) (ExitMergeKernel.kernelX_760_free cx.val))
  simp only [ReflectionE1TickGapLow48.generic,ReflectionE1TickGap.entryStage,
    ReflectionE1TickGapLow48.secondStageX,ReflectionE1TickGapLow48.squareEntry,
    wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨fun h=>y (fy h),entryM_760_free L hw hn (-cx)⟩,restE_760_free L hw hn entryK⟩,
    ⟨⟨⟨square,entryR_760_free L hw hn _⟩,rx⟩,fun h=>y (ey h)⟩⟩

end ECDSAAdd.Entrant.R2Final760

namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

theorem generic_760_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : L.core.poolWire 760∉wires (generic L cx cy) :=
  R2Final760.generic_760_free L hw hn Rolling1588TickGap.entryKernel_760_free
    Rolling1588TickGap.exitKernel_760_free (R2SqEp760.square760_free L hw hn) cx cy

/-- R2: the Low48 point with the lifetime halves and renamed endpoints/square uses 1587 qubits. -/
theorem wrapper_qubits760 (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits760 _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp))
    (generic_760_free layout layout_widths layout_nodup cx cy) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Final =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Low48Generic

/-! E1/reflected Q1588 with TickGap tails and the Low48 square prefix. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151070,1498883,1588,50211199+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2151070 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1498883 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50211199+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1498883
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50211199+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1

def sentinel : Nat := 115792089237316195423570985008687907853269984665640564039457584007908834671662
def sentinelHigh : Nat := 452312848583266388373324160190187140051835877600158453279131187530910662655

/-- Bits 1, 2, 5, 10..31 and 33..255 of `v`, packed in this order. -/
def probeVal (v : Nat) : Nat :=
  v / 2 % 4 + 4 * (v / 32 % 2) + 8 * (v / 1024 % 4194304) + 33554432 * (v / 8589934592)

theorem nonresidue_0 : ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem nonresidue_1 : ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem nonresidue_2 : ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem interval_nonresidue (n : Nat)
    (hn : n = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      n = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      n = 115792089237316195423570985008687907853269984665640564039457584007908834671662) :
    ((n : Fp)^3 + 7)^((p-1)/2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by norm_num [p]
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  have transport (q a : Nat) (hq : q = p)
      (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
      ((a : Fp)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    subst q
    exact h
  rcases hn with rfl | rfl | rfl
  · exact transport _ _ hp nonresidue_0
  · exact transport _ _ hp nonresidue_1
  · exact transport _ _ hp nonresidue_2

theorem curve_x_not_interval {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ (x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671662) := by
  intro h
  have power := interval_nonresidue x.val h
  rw [ZMod.natCast_zmod_val] at power
  have eq := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at eq
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using eq
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y ≠ 0 := by
    intro hz
    rw [← square,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1 = 2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,square,power] at fermat
  have two : ((2 : Nat) : Fp) = 0 := by
    have sum : (-1 : Fp)+1 = 1+1 := by rw [fermat]
    rw [neg_add_cancel] at sum
    exact_mod_cast (by rw [sum]; norm_num : (2 : Fp) = 0)
  rw [ZMod.natCast_eq_zero_iff] at two
  norm_num [p] at two

theorem probe_cases (v : Nat)
    (hv : v < 115792089237316195423570985008687907853269984665640564039457584007908834671663)
    (h : probeVal v = sentinelHigh) :
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      v = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      v = 115792089237316195423570985008687907853269984665640564039457584007908834671662 := by
  unfold probeVal sentinelHigh at h
  omega

theorem curve_x_high_ne {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    probeVal x.val ≠ sentinelHigh := by
  intro h
  apply curve_x_not_interval hc
  have hv : x.val < 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    have hp : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by norm_num [p]
    exact lt_of_lt_of_eq (ZMod.val_lt x) hp
  exact probe_cases x.val hv h

theorem sentinel_lt : sentinel < p := by norm_num [sentinel,p]
theorem sentinel_val : (sentinel : Fp).val = sentinel :=
  ZMod.val_natCast_of_lt sentinel_lt
theorem sentinel_ne_zero : (sentinel : Fp) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [sentinel_val,ZMod.val_zero] at this
  norm_num [sentinel] at this
theorem sentinel_high : probeVal sentinel = sentinelHigh := by
  unfold probeVal sentinel sentinelHigh
  norm_num

end ECDSAAdd.Entrant.FiniteFlagInterval
end

section
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic

theorem drop_sublist_drop (r : List Wire) (a b : Nat) (hab : a ≤ b) : (r.drop b).Sublist (r.drop a) := by
  have e : r.drop b = (r.drop a).drop (b - a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e]
  exact List.drop_sublist _ _

theorem seg_sublist (r rest : List Wire) (a k : Nat) (h : rest.Sublist (r.drop (a + k))) :
    ((r.drop a).take k ++ rest).Sublist (r.drop a) := by
  have e : (r.drop a).drop k = r.drop (a + k) := by
    rw [List.drop_drop]
  conv_rhs => rw [← List.take_append_drop k (r.drop a)]
  exact List.Sublist.append (List.Sublist.refl _) (e ▸ h)

theorem probe_sublist_gen (r : List Wire) :
    ((r.drop 1).take 2 ++ (r.drop 5).take 1 ++ (r.drop 10).take 22 ++ r.drop 33).Sublist r := by
  simp only [List.append_assoc]
  have hD : (r.drop 33).Sublist (r.drop (10 + 22)) := drop_sublist_drop r _ _ (by omega)
  have hC := seg_sublist r _ 10 22 hD
  have hB := seg_sublist r _ 5 1 ((hC).trans (drop_sublist_drop r _ _ (by omega)))
  have hA := seg_sublist r _ 1 2 ((hB).trans (drop_sublist_drop r _ _ (by omega)))
  exact hA.trans (List.drop_sublist _ _)

theorem probe_value_gen (r : List Wire) (hr : r.length = 256) (s : BasisState) :
    regValue ((r.drop 1).take 2 ++ (r.drop 5).take 1 ++ (r.drop 10).take 22 ++ r.drop 33) s =
      probeVal (regValue r s) := by
  have seg (a k : Nat) (h : a + k ≤ 256) :
      regValue ((r.drop a).take k) s = regValue r s / 2^a % 2^k := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by simp [hr]; omega),
      CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega)]
  have e1 := seg 1 2 (by norm_num)
  have e2 := seg 5 1 (by norm_num)
  have e3 := seg 10 22 (by norm_num)
  have e4 := CuccaroStreamedSquareWideLayout.regValue_drop_div r 33 (by omega) s
  simp only [Arithmetic.regValue_append, List.length_append, List.length_take, List.length_drop, hr,
    e1, e2, e3, e4, probeVal]
  norm_num

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalGadget =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

def probeX (L : ControlledPointLayout) : List Wire :=
  (L.point.x.drop 1).take 2 ++ (L.point.x.drop 5).take 1 ++ (L.point.x.drop 10).take 22 ++ L.point.x.drop 33
def probeControl (L : ControlledPointLayout) : Wire := (probeX L).headD 0
def probeTail (L : ControlledPointLayout) : List Wire := (probeX L).tail
def zrep (L : ControlledPointLayout) : Program :=
  [.X L.point.finite] ++ maskedConstant L.point.finite L.point.x sentinel ++ [.X L.point.finite]
def clrF (L : ControlledPointLayout) : Program :=
  [.X L.point.finite] ++ equalConstant (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw in
theorem probe_length : (probeX L).length = 248 := by
  simp [probeX,show L.point.x.length = 256 from hw.inputX]
include hw in
theorem probe_cons : probeX L = probeControl L :: probeTail L := by
  have h := probe_length L hw
  unfold probeControl probeTail
  cases e : probeX L with
  | nil => simp [e] at h
  | cons a t => rfl
include hw in
theorem probeTail_length : (probeTail L).length = 247 := by
  simp [probeTail,probe_length L hw]
include hw in
theorem probeControl_mem : probeControl L ∈ L.point.x := by
  apply (probe_sublist_gen L.point.x).subset
  change probeControl L ∈ probeX L
  rw [probe_cons L hw]
  simp
theorem probeTail_mem (q : Wire) (hq : q ∈ probeTail L) : q ∈ L.point.x :=
  (probe_sublist_gen L.point.x).subset (show q ∈ probeX L from List.mem_of_mem_tail hq)
include hw in
theorem work_length : (L.dialogPool.take 247).length = 247 := by
  simp [L.dialogPool_length hw]
include hw hn in
theorem probe_nodup :
    (probeControl L :: L.point.finite :: probeTail L ++ L.dialogPool.take 247).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 247 L.dialogPool).count_le q
  have hx := (probe_sublist_gen L.point.x).count_le q
  have hc := congrArg (List.count q) (probe_cons L hw)
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
    List.count_nil,List.cons_append] at h hc ⊢
  change (probeX L).count q ≤ L.point.x.count q at hx
  omega
include hw hn in
theorem finite_ne_probe : L.point.finite ≠ probeControl L := by
  intro h
  apply fin_not_x L hn
  rw [h]
  exact probeControl_mem L hw
include hw in
theorem probe_value_cons (s : BasisState) :
    regValue (probeX L) s = (if s (probeControl L) then 1 else 0) + 2*regValue (probeTail L) s := by
  conv_lhs => rw [probe_cons L hw]
  rfl
include hw in
theorem probe_value (s : BasisState) : regValue (probeX L) s = probeVal (regValue L.point.x s) :=
  probe_value_gen L.point.x hw.inputX s

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (L.dialogPool.take 247) s.basis = 0) :
    run (clrF L) m s = ⟨s.phase, writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ decide (regValue (probeX L) s.basis ≠ sentinelHigh))⟩ := by
  have nd := probe_nodup L hw hn
  have hfx := finite_ne_probe L hw hn
  have hft : L.point.finite ∉ (probeTail L) := by
    intro h; exact fin_not_x L hn (probeTail_mem L _ h)
  have hfp : L.point.finite ∉ L.dialogPool.take 247 := by
    intro h
    have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take h)
    simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons,
      beq_self_eq_true, if_true] at hh
    omega
  let s1 : State := ⟨s.phase, writeBit s.basis L.point.finite (!s.basis L.point.finite)⟩
  have h1 : run [.X L.point.finite] [] s = s1 := rfl
  have hz1 : regValue (L.dialogPool.take 247) s1.basis = 0 := by
    rw [← hz]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfp (e ▸ hq)
    simp [s1, writeBit, this]
  have hh := equalPorts_correct (probeControl L) L.point.finite (probeTail L) (L.dialogPool.take 247) 226156424291633194186662080095093570025917938800079226639565593765455331327
    ((probeTail_length L hw).trans (work_length L hw).symm) nd
    (by rw [probeTail_length L hw]; norm_num) s1 m hz1
  have hm0 : measurementCount [Instr.X L.point.finite] = 0 := rfl
  rw [clrF, run_append, hm0, List.take_zero, List.drop_zero, h1, hh]
  have e1 : s1.basis L.point.finite = !s.basis L.point.finite := by simp [s1, writeBit]
  have e2 : s1.basis (probeControl L) = s.basis (probeControl L) := by simp [s1, writeBit, Ne.symm hfx]
  have e3 : regValue (probeTail L) s1.basis = regValue (probeTail L) s.basis := by
    apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hft (e ▸ hq)
    simp [s1, writeBit, this]
  rw [e1, e2, e3, probe_value_cons L hw]
  congr 1
  funext q
  by_cases hq : q = L.point.finite
  · subst hq
    simp only [s1, writeBit, Function.update_self]
    cases s.basis L.point.finite <;> cases s.basis (probeControl L) <;>
      by_cases ht : regValue (probeTail L) s.basis = 226156424291633194186662080095093570025917938800079226639565593765455331327 <;> simp [ht,sentinelHigh] <;> omega
  · simp [s1, writeBit, Function.update_of_ne hq]

include hw hn in
theorem zrep_run (s : State) (m : List Bool) :
    (run (zrep L) m s).phase = s.phase ∧
    (∀ q, q ∉ L.point.x → (run (zrep L) m s).basis q = s.basis q) ∧
    regValue L.point.x (run (zrep L) m s).basis =
      regValue L.point.x s.basis ^^^ (if s.basis L.point.finite then 0 else sentinel) := by
  have hfx := fin_not_x L hn
  have hnd := finX_nodup L hn
  let s1 : State := ⟨s.phase, writeBit s.basis L.point.finite (!s.basis L.point.finite)⟩
  have h1 : run [.X L.point.finite] [] s = s1 := rfl
  have hm0 : measurementCount [Instr.X L.point.finite] = 0 := rfl
  have hmc := (maskedConstant_counts L.point.finite L.point.x sentinel).2
  have hk : sentinel < 2 ^ L.point.x.length := by
    rw [show L.point.x.length = 256 from hw.inputX]; norm_num [sentinel]
  obtain ⟨tp, tout, tx⟩ := maskedConstant_correct L.point.finite L.point.x sentinel hnd hfx hk s1 []
  obtain ⟨t, ht⟩ : ∃ t : State, t = run (maskedConstant L.point.finite L.point.x sentinel) [] s1 := ⟨_, rfl⟩
  rw [← ht] at tp tout tx
  have hrun : run (zrep L) m s = ⟨t.phase, writeBit t.basis L.point.finite (!t.basis L.point.finite)⟩ := by
    rw [zrep, run_append, run_append, measurementCount_append, hm0, hmc, Nat.add_zero,
      List.take_zero, List.drop_zero, List.take_nil, List.drop_nil, h1, ← ht]
    rfl
  have tf : t.basis L.point.finite = !s.basis L.point.finite := by
    rw [tout _ hfx]; simp [s1, writeBit]
  rw [hrun]
  refine ⟨tp, ?_, ?_⟩
  · intro q hq
    by_cases hqf : q = L.point.finite
    · subst hqf; simp [writeBit, tf]
    · simp only [writeBit, Function.update_of_ne hqf]
      rw [tout q hq]; simp [s1, writeBit, Function.update_of_ne hqf]
  · have e1 : regValue L.point.x (writeBit t.basis L.point.finite (!t.basis L.point.finite)) =
        regValue L.point.x t.basis := by
      apply regValue_congr; intro q hq
      have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
      simp [writeBit, this]
    have e2 : regValue L.point.x s1.basis = regValue L.point.x s.basis := by
      apply regValue_congr; intro q hq
      have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
      simp [s1, writeBit, this]
    show regValue L.point.x (writeBit t.basis L.point.finite (!t.basis L.point.finite)) = _
    rw [e1, tx, e2]
    have : s1.basis L.point.finite = !s.basis L.point.finite := by simp [s1, writeBit]
    rw [this]
    cases s.basis L.point.finite <;> rfl

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))) := by
  intro s m v
  have hz : regValue (L.dialogPool.take 247) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz,probe_value L hw]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite = base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite ∉ L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [← v.x]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit, this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [← v.y]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit, this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit, Ne.symm (fin_ne_generic L hn), v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [← v.clean]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit, this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q = writeBit base L.point.finite _ q
    by_cases hqf : q = L.point.finite
    · subst hqf; simp [writeBit, hfs, v.x]
    · simp [writeBit, hqf, v.rest q hq]

include hw hn in
theorem zrep_step (X X' Y : Fp) (G : Bool) (base : BasisState)
    (hX : X'.val = X.val ^^^ (if base L.point.finite then 0 else sentinel)) :
    Triple (PointDialogValues L X Y G base) (zrep L) (PointDialogValues L X' Y G base) := by
  intro s m v
  obtain ⟨hp, hout, hx⟩ := zrep_run L hw hn s m
  have hf : s.basis L.point.finite = base L.point.finite := v.rest _ (finite_not_x L hn)
  refine ⟨hp, v.withX hn ?_ hout⟩
  rw [hx, v.x, hf, hX]

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalResources =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
theorem ports_length : (zeroPorts (probeTail L) (L.dialogPool.take 247)).length = 247 := by
  have h := (zeroPorts_maps (probeTail L) (L.dialogPool.take 247)
    ((probeTail_length L hw).trans (work_length L hw).symm)).1
  simpa only [List.length_map,probeTail_length L hw] using congrArg List.length h

theorem zrep_counts : toffoliCount (zrep L) = 0 ∧ measurementCount (zrep L) = 0 := by
  have h := maskedConstant_counts L.point.finite L.point.x sentinel
  simp only [zrep,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hw in
theorem clrF_counts : toffoliCount (clrF L) = 247 ∧ measurementCount (clrF L) = 247 := by
  have h := equalConstant_counts (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  simp only [clrF,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hn in
theorem zrep_physical : GatePhysical (zrep L) := by
  simp only [zrep,gatePhysical_append]
  refine ⟨⟨?_,maskedConstant_physical _ _ _ (fin_not_x L hn)⟩,?_⟩
  all_goals intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial

include hw hn in
theorem clrF_physical : GatePhysical (clrF L) := by
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  simp only [clrF,gatePhysical_append]
  refine ⟨?_,equalConstant_physical _ _ _ _ ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial
  · exact (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)

include hw in
theorem old_clrF_support : wires (ECDSAAdd.Entrant.clrF L) =
    (L.point.finite :: (L.point.x ++ L.dialogPool.take 255)).toFinset := by
  have hl := (finTail_length L hw).trans (finWork255_length L hw).symm
  rw [ECDSAAdd.Entrant.clrF,wires_append,equalConstant_wires]
  ext q
  have hp : q ∈ (zeroPorts L.point.x.tail (L.dialogPool.take 255)).flatMap ZeroBit.wires ↔
      q ∈ L.point.x.tail ++ L.dialogPool.take 255 :=
    (zeroPorts_perm L.point.x.tail (L.dialogPool.take 255) hl).mem_iff
  have hx : q ∈ L.point.x ↔ q = x0 L ∨ q ∈ L.point.x.tail := by
    conv_lhs => rw [x_cons L hw]
    simp
  simp only [Finset.mem_union,wires,Instr.wires,Finset.union_empty,Finset.mem_singleton,
    List.mem_toFinset,List.mem_cons] at *
  rw [hp]
  simp only [List.mem_append] at *
  tauto

include hw in
theorem zrep_support_old : wires (zrep L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [old_clrF_support L hw]
  intro q used
  simp only [zrep,wires_append,Finset.mem_union] at used
  rcases used with (h | h) | h
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]
  · have h' := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h' ⊢
    tauto
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]

include hw in
theorem clrF_support_old : wires (clrF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [old_clrF_support L hw]
  intro q used
  simp only [clrF,wires_append,Finset.mem_union] at used
  rcases used with h | h
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]
  · rw [equalConstant_wires] at h
    have h' := List.mem_toFinset.mp h
    rcases List.mem_cons.mp h' with e | h'
    · subst q
      simp [probeControl_mem L hw]
    rcases List.mem_cons.mp h' with e | h'
    · subst q; simp
    have hl := (probeTail_length L hw).trans (work_length L hw).symm
    rcases List.mem_append.mp ((zeroPorts_perm _ _ hl).subset h') with inp | work
    · simp [probeTail_mem L q inp]
    · have included : L.dialogPool.take 247 ⊆ L.dialogPool.take 255 := by
        have h : L.dialogPool.take 247 = (L.dialogPool.take 255).take 247 := by
          rw [List.take_take]; rfl
        rw [h]
        exact List.take_subset _ _
      simp [included work]

include hw in
theorem zrep_slots : gateSlots (zrep L) ≤ 258 := by
  have h := maskedConstant_gateSlots_le L.point.finite L.point.x sentinel
  rw [show L.point.x.length = 256 from hw.inputX] at h
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [zrep,gateSlots_append,one]
  omega

include hw in
def constantSlots : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, k => (if k % 2 = 1 then 1 else 0) + constantSlots n (k/2)

theorem xor_slots_exact (r : List Wire) (k : Nat) :
    gateSlots (xorConstant r k) = constantSlots r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [xorConstant,constantSlots,List.length_cons,gateSlots_append]
    split <;> simp [gateSlots_cons,instructionSlots,ih]

theorem masked_slots_exact (c : Wire) (r : List Wire) (k : Nat) :
    gateSlots (maskedConstant c r k) = constantSlots r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [maskedConstant,constantSlots,List.length_cons,gateSlots_append]
    split <;> simp [gateSlots_cons,instructionSlots,ih]

theorem equal_slots_exact (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    gateSlots (equalConstant c t bs k) = 7*bs.length+1+2*constantSlots bs.length k := by
  simp only [equalConstant,gateSlots_append,zeroControlled_gateSlots,xor_slots_exact,List.length_map]
  omega

include hw in
theorem zrep_slots_exact : gateSlots (zrep L) = 251 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [zrep,gateSlots_append,one,masked_slots_exact,
    show L.point.x.length = 256 from hw.inputX]
  decide +kernel

include hw in
theorem old_zrep_slots_exact : gateSlots (ECDSAAdd.Entrant.zrep L) = 4 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [ECDSAAdd.Entrant.zrep,gateSlots_append,one,masked_slots_exact,
    show L.point.x.length = 256 from hw.inputX]
  decide +kernel

include hw in
theorem clrF_slots_exact : gateSlots (clrF L) = 2225 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [clrF,gateSlots_append,one,equal_slots_exact,ports_length L hw]
  decide +kernel

include hw in
theorem old_clrF_slots_exact : gateSlots (ECDSAAdd.Entrant.clrF L) = 1789 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [ECDSAAdd.Entrant.clrF,gateSlots_append,one,equal_slots_exact,finClr_ports_length L hw]
  decide +kernel

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalPoint =====
section
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

def clearF : Program := [.X L.point.finite] ++ MeasuredZeroClear.equalClear
  (probeControl L) L.point.finite (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (L.dialogPool.take 247) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  let bs := zeroPorts (probeTail L) (L.dialogPool.take 247)
  let s1 := run [Instr.X L.point.finite] [] s
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  have nd : (probeControl L::L.point.finite::bs.flatMap ZeroBit.wires).Nodup :=
    (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)
  have hz1 : ∀b∈bs,s1.basis b.work=false := by
    intro b hb
    have mem : b.work∈L.dialogPool.take 247 := by
      rw [←(zeroPorts_maps _ _ hl).2]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    have ne : b.work≠L.point.finite := fun eq =>
      fin_not_pool L hn (eq ▸ List.mem_of_mem_take mem)
    simpa [s1,run,writeBit,ne] using (regValue_zero _ _).mp hz b.work mem
  have zero : (run (equalConstant (probeControl L) L.point.finite bs 226156424291633194186662080095093570025917938800079226639565593765455331327) m s1).basis
      L.point.finite=false := by
    simpa only [clrF,run_append,show measurementCount [Instr.X L.point.finite]=0 from rfl,
      List.take_zero,List.drop_zero] using hzero
  have eq := MeasuredZeroClear.equal_run_eq _ _ bs 226156424291633194186662080095093570025917938800079226639565593765455331327 nd s1 m hz1 zero
  simpa only [clearF,clrF,run_append,show measurementCount [Instr.X L.point.finite]=0 from rfl,
    List.take_zero,List.drop_zero] using eq

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=decide (probeVal X.val ≠ sentinelHigh)) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))) := by
  intro s m v
  have hz : regValue (L.dialogPool.take 247) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz,probe_value L hw,v.x]
    simp [writeBit,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

theorem clearF_support : wires (clearF L) ⊆ wires (clrF L) := by
  simp only [clearF,clrF,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (MeasuredZeroClear.equal_support _ _ _ _)

include hw in
theorem clearF_counts : toffoliCount (clearF L)=246 ∧ measurementCount (clearF L)=247 := by
  have h := MeasuredZeroClear.equal_counts (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  simp only [clearF,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hw in
theorem clearF_slots : gateSlots (clearF L)=2221 := by
  have ne : zeroPorts (probeTail L) (L.dialogPool.take 247)≠[] := by
    intro h
    have len := ports_length L hw
    rw [h] at len
    contradiction
  have h := MeasuredZeroClear.equal_slots (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327 ne
  have old := clrF_slots_exact L hw
  simp only [clearF,clrF,gateSlots_append] at old ⊢
  omega

include hw hn in
theorem clearF_physical : GatePhysical (clearF L) := by
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  simp only [clearF,gatePhysical_append]
  refine ⟨?_,MeasuredZeroClear.equal_physical _ _ _ _ ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial
  · exact (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)

end ECDSAAdd.Entrant.FiniteFlagInterval
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (probeVal X.val ≠ sentinelHigh) = fin) (h2 : decide (probeVal X'.val ≠ sentinelHigh) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
        L.point.finite ^^ decide (probeVal X'.val ≠ sentinelHigh)) = base := by
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
    have z1 := zrep_step L hw hn 0 (sentinel : Fp) 0 false s.basis (by rw [hfin, sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (sentinel : Fp) 0 (sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (sentinel : Fp) 0 cx cy base' sentinel_ne_zero) hfin
      (by rw [sentinel_val, sentinel_high]; decide) (by rw [sentinel_val, sentinel_high]; decide)
    have z2 := zrep_step L hw hn (sentinel : Fp) 0 0 false s.basis (by rw [hfin, sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (probeVal x.val ≠ sentinelHigh) = true := decide_eq_true (curve_x_high_ne hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide (probeVal (genericX x y cx cy).val ≠ sentinelHigh) = true :=
        decide_eq_true (curve_x_high_ne (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalFinal =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  ReflectionE1TickGapLow48.generic

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) := by
  intro q used
  have hz : q ∈ wires (zrep L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => zrep_support_old L hw h
  have hc : q ∈ wires (clrF L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clrF_support_old L hw h
  have he : q ∈ wires (clearF L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => hc (clearF_support L h)
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,
    generic,wires_append,Finset.mem_union] at used ⊢
  tauto

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy) ⊆ (OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (ReflectionE1TickGapLow48.gen_sites L hw hn cx cy)

theorem gen_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+17 = toffoliCount (ReflectionE1TickGapLow48.gen L cx cy) ∧
    measurementCount (gen L cx cy)+16 = measurementCount (ReflectionE1TickGapLow48.gen L cx cy) ∧
    gateSlots (gen L cx cy) = gateSlots (ReflectionE1TickGapLow48.gen L cx cy)+1362 := by
  have z := zrep_counts L
  have c := clrF_counts L hw
  have e := clearF_counts L hw
  have oz := ECDSAAdd.Entrant.zrep_counts L
  have oc := ECDSAAdd.Entrant.clrF_counts L hw
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,generic,
    toffoliCount_append,measurementCount_append,gateSlots_append,z.1,z.2,c.1,c.2,
    oz.1,oz.2,oc.1,oc.2,e.1,e.2,zrep_slots_exact L hw,clrF_slots_exact L hw,clearF_slots L hw,
    old_zrep_slots_exact L hw,old_clrF_slots_exact L hw]
  omega

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := zrep_physical L hn
  have c := clrF_physical L hw hn
  have e := clearF_physical L hw hn
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

theorem wrapper_support_mono (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : wires P ⊆ wires Q) :
    wires (Edges.wrapper L C cy P) ⊆ wires (Edges.wrapper L C cy Q) := by
  simp only [Edges.wrapper,Edges.finiteProgram,wires_append,renameProgram_support]
  repeat' first
    | exact h
    | exact Finset.Subset.refl _
    | apply Finset.union_subset_union
    | apply Finset.image_subset_image

theorem wrapper_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+17 =
      toffoliCount (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+16 =
      measurementCount (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy)) =
      gateSlots (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy))+1362 := by
  have h := gen_counts L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1588 := by
  have h := wrapper_support_mono layout C cy _ _ (gen_support_subset layout layout_widths cx cy)
  have card := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)
  exact card.trans (ReflectionE1TickGapLow48.wrapper_qubits C cx cy)

theorem wrapper_qubits760 (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1587 := by
  have h := wrapper_support_mono layout C cy _ _ (gen_support_subset layout layout_widths cx cy)
  have card := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)
  exact card.trans (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2151053 := by
  have h := (wrapper_counts layout layout_widths (.some hc) cx cy).1
  have old := ReflectionE1TickGapLow48.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1498867 := by
  have h := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
  have old := ReflectionE1TickGapLow48.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50212561+Rolling1588.slotGrowth := by
  have h := (wrapper_counts layout layout_widths C cx cy).2.2
  have old := ReflectionE1TickGapLow48.wrapper_slots C cx cy
  omega

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151053,1498867,1588,50212561+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2151053 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1498867 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50212561+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1498867
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50212561+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.Main =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.MeasuredDHFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      MeasuredDH.wrapper layout C cy (FiniteFlagInterval.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151090,1498894,1588,50212550+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := FiniteFlagInterval.gen_sites layout layout_widths layout_nodup cx cy
    have support := (MeasuredDH.wrapper_support layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ b R _
      (MeasuredDH.full_spec layout layout_widths layout_nodup R hc b _
        (FiniteFlagInterval.genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151090 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤2151090
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498894 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤1498894
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := MeasuredDH.wrapper_support layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (FiniteFlagInterval.wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact MeasuredDH.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FiniteFlagInterval.gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50212550+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    change gateSlots (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤50212550+Rolling1588.slotGrowth
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498894
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50212550+Rolling1588.slotGrowth
    rw [normalize_slots]; exact program_gateSlots C
end ECDSAAdd.Entrant.MeasuredDHFinal
end
end

-- ===== merged module ECDSAAdd.Submission.Entrant.FusedBoundaryFinal =====
section
namespace ECDSAAdd.Entrant.FusedBoundaryFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (FiniteFlagInterval.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151050,1498865,1587,50236132⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := FiniteFlagInterval.gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (FiniteFlagInterval.gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ b R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc b _
        (FiniteFlagInterval.genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151050 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤2151050
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498865 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤1498865
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1587 := by
  cases C with
  | zero => change qubits []≤1587; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (FiniteFlagInterval.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (FiniteFlagInterval.wrapper_qubits760 (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FiniteFlagInterval.gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50236132 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=23581 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤50236132
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498865
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50236132
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.FusedBoundaryFinal
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineMath =====
section
/-!
A 247-bit affine finite-point probe. The design follows the unintegrated
research direction in Yukon submission a67cb86c-fb4d-4634-98e9-dcb7b60d563a:
bits 1 and 2 agree; bit 5 and the selected high bits are set.
The case split and field proofs below are independently reconstructed.
-/
namespace ECDSAAdd.Entrant.CodexAffineMath
open Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def matchesX (v : Nat) : Prop :=
  v / 2 % 2 = v / 4 % 2 ∧
  v / 32 % 2 = 1 ∧
  v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607

instance : DecidablePred matchesX := fun v =>
  inferInstanceAs (Decidable (v / 2 % 2 = v / 4 % 2 ∧ v / 32 % 2 = 1 ∧
    v / 1024 % 4194304 = 4194303 ∧
    v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607))

def excluded (v : Nat) : Prop :=
  v = 115792089237316195423570985008687907853269984665640564039457584007908834671648 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671649 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671656 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671657 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671662

theorem matches_cases (v : Nat) (hv : v < p) (h : matchesX v) : excluded v := by
  unfold matchesX at h
  unfold excluded
  norm_num [p] at hv
  omega

theorem sentinel_matches : matchesX (p-1) := by
  norm_num [matchesX,p]

private theorem nonresidue_0 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671648 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_1 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671649 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_2 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_3 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_4 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_5 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671657 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_6 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem excluded_nonresidue (v : Nat) (hv : excluded v) :
    ((v : Fp)^3+7)^((p-1)/2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by norm_num [p]
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  have transport (q a : Nat) (hq : q=p)
      (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
      ((a : Fp)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    subst q
    exact h
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transport _ _ hp nonresidue_0
  · exact transport _ _ hp nonresidue_1
  · exact transport _ _ hp nonresidue_2
  · exact transport _ _ hp nonresidue_3
  · exact transport _ _ hp nonresidue_4
  · exact transport _ _ hp nonresidue_5
  · exact transport _ _ hp nonresidue_6

theorem curve_x_not_matches {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ matchesX x.val := by
  intro h
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have power := excluded_nonresidue x.val (matches_cases x.val (ZMod.val_lt x) h)
  rw [ZMod.natCast_zmod_val] at power
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using equation
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [←square,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1=2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,square,power] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

theorem probe_bridge (a b : Bool) (rest v : Nat)
    (h : (if a then 1 else 0)+2*((if b then 1 else 0)+2*rest) =
      v / 2 % 4 + 4*(v / 32 % 2) + 8*(v / 1024 % 4194304) +
      33554432*(v / 8589934592)) :
    (!(b ^^ a) && decide (rest=2^246-1)) = decide (matchesX v) := by
  change (!(b ^^ a) && decide (rest=113078212145816597093331040047546785012958969400039613319782796882727665663)) = decide (matchesX v)
  have low : v / 2 % 4 = v / 2 % 2 + 2*(v / 4 % 2) := by
    have h4 : v / 2 / 2 = v / 4 := by simp [Nat.div_div_eq_div_mul]
    have h8 : v / 2 / 4 = v / 4 / 2 := by simp [Nat.div_div_eq_div_mul]
    omega
  have tail : rest = v / 32 % 2 + 2*(v / 1024 % 4194304) + 8388608*(v / 8589934592) := by
    have hlt := Nat.mod_lt (v / 2) (by decide : 0 < 4)
    cases a <;> cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
  have bits : (if a then 1 else 0) = v / 2 % 2 ∧ (if b then 1 else 0) = v / 4 % 2 := by
    cases a <;> cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
  have tail_iff : rest=113078212145816597093331040047546785012958969400039613319782796882727665663 ↔ v / 32 % 2 = 1 ∧ v / 1024 % 4194304 = 4194303 ∧ v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607 := by
    omega
  cases a <;> cases b <;> simp_all [matchesX] <;> omega

end ECDSAAdd.Entrant.CodexAffineMath
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineGadget =====
section
namespace ECDSAAdd.Entrant.CodexAffineGadget
open Arithmetic RecordedQuantum Challenge Baselines

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def view (a b : Wire) : Program := [.CX a b, .X b]
def restore (a b : Wire) : Program := [.X b, .CX a b]
def core (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ equalConstant b f (zeroPorts r work) k
def program (a b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view a b ++ core b f r work k ++ restore a b
def clearCore (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ MeasuredZeroClear.equalClear b f (zeroPorts r work) k
def clearProgram (a b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view a b ++ clearCore b f r work k ++ restore a b

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append, run_take]

theorem ports_length (r work : List Wire) (hl : r.length = work.length) :
    (zeroPorts r work).length = r.length := by
  have h := congrArg List.length (zeroPorts_maps r work hl).1
  simpa using h

theorem ports_nodup (a b f : Wire) (r work : List Wire)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    (b :: f :: (zeroPorts r work).flatMap ZeroBit.wires).Nodup := by
  exact (((zeroPorts_perm r work hl).cons f).cons b).nodup_iff.mpr
    (List.nodup_cons.mp hn).2

theorem view_run (a b : Wire) (_hab : a ≠ b) (s : State) (m : List Bool) :
    run (view a b) m s =
      ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ s.basis a))⟩ := by
  simp [view, run, writeBit]

theorem restore_update (a b f : Wire) (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
    (s : State) (m : List Bool) (z : Bool) :
    run (restore a b) m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ s.basis a))) f z⟩ =
      ⟨s.phase, writeBit s.basis f z⟩ := by
  simp only [restore, run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = b
  · subst q
    cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp [writeBit, hab, haf, hbf, ha, hb]
  · by_cases hqf : q = f
    · subst q
      simp [writeBit, hab, haf, hbf, hbf.symm]
    · simp [writeBit, hq, hqf, hab, haf, hbf]

theorem program_run (a b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (a :: b :: f :: (r ++ work)).Nodup) (hl : r.length = work.length)
    (hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0) :
    run (program a b f r work k) m s =
      ⟨s.phase, writeBit s.basis f
        (s.basis f ^^ !((!(s.basis b ^^ s.basis a)) && decide (regValue r s.basis = k)))⟩ := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hab : a ≠ b := sep.1.1
  have haf : a ≠ f := sep.1.2.1
  have hbf : b ≠ f := sep.2.1.1
  have hbr : b ∉ r := sep.2.1.2.1
  have hbw : b ∉ work := sep.2.1.2.2
  have hfr : f ∉ r := sep.2.2.1.1
  have hfw : f ∉ work := sep.2.2.1.2
  let u : State := ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ s.basis a))⟩
  let v : State := ⟨s.phase, writeBit u.basis f (!s.basis f)⟩
  have hu : run (view a b) m s = u := view_run a b hab s m
  have uv : run [.X f] m u = v := by simp [run, u, v, writeBit, hbf.symm]
  have hports := zeroPorts_maps r work hl
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← hports.2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    simpa [v, u, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have hr : regValue r v.basis = regValue r s.basis := by
    apply regValue_congr
    intro q hq
    simp [v, u, writeBit, show q ≠ b from fun e => hbr (e ▸ hq),
      show q ≠ f from fun e => hfr (e ▸ hq)]
  have eq := equalConstant_correct b f (zeroPorts r work) k (ports_nodup a b f r work hl hn)
    (by simpa only [ports_length r work hl] using hk) v m clean
  rw [hports.1, hr] at eq
  have vb : v.basis b = !(s.basis b ^^ s.basis a) := by simp [v, u, writeBit, hbf]
  have vf : v.basis f = !s.basis f := by simp [v, writeBit]
  rw [vb, vf] at eq
  have folded : ((!s.basis f) ^^
      (!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k))) =
      (s.basis f ^^ !(!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k))) := by
    cases s.basis f <;> cases (!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k)) <;> rfl
  rw [folded] at eq
  have shape : run (program a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, hu, uv]
  rw [shape, eq]
  simpa only [v, u, writeBit, Function.update_idem] using
    restore_update a b f hab haf hbf s (m.drop (zeroPorts r work).length)
      (s.basis f ^^ !(!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k)))

theorem program_counts (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (program a b f r work k) = r.length ∧
    measurementCount (program a b f r work k) = r.length := by
  simp [program, core, view, restore, toffoliCount_append, measurementCount_append,
    equalConstant_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem clearProgram_counts (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (clearProgram a b f r work k) = r.length - 1 ∧
    measurementCount (clearProgram a b f r work k) = r.length := by
  simp [clearProgram, clearCore, view, restore, toffoliCount_append, measurementCount_append,
    MeasuredZeroClear.equal_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem program_support (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    wires (program a b f r work k) ⊆ (a :: b :: f :: (r ++ work)).toFinset := by
  intro q hq
  have hp : q ∈ (zeroPorts r work).flatMap ZeroBit.wires ↔ q ∈ r ++ work :=
    (zeroPorts_perm r work hl).mem_iff
  simp only [program, core, view, restore, wires_append, equalConstant_wires, wires,
    Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty, or_false, List.mem_toFinset, List.mem_cons, hp] at hq ⊢
  tauto

theorem clearProgram_support (a b f : Wire) (r work : List Wire) (k : Nat) :
    wires (clearProgram a b f r work k) ⊆ wires (program a b f r work k) := by
  simp only [clearProgram, clearCore, program, core, wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (MeasuredZeroClear.equal_support b f (zeroPorts r work) k)))
    (Finset.Subset.refl _)

theorem clearProgram_run_eq (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup)
    (s : State) (m : List Bool) (hz : regValue work s.basis = 0)
    (hzero : (run (program a b f r work k) m s).basis f = false) :
    run (clearProgram a b f r work k) m s = run (program a b f r work k) m s := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have haf : a ≠ f := sep.1.2.1
  have hbf : b ≠ f := sep.2.1.1
  have haw : a ∉ work := sep.1.2.2.2
  have hbw : b ∉ work := sep.2.1.2.2
  have hfw : f ∉ work := sep.2.2.1.2
  let v := run [Instr.X f] m (run (view a b) m s)
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← (zeroPorts_maps r work hl).2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have nea : p.work ≠ a := fun e => haw (e ▸ mem)
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    have away : p.work ∉ wires (view a b) := by simp [view, wires, Instr.wires, nea, neb]
    change (run [Instr.X f] m (run (view a b) m s)).basis p.work = false
    rw [run_preserves_outside _ _ _ _ (by simp [wires, Instr.wires, nef]),
      run_preserves_outside _ _ _ _ away]
    exact (regValue_zero work s.basis).mp hz p.work mem
  have oldShape : run (program a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have newShape : run (clearProgram a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) m v) := by
    simp only [clearProgram, clearCore, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (MeasuredZeroClear.equal_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have away : f ∉ wires (restore a b) := by
    simp [restore, wires, Instr.wires, haf.symm, hbf.symm]
  have keep := run_preserves_outside (restore a b) (m.drop (zeroPorts r work).length)
    (run (equalConstant b f (zeroPorts r work) k) m v) f away
  have zero : (run (equalConstant b f (zeroPorts r work) k) m v).basis f = false := by
    rw [oldShape] at hzero
    exact keep.symm.trans hzero
  have eq := MeasuredZeroClear.equal_run_eq b f (zeroPorts r work) k
    (ports_nodup a b f r work hl hn) v m clean zero
  rw [oldShape, newShape, eq]

theorem clearProgram_eq (a b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (a :: b :: f :: (r ++ work)).Nodup) (hl : r.length = work.length)
    (_hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0)
    (hzero : (run (program a b f r work k) m s).basis f = false) :
    run (clearProgram a b f r work k) m s = run (program a b f r work k) m s :=
  clearProgram_run_eq a b f r work k hl hn s m hz hzero

theorem program_physical (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    GatePhysical (program a b f r work k) := by
  have hab : a ≠ b := by
    intro e
    exact (List.nodup_cons.mp hn).1 (by simp [e])
  have hv : GatePhysical (view a b) := by simp [view, GatePhysical, PhysicalInstr, ProperGate, hab]
  have hr : GatePhysical (restore a b) := by simp [restore, GatePhysical, PhysicalInstr, ProperGate, hab]
  simp only [program, core, gatePhysical_append]
  exact ⟨⟨hv, ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
    equalConstant_physical b f (zeroPorts r work) k (ports_nodup a b f r work hl hn)⟩⟩, hr⟩

theorem clearProgram_physical (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    GatePhysical (clearProgram a b f r work k) := by
  have old := program_physical a b f r work k hl hn
  simp only [program, core, gatePhysical_append] at old
  simp only [clearProgram, clearCore, gatePhysical_append]
  exact ⟨⟨old.1.1, ⟨old.1.2.1,
    MeasuredZeroClear.equal_physical b f (zeroPorts r work) k
      (ports_nodup a b f r work hl hn)⟩⟩, old.2⟩

theorem program_slots (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (program a b f r work k) ≤ 9 * r.length + 6 := by
  have h := equalConstant_gateSlots_le b f (zeroPorts r work) k
  rw [ports_length r work hl] at h
  simp only [program, core, view, restore, gateSlots_append] at *
  change 2 + (1 + gateSlots (equalConstant b f (zeroPorts r work) k)) + 2 ≤ _
  omega

theorem clearProgram_slots_le (a b f : Wire) (r work : List Wire) (k : Nat) :
    gateSlots (clearProgram a b f r work k) ≤ gateSlots (program a b f r work k) := by
  have h : gateSlots (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) ≤
      gateSlots (equalConstant b f (zeroPorts r work) k) := by
    by_cases he : zeroPorts r work = []
    · rw [he]
      exact Nat.le_refl _
    · have h := MeasuredZeroClear.equal_slots b f (zeroPorts r work) k he
      omega
  simp only [clearProgram, clearCore, program, core, gateSlots_append]
  omega

theorem clearProgram_slots (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (clearProgram a b f r work k) ≤ 9 * r.length + 6 :=
  (clearProgram_slots_le a b f r work k).trans (program_slots a b f r work k hl)

end ECDSAAdd.Entrant.CodexAffineGadget
end

-- ===== combined module ECDSAAdd.Submission.Entrant.CodexAffineProbe =====
section
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

attribute [local irreducible] toffoliCount measurementCount gateSlots ReflectionE1TickGapLow48.generic

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
def bounds : Challenge.Bounds := ⟨2151048,1498863,1587,50236132⟩

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

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151048 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤2151048
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498863 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤1498863
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

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50236132 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.2
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=23581 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤50236132
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498863
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50236132
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.CodexAffineProbe
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityMath =====
section
namespace ECDSAAdd.Entrant.CodexYParityMath
open Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def highX (v : Nat) : Prop :=
  v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607

instance : DecidablePred highX := fun v => inferInstanceAs (Decidable
  (v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607))

def yParity (v : Nat) : Bool :=
  decide (v / 6901746346790563787434755862277025452451108972170386555162524223799296 % 2 = 1) ^^
  decide (v / 441711766194596082395824375185729628956870974218904739530401550323154944 % 2 = 1) ^^
  decide (v / 883423532389192164791648750371459257913741948437809479060803100646309888 % 2 = 1) ^^
  decide (v / 1766847064778384329583297500742918515827483896875618958121606201292619776 % 2 = 1) ^^
  decide (v / 113078212145816597093331040047546785012958969400039613319782796882727665664 % 2 = 1) ^^
  decide (v / 226156424291633194186662080095093570025917938800079226639565593765455331328 % 2 = 1) ^^
  decide (v / 452312848583266388373324160190187140051835877600158453279131187530910662656 % 2 = 1) ^^
  decide (v / 3618502788666131106986593281521497120414687020801267626233049500247285301248 % 2 = 1)

def matchesXY (x y : Nat) : Prop := highX x ∧ yParity y = false
instance (x y : Nat) : Decidable (matchesXY x y) := inferInstanceAs (Decidable (highX x ∧ yParity y = false))

theorem highX_range (v : Nat) (hv : v < p) (h : highX v) : p-47 ≤ v := by
  unfold highX at h
  norm_num [p] at hv ⊢
  omega

theorem sentinel_matches : matchesXY (p-1) 0 := by
  norm_num [matchesXY,highX,yParity,p]

private theorem nonsquare {a y : Fp} (power : a^((p-1)/2) = -1) (hs : y^2 = a) : False := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [←hs,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1=2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,hs,power] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

private theorem powerTransport (q a : Nat) (hq : q=p)
    (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
    ((a : Fp)^3+7)^((p-1)/2) = -1 := by
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  subst q
  exact h

private theorem squareTransport (q a r : Nat) (hq : q=p)
    (h : (r : ZMod q)^2 = (a : ZMod q)^3+7) :
    (r : Fp)^2 = (a : Fp)^3+7 := by
  subst q
  exact h

private theorem case_1 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671662 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_2 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671661 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671661 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_3 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671660 : Fp)^3+7) : yParity y.val = true := by
  have hr : (6603225675942137755722016048183769717410321709583529039474051610042430502525 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671660 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_4 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671659 : Fp)^3+7) : yParity y.val = true := by
  have hr : (59494462493979449647570233702496999513658646306271329894531992659739671393069 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671659 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_5 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671658 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671658 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_6 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671657 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671657 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_7 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671656 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_8 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671655 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_9 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671654 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_10 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671653 : Fp)^3+7) : yParity y.val = true := by
  have hr : (32675455276886538377135961527970747392999635122131544003589039477106874644692 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671653 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_11 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671652 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671652 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_12 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671651 : Fp)^3+7) : yParity y.val = true := by
  have hr : (26128689524504706065261118141317656197887299188579002162273527811606361449708 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671651 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_13 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671650 : Fp)^3+7) : yParity y.val = true := by
  have hr : (8577303908373580249506288492821825305199069524882698424576740044335877264616 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671650 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_14 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671649 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671649 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_15 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671648 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671648 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_16 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671647 : Fp)^3+7) : yParity y.val = true := by
  have hr : (91140719503136456702788776376224035068647810528229755089092598492509977513391 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671647 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_17 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671646 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671646 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_18 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671645 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671645 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_19 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671644 : Fp)^3+7) : yParity y.val = true := by
  have hr : (39884473096376270427702265980090836962804851088800575884979558070656540211742 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671644 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_20 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671643 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671643 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_21 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671642 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671642 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_22 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671641 : Fp)^3+7) : yParity y.val = true := by
  have hr : (87858050732041572112946130011090019437744585579749573053061107584625869568789 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671641 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_23 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671640 : Fp)^3+7) : yParity y.val = true := by
  have hr : (108804142492889174614636371636043929694359971927800610566698906308390880838775 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671640 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_24 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671639 : Fp)^3+7) : yParity y.val = true := by
  have hr : (90251269264737004142706139481528124213741093942080018241141466145201744297488 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671639 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_25 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671638 : Fp)^3+7) : yParity y.val = true := by
  have hr : (75235462138975110463823503735425296584550141080759035749156047496719874561987 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671638 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_26 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671637 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671637 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_27 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671636 : Fp)^3+7) : yParity y.val = true := by
  have hr : (86939888355575964094991750730646468908583063016749246259798665632714130501197 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671636 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_28 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671635 : Fp)^3+7) : yParity y.val = true := by
  have hr : (4182962361524284598535907236655905568231458553838165214763798974835028006434 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671635 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_29 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671634 : Fp)^3+7) : yParity y.val = true := by
  have hr : (68955841494607169053734295970461238553869482894404290786540257300019047034624 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671634 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_30 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671633 : Fp)^3+7) : yParity y.val = true := by
  have hr : (49733659202714845321509626322873875871991168724474382738121548382114922697663 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671633 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_31 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671632 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671632 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_32 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671631 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671631 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_33 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671630 : Fp)^3+7) : yParity y.val = true := by
  have hr : (44691740129539857302436916955866976963397033623780589459590642317128159632006 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671630 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_34 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671629 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671629 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_35 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671628 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671628 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_36 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671627 : Fp)^3+7) : yParity y.val = true := by
  have hr : (51193769181865963694859153139841532078256707687335846879742476169529437790917 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671627 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_37 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671626 : Fp)^3+7) : yParity y.val = true := by
  have hr : (103618749943476312868418606276677894873806957446321936724134933650386344711784 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671626 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_38 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671625 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671625 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_39 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671624 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671624 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_40 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671623 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671623 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_41 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671622 : Fp)^3+7) : yParity y.val = true := by
  have hr : (66850597368902350158169512472851730375964505860741535628662529042753517520652 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671622 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_42 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671621 : Fp)^3+7) : yParity y.val = true := by
  have hr : (70401031564568261752508033145049036971610607287643400116337276464925705083252 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671621 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_43 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671620 : Fp)^3+7) : yParity y.val = true := by
  have hr : (16630661555480012533216961328463789703838228518257063889232934184924812474445 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671620 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_44 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671619 : Fp)^3+7) : yParity y.val = true := by
  have hr : (107334166703719341558589207297916674948985469142494621554787815725265730778893 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671619 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

private theorem case_45 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671618 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671618 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_46 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671617 : Fp)^3+7) : yParity y.val = true := by
  have power : ((115792089237316195423570985008687907853269984665640564039457584007908834671617 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    reduce_mod_char
  have power2 := powerTransport _ _ (by norm_num [p]) power
  exact False.elim (nonsquare power2 hy)

private theorem case_47 (y : Fp) (hy : y^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671616 : Fp)^3+7) : yParity y.val = true := by
  have hr : (112234481090334865465835242450756667684869773413855542198653146390767513213554 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^2 = (115792089237316195423570985008687907853269984665640564039457584007908834671616 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7 := by
    reduce_mod_char
  have hr2 := squareTransport _ _ _ (by norm_num [p]) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hr2.symm) with rfl | rfl <;> decide

theorem highX_curve_parity {x y : Fp} (hc : curve.toAffine.Nonsingular x y)
    (hx : highX x.val) : yParity y.val = true := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have hv := ZMod.val_lt x
  have lo := highX_range x.val hv hx
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using equation
  have xv : (x.val : Fp) = x := ZMod.natCast_zmod_val x
  rw [←xv] at square
  have hcases : x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671662 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671661 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671660 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671659 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671658 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671657 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671656 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671653 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671652 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671651 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671650 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671649 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671648 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671647 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671646 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671645 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671644 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671643 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671642 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671641 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671640 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671639 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671638 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671637 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671636 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671635 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671634 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671633 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671632 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671631 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671630 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671629 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671628 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671627 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671626 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671625 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671624 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671623 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671622 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671621 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671620 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671619 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671618 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671617 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671616 := by
    norm_num [p] at lo hv
    omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47
  · rw [h1] at square; exact case_1 y square
  · rw [h2] at square; exact case_2 y square
  · rw [h3] at square; exact case_3 y square
  · rw [h4] at square; exact case_4 y square
  · rw [h5] at square; exact case_5 y square
  · rw [h6] at square; exact case_6 y square
  · rw [h7] at square; exact case_7 y square
  · rw [h8] at square; exact case_8 y square
  · rw [h9] at square; exact case_9 y square
  · rw [h10] at square; exact case_10 y square
  · rw [h11] at square; exact case_11 y square
  · rw [h12] at square; exact case_12 y square
  · rw [h13] at square; exact case_13 y square
  · rw [h14] at square; exact case_14 y square
  · rw [h15] at square; exact case_15 y square
  · rw [h16] at square; exact case_16 y square
  · rw [h17] at square; exact case_17 y square
  · rw [h18] at square; exact case_18 y square
  · rw [h19] at square; exact case_19 y square
  · rw [h20] at square; exact case_20 y square
  · rw [h21] at square; exact case_21 y square
  · rw [h22] at square; exact case_22 y square
  · rw [h23] at square; exact case_23 y square
  · rw [h24] at square; exact case_24 y square
  · rw [h25] at square; exact case_25 y square
  · rw [h26] at square; exact case_26 y square
  · rw [h27] at square; exact case_27 y square
  · rw [h28] at square; exact case_28 y square
  · rw [h29] at square; exact case_29 y square
  · rw [h30] at square; exact case_30 y square
  · rw [h31] at square; exact case_31 y square
  · rw [h32] at square; exact case_32 y square
  · rw [h33] at square; exact case_33 y square
  · rw [h34] at square; exact case_34 y square
  · rw [h35] at square; exact case_35 y square
  · rw [h36] at square; exact case_36 y square
  · rw [h37] at square; exact case_37 y square
  · rw [h38] at square; exact case_38 y square
  · rw [h39] at square; exact case_39 y square
  · rw [h40] at square; exact case_40 y square
  · rw [h41] at square; exact case_41 y square
  · rw [h42] at square; exact case_42 y square
  · rw [h43] at square; exact case_43 y square
  · rw [h44] at square; exact case_44 y square
  · rw [h45] at square; exact case_45 y square
  · rw [h46] at square; exact case_46 y square
  · rw [h47] at square; exact case_47 y square

theorem curve_not_matches {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ matchesXY x.val y.val := by
  rintro ⟨hx,hy⟩
  have yes := highX_curve_parity hc hx
  rw [yes] at hy
  contradiction

end ECDSAAdd.Entrant.CodexYParityMath
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityGadget =====
section
/-
Research helper: generic affine parity view for the 246-condition finite probe.
Standalone real-source compilation passed; full integrated certificate remains pending.
Import is for a minimal helper tree containing the official-validated MeasuredZeroClear module;
when integrated into the consolidated Main, omit this import and retain the namespace.
-/

namespace ECDSAAdd.Entrant.CodexYParityGadget
open Arithmetic RecordedQuantum Challenge Baselines

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def parity (xs : List Wire) (s : BasisState) : Bool :=
  xs.foldr (fun x t => s x ^^ t) false

def fan (xs : List Wire) (b : Wire) : Program := xs.map (fun x => .CX x b)
def view (xs : List Wire) (b : Wire) : Program := fan xs b ++ [.X b]
def restore (xs : List Wire) (b : Wire) : Program := [.X b] ++ fan xs.reverse b
def core (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ equalConstant b f (zeroPorts r work) k
def program (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view xs b ++ core b f r work k ++ restore xs b
def clearCore (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ MeasuredZeroClear.equalClear b f (zeroPorts r work) k
def clearProgram (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view xs b ++ clearCore b f r work k ++ restore xs b

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append, run_take]

theorem ports_length (r work : List Wire) (hl : r.length = work.length) :
    (zeroPorts r work).length = r.length := by
  have h := congrArg List.length (zeroPorts_maps r work hl).1
  simpa using h

theorem parity_congr (xs : List Wire) (s t : BasisState)
    (h : ∀ q ∈ xs, s q = t q) : parity xs s = parity xs t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (s x ^^ parity xs s) = (t x ^^ parity xs t)
    rw [h x (by simp), ih (fun q hq => h q (by simp [hq]))]

theorem parity_append (xs ys : List Wire) (s : BasisState) :
    parity (xs ++ ys) s = (parity xs s ^^ parity ys s) := by
  induction xs with
  | nil => simp [parity]
  | cons x xs ih =>
    change (s x ^^ parity (xs ++ ys) s) = ((s x ^^ parity xs s) ^^ parity ys s)
    rw [ih, Bool.xor_assoc]

theorem parity_reverse (xs : List Wire) (s : BasisState) :
    parity xs.reverse s = parity xs s := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, parity_append, ih]
    change (parity xs s ^^ parity [x] s) = (s x ^^ parity xs s)
    simp [parity, Bool.xor_comm]

theorem fan_counts (xs : List Wire) (b : Wire) :
    toffoliCount (fan xs b) = 0 ∧ measurementCount (fan xs b) = 0 := by
  induction xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih => simpa only [fan, List.map_cons, toffoliCount, measurementCount] using ih

theorem fan_slots (xs : List Wire) (b : Wire) : gateSlots (fan xs b) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa [fan, gateSlots, instructionSlots, Nat.add_comm] using congrArg Nat.succ ih

theorem fan_support (xs : List Wire) (b : Wire) :
    wires (fan xs b) ⊆ (b :: xs).toFinset := by
  induction xs with
  | nil => simp [fan, wires]
  | cons x xs ih =>
    intro q hq
    simp only [fan, List.map_cons, wires, Instr.wires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with (rfl | rfl) | hq
    · simp
    · simp
    · have h := ih hq
      simp only [List.mem_toFinset, List.mem_cons] at h ⊢
      tauto

theorem fan_physical (xs : List Wire) (b : Wire) (hb : b ∉ xs) :
    GatePhysical (fan xs b) := by
  intro i hi
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
  have hqb : q ≠ b := fun e => hb (e ▸ hq)
  simpa [PhysicalInstr, ProperGate] using hqb

-- This induction is the same affine fan semantics already used in TerminalGraph.
theorem fan_run (xs : List Wire) (b : Wire) (hb : b ∉ xs)
    (s : State) (m : List Bool) :
    run (fan xs b) m s =
      ⟨s.phase, writeBit s.basis b (s.basis b ^^ parity xs s.basis)⟩ := by
  induction xs generalizing s with
  | nil =>
    simp only [fan, List.map_nil, run, parity, List.foldr_nil, Bool.xor_false]
    cases s with
    | mk phase basis =>
      apply congrArg (State.mk phase)
      funext q
      by_cases hq : q = b <;> simp [writeBit, hq]
  | cons x xs ih =>
    have tail : b ∉ xs := fun h => hb (by simp [h])
    let t : State := ⟨s.phase, writeBit s.basis b (s.basis b ^^ s.basis x)⟩
    have same : parity xs t.basis = parity xs s.basis := parity_congr _ _ _ (by
      intro q hq
      have hqb : q ≠ b := fun e => tail (e ▸ hq)
      simp [t, writeBit, hqb])
    simp only [fan, List.map_cons, run]
    change run (fan xs b) m t = _
    rw [ih tail t, same]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q = b
    · subst q
      simp [t, writeBit, parity, Bool.xor_assoc]
    · simp [t, writeBit, hq]

theorem view_counts (xs : List Wire) (b : Wire) :
    toffoliCount (view xs b) = 0 ∧ measurementCount (view xs b) = 0 := by
  simp [view, toffoliCount_append, measurementCount_append, fan_counts,
    toffoliCount, measurementCount]

theorem restore_counts (xs : List Wire) (b : Wire) :
    toffoliCount (restore xs b) = 0 ∧ measurementCount (restore xs b) = 0 := by
  simp [restore, toffoliCount_append, measurementCount_append, fan_counts,
    toffoliCount, measurementCount]

theorem view_support (xs : List Wire) (b : Wire) :
    wires (view xs b) ⊆ (b :: xs).toFinset := by
  intro q hq
  simp only [view, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact fan_support xs b hq
  · have hqb : q = b := by simpa [wires, Instr.wires] using hq
    simp [hqb]

theorem restore_support (xs : List Wire) (b : Wire) :
    wires (restore xs b) ⊆ (b :: xs).toFinset := by
  intro q hq
  simp only [restore, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · have hqb : q = b := by simpa [wires, Instr.wires] using hq
    simp [hqb]
  · simpa only [List.mem_toFinset, List.mem_cons, List.mem_reverse] using
      fan_support xs.reverse b hq

theorem ports_nodup (xs : List Wire) (b f : Wire) (r work : List Wire)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    (b :: f :: (zeroPorts r work).flatMap ZeroBit.wires).Nodup := by
  have keep : (b :: f :: (r ++ work)).Nodup := by
    exact List.Nodup.sublist
      (List.Sublist.cons₂ b (List.Sublist.cons₂ f (List.sublist_append_right xs (r ++ work)))) hn
  exact (((zeroPorts_perm r work hl).cons f).cons b).nodup_iff.mpr keep

theorem view_run (xs : List Wire) (b : Wire) (hb : b ∉ xs)
    (s : State) (m : List Bool) :
    run (view xs b) m s =
      ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))⟩ := by
  rw [view, run_concat, (fan_counts xs b).2, List.drop_zero, fan_run xs b hb]
  simp [run, writeBit]

theorem restore_update (xs : List Wire) (b f : Wire)
    (hb : b ∉ xs) (hf : f ∉ xs) (hbf : b ≠ f)
    (s : State) (m : List Bool) (z : Bool) :
    run (restore xs b) m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z⟩ =
      ⟨s.phase, writeBit s.basis f z⟩ := by
  let t : State := ⟨s.phase, writeBit
    (writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z)
    b (s.basis b ^^ parity xs s.basis)⟩
  have first : run [Instr.X b] m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))) f z⟩ = t := by
    simp [run, t, writeBit, hbf]
  have same : parity xs t.basis = parity xs s.basis := parity_congr _ _ _ (by
    intro q hq
    simp [t, writeBit, show q ≠ b from fun e => hb (e ▸ hq),
      show q ≠ f from fun e => hf (e ▸ hq)])
  rw [restore, run_concat, show measurementCount [Instr.X b] = 0 from rfl,
    List.drop_zero, first, fan_run xs.reverse b (by simpa using hb), parity_reverse, same]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = b
  · subst q
    cases hp : parity xs s.basis <;> cases hs : s.basis b <;>
      simp [t, writeBit, hbf, hp, hs]
  · by_cases hqf : q = f
    · subst q
      simp [t, writeBit, hbf.symm]
    · simp [t, writeBit, hq, hqf]

theorem program_run (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) (hl : r.length = work.length)
    (hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0) :
    run (program xs b f r work k) m s =
      ⟨s.phase, writeBit s.basis f
        (s.basis f ^^ !((!(s.basis b ^^ parity xs s.basis)) && decide (regValue r s.basis = k)))⟩ := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hbf : b ≠ f := sep.1.1
  have hbx : b ∉ xs := sep.1.2.1
  have hbr : b ∉ r := sep.1.2.2.1
  have hbw : b ∉ work := sep.1.2.2.2
  have hfx : f ∉ xs := sep.2.1.1
  have hfr : f ∉ r := sep.2.1.2.1
  have hfw : f ∉ work := sep.2.1.2.2
  let u : State := ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ parity xs s.basis))⟩
  let v : State := ⟨s.phase, writeBit u.basis f (!s.basis f)⟩
  have hu : run (view xs b) m s = u := view_run xs b hbx s m
  have uv : run [.X f] m u = v := by simp [run, u, v, writeBit, hbf.symm]
  have hports := zeroPorts_maps r work hl
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← hports.2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    simpa [v, u, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have hr : regValue r v.basis = regValue r s.basis := by
    apply regValue_congr
    intro q hq
    simp [v, u, writeBit, show q ≠ b from fun e => hbr (e ▸ hq),
      show q ≠ f from fun e => hfr (e ▸ hq)]
  have eq := equalConstant_correct b f (zeroPorts r work) k (ports_nodup xs b f r work hl hn)
    (by simpa only [ports_length r work hl] using hk) v m clean
  rw [hports.1, hr] at eq
  have vb : v.basis b = !(s.basis b ^^ parity xs s.basis) := by simp [v, u, writeBit, hbf]
  have vf : v.basis f = !s.basis f := by simp [v, writeBit]
  rw [vb, vf] at eq
  have folded : ((!s.basis f) ^^
      (!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k))) =
      (s.basis f ^^ !(!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k))) := by
    cases s.basis f <;> cases (!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k)) <;> rfl
  rw [folded] at eq
  have shape : run (program xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, hu, uv]
  rw [shape, eq]
  simpa only [v, u, writeBit, Function.update_idem] using
    restore_update xs b f hbx hfx hbf s (m.drop (zeroPorts r work).length)
      (s.basis f ^^ !(!(s.basis b ^^ parity xs s.basis) && decide (regValue r s.basis = k)))

theorem program_counts (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (program xs b f r work k) = r.length ∧
    measurementCount (program xs b f r work k) = r.length := by
  simp [program, core, toffoliCount_append, measurementCount_append,
    (view_counts xs b).1, (view_counts xs b).2,
    (restore_counts xs b).1, (restore_counts xs b).2,
    equalConstant_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem clearProgram_counts (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (clearProgram xs b f r work k) = r.length - 1 ∧
    measurementCount (clearProgram xs b f r work k) = r.length := by
  simp [clearProgram, clearCore, toffoliCount_append, measurementCount_append,
    (view_counts xs b).1, (view_counts xs b).2,
    (restore_counts xs b).1, (restore_counts xs b).2,
    MeasuredZeroClear.equal_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem program_support (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    wires (program xs b f r work k) ⊆ (b :: f :: (xs ++ (r ++ work))).toFinset := by
  have hsmall (q : Wire) (hq : q ∈ (b :: xs).toFinset) :
      q ∈ (b :: f :: (xs ++ (r ++ work))).toFinset := by
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq ⊢
    tauto
  intro q hq
  simp only [program, core, wires_append, Finset.mem_union] at hq
  rcases hq with (hq | (hq | hq)) | hq
  · exact hsmall q (view_support xs b hq)
  · have hfq : q = f := by simpa [wires, Instr.wires] using hq
    simp [hfq]
  · have hp : q ∈ (zeroPorts r work).flatMap ZeroBit.wires ↔ q ∈ r ++ work :=
      (zeroPorts_perm r work hl).mem_iff
    simp only [equalConstant_wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, List.mem_toFinset, List.mem_cons, List.mem_append, hp] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  · exact hsmall q (restore_support xs b hq)

theorem clearProgram_support (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) :
    wires (clearProgram xs b f r work k) ⊆ wires (program xs b f r work k) := by
  simp only [clearProgram, clearCore, program, core, wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (MeasuredZeroClear.equal_support b f (zeroPorts r work) k)))
    (Finset.Subset.refl _)

theorem clearProgram_run_eq (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup)
    (s : State) (m : List Bool) (hz : regValue work s.basis = 0)
    (hzero : (run (program xs b f r work k) m s).basis f = false) :
    run (clearProgram xs b f r work k) m s = run (program xs b f r work k) m s := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hbf : b ≠ f := sep.1.1
  have hbx : b ∉ xs := sep.1.2.1
  have hbw : b ∉ work := sep.1.2.2.2
  have hfx : f ∉ xs := sep.2.1.1
  have hfw : f ∉ work := sep.2.1.2.2
  let v := run [Instr.X f] m (run (view xs b) m s)
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← (zeroPorts_maps r work hl).2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    change (run [Instr.X f] m (run (view xs b) m s)).basis p.work = false
    rw [view_run xs b hbx]
    simpa [run, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have oldShape : run (program xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have newShape : run (clearProgram xs b f r work k) m s =
      run (restore xs b) (m.drop (zeroPorts r work).length)
        (run (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) m v) := by
    simp only [clearProgram, clearCore, run_concat, measurementCount_append,
      (view_counts xs b).2,
      show measurementCount [Instr.X f] = 0 from rfl,
      (MeasuredZeroClear.equal_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have away : f ∉ wires (restore xs b) := by
    intro hf
    have h := restore_support xs b hf
    simp only [List.mem_toFinset, List.mem_cons] at h
    exact h.elim (fun e => hbf e.symm) hfx
  have keep := run_preserves_outside (restore xs b) (m.drop (zeroPorts r work).length)
    (run (equalConstant b f (zeroPorts r work) k) m v) f away
  have zero : (run (equalConstant b f (zeroPorts r work) k) m v).basis f = false := by
    rw [oldShape] at hzero
    exact keep.symm.trans hzero
  have eq := MeasuredZeroClear.equal_run_eq b f (zeroPorts r work) k
    (ports_nodup xs b f r work hl hn) v m clean zero
  rw [oldShape, newShape, eq]

theorem clearProgram_eq (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) (hl : r.length = work.length)
    (_hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0)
    (hzero : (run (program xs b f r work k) m s).basis f = false) :
    run (clearProgram xs b f r work k) m s = run (program xs b f r work k) m s :=
  clearProgram_run_eq xs b f r work k hl hn s m hz hzero

theorem program_physical (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    GatePhysical (program xs b f r work k) := by
  have hbx : b ∉ xs := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  have hv : GatePhysical (view xs b) := by
    rw [view, gatePhysical_append]
    exact ⟨fan_physical xs b hbx, by simp [GatePhysical, PhysicalInstr, ProperGate]⟩
  have hr : GatePhysical (restore xs b) := by
    rw [restore, gatePhysical_append]
    exact ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
      fan_physical xs.reverse b (by simpa using hbx)⟩
  simp only [program, core, gatePhysical_append]
  exact ⟨⟨hv, ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
    equalConstant_physical b f (zeroPorts r work) k (ports_nodup xs b f r work hl hn)⟩⟩, hr⟩

theorem clearProgram_physical (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (b :: f :: (xs ++ (r ++ work))).Nodup) :
    GatePhysical (clearProgram xs b f r work k) := by
  have old := program_physical xs b f r work k hl hn
  simp only [program, core, gatePhysical_append] at old
  simp only [clearProgram, clearCore, gatePhysical_append]
  exact ⟨⟨old.1.1, ⟨old.1.2.1,
    MeasuredZeroClear.equal_physical b f (zeroPorts r work) k
      (ports_nodup xs b f r work hl hn)⟩⟩, old.2⟩

theorem program_slots (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (program xs b f r work k) ≤ 9 * r.length + 2 * xs.length + 4 := by
  have h := equalConstant_gateSlots_le b f (zeroPorts r work) k
  rw [ports_length r work hl] at h
  simp only [program, core, view, restore, gateSlots_append, fan_slots, List.length_reverse]
  change (xs.length + 1) + (1 + gateSlots (equalConstant b f (zeroPorts r work) k)) +
    (1 + xs.length) ≤ _
  omega

theorem clearProgram_slots_le (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat) :
    gateSlots (clearProgram xs b f r work k) ≤ gateSlots (program xs b f r work k) := by
  have h : gateSlots (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) ≤
      gateSlots (equalConstant b f (zeroPorts r work) k) := by
    by_cases he : zeroPorts r work = []
    · rw [he]
      exact Nat.le_refl _
    · have h := MeasuredZeroClear.equal_slots b f (zeroPorts r work) k he
      omega
  simp only [clearProgram, clearCore, program, core, gateSlots_append]
  omega

theorem clearProgram_slots (xs : List Wire) (b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (clearProgram xs b f r work k) ≤ 9 * r.length + 2 * xs.length + 4 :=
  (clearProgram_slots_le xs b f r work k).trans (program_slots xs b f r work k hl)

end ECDSAAdd.Entrant.CodexYParityGadget
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityBridge =====
section
namespace ECDSAAdd.Entrant.CodexYParityProbe
open Arithmetic ControlledPointLayout
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

def b (L : ControlledPointLayout) : Wire := L.point.y.getD 232 0
def xs (L : ControlledPointLayout) : List Wire :=
  [238,239,240,246,247,248,251].map (fun i => L.point.y.getD i 0)
def rest (L : ControlledPointLayout) : List Wire :=
  (L.point.x.drop 10).take 22 ++ L.point.x.drop 33
def work (L : ControlledPointLayout) : List Wire := L.dialogPool.take 245
def literal : Nat := 2^245-1

private theorem drop_sublist_drop (r : List Wire) (a b : Nat) (hab : a ≤ b) :
    (r.drop b).Sublist (r.drop a) := by
  have e : r.drop b = (r.drop a).drop (b-a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e]
  exact List.drop_sublist _ _

private theorem getD_range (r : List Wire) (n : Nat) (hn : r.length=n) :
    (List.range n).map (fun i => r.getD i 0)=r := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem _ _ hj

theorem rest_sublist (L : ControlledPointLayout) : (rest L).Sublist L.point.x := by
  have h : (L.point.x.drop 33).Sublist ((L.point.x.drop 10).drop 22) := by
    rw [List.drop_drop]
    exact drop_sublist_drop _ _ _ (by omega)
  have h' := List.Sublist.append (List.Sublist.refl ((L.point.x.drop 10).take 22)) h
  rw [List.take_append_drop] at h'
  exact h'.trans (List.drop_sublist _ _)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
private theorem point_x_length : L.point.x.length=256 := hw.inputX
include hw in
private theorem point_y_length : L.point.y.length=256 := hw.inputY

include hw in
theorem y_sublist : (b L :: xs L).Sublist L.point.y := by
  have h : ([232,238,239,240,246,247,248,251] : List Nat).Sublist (List.range 256) := by decide
  have hm := h.map (fun i => L.point.y.getD i 0)
  rw [getD_range L.point.y 256 (point_y_length L hw)] at hm
  simpa only [b,xs,List.map_cons] using hm

include hw in
theorem lengths : (rest L).length=245 ∧ (work L).length=245 := by
  simp [rest,work,point_x_length L hw,L.dialogPool_length hw]

theorem work_subset : work L ⊆ L.dialogPool.take 255 := by
  have h : work L=(L.dialogPool.take 255).take 245 := by
    simp only [work,List.take_take]; rfl
  rw [h]
  exact List.take_subset _ _

include hw hn in
theorem ports_nodup :
    (b L :: L.point.finite :: (xs L ++ (rest L ++ work L))).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hy := (y_sublist L hw).count_le q
  have hx := (rest_sublist L).count_le q
  have hp := (List.take_sublist 245 L.dialogPool).count_le q
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
    List.count_nil,List.cons_append,work] at h hy hp ⊢
  omega

include hw in
theorem inputs_mem : b L∈L.point.y ∧ xs L⊆L.point.y ∧ rest L⊆L.point.x := by
  have hy := (y_sublist L hw).subset
  refine ⟨hy (by simp),?_,(rest_sublist L).subset⟩
  intro q hq
  exact hy (List.mem_cons_of_mem _ hq)

include hw in
theorem rest_value (s : BasisState) :
    regValue (rest L) s = regValue L.point.x s / 1024 % 4194304 +
      4194304 * (regValue L.point.x s / 8589934592) := by
  have lo : regValue ((L.point.x.drop 10).take 22) s =
      regValue L.point.x s / 2^10 % 2^22 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by simp [point_x_length L hw]),
      CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [point_x_length L hw]; omega)]
  have hi := CuccaroStreamedSquareWideLayout.regValue_drop_div L.point.x 33
    (by rw [point_x_length L hw]; omega) s
  simp only [rest,regValue_append,lo,hi,List.length_take,List.length_drop,point_x_length L hw]
  norm_num

private theorem packed_eq_highX (v : Nat) :
    (v/1024%4194304 + 4194304*(v/8589934592)=literal) ↔ CodexYParityMath.highX v := by
  have h := Nat.mod_lt (v/1024) (by decide : 0<4194304)
  norm_num [literal,CodexYParityMath.highX]
  omega

private theorem bit_value (r : List Wire) (i : Nat) (s : BasisState) (hi : i<r.length) :
    s (r.getD i 0) = decide (regValue r s / 2^i % 2 = 1) := by
  rw [←regValue_bit r i 0 s hi]
  cases s (r.getD i 0) <;> rfl

include hw in
theorem parity_value (s : BasisState) :
    (s (b L) ^^ CodexYParityGadget.parity (xs L) s) =
      CodexYParityMath.yParity (regValue L.point.y s) := by
  have h232 := bit_value L.point.y 232 s (by rw [point_y_length L hw]; decide)
  have h238 := bit_value L.point.y 238 s (by rw [point_y_length L hw]; decide)
  have h239 := bit_value L.point.y 239 s (by rw [point_y_length L hw]; decide)
  have h240 := bit_value L.point.y 240 s (by rw [point_y_length L hw]; decide)
  have h246 := bit_value L.point.y 246 s (by rw [point_y_length L hw]; decide)
  have h247 := bit_value L.point.y 247 s (by rw [point_y_length L hw]; decide)
  have h248 := bit_value L.point.y 248 s (by rw [point_y_length L hw]; decide)
  have h251 := bit_value L.point.y 251 s (by rw [point_y_length L hw]; decide)
  simp only [b,xs,CodexYParityGadget.parity,List.map_cons,List.map_nil,List.foldr_cons,
    List.foldr_nil,Bool.xor_false,h232,h238,h239,h240,h246,h247,h248,h251,
    CodexYParityMath.yParity,Bool.xor_assoc]
  norm_num

include hw in
theorem hit (s : BasisState) :
    (!(s (b L) ^^ CodexYParityGadget.parity (xs L) s) &&
      decide (regValue (rest L) s=literal)) =
      decide (CodexYParityMath.matchesXY (regValue L.point.x s) (regValue L.point.y s)) := by
  rw [parity_value L hw s,rest_value L hw s]
  have he : decide (regValue L.point.x s/1024%4194304 +
      4194304*(regValue L.point.x s/8589934592)=literal) =
      decide (CodexYParityMath.highX (regValue L.point.x s)) := by
    simp only [packed_eq_highX]
  rw [he]
  cases h : CodexYParityMath.yParity (regValue L.point.y s) <;>
    simp [CodexYParityMath.matchesXY,h]

end ECDSAAdd.Entrant.CodexYParityProbe
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParitySupport =====
section
/-
Research-only integration bridge. Not yet compiled.
The two imports are conveniences for a temporary minimal test tree; strip them when
inserting these declarations after the new gadget in the consolidated Main.
-/

namespace ECDSAAdd.Entrant.CodexYParitySupport
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  ReflectionE1TickGapLow48.generic

/-- The new y sources are the only support beyond the original x-only finite probe. -/
theorem probe_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (xs : List Wire) (b : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hb : b ∈ L.point.y)
    (hxs : xs ⊆ L.point.y) (hr : r ⊆ L.point.x)
    (hwork : work ⊆ L.dialogPool.take 255) :
    wires (CodexYParityGadget.program xs b L.point.finite r work k) ⊆
      wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset := by
  rw [FiniteFlagInterval.old_clrF_support L hw]
  intro q hq
  have h := CodexYParityGadget.program_support xs b L.point.finite r work k hl hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at h
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
  rcases h with rfl | rfl | h | h | h
  · exact Or.inr hb
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (hxs h)
  · exact Or.inl (Or.inr (Or.inl (hr h)))
  · exact Or.inl (Or.inr (Or.inr (hwork h)))

theorem clear_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (xs : List Wire) (b : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hb : b ∈ L.point.y)
    (hxs : xs ⊆ L.point.y) (hr : r ⊆ L.point.x)
    (hwork : work ⊆ L.dialogPool.take 255) :
    wires (CodexYParityGadget.clearProgram xs b L.point.finite r work k) ⊆
      wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
  (CodexYParityGadget.clearProgram_support xs b L.point.finite r work k).trans
    (probe_support_old L hw xs b r work k hl hb hxs hr hwork)

/-- Apply to the new clearF and clrF after unfolding only the two small wrappers. -/
theorem gen_support_old (L : ControlledPointLayout) (hw : L.Widths)
    (cx cy : Fp) (Clear Restore : Program)
    (he : wires Clear ⊆ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset)
    (hc : wires Restore ⊆ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset) :
    wires (FiniteFlagInterval.zrep L ++
      (Clear ++ renameProgram (swapF L) (ReflectionE1TickGapLow48.generic L cx cy) ++ Restore) ++
      FiniteFlagInterval.zrep L) ⊆
      wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset := by
  intro q used
  have hz : q ∈ wires (FiniteFlagInterval.zrep L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => FiniteFlagInterval.zrep_support_old L hw h
  have heq : q ∈ wires Clear → q ∈ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
    fun h => he h
  have hcq : q ∈ wires Restore → q ∈ wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
    fun h => hc h
  simp only [Finset.mem_union] at heq hcq
  simp only [ReflectionE1TickGapLow48.gen, ReflectionE1TickGapLow48.mid,
    wires_append, Finset.mem_union] at used ⊢
  tauto

theorem point_y_generic (L : ControlledPointLayout) :
    L.point.y.toFinset ⊆ (OB5Support.genericSites L).toFinset := by
  intro q hq
  simp only [OB5Support.genericSites, PointAddLayout.pointWires,
    List.mem_toFinset, List.mem_append, List.mem_cons] at hq ⊢
  tauto

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (P : Program)
    (hP : wires P ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset) :
    wires P ⊆ (OB5Support.genericSites L).toFinset := by
  intro q hq
  rcases Finset.mem_union.mp (hP hq) with old | extra
  · exact ReflectionE1TickGapLow48.gen_sites L hw hn cx cy old
  · exact point_y_generic L extra

/-- Relabel an augmented support set when the added set is closed under the map. -/
theorem rename_support_extra (f : Wire → Wire) (P Q : Program) (S : Finset Wire)
    (h : wires P ⊆ wires Q ∪ S) (closed : ∀ q ∈ S, f q ∈ S) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) ∪ S := by
  rw [renameProgram_support, renameProgram_support]
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (h hp) with old | extra
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, old, rfl⟩)
  · exact Finset.mem_union_right _ (closed p extra)

/-- All renamings along the generic-input path are explicit here. -/
theorem wrapper_support_extra (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (S : Finset Wire) (h : wires P ⊆ wires Q ∪ S)
    (hU : ∀ q ∈ S, Wrapper5.U L q ∈ S) (hM : ∀ q ∈ S, tauM L q ∈ S)
    (hE : ∀ q ∈ S, swapE L q ∈ S) (hD : ∀ q ∈ S, swapD L q ∈ S) :
    wires (Edges.wrapper L C cy P) ⊆ wires (Edges.wrapper L C cy Q) ∪ S := by
  have u := rename_support_extra (Wrapper5.U L) P Q S h hU
  have m := rename_support_extra (tauM L) _ _ S u hM
  have e := rename_support_extra (swapE L) _ _ S m hE
  have d := rename_support_extra (swapD L) _ _ S e hD
  have finite :
      wires (Edges.finiteProgram L C cy (renameProgram (Wrapper5.U L) P)) ⊆
      wires (Edges.finiteProgram L C cy (renameProgram (Wrapper5.U L) Q)) ∪ S := by
    intro q hq
    have hd : q ∈ wires (renameProgram (swapD L) (renameProgram (swapE L)
        (renameProgram (tauM L) (renameProgram (Wrapper5.U L) P)))) →
        q ∈ wires (renameProgram (swapD L) (renameProgram (swapE L)
        (renameProgram (tauM L) (renameProgram (Wrapper5.U L) Q)))) ∪ S :=
      fun hh => d hh
    simp only [Finset.mem_union] at hd
    simp only [Edges.finiteProgram, wires_append, Finset.mem_union] at hq ⊢
    tauto
  simpa only [Edges.wrapper] using rename_support_extra (Wrapper5.U L) _ _ S finite hU

/-- The concrete public y register is already counted even if idle. -/
theorem layout_y_io : layout.point.y.toFinset ⊆ ioWires := by decide +kernel

/-- Small finite checks: no arithmetic program is unfolded by these four claims. -/
theorem layout_y_images :
    (layout.point.y.toFinset.image (Wrapper5.U layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (tauM layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (swapE layout) ⊆ layout.point.y.toFinset) ∧
    (layout.point.y.toFinset.image (swapD layout) ⊆ layout.point.y.toFinset) := by
  decide +kernel

/-- An old-wrapper-plus-I/O support bound preserves the exact previous static Q bound. -/
theorem wrapper_qubits760 (C : Point) (cx cy : Fp) (P : Program)
    (hP : wires P ⊆ wires (ReflectionE1TickGapLow48.gen layout cx cy) ∪ layout.point.y.toFinset) :
    qubits (Edges.wrapper layout C cy P) ≤ 1587 := by
  have images := layout_y_images
  have image_closed (f : Wire → Wire)
      (h : layout.point.y.toFinset.image f ⊆ layout.point.y.toFinset) :
      ∀ q ∈ layout.point.y.toFinset, f q ∈ layout.point.y.toFinset :=
    fun q hq => h (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have sup := wrapper_support_extra layout C cy P
    (ReflectionE1TickGapLow48.gen layout cx cy) layout.point.y.toFinset hP
    (image_closed _ images.1) (image_closed _ images.2.1)
    (image_closed _ images.2.2.1) (image_closed _ images.2.2.2)
  have absorb : ioWires ∪ wires (Edges.wrapper layout C cy P) ⊆
      ioWires ∪ wires (Edges.wrapper layout C cy (ReflectionE1TickGapLow48.gen layout cx cy)) := by
    intro q hq
    rcases Finset.mem_union.mp hq with io | used
    · exact Finset.mem_union_left _ io
    · rcases Finset.mem_union.mp (sup used) with old | extra
      · exact Finset.mem_union_right _ old
      · exact Finset.mem_union_left _ (layout_y_io extra)
  exact (Finset.card_le_card absorb).trans (ReflectionE1TickGapLow48.wrapper_qubits760 C cx cy)

end ECDSAAdd.Entrant.CodexYParitySupport
end

-- ===== added module ECDSAAdd.Submission.Entrant.CodexYParityProbe =====
section
/- Research integration draft, not yet compiled as a complete entrant. -/

namespace ECDSAAdd.Entrant.CodexYParityProbe
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def finiteBit (v w : Nat) : Bool := decide (¬ CodexYParityMath.matchesXY v w)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

def clrF : Program := CodexYParityGadget.program (xs L) (b L) L.point.finite (rest L) (work L) literal
def clearF : Program := CodexYParityGadget.clearProgram (xs L) (b L) L.point.finite (rest L) (work L) literal

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0) :
    run (clrF L) m s = ⟨s.phase,writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ finiteBit (regValue L.point.x s.basis) (regValue L.point.y s.basis))⟩ := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have hk : literal < 2^(rest L).length := by rw [(lengths L hw).1]; decide
  rw [clrF,CodexYParityGadget.program_run _ _ _ _ _ _ (ports_nodup L hw hn) hl hk s m hz,
    hit L hw s.basis]
  simp only [finiteBit,decide_not]

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (work L) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  exact CodexYParityGadget.clearProgram_eq _ _ _ _ _ _ (ports_nodup L hw hn)
    ((lengths L hw).1.trans (lengths L hw).2.symm)
    (by rw [(lengths L hw).1]; decide) s m hz hzero

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))) := by
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
    · subst hqf; simp [writeBit,hfs,v.x,v.y]
    · simp [writeBit,hqf,v.rest q hq]

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=finiteBit X.val Y.val) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))) := by
  intro s m v
  have hz : regValue (work L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz]
    simp [writeBit,v.x,v.y,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

include hw in
theorem clrF_support_old : wires (clrF L) ⊆
    wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset := by
  have inputs := inputs_mem L hw
  exact CodexYParitySupport.probe_support_old L hw (xs L) (b L) (rest L) (work L) literal
    ((lengths L hw).1.trans (lengths L hw).2.symm) inputs.1 inputs.2.1 inputs.2.2
    (work_subset L)

include hw in
theorem clearF_support_old : wires (clearF L) ⊆
    wires (ECDSAAdd.Entrant.clrF L) ∪ L.point.y.toFinset :=
  (CodexYParityGadget.clearProgram_support (xs L) (b L) L.point.finite (rest L) (work L) literal).trans
    (clrF_support_old L hw)

include hw in
theorem counts :
    toffoliCount (clrF L)=245 ∧ measurementCount (clrF L)=245 ∧
    toffoliCount (clearF L)=244 ∧ measurementCount (clearF L)=245 := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  have p := CodexYParityGadget.program_counts (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  have c := CodexYParityGadget.clearProgram_counts (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  simpa only [(lengths L hw).1,clrF,clearF] using And.intro p.1 (And.intro p.2 c)

include hw hn in
theorem physical : GatePhysical (clrF L) ∧ GatePhysical (clearF L) := by
  have hl := (lengths L hw).1.trans (lengths L hw).2.symm
  exact ⟨CodexYParityGadget.program_physical _ _ _ _ _ _ hl (ports_nodup L hw hn),
    CodexYParityGadget.clearProgram_physical _ _ _ _ _ _ hl (ports_nodup L hw hn)⟩

abbrev zrep := FiniteFlagInterval.zrep
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L

theorem sentinel_finiteBit : finiteBit FiniteFlagInterval.sentinel 0=false := by
  have eq : FiniteFlagInterval.sentinel=p-1 := by norm_num [FiniteFlagInterval.sentinel,p]
  simp [finiteBit,eq,CodexYParityMath.sentinel_matches]

include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : finiteBit X.val Y.val = fin) (h2 : finiteBit X'.val Y'.val = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ finiteBit X.val Y.val))
        L.point.finite ^^ finiteBit X'.val Y'.val) = base := by
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
    have hx5 : finiteBit x.val y.val = true := decide_eq_true (CodexYParityMath.curve_not_matches hr)
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
      have hg5 : finiteBit (genericX x y cx cy).val (genericY x y cx cy).val = true :=
        decide_eq_true (CodexYParityMath.curve_not_matches (generic_nonsingular hr hc den.1))
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

attribute [local irreducible] toffoliCount measurementCount gateSlots ReflectionE1TickGapLow48.generic

include hw in
theorem gen_support_subset (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) ∪ L.point.y.toFinset := by
  exact CodexYParitySupport.gen_support_old L hw cx cy (clearF L) (clrF L)
    (clearF_support_old L hw) (clrF_support_old L hw)

include hw hn in
theorem gen_sites (cx cy : Fp) : wires (gen L cx cy) ⊆ (OB5Support.genericSites L).toFinset :=
  CodexYParitySupport.gen_sites L hw hn cx cy (gen L cx cy) (gen_support_subset L hw cx cy)

include hw in
theorem gen_counts (cx cy : Fp) :
    toffoliCount (gen L cx cy)+4=toffoliCount (FiniteFlagInterval.gen L cx cy) ∧
    measurementCount (gen L cx cy)+4=measurementCount (FiniteFlagInterval.gen L cx cy) := by
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
  have n := CodexYParityGadget.program_slots (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  have e := CodexYParityGadget.clearProgram_slots (xs L) (b L) L.point.finite (rest L) (work L) literal hl
  rw [(lengths L hw).1] at n e
  have hxs : (xs L).length = 7 := by simp [xs]
  rw [hxs] at n e
  change gateSlots (clrF L)≤2223 at n
  change gateSlots (clearF L)≤2223 at e
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
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+4=
      toffoliCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+4=
      measurementCount (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy))≤
      gateSlots (Edges.wrapper L C cy (FiniteFlagInterval.gen L cx cy)) := by
  have h := gen_counts L hw cx cy
  have s := gen_slots L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1587 :=
  CodexYParitySupport.wrapper_qubits760 C cx cy (gen layout cx cy)
    (gen_support_subset layout layout_widths cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151041,1498861,1587,50236132⟩

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

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2151041 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤2151041
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1498861 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.1
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤1498861
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

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50236132 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (gen layout cx cy) hc).2.2
    have delta := (wrapper_counts layout layout_widths (.some hc) cx cy).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    have growth : Rolling1588.slotGrowth=23581 := rfl
    rw [growth] at old
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (gen layout cx cy))≤50236132
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C control R := (normalize_triple _ _ _).mpr (program_correct C control R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1498861
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1587
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50236132
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.CodexYParityProbe
end

