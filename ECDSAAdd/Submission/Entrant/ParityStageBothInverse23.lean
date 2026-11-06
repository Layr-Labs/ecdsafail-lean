import ECDSAAdd.Submission.Entrant.InverseFiveEntry23
import ECDSAAdd.Submission.Entrant.ParityStageXInverse23
import ECDSAAdd.Submission.Entrant.ParityUniform
import ECDSAAdd.Submission.Entrant.ParityXEntry
import ECDSAAdd.Submission.Entrant.ParityXExitInverse23Kernel
import ECDSAAdd.Submission.Entrant.MainPart07

namespace ECDSAAdd.Entrant.ParityStageBothInverse23
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
  ReflectionE1TickGap OB5 Rolling1588Lifetime ParityCarry ParityConvert ParityUniform ParityXEntry
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical
  InverseFive23.lastPhase15 InverseFive23.stackReverse15 InverseFive23.reverseTail15 Rolling1588TickGap.tailPhase
attribute [local irreducible] InverseFour15.lastPhase15 InverseFour15.stackReverse15
  InverseFour15.reverseTail15 Rolling1588.entryFieldHosted

def restEntry (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true) ++
      (Rolling1588.entryFieldHosted ++ renameProgram phaseHost (InverseFive23.lastPhase15 false)))

def entryRef (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky ++ E1QubitPlacement.entryM L kx ++ restEntry L

theorem entry_split_ref (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry InverseFiveEntry23.entryKernel15 L = E1QubitPlacement.tickF L ++ restEntry L := by
  have tick := E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base)) = E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,InverseFiveEntry23.entryKernel15,InverseFiveEntry23.kernel15,
    Rolling1588TickGap.firstPhase,restEntry,renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem entryRef_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryRef L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX L hw hn X Y G origin kx
  have divide := division_step InverseFiveEntry23.entryKernel15 InverseFiveEntry23.entry_support530
    InverseFiveEntry23.entry_correct15 L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior := add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky ++ E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx ++ fusedY L ky ++ E1QubitPlacement.tickF L)
    (R:=restEntry L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryRef,division,entry_split_ref,List.append_assoc] using prior


def entryStageAll (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  entryYAll L ky++entryXAll L kx++restEntry L

theorem entryStageAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (s : State) (m : List Bool) (hX:regValue L.point.x s.basis=X.val)
    (hY:regValue L.point.y s.basis=Y.val) (hc : regValue L.dialogPool s.basis=0) :
    run (entryStageAll L kx ky) m s=run (entryRef L kx ky) m s := by
  have cm:measurementCount (entryYAll L ky)=measurementCount (fusedY L ky) :=
    (entryYAll_counts L hw ky).2.1.trans (fusedY_counts L hw ky).2.symm
  have first:=prefix_eq (entryYAll L ky) (fusedY L ky) (entryXAll L kx++restEntry L) s m cm
      (entryYAll_eq L hw hn Y ky s m hY hc)
  have fy:=fusedY_correct L hw hn Y ky s (m.take (measurementCount (fusedY L ky))) hY hc
  let t:=run (fusedY L ky) (m.take (measurementCount (fusedY L ky))) s
  have tx:regValue L.point.x t.basis=X.val:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q ((E1QubitPlacement.lay L hw hn q).1 hq)),hX]
  have tc:regValue L.dialogPool t.basis=0:=by
    rw [regValue_congr _ _ s.basis (fun q hq=>fy.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).2)),hc]
  have second:=prefix_eq (entryXAll L kx) (E1QubitPlacement.entryM L kx) (restEntry L)
    t (m.drop (measurementCount (fusedY L ky))) (entryXAll_counts L kx).2.1
    (entryXAll_eq L hw hn X kx t _ tx tc)
  change run ((entryYAll L ky++entryXAll L kx)++restEntry L) m s=_
  rw [List.append_assoc,first]
  simpa only [entryRef,List.append_assoc,run_append,t] using second

theorem entryStageAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y kx ky : Fp) (G : Bool) (origin : BasisState) (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStageAll L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  intro s m hs
  rw [entryStageAll_eq L hw hn X Y kx ky s m hs.x hs.y hs.clean]
  exact entryRef_step L hw hn X Y kx ky G origin hx s m hs

theorem multiplyExitAll_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ParityXExitInverse23Kernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (P++exitYAll L k) m s=run (P++ExitFusionResearch.exitY L k) m s := by
  let n:=measurementCount P
  let a:=run P (m.take n) s
  have hp:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have half:=correct X.val Y.val X.isLt hp Y.isLt s (m.take n) v.x v.y v.clean
  have poolY (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_right _ h)
  have poolX (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    fun h=>finPool_not_xy L hn q hq (List.mem_append_left _ h)
  have ac:regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq=>half.2.2.2 q (poolY q hq) (poolX q hq)),v.clean]
  have av:regValue L.point.y a.basis=centerWord ((Y*X)/2) := by
    simpa only [ZMod.natCast_zmod_val] using half.2.1
  rw [run_append,run_append]
  exact exitYAll_eq L hw hn ((Y*X)/2) k a (m.drop n) (m.drop n) av ac

theorem multiplyExitAll_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (cx : Fp) (correct : ParityXExitInverse23Kernel.HalfMultiplyNegCorrect L P cx.val)
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (P++exitYAll L k)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then k else 0)) G origin) := by
  intro s m hs
  rw [multiplyExitAll_eq L hw hn P cx correct X Y k G origin hX s m hs]
  exact ParityXExitInverse23Kernel.fusedMultiplyX_step L hw hn P cx correct X Y k G origin hX s m hs

def secondStageAll (L : ControlledPointLayout) (k cy cx : Fp) : Program :=
  ReflectionE1TickGapLow48.squareEntry L k++ParityXExitInverse23Kernel.restXX L cx.val++exitYAll L cy

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
open ReflectionE1TickGapLow48
theorem secondStageAll_step (X Y k cy cx : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStageAll L k cy cx)
      (PointDialogValues L (if G then cx-Z else Z) (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=multiplyExitAll_step L hw hn
    (FrontierEntry1591Callers.exit (ParityXExitInverse23Kernel.kernelX cx.val) L) cx
    (ParityXExitInverse23Kernel.exitX_correct L hw hn cx.val cx.isLt)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStageAll,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=ParityXExitInverse23Kernel.restXX L cx.val++exitYAll L cy)
  · intro s v m1 m2
    exact squareEntry_base L hw hn k X Y G origin s m1 m2 v
  · simpa only [ParityXExitInverse23Kernel.exit_splitX,List.append_assoc,Z] using prior

end

def genericAll (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStageAll L (-cx) (-cy)++secondStageAll L (ReflectionE1.correction cx) cy cx

def genericRef (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ParityStageXInverse23.entryRef L (-cx) (-cy)++ReflectionE1TickGapLow48.secondStageX L (ReflectionE1.correction cx) cy cx

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (genericAll L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStageAll_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy cx true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring,
    show a*d-cy=genericY X Y cx cy from hv.2.2] at second
  exact first.seq second

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (genericAll L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStageAll_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStageAll_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy cx false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second
  rw [back] at second
  exact first.seq second



end


theorem last_delta (b : Bool) :
    toffoliCount (InverseFive23.lastPhase15 b)+1=toffoliCount (InverseFour15.lastPhase15 b) ∧
    measurementCount (InverseFive23.lastPhase15 b)=measurementCount (InverseFour15.lastPhase15 b) ∧
    gateSlots (InverseFive23.lastPhase15 b)=gateSlots (InverseFour15.lastPhase15 b)+151 := by
  have h:=InverseFive23.stack_delta b
  simp only [InverseFive23.lastPhase15,InverseFour15.lastPhase15,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  omega

theorem rest_delta (L : ControlledPointLayout) :
    toffoliCount (restEntry L)+1=toffoliCount (ParityStageXInverse23.restEntry L) ∧
    measurementCount (restEntry L)=measurementCount (ParityStageXInverse23.restEntry L) ∧
    gateSlots (restEntry L)=gateSlots (ParityStageXInverse23.restEntry L)+151 := by
  have h:=last_delta false
  simp only [restEntry,ParityStageXInverse23.restEntry,toffoliCount_append,
    measurementCount_append,gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,rename_gateSlots]
  omega

theorem nested_support (f g : Wire→Wire) (P Q R S : Program) (h : wires R⊆wires S) :
    wires (renameProgram f (P++(Q++renameProgram g R)))⊆
      wires (renameProgram f (P++(Q++renameProgram g S))) := by
  simp only [renameProgram_support,wires_append]
  exact Finset.image_mono f (Finset.union_subset_union (Finset.Subset.refl _) 
    (Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono g h)))

theorem rest_subset (L : ControlledPointLayout) :
    wires (restEntry L)⊆wires (ParityStageXInverse23.restEntry L) :=
  nested_support (wireFn2 L) phaseHost
    (renameProgram phaseHost (Rolling1588TickGap.tailPhase true)) Rolling1588.entryFieldHosted
    (InverseFive23.lastPhase15 false) (InverseFour15.lastPhase15 false) (InverseFive23.last_subset false)

theorem rest_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restEntry L) := by
  have p := placed_physical InverseFiveEntry23.entryKernel15 InverseFiveEntry23.entry_support530
    InverseFiveEntry23.entry_physical15 L hw hn
  have entryP : GatePhysical (FrontierEntry1591Callers.entry InverseFiveEntry23.entryKernel15 L) := by
    simpa only [FrontierEntry1591Callers.entry] using p
  rw [entry_split_ref,gatePhysical_append] at entryP
  exact entryP.2

theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+6=toffoliCount (genericRef L cx cy) ∧
    measurementCount (genericAll L cx cy)=measurementCount (genericRef L cx cy) ∧
    gateSlots (genericAll L cx cy)≤gateSlots (genericRef L cx cy)+302 := by
  have e:=rest_delta L
  have r:=ParityXExitInverse23Kernel.restXX_delta L cx.val
  have x:=entryXAll_counts L (-cx)
  have a:=entryYAll_counts L hw (-cy)
  have aa:=fusedY_counts L hw (-cy)
  have b:=exitYAll_counts L hw cy
  have bb:=ExitFusionResearch.exitY_counts L hw cy
  simp only [genericAll,genericRef,entryStageAll,ParityStageXInverse23.entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem generic_toffoli (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericAll L cx cy)+6=toffoliCount (genericRef L cx cy) := by
  have h:=generic_counts L hw cx cy
  omega

theorem generic_wires (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (genericAll L cx cy)⊆wires (genericRef L cx cy) := by
  have r:=ParityXExitInverse23Kernel.restXX_subset L cx.val
  have a:=entryYAll_wires L hw (-cy)
  have b:=exitYAll_wires L hw cy
  simp only [genericAll,genericRef,entryStageAll,ParityStageXInverse23.entryRef,secondStageAll,
    ReflectionE1TickGapLow48.secondStageX,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union a (entryXAll_wires L (-cx))) (rest_subset L))
    (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) r) b)

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp)
    (h : GatePhysical (genericRef L cx cy)) : GatePhysical (genericAll L cx cy) := by
  simp only [genericRef,ParityStageXInverse23.entryRef,ReflectionE1TickGapLow48.secondStageX,gatePhysical_append] at h
  simp only [genericAll,entryStageAll,secondStageAll,gatePhysical_append]
  exact ⟨⟨⟨entryYAll_physical L hw hn (-cy),entryXAll_physical L hw hn (-cx)⟩,rest_physical L hw hn⟩,
    ⟨⟨h.2.1.1,ParityXExitInverse23Kernel.restXX_physical L hw hn cx.val⟩,exitYAll_physical L hw hn cy⟩⟩

end ECDSAAdd.Entrant.ParityStageBothInverse23
