import ECDSAAdd.Submission.Entrant.PrizeTail05e06b1e9
import ECDSAAdd.Submission.Entrant.PrizeTail8dd9f9e60
import ECDSAAdd.Submission.Entrant.PrizeTaila22007f05

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorEntryCut
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3Seg StairField2V3LastRecX StairField2V3Delta
open StairField2V3EntryPlanR StairOpenWiring StairOuterPlacement StairPhysicalLayout
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] run measurementCount

private theorem pin (x:Nat) (r record:State) (h:RowRelEn x 87 (R0++firstPkt) r record):
    FrameAt x 1 record ∧ AgreeOutside (Δv 87) r record:=by
  obtain ⟨rel,root,tape,⟨F,fx⟩,reach⟩:=h
  have pinned:=g_first root F tape
  rw [fx] at pinned
  exact ⟨reach.symm ▸ pinned.1,rel.1⟩

def stockPrefix:Program:=(((entryPieces cp hostPlan).take 3).map Piece.H).flatten
def Pinned (x:Nat) (ref:State):Prop:=∃record,FrameAt x 1 record ∧ AgreeOutside (Δv 87) ref record
def Loan (ref : State) : Prop := ∀q ∈ StairSchedule.exclusiveRoles ++ hosts 87, ref.basis (fieldPlace q) = false

private theorem loanSite (q : Wire) (hq : q∈StairSchedule.exclusiveRoles ++ hosts 87) :
    fieldPlace q ∈ ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap) := by
  rw [hp_group true 0 1 84 (by decide)]
  exact List.mem_map.mpr ⟨q,hq,rfl⟩

private theorem fullCutClean (parts:StairField13V3Fresh.EntryClean):
    CutClean EntryPre (cut eps 3) ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap):=
  parts.groupsBefore (3,0,1,84) (by simp)
private theorem cutLoan {P : Program} {pre : State → Prop}
    (clean : CutClean pre P ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap))
    (s : State) (h : pre s) (m : List Bool) : Loan (run P m s) := by
  intro q hq
  exact clean s h m _ (loanSite q hq)


theorem at_cut {s:State} (F:EntryFrame s) (m:List Bool):Pinned F.x (run stockPrefix m s) ∧ Loan (run stockPrefix m s):=by
  have eq:=Stair44HostedCut.entry 3 s ⟨F⟩ m
  change run stockPrefix m s=run (cut eps 3) m s at eq
  rw [eq]
  refine ⟨?_,cutLoan (fullCutClean (entryClean_of_planR entryPlans half760)) s ⟨F⟩ m⟩
  obtain ⟨Q,step⟩:=ern3 F.x (entryPlans F.x)
  obtain ⟨n,h⟩:=step s s ⟨⟨F,rfl⟩,rfl⟩ m
  rw [ecut3]
  exact ⟨_,pin _ _ _ h⟩
theorem tag {s:State} (F:EntryFrame s) (m:List Bool):
    (run stockPrefix m s).basis (fieldPlace (base 720))=false:=(at_cut F m).2 _ (by decide +kernel)
end ECDSAAdd.Entrant.StairPacket.ExteriorEntryCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowReturningBytes
open Arithmetic MappedCompressed Secp256k1 FrontierEntry1591Field StockArchiveBanks ExteriorPorts
open WindowParityDirty WindowFieldParity
set_option maxRecDepth 6000
attribute [local irreducible] run measurementCount wires
def Keeps (P : Program) : Prop := ∀(s : State) (m : List Bool) (b : Bank) (i : Fin 16),
  (run P m s).basis (siteAt b i) = s.basis (siteAt b i)

theorem untouched {P : Program} (clear : Clear P) : Keeps P :=
  fun s m b i=>run_preserves_outside P m s _ (clear _ (chart b i).2.2.2)

theorem both {P Q : Program} (hp : Keeps P) (hq : Keeps Q) : Keeps (P ++ Q) := by
  intro s m b i
  rw [run_append]
  exact (hq _ _ _ _).trans (hp _ _ _ _)

theorem parity : Keeps StairSchedule.paritySetup := by
  intro s m b i
  have outside : ∀(v : Bank)(j : Fin 16), siteAt v j≠host := by decide +kernel
  have eq : run StairSchedule.paritySetup m s = flip host (stockParity s) s :=
    ParityHost5.setup_run controls host s m host_not_controls
  rw [eq]
  exact at_other _ _ _ _ (outside b i)

theorem nativeBack {d : Bool} {rows : Bank → Nat} {r m P} (hp : Keeps P)
    (old : ∀b,nativeAt d b (rows b) (run P m r)) : ∀b,nativeAt d b (rows b) r :=
  fun b i=>(hp r m b i).symm.trans (old b i)

theorem nativeUnpull {d : Bool} {rows : Bank → Nat} {r} (old : ∀b,nativeAt d b (rows b) (pullState Rolling1588Lifetime.phaseHost r)) :
    ∀b,nativeAt d b (rows b) r := by
  intro b i
  have v := old b i
  change r.basis (Rolling1588Lifetime.phaseHost (siteAt b i))=_ at v
  rwa [host_ports] at v
end ECDSAAdd.Entrant.StairPacket.WindowReturningBytes

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorEntryCut
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField2V3Seg
open WindowFieldMask WindowFieldJourney WindowFieldCosts ExteriorPorts StockArchiveBanks
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
attribute [local irreducible] run measurementCount
theorem history {x rows} (labels:∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (rows b)):
    (∀j∈bankIds,fieldRows rows j<63145) ∧
    (∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x p (fieldRows rows j)):=by
  have times:∀b:Bank,5*groupId b-5=tick b:=by decide +kernel
  constructor <;> intro j hj <;> obtain ⟨b,rfl⟩:=idAt _ hj <;> rw [rowsAt]
  · exact (labels b).1
  · rw [times];exact (labels b).2

private theorem entered (x:Nat) (rows:Bank→Nat) (a ref:State) (m:List Bool)
    (same:Paired true x a ref rows) (pin:Pinned x ref) (loans:Loan ref):
    Fits (fieldRows rows) (finalCode true (plan true) (initialCode true))
      (run (renameProgram fieldEquiv (group84 true)) m a)
      (run (renameProgram fieldEquiv (group true 1 84)) (referenceTape true (plan true) m) ref):=by
  obtain ⟨record,frame,agree⟩:=pin
  obtain ⟨bound,trace⟩:=history same.labels
  apply hosted
  exact WindowFieldView.caller true x _ bound trace (pullState fieldEquiv a) ref record m
    (fitsPull fieldEquiv fieldEquiv.injective fieldFix (fits same)) frame agree
    (loans _ (by decide +kernel)) loans

theorem group_run {s:State} (F:EntryFrame s) (before m:List Bool) (a:State) (rows:Bank→Nat)
    (same:Paired true F.x a (run stockPrefix before s) rows):
    Fits (fieldRows rows) (finalCode true (plan true) (initialCode true))
      (run (renameProgram fieldEquiv (group84 true)) m a)
      (run (renameProgram fieldEquiv (group true 1 84)) (referenceTape true (plan true) m) (run stockPrefix before s)):=by
  have h:=at_cut F before
  exact entered F.x rows a _ m same h.1 h.2
end ECDSAAdd.Entrant.StairPacket.ExteriorEntryCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowReturningTail
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StockArchiveBanks
open WindowReturningBytes WindowFieldMask WindowFieldJourney ExteriorPorts
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
attribute [local irreducible] run measurementCount wires

def program (pre between post setup : Program) := (((pre ++ setup) ++ between) ++ setup) ++ post
private theorem keepTail {pre between post : Program} (hp : Clear pre) (hb : Clear between) (ht : Clear post) :
    Keeps (program pre between post StairSchedule.paritySetup) :=
  WindowReturningBytes.both (WindowReturningBytes.both (WindowReturningBytes.both
    (WindowReturningBytes.both (untouched hp) WindowReturningBytes.parity) (untouched hb)) WindowReturningBytes.parity) (untouched ht)

private theorem stable {d x rows P} (c : Clear P) :
    Relates P P (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,pair.through P c m⟩

private theorem switchParity {d x rows} : Relates WindowFieldParity.setup StairSchedule.paritySetup
    (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,WindowFieldParity.setup_through pair m m⟩

theorem carry {pre between post : Program} (hp : Clear pre) (hb : Clear between) (ht : Clear post)
    {d x rows} : Relates (program pre between post WindowFieldParity.setup) (program pre between post StairSchedule.paritySetup)
      (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) :=
  compose (compose (compose (compose (stable hp) switchParity) (stable hb)) switchParity) (stable ht)

theorem runTail {pre between post oldPrefix : Program} {s : State} (F : EntryFrame s)
    (shape : WindowMiddleContract.oldDivHead=oldPrefix ++ program pre between post StairSchedule.paritySetup)
    (hp : Clear pre) (hb : Clear between) (ht : Clear post) (a : State) (old m : List Bool)
    (ff : Fits (fieldRows (StockRowVector.rows F.x p)) (finalCode true (plan true) (initialCode true)) a (run oldPrefix old s)) :
    ∃n, Paired false F.x (run (program pre between post WindowFieldParity.setup) m a)
      (run (program pre between post StairSchedule.paritySetup) n (run oldPrefix old s)) (StockRowVector.rows F.x p) := by
  let tape := joinTapes oldPrefix old []
  have native := WindowEndBytes.div_native F tape
  have known := nativeUnpull native.bytes
  unfold tape at known
  rw [shape,joined] at known
  have here := nativeBack (keepTail hp hb ht) known
  have source : Paired false F.x a (run oldPrefix old s) (StockRowVector.rows F.x p) := pairFinished ff native.ids here
  exact carry hp hb ht _ _ source m

theorem entryOfPrefix {pre between post newPrefix oldPrefix : Program}
    (newShape : WindowMiddleContract.divHead=newPrefix ++ program pre between post WindowFieldParity.setup)
    (oldShape : WindowMiddleContract.oldDivHead=oldPrefix ++ program pre between post StairSchedule.paritySetup)
    (hp : Clear pre) (hb : Clear between) (ht : Clear post)
    (starts : ∀ {s : State} (F : EntryFrame s) (m : List Bool), ∃old,
      Fits (fieldRows (StockRowVector.rows F.x p)) (finalCode true (plan true) (initialCode true))
        (run newPrefix m s) (run oldPrefix old s)) : WindowMiddleContract.entry := by
  intro s F m
  obtain ⟨old,ff⟩ := starts F m
  obtain ⟨n,pair⟩ := runTail F oldShape hp hb ht _ old (m.drop (measurementCount newPrefix)) ff
  refine ⟨joinTapes oldPrefix old n,?_⟩
  rw [newShape,oldShape,joined,run_append,run_take]
  exact pairPull Rolling1588Lifetime.phaseHost Rolling1588Lifetime.phaseHost.injective phaseFix pair
end ECDSAAdd.Entrant.StairPacket.WindowReturningTail

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairHostsSchedule ExteriorPorts Rolling1588Lifetime
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount wires

def beforeGroup := StairSchedule.fieldRename (StairLoan.rebindMany StairSchedule.exclusiveRoles
  (hostPlan.firstPacket true) (Rolling1588.placedFirstPacket true) ++ FourScratchWindow.clearProgram)
def rawTail := StairSchedule.forwardSegment cp 87 62 425 450 ++ hostedGroup hostPlan true 14 85 5 ++
    StairSchedule.forwardSegment cp 62 47 450 465 ++ hostedGroup hostPlan true 23 90 3 ++
    StairSchedule.forwardSegment cp 47 32 465 480 ++ hostedGroup hostPlan true 31 93 3 ++
    StairSchedule.forwardSegment cp 32 22 480 490 ++ hostedGroup hostPlan true 37 96 2 ++
    StairSchedule.forwardSegment cp 22 12 490 500 ++ hostedGroup hostPlan true 42 98 2 ++ StairSchedule.forwardLast cp
def pre := renameProgram fieldEquiv rawTail ++ StairSchedule.fieldRename FourScratchWindow.unprefix
def between := StairSchedule.hostedX ++ StairSchedule.fieldRename (entryLowSuffix hostPlan) ++ StairSchedule.hostedX
def post := renameProgram phaseHost Stair44Outer.reverseEnd
def field (S G : Program) := (((beforeGroup ++ renameProgram fieldEquiv G) ++ pre) ++ S) ++ between ++ S

theorem ordinary : StairHostsSchedule.entryFieldHosted cp hostPlan =
    field StairSchedule.paritySetup (WindowFieldCosts.group true 1 84) := by
  simp only [field,beforeGroup,pre,between,rawTail,StairHostsSchedule.entryFieldHosted,
    entryLowPrefix,entryTailPrefix,WindowFieldCosts.group,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem corrected : WindowParityCaller.entryFieldHosted cp =
    field WindowFieldParity.setup (WindowFieldCosts.group84 true) := by
  simp only [field,beforeGroup,pre,between,rawTail,WindowParityCaller.entryFieldHosted,
    WindowCallerCosts.entryLowPrefix,WindowCallerCosts.entryTailPrefix,←placedShape,fieldRename_append,rename_append,List.append_assoc]

def stockBegin := renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)
theorem cutShape : ExteriorEntryCut.stockPrefix = stockBegin ++ beforeGroup := by
  simp only [ExteriorEntryCut.stockPrefix,stockBegin,beforeGroup,entryPieces,List.take_succ_cons,
    List.take_zero,common,firstSlot,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,fieldRename_append,List.append_assoc]
end ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts Rolling1588Lifetime
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires
theorem beforeFree : Clear beforeGroup := fieldRename_free (both (WindowExteriorFixed.first true) clearSafe)
theorem preFree : Clear pre := by
  apply both _ (fieldRename_free unprefixSafe)
  apply fieldMapped
  apply both _ forwardLast
  apply both _ (WindowExitOuter.ordinaryGroup true 42 98 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward490
  apply both _ (WindowExitOuter.ordinaryGroup true 37 96 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward480
  apply both _ (WindowExitOuter.ordinaryGroup true 31 93 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward465
  apply both _ (WindowExitOuter.ordinaryGroup true 23 90 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward450
  exact both forward425 (WindowExitOuter.ordinaryGroup true 14 85 5 (by decide) (by decide) (by decide) (by decide +kernel))
theorem betweenFree : Clear between := by
  apply both _ WindowExitOuter.hostedX
  apply both WindowExitOuter.hostedX
  apply fieldRename_free
  apply both _ unprefixSafe
  apply both clearSafe
  exact WindowExitClear.renameClear Prefix1590.borrow Prefix1590.borrow.injective
    (by unfold Fixed; decide +kernel) (WindowExteriorFixed.tail (WindowExitOuter.other true))
theorem postFree : Clear post := mapped _ phaseHost.injective phaseFix reverseEnd_free
end ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorDivReady
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates ExteriorPorts ExteriorDivPieces WindowFieldMask WindowFieldJourney
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
attribute [local irreducible] run measurementCount wires

def pack := renameProgram phaseHost checkpointPrimitives.firstPack
def beginW := opening true 154 ++ pack
def beginR := original true 154 ++ pack
def prefixW := (beginW ++ beforeGroup) ++ renameProgram fieldEquiv (WindowFieldCosts.group84 true)
def prefixR := (beginR ++ beforeGroup) ++ renameProgram fieldEquiv (WindowFieldCosts.group true 1 84)

theorem refBegin : beginR = Stair44Kernel.divLead := by
  simp only [beginR,original,pack,Stair44Kernel.divLead,Six505.rename_append]

theorem begin_pair {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃n, Paired true F.x (run beginW m s) (run beginR n s) (StockRowVector.rows F.x p) := by
  let A := opening true 154
  let B := original true 154
  let t := m.drop (measurementCount A)
  refine ⟨joinTapes B m t,?_⟩
  rw [beginW,beginR,joined,run_append,run_take]
  apply pairUnpull phaseHost phaseFix
  rw [pack,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  exact (WindowStartStates.division F m).through _ firstPack_free _

theorem cut {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃old rec, Paired true F.x (run (beginW ++ beforeGroup) m s) (run (beginR ++ beforeGroup) old s)
        (StockRowVector.rows F.x p) ∧ run (beginR ++ beforeGroup) old s = run ExteriorEntryCut.stockPrefix rec s := by
  obtain ⟨n,pair⟩ := begin_pair F m
  let t := m.drop (measurementCount beginW)
  refine ⟨joinTapes beginR n t,joinTapes stockBegin n t,?_,?_⟩
  · rw [joined,run_append,run_take]
    exact pair.through _ beforeFree _
  · rw [cutShape,joined,joined,refBegin,WindowStockHead.leadD F]
    rfl

theorem starts {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃old, Fits (fieldRows (StockRowVector.rows F.x p)) (finalCode true (plan true) (initialCode true))
      (run prefixW m s) (run prefixR old s) := by
  obtain ⟨n,k,pair,eq⟩ := cut F m
  let t := m.drop (measurementCount (beginW ++ beforeGroup))
  let tape := referenceTape true (plan true) t
  refine ⟨joinTapes (beginR ++ beforeGroup) n tape,?_⟩
  rw [prefixR,prefixW,joined,run_append,run_take,eq]
  rw [eq] at pair
  exact ExteriorEntryCut.group_run F k t _ _ pair

theorem newShape : WindowMiddleContract.divHead = prefixW ++ WindowReturningTail.program pre between post WindowFieldParity.setup := by
  simp only [WindowMiddleContract.divHead,WindowKernelPrograms.divBefore,corrected,field,prefixW,beginW,
    opening,pack,post,WindowReturningTail.program,Six505.rename_append,List.append_assoc]
theorem oldShape : WindowMiddleContract.oldDivHead = prefixR ++ WindowReturningTail.program pre between post StairSchedule.paritySetup := by
  simp only [WindowMiddleContract.oldDivHead,Stair44Kernel.fieldD,ordinary,field,prefixR,refBegin,
    post,WindowReturningTail.program,List.append_assoc]
theorem entry : WindowMiddleContract.entry :=
  WindowReturningTail.entryOfPrefix newShape oldShape preFree betweenFree postFree starts
end ECDSAAdd.Entrant.StairPacket.ExteriorDivReady

end

section

namespace ECDSAAdd.Entrant

def entry : Challenge.Entry := StairPacket.WindowParityRelease.entry
def bounds : Challenge.Bounds := StairPacket.WindowParityRelease.bounds
theorem certificate : Challenge.Certificate entry bounds :=
  StairPacket.WindowReleaseProof.certificate StairPacket.ExteriorDivReady.entry StairPacket.WindowExitReady.exit

end ECDSAAdd.Entrant

#print axioms ECDSAAdd.Entrant.entry
#print axioms ECDSAAdd.Entrant.bounds
#print axioms ECDSAAdd.Entrant.certificate

end

