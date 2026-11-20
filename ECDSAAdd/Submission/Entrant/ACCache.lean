import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.PairFrameUnique
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Arithmetic.NarrowSignedRecord
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ExactBorrowErase
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.DisjointPrograms
import ECDSAAdd.Challenge.Contract
import Mathlib.Tactic.FinCases
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof
import ECDSAAdd.Framework.Cost
import ECDSAAdd.Framework.PacketSequenceFrame
import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Arithmetic.SignedWordBits
import ECDSAAdd.Arithmetic.SignedHalf
import ECDSAAdd.Arithmetic.BalancedCoreLayoutProof
import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Math.SkywalkTerminationBudget
import ECDSAAdd.Math.SkywalkTrace
import ECDSAAdd.Arithmetic.RecordedRailRippleCertificate
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Arithmetic.RecordedRailVentedProof
import ECDSAAdd.Framework.WireRenameEquivalence
import ECDSAAdd.Framework.WireRenameComposition
import ECDSAAdd.Submission.Entrant.Prelude
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.FullLogic
import ECDSAAdd.Submission.Entrant.Fold98
import ECDSAAdd.Submission.Entrant.KnownZeroArithmetic
import ECDSAAdd.Submission.Entrant.BOptimizationsCore

-- repack: ACCache lines 300..5408
section
section
section
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95FactsResearch
open BShortGhostFactsResearch BShortGhostProgramsResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
abbrev old:Program:=ReorderedBMiddlePatchesResearch.output
def ports:Fin 12→Wire:=![256,4889,4627,4628,257,4760,4759,4758,4762,0,1,2]
def oldWindow:Program:=renameProgram (B95PlacedWindowResearch.label ports) B95FiniteWindowResearch.original
def fastWindow:Program:=B95PlacedWindowResearch.fastAt ports
def gap:Program:=(old.drop 2435).take 676
def center:Program:=(old.drop 3112).take 1497++d0++(old.drop 4616).take 758
def suffix:Program:=(old.drop 5376).take 1596++f0++g

theorem ports_inj:Function.Injective ports:=by decide +kernel

theorem checked:
 b0=oldWindow ∧
 (old.drop 3111).take 1=[.CX 4758 4762] ∧
 (old.drop 5374).take 2=[.CX 4762 4758,.X 4758] ∧
 PairedWritesResearch.check 4758 a none=some none ∧
 C163Touch.touched gap 4758=false ∧ C163Touch.touched gap 4762=false ∧
 C163Touch.touched center 4758=false ∧ C163Touch.touched suffix 4758=false ∧
 ([a,fastWindow,gap,center,suffix]:List Program).all (fun P=>
  ([4757,4758,4759,4243,4244,4245]:List Wire).all (fun q=>!C163Touch.touched P q))=true:=by decide +kernel

end ECDSAAdd.Entrant.B95FactsResearch

end

-- Verified B95 optimization component B95Parts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95FactsResearch
open BShortGhostFactsResearch BShortGhostProgramsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem c_split:c=gap++copy 4758 4762++(old.drop 3112).take 1497:=by
 have h:=ListWindowPartsResearch.c_template old
 have eq:=congrArg (fun P:Program=>(old.drop 2435).take 676++P++(old.drop 3112).take 1497) checked.2.1
 exact h.trans eq

theorem e_split:e=(old.drop 4616).take 758++cleanup 4758 4762++(old.drop 5376).take 1596:=by
 have h:=ListWindowPartsResearch.e_template old
 have eq:=congrArg (fun P:Program=>(old.drop 4616).take 758++P++(old.drop 5376).take 1596) checked.2.2.1
 exact h.trans eq

theorem old_shape:B95Q0BaseResearch.program=a++b0++(gap++copy 4758 4762++center++cleanup 4758 4762++suffix):=by
 simp only [B95Q0BaseResearch.program,c_split,e_split,center,suffix,List.append_assoc]

theorem gap_fresh:4758∉wires gap ∧ 4762∉wires gap:=
 ⟨not_wire _ _ checked.2.2.2.2.1,not_wire _ _ checked.2.2.2.2.2.1⟩

theorem center_fresh:4758∉wires center:=not_wire _ _ checked.2.2.2.2.2.2.1

theorem suffix_fresh:4758∉wires suffix:=not_wire _ _ checked.2.2.2.2.2.2.2.1

end ECDSAAdd.Entrant.B95FactsResearch

end

-- Verified B95 optimization component B95WindowFrame
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95FactsResearch
open BShortGhostFactsResearch BShortGhostProgramsResearch B95RetimeResearch ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem reference_shape:B95PlacedWindowResearch.originalAt ports=oldWindow++exchange 4758 4762:=by decide +kernel

theorem window_measurements:measurementCount fastWindow=measurementCount b0:=by
 have n:measurementCount fastWindow=measurementCount B95FiniteWindowResearch.fast:=
  (renameProgram_counts _ _).2
 have o:measurementCount oldWindow=measurementCount B95FiniteWindowResearch.original:=
  (renameProgram_counts _ _).2
 exact (n.trans B95FiniteWindowResearch.counts.2.1).trans
  (o.symm.trans (congrArg measurementCount checked.1.symm))

theorem window_eq(s:State)(m:List Bool)
 (hc:s.basis 4760=false)(h2:s.basis 4759=false)(h1:s.basis 4758=false)(hm:s.basis 4762=false):
 run fastWindow m s=run (exchange 4758 4762) [] (run b0 m s):=by
 have eq:=B95PlacedWindowResearch.run_eq ports ports_inj s m ⟨hc,h2,h1,hm⟩
 have refEq:run (B95PlacedWindowResearch.originalAt ports) m s=
  run (exchange 4758 4762) [] (run oldWindow m s):=by
  rw [reference_shape,run_cat]
  exact zero_records _ (by simp [exchange,measurementCount]) _ _
 exact eq.trans (refEq.trans (congrArg (fun t=>run (exchange 4758 4762) [] t)
  (congrArg (fun P=>run P m s) checked.1.symm)))

end ECDSAAdd.Entrant.B95FactsResearch

namespace ECDSAAdd.Entrant.B95RetimeResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
attribute [local irreducible] ECDSAAdd.run

theorem window_context(A W V B C D:Program)(q z:Wire)(ne:q≠z)
 (bq:q∉wires B)(bz:z∉wires B)(cq:q∉wires C)(dq:q∉wires D)
 (mc:measurementCount V=measurementCount W)(s:State)(m:List Bool)
 (eq:∀r,run V r (run A (m.take (measurementCount A)) s)=
  run (exchange q z) [] (run W r (run A (m.take (measurementCount A)) s)))
 (hz:∀r,(run W r (run A (m.take (measurementCount A)) s)).basis z=false):
 run (A++V++(B++C++D)) m s=erase q (run (A++W++(B++copy q z++C++cleanup q z++D)) m s):=by
 rw [run_three A V (B++C++D) s m,run_three A W (B++copy q z++C++cleanup q z++D) s m]
 rw [mc,eq]
 exact retime B C D q z ne bq bz cq dq _ _ (hz _)

end ECDSAAdd.Entrant.B95RetimeResearch

end

-- Verified B95 optimization component B95Middle (core)
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95MiddleResearch
open BShortGhostFactsResearch BShortGhostProgramsResearch B95FactsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def program:Program:=a++fastWindow++gap++center++suffix

theorem fresh(q:Wire)(hq:q∈([4757,4758,4759,4243,4244,4245]:List Wire)):
 q∉wires program:=by
 have checked:=B95FactsResearch.checked.2.2.2.2.2.2.2.2
 have off(P:Program)(hp:P∈([a,fastWindow,gap,center,suffix]:List Program)):q∉wires P:=by
  have h:=List.all_eq_true.mp (List.all_eq_true.mp checked P hp) q hq
  intro bad
  have yes:C163Touch.touched P q=true:=(C163Touch.touched_spec _ _).mpr bad
  simp only [yes,Bool.not_true,Bool.false_eq_true] at h
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨⟨⟨off a (by simp),off fastWindow (by simp)⟩,off gap (by simp)⟩,off center (by simp)⟩,off suffix (by simp)⟩


end ECDSAAdd.Entrant.B95MiddleResearch

end

-- Verified B95 optimization component B95MiddleResources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95MiddleResearch
open BShortGhostFactsResearch BShortGhostProgramsResearch B95FactsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots
 B95Q0BaseResearch.program ECDSAAdd.wires GatePhysical

theorem q0_metric(metric:Program→Nat)(app:∀P Q,metric (P++Q)=metric P+metric Q)
 (hb:metric b0=metric b)(hd:metric d0=metric d)(hf:metric f0=metric f):
 metric B95Q0BaseResearch.program=metric ReorderedBMiddlePatchesResearch.output:=by
 have old:=congrArg metric BShortGhostProgramsResearch.old_shape
 have new:metric B95Q0BaseResearch.program=metric a+metric b0+metric c+metric d0+metric e+metric f0+metric g:=by
  simp only [B95Q0BaseResearch.program,app]
 simp only [app] at old
 change metric B95Q0BaseResearch.program=metric BShortGhostProgramsResearch.old
 omega

theorem q0_counts:
 toffoliCount B95Q0BaseResearch.program=toffoliCount ReorderedBMiddlePatchesResearch.output ∧
 measurementCount B95Q0BaseResearch.program=measurementCount ReorderedBMiddlePatchesResearch.output ∧
 Challenge.gateSlots B95Q0BaseResearch.program=Challenge.gateSlots ReorderedBMiddlePatchesResearch.output:=by
 refine ⟨q0_metric toffoliCount toffoliCount_append ?_ ?_ ?_,
  q0_metric measurementCount measurementCount_append ?_ ?_ ?_,
  q0_metric Challenge.gateSlots Challenge.gateSlots_append ?_ ?_ ?_⟩
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).2
 · exact (renameProgram_counts _ _).2
 · exact (renameProgram_counts _ _).2
 · exact Baselines.rename_gateSlots _ _
 · exact Baselines.rename_gateSlots _ _
 · exact Baselines.rename_gateSlots _ _

theorem window_slots:Challenge.gateSlots fastWindow+6=Challenge.gateSlots b0:=by
 have n:Challenge.gateSlots fastWindow=Challenge.gateSlots B95FiniteWindowResearch.fast:=Baselines.rename_gateSlots _ _
 have o:Challenge.gateSlots oldWindow=Challenge.gateSlots B95FiniteWindowResearch.original:=Baselines.rename_gateSlots _ _
 have e:=congrArg Challenge.gateSlots B95FactsResearch.checked.1
 have h:=B95FiniteWindowResearch.counts.2.2
 omega

theorem window_toffoli:toffoliCount fastWindow=toffoliCount b0:=by
 have n:toffoliCount fastWindow=toffoliCount B95FiniteWindowResearch.fast:=(renameProgram_counts _ _).1
 have o:toffoliCount oldWindow=toffoliCount B95FiniteWindowResearch.original:=(renameProgram_counts _ _).1
 exact (n.trans B95FiniteWindowResearch.counts.1).trans (o.symm.trans (congrArg toffoliCount B95FactsResearch.checked.1.symm))

theorem counts:toffoliCount program=toffoliCount ReorderedBMiddlePatchesResearch.output ∧
 measurementCount program=measurementCount ReorderedBMiddlePatchesResearch.output ∧
 Challenge.gateSlots program+9=Challenge.gateSlots ReorderedBMiddlePatchesResearch.output:=by
 have t:=congrArg toffoliCount B95FactsResearch.old_shape
 have m:=congrArg measurementCount B95FactsResearch.old_shape
 have s:=congrArg Challenge.gateSlots B95FactsResearch.old_shape
 have c:toffoliCount (copy 4758 4762)=0 ∧ measurementCount (copy 4758 4762)=0 ∧ Challenge.gateSlots (copy 4758 4762)=1:=by decide +kernel
 have e:toffoliCount (cleanup 4758 4762)=0 ∧ measurementCount (cleanup 4758 4762)=0 ∧ Challenge.gateSlots (cleanup 4758 4762)=2:=by decide +kernel
 have old:=q0_counts
 have tw:=window_toffoli
 have mw:=window_measurements
 have sw:=window_slots
 simp only [toffoliCount_append] at t
 simp only [measurementCount_append] at m
 simp only [Challenge.gateSlots_append] at s
 simp only [program,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩


end ECDSAAdd.Entrant.B95MiddleResearch

end

-- Verified B95 optimization component B95MiddlePhysical
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95MiddleResearch
open BShortGhostFactsResearch BShortGhostProgramsResearch B95FactsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] GatePhysical ECDSAAdd.wires

theorem physical_slice(P:Program)(a b:Nat)(h:GatePhysical P):GatePhysical ((P.drop a).take b):=by
 unfold GatePhysical at *
 intro i hi
 exact h i (List.mem_of_mem_drop (List.mem_of_mem_take hi))

theorem physical_drop(P:Program)(a:Nat)(h:GatePhysical P):GatePhysical (P.drop a):=by
 unfold GatePhysical at *
 intro i hi
 exact h i (List.mem_of_mem_drop hi)

theorem fast_physical:GatePhysical fastWindow:=by
 change GatePhysical [
  .CCX 256 4889 4760,.CX 4627 4760,.CX 4627 4889,.CX 4627 256,.CX 4628 257,.CX 4628 4760,
  .CCX 257 4760 4762,.CX 4628 4762,.CX 4628 4760,.CX 4760 257,
  .measureX 4760 [] [.CZ 4627 256,.CZ 4627 4889,.CZ 256 4889],.measureX 4760 [] []]
 simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]

theorem physical:GatePhysical program:=by
 have p:GatePhysical B95FactsResearch.old:=ReorderedBMiddlePatchesResearch.physical BReorderedPhysicalResearch.middle
 have aP:GatePhysical a:=by simpa only [a,List.drop_zero] using physical_slice B95FactsResearch.old 0 2420 p
 have dP:GatePhysical d0:=gatePhysical_rename (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective d
  (physical_slice B95FactsResearch.old 4609 7 p)
 have fP:GatePhysical f0:=gatePhysical_rename (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective f
  (physical_slice B95FactsResearch.old 6972 10 p)
 have cP:GatePhysical center:=by
  simp only [center,gatePhysical_append]
  exact ⟨⟨physical_slice B95FactsResearch.old 3112 1497 p,dP⟩,physical_slice B95FactsResearch.old 4616 758 p⟩
 have sP:GatePhysical suffix:=by
  simp only [suffix,gatePhysical_append]
  exact ⟨⟨physical_slice B95FactsResearch.old 5376 1596 p,fP⟩,physical_drop B95FactsResearch.old 6982 p⟩
 simp only [program,gatePhysical_append]
 exact ⟨⟨⟨⟨aP,fast_physical⟩,physical_slice B95FactsResearch.old 2435 676 p⟩,cP⟩,sP⟩

end ECDSAAdd.Entrant.B95MiddleResearch

end

-- Verified B95 optimization component B95MiddleSupport
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95MiddleResearch
open BShortGhostFactsResearch BShortGhostProgramsResearch B95FactsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem slice_subset(P:Program)(a b:Nat):wires ((P.drop a).take b)⊆wires P:=by
 have h:=congrArg wires (List.take_append_drop a P)
 have k:=congrArg wires (List.take_append_drop b (P.drop a))
 rw [wires_append] at h k
 exact (k ▸ Finset.subset_union_left).trans (h ▸ Finset.subset_union_right)

theorem drop_subset(P:Program)(a:Nat):wires (P.drop a)⊆wires P:=by
 have h:=congrArg wires (List.take_append_drop a P)
 rw [wires_append] at h
 exact h ▸ Finset.subset_union_right

theorem fast_support:wires fastWindow⊆wires oldWindow∪{4762}:=by decide +kernel

theorem fresh_of_old(q:Wire)(off:q∉wires ReorderedBMiddlePatchesResearch.output)
 (fixed:(Equiv.swap 4757 4760) q=q)(mod:q≠4762):q∉wires program:=by
 have slice(a b:Nat):q∉wires ((ReorderedBMiddlePatchesResearch.output.drop a).take b):=
  fun h=>off (slice_subset _ a b h)
 have aOff:q∉wires a:=by simpa only [a,List.drop_zero] using slice 0 2420
 have bOff:q∉wires b0:=fresh_fixed _ (Equiv.swap 4757 4760).injective b q fixed (slice 2420 15)
 have fastOff:q∉wires fastWindow:=by
  intro h
  rcases Finset.mem_union.mp (fast_support h) with h|h
  · exact bOff ((congrArg wires B95FactsResearch.checked.1).symm ▸ h)
  · exact mod (Finset.mem_singleton.mp h)
 have dOff:q∉wires d0:=fresh_fixed _ (Equiv.swap 4757 4760).injective d q fixed (slice 4609 7)
 have fOff:q∉wires f0:=fresh_fixed _ (Equiv.swap 4757 4760).injective f q fixed (slice 6972 10)
 have cOff:q∉wires center:=by
  simp only [center,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨slice 3112 1497,dOff⟩,slice 4616 758⟩
 have sOff:q∉wires suffix:=by
  simp only [suffix,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨slice 5376 1596,fOff⟩,fun h=>off (drop_subset _ 6982 h)⟩
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨⟨⟨aOff,fastOff⟩,slice 2435 676⟩,cOff⟩,sOff⟩

end ECDSAAdd.Entrant.B95MiddleResearch

end

-- Verified B95 optimization component B95Aliases (definitions)
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95AliasesResearch
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev original:Program:=ReorderedBMiddlePatchesResearch.output
abbrev single:Program:=B95MiddleResearch.program
def prep:Program:=[.CX 4243 4245]
def first:Program:=renameProgram (Equiv.swap 4505 4243) single
def second:Program:=renameProgram (Equiv.swap 4506 4244) first
def aliased:Program:=renameProgram (Equiv.swap 4507 4245) second
def program:Program:=prep++aliased++prep


end ECDSAAdd.Entrant.B95AliasesResearch

end

-- Verified B95 optimization component B95AliasesResources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95AliasesResearch
open BShortGhostProgramsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem combine_fresh(q:Wire)(off:q∉wires aliased)(h0:q≠4243)(h2:q≠4245):q∉wires program:=by
 have small:q∉wires prep:=by simp [prep,wires,Instr.wires,h0,h2]
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨small,off⟩,small⟩

theorem fresh_of_single(q:Wire)(off:q∉wires single)
 (f4:(Equiv.swap 4505 4243) q=q)(f5:(Equiv.swap 4506 4244) q=q)(f6:(Equiv.swap 4507 4245) q=q)
 (h0:q≠4243)(h2:q≠4245):q∉wires program:=by
 have a:q∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single q f4 off
 have b:q∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first q f5 a
 have c:q∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second q f6 b
 exact combine_fresh q c h0 h2

theorem low4_free:4505∉wires program:=by
 have a:4505∉wires first:=EqualSourceSwapResearch.retired single 4505 4243 (B95MiddleResearch.fresh _ (by decide))
 have b:4505∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first 4505 (by decide) a
 have c:4505∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second 4505 (by decide) b
 exact combine_fresh 4505 c (by decide) (by decide)

theorem low5_free:4506∉wires program:=by
 have src:4244∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single 4244 (by decide)
  (B95MiddleResearch.fresh _ (by decide))
 have b:4506∉wires second:=EqualSourceSwapResearch.retired first 4506 4244 src
 have c:4506∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second 4506 (by decide) b
 exact combine_fresh 4506 c (by decide) (by decide)

theorem low6_free:4507∉wires program:=by
 have a:4245∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single 4245 (by decide)
  (B95MiddleResearch.fresh _ (by decide))
 have b:4245∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first 4245 (by decide) a
 have c:4507∉wires aliased:=EqualSourceSwapResearch.retired second 4507 4245 b
 exact combine_fresh 4507 c (by decide) (by decide)

theorem ghost_free(q:Wire)(hq:q∈([4757,4758,4759]:List Wire)):q∉wires program:=by
 have p:q∈([4757,4758,4759,4243,4244,4245]:List Wire):=by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢;itauto
 have off:q∉wires single:=B95MiddleResearch.fresh q p
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>
  exact fresh_of_single _ off (by decide) (by decide) (by decide) (by decide) (by decide)

theorem counts:toffoliCount program=toffoliCount original ∧ measurementCount program=measurementCount original ∧
 Challenge.gateSlots program+7=Challenge.gateSlots original:=by
 have old:toffoliCount single=toffoliCount original ∧ measurementCount single=measurementCount original ∧
  Challenge.gateSlots single+9=Challenge.gateSlots original:=B95MiddleResearch.counts
 have pp:toffoliCount prep=0 ∧ measurementCount prep=0 ∧ Challenge.gateSlots prep=1:=by decide +kernel
 simp only [program,aliased,second,first,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
  (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots,pp.1,pp.2.1,pp.2.2]
 exact ⟨by omega,by omega,by omega⟩

theorem physical:GatePhysical program:=by
 have pp:GatePhysical prep:=by simp [GatePhysical,prep,RecordedQuantum.PhysicalInstr,ProperGate]
 have a:GatePhysical first:=gatePhysical_rename _ (Equiv.swap 4505 4243).injective single B95MiddleResearch.physical
 have b:GatePhysical second:=gatePhysical_rename _ (Equiv.swap 4506 4244).injective first a
 have c:GatePhysical aliased:=gatePhysical_rename _ (Equiv.swap 4507 4245).injective second b
 simp only [program,gatePhysical_append]
 exact ⟨⟨pp,c⟩,pp⟩



end ECDSAAdd.Entrant.B95AliasesResearch

end

-- Verified B95 optimization component B95Geometry
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95Research
open ReorderedBPrefixResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

def hosts:List Wire:=ReorderedBSupportResearch.hosts++[4757,4758,4759,4505,4506,4507]
def ports:List Wire:=[4757,4760,4759,4762,4758,4244,4506,4505,4243,4507,4245]

theorem geometry:hosts.Nodup ∧ hosts.length=95 ∧
 (∀q∈hosts,q∉cin::(src++(acc.take 138).drop 10++bank.take 127)):=by decide +kernel

theorem old_away:∀q∈ReorderedBSupportResearch.hosts,q∉ports:=by decide +kernel

theorem fix(q a b:Wire)(ha:q≠a)(hb:q≠b):(Equiv.swap a b) q=q:=by
 simp [Equiv.swap_apply_def,ha,hb]

theorem old_fresh(q:Wire)(hq:q∈ReorderedBSupportResearch.hosts):q∉wires B95AliasesResearch.program:=by
 have away:q∉ports:=old_away q hq
 have ne(a:Wire)(ha:a∈ports):q≠a:=by intro eq;subst q;exact away ha
 have s:q∉wires B95AliasesResearch.single:=B95MiddleResearch.fresh_of_old q
  (ReorderedBMiddlePatchesResearch.fresh q hq)
  (fix q 4757 4760 (ne _ (by decide)) (ne _ (by decide))) (ne _ (by decide))
 exact B95AliasesResearch.fresh_of_single q s
  (fix q 4505 4243 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4506 4244 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4507 4245 (ne _ (by decide)) (ne _ (by decide)))
  (ne _ (by decide)) (ne _ (by decide))

theorem middle_fresh(q:Wire)(hq:q∈hosts):q∉wires B95AliasesResearch.program:=by
 rcases List.mem_append.mp hq with hq|hq
 · exact old_fresh q hq
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
   · exact B95AliasesResearch.ghost_free _ (by decide)
   · exact B95AliasesResearch.ghost_free _ (by decide)
   · exact B95AliasesResearch.ghost_free _ (by decide)
   · exact B95AliasesResearch.low4_free
   · exact B95AliasesResearch.low5_free
   · exact B95AliasesResearch.low6_free

end ECDSAAdd.Entrant.B95Research

end

-- Verified ABC18 optimization component ClearContext
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ClearContextResearch
open InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem suffix(P C T:Program)(mc:measurementCount C=0)(u v:State)(m:List Bool)
 (eq:run (P++C) m u=run P m v):
 run (P++C++T) m u=run (P++T) m v:=by
 conv_lhs=>rw [run_cat]
 rw [eq]
 conv_rhs=>rw [run_cat]
 simp only [measurementCount_append,mc,Nat.add_zero]

theorem middle_context(F M G N J K:Program)(s:State)(m:List Bool)
 (eq:run J (m.drop (measurementCount F+measurementCount M)) (middleState F M s m)=
  run K (m.drop (measurementCount G+measurementCount N)) (middleState G N s m)):
 run (F++M++J) m s=run (G++N++K) m s:=by
 rw [run_three,run_three]
 exact eq

end ECDSAAdd.Entrant.ClearContextResearch

end

-- Verified ABC18 optimization component AppendContext
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ClearContextResearch
open ControlledBorrowResearch
set_option autoImplicit false

attribute [local irreducible] ECDSAAdd.run

theorem append_at(P Q R:Program)(s:State)(m:List Bool)
 (mc:measurementCount P=measurementCount Q)(eq:run P m s=run Q m s):
 run (P++R) m s=run (Q++R) m s:=by
 rw [run_cat,run_cat,mc,eq]



end ECDSAAdd.Entrant.ClearContextResearch

end

-- Verified ABC18 optimization component ProjectedContext
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ClearContextResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
attribute [local irreducible] ECDSAAdd.run

theorem projected(F M G N J K:Program)(E:State→State)(s:State)(m:List Bool)
 (cf:measurementCount F=measurementCount G)(cm:measurementCount M=measurementCount N)
 (mid:middleState F M s m=E (middleState G N s m))
 (suffix:run J (m.drop (measurementCount G+measurementCount N)) (E (middleState G N s m))=
  run K (m.drop (measurementCount G+measurementCount N)) (middleState G N s m)):
 run (F++M++J) m s=run (G++N++K) m s:=by
 apply middle_context
 rw [cf,cm,mid]
 exact suffix
end ECDSAAdd.Entrant.ClearContextResearch

end

-- Verified ABC18 optimization component CacheFromCleanForward
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CacheFromCleanForwardResearch
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run

theorem equivalent(F newF M I newI:Program)(hs:List Wire)(vs:List Bool)
 (sameM:measurementCount newF=measurementCount F)
 (offM:∀w∈hs,w∉wires M)(offI:∀w∈hs,w∉wires I)
 (nd:hs.Nodup)(s:State)(tape:List Bool)
 (zeroF:∀w∈hs,(run F (tape.take (measurementCount F)) s).basis w=false)
 (forward:run newF (tape.take (measurementCount F)) s=
  scatterState hs vs (run F (tape.take (measurementCount F)) s))
 (inverse:run newI (tape.drop (measurementCount F+measurementCount M)) (scatterState hs vs (middleState F M s tape))=
  scatterState hs (List.replicate hs.length false)
   (run I (tape.drop (measurementCount F+measurementCount M)) (scatterState hs vs (middleState F M s tape)))):
 run (newF++M++newI) tape s=run (F++M++I) tape s:=by
 let last:=run I (tape.drop (measurementCount F+measurementCount M)) (middleState F M s tape)
 have lastZero:∀w∈hs,last.basis w=false:=by
  intro w hw
  dsimp only [last,middleState]
  rw [run_preserves_outside I _ _ w (offI w hw),run_preserves_outside M _ _ w (offM w hw)]
  exact zeroF w hw
 simp only [run_three,sameM]
 rw [forward,run_scatter M hs vs _ _ offM]
 change run newI (tape.drop (measurementCount F+measurementCount M)) (scatterState hs vs (middleState F M s tape))=last
 rw [inverse,run_scatter I hs vs _ _ offI]
 exact scatter_clear_overlay hs vs last nd lastZero

end ECDSAAdd.Entrant.CacheFromCleanForwardResearch

end

-- Verified ABC18 optimization component CacheBetweenFrame
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CacheBetweenFrameResearch
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop MixedLiteralAdderDevelop
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run

theorem forward(head post:Program)(k:Nat)(xs ys cs hs:List Wire)(cin:Wire)
 (hx:k+6≤xs.length)(hy:k+6≤ys.length)(hc:k+4≤cs.length)
 (nd:hs.Nodup)(fresh:∀h∈hs,h∉cs)
 (off:∀h∈hs,h∉wires (mappedAdd (mappedRead xs false) ys cs cin))
 (postOff:∀h∈hs,h∉wires post)(s:State)(m:List Bool)
 (zero:∀h∈hs,(run head (m.take (measurementCount head)) s).basis h=false):
 run (head++ReorderedGenericCache.cachedAdd k xs ys cs hs cin++post) m s=
 scatterState hs (((cs.drop 4).take k).map
  (run (carryPrefix (4+k) xs ys cs cin) []
   (run head (m.take (measurementCount head)) s)).basis)
  (run (head++mappedAdd (mappedRead xs false) ys cs cin++post) m s):=by
 have same:= (ReorderedGenericCache.count_balance k xs ys cs hs cin hx hy hc).2.1
 let t:=run head (m.take (measurementCount head)) s
 let r:=(m.drop (measurementCount head)).take (measurementCount (mappedAdd (mappedRead xs false) ys cs cin))
 have eq:=ReorderedGenericCache.cachedAdd_frame k xs ys cs hs cin hx hy hc nd fresh off t r zero
 simp only [run_three,same]
 rw [eq,run_scatter post hs _ _ _ postOff]

end ECDSAAdd.Entrant.CacheBetweenFrameResearch

end

-- Verified ABC18 optimization component ReorderedHeadArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ReorderedHeadArithmeticResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem ready(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0):
 let t:=run (ReorderedAHead.head acc Z bank cin src) m s
 (∀q∈bank.take 127,t.basis q=false) ∧ t.basis cin=false ∧
 regValue src t.basis=regValue src s.basis ∧
 regValue ((acc.take 138).drop 10) t.basis=((2^138-48*regValue src s.basis)%2^138)/1024:=by
 let H:=regValue src s.basis
 let t:=run (ReorderedAHead.head acc Z bank cin src) m s
 have frame:=ReorderedAHead.head_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have hf10:=hf _ (A161NarrowAcc.terms_mem src).2.1
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;>omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=frame.2.2 q (away q hq)
 have len:(acc.take 138).length=138:=by simp [hacc]
 have pref:=regValue_take_drop_of_lt acc 138 ((2^138-48*H)%2^138) t.basis
  (by omega) frame.2.1 (Nat.mod_lt _ (by positivity))
 refine ⟨?_,?_,?_,?_⟩
 · intro q hq
   exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 · exact (same cin (Or.inr rfl)).trans hi
 · exact regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 · rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
   rfl

end ECDSAAdd.Entrant.ReorderedHeadArithmeticResearch

end

-- Verified ABC18 optimization component ReorderedPreInverseArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ReorderedPreInverseArithmeticResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem ready(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=161)(hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=4294968272*regValue src s.basis):
 let t:=run (A161Carry.unbuildPre acc Z bank cin src) m s
 (∀q∈bank.take 127,t.basis q=false) ∧ t.basis cin=false ∧
 regValue src t.basis=regValue src s.basis ∧
 regValue ((acc.take 138).drop 10) t.basis=976*regValue src s.basis/1024:=by
 let H:=regValue src s.basis
 let t:=run (A161Carry.unbuildPre acc Z bank cin src) m s
 have frame:=A161Carry.unbuildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have hf10:=hf _ (A161NarrowAcc.terms_mem src).2.1
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;>omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=frame.2.2 q (away q hq)
 have len:(acc.take 138).length=138:=by simp [hacc]
 have hH:H<2^128:=by simpa only [H,hsrc] using regValue_lt src s.basis
 have pref:=regValue_take_drop_of_lt acc 138 (976*H) t.basis
  (by omega) frame.2.1 (by norm_num at hH ⊢;omega)
 refine ⟨?_,?_,?_,?_⟩
 · intro q hq
   exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 · exact (same cin (Or.inr rfl)).trans hi
 · exact regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 · rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
   rfl

end ECDSAAdd.Entrant.ReorderedPreInverseArithmeticResearch

end

-- Verified ABC18 optimization component BRelocatedReady (plain)
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BRelocatedReadyResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ReorderedBPrefixResearch
 ReorderedBRetapeResearch InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem plain_before(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)
 (ha:regValue acc s.basis=0):
 WReady acc pad bank L.core.cin src (regValue src s.basis)
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s):=
 Ghost3CacheA.plain_ready s m hz hb hi ha


end ECDSAAdd.Entrant.BRelocatedReadyResearch

end

-- Verified ABC18 optimization component ACFiniteWindow
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ACFiniteWindowResearch
open MeasuredCodec5
set_option autoImplicit false

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def original:Program:=[.CCX 0 1 5,.CCX 4 5 6,.CX 6 7,
 .measureX 6 [] [.CZ 4 5],.CX 5 4,.measureX 5 [] [.CZ 0 1]]
def exchange:Program:=[.CX 7 8,.CX 8 7,.CX 7 8]
def reference:Program:=original++exchange
def fast:Program:=[.CCX 0 1 5,.CCX 4 5 8,.CX 5 4,
 .measureX 5 [] [.CZ 0 1],.measureX 5 [] []]

theorem finite:∀x:Fin 32,safe fast x.val=true ∧ safe reference x.val=true ∧
 bitRun fast x.val=bitRun reference x.val:=by decide +kernel

theorem modeled(x:Nat)(hx:x<32)(m:List Bool)(ph:Bool):
 run fast m ⟨ph,bitsOf x⟩=run reference m ⟨ph,bitsOf x⟩:=by
 have h:=finite ⟨x,hx⟩
 rw [run_sim,run_sim,sim_safe fast x h.1 m ph,sim_safe reference x h.2.1 m ph,h.2.2]

theorem counts:toffoliCount fast=toffoliCount original ∧ measurementCount fast=measurementCount original ∧
 Challenge.gateSlots fast+2=Challenge.gateSlots original:=by decide +kernel



end ECDSAAdd.Entrant.ACFiniteWindowResearch

end

-- Verified ABC18 optimization component ACLocalWindow
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ACFiniteWindowResearch
open MeasuredCodec5
set_option autoImplicit false

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem pack5_lt:∀b0 b1 b2 b3 b4:Bool,
 pack10 b0 b1 b2 b3 b4 false false false false false<32:=by decide +kernel

theorem local_word9(s:State)(hc:s.basis 5=false ∧ s.basis 6=false ∧ s.basis 7=false ∧ s.basis 8=false):
 ∃x,x<32 ∧ ∀q∈Finset.range 9,s.basis q=bitsOf x q:=by
 let x:=pack10 (s.basis 0) (s.basis 1) (s.basis 2) (s.basis 3) (s.basis 4) false false false false false
 refine ⟨x,pack5_lt _ _ _ _ _,?_⟩
 intro q hq
 have hi:q<10:=by have h:=Finset.mem_range.mp hq;omega
 change s.basis q=x.testBit q
 rw [show x=pack10 (s.basis 0) (s.basis 1) (s.basis 2) (s.basis 3) (s.basis 4) false false false false false from rfl,
  pack10_bits _ _ _ _ _ _ _ _ _ _ q hi]
 have hq':q<9:=Finset.mem_range.mp hq
 interval_cases q <;>simp [raw,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem support:wires fast⊆Finset.range 9 ∧ wires reference⊆Finset.range 9:=by decide +kernel

theorem run_eq(s:State)(m:List Bool)
 (hc:s.basis 5=false ∧ s.basis 6=false ∧ s.basis 7=false ∧ s.basis 8=false):
 run fast m s=run reference m s:=by
 obtain ⟨x,hx,hb⟩:=local_word9 s hc
 have eq:=modeled x hx m s.phase
 have a:=pool_run_agrees fast (Finset.range 9) support.1 m s ⟨s.phase,bitsOf x⟩ rfl hb
 have b:=pool_run_agrees reference (Finset.range 9) support.2 m s ⟨s.phase,bitsOf x⟩ rfl hb
 apply State.extensionality
 · exact a.1.trans ((congrArg State.phase eq).trans b.1.symm)
 · funext q
   by_cases hq:q∈Finset.range 9
   · exact (a.2 q hq).trans ((congrArg (fun t:State=>t.basis q) eq).trans (b.2 q hq).symm)
   · exact (run_preserves_outside fast m s q (fun h=>hq (support.1 h))).trans
      (run_preserves_outside reference m s q (fun h=>hq (support.2 h))).symm

end ECDSAAdd.Entrant.ACFiniteWindowResearch

end

-- Verified ABC18 optimization component ACPlacedWindow
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ACPlacedWindowResearch
open ACFiniteWindowResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def label (f : Fin 12→Wire) (q : Wire) : Wire := if h:q<12 then f ⟨q,h⟩ else q

theorem label_inj (f : Fin 12→Wire) (hf : Function.Injective f) :
 ∀a∈Finset.range 12,∀b∈Finset.range 12,label f a=label f b → a=b := by
 intro a ha b hb e
 have ha':=Finset.mem_range.mp ha
 have hb':=Finset.mem_range.mp hb
 have he : f ⟨a,ha'⟩=f ⟨b,hb'⟩:=by simpa only [label,dif_pos ha',dif_pos hb'] using e
 exact congrArg Fin.val (hf he)

def fastAt(f:Fin 12→Wire):Program:=renameProgram (label f) fast
def originalAt(f:Fin 12→Wire):Program:=renameProgram (label f) reference

theorem run_eq(f:Fin 12→Wire)(hf:Function.Injective f)(s:State)(m:List Bool)
 (hc:s.basis (f 5)=false ∧ s.basis (f 6)=false ∧ s.basis (f 7)=false ∧ s.basis (f 8)=false):
 run (fastAt f) m s=run (originalAt f) m s:=by
 let t:State:=⟨s.phase,fun q=>s.basis (label f q)⟩
 have ht:t.basis 5=false ∧ t.basis 6=false ∧ t.basis 7=false ∧ t.basis 8=false:=hc
 have eq:=ACFiniteWindowResearch.run_eq t m ht
 have a:=run_rename_pool (label f) (Finset.range 9) (fun a ha b hb=>label_inj f hf a (Finset.mem_range.mpr (by have h:=Finset.mem_range.mp ha;omega)) b (Finset.mem_range.mpr (by have h:=Finset.mem_range.mp hb;omega))) fast support.1 m t s rfl (fun _ _=>rfl)
 have b:=run_rename_pool (label f) (Finset.range 9) (fun a ha b hb=>label_inj f hf a (Finset.mem_range.mpr (by have h:=Finset.mem_range.mp ha;omega)) b (Finset.mem_range.mpr (by have h:=Finset.mem_range.mp hb;omega))) reference support.2 m t s rfl (fun _ _=>rfl)
 have sa:wires (fastAt f)⊆(Finset.range 9).image (label f):=by
  rw [fastAt,renameProgram_support]
  exact Finset.image_mono (label f) support.1
 have sb:wires (originalAt f)⊆(Finset.range 9).image (label f):=by
  rw [originalAt,renameProgram_support]
  exact Finset.image_mono (label f) support.2
 apply State.extensionality
 · exact a.1.trans ((congrArg State.phase eq).trans b.1.symm)
 · funext q
   by_cases hq:q∈(Finset.range 9).image (label f)
   · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hq
     exact (a.2 i hi).trans ((congrArg (fun z:State=>z.basis i) eq).trans (b.2 i hi).symm)
   · have ea:=run_preserves_outside (fastAt f) m s q (fun h=>hq (sa h))
     have eb:=run_preserves_outside (originalAt f) m s q (fun h=>hq (sb h))
     exact ea.trans eb.symm


end ECDSAAdd.Entrant.ACPlacedWindowResearch

end

-- Verified ABC18 optimization component RelocateMembership
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.RelocateMembershipResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem embedded(P A B:Program)(f:Wire→Wire)(q:Wire)(fixed:f q=q)
 (hq:q∈wires P):q∈wires (A++renameProgram f P++B):=by
 rw [wires_append,wires_append,renameProgram_support]
 exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q,hq,fixed⟩))

theorem copy(q a b:Wire)(P:Program)(x:Wire)(fixed:(Equiv.swap q a) x=x)
 (hx:x∈wires P):x∈wires (ClearCopyBorrow.program q a b P):=
 embedded P _ _ _ x fixed hx

theorem xor(q a b c:Wire)(P:Program)(x:Wire)(fixed:(Equiv.swap q a) x=x)
 (hx:x∈wires P):x∈wires (ClearXorBorrow.program q a b c P):=
 embedded P _ _ _ x fixed hx

theorem kept(w:Fin 9→Wire)(P:Program)(q:Wire)(away:∀i,q≠w i)
 (hq:q∈wires P):q∈wires (RelocateThreeGhosts.program w P):=by
 have fix(i j:Fin 9):(Equiv.swap (w i) (w j)) q=q:=by
  simp [Equiv.swap_apply_def,away i,away j]
 apply xor _ _ _ _ _ q (fix 2 5)
 apply copy _ _ _ _ q (fix 1 4)
 exact copy _ _ _ _ q (fix 0 3) hq

end ECDSAAdd.Entrant.RelocateMembershipResearch

end

-- Verified ABC18 optimization component BodySupportContext
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.BodySupportContextResearch
set_option autoImplicit false
attribute [local irreducible] ECDSAAdd.wires
 theorem replace1(A P Q D:Program)(h:wires Q⊆wires ((A++P)++D)):
 wires ((A++Q)++D)⊆wires ((A++P)++D):=by
 simp only [wires_append] at h ⊢
 exact Finset.union_subset (Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) h)
  Finset.subset_union_right
 theorem replace2(A B P Q D:Program)(h:wires Q⊆wires ((A++(B++P))++D)):
 wires ((A++(B++Q))++D)⊆wires ((A++(B++P))++D):=by
 simp only [wires_append] at h ⊢
 have a:wires A⊆(wires A∪(wires B∪wires P))∪wires D:=
  Finset.subset_union_left.trans Finset.subset_union_left
 have b:wires B⊆(wires A∪(wires B∪wires P))∪wires D:=
  Finset.subset_union_left.trans (Finset.subset_union_right.trans Finset.subset_union_left)
 exact Finset.union_subset (Finset.union_subset a (Finset.union_subset b h)) Finset.subset_union_right
end ECDSAAdd.Entrant.BodySupportContextResearch

end

-- Verified ABC18 optimization component AShortGhostFacts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AShortGhostFactsResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
abbrev p:Program:=KnownAMidStaged.body
def a:Program:=p.take 1448
def b:Program:=(p.drop 1448).take 6
def c:Program:=(p.drop 1454).take 2164
def d:Program:=(p.drop 3618).take 7
def e:Program:=(p.drop 3625).take 2305
def f:Program:=(p.drop 5930).take 10
def g:Program:=p.drop 5940

theorem checked:
 PairedWritesResearch.check 4760 (p.take 1448) none=some none ∧
 PairedWritesResearch.check 4760 (p.take 3618) none=some none ∧
 PairedWritesResearch.check 4760 (p.take 5930) none=some none ∧
 PairedWritesResearch.check 4762 (p.take 1448) none=some none ∧
 PairedWritesResearch.check 4757 (p.take 1448) none=some none ∧
 PairedWritesResearch.check 4759 (p.take 1448) none=some none ∧
 ZeroAfterWriteResearch.check 4757 (p.take 3618) false=true ∧
 ZeroAfterWriteResearch.check 4757 (p.take 5930) false=true ∧
 ZeroAfterWriteResearch.check 4757 b false=true ∧
 ZeroAfterWriteResearch.check 4759 b false=true ∧
 ZeroAfterWriteResearch.check 4757 d false=true ∧
 ZeroAfterWriteResearch.check 4757 f false=true ∧
 C163Touch.touched b 4760=false ∧ C163Touch.touched b 4762=false ∧
 C163Touch.touched d 4760=false ∧ C163Touch.touched f 4760=false ∧
 5940≤p.length:=by decide +kernel

end ECDSAAdd.Entrant.AShortGhostFactsResearch

end

-- Verified ABC18 optimization component AShortGhostPrograms
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AShortGhostProgramsResearch
open AShortGhostFactsResearch
abbrev old:Program:=AShortGhostFactsResearch.p
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def b0:Program:=renameProgram (Equiv.swap 4757 4760) b
def b02:Program:=renameProgram (Equiv.swap 4759 4762) b0
def d0:Program:=renameProgram (Equiv.swap 4757 4760) d
def f0:Program:=renameProgram (Equiv.swap 4757 4760) f
def program:Program:=a++b02++c++d0++e++f0++g

theorem partition(P:Program):P=P.take 1448++(P.drop 1448).take 6++
 (P.drop 1454).take 2164++(P.drop 3618).take 7++(P.drop 3625).take 2305++
 (P.drop 5930).take 10++P.drop 5940:=by
 let r1:=P.drop 1448
 let r2:=r1.drop 6
 let r3:=r2.drop 2164
 let r4:=r3.drop 7
 let r5:=r4.drop 2305
 let r6:=r5.drop 10
 have h:P=P.take 1448++r1.take 6++r2.take 2164++r3.take 7++r4.take 2305++r5.take 10++r6:=by
  dsimp [r1,r2,r3,r4,r5,r6]
  simp only [List.append_assoc,List.take_append_drop]
 simpa only [r1,r2,r3,r4,r5,r6,List.drop_drop,Nat.reduceAdd] using h

theorem old_shape:old=a++b++c++d++e++f++g:=partition old

theorem prefixD:a++b++c=old.take 3618:=by
 change (old.take 1448++(old.drop 1448).take 6)++(old.drop 1454).take 2164=_
 rw [←List.take_add (l:=old) (i:=1448) (j:=6)]
 exact (List.take_add (l:=old) (i:=1454) (j:=2164)).symm

theorem prefixF:a++b++c++d++e=old.take 5930:=by
 rw [prefixD]
 change (old.take 3618++(old.drop 3618).take 7)++(old.drop 3625).take 2305=_
 rw [←List.take_add (l:=old) (i:=3618) (j:=7)]
 exact (List.take_add (l:=old) (i:=3625) (j:=2305)).symm

theorem not_wire(P:Program)(q:Nat)(h:C163Touch.touched P q=false):q∉wires P:=by
 intro bad
 have eq: C163Touch.touched P q=true:=(C163Touch.touched_spec _ _).mpr bad
 rw [h] at eq
 cases eq

theorem fresh_fixed(f:Wire→Wire)(inj:Function.Injective f)(P:Program)(q:Wire)
 (fix:f q=q)(fresh:q∉wires P):q∉wires (renameProgram f P):=by
 rw [renameProgram_support]
 intro bad
 obtain ⟨w,hw,he⟩:=Finset.mem_image.mp bad
 have eq:w=q:=inj (he.trans fix.symm)
 exact fresh (eq ▸ hw)

















theorem d0_eq(s:State)(m:List Bool)(h0:s.basis 4757=false)(hc:s.basis 4760=false):
 run d0 m s=run d m s:=by
 rcases checked with ⟨_,_,_,_,_,_,_,_,_,_,qd,_,_,_,fd,_,_⟩
 exact EqualSourceSwapResearch.rename_swap_equal_eq d 4757 4760 (not_wire d 4760 fd) s m
  (h0.trans hc.symm) ((ZeroAfterWriteResearch.erased 4757 d qd s m).trans h0.symm)

theorem f0_eq(s:State)(m:List Bool)(h0:s.basis 4757=false)(hc:s.basis 4760=false):
 run f0 m s=run f m s:=by
 rcases checked with ⟨_,_,_,_,_,_,_,_,_,_,_,qf,_,_,_,ff,_⟩
 exact EqualSourceSwapResearch.rename_swap_equal_eq f 4757 4760 (not_wire f 4760 ff) s m
  (h0.trans hc.symm) ((ZeroAfterWriteResearch.erased 4757 f qf s m).trans h0.symm)



end ECDSAAdd.Entrant.AShortGhostProgramsResearch

end

-- Verified ABC18 optimization component AQ0Base
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AQ0BaseResearch
open AShortGhostFactsResearch AShortGhostProgramsResearch InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def program:Program:=a++b0++c++d0++e++f0++g

theorem b0_eq(s:State)(m:List Bool)(h0:s.basis 4757=false)(hc:s.basis 4760=false):
 run b0 m s=run b m s:=by
 rcases checked with ⟨_,_,_,_,_,_,_,_,qb,_,_,_,fb,_,_,_,_⟩
 exact EqualSourceSwapResearch.rename_swap_equal_eq b 4757 4760 (not_wire b 4760 fb) s m
  (h0.trans hc.symm) ((ZeroAfterWriteResearch.erased 4757 b qb s m).trans h0.symm)

theorem context_eq(pre P Q post:Program)(s:State)(m:List Bool)
 (hm:measurementCount P=measurementCount Q)
 (he:∀r,run P r (run pre (m.take (measurementCount pre)) s)=
  run Q r (run pre (m.take (measurementCount pre)) s)):
 run (pre++P++post) m s=run (pre++Q++post) m s:=by
 apply BPatchedLoopResearch.run_middle_congr pre P Q post s m hm
 unfold middleState
 rw [hm]
 exact he _

theorem equivalent(s:State)(m:List Bool)(q0:s.basis 4757=false)
 (cin:s.basis 4760=false):run program m s=run old m s:=by
 rcases checked with ⟨ciA,ciD,ciF,flA,qoA,qtA,qoD,qoF,_,_,_,_,_,_,_,_,_⟩
 have mb:measurementCount b=measurementCount b0:=by
  simp only [b0,b0,(renameProgram_counts _ _).2]
 have md:measurementCount d=measurementCount d0:=by
  simp only [d0,(renameProgram_counts _ _).2]
 have mf:measurementCount f=measurementCount f0:=by
  simp only [f0,(renameProgram_counts _ _).2]
 have paQ:(run a (m.take (measurementCount a)) s).basis 4757=false:=
  (PairedWritesResearch.preserved 4757 a qoA s _).trans q0
 have paC:(run a (m.take (measurementCount a)) s).basis 4760=false:=
  (PairedWritesResearch.preserved 4760 a ciA s _).trans cin
 have hb:∀r,run b r (run a (m.take (measurementCount a)) s)=run b0 r (run a (m.take (measurementCount a)) s):=fun r=>(b0_eq (run a (m.take (measurementCount a)) s) r paQ paC).symm
 have pdQ:(run (a++b++c) (m.take (measurementCount (a++b++c))) s).basis 4757=false:=by
  rw [prefixD]
  exact ZeroAfterWriteResearch.erased 4757 (old.take 3618) qoD s _
 have pdC:(run (a++b++c) (m.take (measurementCount (a++b++c))) s).basis 4760=false:=by
  rw [prefixD]
  exact (PairedWritesResearch.preserved 4760 (old.take 3618) ciD s _).trans cin
 have hd:∀r,run d r (run (a++b++c) (m.take (measurementCount (a++b++c))) s)=run d0 r (run (a++b++c) (m.take (measurementCount (a++b++c))) s):=fun r=>(d0_eq (run (a++b++c) (m.take (measurementCount (a++b++c))) s) r pdQ pdC).symm
 have pfQ:(run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s).basis 4757=false:=by
  rw [prefixF]
  exact ZeroAfterWriteResearch.erased 4757 (old.take 5930) qoF s _
 have pfC:(run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s).basis 4760=false:=by
  rw [prefixF]
  exact (PairedWritesResearch.preserved 4760 (old.take 5930) ciF s _).trans cin
 have hf:∀r,run f r (run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s)=run f0 r (run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s):=fun r=>(f0_eq (run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s) r pfQ pfC).symm
 have ef:=context_eq (a++b++c++d++e) f f0 g s m mf hf
 have ed:=context_eq (a++b++c) d d0 (e++f0++g) s m md hd
 have eb:=context_eq a b b0 (c++d0++e++f0++g) s m mb hb
 have shape:old=(a++b++c++d++e)++f++g:=old_shape
 calc
  run program m s=run (a++b0++(c++d0++e++f0++g)) m s:=by
   simp only [program,List.append_assoc]
  _=run (a++b++(c++d0++e++f0++g)) m s:=eb.symm
  _=run ((a++b++c)++d0++(e++f0++g)) m s:=by simp only [List.append_assoc]
  _=run ((a++b++c)++d++(e++f0++g)) m s:=ed.symm
  _=run ((a++b++c++d++e)++f0++g) m s:=by simp only [List.append_assoc]
  _=run ((a++b++c++d++e)++f++g) m s:=ef.symm
  _=run old m s:=by rw [←shape]

end ECDSAAdd.Entrant.AQ0BaseResearch

end

-- Verified ABC18 optimization component ARetimeFacts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ARetimeFactsResearch
open AShortGhostFactsResearch AShortGhostProgramsResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
abbrev old:Program:=KnownAMidStaged.body
def ports:Fin 12→Wire:=![256,4889,4627,4628,257,4760,4759,4758,4762,0,1,2]
def oldWindow:Program:=renameProgram (ACPlacedWindowResearch.label ports) ACFiniteWindowResearch.original
def fastWindow:Program:=ACPlacedWindowResearch.fastAt ports
def gap:Program:=(old.drop 1454).take 666
def center:Program:=(old.drop 2121).take 1497++d0++(old.drop 3625).take 758
def suffix:Program:=(old.drop 4385).take 1545++f0++g

theorem ports_inj:Function.Injective ports:=by decide +kernel

theorem checked:
 b0=oldWindow ∧
 (old.drop 2120).take 1=[.CX 4758 4762] ∧
 (old.drop 4383).take 2=[.CX 4762 4758,.X 4758] ∧
 PairedWritesResearch.check 4758 a none=some none ∧
 C163Touch.touched gap 4758=false ∧ C163Touch.touched gap 4762=false ∧
 C163Touch.touched center 4758=false ∧ C163Touch.touched suffix 4758=false ∧
 ([a,fastWindow,gap,center,suffix]:List Program).all (fun P=>
  ([4757,4758,4759,4243,4244,4245]:List Wire).all (fun q=>!C163Touch.touched P q))=true:=by decide +kernel

end ECDSAAdd.Entrant.ARetimeFactsResearch

end

-- Verified ABC18 optimization component ListAWindowParts
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ListAWindowPartsResearch
set_option autoImplicit false

set_option maxRecDepth 10000

theorem split3(P:Program)(a b:Nat):P=P.take a++(P.drop a).take b++P.drop (a+b):=by
 calc
  P=P.take a++P.drop a:=(List.take_append_drop a P).symm
  _=P.take a++((P.drop a).take b++(P.drop a).drop b):=
   congrArg (fun t=>P.take a++t) (List.take_append_drop b (P.drop a)).symm
  _=P.take a++(P.drop a).take b++P.drop (a+b):=by simp only [List.append_assoc,List.drop_drop]

theorem c_template(P:Program):(P.drop 1454).take 2164=
 (P.drop 1454).take 666++(P.drop 2120).take 1++(P.drop 2121).take 1497:=by
 simpa only [List.take_take,List.drop_take,List.drop_drop] using split3 ((P.drop 1454).take 2164) 666 1

theorem e_template(P:Program):(P.drop 3625).take 2305=
 (P.drop 3625).take 758++(P.drop 4383).take 2++(P.drop 4385).take 1545:=by
 simpa only [List.take_take,List.drop_take,List.drop_drop] using split3 ((P.drop 3625).take 2305) 758 2
end ECDSAAdd.Entrant.ListAWindowPartsResearch

end

-- Verified ABC18 optimization component ARetimeParts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ARetimeFactsResearch
open AShortGhostFactsResearch AShortGhostProgramsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem c_split:c=gap++copy 4758 4762++(old.drop 2121).take 1497:=by
 have h:=ListAWindowPartsResearch.c_template old
 have eq:=congrArg (fun P:Program=>(old.drop 1454).take 666++P++(old.drop 2121).take 1497) checked.2.1
 exact h.trans eq

theorem e_split:e=(old.drop 3625).take 758++cleanup 4758 4762++(old.drop 4385).take 1545:=by
 have h:=ListAWindowPartsResearch.e_template old
 have eq:=congrArg (fun P:Program=>(old.drop 3625).take 758++P++(old.drop 4385).take 1545) checked.2.2.1
 exact h.trans eq

theorem old_shape:AQ0BaseResearch.program=a++b0++(gap++copy 4758 4762++center++cleanup 4758 4762++suffix):=by
 simp only [AQ0BaseResearch.program,c_split,e_split,center,suffix,List.append_assoc]

theorem gap_fresh:4758∉wires gap ∧ 4762∉wires gap:=
 ⟨not_wire _ _ checked.2.2.2.2.1,not_wire _ _ checked.2.2.2.2.2.1⟩

theorem center_fresh:4758∉wires center:=not_wire _ _ checked.2.2.2.2.2.2.1

theorem suffix_fresh:4758∉wires suffix:=not_wire _ _ checked.2.2.2.2.2.2.2.1

end ECDSAAdd.Entrant.ARetimeFactsResearch

end

-- Verified ABC18 optimization component AWindowFrame
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.ARetimeFactsResearch
open AShortGhostFactsResearch AShortGhostProgramsResearch B95RetimeResearch ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem reference_shape:ACPlacedWindowResearch.originalAt ports=oldWindow++exchange 4758 4762:=by decide +kernel

theorem window_measurements:measurementCount fastWindow=measurementCount b0:=by
 have n:measurementCount fastWindow=measurementCount ACFiniteWindowResearch.fast:=
  (renameProgram_counts _ _).2
 have o:measurementCount oldWindow=measurementCount ACFiniteWindowResearch.original:=
  (renameProgram_counts _ _).2
 exact (n.trans ACFiniteWindowResearch.counts.2.1).trans
  (o.symm.trans (congrArg measurementCount checked.1.symm))

theorem window_eq(s:State)(m:List Bool)
 (hc:s.basis 4760=false)(h2:s.basis 4759=false)(h1:s.basis 4758=false)(hm:s.basis 4762=false):
 run fastWindow m s=run (exchange 4758 4762) [] (run b0 m s):=by
 have eq:=ACPlacedWindowResearch.run_eq ports ports_inj s m ⟨hc,h2,h1,hm⟩
 have refEq:run (ACPlacedWindowResearch.originalAt ports) m s=
  run (exchange 4758 4762) [] (run oldWindow m s):=by
  rw [reference_shape,run_cat]
  exact zero_records _ (by simp [exchange,measurementCount]) _ _
 exact eq.trans (refEq.trans (congrArg (fun t=>run (exchange 4758 4762) [] t)
  (congrArg (fun P=>run P m s) checked.1.symm)))

end ECDSAAdd.Entrant.ARetimeFactsResearch

end

-- Verified ABC18 optimization component AMiddle
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AMiddleResearch
open AShortGhostFactsResearch AShortGhostProgramsResearch ARetimeFactsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def program:Program:=a++fastWindow++gap++center++suffix

theorem run_erased(s:State)(m:List Bool)
 (q0:s.basis 4757=false)(q1:s.basis 4758=false)(q2:s.basis 4759=false)
 (ci:s.basis 4760=false)(fl:s.basis 4762=false):
 run program m s=erase 4758 (run KnownAMidStaged.body m s):=by
 let t:=run a (m.take (measurementCount a)) s
 rcases AShortGhostFactsResearch.checked with ⟨ciA,_,_,flA,_,q2A,_,_,_,_,_,_,_,fbm,_,_,_⟩
 have tc:t.basis 4760=false:=(PairedWritesResearch.preserved 4760 a ciA s _).trans ci
 have tq1:t.basis 4758=false:=(PairedWritesResearch.preserved 4758 a ARetimeFactsResearch.checked.2.2.2.1 s _).trans q1
 have tq2:t.basis 4759=false:=(PairedWritesResearch.preserved 4759 a q2A s _).trans q2
 have tf:t.basis 4762=false:=(PairedWritesResearch.preserved 4762 a flA s _).trans fl
 have eq:∀r,run fastWindow r t=run (exchange 4758 4762) [] (run b0 r t):=
  fun r=>window_eq t r tc tq2 tq1 tf
 have off:4762∉wires b0:=fresh_fixed (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective b 4762
  (by decide) (not_wire b 4762 fbm)
 have hz:∀r,(run b0 r t).basis 4762=false:=fun r=>(run_preserves_outside b0 r t 4762 off).trans tf
 have h:=window_context a b0 fastWindow gap center suffix 4758 4762 (by decide)
  gap_fresh.1 gap_fresh.2 center_fresh suffix_fresh window_measurements s m eq hz
 have new_shape:program=a++fastWindow++(gap++center++suffix):=by simp only [program,List.append_assoc]
 have one:run program m s=erase 4758 (run AQ0BaseResearch.program m s):=
  (congrArg (fun P=>run P m s) new_shape).trans
   (h.trans (congrArg (fun P=>erase 4758 (run P m s)) ARetimeFactsResearch.old_shape.symm))
 exact one.trans (congrArg (erase 4758) (AQ0BaseResearch.equivalent s m q0 ci))

theorem equivalent(s:State)(m:List Bool)
 (q0:s.basis 4757=false)(q1:s.basis 4758=false)(q2:s.basis 4759=false)
 (ci:s.basis 4760=false)(fl:s.basis 4762=false)
 (out:(run KnownAMidStaged.body m s).basis 4758=false):
 run program m s=run KnownAMidStaged.body m s:=
 (run_erased s m q0 q1 q2 ci fl).trans (erase_eq 4758 _ out)

theorem fresh(q:Wire)(hq:q∈([4757,4758,4759,4243,4244,4245]:List Wire)):
 q∉wires program:=by
 have checked:=ARetimeFactsResearch.checked.2.2.2.2.2.2.2.2
 have off(P:Program)(hp:P∈([a,fastWindow,gap,center,suffix]:List Program)):q∉wires P:=by
  have h:=List.all_eq_true.mp (List.all_eq_true.mp checked P hp) q hq
  intro bad
  have yes:C163Touch.touched P q=true:=(C163Touch.touched_spec _ _).mpr bad
  simp only [yes,Bool.not_true,Bool.false_eq_true] at h
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨⟨⟨off a (by simp),off fastWindow (by simp)⟩,off gap (by simp)⟩,off center (by simp)⟩,off suffix (by simp)⟩


end ECDSAAdd.Entrant.AMiddleResearch

end

-- Verified ABC18 optimization component AReady
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AMiddleResearch
open InverseCarryDevelop
abbrev acc:List Wire:=ReorderedAFixed.acc
abbrev src:List Wire:=ReorderedAFixed.src
abbrev pad:List Wire:=ReorderedAFixed.pad
abbrev bank:List Wire:=ReorderedAFixed.bank
abbrev cin:Wire:=ReorderedAFixed.L.core.cin
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem acc_length: acc.length=161:=by decide +kernel
theorem source_length: src.length=128:=by decide +kernel

theorem maps:acc.getD 0 0=4757 ∧ acc.getD 1 0=4758 ∧ acc.getD 2 0=4759:=by decide +kernel

theorem ready_eq(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run KnownAMidStaged.body m s))
 (flag:s.basis 4762=false):run program m s=run KnownAMidStaged.body m s:=by
 have zero(i:Nat)(hi:i<3):s.basis (acc.getD i 0)=false:=
  LowWordRecovery.low_register_zero acc s.basis H i (by omega)
   (by have h:=acc_length;omega) before.1
 have out:(run KnownAMidStaged.body m s).basis 4758=false:=by
  have h:=LowWordRecovery.low_register_zero acc (run KnownAMidStaged.body m s).basis H 1 (by decide)
   (by have h:=acc_length;omega) after.1
  simpa only [maps.2.1] using h
 apply equivalent s m
 · simpa only [maps.1] using zero 0 (by decide)
 · simpa only [maps.2.1] using zero 1 (by decide)
 · simpa only [maps.2.2] using zero 2 (by decide)
 · exact before.2.2.2.2
 · exact flag
 · exact out

end ECDSAAdd.Entrant.AMiddleResearch

end

-- Verified ABC18 optimization component AAliases
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AAliasesResearch
open AMiddleResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev original:Program:=KnownAMidStaged.body
abbrev single:Program:=AMiddleResearch.program
def prep:Program:=[.CX 4243 4245]
def first:Program:=renameProgram (Equiv.swap 4505 4243) single
def second:Program:=renameProgram (Equiv.swap 4506 4244) first
def aliased:Program:=renameProgram (Equiv.swap 4507 4245) second
def program:Program:=prep++aliased++prep

theorem equivalent(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run original m s))
 (flag:s.basis 4762=false):run program m s=run original m s:=by
 have eq:run single m s=run original m s:=AMiddleResearch.ready_eq H s m before after flag
 have stable:∀q∈acc,(run single m s).basis q=s.basis q:=by
  apply (regValue_eq_iff acc _ _).mp
  rw [eq]
  exact after.1.trans before.1.symm
 have q4s: (run single m s).basis 4505=s.basis 4505:=stable _ (by decide +kernel)
 have q5s:(run single m s).basis 4506=s.basis 4506:=stable _ (by decide +kernel)
 have q6s: (run single m s).basis 4507=s.basis 4507:=stable _ (by decide +kernel)
 have val:regValue acc s.basis=4294968272*regValue src s.basis:=by rw [before.2.1];exact before.1
 have cp:=LowWordRecovery.copies acc src s.basis (by rw [acc_length];decide) (by rw [source_length];decide) val
 have c4:s.basis 4505=s.basis 4243:=by
  simpa only [show src.getD 0 0=4243 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.1.symm
 have c5:s.basis 4506=s.basis 4244:=by
  simpa only [show src.getD 1 0=4244 from by decide +kernel,
   show acc.getD 5 0=4506 from by decide +kernel] using cp.2.1.symm
 have c6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243):=by
  have low:s.basis 4245=(s.basis 4507 ^^ s.basis 4505):=by
   simpa only [show src.getD 2 0=4245 from by decide +kernel,
    show acc.getD 6 0=4507 from by decide +kernel,
    show acc.getD 4 0=4505 from by decide +kernel] using cp.2.2
  rw [low,←c4]
  simp [Bool.xor_assoc]
 have h0:4243∉wires single:=AMiddleResearch.fresh _ (by decide)
 have h1:4244∉wires single:=AMiddleResearch.fresh _ (by decide)
 have h2:4245∉wires single:=AMiddleResearch.fresh _ (by decide)
 let t:=run prep m s
 have commute:run single m t=run prep m (run single m s):=
  FreshCXResearch.commute single 4243 4245 h0 h2 s m m
 have equal4:t.basis 4505=t.basis 4243:=by simpa [t,prep,run,writeBit] using c4
 have equal5:t.basis 4506=t.basis 4244:=by simpa [t,prep,run,writeBit] using c5
 have equal6:t.basis 4507=t.basis 4245:=by simpa [t,prep,run,writeBit] using c6
 have restore4:(run single m t).basis 4505=t.basis 4505:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q4s
 have restore5:(run single m t).basis 4506=t.basis 4506:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q5s
 have restore6:(run single m t).basis 4507=t.basis 4507:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q6s
 have e4:run first m t=run single m t:=
  EqualSourceSwapResearch.rename_swap_equal_eq single 4505 4243 h0 t m equal4 restore4
 have fresh1:4244∉wires first:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4505 4243)
  (Equiv.swap 4505 4243).injective single 4244 (by decide) h1
 have e5:run second m t=run single m t:=by
  have last:(run first m t).basis 4506=t.basis 4506:=by rw [e4];exact restore5
  exact (EqualSourceSwapResearch.rename_swap_equal_eq first 4506 4244 fresh1 t m equal5 last).trans e4
 have fresh2a:4245∉wires first:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4505 4243)
  (Equiv.swap 4505 4243).injective single 4245 (by decide) h2
 have fresh2:4245∉wires second:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4506 4244)
  (Equiv.swap 4506 4244).injective first 4245 (by decide) fresh2a
 have e6:run aliased m t=run single m t:=by
  have last:(run second m t).basis 4507=t.basis 4507:=by rw [e5];exact restore6
  exact (EqualSourceSwapResearch.rename_swap_equal_eq second 4507 4245 fresh2 t m equal6 last).trans e5
 have mp:measurementCount prep=0:=by simp [prep,measurementCount]
 rw [program,run_cat,run_cat]
 simp only [measurementCount_append,mp,Nat.zero_add,List.drop_zero]
 change run prep (m.drop (measurementCount aliased)) (run aliased m t)=_
 rw [e6,commute]
 exact (FreshCXResearch.twice 4243 4245 (by decide) (run single m s) m _).trans eq

end ECDSAAdd.Entrant.AAliasesResearch

end

-- Verified ABC18 optimization component AMiddleResources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AMiddleResearch
open AShortGhostFactsResearch AShortGhostProgramsResearch ARetimeFactsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots
 AQ0BaseResearch.program ECDSAAdd.wires GatePhysical

theorem q0_metric(metric:Program→Nat)(app:∀P Q,metric (P++Q)=metric P+metric Q)
 (hb:metric b0=metric b)(hd:metric d0=metric d)(hf:metric f0=metric f):
 metric AQ0BaseResearch.program=metric KnownAMidStaged.body:=by
 have old:=congrArg metric AShortGhostProgramsResearch.old_shape
 have new:metric AQ0BaseResearch.program=metric a+metric b0+metric c+metric d0+metric e+metric f0+metric g:=by
  simp only [AQ0BaseResearch.program,app]
 simp only [app] at old
 change metric AQ0BaseResearch.program=metric AShortGhostProgramsResearch.old
 omega

theorem q0_counts:
 toffoliCount AQ0BaseResearch.program=toffoliCount KnownAMidStaged.body ∧
 measurementCount AQ0BaseResearch.program=measurementCount KnownAMidStaged.body ∧
 Challenge.gateSlots AQ0BaseResearch.program=Challenge.gateSlots KnownAMidStaged.body:=by
 refine ⟨q0_metric toffoliCount toffoliCount_append ?_ ?_ ?_,
  q0_metric measurementCount measurementCount_append ?_ ?_ ?_,
  q0_metric Challenge.gateSlots Challenge.gateSlots_append ?_ ?_ ?_⟩
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).2
 · exact (renameProgram_counts _ _).2
 · exact (renameProgram_counts _ _).2
 · exact Baselines.rename_gateSlots _ _
 · exact Baselines.rename_gateSlots _ _
 · exact Baselines.rename_gateSlots _ _

theorem window_slots:Challenge.gateSlots fastWindow+2=Challenge.gateSlots b0:=by
 have n:Challenge.gateSlots fastWindow=Challenge.gateSlots ACFiniteWindowResearch.fast:=Baselines.rename_gateSlots _ _
 have o:Challenge.gateSlots oldWindow=Challenge.gateSlots ACFiniteWindowResearch.original:=Baselines.rename_gateSlots _ _
 have e:=congrArg Challenge.gateSlots ARetimeFactsResearch.checked.1
 have h:=ACFiniteWindowResearch.counts.2.2
 omega

theorem window_toffoli:toffoliCount fastWindow=toffoliCount b0:=by
 have n:toffoliCount fastWindow=toffoliCount ACFiniteWindowResearch.fast:=(renameProgram_counts _ _).1
 have o:toffoliCount oldWindow=toffoliCount ACFiniteWindowResearch.original:=(renameProgram_counts _ _).1
 exact (n.trans ACFiniteWindowResearch.counts.1).trans (o.symm.trans (congrArg toffoliCount ARetimeFactsResearch.checked.1.symm))

theorem counts:toffoliCount program=toffoliCount KnownAMidStaged.body ∧
 measurementCount program=measurementCount KnownAMidStaged.body ∧
 Challenge.gateSlots program+5=Challenge.gateSlots KnownAMidStaged.body:=by
 have t:=congrArg toffoliCount ARetimeFactsResearch.old_shape
 have m:=congrArg measurementCount ARetimeFactsResearch.old_shape
 have s:=congrArg Challenge.gateSlots ARetimeFactsResearch.old_shape
 have c:toffoliCount (copy 4758 4762)=0 ∧ measurementCount (copy 4758 4762)=0 ∧ Challenge.gateSlots (copy 4758 4762)=1:=by decide +kernel
 have e:toffoliCount (cleanup 4758 4762)=0 ∧ measurementCount (cleanup 4758 4762)=0 ∧ Challenge.gateSlots (cleanup 4758 4762)=2:=by decide +kernel
 have old:=q0_counts
 have tw:=window_toffoli
 have mw:=window_measurements
 have sw:=window_slots
 simp only [toffoliCount_append] at t
 simp only [measurementCount_append] at m
 simp only [Challenge.gateSlots_append] at s
 simp only [program,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩


end ECDSAAdd.Entrant.AMiddleResearch

end

-- Verified ABC18 optimization component AMiddleSupport
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AMiddleResearch
open AShortGhostFactsResearch AShortGhostProgramsResearch ARetimeFactsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem slice_subset(P:Program)(a b:Nat):wires ((P.drop a).take b)⊆wires P:=by
 have h:=congrArg wires (List.take_append_drop a P)
 have k:=congrArg wires (List.take_append_drop b (P.drop a))
 rw [wires_append] at h k
 exact (k ▸ Finset.subset_union_left).trans (h ▸ Finset.subset_union_right)

theorem drop_subset(P:Program)(a:Nat):wires (P.drop a)⊆wires P:=by
 have h:=congrArg wires (List.take_append_drop a P)
 rw [wires_append] at h
 exact h ▸ Finset.subset_union_right

theorem fast_support:wires fastWindow⊆wires oldWindow∪{4762}:=by decide +kernel

theorem fresh_of_old(q:Wire)(off:q∉wires KnownAMidStaged.body)
 (fixed:(Equiv.swap 4757 4760) q=q)(mod:q≠4762):q∉wires program:=by
 have slice(a b:Nat):q∉wires ((KnownAMidStaged.body.drop a).take b):=
  fun h=>off (slice_subset _ a b h)
 have aOff:q∉wires a:=by simpa only [a,List.drop_zero] using slice 0 1448
 have bOff:q∉wires b0:=fresh_fixed _ (Equiv.swap 4757 4760).injective b q fixed (slice 1448 6)
 have fastOff:q∉wires fastWindow:=by
  intro h
  rcases Finset.mem_union.mp (fast_support h) with h|h
  · exact bOff ((congrArg wires ARetimeFactsResearch.checked.1).symm ▸ h)
  · exact mod (Finset.mem_singleton.mp h)
 have dOff:q∉wires d0:=fresh_fixed _ (Equiv.swap 4757 4760).injective d q fixed (slice 3618 7)
 have fOff:q∉wires f0:=fresh_fixed _ (Equiv.swap 4757 4760).injective f q fixed (slice 5930 10)
 have cOff:q∉wires center:=by
  simp only [center,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨slice 2121 1497,dOff⟩,slice 3625 758⟩
 have sOff:q∉wires suffix:=by
  simp only [suffix,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨slice 4385 1545,fOff⟩,fun h=>off (drop_subset _ 5940 h)⟩
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨⟨⟨aOff,fastOff⟩,slice 1454 666⟩,cOff⟩,sOff⟩

end ECDSAAdd.Entrant.AMiddleResearch

end

-- Verified ABC18 optimization component AMiddlePhysical
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AMiddleResearch
open ThirdSavedCarryDevelop
open AShortGhostFactsResearch AShortGhostProgramsResearch ARetimeFactsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] GatePhysical ECDSAAdd.wires

theorem physical_slice(P:Program)(a b:Nat)(h:GatePhysical P):GatePhysical ((P.drop a).take b):=by
 unfold GatePhysical at *
 intro i hi
 exact h i (List.mem_of_mem_drop (List.mem_of_mem_take hi))

theorem physical_drop(P:Program)(a:Nat)(h:GatePhysical P):GatePhysical (P.drop a):=by
 unfold GatePhysical at *
 intro i hi
 exact h i (List.mem_of_mem_drop hi)

theorem fast_physical:GatePhysical fastWindow:=by
 change GatePhysical [.CCX 256 4889 4760,.CCX 257 4760 4762,.CX 4760 257,
  .measureX 4760 [] [.CZ 256 4889],.measureX 4760 [] []]
 simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]

theorem physical:GatePhysical program:=by
 have old:GatePhysical A161Low4FixedFold.body:=by
  have base:=aBodyTriple_physical ReorderedAFixed.L ReorderedAFixed.hw ReorderedAFixed.g
   (List.nodup_cons.mpr ⟨A161Low4FixedFold.ready.1,ReorderedAFixed.hn⟩)
  simp only [aBodyTriple,gatePhysical_append] at base
  simp only [A161Low4FixedFold.body,gatePhysical_append]
  exact ⟨base.1,base.2.1,A161Low4FixedFold.fold_physical⟩
 simp only [A161Low4FixedFold.body,A161Low4FixedFold.fold100,A161Low4GenericFold.loop,gatePhysical_append] at old
 have p:GatePhysical ARetimeFactsResearch.old:=by
  unfold GatePhysical at old ⊢
  intro i hi
  exact old.2.2.1.2 i ((KnownSparseFold.Cert.sublist _ _ _ _ _ KnownAMidStaged.cert).subset hi)
 have aP:GatePhysical a:=by simpa only [a,List.drop_zero] using physical_slice ARetimeFactsResearch.old 0 1448 p
 have dP:GatePhysical d0:=gatePhysical_rename (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective d
  (physical_slice ARetimeFactsResearch.old 3618 7 p)
 have fP:GatePhysical f0:=gatePhysical_rename (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective f
  (physical_slice ARetimeFactsResearch.old 5930 10 p)
 have cP:GatePhysical center:=by
  simp only [center,gatePhysical_append]
  exact ⟨⟨physical_slice ARetimeFactsResearch.old 2121 1497 p,dP⟩,physical_slice ARetimeFactsResearch.old 3625 758 p⟩
 have sP:GatePhysical suffix:=by
  simp only [suffix,gatePhysical_append]
  exact ⟨⟨physical_slice ARetimeFactsResearch.old 4385 1545 p,fP⟩,physical_drop ARetimeFactsResearch.old 5940 p⟩
 simp only [program,gatePhysical_append]
 exact ⟨⟨⟨⟨aP,fast_physical⟩,physical_slice ARetimeFactsResearch.old 1454 666 p⟩,cP⟩,sP⟩

end ECDSAAdd.Entrant.AMiddleResearch

end

-- Verified ABC18 optimization component AAliasesResources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AAliasesResearch
open AShortGhostProgramsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem combine_fresh(q:Wire)(off:q∉wires aliased)(h0:q≠4243)(h2:q≠4245):q∉wires program:=by
 have small:q∉wires prep:=by simp [prep,wires,Instr.wires,h0,h2]
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨small,off⟩,small⟩

theorem fresh_of_single(q:Wire)(off:q∉wires single)
 (f4:(Equiv.swap 4505 4243) q=q)(f5:(Equiv.swap 4506 4244) q=q)(f6:(Equiv.swap 4507 4245) q=q)
 (h0:q≠4243)(h2:q≠4245):q∉wires program:=by
 have a:q∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single q f4 off
 have b:q∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first q f5 a
 have c:q∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second q f6 b
 exact combine_fresh q c h0 h2

theorem low4_free:4505∉wires program:=by
 have a:4505∉wires first:=EqualSourceSwapResearch.retired single 4505 4243 (AMiddleResearch.fresh _ (by decide))
 have b:4505∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first 4505 (by decide) a
 have c:4505∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second 4505 (by decide) b
 exact combine_fresh 4505 c (by decide) (by decide)

theorem low5_free:4506∉wires program:=by
 have src:4244∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single 4244 (by decide)
  (AMiddleResearch.fresh _ (by decide))
 have b:4506∉wires second:=EqualSourceSwapResearch.retired first 4506 4244 src
 have c:4506∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second 4506 (by decide) b
 exact combine_fresh 4506 c (by decide) (by decide)

theorem low6_free:4507∉wires program:=by
 have a:4245∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single 4245 (by decide)
  (AMiddleResearch.fresh _ (by decide))
 have b:4245∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first 4245 (by decide) a
 have c:4507∉wires aliased:=EqualSourceSwapResearch.retired second 4507 4245 b
 exact combine_fresh 4507 c (by decide) (by decide)

theorem ghost_free(q:Wire)(hq:q∈([4757,4758,4759]:List Wire)):q∉wires program:=by
 have p:q∈([4757,4758,4759,4243,4244,4245]:List Wire):=by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢;itauto
 have off:q∉wires single:=AMiddleResearch.fresh q p
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>
  exact fresh_of_single _ off (by decide) (by decide) (by decide) (by decide) (by decide)

theorem counts:toffoliCount program=toffoliCount original ∧ measurementCount program=measurementCount original ∧
 Challenge.gateSlots program+3=Challenge.gateSlots original:=by
 have old:toffoliCount single=toffoliCount original ∧ measurementCount single=measurementCount original ∧
  Challenge.gateSlots single+5=Challenge.gateSlots original:=AMiddleResearch.counts
 have pp:toffoliCount prep=0 ∧ measurementCount prep=0 ∧ Challenge.gateSlots prep=1:=by decide +kernel
 simp only [program,aliased,second,first,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
  (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots,pp.1,pp.2.1,pp.2.2]
 exact ⟨by omega,by omega,by omega⟩

theorem physical:GatePhysical program:=by
 have pp:GatePhysical prep:=by simp [GatePhysical,prep,RecordedQuantum.PhysicalInstr,ProperGate]
 have a:GatePhysical first:=gatePhysical_rename _ (Equiv.swap 4505 4243).injective single AMiddleResearch.physical
 have b:GatePhysical second:=gatePhysical_rename _ (Equiv.swap 4506 4244).injective first a
 have c:GatePhysical aliased:=gatePhysical_rename _ (Equiv.swap 4507 4245).injective second b
 simp only [program,gatePhysical_append]
 exact ⟨⟨pp,c⟩,pp⟩



end ECDSAAdd.Entrant.AAliasesResearch

end


end

end
section


-- C short-lifetime helpers precede the existing A/C cache bodies.
-- Verified ABC18 optimization component CKShortGhostFacts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKShortGhostFactsResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
abbrev p:Program:=KnownCMidStaged.body
def a:Program:=p.take 1768
def b:Program:=(p.drop 1768).take 6
def c:Program:=(p.drop 1774).take 2166
def d:Program:=(p.drop 3940).take 7
def e:Program:=(p.drop 3947).take 2315
def f:Program:=(p.drop 6262).take 10
def g:Program:=p.drop 6272

theorem checked:
 PairedWritesResearch.check 4760 (p.take 1768) none=some none ∧
 PairedWritesResearch.check 4760 (p.take 3940) none=some none ∧
 PairedWritesResearch.check 4760 (p.take 6262) none=some none ∧
 PairedWritesResearch.check 4762 (p.take 1768) none=some none ∧
 PairedWritesResearch.check 4757 (p.take 1768) none=some none ∧
 PairedWritesResearch.check 4759 (p.take 1768) none=some none ∧
 ZeroAfterWriteResearch.check 4757 (p.take 3940) false=true ∧
 ZeroAfterWriteResearch.check 4757 (p.take 6262) false=true ∧
 ZeroAfterWriteResearch.check 4757 b false=true ∧
 ZeroAfterWriteResearch.check 4759 b false=true ∧
 ZeroAfterWriteResearch.check 4757 d false=true ∧
 ZeroAfterWriteResearch.check 4757 f false=true ∧
 C163Touch.touched b 4760=false ∧ C163Touch.touched b 4762=false ∧
 C163Touch.touched d 4760=false ∧ C163Touch.touched f 4760=false ∧
 6272≤p.length:=by decide +kernel

end ECDSAAdd.Entrant.CKShortGhostFactsResearch

end

-- Verified ABC18 optimization component CKShortGhostPrograms
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKShortGhostProgramsResearch
open CKShortGhostFactsResearch
abbrev old:Program:=CKShortGhostFactsResearch.p
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def b0:Program:=renameProgram (Equiv.swap 4757 4760) b
def b02:Program:=renameProgram (Equiv.swap 4759 4762) b0
def d0:Program:=renameProgram (Equiv.swap 4757 4760) d
def f0:Program:=renameProgram (Equiv.swap 4757 4760) f
def program:Program:=a++b02++c++d0++e++f0++g

theorem partition(P:Program):P=P.take 1768++(P.drop 1768).take 6++
 (P.drop 1774).take 2166++(P.drop 3940).take 7++(P.drop 3947).take 2315++
 (P.drop 6262).take 10++P.drop 6272:=by
 let r1:=P.drop 1768
 let r2:=r1.drop 6
 let r3:=r2.drop 2166
 let r4:=r3.drop 7
 let r5:=r4.drop 2315
 let r6:=r5.drop 10
 have h:P=P.take 1768++r1.take 6++r2.take 2166++r3.take 7++r4.take 2315++r5.take 10++r6:=by
  dsimp [r1,r2,r3,r4,r5,r6]
  simp only [List.append_assoc,List.take_append_drop]
 simpa only [r1,r2,r3,r4,r5,r6,List.drop_drop,Nat.reduceAdd] using h

theorem old_shape:old=a++b++c++d++e++f++g:=partition old

theorem prefixD:a++b++c=old.take 3940:=by
 change (old.take 1768++(old.drop 1768).take 6)++(old.drop 1774).take 2166=_
 rw [←List.take_add (l:=old) (i:=1768) (j:=6)]
 exact (List.take_add (l:=old) (i:=1774) (j:=2166)).symm

theorem prefixF:a++b++c++d++e=old.take 6262:=by
 rw [prefixD]
 change (old.take 3940++(old.drop 3940).take 7)++(old.drop 3947).take 2315=_
 rw [←List.take_add (l:=old) (i:=3940) (j:=7)]
 exact (List.take_add (l:=old) (i:=3947) (j:=2315)).symm

theorem not_wire(P:Program)(q:Nat)(h:C163Touch.touched P q=false):q∉wires P:=by
 intro bad
 have eq: C163Touch.touched P q=true:=(C163Touch.touched_spec _ _).mpr bad
 rw [h] at eq
 cases eq

theorem fresh_fixed(f:Wire→Wire)(inj:Function.Injective f)(P:Program)(q:Wire)
 (fix:f q=q)(fresh:q∉wires P):q∉wires (renameProgram f P):=by
 rw [renameProgram_support]
 intro bad
 obtain ⟨w,hw,he⟩:=Finset.mem_image.mp bad
 have eq:w=q:=inj (he.trans fix.symm)
 exact fresh (eq ▸ hw)

















theorem d0_eq(s:State)(m:List Bool)(h0:s.basis 4757=false)(hc:s.basis 4760=false):
 run d0 m s=run d m s:=by
 rcases checked with ⟨_,_,_,_,_,_,_,_,_,_,qd,_,_,_,fd,_,_⟩
 exact EqualSourceSwapResearch.rename_swap_equal_eq d 4757 4760 (not_wire d 4760 fd) s m
  (h0.trans hc.symm) ((ZeroAfterWriteResearch.erased 4757 d qd s m).trans h0.symm)

theorem f0_eq(s:State)(m:List Bool)(h0:s.basis 4757=false)(hc:s.basis 4760=false):
 run f0 m s=run f m s:=by
 rcases checked with ⟨_,_,_,_,_,_,_,_,_,_,_,qf,_,_,_,ff,_⟩
 exact EqualSourceSwapResearch.rename_swap_equal_eq f 4757 4760 (not_wire f 4760 ff) s m
  (h0.trans hc.symm) ((ZeroAfterWriteResearch.erased 4757 f qf s m).trans h0.symm)



end ECDSAAdd.Entrant.CKShortGhostProgramsResearch

end

-- Verified ABC18 optimization component CKQ0Base
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKQ0BaseResearch
open CKShortGhostFactsResearch CKShortGhostProgramsResearch InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def program:Program:=a++b0++c++d0++e++f0++g

theorem b0_eq(s:State)(m:List Bool)(h0:s.basis 4757=false)(hc:s.basis 4760=false):
 run b0 m s=run b m s:=by
 rcases checked with ⟨_,_,_,_,_,_,_,_,qb,_,_,_,fb,_,_,_,_⟩
 exact EqualSourceSwapResearch.rename_swap_equal_eq b 4757 4760 (not_wire b 4760 fb) s m
  (h0.trans hc.symm) ((ZeroAfterWriteResearch.erased 4757 b qb s m).trans h0.symm)

theorem context_eq(pre P Q post:Program)(s:State)(m:List Bool)
 (hm:measurementCount P=measurementCount Q)
 (he:∀r,run P r (run pre (m.take (measurementCount pre)) s)=
  run Q r (run pre (m.take (measurementCount pre)) s)):
 run (pre++P++post) m s=run (pre++Q++post) m s:=by
 apply BPatchedLoopResearch.run_middle_congr pre P Q post s m hm
 unfold middleState
 rw [hm]
 exact he _

theorem equivalent(s:State)(m:List Bool)(q0:s.basis 4757=false)
 (cin:s.basis 4760=false):run program m s=run old m s:=by
 rcases checked with ⟨ciA,ciD,ciF,flA,qoA,qtA,qoD,qoF,_,_,_,_,_,_,_,_,_⟩
 have mb:measurementCount b=measurementCount b0:=by
  simp only [b0,b0,(renameProgram_counts _ _).2]
 have md:measurementCount d=measurementCount d0:=by
  simp only [d0,(renameProgram_counts _ _).2]
 have mf:measurementCount f=measurementCount f0:=by
  simp only [f0,(renameProgram_counts _ _).2]
 have paQ:(run a (m.take (measurementCount a)) s).basis 4757=false:=
  (PairedWritesResearch.preserved 4757 a qoA s _).trans q0
 have paC:(run a (m.take (measurementCount a)) s).basis 4760=false:=
  (PairedWritesResearch.preserved 4760 a ciA s _).trans cin
 have hb:∀r,run b r (run a (m.take (measurementCount a)) s)=run b0 r (run a (m.take (measurementCount a)) s):=fun r=>(b0_eq (run a (m.take (measurementCount a)) s) r paQ paC).symm
 have pdQ:(run (a++b++c) (m.take (measurementCount (a++b++c))) s).basis 4757=false:=by
  rw [prefixD]
  exact ZeroAfterWriteResearch.erased 4757 (old.take 3940) qoD s _
 have pdC:(run (a++b++c) (m.take (measurementCount (a++b++c))) s).basis 4760=false:=by
  rw [prefixD]
  exact (PairedWritesResearch.preserved 4760 (old.take 3940) ciD s _).trans cin
 have hd:∀r,run d r (run (a++b++c) (m.take (measurementCount (a++b++c))) s)=run d0 r (run (a++b++c) (m.take (measurementCount (a++b++c))) s):=fun r=>(d0_eq (run (a++b++c) (m.take (measurementCount (a++b++c))) s) r pdQ pdC).symm
 have pfQ:(run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s).basis 4757=false:=by
  rw [prefixF]
  exact ZeroAfterWriteResearch.erased 4757 (old.take 6262) qoF s _
 have pfC:(run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s).basis 4760=false:=by
  rw [prefixF]
  exact (PairedWritesResearch.preserved 4760 (old.take 6262) ciF s _).trans cin
 have hf:∀r,run f r (run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s)=run f0 r (run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s):=fun r=>(f0_eq (run (a++b++c++d++e) (m.take (measurementCount (a++b++c++d++e))) s) r pfQ pfC).symm
 have ef:=context_eq (a++b++c++d++e) f f0 g s m mf hf
 have ed:=context_eq (a++b++c) d d0 (e++f0++g) s m md hd
 have eb:=context_eq a b b0 (c++d0++e++f0++g) s m mb hb
 have shape:old=(a++b++c++d++e)++f++g:=old_shape
 calc
  run program m s=run (a++b0++(c++d0++e++f0++g)) m s:=by
   simp only [program,List.append_assoc]
  _=run (a++b++(c++d0++e++f0++g)) m s:=eb.symm
  _=run ((a++b++c)++d0++(e++f0++g)) m s:=by simp only [List.append_assoc]
  _=run ((a++b++c)++d++(e++f0++g)) m s:=ed.symm
  _=run ((a++b++c++d++e)++f0++g) m s:=by simp only [List.append_assoc]
  _=run ((a++b++c++d++e)++f++g) m s:=ef.symm
  _=run old m s:=by rw [←shape]

end ECDSAAdd.Entrant.CKQ0BaseResearch

end

-- Verified ABC18 optimization component CKRetimeFacts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKRetimeFactsResearch
open CKShortGhostFactsResearch CKShortGhostProgramsResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
abbrev old:Program:=KnownCMidStaged.body
def ports:Fin 12→Wire:=![256,4889,4627,4628,257,4760,4759,4758,4762,0,1,2]
def oldWindow:Program:=renameProgram (ACPlacedWindowResearch.label ports) ACFiniteWindowResearch.original
def fastWindow:Program:=ACPlacedWindowResearch.fastAt ports
def gap:Program:=(old.drop 1774).take 668
def center:Program:=(old.drop 2443).take 1497++d0++(old.drop 3947).take 758
def suffix:Program:=(old.drop 4707).take 1555++f0++g

theorem ports_inj:Function.Injective ports:=by decide +kernel

theorem checked:
 b0=oldWindow ∧
 (old.drop 2442).take 1=[.CX 4758 4762] ∧
 (old.drop 4705).take 2=[.CX 4762 4758,.X 4758] ∧
 PairedWritesResearch.check 4758 a none=some none ∧
 C163Touch.touched gap 4758=false ∧ C163Touch.touched gap 4762=false ∧
 C163Touch.touched center 4758=false ∧ C163Touch.touched suffix 4758=false ∧
 ([a,fastWindow,gap,center,suffix]:List Program).all (fun P=>
  ([4757,4758,4759,4243,4244,4245]:List Wire).all (fun q=>!C163Touch.touched P q))=true:=by decide +kernel

end ECDSAAdd.Entrant.CKRetimeFactsResearch

end

-- Verified ABC18 optimization component ListCKWindowParts
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ListCKWindowPartsResearch
set_option autoImplicit false

set_option maxRecDepth 10000

theorem split3(P:Program)(a b:Nat):P=P.take a++(P.drop a).take b++P.drop (a+b):=by
 calc
  P=P.take a++P.drop a:=(List.take_append_drop a P).symm
  _=P.take a++((P.drop a).take b++(P.drop a).drop b):=
   congrArg (fun t=>P.take a++t) (List.take_append_drop b (P.drop a)).symm
  _=P.take a++(P.drop a).take b++P.drop (a+b):=by simp only [List.append_assoc,List.drop_drop]

theorem c_template(P:Program):(P.drop 1774).take 2166=
 (P.drop 1774).take 668++(P.drop 2442).take 1++(P.drop 2443).take 1497:=by
 simpa only [List.take_take,List.drop_take,List.drop_drop] using split3 ((P.drop 1774).take 2166) 668 1

theorem e_template(P:Program):(P.drop 3947).take 2315=
 (P.drop 3947).take 758++(P.drop 4705).take 2++(P.drop 4707).take 1555:=by
 simpa only [List.take_take,List.drop_take,List.drop_drop] using split3 ((P.drop 3947).take 2315) 758 2
end ECDSAAdd.Entrant.ListCKWindowPartsResearch

end

-- Verified ABC18 optimization component CKRetimeParts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKRetimeFactsResearch
open CKShortGhostFactsResearch CKShortGhostProgramsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem c_split:c=gap++copy 4758 4762++(old.drop 2443).take 1497:=by
 have h:=ListCKWindowPartsResearch.c_template old
 have eq:=congrArg (fun P:Program=>(old.drop 1774).take 668++P++(old.drop 2443).take 1497) checked.2.1
 exact h.trans eq

theorem e_split:e=(old.drop 3947).take 758++cleanup 4758 4762++(old.drop 4707).take 1555:=by
 have h:=ListCKWindowPartsResearch.e_template old
 have eq:=congrArg (fun P:Program=>(old.drop 3947).take 758++P++(old.drop 4707).take 1555) checked.2.2.1
 exact h.trans eq

theorem old_shape:CKQ0BaseResearch.program=a++b0++(gap++copy 4758 4762++center++cleanup 4758 4762++suffix):=by
 simp only [CKQ0BaseResearch.program,c_split,e_split,center,suffix,List.append_assoc]

theorem gap_fresh:4758∉wires gap ∧ 4762∉wires gap:=
 ⟨not_wire _ _ checked.2.2.2.2.1,not_wire _ _ checked.2.2.2.2.2.1⟩

theorem center_fresh:4758∉wires center:=not_wire _ _ checked.2.2.2.2.2.2.1

theorem suffix_fresh:4758∉wires suffix:=not_wire _ _ checked.2.2.2.2.2.2.2.1

end ECDSAAdd.Entrant.CKRetimeFactsResearch

end

-- Verified ABC18 optimization component CKWindowFrame
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKRetimeFactsResearch
open CKShortGhostFactsResearch CKShortGhostProgramsResearch B95RetimeResearch ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem reference_shape:ACPlacedWindowResearch.originalAt ports=oldWindow++exchange 4758 4762:=by decide +kernel

theorem window_measurements:measurementCount fastWindow=measurementCount b0:=by
 have n:measurementCount fastWindow=measurementCount ACFiniteWindowResearch.fast:=
  (renameProgram_counts _ _).2
 have o:measurementCount oldWindow=measurementCount ACFiniteWindowResearch.original:=
  (renameProgram_counts _ _).2
 exact (n.trans ACFiniteWindowResearch.counts.2.1).trans
  (o.symm.trans (congrArg measurementCount checked.1.symm))

theorem window_eq(s:State)(m:List Bool)
 (hc:s.basis 4760=false)(h2:s.basis 4759=false)(h1:s.basis 4758=false)(hm:s.basis 4762=false):
 run fastWindow m s=run (exchange 4758 4762) [] (run b0 m s):=by
 have eq:=ACPlacedWindowResearch.run_eq ports ports_inj s m ⟨hc,h2,h1,hm⟩
 have refEq:run (ACPlacedWindowResearch.originalAt ports) m s=
  run (exchange 4758 4762) [] (run oldWindow m s):=by
  rw [reference_shape,run_cat]
  exact zero_records _ (by simp [exchange,measurementCount]) _ _
 exact eq.trans (refEq.trans (congrArg (fun t=>run (exchange 4758 4762) [] t)
  (congrArg (fun P=>run P m s) checked.1.symm)))

end ECDSAAdd.Entrant.CKRetimeFactsResearch

end

-- Verified ABC18 optimization component CKMiddle
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKMiddleResearch
open CKShortGhostFactsResearch CKShortGhostProgramsResearch CKRetimeFactsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def program:Program:=a++fastWindow++gap++center++suffix

theorem run_erased(s:State)(m:List Bool)
 (q0:s.basis 4757=false)(q1:s.basis 4758=false)(q2:s.basis 4759=false)
 (ci:s.basis 4760=false)(fl:s.basis 4762=false):
 run program m s=erase 4758 (run KnownCMidStaged.body m s):=by
 let t:=run a (m.take (measurementCount a)) s
 rcases CKShortGhostFactsResearch.checked with ⟨ciA,_,_,flA,_,q2A,_,_,_,_,_,_,_,fbm,_,_,_⟩
 have tc:t.basis 4760=false:=(PairedWritesResearch.preserved 4760 a ciA s _).trans ci
 have tq1:t.basis 4758=false:=(PairedWritesResearch.preserved 4758 a CKRetimeFactsResearch.checked.2.2.2.1 s _).trans q1
 have tq2:t.basis 4759=false:=(PairedWritesResearch.preserved 4759 a q2A s _).trans q2
 have tf:t.basis 4762=false:=(PairedWritesResearch.preserved 4762 a flA s _).trans fl
 have eq:∀r,run fastWindow r t=run (exchange 4758 4762) [] (run b0 r t):=
  fun r=>window_eq t r tc tq2 tq1 tf
 have off:4762∉wires b0:=fresh_fixed (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective b 4762
  (by decide) (not_wire b 4762 fbm)
 have hz:∀r,(run b0 r t).basis 4762=false:=fun r=>(run_preserves_outside b0 r t 4762 off).trans tf
 have h:=window_context a b0 fastWindow gap center suffix 4758 4762 (by decide)
  gap_fresh.1 gap_fresh.2 center_fresh suffix_fresh window_measurements s m eq hz
 have new_shape:program=a++fastWindow++(gap++center++suffix):=by simp only [program,List.append_assoc]
 have one:run program m s=erase 4758 (run CKQ0BaseResearch.program m s):=
  (congrArg (fun P=>run P m s) new_shape).trans
   (h.trans (congrArg (fun P=>erase 4758 (run P m s)) CKRetimeFactsResearch.old_shape.symm))
 exact one.trans (congrArg (erase 4758) (CKQ0BaseResearch.equivalent s m q0 ci))

theorem equivalent(s:State)(m:List Bool)
 (q0:s.basis 4757=false)(q1:s.basis 4758=false)(q2:s.basis 4759=false)
 (ci:s.basis 4760=false)(fl:s.basis 4762=false)
 (out:(run KnownCMidStaged.body m s).basis 4758=false):
 run program m s=run KnownCMidStaged.body m s:=
 (run_erased s m q0 q1 q2 ci fl).trans (erase_eq 4758 _ out)

theorem fresh(q:Wire)(hq:q∈([4757,4758,4759,4243,4244,4245]:List Wire)):
 q∉wires program:=by
 have checked:=CKRetimeFactsResearch.checked.2.2.2.2.2.2.2.2
 have off(P:Program)(hp:P∈([a,fastWindow,gap,center,suffix]:List Program)):q∉wires P:=by
  have h:=List.all_eq_true.mp (List.all_eq_true.mp checked P hp) q hq
  intro bad
  have yes:C163Touch.touched P q=true:=(C163Touch.touched_spec _ _).mpr bad
  simp only [yes,Bool.not_true,Bool.false_eq_true] at h
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨⟨⟨off a (by simp),off fastWindow (by simp)⟩,off gap (by simp)⟩,off center (by simp)⟩,off suffix (by simp)⟩


end ECDSAAdd.Entrant.CKMiddleResearch

end

-- Verified ABC18 optimization component CKReady
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKMiddleResearch
open InverseCarryDevelop
abbrev acc:List Wire:=C163Low4Middle.ga
abbrev src:List Wire:=C163Low4Middle.src
abbrev pad:List Wire:=C163Low4Middle.pad
abbrev bank:List Wire:=C163Low4Middle.bank
abbrev cin:Wire:=C163Low4Middle.L.core.cin
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem acc_length: acc.length=163:=by decide +kernel
theorem source_length: src.length=130:=by decide +kernel

theorem maps:acc.getD 0 0=4757 ∧ acc.getD 1 0=4758 ∧ acc.getD 2 0=4759:=by decide +kernel

theorem ready_eq(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run KnownCMidStaged.body m s))
 (flag:s.basis 4762=false):run program m s=run KnownCMidStaged.body m s:=by
 have zero(i:Nat)(hi:i<3):s.basis (acc.getD i 0)=false:=
  LowWordRecovery.low_register_zero acc s.basis H i (by omega)
   (by have h:=acc_length;omega) before.1
 have out:(run KnownCMidStaged.body m s).basis 4758=false:=by
  have h:=LowWordRecovery.low_register_zero acc (run KnownCMidStaged.body m s).basis H 1 (by decide)
   (by have h:=acc_length;omega) after.1
  simpa only [maps.2.1] using h
 apply equivalent s m
 · simpa only [maps.1] using zero 0 (by decide)
 · simpa only [maps.2.1] using zero 1 (by decide)
 · simpa only [maps.2.2] using zero 2 (by decide)
 · exact before.2.2.2.2
 · exact flag
 · exact out

end ECDSAAdd.Entrant.CKMiddleResearch

end

-- Verified ABC18 optimization component CKAliases
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKAliasesResearch
open CKMiddleResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev original:Program:=KnownCMidStaged.body
abbrev single:Program:=CKMiddleResearch.program
def prep:Program:=[.CX 4243 4245]
def first:Program:=renameProgram (Equiv.swap 4505 4243) single
def second:Program:=renameProgram (Equiv.swap 4506 4244) first
def aliased:Program:=renameProgram (Equiv.swap 4507 4245) second
def program:Program:=prep++aliased++prep

theorem equivalent(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run original m s))
 (flag:s.basis 4762=false):run program m s=run original m s:=by
 have eq:run single m s=run original m s:=CKMiddleResearch.ready_eq H s m before after flag
 have stable:∀q∈acc,(run single m s).basis q=s.basis q:=by
  apply (regValue_eq_iff acc _ _).mp
  rw [eq]
  exact after.1.trans before.1.symm
 have q4s: (run single m s).basis 4505=s.basis 4505:=stable _ (by decide +kernel)
 have q5s:(run single m s).basis 4506=s.basis 4506:=stable _ (by decide +kernel)
 have q6s: (run single m s).basis 4507=s.basis 4507:=stable _ (by decide +kernel)
 have val:regValue acc s.basis=4294968272*regValue src s.basis:=by rw [before.2.1];exact before.1
 have cp:=LowWordRecovery.copies acc src s.basis (by rw [acc_length];decide) (by rw [source_length];decide) val
 have c4:s.basis 4505=s.basis 4243:=by
  simpa only [show src.getD 0 0=4243 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.1.symm
 have c5:s.basis 4506=s.basis 4244:=by
  simpa only [show src.getD 1 0=4244 from by decide +kernel,
   show acc.getD 5 0=4506 from by decide +kernel] using cp.2.1.symm
 have c6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243):=by
  have low:s.basis 4245=(s.basis 4507 ^^ s.basis 4505):=by
   simpa only [show src.getD 2 0=4245 from by decide +kernel,
    show acc.getD 6 0=4507 from by decide +kernel,
    show acc.getD 4 0=4505 from by decide +kernel] using cp.2.2
  rw [low,←c4]
  simp [Bool.xor_assoc]
 have h0:4243∉wires single:=CKMiddleResearch.fresh _ (by decide)
 have h1:4244∉wires single:=CKMiddleResearch.fresh _ (by decide)
 have h2:4245∉wires single:=CKMiddleResearch.fresh _ (by decide)
 let t:=run prep m s
 have commute:run single m t=run prep m (run single m s):=
  FreshCXResearch.commute single 4243 4245 h0 h2 s m m
 have equal4:t.basis 4505=t.basis 4243:=by simpa [t,prep,run,writeBit] using c4
 have equal5:t.basis 4506=t.basis 4244:=by simpa [t,prep,run,writeBit] using c5
 have equal6:t.basis 4507=t.basis 4245:=by simpa [t,prep,run,writeBit] using c6
 have restore4:(run single m t).basis 4505=t.basis 4505:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q4s
 have restore5:(run single m t).basis 4506=t.basis 4506:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q5s
 have restore6:(run single m t).basis 4507=t.basis 4507:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q6s
 have e4:run first m t=run single m t:=
  EqualSourceSwapResearch.rename_swap_equal_eq single 4505 4243 h0 t m equal4 restore4
 have fresh1:4244∉wires first:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4505 4243)
  (Equiv.swap 4505 4243).injective single 4244 (by decide) h1
 have e5:run second m t=run single m t:=by
  have last:(run first m t).basis 4506=t.basis 4506:=by rw [e4];exact restore5
  exact (EqualSourceSwapResearch.rename_swap_equal_eq first 4506 4244 fresh1 t m equal5 last).trans e4
 have fresh2a:4245∉wires first:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4505 4243)
  (Equiv.swap 4505 4243).injective single 4245 (by decide) h2
 have fresh2:4245∉wires second:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4506 4244)
  (Equiv.swap 4506 4244).injective first 4245 (by decide) fresh2a
 have e6:run aliased m t=run single m t:=by
  have last:(run second m t).basis 4507=t.basis 4507:=by rw [e5];exact restore6
  exact (EqualSourceSwapResearch.rename_swap_equal_eq second 4507 4245 fresh2 t m equal6 last).trans e5
 have mp:measurementCount prep=0:=by simp [prep,measurementCount]
 rw [program,run_cat,run_cat]
 simp only [measurementCount_append,mp,Nat.zero_add,List.drop_zero]
 change run prep (m.drop (measurementCount aliased)) (run aliased m t)=_
 rw [e6,commute]
 exact (FreshCXResearch.twice 4243 4245 (by decide) (run single m s) m _).trans eq

end ECDSAAdd.Entrant.CKAliasesResearch

end

-- Verified ABC18 optimization component CKMiddleResources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKMiddleResearch
open CKShortGhostFactsResearch CKShortGhostProgramsResearch CKRetimeFactsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots
 CKQ0BaseResearch.program ECDSAAdd.wires GatePhysical

theorem q0_metric(metric:Program→Nat)(app:∀P Q,metric (P++Q)=metric P+metric Q)
 (hb:metric b0=metric b)(hd:metric d0=metric d)(hf:metric f0=metric f):
 metric CKQ0BaseResearch.program=metric KnownCMidStaged.body:=by
 have old:=congrArg metric CKShortGhostProgramsResearch.old_shape
 have new:metric CKQ0BaseResearch.program=metric a+metric b0+metric c+metric d0+metric e+metric f0+metric g:=by
  simp only [CKQ0BaseResearch.program,app]
 simp only [app] at old
 change metric CKQ0BaseResearch.program=metric CKShortGhostProgramsResearch.old
 omega

theorem q0_counts:
 toffoliCount CKQ0BaseResearch.program=toffoliCount KnownCMidStaged.body ∧
 measurementCount CKQ0BaseResearch.program=measurementCount KnownCMidStaged.body ∧
 Challenge.gateSlots CKQ0BaseResearch.program=Challenge.gateSlots KnownCMidStaged.body:=by
 refine ⟨q0_metric toffoliCount toffoliCount_append ?_ ?_ ?_,
  q0_metric measurementCount measurementCount_append ?_ ?_ ?_,
  q0_metric Challenge.gateSlots Challenge.gateSlots_append ?_ ?_ ?_⟩
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).1
 · exact (renameProgram_counts _ _).2
 · exact (renameProgram_counts _ _).2
 · exact (renameProgram_counts _ _).2
 · exact Baselines.rename_gateSlots _ _
 · exact Baselines.rename_gateSlots _ _
 · exact Baselines.rename_gateSlots _ _

theorem window_slots:Challenge.gateSlots fastWindow+2=Challenge.gateSlots b0:=by
 have n:Challenge.gateSlots fastWindow=Challenge.gateSlots ACFiniteWindowResearch.fast:=Baselines.rename_gateSlots _ _
 have o:Challenge.gateSlots oldWindow=Challenge.gateSlots ACFiniteWindowResearch.original:=Baselines.rename_gateSlots _ _
 have e:=congrArg Challenge.gateSlots CKRetimeFactsResearch.checked.1
 have h:=ACFiniteWindowResearch.counts.2.2
 omega

theorem window_toffoli:toffoliCount fastWindow=toffoliCount b0:=by
 have n:toffoliCount fastWindow=toffoliCount ACFiniteWindowResearch.fast:=(renameProgram_counts _ _).1
 have o:toffoliCount oldWindow=toffoliCount ACFiniteWindowResearch.original:=(renameProgram_counts _ _).1
 exact (n.trans ACFiniteWindowResearch.counts.1).trans (o.symm.trans (congrArg toffoliCount CKRetimeFactsResearch.checked.1.symm))

theorem counts:toffoliCount program=toffoliCount KnownCMidStaged.body ∧
 measurementCount program=measurementCount KnownCMidStaged.body ∧
 Challenge.gateSlots program+5=Challenge.gateSlots KnownCMidStaged.body:=by
 have t:=congrArg toffoliCount CKRetimeFactsResearch.old_shape
 have m:=congrArg measurementCount CKRetimeFactsResearch.old_shape
 have s:=congrArg Challenge.gateSlots CKRetimeFactsResearch.old_shape
 have c:toffoliCount (copy 4758 4762)=0 ∧ measurementCount (copy 4758 4762)=0 ∧ Challenge.gateSlots (copy 4758 4762)=1:=by decide +kernel
 have e:toffoliCount (cleanup 4758 4762)=0 ∧ measurementCount (cleanup 4758 4762)=0 ∧ Challenge.gateSlots (cleanup 4758 4762)=2:=by decide +kernel
 have old:=q0_counts
 have tw:=window_toffoli
 have mw:=window_measurements
 have sw:=window_slots
 simp only [toffoliCount_append] at t
 simp only [measurementCount_append] at m
 simp only [Challenge.gateSlots_append] at s
 simp only [program,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩


end ECDSAAdd.Entrant.CKMiddleResearch

end

-- Verified ABC18 optimization component CKMiddleSupport
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKMiddleResearch
open CKShortGhostFactsResearch CKShortGhostProgramsResearch CKRetimeFactsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem slice_subset(P:Program)(a b:Nat):wires ((P.drop a).take b)⊆wires P:=by
 have h:=congrArg wires (List.take_append_drop a P)
 have k:=congrArg wires (List.take_append_drop b (P.drop a))
 rw [wires_append] at h k
 exact (k ▸ Finset.subset_union_left).trans (h ▸ Finset.subset_union_right)

theorem drop_subset(P:Program)(a:Nat):wires (P.drop a)⊆wires P:=by
 have h:=congrArg wires (List.take_append_drop a P)
 rw [wires_append] at h
 exact h ▸ Finset.subset_union_right

theorem fast_support:wires fastWindow⊆wires oldWindow∪{4762}:=by decide +kernel

theorem fresh_of_old(q:Wire)(off:q∉wires KnownCMidStaged.body)
 (fixed:(Equiv.swap 4757 4760) q=q)(mod:q≠4762):q∉wires program:=by
 have slice(a b:Nat):q∉wires ((KnownCMidStaged.body.drop a).take b):=
  fun h=>off (slice_subset _ a b h)
 have aOff:q∉wires a:=by simpa only [a,List.drop_zero] using slice 0 1768
 have bOff:q∉wires b0:=fresh_fixed _ (Equiv.swap 4757 4760).injective b q fixed (slice 1768 6)
 have fastOff:q∉wires fastWindow:=by
  intro h
  rcases Finset.mem_union.mp (fast_support h) with h|h
  · exact bOff ((congrArg wires CKRetimeFactsResearch.checked.1).symm ▸ h)
  · exact mod (Finset.mem_singleton.mp h)
 have dOff:q∉wires d0:=fresh_fixed _ (Equiv.swap 4757 4760).injective d q fixed (slice 3940 7)
 have fOff:q∉wires f0:=fresh_fixed _ (Equiv.swap 4757 4760).injective f q fixed (slice 6262 10)
 have cOff:q∉wires center:=by
  simp only [center,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨slice 2443 1497,dOff⟩,slice 3947 758⟩
 have sOff:q∉wires suffix:=by
  simp only [suffix,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨slice 4707 1555,fOff⟩,fun h=>off (drop_subset _ 6272 h)⟩
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨⟨⟨aOff,fastOff⟩,slice 1774 668⟩,cOff⟩,sOff⟩

end ECDSAAdd.Entrant.CKMiddleResearch

end

-- Verified ABC18 optimization component CKMiddlePhysical
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKMiddleResearch
open ThirdSavedCarryDevelop
open CKShortGhostFactsResearch CKShortGhostProgramsResearch CKRetimeFactsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] GatePhysical ECDSAAdd.wires

theorem physical_slice(P:Program)(a b:Nat)(h:GatePhysical P):GatePhysical ((P.drop a).take b):=by
 unfold GatePhysical at *
 intro i hi
 exact h i (List.mem_of_mem_drop (List.mem_of_mem_take hi))

theorem physical_drop(P:Program)(a:Nat)(h:GatePhysical P):GatePhysical (P.drop a):=by
 unfold GatePhysical at *
 intro i hi
 exact h i (List.mem_of_mem_drop hi)

theorem fast_physical:GatePhysical fastWindow:=by
 change GatePhysical [.CCX 256 4889 4760,.CCX 257 4760 4762,.CX 4760 257,
  .measureX 4760 [] [.CZ 256 4889],.measureX 4760 [] []]
 simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]

theorem physical:GatePhysical program:=by
 have old:=C163Low4Middle.body_physical
 simp only [C163Low4Middle.body,C163Low4Body.bodyProgram,C163Low4Middle.loop,gatePhysical_append] at old
 have p:GatePhysical CKRetimeFactsResearch.old:=by
  unfold GatePhysical at old ⊢
  intro i hi
  exact old.2.1.2 i ((KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert).subset hi)
 have aP:GatePhysical a:=by simpa only [a,List.drop_zero] using physical_slice CKRetimeFactsResearch.old 0 1768 p
 have dP:GatePhysical d0:=gatePhysical_rename (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective d
  (physical_slice CKRetimeFactsResearch.old 3940 7 p)
 have fP:GatePhysical f0:=gatePhysical_rename (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective f
  (physical_slice CKRetimeFactsResearch.old 6262 10 p)
 have cP:GatePhysical center:=by
  simp only [center,gatePhysical_append]
  exact ⟨⟨physical_slice CKRetimeFactsResearch.old 2443 1497 p,dP⟩,physical_slice CKRetimeFactsResearch.old 3947 758 p⟩
 have sP:GatePhysical suffix:=by
  simp only [suffix,gatePhysical_append]
  exact ⟨⟨physical_slice CKRetimeFactsResearch.old 4707 1555 p,fP⟩,physical_drop CKRetimeFactsResearch.old 6272 p⟩
 simp only [program,gatePhysical_append]
 exact ⟨⟨⟨⟨aP,fast_physical⟩,physical_slice CKRetimeFactsResearch.old 1774 668 p⟩,cP⟩,sP⟩

end ECDSAAdd.Entrant.CKMiddleResearch

end

-- Verified ABC18 optimization component CKAliasesResources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKAliasesResearch
open CKShortGhostProgramsResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem combine_fresh(q:Wire)(off:q∉wires aliased)(h0:q≠4243)(h2:q≠4245):q∉wires program:=by
 have small:q∉wires prep:=by simp [prep,wires,Instr.wires,h0,h2]
 simp only [program,wires_append,Finset.mem_union,not_or]
 exact ⟨⟨small,off⟩,small⟩

theorem fresh_of_single(q:Wire)(off:q∉wires single)
 (f4:(Equiv.swap 4505 4243) q=q)(f5:(Equiv.swap 4506 4244) q=q)(f6:(Equiv.swap 4507 4245) q=q)
 (h0:q≠4243)(h2:q≠4245):q∉wires program:=by
 have a:q∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single q f4 off
 have b:q∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first q f5 a
 have c:q∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second q f6 b
 exact combine_fresh q c h0 h2

theorem low4_free:4505∉wires program:=by
 have a:4505∉wires first:=EqualSourceSwapResearch.retired single 4505 4243 (CKMiddleResearch.fresh _ (by decide))
 have b:4505∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first 4505 (by decide) a
 have c:4505∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second 4505 (by decide) b
 exact combine_fresh 4505 c (by decide) (by decide)

theorem low5_free:4506∉wires program:=by
 have src:4244∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single 4244 (by decide)
  (CKMiddleResearch.fresh _ (by decide))
 have b:4506∉wires second:=EqualSourceSwapResearch.retired first 4506 4244 src
 have c:4506∉wires aliased:=fresh_fixed _ (Equiv.swap 4507 4245).injective second 4506 (by decide) b
 exact combine_fresh 4506 c (by decide) (by decide)

theorem low6_free:4507∉wires program:=by
 have a:4245∉wires first:=fresh_fixed _ (Equiv.swap 4505 4243).injective single 4245 (by decide)
  (CKMiddleResearch.fresh _ (by decide))
 have b:4245∉wires second:=fresh_fixed _ (Equiv.swap 4506 4244).injective first 4245 (by decide) a
 have c:4507∉wires aliased:=EqualSourceSwapResearch.retired second 4507 4245 b
 exact combine_fresh 4507 c (by decide) (by decide)

theorem ghost_free(q:Wire)(hq:q∈([4757,4758,4759]:List Wire)):q∉wires program:=by
 have p:q∈([4757,4758,4759,4243,4244,4245]:List Wire):=by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢;itauto
 have off:q∉wires single:=CKMiddleResearch.fresh q p
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>
  exact fresh_of_single _ off (by decide) (by decide) (by decide) (by decide) (by decide)

theorem counts:toffoliCount program=toffoliCount original ∧ measurementCount program=measurementCount original ∧
 Challenge.gateSlots program+3=Challenge.gateSlots original:=by
 have old:toffoliCount single=toffoliCount original ∧ measurementCount single=measurementCount original ∧
  Challenge.gateSlots single+5=Challenge.gateSlots original:=CKMiddleResearch.counts
 have pp:toffoliCount prep=0 ∧ measurementCount prep=0 ∧ Challenge.gateSlots prep=1:=by decide +kernel
 simp only [program,aliased,second,first,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
  (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots,pp.1,pp.2.1,pp.2.2]
 exact ⟨by omega,by omega,by omega⟩

theorem physical:GatePhysical program:=by
 have pp:GatePhysical prep:=by simp [GatePhysical,prep,RecordedQuantum.PhysicalInstr,ProperGate]
 have a:GatePhysical first:=gatePhysical_rename _ (Equiv.swap 4505 4243).injective single CKMiddleResearch.physical
 have b:GatePhysical second:=gatePhysical_rename _ (Equiv.swap 4506 4244).injective first a
 have c:GatePhysical aliased:=gatePhysical_rename _ (Equiv.swap 4507 4245).injective second b
 simp only [program,gatePhysical_append]
 exact ⟨⟨pp,c⟩,pp⟩



end ECDSAAdd.Entrant.CKAliasesResearch

end


-- Verified ABC18 optimization component A109Geometry
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

def hosts:List Wire:=ReorderedAFixed.hosts++[4757,4758,4759,4505,4506,4507]
def ports:List Wire:=[4757,4760,4759,4762,4758,4244,4506,4505,4243,4507,4245]

theorem geometry:hosts.Nodup ∧ hosts.length=109 ∧
 (∀q∈hosts,q∉cin::(src++(acc.take 138).drop 10++bank.take 127)):=by decide +kernel

theorem old_away:∀q∈ReorderedAFixed.hosts,q∉ports:=by decide +kernel

theorem fix(q a b:Wire)(ha:q≠a)(hb:q≠b):(Equiv.swap a b) q=q:=by
 simp [Equiv.swap_apply_def,ha,hb]

theorem old_fresh(q:Wire)(hq:q∈ReorderedAFixed.hosts):q∉wires AAliasesResearch.program:=by
 have away:q∉ports:=old_away q hq
 have ne(a:Wire)(ha:a∈ports):q≠a:=by intro eq;subst q;exact away ha
 have s:q∉wires AAliasesResearch.single:=AMiddleResearch.fresh_of_old q
  ((by
   intro bad
   have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownAMidStaged.cert
   exact ReorderedAFixed.off_middle q hq (Skip4.wires_mono_of_mem _ _ (fun _ h=>sub.subset h) bad)))
  (fix q 4757 4760 (ne _ (by decide)) (ne _ (by decide))) (ne _ (by decide))
 exact AAliasesResearch.fresh_of_single q s
  (fix q 4505 4243 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4506 4244 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4507 4245 (ne _ (by decide)) (ne _ (by decide)))
  (ne _ (by decide)) (ne _ (by decide))

theorem middle_fresh(q:Wire)(hq:q∈hosts):q∉wires AAliasesResearch.program:=by
 rcases List.mem_append.mp hq with hq|hq
 · exact old_fresh q hq
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
   · exact AAliasesResearch.ghost_free _ (by decide)
   · exact AAliasesResearch.ghost_free _ (by decide)
   · exact AAliasesResearch.ghost_free _ (by decide)
   · exact AAliasesResearch.low4_free
   · exact AAliasesResearch.low5_free
   · exact AAliasesResearch.low6_free

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component HighConsumedA109
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.HighConsumedA109Research
abbrev xs:List Wire:=ReorderedBPrefixResearch.src
abbrev ys:List Wire:=(ReorderedBPrefixResearch.acc.take 138).drop 10
abbrev cs:List Wire:=ReorderedBPrefixResearch.bank.take 127
abbrev hs:List Wire:=A109Research.hosts
abbrev cin:Wire:=ReorderedBPrefixResearch.cin
def ports:Fin 12→Wire:=![4367,4368,4369,4370,4635,4636,4637,4638,4496,4497,4498,4499]
def old:Program:=ReorderedGenericCache.consumedAdd 109 xs ys cs hs cin
def pre:Program:=old.take 308
def post:Program:=old.drop 337
def fast:Program:=pre++PlacedUniformAdder4Research.fastAt ports++post

theorem ports_inj:Function.Injective ports:=by decide +kernel

theorem window:(old.drop 308).take 29=PlacedUniformAdder4Research.originalAt ports:=by decide +kernel

theorem shape:old=pre++PlacedUniformAdder4Research.originalAt ports++post:=by
 rw [pre,post,←window,←List.take_add]
 exact (List.take_append_drop 337 old).symm

theorem pre_measurements:measurementCount pre=0:=by decide +kernel

theorem pre_fresh:∀q∈UniformAdderSpliceResearch.cs ports,q∉wires pre:=by
 have rs4_h:(UniformAdderSpliceResearch.cs ports).all (fun q=>!C163Touch.touched pre q)=true:=by decide +kernel
 intro q hq
 exact HighConsumedStreamResearch.untouched _ _ (by simpa using List.all_eq_true.mp rs4_h q hq)

theorem post_fresh:∀q∈UniformAdderSpliceResearch.ys ports,q∉wires post:=by
 have rs4_h:(UniformAdderSpliceResearch.ys ports).all (fun q=>!C163Touch.touched post q)=true:=by decide +kernel
 intro q hq
 exact HighConsumedStreamResearch.untouched _ _ (by simpa using List.all_eq_true.mp rs4_h q hq)

theorem toffoli:toffoliCount fast+3=toffoliCount old:=by
 have h:=congrArg toffoliCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [toffoliCount_append] at h
 have g:toffoliCount fast=toffoliCount pre+toffoliCount (PlacedUniformAdder4Research.fastAt ports)+toffoliCount post:=by
  simp only [fast,toffoliCount_append]
 omega

theorem measurements:measurementCount fast=measurementCount old:=by
 have h:=congrArg measurementCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [measurementCount_append] at h
 have g:measurementCount fast=measurementCount pre+measurementCount (PlacedUniformAdder4Research.fastAt ports)+measurementCount post:=by
  simp only [fast,measurementCount_append]
 omega


end ECDSAAdd.Entrant.HighConsumedA109Research


namespace ECDSAAdd.Entrant.HighConsumedA109Research
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop

theorem source_length:xs.length=128:=by decide +kernel

theorem target_length:ys.length=128:=by decide +kernel

theorem carry_length:cs.length=127:=by decide +kernel

theorem high_targets:ys.drop 124=UniformAdderSpliceResearch.ys ports:=by decide +kernel

theorem high_carries:∀q∈UniformAdderSpliceResearch.cs ports,q∈cs:=by
 intro q hq
 simp only [UniformAdderSpliceResearch.cs,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel

theorem high_word (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=109)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^128)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 109 H (976*H/1024)):
 regValue (UniformAdderSpliceResearch.ys ports)
  (run old [] (run (notRegister ys) [] s)).basis=0 ∨
 regValue (UniformAdderSpliceResearch.ys ports)
  (run old [] (run (notRegister ys) [] s)).basis=15:=by
 have v:=HighConsumedInputsResearch.inner_value 109 xs ys cs hs cin (by rw [source_length];decide) (by rw [target_length];decide)
   (by rw [carry_length];decide) (source_length.trans target_length.symm)
   (by rw [carry_length,target_length]) hn nd len fresh s [] hz hi H (976*H/1024) source target saved
 change regValue ys (run old [] (run (notRegister ys) [] s)).basis=
  (H+(2^ys.length-1-976*H/1024))%2^ys.length at v
 rw [target_length] at v
 rw [←high_targets,CuccaroStreamedSquareWideLayout.regValue_drop_div ys 124 (by rw [target_length];decide),v]
 have power:16*(2^124)=2^128:=by norm_num
 have a:=HighBorrowArithmeticResearch.borrow_remainder_high (2^124) H (by positivity)
  (show H<16*2^124 by simpa only [power] using hH)
 rw [power] at a
 by_cases h0:H=0
 · right;rw [a,if_pos h0]
 · left;rw [a,if_neg h0]

theorem inner_run_eq (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=109)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^128)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 109 H (976*H/1024)) (m:List Bool):
 run fast m (run (notRegister ys) [] s)=run old m (run (notRegister ys) [] s):=by
 let u:=run (notRegister ys) [] s
 have cys:∀q∈cs,q∉ys:=by
  intro q hq bad
  exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2
   (List.mem_append_right _ bad) hq
 have cu:∀q∈UniformAdderSpliceResearch.cs ports,u.basis q=false:=by
  intro q hq
  have hc:=high_carries q hq
  have off:q∉wires (notRegister ys):=by simpa only [notRegister_wires,List.mem_toFinset] using cys q hc
  exact (run_preserves_outside (notRegister ys) [] s q off).trans (hz q hc)
 have ready:regValue (UniformAdderSpliceResearch.ys ports)
   (run (pre++PlacedUniformAdder4Research.originalAt ports++post) [] u).basis=0 ∨
  regValue (UniformAdderSpliceResearch.ys ports)
   (run (pre++PlacedUniformAdder4Research.originalAt ports++post) [] u).basis=15:=by
  simpa only [←shape] using high_word s hn nd len fresh hz hi H hH source target saved
 have eq:=UniformAdderSpliceResearch.replace ports ports_inj pre post u m pre_measurements cu pre_fresh post_fresh ready
 simpa only [fast,←shape] using eq

def sub:Program:=notRegister ys++fast++notRegister ys

theorem sub_measurements:measurementCount sub=measurementCount (ReorderedConsumedSub.consumed 109 xs ys cs hs cin):=by
 simp only [sub,ReorderedConsumedSub.consumed,measurementCount_append,measurements,old]


theorem sub_run_eq (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=109)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^128)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 109 H (976*H/1024)) (m:List Bool):
 run sub m s=run (ReorderedConsumedSub.consumed 109 xs ys cs hs cin) m s:=by
 have eq:=CodexKnownOnesTail.Helpers.run_mid_congr (notRegister ys) fast old (notRegister ys) m s
  (notRegister_counts ys).2 measurements (fun r=>inner_run_eq s hn nd len fresh hz hi H hH source target saved r)
 simpa only [sub,ReorderedConsumedSub.consumed,old] using eq



end ECDSAAdd.Entrant.HighConsumedA109Research


end

-- Verified ABC18 optimization component HighA109Resources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HighConsumedA109Research

theorem support:wires fast⊆wires old:=by
 have q:=HighBorrowResourceResearch.placed_support ports
 have e:=congrArg wires shape
 simp only [wires_append] at e
 rw [fast,wires_append,wires_append,e]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem physical(h:GatePhysical old):GatePhysical fast:=by
 rw [shape] at h
 simp only [gatePhysical_append] at h
 change GatePhysical (pre++PlacedUniformAdder4Research.fastAt ports++post)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,HighBorrowResourceResearch.placed_physical ports ports_inj⟩,h.2⟩

theorem slots:Challenge.gateSlots fast+3=Challenge.gateSlots old:=by
 have h:=congrArg Challenge.gateSlots shape
 have q:=HighBorrowResourceResearch.placed_slots ports
 simp only [Challenge.gateSlots_append] at h
 have g:Challenge.gateSlots fast=Challenge.gateSlots pre+Challenge.gateSlots (PlacedUniformAdder4Research.fastAt ports)+Challenge.gateSlots post:=by
  simp only [fast,Challenge.gateSlots_append]
 omega

theorem sub_support:wires sub⊆wires (ReorderedConsumedSub.consumed 109 xs ys cs hs cin):=by
 have q:wires fast⊆wires (ReorderedGenericCache.consumedAdd 109 xs ys cs hs cin):=by simpa only [old] using support
 simp only [sub,ReorderedConsumedSub.consumed,wires_append]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem sub_physical(h:GatePhysical (ReorderedConsumedSub.consumed 109 xs ys cs hs cin)):GatePhysical sub:=by
 simp only [ReorderedConsumedSub.consumed,gatePhysical_append] at h
 change GatePhysical (notRegister ys++fast++notRegister ys)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,physical h.1.2⟩,h.2⟩

theorem sub_toffoli:toffoliCount sub+3=toffoliCount (ReorderedConsumedSub.consumed 109 xs ys cs hs cin):=by
 have q:=toffoli
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,toffoliCount_append]
 omega

theorem sub_slots:Challenge.gateSlots sub+3=Challenge.gateSlots (ReorderedConsumedSub.consumed 109 xs ys cs hs cin):=by
 have q:=slots
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,Challenge.gateSlots_append]
 omega
end ECDSAAdd.Entrant.HighConsumedA109Research


end

-- Verified ABC18 optimization component A109LowErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109LowEraseResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def low:List Wire:=[4505,4506,4507]
def erase(s:State):State:=EraseListProof.erase low s
def clear:Program:=[.CX 4243 4505,.CX 4244 4506,.CX 4245 4507,.CX 4243 4507]

theorem clear_eq_erase(s:State)(m:List Bool)
 (h4:s.basis 4505=s.basis 4243)(h5:s.basis 4506=s.basis 4244)
 (h6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243)):
 run clear m s=erase s:=by
 apply State.extensionality
 · simp [clear,run,erase,EraseListProof.phase]
 · funext q
   by_cases hq:q=4505
   · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h4]
   · by_cases hq5:q=4506
     · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h5]
     · by_cases hq6:q=4507
       · subst q
         cases a:s.basis 4243 <;>cases b:s.basis 4245 <;>
          simp_all [clear,run,erase,EraseListProof.basis,low,writeBit]
       · simp [clear,run,erase,EraseListProof.basis,low,writeBit,hq,hq5,hq6]

theorem restore(s:State)(m:List Bool)
 (h4:s.basis 4505=s.basis 4243)(h5:s.basis 4506=s.basis 4244)
 (h6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243)):
 run clear m (erase s)=s:=by
 apply State.extensionality
 · simp [clear,run,erase,EraseListProof.phase]
 · funext q
   by_cases hq:q=4505
   · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h4]
   · by_cases hq5:q=4506
     · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h5]
     · by_cases hq6:q=4507
       · subst q
         cases a:s.basis 4243 <;>cases b:s.basis 4245 <;>
          simp_all [clear,run,erase,EraseListProof.basis,low,writeBit]
       · simp [clear,run,erase,EraseListProof.basis,low,writeBit,hq,hq5,hq6]

theorem commute(P:Program)(m:List Bool)(s:State)(off:∀q∈low,q∉wires P):
 run P m (erase s)=erase (run P m s):=EraseListProof.commute low P m s off

theorem bit_same(s:State)(q:Wire)(off:q∉low):(erase s).basis q=s.basis q:=by
 simp [erase,EraseListProof.basis,off]





theorem zero(s:State)(q:Wire)(hq:q∈low):(erase s).basis q=false:=by
 simp [erase,EraseListProof.basis,hq]

theorem counts:toffoliCount clear=0 ∧ measurementCount clear=0 ∧ Challenge.gateSlots clear=4:=by decide +kernel

theorem physical:GatePhysical clear:=by simp [GatePhysical,clear,RecordedQuantum.PhysicalInstr,ProperGate]


end ECDSAAdd.Entrant.A109LowEraseResearch

end

-- Verified ABC18 optimization component A109LowErasedComposition
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109LowEraseResearch
open InverseCarryDevelop ReorderedBPrefixResearch ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem aliases_erased(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run KnownAMidStaged.body m s))
 (flag:s.basis 4762=false):
 run AAliasesResearch.program m (erase s)=erase (run KnownAMidStaged.body m s):=by
 have off:∀q∈low,q∉wires AAliasesResearch.program:=by
  intro q hq
  simp only [low,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact AAliasesResearch.low4_free
  · exact AAliasesResearch.low5_free
  · exact AAliasesResearch.low6_free
 rw [commute _ m s off,AAliasesResearch.equivalent H s m before after flag]

theorem forward_erased(head P:Program)(s:State)(m:List Bool)
 (off:∀q∈low,q∉wires P)
 (h4:(run head m s).basis 4505=(run head m s).basis 4243)
 (h5:(run head m s).basis 4506=(run head m s).basis 4244)
 (h6:(run head m s).basis 4507=((run head m s).basis 4245 ^^ (run head m s).basis 4243)):
 run (head++clear++P) m s=erase (run (head++P) m s):=by
 have mc:measurementCount clear=0:=counts.2.1
 simp only [run_cat,measurementCount_append,mc,Nat.add_zero]
 rw [clear_eq_erase _ _ h4 h5 h6,commute P _ _ off]

theorem suffix(P:Program)(s:State)(m:List Bool)(off:∀q∈low,q∉wires P)
 (h4:(run P m s).basis 4505=(run P m s).basis 4243)
 (h5:(run P m s).basis 4506=(run P m s).basis 4244)
 (h6:(run P m s).basis 4507=((run P m s).basis 4245 ^^ (run P m s).basis 4243)):
 run (P++clear) m (erase s)=run P m s:=by
 rw [run_cat,commute P m s off]
 exact restore _ _ h4 h5 h6


end ECDSAAdd.Entrant.A109LowEraseResearch

end

-- Verified ABC18 optimization component A109Raw
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

abbrev xs:List Wire:=src
abbrev ys:List Wire:=(acc.take 138).drop 10
abbrev cs:List Wire:=bank.take 127
def domain:List Wire:=cin::(xs++ys++cs)
def rawF:Program:=mappedAdd (mappedRead xs false) ys cs cin
def rawI:Program:=ReorderedConsumedSub.plain xs ys cs cin
def head:Program:=ReorderedAHead.head acc pad bank cin src
def top:Program:=A161Carry.buildPost acc pad bank cin src
def preInv:Program:=A161Carry.unbuildPre acc pad bank cin src
def F:Program:=head++A109LowEraseResearch.clear++rawF++top
def newF:Program:=head++A109LowEraseResearch.clear++ReorderedGenericCache.cachedAdd 109 xs ys cs hosts cin++top
def I:Program:=preInv++rawI
def newI:Program:=preInv++HighConsumedA109Research.sub
def topDomain:List Wire:=cin::(Acc.tx pad 161 (Acc.earlyTerm src false 32)++
 Acc.ty acc (Acc.earlyTerm src false 32)++Acc.tc bank 161 (Acc.earlyTerm src false 32))

theorem raw_lengths:xs.length=128 ∧ ys.length=128 ∧ cs.length=127:=by decide +kernel

theorem raw_nd:domain.Nodup :=
 RawDomainStructural390.sliced_nodup _ _ _ _ _ ReorderedBPrefixResearch.fit_nd 138 10 127

theorem raw_wires:wires rawF=domain.toFinset:=by
 rw [rawF,MixedLiteralAdderDevelop.read_add_eq]
 exact addInPlace_wires xs ys cs cin (by rw [raw_lengths.1,raw_lengths.2.1])
  (by rw [raw_lengths.2.1,raw_lengths.2.2])

theorem rawF_off(q:Wire)(hq:q∈hosts):q∉wires rawF:=by
 intro bad
 rw [raw_wires] at bad
 exact geometry.2.2 q hq (List.mem_toFinset.mp bad)

theorem rawI_off(q:Wire)(hq:q∈hosts):q∉wires rawI:=by
 have ysSub:ys.toFinset⊆domain.toFinset:=by
  intro w hw
  apply List.mem_toFinset.mpr
  have hy:w∈ys:=List.mem_toFinset.mp hw
  simp only [domain,List.mem_cons,List.mem_append]
  itauto
 have support:wires rawI⊆domain.toFinset:=by
  simp only [rawI,ReorderedConsumedSub.plain,wires_append,notRegister_wires]
  change (ys.toFinset∪wires rawF)∪ys.toFinset⊆domain.toFinset
  rw [raw_wires]
  exact Finset.union_subset (Finset.union_subset ysSub (Finset.Subset.refl _)) ysSub
 exact fun bad=>geometry.2.2 q hq (List.mem_toFinset.mp (support bad))

theorem top_away:∀q∈hosts,q∉topDomain:=by decide +kernel

theorem top_wires:wires top=topDomain.toFinset:=by
 have take:acc.take 161=acc:=by rw [←acc_length];exact List.take_length
 unfold top A161Carry.buildPost
 rw [take]
 exact Acc.op_wires acc pad bank cin 161 false (Acc.earlyTerm src false 32) acc_length
  (fits _ (A161NarrowAcc.terms_mem src).2.2.2)

theorem top_off(q:Wire)(hq:q∈hosts):q∉wires top:=by
 rw [top_wires]
 exact fun bad=>top_away q hq (List.mem_toFinset.mp bad)

theorem preInv_support:wires preInv⊆topDomain.toFinset:=by
 have take:acc.take 161=acc:=by rw [←acc_length];exact List.take_length
 have fit:=fits _ (A161NarrowAcc.terms_mem src).2.2.2
 unfold preInv A161Carry.unbuildPre
 rw [take]
 have r:=CodexNarrowTailResource.accSub_support 106 acc pad bank cin 161 (Acc.earlyTerm src false 32)
  acc_length fit.toFitsLen (by norm_num [Acc.earlyTerm])
 rw [Acc.op_wires acc pad bank cin 161 true (Acc.earlyTerm src false 32) acc_length fit] at r
 exact r

theorem preInv_off(q:Wire)(hq:q∈hosts):q∉wires preInv:=
 fun bad=>top_away q hq (List.mem_toFinset.mp (preInv_support bad))

theorem I_off(q:Wire)(hq:q∈hosts):q∉wires I:=by
 simp only [I,wires_append,Finset.mem_union,not_or]
 exact ⟨preInv_off q hq,rawI_off q hq⟩

theorem low_hosts(q:Wire)(hq:q∈A109LowEraseResearch.low):q∈hosts:=by
 simp only [A109LowEraseResearch.low,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel


end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109CacheFrames
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop MixedLiteralAdderDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem sub_frame(s:State)(m:List Bool)(H:Nat)(hH:H<2^128)
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hosts.map s.basis=ReorderedCacheBits.values 4 109 H (976*H/1024)):
 run HighConsumedA109Research.sub m s=
 scatterState hosts (List.replicate hosts.length false) (run rawI m s):=by
 have fast:=HighConsumedA109Research.sub_run_eq s raw_nd geometry.1 geometry.2.1 geometry.2.2
  hz hi H hH source target saved m
 rw [fast]
 exact ReorderedConsumedSub.frame 109 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
  raw_nd geometry.1 geometry.2.1 geometry.2.2 s m hz hi H (976*H/1024) source target saved

theorem inverse_frame(s:State)(m:List Bool)(H:Nat)(hH:H<2^128)
 (hz:∀q∈cs,(run preInv m s).basis q=false)(hi:(run preInv m s).basis cin=false)
 (source:regValue xs (run preInv m s).basis=H)
 (target:regValue ys (run preInv m s).basis=976*H/1024)
 (saved:hosts.map s.basis=ReorderedCacheBits.values 4 109 H (976*H/1024)):
 run newI m s=scatterState hosts (List.replicate hosts.length false) (run I m s):=by
 have same:hosts.map (run preInv m s).basis=hosts.map s.basis:=
  by
   apply List.map_congr_left
   intro q hq
   exact run_preserves_outside preInv m s q (preInv_off q hq)
 simp only [newI,I,ControlledBorrowResearch.run_cat]
 exact sub_frame (run preInv m s) _ H hH hz hi source target (same.trans saved)

theorem forward_frame(s:State)(m:List Bool)(H:Nat)
 (zero:∀q∈hosts,(run (head++A109LowEraseResearch.clear) (m.take (measurementCount (head++A109LowEraseResearch.clear))) s).basis q=false)
 (values:(((cs.drop 4).take 109).map (run (carryPrefix (4+109) xs ys cs cin) []
  (run (head++A109LowEraseResearch.clear) (m.take (measurementCount (head++A109LowEraseResearch.clear))) s)).basis)=
   ReorderedCacheBits.values 4 109 H (976*H/1024)):
 run newF m s=scatterState hosts (ReorderedCacheBits.values 4 109 H (976*H/1024)) (run F m s):=by
 have h:=CacheBetweenFrameResearch.forward (head++A109LowEraseResearch.clear) top 109 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  geometry.1 (fun q hq bad=>geometry.2.2 q hq (by simp only [List.mem_cons,List.mem_append];tauto))
  rawF_off top_off s m zero
 rw [values] at h
 exact h

theorem forward_measurements:measurementCount newF=measurementCount F:=by
 have h:=(ReorderedGenericCache.count_balance 109 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)).2.1
 simp only [newF,F,rawF,measurementCount_append]
 rw [h]


end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109ForwardErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem low_copies(H:Nat)(s:State)(ready:WReady acc pad bank cin src H s):
 s.basis 4505=s.basis 4243 ∧ s.basis 4506=s.basis 4244 ∧ s.basis 4507=(s.basis 4245 ^^ s.basis 4243):=by
 have cp:=LowWordRecovery.copies acc src s.basis (by rw [acc_length];decide)
  (by rw [source_length];decide) (by rw [ready.2.1];exact ready.1)
 have c4:s.basis 4505=s.basis 4243:=by
  simpa only [show src.getD 0 0=4243 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.1.symm
 have c5:s.basis 4506=s.basis 4244:=by
  simpa only [show src.getD 1 0=4244 from by decide +kernel,
   show acc.getD 5 0=4506 from by decide +kernel] using cp.2.1.symm
 refine ⟨c4,c5,?_⟩
 have c6:s.basis 4245=(s.basis 4507 ^^ s.basis 4505):=by
  simpa only [show src.getD 2 0=4245 from by decide +kernel,
   show acc.getD 6 0=4507 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.2.2
 rw [c6,←c4]
 simp [Bool.xor_assoc]

theorem plain_split:ReorderedAPlain.build acc pad bank cin src=head++(rawF++top):=by
 simpa only [head,rawF,top,List.append_assoc] using
  ReorderedABuild.plain_split acc pad bank cin src source_length

theorem rest_off(q:Wire)(hq:q∈A109LowEraseResearch.low):q∉wires (rawF++top):=by
 simp only [wires_append,Finset.mem_union,not_or]
 exact ⟨rawF_off q (low_hosts q hq),top_off q (low_hosts q hq)⟩

theorem head_copies(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 (run head m s).basis 4505=(run head m s).basis 4243 ∧
 (run head m s).basis 4506=(run head m s).basis 4244 ∧
 (run head m s).basis 4507=((run head m s).basis 4245 ^^ (run head m s).basis 4243):=by
 let u:=run (ReorderedAPlain.build acc pad bank cin src) m s
 have ready:WReady acc pad bank cin src (regValue src s.basis) u:=
  BRelocatedReadyResearch.plain_before s m hz hb hi ha
 have cp:=low_copies _ u ready
 have low(q:Wire)(hq:q∈A109LowEraseResearch.low):u.basis q=(run head m s).basis q:=by
  dsimp [u]
  rw [plain_split,run_cat]
  exact run_preserves_outside _ _ _ q (rest_off q hq)
 have frame:=ReorderedAHead.head_triple acc pad bank cin src acc_length (by have h:=source_length;omega)
  fits s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have away:∀q∈src,q∉acc:=by decide +kernel
 have source(q:Wire)(hq:q∈src):u.basis q=(run head m s).basis q:=by
  have h:= (regValue_eq_iff src _ _).mp ready.2.1 q hq
  exact h.trans (frame.2.2 q (away q hq)).symm
 rw [low 4505 (by decide),low 4506 (by decide),low 4507 (by decide),source 4243 (by decide +kernel),source 4244 (by decide +kernel),source 4245 (by decide +kernel)] at cp
 exact cp

theorem forward_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 run F m s=A109LowEraseResearch.erase (run (ReorderedAPlain.build acc pad bank cin src) m s):=by
 have cp:=head_copies s m hz hb hi ha
 have eq:=A109LowEraseResearch.forward_erased head (rawF++top) s m rest_off cp.1 cp.2.1 cp.2.2
 simpa only [F,plain_split,List.append_assoc] using eq

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109ForwardClean
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem old_plain_program_eq398 :
 ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src =
 ReorderedAPlain.build acc pad bank cin src := by
 have aa : ReorderedAFixed.acc=acc := by decide +kernel
 have ap : ReorderedAFixed.pad=pad := by decide +kernel
 have ab : ReorderedAFixed.bank=bank := by decide +kernel
 have ax : ReorderedAFixed.src=src := by decide +kernel
 have ai : ReorderedAFixed.L.core.cin=cin := by decide +kernel
 rw [aa,ap,ab,ax,ai]
 theorem old_plain_off398 (q : Wire) (hq : q ∈ ReorderedAFixed.hosts) :
 q ∉ wires (ReorderedAPlain.build acc pad bank cin src) := by
 rw [←old_plain_program_eq398]
 exact (ReorderedAFixed.off_plain q hq).1

theorem forward_zero(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedAFixed.hosts,s.basis q=false):
 ∀q∈hosts,(run F m s).basis q=false:=by
 rw [forward_erased s m hz hb hi ha]
 let u:=run (ReorderedAPlain.build acc pad bank cin src) m s
 have ready:WReady acc pad bank cin src (regValue src s.basis) u:=
  BRelocatedReadyResearch.plain_before s m hz hb hi ha
 intro q hq
 rcases List.mem_append.mp hq with hq|hq
 · rw [A109LowEraseResearch.bit_same _ q (by
    have away:=old_away q hq
    intro bad
    apply away
    simp only [A109LowEraseResearch.low,List.mem_cons,List.not_mem_nil,or_false] at bad
    rcases bad with rfl|rfl|rfl <;>decide)]
   exact (run_preserves_outside _ m s q (old_plain_off398 q hq)).trans (zero q hq)
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
   · rw [A109LowEraseResearch.bit_same _ _ (by decide)]
     simpa only [show acc.getD 0 0=4757 from by decide +kernel] using
      (LowWordRecovery.low_register_zero acc u.basis _ 0 (by decide)
       (by rw [acc_length];decide) ready.1)
   · rw [A109LowEraseResearch.bit_same _ _ (by decide)]
     simpa only [show acc.getD 1 0=4758 from by decide +kernel] using
      (LowWordRecovery.low_register_zero acc u.basis _ 1 (by decide)
       (by rw [acc_length];decide) ready.1)
   · rw [A109LowEraseResearch.bit_same _ _ (by decide)]
     simpa only [show acc.getD 2 0=4759 from by decide +kernel] using
      (LowWordRecovery.low_register_zero acc u.basis _ 2 (by decide)
       (by rw [acc_length];decide) ready.1)
   · exact A109LowEraseResearch.zero _ _ (by decide)
   · exact A109LowEraseResearch.zero _ _ (by decide)
   · exact A109LowEraseResearch.zero _ _ (by decide)

theorem prefix_zero(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedAFixed.hosts,s.basis q=false):
 ∀q∈hosts,(run (head++A109LowEraseResearch.clear) m s).basis q=false:=by
 have clean:=forward_zero s m hz hb hi ha zero
 intro q hq
 have off:q∉wires (rawF++top):=by
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨rawF_off q hq,top_off q hq⟩
 have eq:(run F m s).basis q=(run (head++A109LowEraseResearch.clear) m s).basis q:=by
  have partition:F=(head++A109LowEraseResearch.clear)++(rawF++top):=by simp only [F,List.append_assoc]
  rw [partition,run_cat]
  exact run_preserves_outside _ _ _ q off
 exact eq.symm.trans (clean q hq)

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109ForwardValues
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem x_in(q:Wire)(hq:q∈xs):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_left cs (List.mem_append_left ys hq))
theorem y_in(q:Wire)(hq:q∈ys):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_left cs (List.mem_append_right xs hq))
theorem c_in(q:Wire)(hq:q∈cs):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_right (xs++ys) hq)
theorem cin_in:cin∈domain:=List.mem_cons_self

theorem domain_away_low(q:Wire)(hq:q∈domain):q∉A109LowEraseResearch.low:=by
 intro bad
 exact geometry.2.2 q (low_hosts q bad) hq

theorem prefix_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 run (head++A109LowEraseResearch.clear) m s=A109LowEraseResearch.erase (run head m s):=by
 rw [run_cat]
 have cp:=head_copies s m hz hb hi ha
 exact A109LowEraseResearch.clear_eq_erase _ _ cp.1 cp.2.1 cp.2.2

theorem forward_values(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 (((cs.drop 4).take 109).map (run (carryPrefix (4+109) xs ys cs cin) []
  (run (head++A109LowEraseResearch.clear) m s)).basis)=
 ReorderedCacheBits.values 4 109 (regValue src s.basis) (976*regValue src s.basis/1024):=by
 let H:=regValue src s.basis
 let u:=run head m s
 let t:=run (head++A109LowEraseResearch.clear) m s
 have te:t=A109LowEraseResearch.erase u:=prefix_erased s m hz hb hi ha
 have hH:H<2^128:=by simpa only [H,source_length] using regValue_lt src s.basis
 have ready:(∀q∈cs,u.basis q=false) ∧ u.basis cin=false ∧ regValue xs u.basis=H ∧
  regValue ys u.basis=((2^138-48*H)%2^138)/1024:=by
  simpa only [cs,xs,ys,u,head,H] using
   ReorderedHeadArithmeticResearch.ready acc pad bank cin src acc_length source_length fits s m hz hb hi ha
 have eraseBit(q:Wire)(hq:q∈domain):t.basis q=u.basis q:=by
  rw [te]
  exact A109LowEraseResearch.bit_same _ q (domain_away_low q hq)
 have eraseReg(r:List Wire)(sub:∀q∈r,q∈domain):regValue r t.basis=regValue r u.basis:=
  regValue_congr _ _ _ (fun q hq=>eraseBit q (sub q hq))
 have sy:regValue ys t.basis=((2^138-48*H)%2^138)/1024:=
  (eraseReg ys y_in).trans ready.2.2.2
 have sh:regValue xs t.basis=H:=
  (eraseReg xs x_in).trans ready.2.2.1
 have sb:∀q∈cs,t.basis q=false:=by
  intro q hq
  exact (eraseBit q (c_in q hq)).trans (ready.1 q hq)
 have si:t.basis cin=false:=
  (eraseBit cin cin_in).trans ready.2.1
 exact ReorderedCacheBits.forward_values 4 109 H (((2^138-48*H)%2^138)/1024) (976*H/1024)
  xs ys cs cin t (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide) raw_nd sb si sh sy (fun j hj=>by
   simpa only [show 128+10=138 by decide] using
    ReorderedCacheArithmetic.high_add_low 128 (4+j+1) H (by omega) hH)

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109InverseReady
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem pre_raw_ready(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 (∀q∈cs,(run preInv m s).basis q=false) ∧ (run preInv m s).basis cin=false ∧
 regValue xs (run preInv m s).basis=H ∧ regValue ys (run preInv m s).basis=976*H/1024:=by
 have h:=ReorderedPreInverseArithmeticResearch.ready acc pad bank cin src acc_length source_length fits s m
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 (by rw [ready.2.1];exact ready.1)
 simpa only [preInv,xs,ys,cs,ready.2.1] using h

theorem scattered_erased_domain(s:State)(vs:List Bool)(q:Wire)(hq:q∈domain):
 (scatterState hosts vs (A109LowEraseResearch.erase s)).basis q=s.basis q:=by
 rw [scatter_outside hosts vs _ q (by intro bad;exact geometry.2.2 q bad hq)]
 exact A109LowEraseResearch.bit_same s q (domain_away_low q hq)

theorem inverse_ready(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 let vs:=ReorderedCacheBits.values 4 109 H (976*H/1024)
 let t:=scatterState hosts vs (A109LowEraseResearch.erase s)
 run newI m t=scatterState hosts (List.replicate hosts.length false) (run I m t):=by
 dsimp only
 let vs:=ReorderedCacheBits.values 4 109 H (976*H/1024)
 let t:=scatterState hosts vs (A109LowEraseResearch.erase s)
 have hH:H<2^128:=by rw [←ready.2.1];simpa only [source_length] using regValue_lt src s.basis
 have commute:run preInv m t=scatterState hosts vs (A109LowEraseResearch.erase (run preInv m s)):=by
  rw [show t=scatterState hosts vs (A109LowEraseResearch.erase s) from rfl,
   run_scatter preInv hosts vs _ _ preInv_off,
   A109LowEraseResearch.commute preInv m s (fun q hq=>preInv_off q (low_hosts q hq))]
 have bits(q:Wire)(hq:q∈domain):(run preInv m t).basis q=(run preInv m s).basis q:=by
  rw [commute]
  exact scattered_erased_domain _ vs q hq
 have regs(r:List Wire)(sub:∀q∈r,q∈domain):regValue r (run preInv m t).basis=regValue r (run preInv m s).basis:=
  regValue_congr _ _ _ (fun q hq=>bits q (sub q hq))
 have rr:=pre_raw_ready H s m ready
 have saved:hosts.map t.basis=vs:=scatter_saved_map hosts vs _ geometry.1
  (by simp only [vs,ReorderedCacheBits.values,List.length_map,geometry.2.1,List.length_range])
 apply inverse_frame t m H hH
 · intro q hq
   rw [bits q (c_in q hq)]
   exact rr.1 q hq
 · rw [bits cin cin_in]
   exact rr.2.1
 · rw [regs xs x_in]
   exact rr.2.2.1
 · rw [regs ys y_in]
   exact rr.2.2.2
 · exact saved

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109MiddleErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev oldF:Program:=ReorderedAPlain.build acc pad bank cin src
abbrev oldM:Program:=KnownAMidStaged.body
abbrev M:Program:=AAliasesResearch.program

theorem measurements:measurementCount F=measurementCount oldF:=by
 rw [oldF,plain_split]
 simp only [F,measurementCount_append,A109LowEraseResearch.counts.2.1,Nat.add_zero,Nat.zero_add,List.append_assoc]

theorem middle_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 middleState F M s m=A109LowEraseResearch.erase (middleState oldF oldM s m):=by
 unfold middleState
 rw [measurements,AAliasesResearch.counts.2.1,forward_erased s _ hz hb hi ha]
 exact A109LowEraseResearch.aliases_erased (regValue src s.basis) _ _
  (BRelocatedReadyResearch.plain_before s _ hz hb hi ha) after flag

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109Restore
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem rawI_eq:rawI=Acc.op (acc.take 138) pad bank cin 138 true (Acc.earlyTerm src false 10):=by
 simp only [rawI,ReorderedConsumedSub.plain,Acc.op,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,
  source_length,Bool.false_eq_true,ite_false,Nat.sub_self,List.take_zero,List.append_nil,
  MixedLiteralAdderDevelop.read_add_eq,subInPlace]
 rfl

theorem I_source(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 ∀q∈src,(run I m s).basis q=s.basis q:=by
 have hH:regValue src s.basis<2^128:=by simpa only [source_length] using regValue_lt src s.basis
 have pre:=A161Carry.unbuildPre_triple acc pad bank cin src acc_length source_length fits s.basis
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2
 have sub:=ReorderedAcc.op_mod_prefix_triple acc pad bank cin 161 138 (Acc.earlyTerm src false 10)
  acc_length (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.1)
  (by simp only [Acc.earlyTerm,source_length];decide) (by norm_num [Acc.earlyTerm])
  s.basis ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 true (976*regValue src s.basis)
  (by norm_num at hH ⊢;omega)
 have frame:=(pre.seq sub) s m ⟨by rw [ready.2.1];exact ready.1,fun _ _=>rfl⟩
 have eq:I=A161Carry.unbuildPre acc pad bank cin src++Acc.op (acc.take 138) pad bank cin 138 true (Acc.earlyTerm src false 10):=by
  rw [I,rawI_eq];rfl
 have away:∀q∈src,q∉acc:=by decide +kernel
 intro q hq
 rw [eq]
 exact frame.2.2 q (away q hq)

theorem restored(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 run (I++A109LowEraseResearch.clear) m (A109LowEraseResearch.erase s)=run I m s:=by
 have cp:=low_copies H s ready
 have low(q:Wire)(hq:q∈A109LowEraseResearch.low):(run I m s).basis q=s.basis q:=
  run_preserves_outside I m s q (I_off q (low_hosts q hq))
 have source:=I_source H s m ready
 apply A109LowEraseResearch.suffix I s m (fun q hq=>I_off q (low_hosts q hq))
 · rw [low 4505 (by decide),source 4243 (by decide +kernel)]
   exact cp.1
 · rw [low 4506 (by decide),source 4244 (by decide +kernel)]
   exact cp.2.1
 · rw [low 4507 (by decide),source 4245 (by decide +kernel),source 4243 (by decide +kernel)]
   exact cp.2.2

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109UnbuildSplit
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev tail:Program:=ReorderedAUnbuild.after acc pad bank cin src

theorem unbuild_split:ReorderedAPlain.unbuild acc pad bank cin src=I++tail:=by
 simpa only [I,preInv,rawI,xs,ys,cs,tail] using ReorderedAUnbuild.plain_split acc pad bank cin src source_length

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109ErasedSuffix
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem erased_suffix(H:Nat)(u:State)(m:List Bool)(ready:WReady acc pad bank cin src H u):
 run (I++A109LowEraseResearch.clear++tail) m (A109LowEraseResearch.erase u)=run (I++tail) m u:=by
 exact ClearContextResearch.suffix I A109LowEraseResearch.clear tail A109LowEraseResearch.counts.2.1
  (A109LowEraseResearch.erase u) u m (restored H u m ready)


end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109PlainLoop
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem plain_loop(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run (F++M++(I++A109LowEraseResearch.clear++tail)) m s=
 run (oldF++oldM++ReorderedAPlain.unbuild acc pad bank cin src) m s:=by
 have eq:=middle_erased s m hz hb hi ha after flag
 apply ClearContextResearch.projected F M oldF oldM (I++A109LowEraseResearch.clear++tail)
  (ReorderedAPlain.unbuild acc pad bank cin src) A109LowEraseResearch.erase s m measurements
  AAliasesResearch.counts.2.1 eq
 exact (erased_suffix _ _ _ after).trans
  (congrArg (fun P=>run P (m.drop (measurementCount oldF+measurementCount oldM))
   (middleState oldF oldM s m)) unbuild_split.symm)


end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109CacheLoop
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem cache_loop(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedAFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run (newF++M++newI) m s=run (F++M++I) m s:=by
 let H:=regValue src s.basis
 let vs:=ReorderedCacheBits.values 4 109 H (976*H/1024)
 have mid:=middle_erased s m hz hb hi ha after flag
 have forward:=forward_frame s (m.take (measurementCount F)) H
  (prefix_zero s _ hz hb hi ha zero) (forward_values s _ hz hb hi ha)
 apply CacheFromCleanForwardResearch.equivalent F newF M I newI hosts vs
  forward_measurements middle_fresh I_off geometry.1 s m
  (forward_zero s _ hz hb hi ha zero) forward
 rw [mid]
 exact inverse_ready H (middleState oldF oldM s m) _ after

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109Core
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def core:Program:=(newF++M++newI)++(A109LowEraseResearch.clear++tail)

theorem inverse_measurements:measurementCount newI=measurementCount I:=by
 have h:=ReorderedConsumedSub.measurement_eq 109 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide)
 have eq:measurementCount HighConsumedA109Research.sub=measurementCount rawI:=
  HighConsumedA109Research.sub_measurements.trans h
 simp only [newI,I,measurementCount_append,eq]

theorem prefix_measurements:measurementCount (newF++M++newI)=measurementCount (F++M++I):=by
 simp only [measurementCount_append,forward_measurements,inverse_measurements]

theorem core_plain(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedAFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run core m s=run (oldF++oldM++ReorderedAPlain.unbuild acc pad bank cin src) m s:=by
 have eq:=ClearContextResearch.append_at (newF++M++newI) (F++M++I) (A109LowEraseResearch.clear++tail)
  s m prefix_measurements (cache_loop s m hz hb hi ha zero after flag)
 have shape:(F++M++I)++(A109LowEraseResearch.clear++tail)=F++M++(I++A109LowEraseResearch.clear++tail):=by
  have g(A B C D E:Program):(A++B++C)++(D++E)=A++B++(C++D++E):=by simp only [List.append_assoc]
  exact g F M I A109LowEraseResearch.clear tail
 exact eq.trans ((congrArg (fun P=>run P m s) shape).trans (plain_loop s m hz hb hi ha after flag))

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component AKnownMiddle
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.AKnownMiddleResearch
open ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked

theorem measurements:measurementCount KnownAMidStaged.body=measurementCount A161Low4FixedFold.checked.out:=
 (KnownSparseFold.Cert.counts _ _ _ _ _ KnownAMidStaged.cert).2

theorem equivalent(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank L.core.cin src H s):
 run KnownAMidStaged.body m s=run A161Low4FixedFold.checked.out m s:=by
 have z:KnownSparseFold.Zero KnownAMidStaged.known0 s:=by
  intro u hu
  rcases ReorderedKnownA.guard u hu with ⟨_,_,hb⟩
  exact hb.elim (fun h=>before.2.2.2.1 u h) (fun h=>h.symm ▸ before.2.2.2.2)
 exact (KnownSparseFold.Cert.correct _ _ _ _ _ KnownAMidStaged.cert s m z).1

theorem middle_eq(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis L.core.cin=false)(ha:regValue acc s.basis=0):
 middleState (ReorderedAPlain.build acc pad bank L.core.cin src) KnownAMidStaged.body s m=
 middleState (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out s m:=by
 unfold middleState
 rw [measurements]
 exact equivalent _ _ _ (Ghost3CacheA.plain_ready s _ hz hb hi ha)


end ECDSAAdd.Entrant.AKnownMiddleResearch

end

-- Verified ABC18 optimization component A109Frame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.A109Research
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked
abbrev p:=ReorderedAFixed.p
theorem core_frame(base:BasisState)(hc:L.PairClean base)(hsum:base q=false)(hV:base r=false)(hP:base p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) core
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hzFull:∀u∈accZ L,s.basis u=false:=by
  intro u hu
  rcases accZ_mem L u hu with hu|hu
  · exact (regValue_zero _ _).mp clean.pad u hu
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>hzFull u ((FullPadDevelop.pad_sublist L).subset hu)
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue acc s.basis=0:=ghostAcc_zero L s.basis clean
 have qz:s.basis q=false:=(hf.2 q (by decide)).trans hsum
 have rz:s.basis r=false:=(hf.2 r (by decide)).trans hV
 have pz:s.basis p=false:=(hf.2 p (by decide)).trans hP
 have zeroU:∀u∈hs,s.basis u=false:=fun u hu=>
  (hf.2 u (A161Low4FixedFold.hostClean base hc hd u hu).1).trans (A161Low4FixedFold.hostClean base hc hd u hu).2
 have zeroOld:∀u∈ReorderedAFixed.hosts,s.basis u=false:=by
  change ∀u∈q::r::p::hs,s.basis u=false
  rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons]
  exact ⟨qz,rz,pz,zeroU⟩
 have offHs:∀u∈hs,u∉wires (ReorderedAPlain.build acc pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (by change u∈q::r::p::hs;simp only [List.mem_cons];exact Or.inr (Or.inr (Or.inr hu)))).1
 have goodOriginal:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) (A161Low4Fold.aMiddle L g) s m):=by
  rw [ReorderedARetape.a_middle_eq acc pad bank L.core.cin src (A161Low4Fold.aMiddle L g)
   lengths.1 lengths.2.2.2 fits s m hz hb clean.cin ha]
  exact good_old base hc O hO s _ hf
 have middleEq:=A161Low4FixedFold.cert100.middle_eq hs (A161Low4Fold.aMiddle L g) A161Low4FixedFold.checked.out
  (ReorderedAPlain.build acc pad bank L.core.cin src) s m zeroU offHs
 have good:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out s m):=by
  rw [middleEq]
  exact goodOriginal
 have knownEq:=AKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
 have goodKnown:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) KnownAMidStaged.body s m):=by
  rw [knownEq]
  exact good
 have buildFrame:=ReorderedAPlain.build_triple acc pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
  s.basis hz hb clean.cin s (m.take (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  ⟨ha,fun _ _=>rfl⟩
 have flag:(run (ReorderedAPlain.build acc pad bank L.core.cin src)
  (m.take (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src))) s).basis 4762=false:=
  (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
 have cachedNew:=core_plain s m hz hb clean.cin ha zeroOld goodKnown flag
 have midEq:run KnownAMidStaged.body (m.drop (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s)=
  run A161Low4FixedFold.checked.out (m.drop (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using knownEq
 have ctxt:=ReorderedKnownA.context_eq
  (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out KnownAMidStaged.body
  (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m AKnownMiddleResearch.measurements midEq
 have cached:=cachedNew.trans ctxt
 have middleReplace:=A161Low4FixedFold.cert100.surround_eq hs (A161Low4Fold.aMiddle L g) A161Low4FixedFold.checked.out
  (ReorderedAPlain.build acc pad bank L.core.cin src) (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m zeroU offHs
 have eq:run core m s=run (ReorderedAPlain.build acc pad bank L.core.cin src++A161Low4Fold.aMiddle L g++
  ReorderedAPlain.unbuild acc pad bank L.core.cin src) m s:=cached.trans middleReplace
 exact transport _ s _ _ eq (plain_frame base hc O hO s m hf)



end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109Sign
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.A109SignResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=A109Research.hosts
abbrev p:=ReorderedAFixed.p

def suffix:Program:=A109LowEraseResearch.clear++
 ReorderedGenericCache.cachedAdd 109 A109Research.xs A109Research.ys A109Research.cs hosts L.core.cin++
 A109Research.top++A109Research.M++A109Research.newI++A109LowEraseResearch.clear++A109Research.tail

def loop:Program:=SignAHead.head++suffix

theorem loop_eq(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p)
 (s:State)(m:List Bool)(hf:SquareFrame L.core.out base O s.basis):
 run loop m s=run A109Research.core
  (SignRetape.tape SignAHead.head (ReorderedAHead.head acc pad bank L.core.cin src) m) s:=by
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=by
  intro u hu
  have hu':u∈accZ L:=(FullPadDevelop.pad_sublist L).subset hu
  rcases accZ_mem L u hu' with hu'|hu'
  · exact (regValue_zero _ _).mp clean.pad u hu'
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu')
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue acc s.basis=0:=ghostAcc_zero L s.basis clean
 have h:∀a b:List Bool,run SignAHead.head a s=run (ReorderedAHead.head acc pad bank L.core.cin src) b s:=by
  intro a b
  exact ReorderedFrameUnique.program_eq acc s.basis 0 ((2^138-48*regValue src s.basis)%2^138) _ _
   (SignAHead.frame s.basis hz hb clean.cin)
   (ReorderedAHead.head_triple acc pad bank L.core.cin src lengths.1 (by decide) fits s.basis hz hb clean.cin)
   s a b ⟨ha,fun _ _=>rfl⟩
 have eq:=SignRetape.replace SignAHead.head (ReorderedAHead.head acc pad bank L.core.cin src) suffix s m h
 simpa only [loop,suffix,A109Research.core,A109Research.newF,A109Research.head,A109Research.xs,
  A109Research.ys,A109Research.cs,List.append_assoc] using eq


theorem frame(base:BasisState)(hc:L.PairClean base)(hsum:base q=false)(hV:base r=false)(hP:base p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have e:=loop_eq base hc O hO s m hf
 have old:=A109Research.core_frame base hc hsum hV hP hd O hO s (SignRetape.tape SignAHead.head (ReorderedAHead.head acc pad bank L.core.cin src) m) hf
 exact ReorderedAFixed.transport _ s _ _ e old

def fold:Program:=loop

def rawBody:Program:=measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)
theorem raw_body_frame (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base g=false → M=0) (hd:base d=false) :
 Triple (SquareFrame L.core.out base O) rawBody
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base g))) := by
 have hb:M^2<2^256:=by simpa using square_bound M 128 hM
 have vZero:base (eV L)=false:=eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
 have pZero:base (spare L)=false:=spare_zero L hw base M hP
 have ff : ∀ O, O<SquareReduction.p →
  Triple (SquareFrame L.core.out base O) fold
   (SquareFrame L.core.out base (((if base g then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base
    else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) :=
  fun O hO=>frame base hc hzero vZero pZero hd O hO
 exact A161Low4Body.body_frame L hw hn g A161Low4FixedFold.ready.1 base M hM hP hc hzero O hO hg fold ff


def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin

theorem body_frame (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base g=false → M=0) (hd:base d=false) :
 Triple (SquareFrame L.core.out base O) body
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base g))) := by
 intro s m hf
 have f:=raw_body_frame base M hM hP hc hzero O hO hg hd s (m.take (measurementCount rawBody)) hf
 have hz:(run rawBody (m.take (measurementCount rawBody)) s).basis L.core.cin=false:=
  (f.2.2 L.core.cin (by decide)).trans hc.cin
 have eq:run body m s=run rawBody (m.take (measurementCount rawBody)) s:=by
  rw [body,run_append,ReorderedRecordPadding.run_zero 7 L.core.cin _ _ hz]
 exact ReorderedAFixed.transport _ s _ _ eq f


end ECDSAAdd.Entrant.A109SignResearch

end

-- Verified ABC18 optimization component A109Counts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109SignResearch
open ReorderedBPrefixResearch A109Research Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem loop_counts:toffoliCount loop+3=toffoliCount HighSignAResearch.loop ∧
 measurementCount loop=measurementCount HighSignAResearch.loop:=by
 have aa:ReorderedAFixed.acc=acc:=by decide +kernel
 have ap:ReorderedAFixed.pad=pad:=by decide +kernel
 have ab:ReorderedAFixed.bank=bank:=by decide +kernel
 have ax:ReorderedAFixed.src=src:=by decide +kernel
 have ai:ReorderedAFixed.L.core.cin=L.core.cin:=by decide +kernel
 have nc:=ReorderedGenericCache.count_balance 109 xs ys cs A109Research.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
 have oc:=ReorderedGenericCache.count_balance 106 xs ys cs Ghost3CacheA.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
 have ni:=HighConsumedA109Research.sub_toffoli
 have nm:=HighConsumedA109Research.sub_measurements
 have oi:=HighUnbuildAResearch.toffoli acc rfl
 have om:=HighUnbuildAResearch.measurements acc rfl
 have mt:=AAliasesResearch.counts.1
 have mm:=AAliasesResearch.counts.2.1
 have ot:=GhostRelocatedKnown.A.counts.1
 have omid:=GhostRelocatedKnown.A.counts.2
 have nt:=notRegister_counts ys
 simp only [ReorderedConsumedSub.consumed,toffoliCount_append,measurementCount_append] at ni nm oi om
 simp only [ReorderedAUnbuild.unbuild,ReorderedConsumedSub.consumed,toffoliCount_append,measurementCount_append] at oi om
 simp only [loop,suffix,newI,preInv,top,tail,M,HighSignAResearch.loop,HighSignAResearch.suffix,
  toffoliCount_append,measurementCount_append,A109LowEraseResearch.counts.1,A109LowEraseResearch.counts.2.1]
 try rw [xs] at *
 try rw [ys] at *
 try rw [cs] at *
 try rw [HighConsumedA109Research.xs] at *
 try rw [HighConsumedA109Research.ys] at *
 try rw [HighConsumedA109Research.cs] at *
 try rw [HighConsumedA109Research.cin] at *
 try rw [HighConsumedA109Research.hs] at *
 try rw [ReorderedBPrefixResearch.cin] at *
 try rw [AAliasesResearch.original] at *
 try rw [Ghost3CacheA.middle] at *
 try rw [GhostRelocatedKnown.A.original] at *
 try rw [HighSignAResearch.hosts] at *
 try rw [A109SignResearch.hosts] at *
 try rw [aa] at *
 try rw [ap] at *
 try rw [ab] at *
 try rw [ax] at *
 try rw [ai] at *
 try rw [xs] at *
 try rw [ys] at *
 try rw [cs] at *
 try rw [HighConsumedA109Research.xs] at *
 try rw [HighConsumedA109Research.ys] at *
 try rw [HighConsumedA109Research.cs] at *
 try rw [HighConsumedA109Research.cin] at *
 try rw [HighConsumedA109Research.hs] at *
 try rw [ReorderedBPrefixResearch.cin] at *
 try rw [AAliasesResearch.original] at *
 try rw [Ghost3CacheA.middle] at *
 try rw [GhostRelocatedKnown.A.original] at *
 try rw [HighSignAResearch.hosts] at *
 try rw [A109SignResearch.hosts] at *
 try rw [aa] at *
 try rw [ap] at *
 try rw [ab] at *
 try rw [ax] at *
 try rw [ai] at *
 exact ⟨by omega,by omega⟩

 theorem body_counts:toffoliCount body+3=toffoliCount HighSignAResearch.body ∧
 measurementCount body=measurementCount HighSignAResearch.body:=by
 have h:=loop_counts
 simp only [body,rawBody,fold,HighSignAResearch.body,HighSignAResearch.rawBody,HighSignAResearch.fold,
  toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩


end ECDSAAdd.Entrant.A109SignResearch

end

-- Verified ABC18 optimization component A109Slots
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109SignResearch
open ReorderedBPrefixResearch A109Research Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Challenge.gateSlots
 theorem loop_slots:gateSlots loop+12=gateSlots HighSignAResearch.loop:=by
 have aa:ReorderedAFixed.acc=acc:=by decide +kernel
 have ap:ReorderedAFixed.pad=pad:=by decide +kernel
 have ab:ReorderedAFixed.bank=bank:=by decide +kernel
 have ax:ReorderedAFixed.src=src:=by decide +kernel
 have ai:ReorderedAFixed.L.core.cin=L.core.cin:=by decide +kernel
 have nc:=ReorderedSlots.cache 109 xs ys cs A109Research.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide) geometry.2.1
 have oc:=ReorderedSlots.cache 106 xs ys cs Ghost3CacheA.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide) Ghost3CacheA.geometry.2.1
 have ni:=HighConsumedA109Research.sub_slots
 have oi:=HighUnbuildAResearch.slots acc rfl
 have mid:=AAliasesResearch.counts.2.2
 have oldmid:=RelocateResources.slots GhostRelocatedKnown.ports KnownAMidStaged.body
 simp only [ReorderedConsumedSub.consumed,gateSlots_append] at ni
 simp only [ReorderedAUnbuild.unbuild,ReorderedConsumedSub.consumed,gateSlots_append] at oi
 simp only [loop,suffix,newI,preInv,top,tail,M,HighSignAResearch.loop,HighSignAResearch.suffix,
  gateSlots_append,A109LowEraseResearch.counts.2.2]
 try rw [xs] at *
 try rw [ys] at *
 try rw [cs] at *
 try rw [HighConsumedA109Research.xs] at *
 try rw [HighConsumedA109Research.ys] at *
 try rw [HighConsumedA109Research.cs] at *
 try rw [HighConsumedA109Research.cin] at *
 try rw [HighConsumedA109Research.hs] at *
 try rw [ReorderedBPrefixResearch.cin] at *
 try rw [AAliasesResearch.original] at *
 try rw [Ghost3CacheA.middle] at *
 try rw [GhostRelocatedKnown.A.program] at *
 try rw [GhostRelocatedKnown.A.original] at *
 try rw [HighSignAResearch.hosts] at *
 try rw [A109SignResearch.hosts] at *
 try rw [aa] at *
 try rw [ap] at *
 try rw [ab] at *
 try rw [ax] at *
 try rw [ai] at *
 try rw [xs] at *
 try rw [ys] at *
 try rw [cs] at *
 try rw [HighConsumedA109Research.xs] at *
 try rw [HighConsumedA109Research.ys] at *
 try rw [HighConsumedA109Research.cs] at *
 try rw [HighConsumedA109Research.cin] at *
 try rw [HighConsumedA109Research.hs] at *
 try rw [ReorderedBPrefixResearch.cin] at *
 try rw [AAliasesResearch.original] at *
 try rw [Ghost3CacheA.middle] at *
 try rw [GhostRelocatedKnown.A.program] at *
 try rw [GhostRelocatedKnown.A.original] at *
 try rw [HighSignAResearch.hosts] at *
 try rw [A109SignResearch.hosts] at *
 try rw [aa] at *
 try rw [ap] at *
 try rw [ab] at *
 try rw [ax] at *
 try rw [ai] at *
 generalize gateSlots (ReorderedGenericCache.cachedAdd 109 src ((acc.take 138).drop 10) (bank.take 127) A109Research.hosts L.core.cin) = count0 at *
 generalize gateSlots (ReorderedGenericCache.consumedAdd 109 src ((acc.take 138).drop 10) (bank.take 127) A109Research.hosts L.core.cin) = count1 at *
 generalize gateSlots (ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin) = count2 at *
 generalize gateSlots (ReorderedGenericCache.consumedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin) = count3 at *
 generalize gateSlots (mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) L.core.cin) = count4 at *
 generalize gateSlots (AAliasesResearch.program) = count5 at *
 generalize gateSlots (KnownAMidStaged.body) = count6 at *
 generalize gateSlots (RelocateThreeGhosts.program GhostRelocatedKnown.ports KnownAMidStaged.body) = count7 at *
 generalize gateSlots (HighConsumedA109Research.sub) = count8 at *
 generalize gateSlots (notRegister ((acc.take 138).drop 10)) = count9 at *
 generalize gateSlots (HighUnbuildAResearch.unbuild acc) = count10 at *
 generalize gateSlots (A161Carry.unbuildPre acc pad bank L.core.cin src) = count11 at *
 generalize gateSlots (ReorderedAUnbuild.after acc pad bank L.core.cin src) = count12 at *
 generalize gateSlots (A161Carry.buildPost acc pad bank L.core.cin src) = count13 at *
 generalize gateSlots (SignAHead.head) = count14 at *
 omega

 theorem body_slots:gateSlots body+12=gateSlots HighSignAResearch.body:=by
 have h:=loop_slots
 simp only [body,rawBody,fold,HighSignAResearch.body,HighSignAResearch.rawBody,HighSignAResearch.fold,gateSlots_append]
 omega


end ECDSAAdd.Entrant.A109SignResearch

end

-- Verified ABC18 optimization component A109Scope
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires
abbrev S:=wires HighSignAResearch.body
def oldPrefix:Program:=SignAHead.head++ReorderedGenericCache.cachedAdd 106 ReorderedAFixed.src ((ReorderedAFixed.acc.take 138).drop 10)
 (ReorderedAFixed.bank.take 127) Ghost3CacheA.hosts ReorderedAFixed.L.core.cin

theorem old_prefix_support:wires oldPrefix⊆S:=by
 intro q h
 simp only [oldPrefix,wires_append,Finset.mem_union] at h
 change q∈wires HighSignAResearch.body
 simp only [HighSignAResearch.body,HighSignAResearch.rawBody,HighSignAResearch.fold,
  HighSignAResearch.loop,HighSignAResearch.suffix,wires_append,Finset.mem_union]
 itauto

theorem old_middle_support:wires GhostRelocatedKnown.A.program⊆S:=by
 intro q h
 change q∈wires HighSignAResearch.body
 simp only [HighSignAResearch.body,HighSignAResearch.rawBody,HighSignAResearch.fold,
  HighSignAResearch.loop,HighSignAResearch.suffix,Ghost3CacheA.middle,wires_append,Finset.mem_union]
 tauto

def domainSelected396 : Program := [
 .CX 4243 4505,
 .CX 4244 4506,
 .CX 4245 4507,
 .CX 4246 4508,
 .CX 4247 4509,
 .CX 4248 4510,
 .CX 4249 4511,
 .CX 4250 4512,
 .CX 4251 4513,
 .CX 4252 4514,
 .CX 4253 4515,
 .CX 4254 4516,
 .CX 4255 4517,
 .CX 4256 4518,
 .CX 4257 4519,
 .CX 4258 4520,
 .CX 4259 4521,
 .CX 4260 4522,
 .CX 4261 4523,
 .CX 4262 4524,
 .CX 4263 4525,
 .CX 4264 4526,
 .CX 4265 4527,
 .CX 4266 4528,
 .CX 4267 4529,
 .CX 4268 4530,
 .CX 4269 4531,
 .CX 4270 4532,
 .CX 4271 4533,
 .CX 4272 4534,
 .CX 4273 4535,
 .CX 4274 4536,
 .CX 4275 4537,
 .CX 4276 4538,
 .CX 4277 4539,
 .CX 4278 4540,
 .CX 4279 4541,
 .CX 4280 4542,
 .CX 4281 4543,
 .CX 4282 4544,
 .CX 4283 4545,
 .CX 4284 4546,
 .CX 4285 4547,
 .CX 4286 4548,
 .CX 4287 4549,
 .CX 4288 4550,
 .CX 4289 4551,
 .CX 4290 4552,
 .CX 4291 4553,
 .CX 4292 4554,
 .CX 4293 4555,
 .CX 4294 4556,
 .CX 4295 4557,
 .CX 4296 4558,
 .CX 4297 4559,
 .CX 4298 4560,
 .CX 4299 4561,
 .CX 4300 4562,
 .CX 4301 4563,
 .CX 4302 4564,
 .CX 4303 4565,
 .CX 4304 4566,
 .CX 4305 4567,
 .CX 4306 4568,
 .CX 4307 4569,
 .CX 4308 4570,
 .CX 4309 4571,
 .CX 4310 4572,
 .CX 4311 4573,
 .CX 4312 4574,
 .CX 4313 4575,
 .CX 4314 4576,
 .CX 4315 4577,
 .CX 4316 4578,
 .CX 4317 4579,
 .CX 4318 4580,
 .CX 4319 4581,
 .CX 4320 4582,
 .CX 4321 4583,
 .CX 4322 4584,
 .CX 4323 4585,
 .CX 4324 4586,
 .CX 4325 4587,
 .CX 4326 4588,
 .CX 4327 4589,
 .CX 4328 4590,
 .CX 4329 4591,
 .CX 4330 4592,
 .CX 4331 4593,
 .CX 4332 4594,
 .CX 4333 4595,
 .CX 4334 4596,
 .CX 4335 4597,
 .CX 4336 4598,
 .CX 4337 4599,
 .CX 4338 4600,
 .CX 4339 4601,
 .CX 4340 4602,
 .CX 4341 4603,
 .CX 4342 4604,
 .CX 4343 4605,
 .CX 4344 4606,
 .CX 4345 4607,
 .CX 4346 4608,
 .CX 4347 4609,
 .CX 4348 4610,
 .CX 4349 4611,
 .CX 4350 4612,
 .CX 4351 4613,
 .CX 4352 4614,
 .CX 4353 4615,
 .CX 4354 4616,
 .CX 4355 4617,
 .CX 4356 4618,
 .CX 4357 4619,
 .CX 4358 4620,
 .CX 4359 4621,
 .CX 4360 4622,
 .CX 4361 4623,
 .CX 4362 4624,
 .CX 4363 4625,
 .CX 4364 4626,
 .CX 4365 4627,
 .CX 4366 4628,
 .CX 4367 4629,
 .CX 4368 4630,
 .CX 4369 4631,
 .CX 4370 4632,
 .CX 4796 4633,
 .CX 4797 4634,
 .CX 4798 4635,
 .CX 4799 4636,
 .CX 4800 4637,
 .CX 4801 4638,
 .CX 4243 4760,
 .CCX 4507 4760 4373,
 .CCX 4508 4373 4374,
 .CCX 4509 4374 4375,
 .CCX 4510 4375 4376,
 .CCX 4511 4376 4377,
 .CCX 4512 4377 4378,
 .CCX 4513 4378 4379,
 .CCX 4514 4379 4380,
 .CCX 4515 4380 4381,
 .CCX 4516 4381 4382,
 .CCX 4517 4382 4383,
 .CCX 4518 4383 4384,
 .CCX 4519 4384 4385,
 .CCX 4520 4385 4386,
 .CCX 4521 4386 4387,
 .CCX 4522 4387 4388,
 .CCX 4523 4388 4389,
 .CCX 4524 4389 4390,
 .CCX 4525 4390 4391,
 .CCX 4526 4391 4392,
 .CCX 4527 4392 4393,
 .CCX 4528 4393 4394,
 .CCX 4529 4394 4395,
 .CCX 4530 4395 4396,
 .CCX 4531 4396 4397,
 .CCX 4532 4397 4398,
 .CCX 4533 4398 4399,
 .CCX 4534 4399 4400,
 .CCX 4535 4400 4401,
 .CCX 4536 4401 4402,
 .CCX 4537 4402 4403,
 .CCX 4538 4403 4404,
 .CCX 4539 4404 4405,
 .CCX 4540 4405 4406,
 .CCX 4541 4406 4407,
 .CCX 4542 4407 4408,
 .CCX 4543 4408 4409,
 .CCX 4544 4409 4410,
 .CCX 4545 4410 4411,
 .CCX 4546 4411 4412,
 .CCX 4547 4412 4413,
 .CCX 4548 4413 4414,
 .CCX 4549 4414 4415,
 .CCX 4550 4415 4416,
 .CCX 4551 4416 4417,
 .CCX 4552 4417 4418,
 .CCX 4553 4418 4419,
 .CCX 4554 4419 4420,
 .CCX 4555 4420 4421,
 .CCX 4556 4421 4422,
 .CCX 4557 4422 4423,
 .CCX 4558 4423 4424,
 .CCX 4559 4424 4425,
 .CCX 4560 4425 4426,
 .CCX 4561 4426 4427,
 .CCX 4562 4427 4428,
 .CCX 4563 4428 4429,
 .CCX 4564 4429 4430,
 .CCX 4565 4430 4431,
 .CCX 4566 4431 4432,
 .CCX 4567 4432 4433,
 .CCX 4568 4433 4434,
 .CCX 4569 4434 4435,
 .CCX 4570 4435 4436,
 .CCX 4571 4436 4437,
 .CCX 4572 4437 4438,
 .CCX 4573 4438 4439,
 .CCX 4574 4439 4440,
 .CCX 4575 4440 4441,
 .CCX 4576 4441 4442,
 .CCX 4577 4442 4443,
 .CCX 4578 4443 4444,
 .CCX 4579 4444 4445,
 .CCX 4580 4445 4446,
 .CCX 4581 4446 4447,
 .CCX 4582 4447 4448,
 .CCX 4583 4448 4449,
 .CCX 4584 4449 4450,
 .CCX 4585 4450 4451,
 .CCX 4586 4451 4452,
 .CCX 4587 4452 4453,
 .CCX 4588 4453 4454,
 .CCX 4589 4454 4455,
 .CCX 4590 4455 4456,
 .CCX 4591 4456 4457,
 .CCX 4592 4457 4458,
 .CCX 4593 4458 4459,
 .CCX 4594 4459 4460,
 .CCX 4595 4460 4461,
 .CCX 4596 4461 4462,
 .CCX 4597 4462 4463,
 .CCX 4598 4463 4464,
 .CCX 4599 4464 4465,
 .CCX 4600 4465 4466,
 .CCX 4601 4466 4467,
 .CCX 4602 4467 4468,
 .CCX 4603 4468 4469,
 .CCX 4604 4469 4470,
 .CCX 4605 4470 4471,
 .CCX 4606 4471 4472,
 .CCX 4607 4472 4473,
 .CCX 4608 4473 4474,
 .CCX 4609 4474 4475,
 .CCX 4610 4475 4476,
 .CCX 4611 4476 4477,
 .CCX 4612 4477 4478,
 .CCX 4613 4478 4479,
 .CCX 4614 4479 4480,
 .CCX 4615 4480 4481,
 .CCX 4616 4481 4482,
 .CCX 4617 4482 4483,
 .CCX 4618 4483 4484,
 .CCX 4619 4484 4485,
 .CCX 4620 4485 4486,
 .CCX 4621 4486 4487,
 .CCX 4622 4487 4488,
 .CCX 4623 4488 4489,
 .CCX 4624 4489 4490,
 .CCX 4625 4490 4491,
 .CCX 4626 4491 4492,
 .CCX 4627 4492 4493,
 .CCX 4628 4493 4494,
 .CCX 4629 4494 4495,
 .CCX 4630 4495 4496,
 .CCX 4631 4496 4497,
 .CCX 4632 4497 4498,
 .CCX 4633 4498 4499,
 .CX 4377 4763,
 .CX 4378 4372,
 .CX 4379 4116,
 .CX 4380 4664,
 .CX 4381 4665,
 .CX 4382 4666,
 .CX 4383 4667,
 .CX 4384 4668,
 .CX 4385 4669,
 .CX 4386 4670,
 .CX 4387 4671,
 .CX 4388 4672,
 .CX 4389 4673,
 .CX 4390 4674,
 .CX 4391 4675,
 .CX 4392 4676,
 .CX 4393 4677,
 .CX 4394 4678,
 .CX 4395 4679,
 .CX 4396 4680,
 .CX 4397 4681,
 .CX 4398 4682,
 .CX 4399 4683,
 .CX 4400 4684,
 .CX 4401 4685,
 .CX 4402 4686,
 .CX 4403 4687,
 .CX 4404 4688,
 .CX 4405 4689,
 .CX 4406 4690,
 .CX 4407 4691,
 .CX 4408 4692,
 .CX 4409 4693,
 .CX 4410 4694,
 .CX 4411 4695,
 .CX 4412 4696,
 .CX 4413 4756,
 .CX 4414 4728,
 .CX 4415 4729,
 .CX 4416 4730,
 .CX 4417 4731,
 .CX 4418 4732,
 .CX 4419 4733,
 .CX 4420 4734,
 .CX 4421 4735,
 .CX 4422 4736,
 .CX 4423 4737,
 .CX 4424 4738,
 .CX 4425 4739,
 .CX 4426 4740,
 .CX 4427 4741,
 .CX 4428 4742,
 .CX 4429 4743,
 .CX 4430 4744,
 .CX 4431 4745,
 .CX 4432 4746,
 .CX 4433 4747,
 .CX 4434 4748,
 .CX 4435 4749,
 .CX 4436 4750,
 .CX 4437 4751,
 .CX 4438 4752,
 .CX 4439 4753,
 .CX 4440 4754,
 .CX 4441 4755,
 .CX 4442 4702,
 .CX 4443 4703,
 .CX 4444 4704,
 .CX 4445 4705,
 .CX 4446 4706,
 .CX 4447 4707,
 .CX 4448 4708,
 .CX 4449 4709,
 .CX 4450 4710,
 .CX 4451 4711,
 .CX 4452 4713,
 .CX 4453 4714,
 .CX 4454 4715,
 .CX 4455 4716,
 .CX 4456 4717,
 .CX 4457 4718,
 .CX 4458 4719,
 .CX 4459 4720,
 .CX 4460 4721,
 .CX 4461 4722,
 .CX 4462 4723,
 .CX 4463 4724,
 .CX 4464 4725,
 .CX 4465 4726,
 .CX 4466 4727,
 .CX 4467 4712,
 .CX 4468 4697,
 .CX 4469 4698,
 .CX 4470 4699,
 .CX 4471 4700,
 .CX 4472 4701,
 .CX 4473 4662,
 .CX 4474 4663,
 .CX 4475 4501,
 .CX 4476 4502,
 .CX 4477 4503,
 .CX 4478 4504,
 .CX 4479 5655,
 .CX 4480 4757,
 .CX 4481 4758,
 .CX 4482 4759
]

 theorem domainSelectedSublist396 : domainSelected396.Sublist oldPrefix := by decide +kernel
 theorem domainSelectedCovers396 : (domain++hosts++ports).all (fun q=>decide (q=4762)||C163Touch.touched domainSelected396 q)=true := by decide +kernel
 theorem checked : (domain++hosts++ports).all (fun q=>decide (q=4762)||C163Touch.touched oldPrefix q)=true := by
 apply List.all_eq_true.mpr
 intro q hq
 have h := List.all_eq_true.mp domainSelectedCovers396 q hq
 simp only [Bool.or_eq_true] at h ⊢
 rcases h with h|h
 · exact Or.inl h
 · exact Or.inr ((C163Touch.touched_spec _ _).mpr
    (RawDomainStructural390.sublist_support domainSelected396 oldPrefix domainSelectedSublist396 ((C163Touch.touched_spec _ _).mp h)))

theorem mod_old:4762∈S:=by
 have used:C163Touch.touched (GhostRelocatedKnown.A.program.take 2200) 4762=true:=by decide +kernel
 have h:4762∈wires (GhostRelocatedKnown.A.program.take 2200):=(C163Touch.touched_spec _ _).mp used
 have sub:wires (GhostRelocatedKnown.A.program.take 2200)⊆wires GhostRelocatedKnown.A.program:=by
  simpa only [List.drop_zero] using AMiddleResearch.slice_subset GhostRelocatedKnown.A.program 0 2200
 exact old_middle_support (sub h)

theorem scope_in(q:Wire)(hq:q∈domain++hosts++ports):q∈S:=by
 have h:=List.all_eq_true.mp checked q hq
 simp only [Bool.or_eq_true] at h
 rcases h with h|h
 · have e:q=4762:=of_decide_eq_true h
   subst q
   exact mod_old
 · exact old_prefix_support ((C163Touch.touched_spec _ _).mp h)

theorem ports_in(q:Wire)(hq:q∈ports):q∈S:=scope_in q (List.mem_append_right _ hq)

theorem raw_domain_in:domain.toFinset∪hosts.toFinset⊆S:=by
 intro q hq
 have h:q∈domain++hosts:=by simpa only [List.mem_toFinset,List.mem_append,Finset.mem_union] using hq
 exact scope_in q (List.mem_append_left _ h)

theorem middle_support:wires M⊆S:=by
 intro q hq
 by_contra bad
 have ne(a:Wire)(ha:a∈ports):q≠a:=by intro eq;subst q;exact bad (ports_in a ha)
 have off:q∉wires oldM:=by
  intro h
  apply bad
  apply old_middle_support
  apply RelocateMembershipResearch.kept GhostRelocatedKnown.ports KnownAMidStaged.body q ?_ h
  intro i
  exact ne _ (by fin_cases i <;>decide)
 have one:q∉wires AAliasesResearch.single:=AMiddleResearch.fresh_of_old q off
  (fix q 4757 4760 (ne _ (by decide)) (ne _ (by decide))) (ne _ (by decide))
 have two:q∉wires M:=AAliasesResearch.fresh_of_single q one
  (fix q 4505 4243 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4506 4244 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4507 4245 (ne _ (by decide)) (ne _ (by decide)))
  (ne _ (by decide)) (ne _ (by decide))
 exact two hq


end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109PhysicalStandalone
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] GatePhysical ECDSAAdd.wires

theorem endpoint_physical:GatePhysical head ∧ GatePhysical top ∧ GatePhysical preInv ∧ GatePhysical tail:=by
 have b:=BReorderedPhysicalResearch.endpoints.1
 have i:=BReorderedPhysicalResearch.endpoints.2
 simp only [ReorderedABuild.build,gatePhysical_append] at b
 simp only [ReorderedAUnbuild.unbuild,gatePhysical_append] at i
 exact ⟨b.1.1,b.2,i.1.1,i.2⟩

theorem cache_physical:GatePhysical (ReorderedGenericCache.cachedAdd 109 xs ys cs hosts cin) ∧
 GatePhysical (ReorderedConsumedSub.consumed 109 xs ys cs hosts cin):=by
 have f:=ReorderedPhysical.cached 109 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  raw_nd (fun q hq bad=>geometry.2.2 q hq (c_in q bad))
 have n:=notRegister_physical ys
 refine ⟨f.1,?_⟩
 simp only [ReorderedConsumedSub.consumed,gatePhysical_append]
 exact ⟨⟨n,f.2⟩,n⟩

theorem loop_physical:GatePhysical A109SignResearch.loop:=by
 have hi:GatePhysical newI:=by
  simp only [newI,gatePhysical_append]
  exact ⟨endpoint_physical.2.2.1,HighConsumedA109Research.sub_physical cache_physical.2⟩
 simp only [A109SignResearch.loop,A109SignResearch.suffix,A109SignResearch.hosts,gatePhysical_append]
 exact ⟨SignAHeadResources.physical,⟨⟨⟨⟨⟨⟨A109LowEraseResearch.physical,cache_physical.1⟩,endpoint_physical.2.1⟩,
  AAliasesResearch.physical⟩,hi⟩,A109LowEraseResearch.physical⟩,endpoint_physical.2.2.2⟩⟩

theorem body_physical:GatePhysical A109SignResearch.body:=by
 have old:=HighBodyAResourceResearch.physical
 simp only [HighSignAResearch.body,HighSignAResearch.rawBody,HighSignAResearch.fold,gatePhysical_append] at old
 simp only [A109SignResearch.body,A109SignResearch.rawBody,A109SignResearch.fold,gatePhysical_append]
 exact ⟨⟨old.1.1,⟨old.1.2.1,loop_physical⟩⟩,old.2⟩

end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component A109Support
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch ControlLoan1589BFFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem clear_support:wires A109LowEraseResearch.clear⊆S:=by
 have eq:wires A109LowEraseResearch.clear=([4243,4505,4244,4506,4245,4507]:List Wire).toFinset:=by
  ext q
  simp [A109LowEraseResearch.clear,wires,Instr.wires,correctionWires]
  itauto
 rw [eq]
 intro q hq
 have sub:([4243,4505,4244,4506,4245,4507]:List Wire)⊆ports:=by decide
 exact ports_in q (sub (List.mem_toFinset.mp hq))

theorem endpoint_support:wires top⊆S ∧ wires preInv⊆S ∧ wires tail⊆S:=by
 have aa:ReorderedAFixed.acc=acc:=by decide +kernel
 have ap:ReorderedAFixed.pad=pad:=by decide +kernel
 have ab:ReorderedAFixed.bank=bank:=by decide +kernel
 have ax:ReorderedAFixed.src=src:=by decide +kernel
 have ai:ReorderedAFixed.L.core.cin=L.core.cin:=by decide +kernel
 have whole:wires HighSignAResearch.loop⊆S:=by
  simp only [S,HighSignAResearch.body,HighSignAResearch.rawBody,HighSignAResearch.fold,wires_append]
  exact Finset.subset_union_right.trans (Finset.subset_union_right.trans Finset.subset_union_left)
 have parts:=whole
 simp only [HighSignAResearch.loop,HighSignAResearch.suffix,wires_append,Finset.union_subset_iff] at parts
 have inv:=parts.2.2
 simp only [HighUnbuildAResearch.unbuild,wires_append,Finset.union_subset_iff] at inv
 refine ⟨?_,?_,?_⟩
 · simpa only [top,aa,ap,ab,ax,ai] using parts.2.1.1.2
 · simpa only [preInv,aa,ap,ab,ax,ai] using inv.1.1
 · simpa only [tail,aa,ap,ab,ax,ai] using inv.2

theorem cache_support:wires (ReorderedGenericCache.cachedAdd 109 xs ys cs hosts cin)⊆S ∧
 wires (ReorderedConsumedSub.consumed 109 xs ys cs hosts cin)⊆S:=by
 have c:=ReorderedSupport.cached 109 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
 have i:=ReorderedSupport.consumed 109 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
 exact ⟨c.1.trans raw_domain_in,i.trans raw_domain_in⟩

theorem loop_support:wires A109SignResearch.loop⊆S:=by
 have hh:wires SignAHead.head⊆S:=by
  apply Finset.Subset.trans ?_ old_prefix_support
  rw [oldPrefix,wires_append]
  exact Finset.subset_union_left
 have hi:wires newI⊆S:=by
  simp only [newI,wires_append]
  exact Finset.union_subset endpoint_support.2.1 (HighConsumedA109Research.sub_support.trans cache_support.2)
 simp only [A109SignResearch.loop,A109SignResearch.suffix,A109SignResearch.hosts,wires_append,Finset.union_subset_iff]
 exact ⟨hh,⟨⟨⟨⟨⟨⟨clear_support,cache_support.1⟩,endpoint_support.1⟩,middle_support⟩,hi⟩,clear_support⟩,endpoint_support.2.2⟩⟩

theorem body_support:wires A109SignResearch.body⊆S:=by
 have h:=BodySupportContextResearch.replace2
  (measuredFoldQTq ReorderedAFixed.L (negP ReorderedAFixed.L))
  (measuredFoldQTq ReorderedAFixed.L (rot128F ReorderedAFixed.L))
  HighSignAResearch.loop A109SignResearch.loop
  (ReorderedRecordPadding.program 7 ReorderedAFixed.L.core.cin) loop_support
 exact h


end ECDSAAdd.Entrant.A109Research

end

-- Verified ABC18 optimization component C105Prefix
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105PrefixResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev L:=C163Low4Middle.L
abbrev acc:=C163Low4Middle.ga
abbrev src:=C163Low4Middle.src
abbrev pad:=C163Low4Middle.pad
abbrev bank:=C163Low4Middle.bank
abbrev cin:=L.core.cin
 theorem acc_length:acc.length=163:=C163Low4Middle.lengths.1
 theorem source_length:src.length=130:=C163Low4Middle.lengths.2.2.2
 theorem fits:∀f∈earlyHTerms src,Acc.Fits acc pad bank cin 163 f:=C163Low4Middle.fits
end ECDSAAdd.Entrant.C105PrefixResearch

end

-- Verified ABC18 optimization component C105Geometry
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

def hosts:List Wire:=ReorderedCFixed.hosts++[4757,4758,4759,4505,4506,4507]
def ports:List Wire:=[4757,4760,4759,4762,4758,4244,4506,4505,4243,4507,4245]

theorem geometry:hosts.Nodup ∧ hosts.length=105 ∧
 (∀q∈hosts,q∉cin::(src++(acc.take 140).drop 10++bank.take 129)):=by decide +kernel

theorem old_away:∀q∈ReorderedCFixed.hosts,q∉ports:=by decide +kernel

theorem fix(q a b:Wire)(ha:q≠a)(hb:q≠b):(Equiv.swap a b) q=q:=by
 simp [Equiv.swap_apply_def,ha,hb]

theorem old_fresh(q:Wire)(hq:q∈ReorderedCFixed.hosts):q∉wires CKAliasesResearch.program:=by
 have away:q∉ports:=old_away q hq
 have ne(a:Wire)(ha:a∈ports):q≠a:=by intro eq;subst q;exact away ha
 have s:q∉wires CKAliasesResearch.single:=CKMiddleResearch.fresh_of_old q
  ((by
   intro bad
   have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert
   exact ReorderedCFixed.off_middle q hq (Skip4.wires_mono_of_mem _ _ (fun _ h=>sub.subset h) bad)))
  (fix q 4757 4760 (ne _ (by decide)) (ne _ (by decide))) (ne _ (by decide))
 exact CKAliasesResearch.fresh_of_single q s
  (fix q 4505 4243 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4506 4244 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4507 4245 (ne _ (by decide)) (ne _ (by decide)))
  (ne _ (by decide)) (ne _ (by decide))

theorem middle_fresh(q:Wire)(hq:q∈hosts):q∉wires CKAliasesResearch.program:=by
 rcases List.mem_append.mp hq with hq|hq
 · exact old_fresh q hq
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
   · exact CKAliasesResearch.ghost_free _ (by decide)
   · exact CKAliasesResearch.ghost_free _ (by decide)
   · exact CKAliasesResearch.ghost_free _ (by decide)
   · exact CKAliasesResearch.low4_free
   · exact CKAliasesResearch.low5_free
   · exact CKAliasesResearch.low6_free

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component HighConsumedC105
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.HighConsumedC105Research
abbrev xs:List Wire:=C105PrefixResearch.src
abbrev ys:List Wire:=(C105PrefixResearch.acc.take 140).drop 10
abbrev cs:List Wire:=C105PrefixResearch.bank.take 129
abbrev hs:List Wire:=C105Research.hosts
abbrev cin:Wire:=C105PrefixResearch.cin
def ports:Fin 12→Wire:=![4369,4370,4371,4372,4637,4638,4639,4640,4498,4499,4500,4764]
def old:Program:=ReorderedGenericCache.consumedAdd 105 xs ys cs hs cin
def pre:Program:=old.take 336
def post:Program:=old.drop 365
def fast:Program:=pre++PlacedUniformAdder4Research.fastAt ports++post

theorem ports_inj:Function.Injective ports:=by decide +kernel

theorem window:(old.drop 336).take 29=PlacedUniformAdder4Research.originalAt ports:=by decide +kernel

theorem shape:old=pre++PlacedUniformAdder4Research.originalAt ports++post:=by
 rw [pre,post,←window,←List.take_add]
 exact (List.take_append_drop 365 old).symm

theorem pre_measurements:measurementCount pre=0:=by decide +kernel

theorem pre_fresh:∀q∈UniformAdderSpliceResearch.cs ports,q∉wires pre:=by
 have rs4_h:(UniformAdderSpliceResearch.cs ports).all (fun q=>!C163Touch.touched pre q)=true:=by decide +kernel
 intro q hq
 exact HighConsumedStreamResearch.untouched _ _ (by simpa using List.all_eq_true.mp rs4_h q hq)

theorem post_fresh:∀q∈UniformAdderSpliceResearch.ys ports,q∉wires post:=by
 have rs4_h:(UniformAdderSpliceResearch.ys ports).all (fun q=>!C163Touch.touched post q)=true:=by decide +kernel
 intro q hq
 exact HighConsumedStreamResearch.untouched _ _ (by simpa using List.all_eq_true.mp rs4_h q hq)

theorem toffoli:toffoliCount fast+3=toffoliCount old:=by
 have h:=congrArg toffoliCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [toffoliCount_append] at h
 have g:toffoliCount fast=toffoliCount pre+toffoliCount (PlacedUniformAdder4Research.fastAt ports)+toffoliCount post:=by
  simp only [fast,toffoliCount_append]
 omega

theorem measurements:measurementCount fast=measurementCount old:=by
 have h:=congrArg measurementCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [measurementCount_append] at h
 have g:measurementCount fast=measurementCount pre+measurementCount (PlacedUniformAdder4Research.fastAt ports)+measurementCount post:=by
  simp only [fast,measurementCount_append]
 omega


end ECDSAAdd.Entrant.HighConsumedC105Research


namespace ECDSAAdd.Entrant.HighConsumedC105Research
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop

theorem source_length:xs.length=130:=by decide +kernel

theorem target_length:ys.length=130:=by decide +kernel

theorem carry_length:cs.length=129:=by decide +kernel

theorem high_targets:ys.drop 126=UniformAdderSpliceResearch.ys ports:=by decide +kernel

theorem high_carries:∀q∈UniformAdderSpliceResearch.cs ports,q∈cs:=by
 intro q hq
 simp only [UniformAdderSpliceResearch.cs,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel

theorem high_word (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=105)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^130)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 105 H (976*H/1024)):
 regValue (UniformAdderSpliceResearch.ys ports)
  (run old [] (run (notRegister ys) [] s)).basis=0 ∨
 regValue (UniformAdderSpliceResearch.ys ports)
  (run old [] (run (notRegister ys) [] s)).basis=15:=by
 have v:=HighConsumedInputsResearch.inner_value 105 xs ys cs hs cin (by rw [source_length];decide) (by rw [target_length];decide)
   (by rw [carry_length];decide) (source_length.trans target_length.symm)
   (by rw [carry_length,target_length]) hn nd len fresh s [] hz hi H (976*H/1024) source target saved
 change regValue ys (run old [] (run (notRegister ys) [] s)).basis=
  (H+(2^ys.length-1-976*H/1024))%2^ys.length at v
 rw [target_length] at v
 rw [←high_targets,CuccaroStreamedSquareWideLayout.regValue_drop_div ys 126 (by rw [target_length];decide),v]
 have power:16*(2^126)=2^130:=by norm_num
 have a:=HighBorrowArithmeticResearch.borrow_remainder_high (2^126) H (by positivity)
  (show H<16*2^126 by simpa only [power] using hH)
 rw [power] at a
 by_cases h0:H=0
 · right;rw [a,if_pos h0]
 · left;rw [a,if_neg h0]

theorem inner_run_eq (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=105)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^130)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 105 H (976*H/1024)) (m:List Bool):
 run fast m (run (notRegister ys) [] s)=run old m (run (notRegister ys) [] s):=by
 let u:=run (notRegister ys) [] s
 have cys:∀q∈cs,q∉ys:=by
  intro q hq bad
  exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2
   (List.mem_append_right _ bad) hq
 have cu:∀q∈UniformAdderSpliceResearch.cs ports,u.basis q=false:=by
  intro q hq
  have hc:=high_carries q hq
  have off:q∉wires (notRegister ys):=by simpa only [notRegister_wires,List.mem_toFinset] using cys q hc
  exact (run_preserves_outside (notRegister ys) [] s q off).trans (hz q hc)
 have ready:regValue (UniformAdderSpliceResearch.ys ports)
   (run (pre++PlacedUniformAdder4Research.originalAt ports++post) [] u).basis=0 ∨
  regValue (UniformAdderSpliceResearch.ys ports)
   (run (pre++PlacedUniformAdder4Research.originalAt ports++post) [] u).basis=15:=by
  simpa only [←shape] using high_word s hn nd len fresh hz hi H hH source target saved
 have eq:=UniformAdderSpliceResearch.replace ports ports_inj pre post u m pre_measurements cu pre_fresh post_fresh ready
 simpa only [fast,←shape] using eq

def sub:Program:=notRegister ys++fast++notRegister ys

theorem sub_measurements:measurementCount sub=measurementCount (ReorderedConsumedSub.consumed 105 xs ys cs hs cin):=by
 simp only [sub,ReorderedConsumedSub.consumed,measurementCount_append,measurements,old]


theorem sub_run_eq (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=105)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^130)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 105 H (976*H/1024)) (m:List Bool):
 run sub m s=run (ReorderedConsumedSub.consumed 105 xs ys cs hs cin) m s:=by
 have eq:=CodexKnownOnesTail.Helpers.run_mid_congr (notRegister ys) fast old (notRegister ys) m s
  (notRegister_counts ys).2 measurements (fun r=>inner_run_eq s hn nd len fresh hz hi H hH source target saved r)
 simpa only [sub,ReorderedConsumedSub.consumed,old] using eq



end ECDSAAdd.Entrant.HighConsumedC105Research


end

-- Verified ABC18 optimization component HighC105Resources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HighConsumedC105Research

theorem support:wires fast⊆wires old:=by
 have q:=HighBorrowResourceResearch.placed_support ports
 have e:=congrArg wires shape
 simp only [wires_append] at e
 rw [fast,wires_append,wires_append,e]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem physical(h:GatePhysical old):GatePhysical fast:=by
 rw [shape] at h
 simp only [gatePhysical_append] at h
 change GatePhysical (pre++PlacedUniformAdder4Research.fastAt ports++post)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,HighBorrowResourceResearch.placed_physical ports ports_inj⟩,h.2⟩

theorem slots:Challenge.gateSlots fast+3=Challenge.gateSlots old:=by
 have h:=congrArg Challenge.gateSlots shape
 have q:=HighBorrowResourceResearch.placed_slots ports
 simp only [Challenge.gateSlots_append] at h
 have g:Challenge.gateSlots fast=Challenge.gateSlots pre+Challenge.gateSlots (PlacedUniformAdder4Research.fastAt ports)+Challenge.gateSlots post:=by
  simp only [fast,Challenge.gateSlots_append]
 omega

theorem sub_support:wires sub⊆wires (ReorderedConsumedSub.consumed 105 xs ys cs hs cin):=by
 have q:wires fast⊆wires (ReorderedGenericCache.consumedAdd 105 xs ys cs hs cin):=by simpa only [old] using support
 simp only [sub,ReorderedConsumedSub.consumed,wires_append]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem sub_physical(h:GatePhysical (ReorderedConsumedSub.consumed 105 xs ys cs hs cin)):GatePhysical sub:=by
 simp only [ReorderedConsumedSub.consumed,gatePhysical_append] at h
 change GatePhysical (notRegister ys++fast++notRegister ys)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,physical h.1.2⟩,h.2⟩

theorem sub_toffoli:toffoliCount sub+3=toffoliCount (ReorderedConsumedSub.consumed 105 xs ys cs hs cin):=by
 have q:=toffoli
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,toffoliCount_append]
 omega

theorem sub_slots:Challenge.gateSlots sub+3=Challenge.gateSlots (ReorderedConsumedSub.consumed 105 xs ys cs hs cin):=by
 have q:=slots
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,Challenge.gateSlots_append]
 omega
end ECDSAAdd.Entrant.HighConsumedC105Research


end

-- Verified ABC18 optimization component C105LowErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105LowEraseResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def low:List Wire:=[4505,4506,4507]
def erase(s:State):State:=EraseListProof.erase low s
def clear:Program:=[.CX 4243 4505,.CX 4244 4506,.CX 4245 4507,.CX 4243 4507]

theorem clear_eq_erase(s:State)(m:List Bool)
 (h4:s.basis 4505=s.basis 4243)(h5:s.basis 4506=s.basis 4244)
 (h6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243)):
 run clear m s=erase s:=by
 apply State.extensionality
 · simp [clear,run,erase,EraseListProof.phase]
 · funext q
   by_cases hq:q=4505
   · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h4]
   · by_cases hq5:q=4506
     · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h5]
     · by_cases hq6:q=4507
       · subst q
         cases a:s.basis 4243 <;>cases b:s.basis 4245 <;>
          simp_all [clear,run,erase,EraseListProof.basis,low,writeBit]
       · simp [clear,run,erase,EraseListProof.basis,low,writeBit,hq,hq5,hq6]

theorem restore(s:State)(m:List Bool)
 (h4:s.basis 4505=s.basis 4243)(h5:s.basis 4506=s.basis 4244)
 (h6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243)):
 run clear m (erase s)=s:=by
 apply State.extensionality
 · simp [clear,run,erase,EraseListProof.phase]
 · funext q
   by_cases hq:q=4505
   · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h4]
   · by_cases hq5:q=4506
     · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h5]
     · by_cases hq6:q=4507
       · subst q
         cases a:s.basis 4243 <;>cases b:s.basis 4245 <;>
          simp_all [clear,run,erase,EraseListProof.basis,low,writeBit]
       · simp [clear,run,erase,EraseListProof.basis,low,writeBit,hq,hq5,hq6]

theorem commute(P:Program)(m:List Bool)(s:State)(off:∀q∈low,q∉wires P):
 run P m (erase s)=erase (run P m s):=EraseListProof.commute low P m s off

theorem bit_same(s:State)(q:Wire)(off:q∉low):(erase s).basis q=s.basis q:=by
 simp [erase,EraseListProof.basis,off]





theorem zero(s:State)(q:Wire)(hq:q∈low):(erase s).basis q=false:=by
 simp [erase,EraseListProof.basis,hq]

theorem counts:toffoliCount clear=0 ∧ measurementCount clear=0 ∧ Challenge.gateSlots clear=4:=by decide +kernel

theorem physical:GatePhysical clear:=by simp [GatePhysical,clear,RecordedQuantum.PhysicalInstr,ProperGate]


end ECDSAAdd.Entrant.C105LowEraseResearch

end

-- Verified ABC18 optimization component C105LowErasedComposition
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105LowEraseResearch
open InverseCarryDevelop C105PrefixResearch ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem aliases_erased(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run KnownCMidStaged.body m s))
 (flag:s.basis 4762=false):
 run CKAliasesResearch.program m (erase s)=erase (run KnownCMidStaged.body m s):=by
 have off:∀q∈low,q∉wires CKAliasesResearch.program:=by
  intro q hq
  simp only [low,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact CKAliasesResearch.low4_free
  · exact CKAliasesResearch.low5_free
  · exact CKAliasesResearch.low6_free
 rw [commute _ m s off,CKAliasesResearch.equivalent H s m before after flag]

theorem forward_erased(head P:Program)(s:State)(m:List Bool)
 (off:∀q∈low,q∉wires P)
 (h4:(run head m s).basis 4505=(run head m s).basis 4243)
 (h5:(run head m s).basis 4506=(run head m s).basis 4244)
 (h6:(run head m s).basis 4507=((run head m s).basis 4245 ^^ (run head m s).basis 4243)):
 run (head++clear++P) m s=erase (run (head++P) m s):=by
 have mc:measurementCount clear=0:=counts.2.1
 simp only [run_cat,measurementCount_append,mc,Nat.add_zero]
 rw [clear_eq_erase _ _ h4 h5 h6,commute P _ _ off]

theorem suffix(P:Program)(s:State)(m:List Bool)(off:∀q∈low,q∉wires P)
 (h4:(run P m s).basis 4505=(run P m s).basis 4243)
 (h5:(run P m s).basis 4506=(run P m s).basis 4244)
 (h6:(run P m s).basis 4507=((run P m s).basis 4245 ^^ (run P m s).basis 4243)):
 run (P++clear) m (erase s)=run P m s:=by
 rw [run_cat,commute P m s off]
 exact restore _ _ h4 h5 h6


end ECDSAAdd.Entrant.C105LowEraseResearch

end

-- Verified ABC18 optimization component C105Raw
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

abbrev xs:List Wire:=src
abbrev ys:List Wire:=(acc.take 140).drop 10
abbrev cs:List Wire:=bank.take 129
def domain:List Wire:=cin::(xs++ys++cs)
def rawF:Program:=mappedAdd (mappedRead xs false) ys cs cin
def rawI:Program:=ReorderedConsumedSub.plain xs ys cs cin
def head:Program:=ReorderedCHead.head acc pad bank cin src
def top:Program:=C163Carry.buildPost acc pad bank cin src
def preInv:Program:=C163Carry.unbuildPre acc pad bank cin src
def F:Program:=head++C105LowEraseResearch.clear++rawF++top
def newF:Program:=head++C105LowEraseResearch.clear++ReorderedGenericCache.cachedAdd 105 xs ys cs hosts cin++top
def I:Program:=preInv++rawI
def newI:Program:=preInv++HighConsumedC105Research.sub
def topDomain:List Wire:=cin::(Acc.tx pad 163 (Acc.earlyTerm src false 32)++
 Acc.ty acc (Acc.earlyTerm src false 32)++Acc.tc bank 163 (Acc.earlyTerm src false 32))

theorem raw_lengths:xs.length=130 ∧ ys.length=130 ∧ cs.length=129:=by decide +kernel

theorem raw_nd:domain.Nodup := by
 have fit := C105PrefixResearch.fits (Acc.earlyTerm C105PrefixResearch.src false 32)
  (A161NarrowAcc.terms_mem C105PrefixResearch.src).2.2.2
 exact RawDomainStructural390.sliced_nodup _ _ _ _ _ fit.nd 140 10 129

theorem raw_wires:wires rawF=domain.toFinset:=by
 rw [rawF,MixedLiteralAdderDevelop.read_add_eq]
 exact addInPlace_wires xs ys cs cin (by rw [raw_lengths.1,raw_lengths.2.1])
  (by rw [raw_lengths.2.1,raw_lengths.2.2])

theorem rawF_off(q:Wire)(hq:q∈hosts):q∉wires rawF:=by
 intro bad
 rw [raw_wires] at bad
 exact geometry.2.2 q hq (List.mem_toFinset.mp bad)

theorem rawI_off(q:Wire)(hq:q∈hosts):q∉wires rawI:=by
 have ysSub:ys.toFinset⊆domain.toFinset:=by
  intro w hw
  apply List.mem_toFinset.mpr
  have hy:w∈ys:=List.mem_toFinset.mp hw
  simp only [domain,List.mem_cons,List.mem_append]
  itauto
 have support:wires rawI⊆domain.toFinset:=by
  simp only [rawI,ReorderedConsumedSub.plain,wires_append,notRegister_wires]
  change (ys.toFinset∪wires rawF)∪ys.toFinset⊆domain.toFinset
  rw [raw_wires]
  exact Finset.union_subset (Finset.union_subset ysSub (Finset.Subset.refl _)) ysSub
 exact fun bad=>geometry.2.2 q hq (List.mem_toFinset.mp (support bad))

theorem top_away:∀q∈hosts,q∉topDomain:=by decide +kernel

theorem top_wires:wires top=topDomain.toFinset:=by
 have take:acc.take 163=acc:=by rw [←acc_length];exact List.take_length
 unfold top C163Carry.buildPost
 rw [take]
 exact Acc.op_wires acc pad bank cin 163 false (Acc.earlyTerm src false 32) acc_length
  (fits _ (A161NarrowAcc.terms_mem src).2.2.2)

theorem top_off(q:Wire)(hq:q∈hosts):q∉wires top:=by
 rw [top_wires]
 exact fun bad=>top_away q hq (List.mem_toFinset.mp bad)

theorem preInv_support:wires preInv⊆topDomain.toFinset:=by
 have take:acc.take 163=acc:=by rw [←acc_length];exact List.take_length
 have fit:=fits _ (A161NarrowAcc.terms_mem src).2.2.2
 unfold preInv C163Carry.unbuildPre
 rw [take]
 have r:=CodexNarrowTailResource.accSub_support 108 acc pad bank cin 163 (Acc.earlyTerm src false 32)
  acc_length fit.toFitsLen (by norm_num [Acc.earlyTerm])
 rw [Acc.op_wires acc pad bank cin 163 true (Acc.earlyTerm src false 32) acc_length fit] at r
 exact r

theorem preInv_off(q:Wire)(hq:q∈hosts):q∉wires preInv:=
 fun bad=>top_away q hq (List.mem_toFinset.mp (preInv_support bad))

theorem I_off(q:Wire)(hq:q∈hosts):q∉wires I:=by
 simp only [I,wires_append,Finset.mem_union,not_or]
 exact ⟨preInv_off q hq,rawI_off q hq⟩

theorem low_hosts(q:Wire)(hq:q∈C105LowEraseResearch.low):q∈hosts:=by
 simp only [C105LowEraseResearch.low,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel


end ECDSAAdd.Entrant.C105Research

end

end

end

-- repack: BOptimizations lines 34..1081
section
section

-- Verified ABC18 optimization component C105CacheFrames
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop MixedLiteralAdderDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem sub_frame(s:State)(m:List Bool)(H:Nat)(hH:H<2^130)
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hosts.map s.basis=ReorderedCacheBits.values 4 105 H (976*H/1024)):
 run HighConsumedC105Research.sub m s=
 scatterState hosts (List.replicate hosts.length false) (run rawI m s):=by
 have fast:=HighConsumedC105Research.sub_run_eq s raw_nd geometry.1 geometry.2.1 geometry.2.2
  hz hi H hH source target saved m
 rw [fast]
 exact ReorderedConsumedSub.frame 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
  raw_nd geometry.1 geometry.2.1 geometry.2.2 s m hz hi H (976*H/1024) source target saved

theorem inverse_frame(s:State)(m:List Bool)(H:Nat)(hH:H<2^130)
 (hz:∀q∈cs,(run preInv m s).basis q=false)(hi:(run preInv m s).basis cin=false)
 (source:regValue xs (run preInv m s).basis=H)
 (target:regValue ys (run preInv m s).basis=976*H/1024)
 (saved:hosts.map s.basis=ReorderedCacheBits.values 4 105 H (976*H/1024)):
 run newI m s=scatterState hosts (List.replicate hosts.length false) (run I m s):=by
 have same:hosts.map (run preInv m s).basis=hosts.map s.basis:=
  by
   apply List.map_congr_left
   intro q hq
   exact run_preserves_outside preInv m s q (preInv_off q hq)
 simp only [newI,I,ControlledBorrowResearch.run_cat]
 exact sub_frame (run preInv m s) _ H hH hz hi source target (same.trans saved)

theorem forward_frame(s:State)(m:List Bool)(H:Nat)
 (zero:∀q∈hosts,(run (head++C105LowEraseResearch.clear) (m.take (measurementCount (head++C105LowEraseResearch.clear))) s).basis q=false)
 (values:(((cs.drop 4).take 105).map (run (carryPrefix (4+105) xs ys cs cin) []
  (run (head++C105LowEraseResearch.clear) (m.take (measurementCount (head++C105LowEraseResearch.clear))) s)).basis)=
   ReorderedCacheBits.values 4 105 H (976*H/1024)):
 run newF m s=scatterState hosts (ReorderedCacheBits.values 4 105 H (976*H/1024)) (run F m s):=by
 have h:=CacheBetweenFrameResearch.forward (head++C105LowEraseResearch.clear) top 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  geometry.1 (fun q hq bad=>geometry.2.2 q hq (by simp only [List.mem_cons,List.mem_append];tauto))
  rawF_off top_off s m zero
 rw [values] at h
 exact h

theorem forward_measurements:measurementCount newF=measurementCount F:=by
 have h:=(ReorderedGenericCache.count_balance 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)).2.1
 simp only [newF,F,rawF,measurementCount_append]
 rw [h]


end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105ForwardErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem low_copies(H:Nat)(s:State)(ready:WReady acc pad bank cin src H s):
 s.basis 4505=s.basis 4243 ∧ s.basis 4506=s.basis 4244 ∧ s.basis 4507=(s.basis 4245 ^^ s.basis 4243):=by
 have cp:=LowWordRecovery.copies acc src s.basis (by rw [acc_length];decide)
  (by rw [source_length];decide) (by rw [ready.2.1];exact ready.1)
 have c4:s.basis 4505=s.basis 4243:=by
  simpa only [show src.getD 0 0=4243 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.1.symm
 have c5:s.basis 4506=s.basis 4244:=by
  simpa only [show src.getD 1 0=4244 from by decide +kernel,
   show acc.getD 5 0=4506 from by decide +kernel] using cp.2.1.symm
 refine ⟨c4,c5,?_⟩
 have c6:s.basis 4245=(s.basis 4507 ^^ s.basis 4505):=by
  simpa only [show src.getD 2 0=4245 from by decide +kernel,
   show acc.getD 6 0=4507 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.2.2
 rw [c6,←c4]
 simp [Bool.xor_assoc]

theorem plain_split:ReorderedCPlain.build acc pad bank cin src=head++(rawF++top):=by
 simpa only [head,rawF,top,List.append_assoc] using
  ReorderedCBuild.plain_split acc pad bank cin src source_length

theorem rest_off(q:Wire)(hq:q∈C105LowEraseResearch.low):q∉wires (rawF++top):=by
 simp only [wires_append,Finset.mem_union,not_or]
 exact ⟨rawF_off q (low_hosts q hq),top_off q (low_hosts q hq)⟩

theorem head_copies(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 (run head m s).basis 4505=(run head m s).basis 4243 ∧
 (run head m s).basis 4506=(run head m s).basis 4244 ∧
 (run head m s).basis 4507=((run head m s).basis 4245 ^^ (run head m s).basis 4243):=by
 let u:=run (ReorderedCPlain.build acc pad bank cin src) m s
 have ready:WReady acc pad bank cin src (regValue src s.basis) u:=
  Ghost3CacheC.plain_ready s m hz hb hi ha
 have cp:=low_copies _ u ready
 have low(q:Wire)(hq:q∈C105LowEraseResearch.low):u.basis q=(run head m s).basis q:=by
  dsimp [u]
  rw [plain_split,run_cat]
  exact run_preserves_outside _ _ _ q (rest_off q hq)
 have frame:=ReorderedCHead.head_triple acc pad bank cin src acc_length (by have h:=source_length;omega)
  fits s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have away:∀q∈src,q∉acc:=by decide +kernel
 have source(q:Wire)(hq:q∈src):u.basis q=(run head m s).basis q:=by
  have h:= (regValue_eq_iff src _ _).mp ready.2.1 q hq
  exact h.trans (frame.2.2 q (away q hq)).symm
 rw [low 4505 (by decide),low 4506 (by decide),low 4507 (by decide),source 4243 (by decide +kernel),source 4244 (by decide +kernel),source 4245 (by decide +kernel)] at cp
 exact cp

theorem forward_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 run F m s=C105LowEraseResearch.erase (run (ReorderedCPlain.build acc pad bank cin src) m s):=by
 have cp:=head_copies s m hz hb hi ha
 have eq:=C105LowEraseResearch.forward_erased head (rawF++top) s m rest_off cp.1 cp.2.1 cp.2.2
 simpa only [F,plain_split,List.append_assoc] using eq

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105ForwardClean
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem forward_zero(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false):
 ∀q∈hosts,(run F m s).basis q=false:=by
 rw [forward_erased s m hz hb hi ha]
 let u:=run (ReorderedCPlain.build acc pad bank cin src) m s
 have ready:WReady acc pad bank cin src (regValue src s.basis) u:=
  Ghost3CacheC.plain_ready s m hz hb hi ha
 intro q hq
 rcases List.mem_append.mp hq with hq|hq
 · rw [C105LowEraseResearch.bit_same _ q (by
    have away:=old_away q hq
    intro bad
    apply away
    simp only [C105LowEraseResearch.low,List.mem_cons,List.not_mem_nil,or_false] at bad
    rcases bad with rfl|rfl|rfl <;>decide)]
   exact (run_preserves_outside _ m s q (ReorderedCFixed.off_plain q hq).1).trans (zero q hq)
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 0 (by decide)
      (by rw [acc_length];decide) ready.1
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 1 (by decide)
      (by rw [acc_length];decide) ready.1
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 2 (by decide)
      (by rw [acc_length];decide) ready.1
   · exact C105LowEraseResearch.zero _ _ (by decide)
   · exact C105LowEraseResearch.zero _ _ (by decide)
   · exact C105LowEraseResearch.zero _ _ (by decide)

theorem prefix_zero(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false):
 ∀q∈hosts,(run (head++C105LowEraseResearch.clear) m s).basis q=false:=by
 have clean:=forward_zero s m hz hb hi ha zero
 intro q hq
 have off:q∉wires (rawF++top):=by
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨rawF_off q hq,top_off q hq⟩
 have eq:(run F m s).basis q=(run (head++C105LowEraseResearch.clear) m s).basis q:=by
  have partition:F=(head++C105LowEraseResearch.clear)++(rawF++top):=by simp only [F,List.append_assoc]
  rw [partition,run_cat]
  exact run_preserves_outside _ _ _ q off
 exact eq.symm.trans (clean q hq)

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CHeadArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CHeadArithmeticResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem ready(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0):
 let t:=run (ReorderedCHead.head acc Z bank cin src) m s
 (∀q∈bank.take 129,t.basis q=false) ∧ t.basis cin=false ∧
 regValue src t.basis=regValue src s.basis ∧
 regValue ((acc.take 140).drop 10) t.basis=((2^140-48*regValue src s.basis)%2^140)/1024:=by
 let H:=regValue src s.basis
 let t:=run (ReorderedCHead.head acc Z bank cin src) m s
 have frame:=ReorderedCHead.head_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have hf10:=hf _ (A161NarrowAcc.terms_mem src).2.1
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;>omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=frame.2.2 q (away q hq)
 have len:(acc.take 140).length=140:=by simp [hacc]
 have pref:=regValue_take_drop_of_lt acc 140 ((2^140-48*H)%2^140) t.basis
  (by omega) frame.2.1 (Nat.mod_lt _ (by positivity))
 refine ⟨?_,?_,?_,?_⟩
 · intro q hq
   exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 · exact (same cin (Or.inr rfl)).trans hi
 · exact regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 · rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
   rfl

end ECDSAAdd.Entrant.CHeadArithmeticResearch

end

-- Verified ABC18 optimization component C105ForwardValues
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem x_in(q:Wire)(hq:q∈xs):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_left cs (List.mem_append_left ys hq))
theorem y_in(q:Wire)(hq:q∈ys):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_left cs (List.mem_append_right xs hq))
theorem c_in(q:Wire)(hq:q∈cs):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_right (xs++ys) hq)
theorem cin_in:cin∈domain:=List.mem_cons_self

theorem domain_away_low(q:Wire)(hq:q∈domain):q∉C105LowEraseResearch.low:=by
 intro bad
 exact geometry.2.2 q (low_hosts q bad) hq

theorem prefix_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 run (head++C105LowEraseResearch.clear) m s=C105LowEraseResearch.erase (run head m s):=by
 rw [run_cat]
 have cp:=head_copies s m hz hb hi ha
 exact C105LowEraseResearch.clear_eq_erase _ _ cp.1 cp.2.1 cp.2.2

theorem forward_values(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 (((cs.drop 4).take 105).map (run (carryPrefix (4+105) xs ys cs cin) []
  (run (head++C105LowEraseResearch.clear) m s)).basis)=
 ReorderedCacheBits.values 4 105 (regValue src s.basis) (976*regValue src s.basis/1024):=by
 let H:=regValue src s.basis
 let u:=run head m s
 let t:=run (head++C105LowEraseResearch.clear) m s
 have te:t=C105LowEraseResearch.erase u:=prefix_erased s m hz hb hi ha
 have hH:H<2^130:=by simpa only [H,source_length] using regValue_lt src s.basis
 have ready:(∀q∈cs,u.basis q=false) ∧ u.basis cin=false ∧ regValue xs u.basis=H ∧
  regValue ys u.basis=((2^140-48*H)%2^140)/1024:=by
  simpa only [cs,xs,ys,u,head,H] using
   CHeadArithmeticResearch.ready acc pad bank cin src acc_length source_length fits s m hz hb hi ha
 have eraseBit(q:Wire)(hq:q∈domain):t.basis q=u.basis q:=by
  rw [te]
  exact C105LowEraseResearch.bit_same _ q (domain_away_low q hq)
 have eraseReg(r:List Wire)(sub:∀q∈r,q∈domain):regValue r t.basis=regValue r u.basis:=
  regValue_congr _ _ _ (fun q hq=>eraseBit q (sub q hq))
 have sy:regValue ys t.basis=((2^140-48*H)%2^140)/1024:=
  (eraseReg ys y_in).trans ready.2.2.2
 have sh:regValue xs t.basis=H:=
  (eraseReg xs x_in).trans ready.2.2.1
 have sb:∀q∈cs,t.basis q=false:=by
  intro q hq
  exact (eraseBit q (c_in q hq)).trans (ready.1 q hq)
 have si:t.basis cin=false:=
  (eraseBit cin cin_in).trans ready.2.1
 exact ReorderedCacheBits.forward_values 4 105 H (((2^140-48*H)%2^140)/1024) (976*H/1024)
  xs ys cs cin t (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide) raw_nd sb si sh sy (fun j hj=>by
   simpa only [show 130+10=140 by decide] using
    ReorderedCacheArithmetic.high_add_low 130 (4+j+1) H (by omega) hH)

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CPreInverseArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CPreInverseArithmeticResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem ready(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=4294968272*regValue src s.basis):
 let t:=run (C163Carry.unbuildPre acc Z bank cin src) m s
 (∀q∈bank.take 129,t.basis q=false) ∧ t.basis cin=false ∧
 regValue src t.basis=regValue src s.basis ∧
 regValue ((acc.take 140).drop 10) t.basis=976*regValue src s.basis/1024:=by
 let H:=regValue src s.basis
 let t:=run (C163Carry.unbuildPre acc Z bank cin src) m s
 have frame:=C163Carry.unbuildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have hf10:=hf _ (A161NarrowAcc.terms_mem src).2.1
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;>omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=frame.2.2 q (away q hq)
 have len:(acc.take 140).length=140:=by simp [hacc]
 have hH:H<2^130:=by simpa only [H,hsrc] using regValue_lt src s.basis
 have pref:=regValue_take_drop_of_lt acc 140 (976*H) t.basis
  (by omega) frame.2.1 (by norm_num at hH ⊢;omega)
 refine ⟨?_,?_,?_,?_⟩
 · intro q hq
   exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 · exact (same cin (Or.inr rfl)).trans hi
 · exact regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 · rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
   rfl

end ECDSAAdd.Entrant.CPreInverseArithmeticResearch

end

-- Verified ABC18 optimization component C105InverseReady
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem pre_raw_ready(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 (∀q∈cs,(run preInv m s).basis q=false) ∧ (run preInv m s).basis cin=false ∧
 regValue xs (run preInv m s).basis=H ∧ regValue ys (run preInv m s).basis=976*H/1024:=by
 have h:=CPreInverseArithmeticResearch.ready acc pad bank cin src acc_length source_length fits s m
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 (by rw [ready.2.1];exact ready.1)
 simpa only [preInv,xs,ys,cs,ready.2.1] using h

theorem scattered_erased_domain(s:State)(vs:List Bool)(q:Wire)(hq:q∈domain):
 (scatterState hosts vs (C105LowEraseResearch.erase s)).basis q=s.basis q:=by
 rw [scatter_outside hosts vs _ q (by intro bad;exact geometry.2.2 q bad hq)]
 exact C105LowEraseResearch.bit_same s q (domain_away_low q hq)

theorem inverse_ready(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 let vs:=ReorderedCacheBits.values 4 105 H (976*H/1024)
 let t:=scatterState hosts vs (C105LowEraseResearch.erase s)
 run newI m t=scatterState hosts (List.replicate hosts.length false) (run I m t):=by
 dsimp only
 let vs:=ReorderedCacheBits.values 4 105 H (976*H/1024)
 let t:=scatterState hosts vs (C105LowEraseResearch.erase s)
 have hH:H<2^130:=by rw [←ready.2.1];simpa only [source_length] using regValue_lt src s.basis
 have commute:run preInv m t=scatterState hosts vs (C105LowEraseResearch.erase (run preInv m s)):=by
  rw [show t=scatterState hosts vs (C105LowEraseResearch.erase s) from rfl,
   run_scatter preInv hosts vs _ _ preInv_off,
   C105LowEraseResearch.commute preInv m s (fun q hq=>preInv_off q (low_hosts q hq))]
 have bits(q:Wire)(hq:q∈domain):(run preInv m t).basis q=(run preInv m s).basis q:=by
  rw [commute]
  exact scattered_erased_domain _ vs q hq
 have regs(r:List Wire)(sub:∀q∈r,q∈domain):regValue r (run preInv m t).basis=regValue r (run preInv m s).basis:=
  regValue_congr _ _ _ (fun q hq=>bits q (sub q hq))
 have rr:=pre_raw_ready H s m ready
 have saved:hosts.map t.basis=vs:=scatter_saved_map hosts vs _ geometry.1
  (by simp only [vs,ReorderedCacheBits.values,List.length_map,geometry.2.1,List.length_range])
 apply inverse_frame t m H hH
 · intro q hq
   rw [bits q (c_in q hq)]
   exact rr.1 q hq
 · rw [bits cin cin_in]
   exact rr.2.1
 · rw [regs xs x_in]
   exact rr.2.2.1
 · rw [regs ys y_in]
   exact rr.2.2.2
 · exact saved

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105MiddleErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev oldF:Program:=ReorderedCPlain.build acc pad bank cin src
abbrev oldM:Program:=KnownCMidStaged.body
abbrev M:Program:=CKAliasesResearch.program

theorem measurements:measurementCount F=measurementCount oldF:=by
 rw [oldF,plain_split]
 simp only [F,measurementCount_append,C105LowEraseResearch.counts.2.1,Nat.add_zero,Nat.zero_add,List.append_assoc]

theorem middle_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 middleState F M s m=C105LowEraseResearch.erase (middleState oldF oldM s m):=by
 unfold middleState
 rw [measurements,CKAliasesResearch.counts.2.1,forward_erased s _ hz hb hi ha]
 exact C105LowEraseResearch.aliases_erased (regValue src s.basis) _ _
  (Ghost3CacheC.plain_ready s _ hz hb hi ha) after flag

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Restore
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem rawI_eq:rawI=Acc.op (acc.take 140) pad bank cin 140 true (Acc.earlyTerm src false 10):=by
 simp only [rawI,ReorderedConsumedSub.plain,Acc.op,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,
  source_length,Bool.false_eq_true,ite_false,Nat.sub_self,List.take_zero,List.append_nil,
  MixedLiteralAdderDevelop.read_add_eq,subInPlace]
 rfl

theorem I_source(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 ∀q∈src,(run I m s).basis q=s.basis q:=by
 have hH:regValue src s.basis<2^130:=by simpa only [source_length] using regValue_lt src s.basis
 have pre:=C163Carry.unbuildPre_triple acc pad bank cin src acc_length source_length fits s.basis
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2
 have sub:=ReorderedAcc.op_mod_prefix_triple acc pad bank cin 163 140 (Acc.earlyTerm src false 10)
  acc_length (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.1)
  (by simp only [Acc.earlyTerm,source_length];decide) (by norm_num [Acc.earlyTerm])
  s.basis ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 true (976*regValue src s.basis)
  (by norm_num at hH ⊢;omega)
 have frame:=(pre.seq sub) s m ⟨by rw [ready.2.1];exact ready.1,fun _ _=>rfl⟩
 have eq:I=C163Carry.unbuildPre acc pad bank cin src++Acc.op (acc.take 140) pad bank cin 140 true (Acc.earlyTerm src false 10):=by
  rw [I,rawI_eq];rfl
 have away:∀q∈src,q∉acc:=by decide +kernel
 intro q hq
 rw [eq]
 exact frame.2.2 q (away q hq)

theorem restored(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 run (I++C105LowEraseResearch.clear) m (C105LowEraseResearch.erase s)=run I m s:=by
 have cp:=low_copies H s ready
 have low(q:Wire)(hq:q∈C105LowEraseResearch.low):(run I m s).basis q=s.basis q:=
  run_preserves_outside I m s q (I_off q (low_hosts q hq))
 have source:=I_source H s m ready
 apply C105LowEraseResearch.suffix I s m (fun q hq=>I_off q (low_hosts q hq))
 · rw [low 4505 (by decide),source 4243 (by decide +kernel)]
   exact cp.1
 · rw [low 4506 (by decide),source 4244 (by decide +kernel)]
   exact cp.2.1
 · rw [low 4507 (by decide),source 4245 (by decide +kernel),source 4243 (by decide +kernel)]
   exact cp.2.2

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105UnbuildSplit
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev tail:Program:=ReorderedCUnbuild.after acc pad bank cin src

theorem unbuild_split:ReorderedCPlain.unbuild acc pad bank cin src=I++tail:=by
 simpa only [I,preInv,rawI,xs,ys,cs,tail] using ReorderedCUnbuild.plain_split acc pad bank cin src source_length

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105ErasedSuffix
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem erased_suffix(H:Nat)(u:State)(m:List Bool)(ready:WReady acc pad bank cin src H u):
 run (I++C105LowEraseResearch.clear++tail) m (C105LowEraseResearch.erase u)=run (I++tail) m u:=by
 exact ClearContextResearch.suffix I C105LowEraseResearch.clear tail C105LowEraseResearch.counts.2.1
  (C105LowEraseResearch.erase u) u m (restored H u m ready)


end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105PlainLoop
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem plain_loop(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run (F++M++(I++C105LowEraseResearch.clear++tail)) m s=
 run (oldF++oldM++ReorderedCPlain.unbuild acc pad bank cin src) m s:=by
 have eq:=middle_erased s m hz hb hi ha after flag
 apply ClearContextResearch.projected F M oldF oldM (I++C105LowEraseResearch.clear++tail)
  (ReorderedCPlain.unbuild acc pad bank cin src) C105LowEraseResearch.erase s m measurements
  CKAliasesResearch.counts.2.1 eq
 exact (erased_suffix _ _ _ after).trans
  (congrArg (fun P=>run P (m.drop (measurementCount oldF+measurementCount oldM))
   (middleState oldF oldM s m)) unbuild_split.symm)


end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105CacheLoop
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem cache_loop(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run (newF++M++newI) m s=run (F++M++I) m s:=by
 let H:=regValue src s.basis
 let vs:=ReorderedCacheBits.values 4 105 H (976*H/1024)
 have mid:=middle_erased s m hz hb hi ha after flag
 have forward:=forward_frame s (m.take (measurementCount F)) H
  (prefix_zero s _ hz hb hi ha zero) (forward_values s _ hz hb hi ha)
 apply CacheFromCleanForwardResearch.equivalent F newF M I newI hosts vs
  forward_measurements middle_fresh I_off geometry.1 s m
  (forward_zero s _ hz hb hi ha zero) forward
 rw [mid]
 exact inverse_ready H (middleState oldF oldM s m) _ after

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Core
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def core:Program:=(newF++M++newI)++(C105LowEraseResearch.clear++tail)

theorem inverse_measurements:measurementCount newI=measurementCount I:=by
 have h:=ReorderedConsumedSub.measurement_eq 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide)
 have eq:measurementCount HighConsumedC105Research.sub=measurementCount rawI:=
  HighConsumedC105Research.sub_measurements.trans h
 simp only [newI,I,measurementCount_append,eq]

theorem prefix_measurements:measurementCount (newF++M++newI)=measurementCount (F++M++I):=by
 simp only [measurementCount_append,forward_measurements,inverse_measurements]

theorem core_plain(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run core m s=run (oldF++oldM++ReorderedCPlain.unbuild acc pad bank cin src) m s:=by
 have eq:=ClearContextResearch.append_at (newF++M++newI) (F++M++I) (C105LowEraseResearch.clear++tail)
  s m prefix_measurements (cache_loop s m hz hb hi ha zero after flag)
 have shape:(F++M++I)++(C105LowEraseResearch.clear++tail)=F++M++(I++C105LowEraseResearch.clear++tail):=by
  have g(A B C D E:Program):(A++B++C)++(D++E)=A++B++(C++D++E):=by simp only [List.append_assoc]
  exact g F M I C105LowEraseResearch.clear tail
 exact eq.trans ((congrArg (fun P=>run P m s) shape).trans (plain_loop s m hz hb hi ha after flag))

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CKKnownMiddle
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKKnownMiddleResearch
open ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires C163Low4Middle.bankChecked

theorem measurements:measurementCount KnownCMidStaged.body=measurementCount C163Low4Middle.bankChecked.out:=
 (KnownSparseFold.Cert.counts _ _ _ _ _ KnownCMidStaged.cert).2

theorem equivalent(H:Nat)(s:State)(m:List Bool)
 (before:WReady ga pad bank L.core.cin src H s):
 run KnownCMidStaged.body m s=run C163Low4Middle.bankChecked.out m s:=by
 have z:KnownSparseFold.Zero KnownCMidStaged.known0 s:=by
  intro u hu
  rcases ReorderedKnownC.guard u hu with ⟨_,_,hb⟩
  exact hb.elim (fun h=>before.2.2.2.1 u h) (fun h=>h.symm ▸ before.2.2.2.2)
 exact (KnownSparseFold.Cert.correct _ _ _ _ _ KnownCMidStaged.cert s m z).1

theorem middle_eq(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis L.core.cin=false)(ha:regValue ga s.basis=0):
 middleState (ReorderedCPlain.build ga pad bank L.core.cin src) KnownCMidStaged.body s m=
 middleState (ReorderedCPlain.build ga pad bank L.core.cin src) C163Low4Middle.bankChecked.out s m:=by
 unfold middleState
 rw [measurements]
 exact equivalent _ _ _ (Ghost3CacheC.plain_ready s _ hz hb hi ha)


end ECDSAAdd.Entrant.CKKnownMiddleResearch

end

-- Verified ABC18 optimization component C105Frame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.C105Research
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
 InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires C163Low4Middle.bankChecked C163Low4Middle.specialChecked
abbrev p:=C163Low4Middle.p
theorem core_frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) core
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have len:=lengths
 have fit:=fits
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue ga s.basis=0:=C163Low4Ghost.ghostAcc_zero L s.basis clean
 have qz:s.basis q=false:=(regValue_zero _ _).mp clean.work q (by decide)
 have rz:s.basis r=false:=(regValue_zero _ _).mp clean.work r (by decide)
 have pz:s.basis p=false:=(hf.2 p (by decide)).trans hp
 have dz:s.basis d=false:=(hf.2 d (by decide)).trans hd
 have zeroU:∀u∈hs,s.basis u=false:=by
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · rcases List.mem_append.mp hu with hu|hu
    · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
    · have e:u=d:=by simpa only [List.mem_singleton] using hu
      subst u
      exact dz
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_take hu)
 have zeroOld:∀u∈ReorderedCFixed.hosts,s.basis u=false:=by
  intro u hu
  simp only [ReorderedCFixed.hosts,List.mem_cons] at hu
  rcases hu with rfl|rfl|rfl|hu
  · exact qz
  · exact rz
  · exact pz
  · exact zeroU u hu
 have offHs:∀u∈hs,u∉wires (ReorderedCPlain.build ga pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (by simp only [ReorderedCFixed.hosts,List.mem_cons];exact Or.inr (Or.inr (Or.inr hu)))).1
 have goodOld:=fun record=>good base hc O hO s record hf
 have goodSpecial:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) specialChecked.out s m):=by
  rw [ReorderedRetape.c_middle_eq ga pad bank L.core.cin src specialChecked.out
   len.1 len.2.2.2 fit s m hz hb clean.cin ha]
  exact goodOld _
 have middleEq:=bank_cert.middle_eq hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) s m zeroU offHs
 have goodBank:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) bankChecked.out s m):=by
  rw [middleEq]
  exact goodSpecial
 have knownEq:=CKKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
 have goodKnown:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) KnownCMidStaged.body s m):=by
  rw [knownEq]
  exact goodBank
 have buildFrame:=ReorderedCPlain.build_triple ga pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
  s.basis hz hb clean.cin s (m.take (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  ⟨ha,fun _ _=>rfl⟩
 have flag:(run (ReorderedCPlain.build ga pad bank L.core.cin src)
  (m.take (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src))) s).basis 4762=false:=
  (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
 have cachedNew:=core_plain s m hz hb clean.cin ha zeroOld goodKnown flag
 have midEq:run KnownCMidStaged.body (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s)=
  run C163Low4Middle.bankChecked.out (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using knownEq
 have ctxt:=ReorderedKnownA.context_eq
  (ReorderedCPlain.build ga pad bank L.core.cin src) C163Low4Middle.bankChecked.out KnownCMidStaged.body
  (ReorderedCPlain.unbuild ga pad bank L.core.cin src) s m CKKnownMiddleResearch.measurements midEq
 have cacheEq:=cachedNew.trans ctxt
 have middleReplace:=bank_cert.surround_eq hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) (ReorderedCPlain.unbuild ga pad bank L.core.cin src)
  s m zeroU offHs
 have plainEq:=ReorderedRetape.c_loop_eq ga pad bank L.core.cin src specialChecked.out
  len.1 len.2.2.2 fit s m hz hb clean.cin ha goodOld
 let record:=ReorderedRetape.tape (measurementCount (C163NarrowAcc.build8 ga pad bank L.core.cin src))
  (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)) m
 have oldFrame:=C163Low4Middle.frame base hc hp hd O hO s record hf
 rw [eq_plain base hc hp hd O hO s record hf] at oldFrame
 have finalEq:run core m s=run (C163NarrowAcc.build8 ga pad bank L.core.cin src++specialChecked.out++
  C163SourceAdd.unbuild ga pad bank L.core.cin src) record s:=cacheEq.trans (middleReplace.trans plainEq)
 exact transport (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)) s _ _ finalEq oldFrame



end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Sign
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.C105SignResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=C105Research.hosts
abbrev p:=C163Low4Middle.p

def suffix:Program:=C105LowEraseResearch.clear++
 ReorderedGenericCache.cachedAdd 105 C105Research.xs C105Research.ys C105Research.cs hosts L.core.cin++
 C105Research.top++C105Research.M++C105Research.newI++C105LowEraseResearch.clear++C105Research.tail

def loop:Program:=SignCHead.head++suffix

theorem loop_eq(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p)
 (s:State)(m:List Bool)(hf:SquareFrame L.core.out base O s.basis):
 run loop m s=run C105Research.core
  (SignRetape.tape SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) m) s:=by
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue ga s.basis=0:=ghostAcc_zero L s.basis clean
 have h:∀a b:List Bool,run SignCHead.head a s=run (ReorderedCHead.head ga pad bank L.core.cin src) b s:=by
  intro a b
  exact ReorderedFrameUnique.program_eq ga s.basis 0 ((2^140-48*regValue src s.basis)%2^140) _ _
   (SignCHead.frame s.basis hz hb clean.cin)
   (ReorderedCHead.head_triple ga pad bank L.core.cin src lengths.1 (by decide) fits s.basis hz hb clean.cin)
   s a b ⟨ha,fun _ _=>rfl⟩
 have eq:=SignRetape.replace SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) suffix s m h
 simpa only [loop,suffix,C105Research.core,C105Research.newF,C105Research.head,C105Research.xs,
  C105Research.ys,C105Research.cs,List.append_assoc] using eq


theorem frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have e:=loop_eq base hc O hO s m hf
 have old:=C105Research.core_frame base hc hp hd O hO s (SignRetape.tape SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) m) hf
 exact ReorderedCFixed.transport _ s _ _ e old

theorem fold_frame(base:BasisState)(hv:AccView L base (OwnDiagAll12Square.accCItem L))(hc:L.PairClean base)
 (M:Nat)(pv:regValue L.core.product base=M^2)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-Acc.accVal base 0 (OwnDiagAll12Square.accCItem L).spec else Acc.accVal base 0 (OwnDiagAll12Square.accCItem L).spec)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have f:=frame base hc (spare_zero L hw base M pv) hd O hO s m hf
 have e:=congrArg (fun A:Nat=>((if base g then C163Low4Facts.Klow-A else A)+(SquareReduction.p-1-O))%SquareReduction.p)
  (C163Fold.payload_spec L base)
 exact ⟨f.1,Eq.mp (congrArg (fun n:Nat=>SquareFrame L.core.out base n (run loop m s).basis) e) f.2⟩

def rawBody:Program:=C163Low4Body.bodyProgram L loop

theorem raw_body_frame(base:BasisState)(M:Nat)(pv:regValue L.core.product base=M^2)
 (clean:L.PairClean base)(disabled:base g=false→M=0)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) rawBody
  (SquareFrame L.core.out base (C163Low4Body.resCFK C163Low4Facts.Klow (base g) (M^2) O)):=by
 intro s m hf
 have away(q:Wire)(hq:q∈L.core.product):q∉L.core.out:=
  fun ho=>List.disjoint_left.mp (L.product_out_disjoint hn) hq ho
 have prod:regValue L.core.product s.basis=M^2:=
  (regValue_congr _ _ _ (fun q hq=>hf.2 q (away q hq))).trans pv
 have cs:=L.squareFrame_clean hn base s.basis O hf clean
 have gs:s.basis g=base g:=hf.2 g (by decide)
 have ds:s.basis d=false:=(hf.2 d (by decide)).trans hd
 have dm:s.basis g=false→M=0:=by rw [gs];exact disabled
 have out:=C163Low4Body.body_output L hw g (List.nodup_cons.mpr ⟨geometry.1,hn⟩)
  d loop C163Low4Facts.Klow cap fold_frame M O hO s m prod dm cs hf.1 ds
 rw [gs] at out
 exact ⟨out.1,out.2.1,fun q hq=>(out.2.2 q hq).trans (hf.2 q hq)⟩

def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin

theorem body_frame(base:BasisState)(M:Nat)(pv:regValue L.core.product base=M^2)
 (clean:L.PairClean base)(disabled:base g=false→M=0)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) body
  (SquareFrame L.core.out base (C163Low4Body.resCFK C163Low4Facts.Klow (base g) (M^2) O)):=by
 intro s m hf
 have f:=raw_body_frame base M pv clean disabled hd O hO s (m.take (measurementCount rawBody)) hf
 have hz:(run rawBody (m.take (measurementCount rawBody)) s).basis L.core.cin=false:=
  (f.2.2 L.core.cin (by decide)).trans clean.cin
 have eq:run body m s=run rawBody (m.take (measurementCount rawBody)) s:=by
  rw [body,run_append,ReorderedRecordPadding.run_zero 7 L.core.cin _ _ hz]
 exact ReorderedCFixed.transport _ s _ _ eq f



end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Counts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105SignResearch
open C105PrefixResearch C105Research Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem loop_counts:toffoliCount loop+3=toffoliCount HighSignCResearch.loop ∧
 measurementCount loop=measurementCount HighSignCResearch.loop:=by
 have aa:C163Low4Middle.ga=acc:=by decide +kernel
 have ap:C163Low4Middle.pad=pad:=by decide +kernel
 have ab:C163Low4Middle.bank=bank:=by decide +kernel
 have ax:C163Low4Middle.src=src:=by decide +kernel
 have ai:C163Low4Middle.L.core.cin=L.core.cin:=by decide +kernel
 have nc:=ReorderedGenericCache.count_balance 105 xs ys cs C105Research.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
 have oc:=ReorderedGenericCache.count_balance 102 xs ys cs Ghost3CacheC.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
 have ni:=HighConsumedC105Research.sub_toffoli
 have nm:=HighConsumedC105Research.sub_measurements
 have oi:=HighUnbuildCResearch.toffoli acc rfl
 have om:=HighUnbuildCResearch.measurements acc rfl
 have mt:=CKAliasesResearch.counts.1
 have mm:=CKAliasesResearch.counts.2.1
 have ot:=GhostRelocatedKnown.C.counts.1
 have omid:=GhostRelocatedKnown.C.counts.2
 have nt:=notRegister_counts ys
 simp only [ReorderedConsumedSub.consumed,toffoliCount_append,measurementCount_append] at ni nm oi om
 simp only [ReorderedCUnbuild.unbuild,ReorderedConsumedSub.consumed,toffoliCount_append,measurementCount_append] at oi om
 simp only [loop,suffix,newI,preInv,top,tail,M,HighSignCResearch.loop,HighSignCResearch.suffix,
  toffoliCount_append,measurementCount_append,C105LowEraseResearch.counts.1,C105LowEraseResearch.counts.2.1]
 simp only [xs,ys,cs,HighConsumedC105Research.xs,HighConsumedC105Research.ys,
  HighConsumedC105Research.cs,HighConsumedC105Research.cin,HighConsumedC105Research.hs,
  C105PrefixResearch.cin,CKAliasesResearch.original,Ghost3CacheC.middle,
  GhostRelocatedKnown.C.original,HighSignCResearch.hosts,C105SignResearch.hosts,aa,ap,ab,ax,ai] at *
 exact ⟨by omega,by omega⟩

 theorem body_counts:toffoliCount body+3=toffoliCount HighSignCResearch.body ∧
 measurementCount body=measurementCount HighSignCResearch.body:=by
 have h:=loop_counts
 simp only [body,rawBody,HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,
  toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩


end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Slots
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105SignResearch
open C105PrefixResearch C105Research Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Challenge.gateSlots
 theorem loop_slots:gateSlots loop+12=gateSlots HighSignCResearch.loop:=by
 have aa:C163Low4Middle.ga=acc:=by decide +kernel
 have ap:C163Low4Middle.pad=pad:=by decide +kernel
 have ab:C163Low4Middle.bank=bank:=by decide +kernel
 have ax:C163Low4Middle.src=src:=by decide +kernel
 have ai:C163Low4Middle.L.core.cin=L.core.cin:=by decide +kernel
 have nc:=ReorderedSlots.cache 105 xs ys cs C105Research.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide) geometry.2.1
 have oc:=ReorderedSlots.cache 102 xs ys cs Ghost3CacheC.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide) Ghost3CacheC.geometry.2.1
 have ni:=HighConsumedC105Research.sub_slots
 have oi:=HighUnbuildCResearch.slots acc rfl
 have mid:=CKAliasesResearch.counts.2.2
 have oldmid:=RelocateResources.slots GhostRelocatedKnown.ports KnownCMidStaged.body
 simp only [ReorderedConsumedSub.consumed,gateSlots_append] at ni
 simp only [ReorderedCUnbuild.unbuild,ReorderedConsumedSub.consumed,gateSlots_append] at oi
 simp only [loop,suffix,newI,preInv,top,tail,M,HighSignCResearch.loop,HighSignCResearch.suffix,
  gateSlots_append,C105LowEraseResearch.counts.2.2]
 simp only [xs,ys,cs,HighConsumedC105Research.xs,HighConsumedC105Research.ys,
  HighConsumedC105Research.cs,HighConsumedC105Research.cin,HighConsumedC105Research.hs,
  C105PrefixResearch.cin,CKAliasesResearch.original,Ghost3CacheC.middle,
  GhostRelocatedKnown.C.program,GhostRelocatedKnown.C.original,HighSignCResearch.hosts,C105SignResearch.hosts,aa,ap,ab,ax,ai] at *
 omega
 theorem body_slots:gateSlots body+12=gateSlots HighSignCResearch.body:=by
 have h:=loop_slots
 simp only [body,rawBody,HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,gateSlots_append]
 omega


end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Scope
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires
abbrev S:=wires HighSignCResearch.body
def oldPrefix:Program:=SignCHead.head++ReorderedGenericCache.cachedAdd 102 C163Low4Middle.src ((C163Low4Middle.ga.take 140).drop 10)
 (C163Low4Middle.bank.take 129) Ghost3CacheC.hosts C163Low4Middle.L.core.cin

theorem old_prefix_support:wires oldPrefix⊆S:=by
 intro q h
 simp only [oldPrefix,wires_append,Finset.mem_union] at h
 change q∈wires HighSignCResearch.body
 simp only [HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,
  HighSignCResearch.loop,HighSignCResearch.suffix,wires_append,Finset.mem_union]
 tauto

theorem old_middle_support:wires GhostRelocatedKnown.C.program⊆S:=by
 intro q h
 change q∈wires HighSignCResearch.body
 simp only [HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,
  HighSignCResearch.loop,HighSignCResearch.suffix,Ghost3CacheC.middle,wires_append,Finset.mem_union]
 tauto

end ECDSAAdd.Entrant.C105Research
end
end
end
