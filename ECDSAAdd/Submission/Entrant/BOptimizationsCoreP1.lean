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
import ECDSAAdd.Submission.Entrant.KnownZeroArithmetic

-- BOptimizationsCore = BOptimizationsCore ++ ACCache
-- ==== begin BOptimizationsCore ====
section

-- Rebalanced closed source chunks; all ordinary declarations and circuit literals retained.
section
section
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
namespace ECDSAAdd.Entrant.HighKnownAResearch



end ECDSAAdd.Entrant.HighKnownAResearch
end

section
namespace ECDSAAdd.Entrant.HighSignAResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=Ghost3CacheA.hosts


def suffix:Program:=ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin++
 A161Carry.buildPost acc pad bank L.core.cin src++Ghost3CacheA.middle++
 HighUnbuildAResearch.unbuild acc

def loop:Program:=SignAHead.head++suffix


































def fold:Program:=loop

def rawBody:Program:=measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)
















def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin















end ECDSAAdd.Entrant.HighSignAResearch
end

section
namespace ECDSAAdd.Entrant.HighKnownCResearch



end ECDSAAdd.Entrant.HighKnownCResearch
end

section
namespace ECDSAAdd.Entrant.HighSignCResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=Ghost3CacheC.hosts


def suffix:Program:=ReorderedGenericCache.cachedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin++
 C163Carry.buildPost ga pad bank L.core.cin src++Ghost3CacheC.middle++
 HighUnbuildCResearch.unbuild ga

def loop:Program:=SignCHead.head++suffix










































def rawBody:Program:=C163Low4Body.bodyProgram L loop



















def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin















end ECDSAAdd.Entrant.HighSignCResearch
end

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Baselines
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.HighBodyAResourceResearch
open ReorderedAFixed ControlLoan1589BFFold
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots

def withTail(u:Program):Program:=(measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(SignAHead.head++(ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin++
 A161Carry.buildPost acc pad bank L.core.cin src++Ghost3CacheA.middle++u))))++ReorderedRecordPadding.program 7 L.core.cin
def oldU:Program:=ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src Ghost3CacheA.hosts
def newU:Program:=HighUnbuildAResearch.unbuild acc

theorem old_shape:Ghost3SignA.body=withTail oldU:=by simp only [Ghost3SignA.body.eq_1,Ghost3SignA.rawBody.eq_1,Ghost3SignA.loop.eq_1,Ghost3SignA.suffix.eq_1,Ghost3SignA.hosts,withTail.eq_1,oldU.eq_1,Ghost3SignA.fold.eq_1]

theorem new_shape:HighSignAResearch.body=withTail newU:=by simp only [HighSignAResearch.body.eq_1,HighSignAResearch.rawBody.eq_1,HighSignAResearch.loop.eq_1,HighSignAResearch.suffix.eq_1,HighSignAResearch.hosts,withTail.eq_1,newU.eq_1,HighSignAResearch.fold.eq_1]

theorem tail_toffoli(u v:Program)(h:toffoliCount u+3=toffoliCount v):
 toffoliCount (withTail u)+3=toffoliCount (withTail v):=by
 simp only [withTail,toffoliCount_append]
 omega

theorem tail_measurements(u v:Program)(h:measurementCount u=measurementCount v):
 measurementCount (withTail u)=measurementCount (withTail v):=by
 simp only [withTail,measurementCount_append]
 omega

theorem tail_slots(u v:Program)(h:Challenge.gateSlots u+3=Challenge.gateSlots v):
 Challenge.gateSlots (withTail u)+3=Challenge.gateSlots (withTail v):=by
 simp only [withTail,Challenge.gateSlots_append]
 omega

theorem tail_support(u v:Program)(h:wires u⊆wires v):wires (withTail u)⊆wires (withTail v):=by
 simp only [withTail,wires_append]
 gcongr

theorem tail_physical(u v:Program)(h:GatePhysical u→GatePhysical v)(hp:GatePhysical (withTail u)):
 GatePhysical (withTail v):=by
 simp only [withTail,gatePhysical_append] at hp ⊢
 tauto

theorem toffoli:toffoliCount HighSignAResearch.body+3=toffoliCount Ghost3SignA.body:=by
 have a:=congrArg toffoliCount new_shape
 have b:=congrArg toffoliCount old_shape
 have e:toffoliCount newU+3=toffoliCount oldU:=by
  have e0:=HighUnbuildAResearch.toffoli acc rfl
  rw [show newU=HighUnbuildAResearch.unbuild acc from rfl,show oldU=ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src Ghost3CacheA.hosts from rfl]
  exact e0
 have q:=tail_toffoli newU oldU e
 omega

theorem measurements:measurementCount HighSignAResearch.body=measurementCount Ghost3SignA.body:=by
 have a:=congrArg measurementCount new_shape
 have b:=congrArg measurementCount old_shape
 have e:measurementCount newU=measurementCount oldU:=HighUnbuildAResearch.measurements acc rfl
 have q:=tail_measurements newU oldU e
 omega

theorem slots:Challenge.gateSlots HighSignAResearch.body+3=Challenge.gateSlots Ghost3SignA.body:=by
 have a:=congrArg Challenge.gateSlots new_shape
 have b:=congrArg Challenge.gateSlots old_shape
 have e:Challenge.gateSlots newU+3=Challenge.gateSlots oldU:=by
  have e0:=HighUnbuildAResearch.slots acc rfl
  rw [show newU=HighUnbuildAResearch.unbuild acc from rfl,show oldU=ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src Ghost3CacheA.hosts from rfl]
  exact e0
 have q:=tail_slots newU oldU e
 omega

theorem support:wires HighSignAResearch.body⊆wires Ghost3SignA.body:=by
 have q:wires newU⊆wires oldU:=HighUnbuildAResearch.support acc rfl
 calc
  _=wires (withTail newU):=congrArg wires new_shape
  _⊆wires (withTail oldU):=tail_support newU oldU q
  _=wires Ghost3SignA.body:=(congrArg wires old_shape).symm

theorem physical:GatePhysical HighSignAResearch.body:=by
 have h:=Eq.mp (congrArg GatePhysical old_shape) Ghost3BodyResources.a_physical
 have hu:GatePhysical oldU→GatePhysical newU:=HighUnbuildAResearch.physical acc rfl
 have hp:=tail_physical oldU newU hu h
 exact Eq.mpr (congrArg GatePhysical new_shape) hp




end ECDSAAdd.Entrant.HighBodyAResourceResearch

namespace ECDSAAdd.Entrant.HighABalance
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem counts:toffoliCount HighSignAResearch.body+6=toffoliCount SignKnownA.body ∧
 measurementCount HighSignAResearch.body=measurementCount SignKnownA.body:=by
 have q:=HighBodyAResourceResearch.toffoli
 have old:=Ghost3ABalance.counts
 exact ⟨by omega,HighBodyAResourceResearch.measurements.trans old.2⟩

theorem slots:Challenge.gateSlots HighSignAResearch.body+4=Challenge.gateSlots SignKnownA.body:=by
 have q:=HighBodyAResourceResearch.slots
 have old:=Ghost3ABalance.slots
 omega
end ECDSAAdd.Entrant.HighABalance

namespace ECDSAAdd.Entrant.HighBodyCResourceResearch
open C163Low4Middle ControlLoan1589BFFold
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots

def withTail(u:Program):Program:=(mixFoldsQTq L false [.inl (negRot L)]++(SignCHead.head++(ReorderedGenericCache.cachedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin++
 C163Carry.buildPost ga pad bank L.core.cin src++Ghost3CacheC.middle++u)))++ReorderedRecordPadding.program 7 L.core.cin
def oldU:Program:=ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src Ghost3CacheC.hosts
def newU:Program:=HighUnbuildCResearch.unbuild ga

theorem old_shape:Ghost3SignC.body=withTail oldU:=by simp only [Ghost3SignC.body.eq_1,Ghost3SignC.rawBody.eq_1,Ghost3SignC.loop.eq_1,Ghost3SignC.suffix.eq_1,Ghost3SignC.hosts,withTail.eq_1,oldU.eq_1,C163Low4Body.bodyProgram.eq_1]

theorem new_shape:HighSignCResearch.body=withTail newU:=by simp only [HighSignCResearch.body.eq_1,HighSignCResearch.rawBody.eq_1,HighSignCResearch.loop.eq_1,HighSignCResearch.suffix.eq_1,HighSignCResearch.hosts,withTail.eq_1,newU.eq_1,C163Low4Body.bodyProgram.eq_1]

theorem tail_toffoli(u v:Program)(h:toffoliCount u+3=toffoliCount v):
 toffoliCount (withTail u)+3=toffoliCount (withTail v):=by
 simp only [withTail,toffoliCount_append]
 omega

theorem tail_measurements(u v:Program)(h:measurementCount u=measurementCount v):
 measurementCount (withTail u)=measurementCount (withTail v):=by
 simp only [withTail,measurementCount_append]
 omega

theorem tail_slots(u v:Program)(h:Challenge.gateSlots u+3=Challenge.gateSlots v):
 Challenge.gateSlots (withTail u)+3=Challenge.gateSlots (withTail v):=by
 simp only [withTail,Challenge.gateSlots_append]
 omega

theorem tail_support(u v:Program)(h:wires u⊆wires v):wires (withTail u)⊆wires (withTail v):=by
 simp only [withTail,wires_append]
 gcongr

theorem tail_physical(u v:Program)(h:GatePhysical u→GatePhysical v)(hp:GatePhysical (withTail u)):
 GatePhysical (withTail v):=by
 simp only [withTail,gatePhysical_append] at hp ⊢
 itauto

theorem toffoli:toffoliCount HighSignCResearch.body+3=toffoliCount Ghost3SignC.body:=by
 have a:=congrArg toffoliCount new_shape
 have b:=congrArg toffoliCount old_shape
 have e:toffoliCount newU+3=toffoliCount oldU:=by
  have e0:=HighUnbuildCResearch.toffoli ga rfl
  rw [show newU=HighUnbuildCResearch.unbuild ga from rfl,show oldU=ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src Ghost3CacheC.hosts from rfl]
  exact e0
 have q:=tail_toffoli newU oldU e
 omega

theorem measurements:measurementCount HighSignCResearch.body=measurementCount Ghost3SignC.body:=by
 have a:=congrArg measurementCount new_shape
 have b:=congrArg measurementCount old_shape
 have e:measurementCount newU=measurementCount oldU:=HighUnbuildCResearch.measurements ga rfl
 have q:=tail_measurements newU oldU e
 omega

theorem slots:Challenge.gateSlots HighSignCResearch.body+3=Challenge.gateSlots Ghost3SignC.body:=by
 have a:=congrArg Challenge.gateSlots new_shape
 have b:=congrArg Challenge.gateSlots old_shape
 have e:Challenge.gateSlots newU+3=Challenge.gateSlots oldU:=by
  have e0:=HighUnbuildCResearch.slots ga rfl
  rw [show newU=HighUnbuildCResearch.unbuild ga from rfl,show oldU=ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src Ghost3CacheC.hosts from rfl]
  exact e0
 have q:=tail_slots newU oldU e
 omega

theorem support:wires HighSignCResearch.body⊆wires Ghost3SignC.body:=by
 have q:wires newU⊆wires oldU:=HighUnbuildCResearch.support ga rfl
 calc
  _=wires (withTail newU):=congrArg wires new_shape
  _⊆wires (withTail oldU):=tail_support newU oldU q
  _=wires Ghost3SignC.body:=(congrArg wires old_shape).symm

theorem physical:GatePhysical HighSignCResearch.body:=by
 have h:=Eq.mp (congrArg GatePhysical old_shape) Ghost3BodyResources.c_physical
 have hu:GatePhysical oldU→GatePhysical newU:=HighUnbuildCResearch.physical ga rfl
 have hp:=tail_physical oldU newU hu h
 exact Eq.mpr (congrArg GatePhysical new_shape) hp




end ECDSAAdd.Entrant.HighBodyCResourceResearch

namespace ECDSAAdd.Entrant.HighCBalance
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem counts:toffoliCount HighSignCResearch.body+6=toffoliCount SignKnownC.body ∧
 measurementCount HighSignCResearch.body=measurementCount SignKnownC.body:=by
 have q:=HighBodyCResourceResearch.toffoli
 have old:=Ghost3CBalance.counts
 exact ⟨by omega,HighBodyCResourceResearch.measurements.trans old.2⟩

theorem slots:Challenge.gateSlots HighSignCResearch.body+4=Challenge.gateSlots SignKnownC.body:=by
 have q:=HighBodyCResourceResearch.slots
 have old:=Ghost3CBalance.slots
 omega
end ECDSAAdd.Entrant.HighCBalance

namespace ECDSAAdd.Entrant.HighBodyResources
attribute [local irreducible] ECDSAAdd.wires

theorem a_support:wires HighSignAResearch.body⊆wires Ghost3KnownA.body:=
 HighBodyAResourceResearch.support.trans Ghost3BodyResources.a_support

theorem c_support:wires HighSignCResearch.body⊆wires Ghost3KnownC.body:=
 HighBodyCResourceResearch.support.trans Ghost3BodyResources.c_support




end ECDSAAdd.Entrant.HighBodyResources

end

section

section
open ECDSAAdd ECDSAAdd.Entrant ZeroReadDevelop
namespace ECDSAAdd.Entrant.FullPadASteps

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                                                                                                                           
                   
end ECDSAAdd.Entrant.FullPadASteps

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullAReady
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ZeroReadDevelop
open ECDSAAdd.Entrant.FullASelectedDevelop

set_option maxRecDepth 100000
set_option maxHeartbeats 500000000

def L := Baselines.layout.dialogStreamedSquareWide
def c := Baselines.layout.core.generic
                                                                                                                                                                                   
                               
                                                                                                                                                                                                                             









                         
end ECDSAAdd.Entrant.FullAReady

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullAReady
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ZeroReadDevelop FullASelectedDevelop

set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
                                                                                    
                                                                                                                                        
                                                                    
                                                                                       
                                                                                     
                                                                                                                                                                                                                  
                                                                                                   

                                                              
                                                                                             




theorem onePass_input_eq : ParkAData.p0=aMiddle L c := ParkAStagedProof.input_eq
attribute [local irreducible] ZeroSetDevelop.compileS?




end ECDSAAdd.Entrant.FullAReady

namespace ECDSAAdd.Entrant.FullASelectedDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false






















theorem eU_off_aBodySelected (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (c:Wire) (hc:c∉L.wires):eU L∉wires (aBodySelected L c):=by
 intro h
 rcases Finset.mem_insert.mp (aBodySelected_refined L hw c h) with e|h
 · exact (ThirdSavedCarryDevelop.spare_ne_eU L hw hn) e.symm
 · exact InverseCarryDevelop.eU_off_aBodyDual L hw hn c hc h

theorem hostedASelected_fold_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths)
 (hn:L.wires.Nodup) (ext:List Wire) (c:Wire) (hlen:300≤ext.length) (away:∀q∈ext,q∉L.wires):
 wires (hostedASelected L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset:=by
 rw [hostedASelected_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact aBodySelected_support L hw hn c


end ECDSAAdd.Entrant.FullASelectedDevelop

end

end

section

section
section


-- ===== Five-tick forward window: the TickGap forward stack now uses Five506 =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed Secp256k1 OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  forward stackForward0 Rolling1588.forward Rolling1588.stackForward

/-- The forward stack: ticks 1..505, then the jointly re-synthesized five-tick window
(tick 506 and ticks 507..510), then the unchanged tail. -/
def stackForward (isA : Bool) : Program := Six505.stackForward6 isA

theorem stackForward_metrics (isA : Bool) :
    toffoliCount (stackForward isA)+69=toffoliCount (Rolling1588.stackForward isA) ∧
      measurementCount (stackForward isA)=measurementCount (Rolling1588.stackForward isA) ∧
      Challenge.gateSlots (stackForward isA) ≤ Challenge.gateSlots (Rolling1588.stackForward isA)+1005 := by
  have old := stackForward0_metrics isA
  have c := Five506.counts5
  have sl := Five506.slots5
  have c6 := Six505.counts6
  have s6 := Six505.slots6
  rw [Five506.shape, Six505.forward_split] at old
  rw [stackForward, Six505.stackForward6]
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append] at old ⊢
  exact ⟨by omega, by omega, by omega⟩

theorem stackForward_support (isA : Bool) :
    wires (stackForward isA)⊆wires (Rolling1588.stackForward isA) :=
  (Six505.support6 isA).trans (stackForward0_support isA)

theorem stackForward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=run (Rolling1588.stackForward isA) m s := by
  rw [stackForward, Six505.stackForward6_run_eq isA x hx0 hx s m first]
  exact stackForward0_run_eq isA x hx0 hx s m first

                                          
                                                                             
                                                                
                                       
                                                                    
                                                  
                                                  
                                                              
                                                 
                                                                       

theorem stack_roundtrip (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (Rolling1588.stackReverse isA) mD (run (stackForward isA) mE s)=s := by
  rw [stackForward_run_eq isA x hx0 hx s mE first]
  exact Rolling1588.stack_roundtrip isA hn hlo x hx0 hx s mE mD first

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- five-tick bridge

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Native
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Kernel
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588KernelResources

/-! The new forward phase has the exact old A/B State boundary. All native,
field, inverse, host, and caller interfaces are retained. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Challenge Baselines
  FrontierEntry1591Callers OB5
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  forward stackForward Rolling1588.forward Rolling1588.stackForward Rolling1588.stackReverse
  FrontierEntry1591Native.forward FrontierEntry1591Native.inverse
  Rolling1588.firstPhase Rolling1588.lastPhase

def tailPhase (isA : Bool) : Program := stackForward isA++skywalkArithmeticClear base

def firstPhase (isA : Bool) : Program := FrontierEntry1591Native.forward base++tailPhase isA

def oldKernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def kernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def entryKernel : Program := kernel true false Rolling1588.entryFieldHosted
def exitKernel : Program := kernel false true Rolling1588.exitFieldHosted

attribute [local irreducible] tailPhase firstPhase oldKernel kernel entryKernel exitKernel
  Rolling1588.entryKernel Rolling1588.exitKernel

private theorem first_run_eq_of_stack (N F F0 C : Program) (s : State) (m : List Bool)
    (records : measurementCount F=measurementCount F0)
    (same : ∀mn mf,run F mf (run N mn s)=run F0 mf (run N mn s)) :
    run (N++(F++C)) m s=run (N++(F0++C)) m s := by
  simp only [run_append,records]
  rw [same]

theorem first_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=run (Rolling1588.firstPhase isA) m s := by
  have same (mn mf : List Bool) :
      run (stackForward isA) mf (run (FrontierEntry1591Native.forward base) mn s)=
        run (Rolling1588.stackForward isA) mf
          (run (FrontierEntry1591Native.forward base) mn s) :=
    stackForward_run_eq isA x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [firstPhase,tailPhase,Rolling1588.firstPhase,List.append_assoc] using
    first_run_eq_of_stack (FrontierEntry1591Native.forward base) (stackForward isA)
      (Rolling1588.stackForward isA) (skywalkArithmeticClear base) s m
      (stackForward_metrics isA).2.1 same






                                                                       
                                                                         
                                                                                   
                                                                                       
                        
                                                                 
                                                                             
                                              
                                                                     

                                                                       
                                                                         
                                                                                   
                                                  
                                                 
                                                                             
                                              
                                                                     

                                                                          
                                                                         
                                                                                   
                                                
                                                  
                                                                                          
                                                     
                                                                                          
                                               
                                                                          

                                                                            
                                                                         
                                                                                       
                                                                          
                                                
                                                                                

theorem first_metrics (isA : Bool) :
    toffoliCount (firstPhase isA)+69=toffoliCount (Rolling1588.firstPhase isA) ∧
      measurementCount (firstPhase isA)=measurementCount (Rolling1588.firstPhase isA) ∧
      gateSlots (firstPhase isA) ≤ gateSlots (Rolling1588.firstPhase isA)+1005 := by
  have stack := stackForward_metrics isA
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem first_support (isA : Bool) :
    wires (firstPhase isA)⊆wires (Rolling1588.firstPhase isA) := by
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,wires_append,Finset.union_assoc]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (stackForward_support isA) (Finset.Subset.refl _))

private theorem mapped_code_physical (isA : Bool) (f : Fin 10→Wire)
    (hf : Function.Injective f) :
    GatePhysical (renameProgram (MeasuredCodec5.label f) (Rolling1588.codeEncode isA)) := by
  have support : wires (Rolling1588.codeEncode isA)⊆Finset.range 10 := by
    simpa only [(Rolling1588.code_support isA).1] using
      (Finset.Subset.refl (Finset.range 10))
  exact gatePhysical_rename_support _ _
    (fun a ha b hb eq=>FirstNonzeroCodec.label_inj' f hf a (support ha) b (support hb) eq)
    (Rolling1588.code_physical isA).1

private theorem pack_physical (isA : Bool) (i : Nat) (hi : i<512) :
    GatePhysical (Rolling1588.packAtTick isA i) := by
  by_cases first : i=5
  · simp only [Rolling1588.packAtTick,if_pos first]
    exact (ParityCodec5New.first_mapped_physical _
      (History5.historyMap_injective base base_pool_nodup 0 (by decide))).1
  · simp only [Rolling1588.packAtTick,if_neg first]
    split
    · have due := History5.packDue_true i ‹History5.packDue i=true›
      exact mapped_code_physical isA _
        (History5.historyMap_injective base base_pool_nodup (i-5) (by omega))
    · simp [GatePhysical]

theorem forward_physical (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    GatePhysical (forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have pack : GatePhysical (Rolling1588.Integer.packFirst base isA i) := by
      rw [Rolling1588.Integer.packFirst_base]
      exact pack_physical isA i (by omega)
    rw [forward,gatePhysical_append]
    exact ⟨gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr
        ⟨TickRanges.tick_physical base i (by omega) base_pool_nodup,pack⟩),
      ih (i+1) (by omega)⟩

theorem stackForward_physical (isA : Bool) : GatePhysical (stackForward isA) := by
  have old := Rolling1588.stackForward_physical isA
  rw [MorningPlacement.previous_shape] at old
  simp only [gatePhysical_append] at old
  have h5 := forward_physical isA 1 505 (by omega)
  rw [Six505.forward_split] at h5
  simp only [gatePhysical_append] at h5
  rw [stackForward, Six505.stackForward6, Six505.merged6]
  simp only [gatePhysical_append]
  exact ⟨h5.1, gatePhysical_rename _ (sig_injective 510 (by omega)) _ Six505.physical,h5.2.2,old.2.2⟩

theorem first_physical (isA : Bool) : GatePhysical (firstPhase isA) := by
  have old := Rolling1588.firstPhase_physical isA
  simp only [Rolling1588.firstPhase,gatePhysical_append] at old
  simpa only [firstPhase,tailPhase,gatePhysical_append] using
    And.intro old.1.1 (And.intro (stackForward_physical isA) old.2)

private theorem mapped_run_eq (f : Equiv.Perm Wire) (P Q : Program)
    (s : State) (m : List Bool) (clean : pullState f s=s)
    (same : run P m s=run Q m s) :
    run (renameProgram f P) m s=run (renameProgram f Q) m s := by
  apply pullState_perm_injective f
  rw [run_rename _ f.injective,run_rename _ f.injective,clean]
  exact same

theorem first_hosted_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (renameProgram Rolling1588Lifetime.phaseHost (firstPhase isA)) m s=
      run (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase isA)) m s := by
  exact mapped_run_eq Rolling1588Lifetime.phaseHost _ _ s m
    (Rolling1588Lifetime.pull_phase_clean s
      (Rolling1588Lifetime.caller_phase_clean x y s input))
    (first_run_eq isA hn x y hx0 hx s m input)

private theorem append_run_eq_tickgap_phases (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernel_run_eq (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel a b F) m s=run (oldKernel a b F) m s := by
  have records :
      measurementCount (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))=
        measurementCount (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(first_metrics a).2.1]
  simpa only [kernel,oldKernel] using append_run_eq_tickgap_phases
    (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a))
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) s m records
    (fun r=>first_hosted_run_eq a hn x y hx0 hx s r input)

                                                   
                                                                   
                                                                          
                                                                       
                               
                                                                                           
                                                                               
                                    

private theorem mapped_append_support (f : Wire→Wire) (P Q R : Program)
    (first : wires P⊆wires Q) :
    wires (renameProgram f P++R)⊆wires (renameProgram f Q++R) := by
  rw [wires_append,wires_append,renameProgram_support,renameProgram_support]
  exact Finset.union_subset_union
    (Finset.image_mono f first) (Finset.Subset.refl _)

theorem kernel_support (a b : Bool) (F : Program) :
    wires (kernel a b F)⊆wires (oldKernel a b F) := by
  simpa only [kernel,oldKernel] using
    mapped_append_support Rolling1588Lifetime.phaseHost
      (firstPhase a) (Rolling1588.firstPhase a)
      (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) (first_support a)

theorem kernel_physical (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel a b F) := by
  simpa only [kernel,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (first_physical a))
      (And.intro field
        (Rolling1588Lifetime.phase_physical _ (Rolling1588.lastPhase_physical b)))

theorem kernel_entry_correct (F : Program) (raw : EntryCorrect (oldKernel true false F)) :
    EntryCorrect (kernel true false F) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [kernel_run_eq true false F hn x _ hx0 hx t m actual]
  exact raw hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half







theorem entry_correct : EntryCorrect entryKernel := by
  have old : EntryCorrect (oldKernel true false Rolling1588.entryFieldHosted) := by
    simpa only [oldKernel,Rolling1588.entryKernel] using Rolling1588.entry_correct
  simpa only [entryKernel] using kernel_entry_correct Rolling1588.entryFieldHosted old






                                                     
                              
                                                 
                                                                               
                                      
                                                                                  
            
             
               

                             
                                                                      
                                                                             
                                                                          
                                                                              
                      
       
                                                                                              
                                            
       
                                                             
                                                    
                                                                  
                                                            

                            
                                                                    
                                                                           
                                                                        
                                                                            
                     
       
                                                                                            
                                           
       
                                                           
                                                   
                                                                 
                                                           

theorem entryKernel_support_subset : wires entryKernel⊆wires Rolling1588.entryKernel := by
  simpa only [entryKernel,oldKernel,Rolling1588.entryKernel] using
    kernel_support true false Rolling1588.entryFieldHosted

theorem exitKernel_support_subset : wires exitKernel⊆wires Rolling1588.exitKernel := by
  simpa only [exitKernel,oldKernel,Rolling1588.exitKernel] using
    kernel_support false true Rolling1588.exitFieldHosted

theorem entryKernel_support : wires entryKernel⊆OB5Support.logicalSites :=
  entryKernel_support_subset.trans Rolling1588.entryKernel_support

theorem exitKernel_support : wires exitKernel⊆OB5Support.logicalSites :=
  exitKernel_support_subset.trans Rolling1588.exitKernel_support

theorem entryKernel_physical : GatePhysical entryKernel := by
  simpa only [entryKernel] using
    kernel_physical true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exitKernel_physical : GatePhysical exitKernel := by
  simpa only [exitKernel] using
    kernel_physical false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

                                                                                          
                                                                               

                                                                                        
                                                                             

                                                            
                                                                              
                                                          
                                                                            
                                                            
                                                                              
                                                          
                                                                            
                                                            
                                                                              
                                                          
                                                                            
theorem entryKernel_760_free : base 760∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_760_free (entryKernel_support_subset used)
theorem exitKernel_760_free : base 760∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_760_free (exitKernel_support_subset used)

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGap =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Final
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases

/-! E1 entries and the reflected square are unchanged. Only the two
forward tails use the checked TickGap program. Both inverse phases stay. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)++
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))

def entryStage (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky++E1QubitPlacement.entryM L kx++restE L

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  ReflectionE1.squareEntry L k++restX L++exitY L cy

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L=
      E1QubitPlacement.tickF L++restE L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,Rolling1588TickGap.entryKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restE,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L=
      E1QubitPlacement.tickF L++restX L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,Rolling1588TickGap.exitKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restX,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

section CorrectStages
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryStage_step (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStage L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  have add:=fastStep_addX L hw hn X Y G origin kx
  have divide:=division_step Rolling1588TickGap.entryKernel Rolling1588TickGap.entryKernel_support
    Rolling1588TickGap.entry_correct L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior:=add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky++E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx++fusedY L ky++E1QubitPlacement.tickF L)
    (R:=restE L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryStage,division,entry_split,List.append_assoc] using prior

                                                                         
                                                                                  
                               
                                                                                   
                          
                                                                  
                                                                        
                                                                                
                                                             
                                                
                                           
                                                                   
                                                                                     
                                              
                                             
                                           
                                           
                                     
                                     
                                                                                             
                            
                   
                                                                      
                                                                                     

end CorrectStages

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage L (-cx) (-cy)++secondStage L (ReflectionE1.correction cx) cy++fastConstNeg L cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

                                                            
                                                                  

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

                                                                       
                                    
                                                                  
                                                                                       
                               
                              
                                              
                                                                 
                                                                      
                                
                                                 
                                                                                       
                  
                                 
           
                                  
        
                                                                                            
                                          
                                   
                                                              
                               
                                                               
                                                                  
                                     

                                                                         
                                                                   
                                                  
                                                                  
                                                                   
                                                                                            
                                                                            
                                                        
                                           
                                                                                  
                     
                                     


                                                                                                  
                                                                                          
                                          
                                    
                                                                      
                                                                                                  
                                         
                                                                                       
                                  
                           
                                                                        
                                      
                                                                              
                                                                                                
                                                                                                
                                                           
            
                                    
                                           
                         
                
                          


                                                                           
                                      
                      
                                           
                                                                             
                                                                                                         
                                                                                      
                       
                                                                                             
              
           
                                            
                                
           
                                 
                                                                  
                                                              
                                                      
                                                                                     
                                                                          
                                                                               
                                                     
                                                                                     
                                                          
                      
           
                                                                                               
                                            
                   
                                                     
                                                                           
                                    
              
                                                                    
                                                                
                                                                           
                                                                           
                                                                                              
                                                                           
                                                            
                        
                                              
                                                                                                 
                                              
             
                      
                                                                            
                                                                
                                                                      
                                                                   
                                                                
                                                                          
                                                                                                                
                                                                                    
                                                                                                      
                                    
                                                            
                        
                                                                       
                                                                                                 
                                              

end Correct
attribute [local irreducible] restE restX entryStage secondStage generic mid gen
  ReflectionE1.restE ReflectionE1.restX ReflectionE1.tailP ReflectionE1.generic ReflectionE1.gen
  Rolling1588TickGap.tailPhase Rolling1588TickGap.stackForward Rolling1588.stackForward
  Rolling1588.firstPhase Rolling1588.lastPhase Rolling1588.entryFieldHosted Rolling1588.exitFieldHosted

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (n g : Nat) (P Q : Program) : Prop :=
  toffoliCount P+n=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
    gateSlots P ≤ gateSlots Q+g ∧ wires P⊆wires Q

private theorem append_facts (P Q C : Program)
    (count : toffoliCount P+69=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
      gateSlots P ≤ gateSlots Q+1005) (sub : wires P⊆wires Q) : Facts 69 1005 (P++C) (Q++C) := by
  simp only [Facts,toffoliCount_append,measurementCount_append,gateSlots_append,wires_append]
  exact ⟨by omega,by omega,by omega,Finset.union_subset_union sub (Finset.Subset.refl _)⟩

private theorem tail_facts (a : Bool) :
    Facts 69 1005 (Rolling1588TickGap.tailPhase a) (ReflectionE1.tailP a) := by
  apply relation_of_shapes (Facts 69 1005) _ _
    (Rolling1588TickGap.stackForward a++skywalkArithmeticClear base)
    (Rolling1588.stackForward a++skywalkArithmeticClear base)
  · unfold Rolling1588TickGap.tailPhase
    rfl
  · unfold ReflectionE1.tailP
    rfl
  · exact append_facts _ _ _ (Rolling1588TickGap.stackForward_metrics a)
      (Rolling1588TickGap.stackForward_support a)

private def restContext (f g : Wire→Wire) (P R : Program) : Program :=
  renameProgram f (renameProgram g P++R)

private theorem rest_facts (f g : Wire→Wire) (P Q R : Program) (h : Facts 69 1005 P Q) :
    Facts 69 1005 (restContext f g P R) (restContext f g Q R) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (restContext f g P R)⊆wires (restContext f g Q R) := by
    simp only [restContext,renameProgram_support,wires_append]
    exact Finset.image_mono f
      (Finset.union_subset_union (Finset.image_mono g hw) (Finset.Subset.refl _))
  simp only [Facts,restContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem restE_facts (L : ControlledPointLayout) :
    Facts 69 1005 (restE L) (ReflectionE1.restE L) := by
  apply relation_of_shapes (Facts 69 1005) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
  · unfold restE restContext
    rfl
  · unfold ReflectionE1.restE restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts true)

private theorem restX_facts (L : ControlledPointLayout) :
    Facts 69 1005 (restX L) (ReflectionE1.restX L) := by
  apply relation_of_shapes (Facts 69 1005) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
  · unfold restX restContext
    rfl
  · unfold ReflectionE1.restX restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts false)

private def stagesContext (Y M E S X EY N : Program) : Program :=
  (Y++M++E)++(S++X++EY)++N

private theorem stages_facts (Y M E E0 S X X0 EY N : Program)
    (entry : Facts 69 1005 E E0) (exit : Facts 69 1005 X X0) :
    Facts 138 2010 (stagesContext Y M E S X EY N) (stagesContext Y M E0 S X0 EY N) := by
  rcases entry with ⟨et,em,es,ew⟩
  rcases exit with ⟨xt,xm,xs,xw⟩
  have sub : wires (stagesContext Y M E S X EY N)⊆
      wires (stagesContext Y M E0 S X0 EY N) := by
    simp only [stagesContext,wires_append]
    exact Finset.union_subset_union
      (Finset.union_subset_union
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
          (Finset.Subset.refl _)) ew)
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) xw)
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,stagesContext,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold generic entryStage secondStage stagesContext
  rfl

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1.generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold ReflectionE1.generic ReflectionE1.entryStage ReflectionE1.secondStage stagesContext
  rfl

private theorem generic_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 138 2010 (generic L cx cy) (ReflectionE1.generic L cx cy) := by
  exact relation_of_shapes (Facts 138 2010) _ _ _ _
    (generic_shape L cx cy) (old_generic_shape L cx cy)
    (stages_facts (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx)
      (restE_facts L) (restX_facts L))

theorem generic_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1.generic L cx cy) :=
  (generic_facts L cx cy).2.2.2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_subset L cx cy).trans (ReflectionE1.generic_sites L hw hn cx cy)

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) :=
  fun used=>ReflectionE1.generic_free L hw hn cx cy i hi (generic_support_subset L cx cy used)

private theorem suffix_physical (P Q R : Program) (shape : P=Q++R)
    (physical : GatePhysical P) : GatePhysical R := by
  rw [shape,gatePhysical_append] at physical
  exact physical.2

private theorem restE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restE L) := by
  have physical := placed_physical Rolling1588TickGap.entryKernel
    Rolling1588TickGap.entryKernel_support Rolling1588TickGap.entryKernel_physical L hw hn
  have entryPhysical : GatePhysical (FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.entry;rfl) physical
  exact suffix_physical _ _ _ (entry_split L) entryPhysical

private theorem restX_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restX L) := by
  have physical := placed_physical Rolling1588TickGap.exitKernel
    Rolling1588TickGap.exitKernel_support Rolling1588TickGap.exitKernel_physical L hw hn
  have exitPhysical : GatePhysical (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.exit;rfl) physical
  exact suffix_physical _ _ _ (exit_split L) exitPhysical

private theorem stages_physical (Y M E E0 S X X0 EY N : Program)
    (old : GatePhysical (stagesContext Y M E0 S X0 EY N))
    (entry : GatePhysical E) (exit : GatePhysical X) :
    GatePhysical (stagesContext Y M E S X EY N) := by
  simp only [stagesContext,gatePhysical_append] at old ⊢
  exact And.intro
    (And.intro (And.intro old.1.1.1 entry)
      (And.intro (And.intro old.1.2.1.1 exit) old.1.2.2)) old.2

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old := fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1.generic_physical L hw hn cx cy)
  exact fact_of_shape GatePhysical _ _ (generic_shape L cx cy)
    (stages_physical (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) old
      (restE_physical L hw hn) (restX_physical L hw hn))

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program)
    (h : Facts 138 2010 P Q) : Facts 138 2010 (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (wrapContext Z C f P)⊆wires (wrapContext Z C f Q) := by
    simp only [wrapContext,wires_append,renameProgram_support]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union
          (Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono f hw))
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem gen_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 138 2010 (gen L cx cy) (ReflectionE1.gen L cx cy) := by
  apply relation_of_shapes (Facts 138 2010) _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1.gen ReflectionE1.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L cx cy)

                                                              
                                                                            
                                                                                
                                                                          
                                                                           

                                                                     
                                                                                     

                                                                                  
                                                                              
                                                                           

                                                                                     
                                                   
                            
                               
                                                                                                    
                                                                                                        

                                                 
                                                                      
                
                                                                                                             
                                                                        
                                                                        
                                                                             
            
                                                              
                                                                                             
       

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts 138 2010 P Q) :
    toffoliCount (Edges.wrapper L C cy P)+138=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P) ≤ gateSlots (Edges.wrapper L C cy Q)+2010 := by
  rcases h with ⟨ht,hm,hs,_⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2151272 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).1
  have entryDelta := (ReflectionE1.gen_counts_delta layout layout_widths cx cy).1
  have baseline := Rolling1588BFFinal.wrapper_toffoli cx cy hc
  have entryWrapperDelta :
      toffoliCount (Edges.wrapper layout (.some hc) cy (ReflectionE1.gen layout cx cy))+759=
        toffoliCount (Edges.wrapper layout (.some hc) cy (Rolling1588BFFinal.gen layout cx cy)) := by
    simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
      (renameProgram_counts _ _).1]
    omega
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1499214 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).2.1
  have old:=ReflectionE1.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50191209+Rolling1588.slotGrowth := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout cx cy)).2.2
  have old:=ReflectionE1.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGap

/-! E1/reflected Q1588 point with the two checked TickGap forward tails. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots







                                                                    
                                                                                       

                                                            
                                                                             
              
           
                
                                                                                      
                                          
                     
                                                                 
                               
                                                                 
                                                                  
                                                                                   
                                                       

                                                                              
              
                                       
                                                    

                                                                                       
              
                                           
                                                         

                                                                    
              
                                                            
                                                           

                                                                     
              
                                       
                     
                                                                         
                                                            

                                                                                                     
              
                          
                                                          

                                                              
                                                                       
                                                         
                                                                 
                         
                                                                    
                                                            
                   
                                                       
                                                
                      
                                                                                     
                                                  


end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- Checked Low48 dependencies follow; the selected reflected prefix retains both checked TickGap tails.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Square

/-! Only the retained E1 square prefix changes. The reflected entry and all maps stay fixed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Low48Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

abbrev K : Nat := ControlLoan1589BFFold.K

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.branchCK L ext control++LowZero18Square.branchBF L ext control++
    LowZero18Square.branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore L)

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    LowZero18Square.raw L ext control=core L ext control++LowZero18Square.reflection L ext := rfl

theorem program_split (L : ControlledPointLayout) :
    LowZero18Square.program L=program L++ReflectionE1Square.reflectedTail L := by
  change SquareCarryLoan719BF.place L (LowZero18Square.raw L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)=
    SquareCarryLoan719BF.place L (core L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)++
    SquareCarryLoan719BF.place L (SquareCarryLoan719BF.reflection
      L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))
  rw [raw_split,ReflectionE1Square.place_append]
  rfl

theorem raw_core_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (core L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (core L ext control) records s).basis=
      SquareReduction.p-1-
        (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
          (if s.basis control then K else 0))%SquareReduction.p) ∧
    ∀q,q∉L.core.out → (run (core L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (LowZero18Square.branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := LowZero18Square.branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc)
      ((hf.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans hs0) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (LowZero18Square.branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := LowZero18Square.branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc)
      ((hf.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans hs0) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA<SquareReduction.p := ofCast_lt _ _
  have reflected : OA=SquareReduction.p-1-
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) := by
    change SquareReduction.p-1-OA=
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) at exactResult
    omega
  exact ⟨phase,value.trans reflected,frame⟩


open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCore_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p) ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; itauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have extOK:=OwnDiagAll12Square.kext_ok L hw hn
  have hext : ECDSAAdd.Entrant.ExtOK K L.core.generic (OwnDiagAll12Square.kext L) :=
    ⟨extOK.nodup,extOK.away,extOK.len⟩
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hext hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  refine ⟨fresh.1,?_,fresh.2.2⟩
  have hK : ((SquareCarryLoan719BF.K:Nat):Fp).val=SquareCarryLoan719BF.K :=
    ZMod.val_natCast_of_lt (by norm_num [SquareCarryLoan719BF.K,ControlLoan1589BFFold.K,p])
  rw [ZMod.val_add,sub_val]
  cases G
  · simpa using fresh.2.1
  · simpa [ZMod.val_mul,hK,K,SquareCarryLoan719BF.K] using fresh.2.1

private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    itauto
  exact List.disjoint_left.mp dis resident hq

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.point.x (run (program L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program L) m s).basis q=s.basis q := by
  have result:=fastCore_boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (fastCore L) m s=out := ⟨_,rfl⟩
  rw [heq] at result
  have clean : regValue L.dialogPool out.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq)),v.clean]
  have eq:=ReflectionE1Square.place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

                                                                                
                                                                           
                                                    
                                                             
                                                  
                                                                    
                      
                                                                                                   




















private theorem window_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18Square.withLowK2 L ext control src dst body)+558+10*(if src.length=128 then 0 else 1)=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (LowZero18Square.withLowK2 L ext control src dst body)+21+3*(if src.length=128 then 0 else 1)=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have a:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  have b:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  constructor <;> omega

private theorem window_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (LowZero18Square.withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_support_subset L hw ext control src dst body h128 h129 hd he

private theorem window_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_slots_le L hw ext control src dst body h128 h129 hd he

private theorem core_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (core L ext control)+3033=toffoliCount (ReflectionE1Square.core L ext control) ∧
    measurementCount (core L ext control)+75=measurementCount (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_counts L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_counts L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_counts L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := ParkCarry8Develop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256) rfl
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedADual_window_rel L hw ext control L.core.low (L.core.product.take 256)
  rw [if_neg (show ¬L.core.sum.length=128 by omega)] at c
  rw [if_pos high] at b
  rw [if_pos low] at a
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,toffoliCount_append,measurementCount_append]
  constructor <;> omega

private theorem core_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (core L ext control)⊆wires (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_support L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_support L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_support L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := ParkCarry8Develop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256) rfl
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedADual_window_rel L hw ext control L.core.low (L.core.product.take 256)
  have k3 := q3.trans k3
  have b := b3.trans (Finset.insert_subset_insert L.core.sumCarry b)
  have a := a3.trans (Finset.insert_subset_insert L.core.sumCarry (Finset.insert_subset_insert ((LowZero18Square.foldPerm L ext) (ControlLoan1589BFFold.eV L)) a))
  have ck:wires (LowZero18Square.branchCK L ext control)⊆wires (SquareCarryLoan719BF.branchCK L ext control) := by
    simp only [LowZero18Square.branchCK,SquareCarryLoan719BF.branchCK,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact k3.trans c | exact Finset.Subset.refl _
  have qmem:L.core.sumCarry∈wires (SquareCarryLoan719BF.branchCK L ext control) := by
    simp only [SquareCarryLoan719BF.branchCK,wires_append]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (ParkCarryDevelop.sumCarry_gPrep L hw))
  have cb:=ParkCarryDevelop.absorb_support L.core.sumCarry _ _ _ _ ck b qmem
  have qab:L.core.sumCarry∈wires (SquareCarryLoan719BF.branchCK L ext control++SquareCarryLoan719BF.branchBF L ext control) := by
    rw [wires_append];exact Finset.mem_union_left _ qmem
  have rab:(LowZero18Square.foldPerm L ext) (ControlLoan1589BFFold.eV L)∈wires
      (SquareCarryLoan719BF.branchCK L ext control++SquareCarryLoan719BF.branchBF L ext control) := by
    rw [wires_append]
    exact Finset.mem_union_right _ (InverseCarryDevelop.old_b_window_eV_mem L hw ext control he)
  have cba:=InverseCarryDevelop.absorb_support_two L.core.sumCarry ((LowZero18Square.foldPerm L ext) (ControlLoan1589BFFold.eV L)) _ _ _ _ cb a qab rab
  simp only [wires_append] at cba
  simp only [core,ReflectionE1Square.core,wires_append]
  exact cba

private theorem core_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (core L ext control)≤Challenge.gateSlots (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_slots L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_slots L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_slots L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := ParkCarry8Develop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256) rfl
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedADual_window_rel L hw ext control L.core.low (L.core.product.take 256)
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,Challenge.gateSlots_append]
  omega

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+3033=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program L)+75=measurementCount (ReflectionE1Square.program L) := by
  have h:=core_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    (ReflectionE1Square.place_counts _ _).1,(ReflectionE1Square.place_counts _ _).2] using h

                                                            
                                                                             
                          
                                        
                       

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (ReflectionE1Square.program L) := by
  unfold program ReflectionE1Square.program SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact core_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (ReflectionE1Square.support L hw hn)

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) :=
  fun used=>ReflectionE1Square.free L hw hn i hi (support_subset L hw used)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have full:=LowZero18Square.physical L hw hn
  rw [program_split,gatePhysical_append] at full
  exact full.1

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (ReflectionE1Square.program L) := by
  have h:=core_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    SquareCarryLoan719BF.place,Baselines.rename_gateSlots] using h

end ECDSAAdd.Entrant.ReflectionE1Low48Square
end -- original module boundary



section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.ParkCarry8Develop
open Arithmetic

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen:300≤ext.length)
    (away:∀q∈ext,q∉L.wires) :
    wires (hostedBody L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
  rw [hosted_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away) (ParkCarry8Develop.fold_fixes_source L hw hn ext hlen away)]
  exact body_support L hw hn c

end ECDSAAdd.Entrant.ParkCarry8Develop
end

section
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic
                                                                                     
                                                                         
                             
                                                                                        
                                                                                        
                                   
end ECDSAAdd.Entrant.InverseCarryDevelop
end

-- ===== R2 (sqep component): square with retired poolWire 760 =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


/-! # Square -/

namespace ECDSAAdd.Entrant.R2SqEp760
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

/-! ## Square: definitions -/

/-- The retired square site: fold-pad bit 239 (= `ktmp[108]`, carry #239 of every reflected core
adder; physically `poolWire 760`). -/
                                                                              
                                                                      
                                                     
                                                                                       
                                   
                                                                                               
                                

def branchCK760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.gPrep L++
    ParkCopyS.withLowK2S L ext control L.core.sum L.core.product
      (bodySwap L ext (OwnDiagAll12Square.bodyCKTq L control))++
    OwnDiagAll12Square.gClear L

def branchBF760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256)
    (bodySwap L ext (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) control))

def branchAF760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  ParkCopy10.withLowK2P10 L ext control L.core.low (L.core.product.take 256)
    (bodySwap L ext (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control)) (ControlLoan1589BFFold.eU L)

def core760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK760 L ext control++branchBF760 L ext control++branchAF760 L ext control

def fastCore760 (L : ControlledPointLayout) : Program :=
  core760 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

/-- The new square: `ReflectionE1Low48Square.program` with the three body swaps. -/
def program760 (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore760 L)





                                                                            
                             
                                                                                       
                                                                                       
                                                                                                 
                                                                                                      

/-! ## Square: positions of the two sites -/

section Sites
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
include hw

theorem foldPad_length : L.foldPad.length=254 := by
  simp [foldPad,hw.core.pad,hw.overflowPad]

omit hw in
theorem sqRet_ktmp : sqRet L=(LowZero18LowK.ktmp L).getD 108 0 := by
  simp only [sqRet,LowZero18LowK.ktmp,List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem sqRet_mem_ktmpTail : sqRet L∈(LowZero18LowK.ktmp L).drop 99 := by
  rw [sqRet_ktmp L]
  have len := LowZero18LowK.ktmp_length L hw
  rw [List.getD_eq_getElem _ _ (by omega)]
  have h : (LowZero18LowK.ktmp L)[108]'(by omega)=((LowZero18LowK.ktmp L).drop 99)[9]'(by simp; omega) := by
    simp
  rw [h]
  exact List.getElem_mem _

theorem sqRet_mem_overflow : sqRet L∈L.overflowPad := by
  have h : sqRet L=L.overflowPad.getD 111 0 := by
    simp only [sqRet,foldPad,List.getD_eq_getElem?_getD,List.getElem?_append_right
      (show L.core.pad.length≤239 by rw [hw.core.pad]; omega),hw.core.pad]
  rw [h,List.getD_eq_getElem _ _ (by rw [hw.overflowPad]; omega)]
  exact List.getElem_mem _

                                               
                                                                   
                                        

end Sites

theorem sqHost_mem (ext : List Wire) (he : 300≤ext.length) : sqHost ext∈ext := by
  rw [sqHost,List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- `sqRet` is outside the core layout (it is an overflow-pad site). -/
theorem sqRet_not_core (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) : sqRet L∉L.core.wires := by
  have overflow := sqRet_mem_overflow L hw
  have dis := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
  exact fun used=>dis (sqRet L) used (sqRet L) overflow rfl

/-! ## Square: support facts -/

section Support
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)

/-- Everything a LowZero leaf kernel names, except the untouched tail of `ktmp`. -/
def kOuter : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++
    (LowZero18LowK.ktmp L).take 99)++ext

include hn hs hd hx hdx in
theorem ktail_away (q : Wire) (hq : q∈(LowZero18LowK.ktmp L).drop 99) :
    q∉kOuter L control ext src dst := by
  apply kdis (LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx) _ q hq
  intro w
  have e := congrArg (List.count w) (List.take_append_drop 99 (LowZero18LowK.ktmp L))
  rw [List.count_append] at e
  simp only [kOuter,LowZero18LowK.kbig2,List.count_append,List.count_cons] at e ⊢
  omega

private theorem mem_tk {l : List Wire} {n : Nat} {q : Wire} (h : q∈l.take n) : q∈l := List.mem_of_mem_take h
private theorem mem_dr {l : List Wire} {n : Nat} {q : Wire} (h : q∈l.drop n) : q∈l := List.mem_of_mem_drop h
private theorem mem_dt {l : List Wire} {a b : Nat} {q : Wire} (h : q∈(l.drop a).take b) : q∈l.take (a+b) := by
  have e : (l.drop a).take b=(l.take (a+b)).drop a := by rw [List.drop_take]; simp
  rw [e] at h
  exact List.mem_of_mem_drop h

private theorem mem_66 {l : List Wire} {q : Wire} (h : q∈l.take 66) : q∈l.take 99 := by
  have e : l.take 66=(l.take 99).take 66 := by rw [List.take_take]; rfl
  rw [e] at h
  exact List.mem_of_mem_take h

/-- Every wire of the leaf kernel's register inventory lies in `kOuter`. -/
theorem kall_outer (q : Wire) (h : q∈(LowZero18LowK.kg L ext src dst).all) :
    q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons]
  unfold LowZero18LowK.kg at h
  split_ifs at h
  all_goals
    simp only [LowZero18LowK.kgH,LowZero18LowK.kgS,KG.all,KG.X,KRegs.all,LowZero18LowK.oregs,
      LowZero18LowK.iregs,LowZero18LowK.jregsH,LowZero18LowK.jregsS,KRegs.lo,KRegs.dlo,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    repeat' (refine Or.elim h (fun h => ?_) (fun h => ?_))
    all_goals first
      | simp [h]
      | simp [mem_tk h]
      | simp [mem_dr h]
      | simp [mem_tk (mem_tk h)]
      | simp [mem_dr (mem_tk h)]
      | simp [mem_tk (mem_dr h)]
      | simp [mem_dr (mem_tk (mem_tk h))]
      | simp [mem_66 (mem_tk h)]
      | simp [mem_66 (mem_tk (mem_tk h))]
      | simp [mem_dt h]

include hw hn hs hd hx hdx in
theorem sqRet_not_outer : sqRet L∉kOuter L control ext src dst :=
  ktail_away L control hn ext src dst hs hd hx hdx _ (sqRet_mem_ktmpTail L hw)

include hw hn hs hd hx hdx in
theorem sqRet_ne_of_outer (q : Wire) (hq : q∈kOuter L control ext src dst) : sqRet L≠q :=
  fun e => sqRet_not_outer L hw control hn ext src dst hs hd hx hdx (e ▸ hq)

theorem ktmp_eq : OwnDiagLowK.ktmp L=LowZero18LowK.ktmp L := rfl

theorem tk99_outer (q : Wire) (h : q∈(LowZero18LowK.ktmp L).take 99) : q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons]; itauto

theorem ext_outer (q : Wire) (h : q∈ext) : q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append]; itauto

theorem cs_outer (q : Wire) (h : q∈control::(src++L.inputBank.take src.length)) :
    q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons] at h ⊢; itauto

include hw in
theorem target_outer : SquareCarryLoan719.target L∈kOuter L control ext src dst := by
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.target L∈(LowZero18LowK.ktmp L).take 99 := by
    change (LowZero18LowK.ktmp L).getD 67 0∈_
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : (LowZero18LowK.ktmp L)[67]'(by omega)=((LowZero18LowK.ktmp L).take 99)[67]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  exact tk99_outer L control ext src dst _ m

include hw in
theorem earlyHost_outer : SquareCarryLoan719.earlyHost L∈kOuter L control ext src dst := by
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.earlyHost L∈(LowZero18LowK.ktmp L).take 99 := by
    change (LowZero18LowK.ktmp L).getD 1 0∈_
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : (LowZero18LowK.ktmp L)[1]'(by omega)=((LowZero18LowK.ktmp L).take 99)[1]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  exact tk99_outer L control ext src dst _ m

include hw hn hs hd hx hdx in
theorem sqRet_masks :
    sqRet L∉wires (copyRegister (some control) src (L.inputBank.take src.length)) ∧
    sqRet L∉wires (eraseMask control src (L.inputBank.take src.length)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  constructor
  · intro used
    have h := List.mem_toFinset.mp (copyRegister_wires_subset (some control) src (L.inputBank.take src.length) used)
    exact ne _ (cs_outer L control ext src dst _ (by simpa only [Option.toList_some,List.singleton_append,
      List.cons_append,List.append_assoc] using h)) rfl
  · intro used
    have h := List.mem_toFinset.mp (eraseMask_wires_subset control src (L.inputBank.take src.length) used)
    exact ne _ (cs_outer L control ext src dst _ h) rfl

include hw hn hs hd hx hdx in
theorem sqRet_cached_mask (hpos : 0<dst.length) :
    sqRet L∉wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst)
      src (L.inputBank.take src.length)) := by
  have masks := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have cacheIn : LowZero18Square.cacheWire L dst∈kOuter L control ext src dst := by
    rw [LowZero18Square.cacheWire_fixed L hw (List.nodup_cons.mp hn).2 dst hd hpos]
    have mem := CachedSquareCopy.head_mem dst hpos
    simp only [kOuter,List.mem_cons,List.mem_append]
    tauto
  intro used
  have h := CachedSquareCopy.wires_subset control (LowZero18Square.cacheWire L dst)
    src (L.inputBank.take src.length) used
  rcases Finset.mem_union.mp h with h|h
  · exact masks.1 h
  · exact ne _ cacheIn (Finset.mem_singleton.mp h)

include hw hn hs hd hx hdx in
theorem sqRet_kernels (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) :
    sqRet L∉wires (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) ∧
    sqRet L∉wires (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have sup := LowZero18LowK.kg_support L hw ext src dst h128 hsmax hlen he
  have offAll : sqRet L∉((LowZero18LowK.kg L ext src dst).all.toFinset) := fun h =>
    ne _ (kall_outer L control ext src dst _ (List.mem_toFinset.mp h)) rfl
  have fix : SquareCarryLoan719.earlyPerm L (sqRet L)=sqRet L := by
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (ne _ (target_outer L hw control ext src dst))
      (ne _ (earlyHost_outer L hw control ext src dst))
  have mk : sqRet L∉wires (LowZero18KG.make (LowZero18LowK.kg L ext src dst)) := fun h => offAll (sup.1 h)
  have cl : sqRet L∉wires (LowZero18KG.clear (LowZero18LowK.kg L ext src dst)) := fun h => offAll (sup.2 h)
  let K := LowZero18LowK.kg L ext src dst
  let T := K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
  let C := K.R.smkT++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c
  have o1 : LowZero18KG.make K=K.Q1++T := by simp only [LowZero18KG.make,T,List.append_assoc]
  have n1 : LowZero18Square.make L K=renameProgram (SquareCarryLoan719.earlyPerm L) K.Q1++T := by
    simp only [LowZero18Square.make,LowZero18KG.make,SquareCarryLoan719.patchKG,T,List.append_assoc]
  have o2 : LowZero18KG.clear K=C++K.Q1c := by simp only [LowZero18KG.clear,C,List.append_assoc]
  have n2 : LowZero18Square.clear L K=C++renameProgram (SquareCarryLoan719.earlyPerm L) K.Q1c := by
    simp only [LowZero18Square.clear,LowZero18KG.clear,SquareCarryLoan719.patchKG,C,List.append_assoc]
  rw [o1,wires_append,Finset.mem_union,not_or] at mk
  rw [o2,wires_append,Finset.mem_union,not_or] at cl
  constructor
  · change sqRet L∉wires (LowZero18Square.make L K)
    rw [n1,wires_append,Finset.mem_union,not_or]
    exact ⟨OwnPlusHost.rename_avoid _ _ _ fix mk.1,mk.2⟩
  · change sqRet L∉wires (LowZero18Square.clear L K)
    rw [n2,wires_append,Finset.mem_union,not_or]
    exact ⟨cl.1,OwnPlusHost.rename_avoid _ _ _ fix cl.2⟩

end Support

section Core
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)

include hw in
theorem g_core_support :
    wires (OwnDiagAll12Square.gPrep L)⊆L.core.wires.toFinset ∧
    wires (OwnDiagAll12Square.gClear L)⊆L.core.wires.toFinset := by
  let M : CuccaroStreamedSquareWideLayout := ⟨L.core,L.core.pad.take 126⟩
  have mhw : M.Widths := ⟨hw.core,by simp [M,hw.core.pad]⟩
  have sub : (L.core.cin::M.wires).toFinset⊆L.core.wires.toFinset := by
    intro q used
    have h := List.mem_toFinset.mp used
    rcases List.mem_cons.mp h with h|h
    · subst q
      simp [CuccaroStreamedSquareLayout.wires]
    · change q∈L.core.wires++L.core.pad.take 126 at h
      rcases List.mem_append.mp h with h|h
      · exact List.mem_toFinset.mpr h
      · have hp := List.mem_of_mem_take h
        simp [CuccaroStreamedSquareLayout.wires,hp]
  have support := OwnDiagAll12Square.gSum_support M mhw L.core.cin
  exact ⟨support.1.trans sub,support.2.trans sub⟩

end Core

section Free
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hext in
theorem sqHost_in : sqHost ext∈ext := sqHost_mem ext hext

include hw hdx hext in
theorem sqHost_ne_target : sqHost ext≠SquareCarryLoan719.target L := by
  intro e
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.target L∈LowZero18LowK.ktmp L := by
    change (LowZero18LowK.ktmp L).getD 67 0∈_
    exact DiagSq.getD_in _ 67 (by omega)
  have w : SquareCarryLoan719.target L∈control::L.wires :=
    List.mem_cons_of_mem _ (LowZero18LowK.ktmp_wires L _ m)
  exact hdx _ (sqHost_in ext hext) (e ▸ w)

include hx hext in
theorem sqHost_ne_ext0 : sqHost ext≠ext.getD 0 0 := by
  intro e
  rw [sqHost,List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  omega

include hw hx hdx hext in
theorem sqHost_fold_free (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqHost ext∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  apply OwnPlusHost.rename_avoid _ _ _
    (Equiv.swap_apply_of_ne_of_ne (sqHost_ne_target L hw control ext hdx hext) (sqHost_ne_ext0 ext hx hext))
  exact fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used))

include hw hn hx hdx hext in
theorem sqRet_body_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  apply OwnPlusHost.rename_avoid _ _ _
    (Equiv.swap_apply_of_ne_of_ne (ne _ (target_outer L hw control ext src dst))
      (ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))))
  exact swap_free _ _ _ (fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used)))

include hw hn hx hdx hext in
theorem withLowK2_760_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)) := by
  have m := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have k := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen hext
  have cached := sqRet_cached_mask L hw control hn ext src dst hs hd hx hdx (by omega)
  have f := sqRet_body_free L hw control hn ext hx hdx hext src dst hs hd B hb
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨m.1,k.1⟩,m.2⟩,f⟩,cached⟩,k.2⟩,m.2⟩

end Free

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Bank-bit parking inside the 760 square

The 128-bit leaves `branchBF760`/`branchAF760` use `ParkCopy.withLowK2P`: the last five bank bits ride
on the `ext` wires 129 (top bit of the outer `T`), 131, 231, 298, 299 through the body, so the second controlled copy needs four
Toffoli gates fewer per leaf. The facts below relate it to `LowZero18Square.withLowK2`. -/

theorem park_instr_wires_sub (i : Instr) : ∀ q : Program, i∈q → i.wires⊆wires q
  | [], h => by simp at h
  | j::q, h => by
    intro x hx
    with_unfolding_all change x∈j.wires ∪ wires q
    rcases List.mem_cons.mp h with e|e
    · subst e; exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (park_instr_wires_sub i q e hx)

theorem park_wires_sub_of_mem : ∀ (p q : Program), (∀ i∈p, i∈q) → wires p⊆wires q
  | [], _, _ => by intro x hx; simp [wires] at hx
  | i::p, q, h => by
    intro x hx
    with_unfolding_all change x∈i.wires ∪ wires p at hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact park_instr_wires_sub i q (h i (by simp)) hx
    · exact park_wires_sub_of_mem p q (fun j hj => h j (List.mem_cons_of_mem _ hj)) hx

theorem park_dst_mem_eraseMask (c : Wire) : ∀ (src dst : List Wire), src.length=dst.length →
    ∀ q∈dst, q∈wires (eraseMask c src dst)
  | [], [], _, q, h => by simp at h
  | [], _::_, h, _, _ => by simp at h
  | _::_, [], h, _, _ => by simp at h
  | a::src, b::dst, h, q, hq => by
    with_unfolding_all change q∈(Instr.measureX b [] [.CZ c a]).wires ∪ wires (eraseMask c src dst)
    rcases List.mem_cons.mp hq with e|e
    · subst e; apply Finset.mem_union_left; simp [Instr.wires]
    · exact Finset.mem_union_right _ (park_dst_mem_eraseMask c src dst (by simpa using h) q e)

theorem park_cached_mem (c w : Wire) (k : Nat) : ∀ (src dst : List Wire), src.length=dst.length →
    ∀ i∈CachedSquareCopy.copy c w (src.take (k+1)) (dst.take (k+1)), i∈CachedSquareCopy.copy c w src dst
  | [], _, _, i, h => by simp [CachedSquareCopy.copy,copyRegister] at h
  | _::_, [], h, _, _ => by simp at h
  | x::src, b::dst, h, i, hi => by
    have hl : src.length=dst.length := by simpa using h
    simp only [List.take_succ_cons,CachedSquareCopy.copy,List.mem_append] at hi ⊢
    rw [ParkCopy.copyRegister_split (some c) k src dst hl,List.mem_append]
    itauto

theorem park_erase_mem (c : Wire) (k : Nat) (src dst : List Wire) (h : src.length=dst.length) :
    ∀ i∈eraseMask c (src.take k) (dst.take k), i∈eraseMask c src dst := by
  intro i hi
  rw [ParkCopy.eraseMask_split c k src dst h,List.mem_append]
  exact Or.inl hi

theorem park_move_wires (a b : List Wire) : wires (ParkCopy.move a b)⊆(a++b).toFinset := by
  intro q hq
  simp only [ParkCopy.move,wires_append,Finset.mem_union] at hq
  simp only [List.mem_toFinset,List.mem_append]
  rcases hq with h|h
  · have := List.mem_toFinset.mp (copyRegister_wires_subset none a b h)
    simp only [Option.toList_none,List.nil_append,List.mem_append] at this
    exact this
  · have := List.mem_toFinset.mp (copyRegister_wires_subset none b a h)
    simp only [Option.toList_none,List.nil_append,List.mem_append] at this
    itauto

theorem park_dummies_wires : ∀ hs : List Wire, wires (ParkCopy.dummies hs)⊆hs.toFinset
  | [] => by intro x hx; simp [ParkCopy.dummies,wires] at hx
  | a::hs => by
    intro q hq
    with_unfolding_all change q∈(Instr.measureX a [] []).wires ∪ wires (ParkCopy.dummies hs) at hq
    rcases Finset.mem_union.mp hq with h|h
    · simp [Instr.wires,correctionWires] at h; simp [h]
    · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (park_dummies_wires hs h)))

theorem park_dummies_physical : ∀ hs : List Wire, GatePhysical (ParkCopy.dummies hs)
  | [] => by intro i hi; simp [ParkCopy.dummies] at hi
  | a::hs => by
    intro i hi
    rcases List.mem_cons.mp hi with e|e
    · subst e; trivial
    · exact park_dummies_physical hs i e

theorem park_dummies_slots : ∀ hs : List Wire, Challenge.gateSlots (ParkCopy.dummies hs)=hs.length
  | [] => rfl
  | a::hs => by
    change Challenge.gateSlots ([Instr.measureX a [] []]++ParkCopy.dummies hs)=_
    have s0 : Challenge.gateSlots [Instr.measureX a [] []]=1 := rfl
    rw [Challenge.gateSlots_append,park_dummies_slots hs,s0,List.length_cons]
    omega

theorem park_move_counts (a b : List Wire) (h : a.length=b.length) :
    toffoliCount (ParkCopy.move a b)=0 ∧ measurementCount (ParkCopy.move a b)=0 ∧
      Challenge.gateSlots (ParkCopy.move a b)=2*a.length := by
  have c1 := copyRegister_counts none a b h
  have c2 := copyRegister_counts none b a h.symm
  simp only [ParkCopy.move,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    Baselines.copyRegister_gateSlots,c1.1,c1.2,c2.1,c2.2,h]
  refine ⟨?_,?_,?_⟩
  all_goals (try simp)
  all_goals omega

theorem park_cached_counts (c w : Wire) : ∀ (src dst : List Wire), src.length=dst.length → 0<src.length →
    toffoliCount (CachedSquareCopy.copy c w src dst)+1=src.length ∧
    measurementCount (CachedSquareCopy.copy c w src dst)=0 ∧
    Challenge.gateSlots (CachedSquareCopy.copy c w src dst)=src.length
  | [], _, _, h => by simp at h
  | _::_, [], h, _ => by simp at h
  | x::src, b::dst, h, _ => by
    have hl : src.length=dst.length := by simpa using h
    have cc := copyRegister_counts (some c) src dst hl
    have e : CachedSquareCopy.copy c w (x::src) (b::dst)=[Instr.CX w b]++copyRegister (some c) src dst := rfl
    have t0 : toffoliCount [Instr.CX w b]=0 := rfl
    have m0 : measurementCount [Instr.CX w b]=0 := rfl
    have s0 : Challenge.gateSlots [Instr.CX w b]=1 := rfl
    rw [e,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,Baselines.copyRegister_gateSlots,
      cc.1,cc.2,t0,m0,s0]
    refine ⟨?_,?_,?_⟩
    all_goals (try simp [hl])
    all_goals omega

theorem park_cached_physical (c w : Wire) (src dst : List Wire) (hd : 0<dst.length)
    (hold : GatePhysical (CachedSquareCopy.copy c w src dst)) (k : Nat) (h : src.length=dst.length) :
    GatePhysical (CachedSquareCopy.copy c w (src.take (k+1)) (dst.take (k+1))) :=
  fun i hi => hold i (park_cached_mem c w k src dst h i hi)

section Park
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hx hext in
theorem sqHost_not_hosts : sqHost ext∉ParkCopy.hosts ext := by
  intro h
  simp only [ParkCopy.hosts,ParkCopy.hostIdx,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
    or_false] at h
  rcases h with e|e|e|e|e|e|e|e|e <;>
    (rw [sqHost,List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)] at e
     have := (List.Nodup.getElem_inj_iff hx).mp e
     omega)

include hw hn hx hdx hext in
/-- `sqRet` is outside every parking piece; `sqHost` is outside the pieces before the body. -/
theorem park_pieces_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hlen : dst.length=2*src.length) :
    sqRet L∉wires (ParkCopy.pE1 L control src) ∧ sqRet L∉wires (ParkCopy.pD ext) ∧
    sqRet L∉wires (ParkCopy.pMI L ext src) ∧ sqRet L∉wires (ParkCopy.pC1 L ext control src dst) ∧
    sqRet L∉wires (ParkCopy.pMO L ext src) ∧
    sqHost ext∉wires (ParkCopy.pE1 L control src) ∧ sqHost ext∉wires (ParkCopy.pD ext) ∧
    sqHost ext∉wires (ParkCopy.pMI L ext src) ∧
    sqHost ext∉wires (eraseMask control src (L.inputBank.take src.length)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hostE := sqHost_in ext hext
  have hostH := sqHost_not_hosts ext hx hext
  have hostsE : ∀q∈ParkCopy.hosts ext,q∈ext := ParkCopy.hosts_sub ext hext
  have outerCS : ∀q∈control::(src++L.inputBank.take src.length),sqRet L≠q :=
    fun q h => ne _ (cs_outer L control ext src dst _ h)
  have outerE : ∀q∈ext,sqRet L≠q := fun q h => ne _ (ext_outer L control ext src dst _ h)
  have take_cs : ∀q∈control::(src.take 119++(L.inputBank.take src.length).take 119),
      q∈control::(src++L.inputBank.take src.length) := by
    intro q h
    simp only [List.mem_cons,List.mem_append] at h ⊢
    rcases h with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl (List.mem_of_mem_take h))
    · exact Or.inr (Or.inr (List.mem_of_mem_take h))
  have hostCS : ∀q∈control::(src++L.inputBank.take src.length),sqHost ext≠q := by
    intro q h e
    subst e
    rcases List.mem_cons.mp h with h|h
    · exact hdx _ hostE (by simp [h])
    · rcases List.mem_append.mp h with h|h
      · exact extSrc _ hostE h
      · exact extB _ hostE h
  have moveFree : ∀ a b : List Wire, (∀q∈a,q∈(L.inputBank.take src.length) ∨ q∈ext) →
      (∀q∈b,q∈(L.inputBank.take src.length) ∨ q∈ext) → sqRet L∉wires (ParkCopy.move a b) := by
    intro a b ha hb' used
    have h := List.mem_toFinset.mp (park_move_wires a b used)
    rcases List.mem_append.mp h with h|h
    · rcases ha _ h with h'|h'
      · exact outerCS _ (List.mem_cons_of_mem _ (List.mem_append_right _ h')) rfl
      · exact outerE _ h' rfl
    · rcases hb' _ h with h'|h'
      · exact outerCS _ (List.mem_cons_of_mem _ (List.mem_append_right _ h')) rfl
      · exact outerE _ h' rfl
  have dropB : ∀q∈(L.inputBank.take src.length).drop 119,q∈(L.inputBank.take src.length) ∨ q∈ext :=
    fun q h => Or.inl (List.mem_of_mem_drop h)
  have hostsBE : ∀q∈ParkCopy.hosts ext,q∈(L.inputBank.take src.length) ∨ q∈ext := fun q h => Or.inr (hostsE q h)
  have cacheIn : LowZero18Square.cacheWire L dst∈kOuter L control ext src dst := by
    rw [LowZero18Square.cacheWire_fixed L hw (List.nodup_cons.mp hn).2 dst hd (by omega)]
    have mem := CachedSquareCopy.head_mem dst (by omega)
    simp only [kOuter,List.mem_cons,List.mem_append]
    itauto
  refine ⟨?_,?_,moveFree _ _ dropB hostsBE,?_,moveFree _ _ hostsBE dropB,?_,?_,?_,?_⟩
  · exact fun used => outerCS _ (take_cs _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used))) rfl
  · exact fun used => outerE _ (hostsE _ (List.mem_toFinset.mp (park_dummies_wires _ used))) rfl
  · intro used
    have bl : 119≤(L.inputBank.take src.length).length := by
      simp only [List.length_take,(L.measured_bank_widths hw).1];omega
    have sub:=InnerLinearCopy.copy_wires control (LowZero18Square.cacheWire L dst)
      (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)
      (src.take 119) ((L.inputBank.take src.length).take 119)
      (by simp only [List.length_take];omega) (by rw [List.length_take];exact Nat.min_eq_left bl) used
    rcases Finset.mem_union.mp sub with used|r
    · rcases Finset.mem_union.mp (CachedSquareCopy.wires_subset _ _ _ _ used) with h|h
      · have h' := List.mem_toFinset.mp (copyRegister_wires_subset _ _ _ h)
        exact outerCS _ (take_cs _ (by simpa only [Option.toList_some,List.singleton_append,
          List.cons_append,List.append_assoc] using h')) rfl
      · exact ne _ cacheIn (Finset.mem_singleton.mp h)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at r
      rcases r with e|e|e <;> exact outerE _ (e ▸ DiagSq.getD_in ext _ (by omega)) rfl
  · exact fun used => hostCS _ (take_cs _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used))) rfl
  · exact fun used => hostH (List.mem_toFinset.mp (park_dummies_wires _ used))
  · intro used
    rcases List.mem_append.mp (List.mem_toFinset.mp (park_move_wires _ _ used)) with h|h
    · exact extB _ hostE (List.mem_of_mem_drop h)
    · exact hostH h
  · exact fun used => hostCS _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used)) rfl

include hx hext in
theorem sqHost_not_hostsS : sqHost ext∉ParkCopyS.hostsS ext := by
  intro h
  simp only [ParkCopyS.hostsS,ParkCopyS.hostIdxS,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
    or_false] at h
  rcases h with e|e|e|e|e <;>
    (rw [sqHost,List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)] at e
     have := (List.Nodup.getElem_inj_iff hx).mp e
     omega)

include hw hn hx hdx hext in
/-- `sqRet` is outside every parking piece; `sqHost` is outside the pieces before the body. -/
theorem park_pieces_freeS (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hlen : dst.length=2*src.length) :
    sqRet L∉wires (ParkCopyS.pE1 L control src) ∧ sqRet L∉wires (ParkCopyS.pD ext) ∧
    sqRet L∉wires (ParkCopyS.pMI L ext src) ∧ sqRet L∉wires (ParkCopyS.pC1 L control src dst) ∧
    sqRet L∉wires (ParkCopyS.pMO L ext src) ∧
    sqHost ext∉wires (ParkCopyS.pE1 L control src) ∧ sqHost ext∉wires (ParkCopyS.pD ext) ∧
    sqHost ext∉wires (ParkCopyS.pMI L ext src) ∧
    sqHost ext∉wires (eraseMask control src (L.inputBank.take src.length)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hostE := sqHost_in ext hext
  have hostH := sqHost_not_hostsS ext hx hext
  have hostsE : ∀q∈ParkCopyS.hostsS ext,q∈ext := ParkCopyS.hostsS_sub ext hext
  have outerCS : ∀q∈control::(src++L.inputBank.take src.length),sqRet L≠q :=
    fun q h => ne _ (cs_outer L control ext src dst _ h)
  have outerE : ∀q∈ext,sqRet L≠q := fun q h => ne _ (ext_outer L control ext src dst _ h)
  have take_cs : ∀q∈control::(src.take 124++(L.inputBank.take src.length).take 124),
      q∈control::(src++L.inputBank.take src.length) := by
    intro q h
    simp only [List.mem_cons,List.mem_append] at h ⊢
    rcases h with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl (List.mem_of_mem_take h))
    · exact Or.inr (Or.inr (List.mem_of_mem_take h))
  have hostCS : ∀q∈control::(src++L.inputBank.take src.length),sqHost ext≠q := by
    intro q h e
    subst e
    rcases List.mem_cons.mp h with h|h
    · exact hdx _ hostE (by simp [h])
    · rcases List.mem_append.mp h with h|h
      · exact extSrc _ hostE h
      · exact extB _ hostE h
  have moveFree : ∀ a b : List Wire, (∀q∈a,q∈(L.inputBank.take src.length) ∨ q∈ext) →
      (∀q∈b,q∈(L.inputBank.take src.length) ∨ q∈ext) → sqRet L∉wires (ParkCopy.move a b) := by
    intro a b ha hb' used
    have h := List.mem_toFinset.mp (park_move_wires a b used)
    rcases List.mem_append.mp h with h|h
    · rcases ha _ h with h'|h'
      · exact outerCS _ (List.mem_cons_of_mem _ (List.mem_append_right _ h')) rfl
      · exact outerE _ h' rfl
    · rcases hb' _ h with h'|h'
      · exact outerCS _ (List.mem_cons_of_mem _ (List.mem_append_right _ h')) rfl
      · exact outerE _ h' rfl
  have dropB : ∀q∈(L.inputBank.take src.length).drop 124,q∈(L.inputBank.take src.length) ∨ q∈ext :=
    fun q h => Or.inl (List.mem_of_mem_drop h)
  have hostsBE : ∀q∈ParkCopyS.hostsS ext,q∈(L.inputBank.take src.length) ∨ q∈ext := fun q h => Or.inr (hostsE q h)
  have cacheIn : LowZero18Square.cacheWire L dst∈kOuter L control ext src dst := by
    rw [LowZero18Square.cacheWire_fixed L hw (List.nodup_cons.mp hn).2 dst hd (by omega)]
    have mem := CachedSquareCopy.head_mem dst (by omega)
    simp only [kOuter,List.mem_cons,List.mem_append]
    itauto
  refine ⟨?_,?_,moveFree _ _ dropB hostsBE,?_,moveFree _ _ hostsBE dropB,?_,?_,?_,?_⟩
  · exact fun used => outerCS _ (take_cs _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used))) rfl
  · exact fun used => outerE _ (hostsE _ (List.mem_toFinset.mp (park_dummies_wires _ used))) rfl
  · intro used
    rcases Finset.mem_union.mp (CachedSquareCopy.wires_subset _ _ _ _ used) with h|h
    · have h' := List.mem_toFinset.mp (copyRegister_wires_subset _ _ _ h)
      exact outerCS _ (take_cs _ (by simpa only [Option.toList_some,List.singleton_append,
        List.cons_append,List.append_assoc] using h')) rfl
    · exact ne _ cacheIn (Finset.mem_singleton.mp h)
  · exact fun used => hostCS _ (take_cs _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used))) rfl
  · exact fun used => hostH (List.mem_toFinset.mp (park_dummies_wires _ used))
  · intro used
    rcases List.mem_append.mp (List.mem_toFinset.mp (park_move_wires _ _ used)) with h|h
    · exact extB _ hostE (List.mem_of_mem_drop h)
    · exact hostH h
  · exact fun used => hostCS _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used)) rfl

end Park

/-- Two runs with the same phase, output value and frame are the same state. -/
theorem park_state_eq (L : CuccaroStreamedSquareWideLayout) (a b s : State)
    (pa : a.phase=s.phase) (pb : b.phase=s.phase)
    (va : regValue L.core.out a.basis=regValue L.core.out b.basis)
    (fa : ∀q,q∉L.core.out → a.basis q=s.basis q) (fb : ∀q,q∉L.core.out → b.basis q=s.basis q) : a=b := by
  have hb : a.basis=b.basis := by
    funext q
    by_cases hq : q∈L.core.out
    · exact (regValue_eq_iff _ _ _).mp va q hq
    · rw [fa q hq,fb q hq]
  cases a with
  | mk pa0 ba0 =>
    cases b with
    | mk pb0 bb0 =>
      simp only at pa pb hb
      rw [pa,pb,hb]

theorem withLowK2P_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (B : Program) (h128 : src.length=128) :
    toffoliCount (ParkCopy.withLowK2P L ext control src dst B)+11=
      toffoliCount (LowZero18Square.withLowK2 L ext control src dst B) ∧
    measurementCount (ParkCopy.withLowK2P L ext control src dst B)=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) ∧
    Challenge.gateSlots (ParkCopy.withLowK2P L ext control src dst B)=
      Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst B)+21 := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have l1 : (src.take 119).length=((L.inputBank.take src.length).take 119).length := by
    simp only [List.length_take,bl]
  have l1' : (src.take 119).length=119 := by simp [h128]
  have ld : ((L.inputBank.take src.length).drop 119).length=9 := by rw [List.length_drop,bl,h128]
  have hl := ParkCopy.hosts_length ext
  have ef := eraseMask_counts control src (L.inputBank.take src.length) bl.symm
  have e1 := eraseMask_counts control (src.take 119) ((L.inputBank.take src.length).take 119) l1
  have esf := UncompSwap.eraseMask_slots control src (L.inputBank.take src.length) bl.symm
  have es1 := UncompSwap.eraseMask_slots control (src.take 119) ((L.inputBank.take src.length).take 119) l1
  have dc := ParkCopy.dummies_counts (ParkCopy.hosts ext)
  have ds := park_dummies_slots (ParkCopy.hosts ext)
  have mi := park_move_counts ((L.inputBank.take src.length).drop 119) (ParkCopy.hosts ext) (by rw [ld,hl])
  have mo := park_move_counts (ParkCopy.hosts ext) ((L.inputBank.take src.length).drop 119) (by rw [ld,hl])
  have cf := park_cached_counts control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)
    bl.symm (by omega)
  have c1 := park_cached_counts control (LowZero18Square.cacheWire L dst) (src.take 119)
    ((L.inputBank.take src.length).take 119) l1 (by omega)
  have lin:=InnerLinearCopy.copy_counts control (LowZero18Square.cacheWire L dst)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 119)
    ((L.inputBank.take src.length).take 119) l1' (by omega)
  have sl:=InnerLinearCopy.copy_slots control (LowZero18Square.cacheWire L dst)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 119)
    ((L.inputBank.take src.length).take 119) l1' (by omega)
  simp only [ParkCopy.withLowK2P,ParkCopy.pA,ParkCopy.pM,ParkCopy.pE1,ParkCopy.pD,ParkCopy.pMI,ParkCopy.pB,
    ParkCopy.pC1,ParkCopy.pMO,ParkCopy.pCL,ParkCopy.pE,LowZero18Square.foldPerm,
    LowZero18Square.withLowK2,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  simp only [l1',hl,bl,ld,h128] at *
  omega

theorem withLowK2_swap_counts (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (B : Program) :
    toffoliCount (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))=
      toffoliCount (LowZero18Square.withLowK2 L ext control src dst B) ∧
    measurementCount (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) ∧
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))=
      Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst B) := by
  simp only [LowZero18Square.withLowK2,bodySwap,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    Baselines.rename_gateSlots,and_self]

theorem withLowK2P_swap_mc (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (B : Program) (h128 : src.length=128) :
    measurementCount (ParkCopy.withLowK2P L ext control src dst (bodySwap L ext B))=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) :=
  (withLowK2P_counts L hw ext control src dst _ h128).2.1.trans
    (withLowK2_swap_counts L ext control src dst B).2.1

theorem withLowK2P_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : src.length=128) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (hold : GatePhysical (LowZero18Square.withLowK2 L ext control src dst B)) :
    GatePhysical (ParkCopy.withLowK2P L ext control src dst B) := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have hostsE : ∀q∈ParkCopy.hosts ext,q∈ext := ParkCopy.hosts_sub ext he
  have hHnd : (ParkCopy.hosts ext).Nodup := ParkCopy.hosts_nodup ext hx he
  have ndMI : ((L.inputBank.take src.length).drop 119++ParkCopy.hosts ext).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => extB b (hostsE b hb) (e ▸ List.mem_of_mem_drop ha)⟩
  have ndMO : (ParkCopy.hosts ext++(L.inputBank.take src.length).drop 119).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  simp only [LowZero18Square.withLowK2,gatePhysical_append] at hold
  obtain ⟨⟨⟨⟨⟨⟨pA,pM⟩,pE⟩,pB⟩,pC⟩,pCL⟩,_⟩ := hold
  have pC1 := park_cached_physical control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)
    (by omega) pC 118 bl.symm
  have rs (i : Nat)(hi : i<ext.length) : ext.getD i 0∉((L.inputBank.take src.length).take 119) :=
    fun h => extB _ (DiagSq.getD_in ext i hi) (List.mem_of_mem_take h)
  have pLin:=InnerLinearCopy.copy_physical control (LowZero18Square.cacheWire L dst)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 119)
    ((L.inputBank.take src.length).take 119)
    (by simp [h128]) (by rw [List.length_take,bl,h128];decide) (bNd.sublist (List.take_sublist _ _))
    (rs 198 (by omega)) (rs 199 (by omega)) (rs 233 (by omega)) pC1
  simp only [ParkCopy.withLowK2P,ParkCopy.pA,ParkCopy.pM,ParkCopy.pE1,ParkCopy.pD,ParkCopy.pMI,ParkCopy.pB,
    ParkCopy.pC1,ParkCopy.pMO,ParkCopy.pCL,ParkCopy.pE,LowZero18Square.foldPerm,ParkCopy.move,
    gatePhysical_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨pA,pM⟩,eraseMask_physical _ _ _⟩,park_dummies_physical _⟩,
    ⟨copyRegister_physical none _ _ ndMI (by simp),copyRegister_physical none _ _ ndMO (by simp)⟩⟩,pB⟩,
    pLin⟩,⟨copyRegister_physical none _ _ ndMO (by simp),copyRegister_physical none _ _ ndMI (by simp)⟩⟩,pCL⟩,pE⟩

/-- Parking adds only the five host wires to the leaf's support. -/
theorem withLowK2P_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (B : Program) (h128 : src.length=128) :
    wires (ParkCopy.withLowK2P L ext control src dst B)⊆
      wires (LowZero18Square.withLowK2 L ext control src dst B) ∪ (ParkCopy.supportHosts ext).toFinset := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have eSub : wires (eraseMask control (src.take 119) ((L.inputBank.take src.length).take 119))⊆
      wires (eraseMask control src (L.inputBank.take src.length)) :=
    park_wires_sub_of_mem _ _ (park_erase_mem control 119 src _ bl.symm)
  have cSub : wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) (src.take 119)
      ((L.inputBank.take src.length).take 119))⊆
      wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)) :=
    park_wires_sub_of_mem _ _ (park_cached_mem control _ 118 src _ bl.symm)
  have parkMem : ∀q∈ParkCopy.hosts ext,q∈ParkCopy.supportHosts ext := by
    intro q h;exact List.mem_append_left _ h
  have lin:=InnerLinearCopy.copy_wires control (LowZero18Square.cacheWire L dst)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 119)
    ((L.inputBank.take src.length).take 119) (by simp [h128]) (by rw [List.length_take,bl,h128];decide)
  have linSub : wires (InnerLinearCopy.copy control (LowZero18Square.cacheWire L dst)
      (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 119)
      ((L.inputBank.take src.length).take 119))⊆
      wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)) ∪
      (ParkCopy.supportHosts ext).toFinset := by
    intro q h
    rcases Finset.mem_union.mp (lin h) with h|h
    · exact Finset.mem_union_left _ (cSub h)
    · apply Finset.mem_union_right
      simpa only [ParkCopy.supportHosts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] using
        Or.inr (by simpa only [Finset.mem_insert,Finset.mem_singleton] using h)
  have bankIn : ∀q∈(L.inputBank.take src.length).drop 119,q∈wires (eraseMask control src (L.inputBank.take src.length)) :=
    fun q h => park_dst_mem_eraseMask control src _ bl.symm q (List.mem_of_mem_drop h)
  have mSub : ∀ a b : List Wire, (∀q∈a,q∈(L.inputBank.take src.length).drop 119 ∨ q∈ParkCopy.hosts ext) →
      (∀q∈b,q∈(L.inputBank.take src.length).drop 119 ∨ q∈ParkCopy.hosts ext) →
      wires (ParkCopy.move a b)⊆wires (eraseMask control src (L.inputBank.take src.length)) ∪ (ParkCopy.supportHosts ext).toFinset := by
    intro a b ha hb' q hq
    rcases List.mem_append.mp (List.mem_toFinset.mp (park_move_wires a b hq)) with h|h
    · rcases ha q h with h'|h'
      · exact Finset.mem_union_left _ (bankIn q h')
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (parkMem q h'))
    · rcases hb' q h with h'|h'
      · exact Finset.mem_union_left _ (bankIn q h')
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (parkMem q h'))
  have mI := mSub ((L.inputBank.take src.length).drop 119) (ParkCopy.hosts ext) (fun q h => Or.inl h) (fun q h => Or.inr h)
  have mO := mSub (ParkCopy.hosts ext) ((L.inputBank.take src.length).drop 119) (fun q h => Or.inr h) (fun q h => Or.inl h)
  have dS : wires (ParkCopy.dummies (ParkCopy.hosts ext))⊆(ParkCopy.supportHosts ext).toFinset := by
    intro q h;exact List.mem_toFinset.mpr (parkMem q (List.mem_toFinset.mp (park_dummies_wires _ h)))
  intro q hq
  simp only [ParkCopy.withLowK2P,ParkCopy.pA,ParkCopy.pM,ParkCopy.pE1,ParkCopy.pD,ParkCopy.pMI,ParkCopy.pB,
    ParkCopy.pC1,ParkCopy.pMO,ParkCopy.pCL,ParkCopy.pE,LowZero18Square.foldPerm,
    wires_append,Finset.mem_union] at hq
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union]
  rcases hq with (((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h)
  · simp only [h,true_or,or_true]
  · simp only [h,true_or,or_true]
  · simp only [eSub h,true_or,or_true]
  · simp only [List.mem_toFinset.mp (dS h),List.mem_toFinset,true_or,or_true]
  · rcases Finset.mem_union.mp (mI h) with h'|h'
    · simp only [h',true_or,or_true]
    · simp only [h',true_or,or_true]
  · simp only [h,true_or,or_true]
  · rcases Finset.mem_union.mp (linSub h) with h'|h' <;> simp only [h',true_or,or_true]
  · rcases Finset.mem_union.mp (mO h) with h'|h'
    · simp only [h',true_or,or_true]
    · simp only [h',true_or,or_true]
  · simp only [h,true_or,or_true]
  · simp only [h,true_or,or_true]

open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout ParkCopy
theorem withLowK2P10_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (B : Program) (g : Wire) (h128 : src.length=128) :
    toffoliCount (ParkCopy10.withLowK2P10 L ext control src dst B g)+12=
      toffoliCount (LowZero18Square.withLowK2 L ext control src dst B) ∧
    measurementCount (ParkCopy10.withLowK2P10 L ext control src dst B g)=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) ∧
    Challenge.gateSlots (ParkCopy10.withLowK2P10 L ext control src dst B g)=
      Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst B)+23 := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have l1 : (src.take 118).length=((L.inputBank.take src.length).take 118).length := by
    simp only [List.length_take,bl]
  have l1' : (src.take 118).length=118 := by simp [h128]
  have ld : ((L.inputBank.take src.length).drop 118).length=10 := by rw [List.length_drop,bl,h128]
  have hl := ParkCopy10.hosts10_length ext g
  have ef := eraseMask_counts control src (L.inputBank.take src.length) bl.symm
  have e1 := eraseMask_counts control (src.take 118) ((L.inputBank.take src.length).take 118) l1
  have esf := UncompSwap.eraseMask_slots control src (L.inputBank.take src.length) bl.symm
  have es1 := UncompSwap.eraseMask_slots control (src.take 118) ((L.inputBank.take src.length).take 118) l1
  have dc := ParkCopy.dummies_counts (ParkCopy10.hosts10 ext g)
  have ds := park_dummies_slots (ParkCopy10.hosts10 ext g)
  have mi := park_move_counts ((L.inputBank.take src.length).drop 118) (ParkCopy10.hosts10 ext g) (by rw [ld,hl])
  have mo := park_move_counts (ParkCopy10.hosts10 ext g) ((L.inputBank.take src.length).drop 118) (by rw [ld,hl])
  have cf := park_cached_counts control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)
    bl.symm (by omega)
  have c1 := park_cached_counts control (LowZero18Square.cacheWire L dst) (src.take 118)
    ((L.inputBank.take src.length).take 118) l1 (by omega)
  have lin:=InnerLinearCopy.copy_counts118 control (LowZero18Square.cacheWire L dst)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 118)
    ((L.inputBank.take src.length).take 118) l1' (by omega)
  have sl:=InnerLinearCopy.copy_slots118 control (LowZero18Square.cacheWire L dst)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 118)
    ((L.inputBank.take src.length).take 118) l1' (by omega)
  simp only [ParkCopy10.withLowK2P10,ParkCopy10.pA,ParkCopy10.pM,ParkCopy10.pE1,ParkCopy10.pD,ParkCopy10.pMI,ParkCopy10.pB,
    ParkCopy10.pC1,ParkCopy10.pMO,ParkCopy10.pCL,ParkCopy10.pE,LowZero18Square.foldPerm,
    LowZero18Square.withLowK2,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  simp only [l1',hl,bl,ld,h128] at *
  omega

theorem withLowK2P10_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : src.length=128) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (g : Wire) (hgE : g∉ext) (hgB : g∉L.inputBank.take src.length)
    (hold : GatePhysical (LowZero18Square.withLowK2 L ext control src dst B)) :
    GatePhysical (ParkCopy10.withLowK2P10 L ext control src dst B g) := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have hostsE : ∀q∈ParkCopy10.hosts10 ext g,q∈ext ∨ q=g := fun q h =>
    (List.mem_append.mp h).imp (ParkCopy.hosts_sub ext he q) List.mem_singleton.mp
  have hHnd : (ParkCopy10.hosts10 ext g).Nodup := List.nodup_append.mpr ⟨ParkCopy.hosts_nodup ext hx he,
    List.nodup_singleton g,fun a ha b hb e => hgE (by rw [List.mem_singleton.mp hb] at e; exact e ▸ ParkCopy.hosts_sub ext he a ha)⟩
  have ndMI : ((L.inputBank.take src.length).drop 118++ParkCopy10.hosts10 ext g).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => (hostsE b hb).elim (fun h => extB b h (e ▸ List.mem_of_mem_drop ha))
        (fun e2 => hgB (e2 ▸ e ▸ List.mem_of_mem_drop ha))⟩
  have ndMO : (ParkCopy10.hosts10 ext g++(L.inputBank.take src.length).drop 118).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  simp only [LowZero18Square.withLowK2,gatePhysical_append] at hold
  obtain ⟨⟨⟨⟨⟨⟨pA,pM⟩,pE⟩,pB⟩,pC⟩,pCL⟩,_⟩ := hold
  have pC1 := park_cached_physical control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)
    (by omega) pC 117 bl.symm
  have rs (i : Nat)(hi : i<ext.length) : ext.getD i 0∉((L.inputBank.take src.length).take 118) :=
    fun h => extB _ (DiagSq.getD_in ext i hi) (List.mem_of_mem_take h)
  have pLin:=InnerLinearCopy.copy_physical118 control (LowZero18Square.cacheWire L dst)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 118)
    ((L.inputBank.take src.length).take 118)
    (by simp [h128]) (by rw [List.length_take,bl,h128];decide) (bNd.sublist (List.take_sublist _ _))
    (rs 198 (by omega)) (rs 199 (by omega)) (rs 233 (by omega)) pC1
  simp only [ParkCopy10.withLowK2P10,ParkCopy10.pA,ParkCopy10.pM,ParkCopy10.pE1,ParkCopy10.pD,ParkCopy10.pMI,ParkCopy10.pB,
    ParkCopy10.pC1,ParkCopy10.pMO,ParkCopy10.pCL,ParkCopy10.pE,LowZero18Square.foldPerm,ParkCopy.move,
    gatePhysical_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨pA,pM⟩,eraseMask_physical _ _ _⟩,park_dummies_physical _⟩,
    ⟨copyRegister_physical none _ _ ndMI (by simp),copyRegister_physical none _ _ ndMO (by simp)⟩⟩,pB⟩,
    pLin⟩,⟨copyRegister_physical none _ _ ndMO (by simp),copyRegister_physical none _ _ ndMI (by simp)⟩⟩,pCL⟩,pE⟩

theorem withLowK2P10_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (B : Program) (g : Wire) (h128 : src.length=128) :
    wires (ParkCopy10.withLowK2P10 L ext control src dst B g)⊆
      wires (LowZero18Square.withLowK2 L ext control src dst B) ∪ (ParkCopy10.supportHosts ext g).toFinset := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have eSub : wires (eraseMask control (src.take 118) ((L.inputBank.take src.length).take 118))⊆
      wires (eraseMask control src (L.inputBank.take src.length)) :=
    park_wires_sub_of_mem _ _ (park_erase_mem control 118 src _ bl.symm)
  have cSub : wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) (src.take 118)
      ((L.inputBank.take src.length).take 118))⊆
      wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)) :=
    park_wires_sub_of_mem _ _ (park_cached_mem control _ 117 src _ bl.symm)
  have parkMem : ∀q∈ParkCopy10.hosts10 ext g,q∈ParkCopy10.supportHosts ext g := by
    intro q h;exact List.mem_append_left _ h
  have lin:=InnerLinearCopy.copy_wires118 control (LowZero18Square.cacheWire L dst)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 118)
    ((L.inputBank.take src.length).take 118) (by simp [h128]) (by rw [List.length_take,bl,h128];decide)
  have linSub : wires (InnerLinearCopy.copy control (LowZero18Square.cacheWire L dst)
      (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 118)
      ((L.inputBank.take src.length).take 118))⊆
      wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)) ∪
      (ParkCopy10.supportHosts ext g).toFinset := by
    intro q h
    rcases Finset.mem_union.mp (lin h) with h|h
    · exact Finset.mem_union_left _ (cSub h)
    · apply Finset.mem_union_right
      simpa only [ParkCopy10.supportHosts,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] using
        Or.inr (by simpa only [Finset.mem_insert,Finset.mem_singleton] using h)
  have bankIn : ∀q∈(L.inputBank.take src.length).drop 118,q∈wires (eraseMask control src (L.inputBank.take src.length)) :=
    fun q h => park_dst_mem_eraseMask control src _ bl.symm q (List.mem_of_mem_drop h)
  have mSub : ∀ a b : List Wire, (∀q∈a,q∈(L.inputBank.take src.length).drop 118 ∨ q∈ParkCopy10.hosts10 ext g) →
      (∀q∈b,q∈(L.inputBank.take src.length).drop 118 ∨ q∈ParkCopy10.hosts10 ext g) →
      wires (ParkCopy.move a b)⊆wires (eraseMask control src (L.inputBank.take src.length)) ∪ (ParkCopy10.supportHosts ext g).toFinset := by
    intro a b ha hb' q hq
    rcases List.mem_append.mp (List.mem_toFinset.mp (park_move_wires a b hq)) with h|h
    · rcases ha q h with h'|h'
      · exact Finset.mem_union_left _ (bankIn q h')
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (parkMem q h'))
    · rcases hb' q h with h'|h'
      · exact Finset.mem_union_left _ (bankIn q h')
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (parkMem q h'))
  have mI := mSub ((L.inputBank.take src.length).drop 118) (ParkCopy10.hosts10 ext g) (fun q h => Or.inl h) (fun q h => Or.inr h)
  have mO := mSub (ParkCopy10.hosts10 ext g) ((L.inputBank.take src.length).drop 118) (fun q h => Or.inr h) (fun q h => Or.inl h)
  have dS : wires (ParkCopy.dummies (ParkCopy10.hosts10 ext g))⊆(ParkCopy10.supportHosts ext g).toFinset := by
    intro q h;exact List.mem_toFinset.mpr (parkMem q (List.mem_toFinset.mp (park_dummies_wires _ h)))
  intro q hq
  simp only [ParkCopy10.withLowK2P10,ParkCopy10.pA,ParkCopy10.pM,ParkCopy10.pE1,ParkCopy10.pD,ParkCopy10.pMI,ParkCopy10.pB,
    ParkCopy10.pC1,ParkCopy10.pMO,ParkCopy10.pCL,ParkCopy10.pE,LowZero18Square.foldPerm,
    wires_append,Finset.mem_union] at hq
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union]
  rcases hq with (((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h)
  · simp only [h,true_or,or_true]
  · simp only [h,true_or,or_true]
  · simp only [eSub h,true_or,or_true]
  · simp only [List.mem_toFinset.mp (dS h),List.mem_toFinset,true_or,or_true]
  · rcases Finset.mem_union.mp (mI h) with h'|h'
    · simp only [h',true_or,or_true]
    · simp only [h',true_or,or_true]
  · simp only [h,true_or,or_true]
  · rcases Finset.mem_union.mp (linSub h) with h'|h' <;> simp only [h',true_or,or_true]
  · rcases Finset.mem_union.mp (mO h) with h'|h'
    · simp only [h',true_or,or_true]
    · simp only [h',true_or,or_true]
  · simp only [h,true_or,or_true]
  · simp only [h,true_or,or_true]


open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout ParkCopy
theorem eU_760_facts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (ext : List Wire) (hdx : ∀q∈ext,q∉control::L.wires)
    (hext : 300≤ext.length) :
    sqRet L≠ControlLoan1589BFFold.eU L ∧ sqHost ext≠ControlLoan1589BFFold.eU L ∧
    ControlLoan1589BFFold.eU L∉ext ∧ (∀ k, ControlLoan1589BFFold.eU L∉L.inputBank.take k) := by
  have nd := (List.nodup_cons.mp hn).2
  have eUw := InverseCarryDevelop.eU_mem_wires L hw
  have retPad : sqRet L∈L.foldPad := DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega)
  refine ⟨?_,?_,?_,?_⟩
  · exact fun e => InverseCarryDevelop.eU_off_aux L hw nd (sqRet L)
      (List.mem_append_left _ (List.mem_append_left _ retPad)) e.symm
  · exact fun e => hdx _ (sqHost_mem ext hext) (e ▸ List.mem_cons_of_mem control eUw)
  · exact fun h => hdx _ h (List.mem_cons_of_mem control eUw)
  · intro k h
    have hw' : ControlLoan1589BFFold.eU L∈L.core.work := List.mem_of_mem_take (List.mem_of_mem_take h)
    exact InverseCarryDevelop.eU_off_aux L hw nd _ (by simp [hw']) rfl

/-- `eU` is already a wire of the old high (B) leaf: the ParkCarry7 body parks its carry through it. -/
theorem eU_mem_oldBF (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (nd : L.wires.Nodup)
    (ext : List Wire) (hlen : 300≤ext.length) (away : ∀q∈ext,q∉L.wires) (control : Wire) :
    ControlLoan1589BFFold.eU L∈wires (LowZero18Square.withLowK2 L ext control L.core.high (L.core.product.take 256)
      (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) control)) := by
  have fixS := ParkCarryDevelop.fold_fixes_sumCarry L hw nd ext hlen away
  have hb : ControlLoan1589BFFold.eU L∈wires (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) control) := by
    rw [ParkCarry8Develop.hosted_eq L _ control fixS (ParkCarry8Develop.fold_fixes_source L hw nd ext hlen away)]; exact InverseCarryDevelop.eU_mem_parkCarry8 L control
  have hi : ControlLoan1589BFFold.eU L∈wires (renameProgram (LowZero18Square.foldPerm L ext)
      (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) control)) := by
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_,hb,InverseCarryDevelop.fold_fixes_eU L hw nd ext hlen away⟩
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union]
  simp only [hi,true_or,or_true]
section Park10
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length) (g : Wire)

include hx hext in
theorem sqHost_not_hosts10 (hgH : sqHost ext≠g) : sqHost ext∉ParkCopy10.hosts10 ext g := by
  intro h
  rcases List.mem_append.mp h with h|h
  · exact sqHost_not_hosts ext hx hext h
  · exact hgH (List.mem_singleton.mp h)

include hw hn hx hdx hext in
/-- `sqRet` is outside every parking piece; `sqHost` is outside the pieces before the body. -/
theorem park_pieces_free10 (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hlen : dst.length=2*src.length)
    (hgR : sqRet L≠g) (hgH : sqHost ext≠g) (hgB : g∉L.inputBank.take src.length) :
    sqRet L∉wires (ParkCopy10.pE1 L control src) ∧ sqRet L∉wires (ParkCopy10.pD ext g) ∧
    sqRet L∉wires (ParkCopy10.pMI L ext src g) ∧ sqRet L∉wires (ParkCopy10.pC1 L ext control src dst) ∧
    sqRet L∉wires (ParkCopy10.pMO L ext src g) ∧
    sqHost ext∉wires (ParkCopy10.pE1 L control src) ∧ sqHost ext∉wires (ParkCopy10.pD ext g) ∧
    sqHost ext∉wires (ParkCopy10.pMI L ext src g) ∧
    sqHost ext∉wires (eraseMask control src (L.inputBank.take src.length)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hostE := sqHost_in ext hext
  have hostH := sqHost_not_hosts10 ext hx hext g hgH
  have hostsE : ∀q∈ParkCopy10.hosts10 ext g,q∈ext ∨ q=g := fun q h =>
    (List.mem_append.mp h).imp (ParkCopy.hosts_sub ext hext q) List.mem_singleton.mp
  have outerCS : ∀q∈control::(src++L.inputBank.take src.length),sqRet L≠q :=
    fun q h => ne _ (cs_outer L control ext src dst _ h)
  have outerE : ∀q∈ext,sqRet L≠q := fun q h => ne _ (ext_outer L control ext src dst _ h)
  have take_cs : ∀q∈control::(src.take 118++(L.inputBank.take src.length).take 118),
      q∈control::(src++L.inputBank.take src.length) := by
    intro q h
    simp only [List.mem_cons,List.mem_append] at h ⊢
    rcases h with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl (List.mem_of_mem_take h))
    · exact Or.inr (Or.inr (List.mem_of_mem_take h))
  have hostCS : ∀q∈control::(src++L.inputBank.take src.length),sqHost ext≠q := by
    intro q h e
    subst e
    rcases List.mem_cons.mp h with h|h
    · exact hdx _ hostE (by simp [h])
    · rcases List.mem_append.mp h with h|h
      · exact extSrc _ hostE h
      · exact extB _ hostE h
  have moveFree : ∀ a b : List Wire, (∀q∈a,q∈(L.inputBank.take src.length) ∨ q∈ext ∨ q=g) →
      (∀q∈b,q∈(L.inputBank.take src.length) ∨ q∈ext ∨ q=g) → sqRet L∉wires (ParkCopy.move a b) := by
    intro a b ha hb' used
    have h := List.mem_toFinset.mp (park_move_wires a b used)
    rcases List.mem_append.mp h with h|h
    · rcases ha _ h with h'|h'|h'
      · exact outerCS _ (List.mem_cons_of_mem _ (List.mem_append_right _ h')) rfl
      · exact outerE _ h' rfl
      · exact hgR h'
    · rcases hb' _ h with h'|h'|h'
      · exact outerCS _ (List.mem_cons_of_mem _ (List.mem_append_right _ h')) rfl
      · exact outerE _ h' rfl
      · exact hgR h'
  have dropB : ∀q∈(L.inputBank.take src.length).drop 118,q∈(L.inputBank.take src.length) ∨ q∈ext ∨ q=g :=
    fun q h => Or.inl (List.mem_of_mem_drop h)
  have hostsBE : ∀q∈ParkCopy10.hosts10 ext g,q∈(L.inputBank.take src.length) ∨ q∈ext ∨ q=g := fun q h => Or.inr (hostsE q h)
  have cacheIn : LowZero18Square.cacheWire L dst∈kOuter L control ext src dst := by
    rw [LowZero18Square.cacheWire_fixed L hw (List.nodup_cons.mp hn).2 dst hd (by omega)]
    have mem := CachedSquareCopy.head_mem dst (by omega)
    simp only [kOuter,List.mem_cons,List.mem_append,mem,or_true,true_or]
  refine ⟨?_,?_,moveFree _ _ dropB hostsBE,?_,moveFree _ _ hostsBE dropB,?_,?_,?_,?_⟩
  · exact fun used => outerCS _ (take_cs _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used))) rfl
  · exact fun used => (hostsE _ (List.mem_toFinset.mp (park_dummies_wires _ used))).elim (fun h => outerE _ h rfl) hgR
  · intro used
    have bl : 118≤(L.inputBank.take src.length).length := by
      simp only [List.length_take,(L.measured_bank_widths hw).1];omega
    have sub:=InnerLinearCopy.copy_wires118 control (LowZero18Square.cacheWire L dst)
      (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)
      (src.take 118) ((L.inputBank.take src.length).take 118)
      (by simp only [List.length_take];omega) (by rw [List.length_take];exact Nat.min_eq_left bl) used
    rcases Finset.mem_union.mp sub with used|r
    · rcases Finset.mem_union.mp (CachedSquareCopy.wires_subset _ _ _ _ used) with h|h
      · have h' := List.mem_toFinset.mp (copyRegister_wires_subset _ _ _ h)
        exact outerCS _ (take_cs _ (by simpa only [Option.toList_some,List.singleton_append,
          List.cons_append,List.append_assoc] using h')) rfl
      · exact ne _ cacheIn (Finset.mem_singleton.mp h)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at r
      rcases r with e|e|e <;> exact outerE _ (e ▸ DiagSq.getD_in ext _ (by omega)) rfl
  · exact fun used => hostCS _ (take_cs _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used))) rfl
  · exact fun used => hostH (List.mem_toFinset.mp (park_dummies_wires _ used))
  · intro used
    rcases List.mem_append.mp (List.mem_toFinset.mp (park_move_wires _ _ used)) with h|h
    · exact extB _ hostE (List.mem_of_mem_drop h)
    · exact hostH h
  · exact fun used => hostCS _ (List.mem_toFinset.mp (eraseMask_wires_subset _ _ _ used)) rfl

end Park10
theorem withLowK2P10_760_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
    (hext : 300≤ext.length) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset)
    (g : Wire) (hgR : sqRet L≠g) (hgH : sqHost ext≠g) (hgB : g∉L.inputBank.take src.length) :
    sqRet L∉wires (ParkCopy10.withLowK2P10 L ext control src dst (bodySwap L ext B) g) := by
  have m := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have k := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen hext
  have f := sqRet_body_free L hw control hn ext hx hdx hext src dst hs hd B hb
  have pf := park_pieces_free10 L hw control hn ext hx hdx hext g src dst hs hd h128 hlen hgR hgH hgB
  simp only [ParkCopy10.withLowK2P10,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨m.1,k.1⟩,pf.1⟩,pf.2.1⟩,pf.2.2.1⟩,f⟩,pf.2.2.2.1⟩,pf.2.2.2.2.1⟩,k.2⟩,m.2⟩

theorem withLowK2P_760_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
    (hext : 300≤ext.length) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (ParkCopy.withLowK2P L ext control src dst (bodySwap L ext B)) := by
  have m := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have k := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen hext
  have f := sqRet_body_free L hw control hn ext hx hdx hext src dst hs hd B hb
  have pf := park_pieces_free L hw control hn ext hx hdx hext src dst hs hd h128 hlen
  simp only [ParkCopy.withLowK2P,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨m.1,k.1⟩,pf.1⟩,pf.2.1⟩,pf.2.2.1⟩,f⟩,pf.2.2.2.1⟩,pf.2.2.2.2.1⟩,k.2⟩,m.2⟩

theorem withLowK2S_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (B : Program) (h128 : src.length=129) :
    toffoliCount (ParkCopyS.withLowK2S L ext control src dst B)+5=
      toffoliCount (LowZero18Square.withLowK2 L ext control src dst B) ∧
    measurementCount (ParkCopyS.withLowK2S L ext control src dst B)=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) ∧
    Challenge.gateSlots (ParkCopyS.withLowK2S L ext control src dst B)=
      Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst B)+10 := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have l1 : (src.take 124).length=((L.inputBank.take src.length).take 124).length := by
    simp only [List.length_take,bl]
  have l1' : (src.take 124).length=124 := by simp [h128]
  have ld : ((L.inputBank.take src.length).drop 124).length=5 := by rw [List.length_drop,bl,h128]
  have hl := ParkCopyS.hostsS_length ext
  have ef := eraseMask_counts control src (L.inputBank.take src.length) bl.symm
  have e1 := eraseMask_counts control (src.take 124) ((L.inputBank.take src.length).take 124) l1
  have esf := UncompSwap.eraseMask_slots control src (L.inputBank.take src.length) bl.symm
  have es1 := UncompSwap.eraseMask_slots control (src.take 124) ((L.inputBank.take src.length).take 124) l1
  have dc := ParkCopy.dummies_counts (ParkCopyS.hostsS ext)
  have ds := park_dummies_slots (ParkCopyS.hostsS ext)
  have mi := park_move_counts ((L.inputBank.take src.length).drop 124) (ParkCopyS.hostsS ext) (by rw [ld,hl])
  have mo := park_move_counts (ParkCopyS.hostsS ext) ((L.inputBank.take src.length).drop 124) (by rw [ld,hl])
  have cf := park_cached_counts control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)
    bl.symm (by omega)
  have c1 := park_cached_counts control (LowZero18Square.cacheWire L dst) (src.take 124)
    ((L.inputBank.take src.length).take 124) l1 (by omega)
  simp only [ParkCopyS.withLowK2S,ParkCopyS.pA,ParkCopyS.pM,ParkCopyS.pE1,ParkCopyS.pD,ParkCopyS.pMI,ParkCopyS.pB,
    ParkCopyS.pC1,ParkCopyS.pMO,ParkCopyS.pCL,ParkCopyS.pE,LowZero18Square.foldPerm,
    LowZero18Square.withLowK2,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  simp only [l1',hl,bl,ld,h128] at *
  omega

theorem withLowK2S_swap_mc (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (B : Program) (h128 : src.length=129) :
    measurementCount (ParkCopyS.withLowK2S L ext control src dst (bodySwap L ext B))=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) :=
  (withLowK2S_counts L hw ext control src dst _ h128).2.1.trans
    (withLowK2_swap_counts L ext control src dst B).2.1

theorem withLowK2S_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : src.length=129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (hold : GatePhysical (LowZero18Square.withLowK2 L ext control src dst B)) :
    GatePhysical (ParkCopyS.withLowK2S L ext control src dst B) := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have hostsE : ∀q∈ParkCopyS.hostsS ext,q∈ext := ParkCopyS.hostsS_sub ext he
  have hHnd : (ParkCopyS.hostsS ext).Nodup := ParkCopyS.hostsS_nodup ext hx he
  have ndMI : ((L.inputBank.take src.length).drop 124++ParkCopyS.hostsS ext).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => extB b (hostsE b hb) (e ▸ List.mem_of_mem_drop ha)⟩
  have ndMO : (ParkCopyS.hostsS ext++(L.inputBank.take src.length).drop 124).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  simp only [LowZero18Square.withLowK2,gatePhysical_append] at hold
  obtain ⟨⟨⟨⟨⟨⟨pA,pM⟩,pE⟩,pB⟩,pC⟩,pCL⟩,_⟩ := hold
  have pC1 := park_cached_physical control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)
    (by omega) pC 123 bl.symm
  simp only [ParkCopyS.withLowK2S,ParkCopyS.pA,ParkCopyS.pM,ParkCopyS.pE1,ParkCopyS.pD,ParkCopyS.pMI,ParkCopyS.pB,
    ParkCopyS.pC1,ParkCopyS.pMO,ParkCopyS.pCL,ParkCopyS.pE,LowZero18Square.foldPerm,ParkCopy.move,
    gatePhysical_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨pA,pM⟩,eraseMask_physical _ _ _⟩,park_dummies_physical _⟩,
    ⟨copyRegister_physical none _ _ ndMI (by simp),copyRegister_physical none _ _ ndMO (by simp)⟩⟩,pB⟩,
    pC1⟩,⟨copyRegister_physical none _ _ ndMO (by simp),copyRegister_physical none _ _ ndMI (by simp)⟩⟩,pCL⟩,pE⟩

/-- Parking adds only the five host wires to the leaf's support. -/
theorem withLowK2S_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (B : Program) (h128 : src.length=129) :
    wires (ParkCopyS.withLowK2S L ext control src dst B)⊆
      wires (LowZero18Square.withLowK2 L ext control src dst B) ∪ (ParkCopyS.hostsS ext).toFinset := by
  have sizes := L.measured_bank_widths hw
  have bl : (L.inputBank.take src.length).length=src.length := by
    rw [List.length_take,sizes.1]; omega
  have eSub : wires (eraseMask control (src.take 124) ((L.inputBank.take src.length).take 124))⊆
      wires (eraseMask control src (L.inputBank.take src.length)) :=
    park_wires_sub_of_mem _ _ (park_erase_mem control 124 src _ bl.symm)
  have cSub : wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) (src.take 124)
      ((L.inputBank.take src.length).take 124))⊆
      wires (CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) src (L.inputBank.take src.length)) :=
    park_wires_sub_of_mem _ _ (park_cached_mem control _ 123 src _ bl.symm)
  have bankIn : ∀q∈(L.inputBank.take src.length).drop 124,q∈wires (eraseMask control src (L.inputBank.take src.length)) :=
    fun q h => park_dst_mem_eraseMask control src _ bl.symm q (List.mem_of_mem_drop h)
  have mSub : ∀ a b : List Wire, (∀q∈a,q∈(L.inputBank.take src.length).drop 124 ∨ q∈ParkCopyS.hostsS ext) →
      (∀q∈b,q∈(L.inputBank.take src.length).drop 124 ∨ q∈ParkCopyS.hostsS ext) →
      wires (ParkCopy.move a b)⊆wires (eraseMask control src (L.inputBank.take src.length)) ∪ (ParkCopyS.hostsS ext).toFinset := by
    intro a b ha hb' q hq
    rcases List.mem_append.mp (List.mem_toFinset.mp (park_move_wires a b hq)) with h|h
    · rcases ha q h with h'|h'
      · exact Finset.mem_union_left _ (bankIn q h')
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h')
    · rcases hb' q h with h'|h'
      · exact Finset.mem_union_left _ (bankIn q h')
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h')
  have mI := mSub ((L.inputBank.take src.length).drop 124) (ParkCopyS.hostsS ext) (fun q h => Or.inl h) (fun q h => Or.inr h)
  have mO := mSub (ParkCopyS.hostsS ext) ((L.inputBank.take src.length).drop 124) (fun q h => Or.inr h) (fun q h => Or.inl h)
  have dS : wires (ParkCopy.dummies (ParkCopyS.hostsS ext))⊆(ParkCopyS.hostsS ext).toFinset := park_dummies_wires _
  intro q hq
  simp only [ParkCopyS.withLowK2S,ParkCopyS.pA,ParkCopyS.pM,ParkCopyS.pE1,ParkCopyS.pD,ParkCopyS.pMI,ParkCopyS.pB,
    ParkCopyS.pC1,ParkCopyS.pMO,ParkCopyS.pCL,ParkCopyS.pE,LowZero18Square.foldPerm,
    wires_append,Finset.mem_union] at hq
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union]
  rcases hq with (((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h)
  · simp only [h,true_or,or_true]
  · simp only [h,true_or,or_true]
  · simp only [eSub h,true_or,or_true]
  · simp only [List.mem_toFinset.mp (dS h),List.mem_toFinset,true_or,or_true]
  · rcases Finset.mem_union.mp (mI h) with h'|h'
    · simp only [h',true_or,or_true]
    · simp only [h',true_or,or_true]
  · simp only [h,true_or,or_true]
  · simp only [cSub h,true_or,or_true]
  · rcases Finset.mem_union.mp (mO h) with h'|h'
    · simp only [h',true_or,or_true]
    · simp only [h',true_or,or_true]
  · simp only [h,true_or,or_true]
  · simp only [h,true_or,or_true]

theorem withLowK2S_760_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
    (hext : 300≤ext.length) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (ParkCopyS.withLowK2S L ext control src dst (bodySwap L ext B)) := by
  have m := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have k := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen hext
  have f := sqRet_body_free L hw control hn ext hx hdx hext src dst hs hd B hb
  have pf := park_pieces_freeS L hw control hn ext hx hdx hext src dst hs hd h128 hlen
  simp only [ParkCopyS.withLowK2S,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨m.1,k.1⟩,pf.1⟩,pf.2.1⟩,pf.2.2.1⟩,f⟩,pf.2.2.2.1⟩,pf.2.2.2.2.1⟩,k.2⟩,m.2⟩

section Free2
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hw hn hx hdx hext in
theorem core760_free : sqRet L∉wires (core760 L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have hl (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have hh (q : Wire) : L.core.high.count q≤L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := hh q
    simp only [List.count_append]
    omega
  have hs (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := hh q
    simp only [CuccaroStreamedSquareLayout.sum,List.count_append] at h ⊢
    omega
  have hp (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have fU := eU_760_facts L hw control hn ext hdx hext
  have sa := withLowK2P10_760_free L hw control hn ext hx hdx hext L.core.low (L.core.product.take 256)
    hl hp (by omega) (by omega) (by simp [hw.core.product,low]) _ (FullASelectedDevelop.hostedASelected_fold_support L hw nd ext control hext (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h))) _ fU.1 fU.2.1 (fU.2.2.2 _)
  have sb := withLowK2P_760_free L hw control hn ext hx hdx hext L.core.high (L.core.product.take 256)
    hb hp (by omega) (by omega) (by simp [hw.core.product,high]) _ (ParkCarry10Develop.hosted_fold_support L hw nd ext control hext (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h)))
  have sc := withLowK2S_760_free L hw control hn ext hx hdx hext L.core.sum L.core.product
    hs (fun _=>le_rfl) (by omega) (by omega) (by rw [hw.core.product,sum]) _
    (OwnDiagAll12Square.bodyCK_supportTq L hw nd control)
  have coreOff := sqRet_not_core L hw control hn
  have gs := g_core_support L hw
  have gp : sqRet L∉wires (OwnDiagAll12Square.gPrep L) := fun u => coreOff (List.mem_toFinset.mp (gs.1 u))
  have gc : sqRet L∉wires (OwnDiagAll12Square.gClear L) := fun u => coreOff (List.mem_toFinset.mp (gs.2 u))
  simp only [core760,branchCK760,branchBF760,branchAF760,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨gp,sc⟩,gc⟩,sb⟩,sa⟩

end Free2

section Placed
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
private theorem pool_getD' (i : Nat) (hi : i<2613) : L.dialogPool.getD i 0=L.core.poolWire i := by
  have shape := pool_block L hw 2613 (le_refl _)
  rw [List.take_of_length_le (by rw [L.dialogPool_length hw])] at shape
  rw [shape,List.getD_eq_getElem _ _ (by simp [wireBlock];omega)]
  simp [wireBlock]

include hw in
theorem sqRet_pool760 : sqRet L.dialogStreamedSquareWide=L.core.poolWire 760 := by
  rw [sqRet_ktmp,← ktmp_eq,SquareCarryLoan719Inventory.ktmp_layout L hw,List.getD_eq_getElem _ _ (by
    simp only [List.length_take,List.length_drop,L.dialogPool_length hw]
    omega)]
  simp only [List.getElem_take,List.getElem_drop,Nat.reduceAdd]
  have bound : 760<L.dialogPool.length := by rw [L.dialogPool_length hw];omega
  have same := pool_getD' L hw 760 (by omega)
  rw [List.getD_eq_getElem L.dialogPool 0 bound] at same
  exact same

theorem sqHost_pool1363 : sqHost (OwnDiagAll12Square.kext L)=L.core.poolWire 1363 := by
  simp [sqHost,OwnDiagAll12Square.kext,wireBlock]

include hw hn in
private theorem pool_fix (k a b : Nat) (hk : k<2613) (ha : a<2613) (hb : b<2613) (na : k≠a) (nb : k≠b) :
    Equiv.swap (L.core.poolWire a) (L.core.poolWire b) (L.core.poolWire k)=L.core.poolWire k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq
    exact na (pool_inj L hw hn k a hk ha eq)
  · intro eq
    exact nb (pool_inj L hw hn k b hk hb eq)

include hw hn in
/-- Every placement map of the square fixes pool sites 760 and 1363. -/
theorem place_fix (k : Nat) (hk : k=760 ∨ k=1363) (P : Program) (free : L.core.poolWire k∉wires P) :
    L.core.poolWire k∉wires (SquareCarryLoan719BF.place L P) := by
  have kb : k<2613 := by omega
  have blockFix : Square5Placement.blockPerm L 202 (L.core.poolWire k)=L.core.poolWire k := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) k kb]
    rcases hk with rfl|rfl <;> rfl
  have p0 := OwnPlusHost.rename_avoid _ _ _ blockFix free
  have p1 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 766 1530 kb (by omega) (by omega) (by omega) (by omega)) p0
  have p2 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 765 1531 kb (by omega) (by omega) (by omega) (by omega)) p1
  have p3 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 767 1532 kb (by omega) (by omega) (by omega) (by omega)) p2
  have p4 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 770 1536 kb (by omega) (by omega) (by omega) (by omega)) p3
  have p5 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 1285 1537 kb (by omega) (by omega) (by omega) (by omega)) p4
  have p6 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 1286 1538 kb (by omega) (by omega) (by omega) (by omega)) p5
  have p7 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 769 1539 kb (by omega) (by omega) (by omega) (by omega)) p6
  have p8 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 768 775 kb (by omega) (by omega) (by omega) (by omega)) p7
  have p9 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 718 907 kb (by omega) (by omega) (by omega) (by omega)) p8
  simpa only [SquareCarryLoan719BF.place,OwnPlusSquare.swap,OwnGuardSquare.swap,
    OwnQ4Square.swap,OwnQ5Square.swap,OwnDiagAll12PlacedQ6.swap,OwnDiagAll12PlacedQ7.swap,
    PrefixFrontierSquare1591.swap,Prefix1590Square.swap,ControlLoan1589Square.swap] using p9

include hw hn in
/-- **R2 square deliverable**: the new square never touches physical pool site 760. -/
theorem square760_free : L.core.poolWire 760∉wires (program760 L) := by
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have core := core760_free L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic controlND (OwnDiagAll12Square.kext L) he.nodup he.away he.len
  rw [sqRet_pool760 L hw] at core
  exact place_fix L hw hn 760 (Or.inl rfl) _ core

end Placed

/-! ## Square: counts, slots, physicality, support -/

theorem gatePhysical_rename_iff (e : Equiv.Perm Wire) (P : Program) :
    GatePhysical (renameProgram e P)↔GatePhysical P := by
  constructor
  · intro h i hi
    have hh := h (renameInstr e i) (List.mem_map_of_mem hi)
    cases i <;> simp_all [renameInstr,RecordedQuantum.PhysicalInstr,ECDSAAdd.ProperGate,e.injective.eq_iff]
  · exact gatePhysical_rename e e.injective P

theorem place_physical_iff (L : ControlledPointLayout) (P : Program) :
    GatePhysical (SquareCarryLoan719BF.place L P)↔GatePhysical P := by
  simp only [SquareCarryLoan719BF.place,gatePhysical_rename_iff]

theorem fastCore760_shape (L : ControlledPointLayout) :
    ReflectionE1Low48Square.program L=SquareCarryLoan719BF.place L (ReflectionE1Low48Square.fastCore L) := rfl

theorem program760_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program760 L) := by
  have old := ReflectionE1Low48Square.physical L hw hn
  rw [fastCore760_shape,place_physical_iff] at old
  rw [program760,place_physical_iff]
  simp only [ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,gatePhysical_append] at old
  obtain ⟨⟨⟨⟨gp,ck⟩,gc⟩,bf⟩,af⟩ := old
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have hw' := L.dialogStreamedSquareWide_widths hw
  have swapP : ∀ (src dst : List Wire) (B : Program),
      GatePhysical (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic src dst B) →
      GatePhysical (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic src dst
        (bodySwap L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) B)) := by
    intro src dst B h
    simp only [LowZero18Square.withLowK2,bodySwap,gatePhysical_append,gatePhysical_rename_iff] at h ⊢
    exact h
  have hiC (q : Wire) : L.dialogStreamedSquareWide.core.high.count q≤
      (L.dialogStreamedSquareWide.core.y++[L.dialogStreamedSquareWide.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.dialogStreamedSquareWide.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.dialogStreamedSquareWide.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have loC (q : Wire) : L.dialogStreamedSquareWide.core.low.count q≤
      (L.dialogStreamedSquareWide.core.y++[L.dialogStreamedSquareWide.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.dialogStreamedSquareWide.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have pC (q : Wire) : (L.dialogStreamedSquareWide.core.product.take 256).count q≤
      L.dialogStreamedSquareWide.core.product.count q :=
    (List.take_sublist 256 L.dialogStreamedSquareWide.core.product).count_le q
  have hi := L.dialogStreamedSquareWide.core.high_length hw'.core
  have lo := L.dialogStreamedSquareWide.core.low_length hw'.core
  have pl : (L.dialogStreamedSquareWide.core.product.take 256).length=256 := by simp [hw'.core.product]
  have suC (q : Wire) : L.dialogStreamedSquareWide.core.sum.count q≤
      (L.dialogStreamedSquareWide.core.y++[L.dialogStreamedSquareWide.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.dialogStreamedSquareWide.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.dialogStreamedSquareWide.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have su := L.dialogStreamedSquareWide.core.sum_length hw'.core
  have bf9 : GatePhysical (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
      L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
      (ParkCarry10Develop.hostedBody L.dialogStreamedSquareWide
        (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) := by
    have hb9 : GatePhysical (renameProgram (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))
      (ParkCarry10Develop.hostedBody L.dialogStreamedSquareWide
        (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) := by
      apply gatePhysical_rename _ (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)).injective _
      rw [ParkCarry10Develop.hosted_eq _ _ _ (ParkCarryDevelop.fold_fixes_sumCarry _ hw'
        (List.nodup_cons.mp controlND).2 _ he.len (fun q hq h=>he.away q hq (List.mem_cons_of_mem _ h)))]
      exact ParkCarry10Develop.body_physical _ hw' _ controlND
    simp only [LowZero18Square.withLowK2,gatePhysical_append] at bf ⊢
    tauto
  have af3 : GatePhysical (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
      L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
      (FullASelectedDevelop.hostedASelected L.dialogStreamedSquareWide
        (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) := by
    have hb3 : GatePhysical (renameProgram (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))
      (FullASelectedDevelop.hostedASelected L.dialogStreamedSquareWide
        (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) := by
      apply gatePhysical_rename _ (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)).injective _
      rw [FullASelectedDevelop.hostedASelected_eq _ _ _ (ParkCarryDevelop.fold_fixes_sumCarry _ hw'
        (List.nodup_cons.mp controlND).2 _ he.len (fun q hq h=>he.away q hq (List.mem_cons_of_mem _ h)))]
      exact FullASelectedDevelop.aBodySelected_physical _ hw' _ controlND
    simp only [LowZero18Square.withLowK2,gatePhysical_append] at af ⊢
    tauto
  simp only [fastCore760,core760,branchCK760,branchBF760,branchAF760,gatePhysical_append]
  refine ⟨⟨⟨⟨gp,withLowK2S_physical _ hw' _ controlND _ _ suC (fun _ => le_rfl) su
    (by rw [hw'.core.product,su]) _ he.nodup he.away he.len _ (swapP _ _ _ ck)⟩,gc⟩,?_⟩,?_⟩
  · exact withLowK2P_physical _ hw' _ controlND _ _ hiC pC hi (by rw [pl,hi]) _ he.nodup he.away he.len _
      (swapP _ _ _ bf9)
  · have fU := eU_760_facts _ hw' _ controlND _ he.away he.len
    exact withLowK2P10_physical _ hw' _ controlND _ _ loC pC lo (by rw [pl,lo]) _ he.nodup he.away he.len _
      _ fU.2.2.1 (fU.2.2.2 _) (swapP _ _ _ af3)

theorem program760_counts_gen (L : ControlledPointLayout) (hw : L.Widths) (d : Nat)
    (hd : toffoliCount (FullASelectedDevelop.hostedASelected L.dialogStreamedSquareWide
        (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)+d≤
      toffoliCount (ThirdSavedCarryDevelop.hostedATriple L.dialogStreamedSquareWide
        (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) :
    toffoliCount (program760 L)+31+d≤toffoliCount (ReflectionE1Low48Square.program L) ∧
    measurementCount (program760 L)=measurementCount (ReflectionE1Low48Square.program L) ∧
    Challenge.gateSlots (program760 L)≤Challenge.gateSlots (ReflectionE1Low48Square.program L)+48 := by
  have hw' := L.dialogStreamedSquareWide_widths hw
  have hi := L.dialogStreamedSquareWide.core.high_length hw'.core
  have lo := L.dialogStreamedSquareWide.core.low_length hw'.core
  have cB := withLowK2P_counts L.dialogStreamedSquareWide hw' (OwnDiagAll12Square.kext L) L.core.generic
    L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
    (bodySwap L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)
      (ParkCarry10Develop.hostedBody L.dialogStreamedSquareWide
        (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) hi
  have sB := withLowK2_swap_counts L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
    L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
    (ParkCarry10Develop.hostedBody L.dialogStreamedSquareWide
      (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)
  have cA := withLowK2P10_counts L.dialogStreamedSquareWide hw' (OwnDiagAll12Square.kext L) L.core.generic
    L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
    (bodySwap L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)
      (FullASelectedDevelop.hostedASelected L.dialogStreamedSquareWide (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) (ControlLoan1589BFFold.eU L.dialogStreamedSquareWide) lo
  have sA := withLowK2_swap_counts L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
    L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
    (FullASelectedDevelop.hostedASelected L.dialogStreamedSquareWide (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)
  have sC := withLowK2_swap_counts L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
    L.dialogStreamedSquareWide.core.sum L.dialogStreamedSquareWide.core.product
    (OwnDiagAll12Square.bodyCKTq L.dialogStreamedSquareWide L.core.generic)
  have su := L.dialogStreamedSquareWide.core.sum_length hw'.core
  have cC := withLowK2S_counts L.dialogStreamedSquareWide hw' (OwnDiagAll12Square.kext L) L.core.generic
    L.dialogStreamedSquareWide.core.sum L.dialogStreamedSquareWide.core.product
    (bodySwap L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)
      (OwnDiagAll12Square.bodyCKTq L.dialogStreamedSquareWide L.core.generic)) su
  have nB := ParkCarry10Develop.hosted_counts L.dialogStreamedSquareWide hw'
    (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic
  have oB := ParkCarry8Develop.hosted_counts L.dialogStreamedSquareWide hw'
    (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic
  have nS := ParkCarry10Develop.hosted_slots L.dialogStreamedSquareWide hw'
    (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic
  have oS := ParkCarry8Develop.hosted_slots L.dialogStreamedSquareWide hw'
    (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic
  have dS := ParkCarry10Develop.body_slots L.dialogStreamedSquareWide hw' L.core.generic
  have bDelta :
      toffoliCount (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
        (ParkCarry10Develop.hostedBody L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic))+2 =
      toffoliCount (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
        (ParkCarry8Develop.hostedBody L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) ∧
      measurementCount (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
        (ParkCarry10Develop.hostedBody L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) =
      measurementCount (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
        (ParkCarry8Develop.hostedBody L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) ∧
      Challenge.gateSlots (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
        (ParkCarry10Develop.hostedBody L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic))+3 =
      Challenge.gateSlots (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.high (L.dialogStreamedSquareWide.core.product.take 256)
        (ParkCarry8Develop.hostedBody L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) := by
    simp only [LowZero18Square.withLowK2,toffoliCount_append,measurementCount_append,
      Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
    exact ⟨by omega,by omega,by omega⟩
  have aDelta :
      toffoliCount (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
        (FullASelectedDevelop.hostedASelected L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic))+1+d ≤
      toffoliCount (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
        (InverseCarryDevelop.hostedADual L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) ∧
      measurementCount (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
        (FullASelectedDevelop.hostedASelected L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) =
      measurementCount (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
        (InverseCarryDevelop.hostedADual L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) ∧
      Challenge.gateSlots (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
        (FullASelectedDevelop.hostedASelected L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic))+3 ≤
      Challenge.gateSlots (LowZero18Square.withLowK2 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic
        L.dialogStreamedSquareWide.core.low (L.dialogStreamedSquareWide.core.product.take 256)
        (InverseCarryDevelop.hostedADual L.dialogStreamedSquareWide
          (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic)) := by
    have h := ThirdSavedCarryDevelop.hostedATriple_counts L.dialogStreamedSquareWide hw'
      (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic
    have r := FullASelectedDevelop.hostedASelected_resources L.dialogStreamedSquareWide hw'
      (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic
    simp only [LowZero18Square.withLowK2,toffoliCount_append,measurementCount_append,
      Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots]
    exact ⟨by omega,by omega,by omega⟩
  rw [fastCore760_shape]
  simp only [program760,SquareCarryLoan719BF.place,fastCore760,core760,branchCK760,branchBF760,branchAF760,
    ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,
    toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  refine ⟨?_,?_,?_⟩ <;> omega

theorem program760_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program760 L)+31≤toffoliCount (ReflectionE1Low48Square.program L) ∧
    measurementCount (program760 L)=measurementCount (ReflectionE1Low48Square.program L) ∧
    Challenge.gateSlots (program760 L)≤Challenge.gateSlots (ReflectionE1Low48Square.program L)+48 := by
  have r := (FullASelectedDevelop.hostedASelected_resources L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw)
    (LowZero18Square.foldPerm L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L)) L.core.generic).1
  have h := program760_counts_gen L hw 0 (by omega)
  exact ⟨by omega,h.2.1,h.2.2⟩

theorem program760_slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program760 L)≤Challenge.gateSlots (ReflectionE1Low48Square.program L)+48 :=
  (program760_counts L hw).2.2

def savedA (L : ControlledPointLayout) : Nat :=
  toffoliCount (ReflectionE1Square.program L)-(toffoliCount (program760 L)+3064)

theorem counts_diff760 (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program760 L)+3064+savedA L=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program760 L)+75=measurementCount (ReflectionE1Square.program L) := by
  have c := program760_counts L hw
  have d := ReflectionE1Low48Square.counts_diff L hw
  unfold savedA
  constructor <;> omega

theorem slots_le760 (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program760 L)≤Challenge.gateSlots (ReflectionE1Square.program L)+48 := by
  have s := program760_slots L hw
  have := ReflectionE1Low48Square.slots_le L hw
  omega






































theorem rename_ins (e : Equiv.Perm Wire) (h : Wire) (P Q : Program)
    (sub : wires P⊆insert h (wires Q)) (fix : e h=h) :
    wires (renameProgram e P)⊆insert h (wires (renameProgram e Q)) := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (sub hx) with e'|hx'
  · subst x; rw [fix]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx')

theorem swap_ins (a b : Wire) (P : Program) (hb : b∉wires P) :
    wires (renameProgram (Equiv.swap a b) P)⊆insert b (wires P) :=
  (swap_support a b P hb).trans (Finset.insert_subset_insert _ (Finset.erase_subset _ _))

theorem rename_ins_set (e : Equiv.Perm Wire) (S : Finset Wire) (P Q : Program)
    (sub : wires P⊆S ∪ wires Q) (fix : ∀ h∈S, e h=h) :
    wires (renameProgram e P)⊆S ∪ wires (renameProgram e Q) := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (sub hx) with e'|hx'
  · rw [fix x e']; exact Finset.mem_union_left _ e'
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx')

section SupportNew
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hw hx hdx hext in
theorem withLowK2_ins (src dst : List Wire) (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    wires (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))⊆
      insert (sqHost ext) (wires (LowZero18Square.withLowK2 L ext control src dst B)) := by
  have bfree : sqHost ext∉wires B := fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used))
  have fix : SquareCarryLoan719.foldPerm L ext (sqHost ext)=sqHost ext := by
    rw [SquareCarryLoan719.foldPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (sqHost_ne_target L hw control ext hdx hext) (sqHost_ne_ext0 ext hx hext)
  have body := rename_ins _ _ _ _ (swap_ins (sqRet L) (sqHost ext) B bfree) fix
  intro q hq
  simp only [LowZero18Square.withLowK2,bodySwap,sqSwap,wires_append,Finset.mem_union,Finset.mem_insert] at hq ⊢
  rcases hq with ((((((h|h)|h)|h)|h)|h)|h)
  all_goals first
    | (rcases Finset.mem_insert.mp (body h) with e|e
       · exact Or.inl e
       · tauto)
    | tauto

theorem rename_insert (f : Wire→Wire) (P Q : Program) (v : Wire)
 (h : wires P⊆insert v (wires Q)) :
 wires (renameProgram f P)⊆insert (f v) (wires (renameProgram f Q)) := by
 rw [renameProgram_support,renameProgram_support,←Finset.image_insert]
 exact Finset.image_mono f h

theorem program_insert (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (c : Wire)
 (src dst : List Wire) (P Q : Program) (v : Wire) (sub : wires P⊆insert v (wires Q)) :
 wires (LowZero18Square.withLowK2 L ext c src dst P)⊆
 insert (LowZero18Square.foldPerm L ext v) (wires (LowZero18Square.withLowK2 L ext c src dst Q)) := by
 have ren:=rename_insert (LowZero18Square.foldPerm L ext) P Q v sub
 intro q h
 have leaf : q∈wires (renameProgram (LowZero18Square.foldPerm L ext) P) →
  q=LowZero18Square.foldPerm L ext v ∨ q∈wires (renameProgram (LowZero18Square.foldPerm L ext) Q) :=
  fun hp=>Finset.mem_insert.mp (ren hp)
 simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union] at h ⊢
 simp only [Finset.mem_insert,Finset.mem_union]
 itauto

theorem carry10_low_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (ext : List Wire) (c : Wire) (hn : (c::L.wires).Nodup) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉c::L.wires) (hext : 300≤ext.length) :
 wires (LowZero18Square.withLowK2 L ext c L.core.high (L.core.product.take 256) (bodySwap L ext (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) c)))⊆wires (LowZero18Square.withLowK2 L ext c L.core.high (L.core.product.take 256) (bodySwap L ext (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) c))) := by
 have he : ExtOK L c ext := ⟨hx,hdx,hext⟩
 have nd:=(List.nodup_cons.mp hn).2
 let v:=L.core.high.headD 0
 have vy : v∈L.core.y:=ParkCarry10Develop.source0_in_y L hw
 have vl : v∈L.wires := by
  simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,vy]
 have away : ∀q∈ext,q∉L.wires := fun q h hl=>he.away q h (List.mem_cons_of_mem c hl)
 have fixS:=ParkCarryDevelop.fold_fixes_sumCarry L hw nd ext he.len away
 have fixV:=ParkCarry10Develop.fold_fixes_source L hw nd ext he.len away
 have fixOld:=ParkCarry8Develop.fold_fixes_source L hw nd ext he.len away
 have retMem : sqRet L∈L.foldPad:=DiagSq.getD_in _ 239 (by rw [R2SqEp760.foldPad_length L hw];omega)
 have nret : v≠sqRet L := by
  intro e
  have yp:=List.count_pos_iff.mpr vy
  have fp:=List.count_pos_iff.mpr retMem
  rw [←e] at fp
  have ct:=ControlLoan1589BFFold.layoutCount L nd v
  omega
 have nhost : v≠sqHost ext := by
  intro e
  have hm:=sqHost_in ext he.len
  apply away _ hm
  rw [←e]
  exact vl
 have sw : sqSwap L ext v=v:=Equiv.swap_apply_of_ne_of_ne nret nhost
 have hosted :
  wires (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) c)⊆
  insert v (wires (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) c)) := by
  rw [ParkCarry10Develop.hosted_eq L _ c fixS,ParkCarry8Develop.hosted_eq L _ c fixS fixOld]
  exact Carry10BodyRefined.body_refined L hw c
 have swapSub:=rename_insert (sqSwap L ext)
  (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) c)
  (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) c) v hosted
 rw [sw] at swapSub
 change wires (bodySwap L ext (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) c))⊆
  insert v (wires (bodySwap L ext (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) c))) at swapSub
 have total:=program_insert L ext c L.core.high (L.core.product.take 256) _ _ v swapSub
 rw [show LowZero18Square.foldPerm L ext v=v from fixV] at total
 have mem : v∈wires (LowZero18Square.withLowK2 L ext c L.core.high (L.core.product.take 256) (bodySwap L ext (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) c))) := by
  have srcMem : v∈L.core.high:=CarryWindowCache.head_mem _ (by rw [L.core.high_length hw.core];decide)
  have nonempty : L.core.high.isEmpty=false := by
   rw [List.isEmpty_eq_false_iff]
   intro e
   have h:=L.core.high_length hw.core
   rw [e] at h
   contradiction
  have len : L.core.high.length=(L.inputBank.take L.core.high.length).length := by
   simp [L.core.high_length hw.core,(L.measured_bank_widths hw).1]
  have cp : v∈wires (copyRegister (some c) L.core.high (L.inputBank.take L.core.high.length)) := by
   rw [copyRegister_wires _ _ _ len]
   simp [nonempty,srcMem]
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union]
  tauto
 change wires (LowZero18Square.withLowK2 L ext c L.core.high (L.core.product.take 256) (bodySwap L ext (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) c)))⊆insert v (wires (LowZero18Square.withLowK2 L ext c L.core.high (L.core.product.take 256) (bodySwap L ext (ParkCarry8Develop.hostedBody L (LowZero18Square.foldPerm L ext) c)))) at total
 intro q h
 rcases Finset.mem_insert.mp (total h) with e|h
 · subst q;exact mem
 · exact h


include hw hn hx hdx hext in
theorem core760_ins : wires (core760 L ext control)⊆
    insert (sqHost ext) (wires (ReflectionE1Low48Square.core L ext control)) ∪ (ParkCopy.supportHosts ext).toFinset := by
  have nd := (List.nodup_cons.mp hn).2
  have aNew := withLowK2_ins L hw control ext hx hdx hext L.core.low (L.core.product.take 256) _
    (FullASelectedDevelop.hostedASelected_fold_support L hw nd ext control hext (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h)))
  have aSub : wires (LowZero18Square.withLowK2 L ext control L.core.low (L.core.product.take 256)
      (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control)) ⊆
      wires (LowZero18Square.withLowK2 L ext control L.core.low (L.core.product.take 256)
      (InverseCarryDevelop.hostedADual L (LowZero18Square.foldPerm L ext) control)) := by
    have sub := (FullASelectedDevelop.hostedASelected_subset L hw (LowZero18Square.foldPerm L ext) control).trans (ThirdSavedCarryDevelop.hostedATriple_subset L hw (LowZero18Square.foldPerm L ext) control)
    have ren : wires (renameProgram (LowZero18Square.foldPerm L ext)
        (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control)) ⊆
        wires (renameProgram (LowZero18Square.foldPerm L ext)
        (InverseCarryDevelop.hostedADual L (LowZero18Square.foldPerm L ext) control)) := by
      rw [renameProgram_support,renameProgram_support]
      exact Finset.image_mono _ sub
    intro q h
    have leaf : q∈wires (renameProgram (LowZero18Square.foldPerm L ext)
        (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control)) →
        q∈wires (renameProgram (LowZero18Square.foldPerm L ext)
        (InverseCarryDevelop.hostedADual L (LowZero18Square.foldPerm L ext) control)) := fun h=>ren h
    simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union] at h ⊢
    tauto
  have a := aNew.trans (Finset.insert_subset_insert (sqHost ext) aSub)
  have bOld := withLowK2_ins L hw control ext hx hdx hext L.core.high (L.core.product.take 256) _
    (ParkCarry8Develop.hosted_fold_support L hw nd ext control hext (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h)))
  have b := fun {q : Wire} (h : q∈wires (LowZero18Square.withLowK2 L ext control L.core.high (L.core.product.take 256)
      (bodySwap L ext (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) control)))) =>
    bOld (carry10_low_subset L hw ext control hn hx hdx hext h)
  have c := withLowK2_ins L hw control ext hx hdx hext L.core.sum L.core.product _
    (OwnDiagAll12Square.bodyCK_supportTq L hw nd control)
  have pc := withLowK2S_support L hw ext control L.core.sum L.core.product
    (bodySwap L ext (OwnDiagAll12Square.bodyCKTq L control)) (L.core.sum_length hw.core)
  have sMem : ∀q∈ParkCopyS.hostsS ext,q∈ParkCopy.supportHosts ext := by
    intro q h
    simp only [ParkCopyS.hostsS,ParkCopyS.hostIdxS,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,
      or_false] at h
    apply List.mem_append_left
    simp only [ParkCopy.hosts,ParkCopy.hostIdx,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
    rcases h with rfl|rfl|rfl|rfl|rfl <;> simp
  have pa := withLowK2P10_support L hw ext control L.core.low (L.core.product.take 256)
    (bodySwap L ext (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control)) (ControlLoan1589BFFold.eU L) (L.core.low_length hw.core)
  have pb := withLowK2P_support L hw ext control L.core.high (L.core.product.take 256)
    (bodySwap L ext (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) control)) (L.core.high_length hw.core)
  have euBF := eU_mem_oldBF L hw nd ext hext
    (fun q hq h=>hdx q hq (List.mem_cons_of_mem control h)) control
  have euCore : ControlLoan1589BFFold.eU L∈wires (ReflectionE1Low48Square.core L ext control) := by
    simp only [ReflectionE1Low48Square.core,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr euBF)
  intro q hq
  simp only [core760,branchCK760,branchBF760,branchAF760,wires_append,Finset.mem_union] at hq
  simp only [ReflectionE1Low48Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,wires_append,Finset.mem_union,Finset.mem_insert]
  rcases hq with (((h|h)|h)|h)|h
  · tauto
  · rcases Finset.mem_union.mp (pc h) with h'|h'
    · rcases Finset.mem_insert.mp (c h') with e|e <;> tauto
    · exact Or.inr (List.mem_toFinset.mpr (sMem q (List.mem_toFinset.mp h')))
  · tauto
  · rcases Finset.mem_union.mp (pb h) with h'|h'
    · rcases Finset.mem_insert.mp (b h') with e|e <;> tauto
    · exact Or.inr h'
  · rcases Finset.mem_union.mp (pa h) with h'|h'
    · rcases Finset.mem_insert.mp (a h') with e|e <;> tauto
    · have hh := List.mem_toFinset.mp h'
      rcases List.mem_append.mp hh with hh|hh
      · rcases List.mem_append.mp hh with hh|hh
        · exact Or.inr (List.mem_toFinset.mpr (List.mem_append_left _ hh))
        · have eq : q=ControlLoan1589BFFold.eU L := List.mem_singleton.mp hh
          have ec : q∈wires (ReflectionE1Low48Square.core L ext control) := by rw [eq];exact euCore
          have ee : q∈insert (sqHost ext) (wires (ReflectionE1Low48Square.core L ext control)) := Finset.mem_insert_of_mem ec
          simp only [ReflectionE1Low48Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
            LowZero18Square.branchAF,wires_append,Finset.mem_union,Finset.mem_insert] at ee
          exact Or.inl ee
      · exact Or.inr (List.mem_toFinset.mpr (List.mem_append_right _ hh))

end SupportNew

/-- The square's host sites: 1363 (the 760 body host) and the five parking hosts. -/
def sqSites (L : ControlledPointLayout) : Finset Wire :=
  {L.core.poolWire 1362,L.core.poolWire 1363,L.core.poolWire 1364,L.core.poolWire 1430,L.core.poolWire 1464,
    L.core.poolWire 1533,L.core.poolWire 1534,L.core.poolWire 1535,L.core.poolWire 1431,L.core.poolWire 1432,L.core.poolWire 1466,L.core.poolWire 1365,L.core.poolWire 1465}

theorem hosts_pool (L : ControlledPointLayout) :
    ParkCopy.supportHosts (OwnDiagAll12Square.kext L)=
      [L.core.poolWire 1362,L.core.poolWire 1364,L.core.poolWire 1365,L.core.poolWire 1430,L.core.poolWire 1464,L.core.poolWire 1465,L.core.poolWire 1533,L.core.poolWire 1534,L.core.poolWire 1535,L.core.poolWire 1431,L.core.poolWire 1432,L.core.poolWire 1466] := by
  simp [ParkCopy.supportHosts,ParkCopy.hosts,ParkCopy.hostIdx,OwnDiagAll12Square.kext,wireBlock]

section SupportPlaced
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw hn in
theorem place_ins (P Q : Program) (sub : wires P⊆insert (L.core.poolWire 1363) (wires Q)) :
    wires (SquareCarryLoan719BF.place L P)⊆insert (L.core.poolWire 1363) (wires (SquareCarryLoan719BF.place L Q)) := by
  have kb : 1363<2613 := by omega
  have blockFix : Square5Placement.blockPerm L 202 (L.core.poolWire 1363)=L.core.poolWire 1363 := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) 1363 kb]; rfl
  have f (a b : Nat) (ha : a<2613) (hb : b<2613) (na : 1363≠a) (nb : 1363≠b) :=
    pool_fix L hw hn 1363 a b kb ha hb na nb
  simp only [SquareCarryLoan719BF.place]
  apply rename_ins _ _ _ _ _ (f 718 907 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 768 775 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 769 1539 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 1286 1538 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 1285 1537 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 770 1536 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 767 1532 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 765 1531 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 766 1530 (by omega) (by omega) (by omega) (by omega))
  exact rename_ins _ _ _ _ sub blockFix

include hw hn in
theorem place_ins_set (P Q : Program) (sub : wires P⊆sqSites L ∪ wires Q) :
    wires (SquareCarryLoan719BF.place L P)⊆sqSites L ∪ wires (SquareCarryLoan719BF.place L Q) := by
  have mem (h : Wire) (hh : h∈sqSites L) :
      ∃ k, (k=1362 ∨ k=1363 ∨ k=1364 ∨ k=1430 ∨ k=1464 ∨ k=1533 ∨ k=1534 ∨ k=1535 ∨ k=1431 ∨ k=1432 ∨ k=1466 ∨ k=1365 ∨ k=1465) ∧ h=L.core.poolWire k := by
    simp only [sqSites,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨1362,by omega,rfl⟩
    · exact ⟨1363,by omega,rfl⟩
    · exact ⟨1364,by omega,rfl⟩
    · exact ⟨1430,by omega,rfl⟩
    · exact ⟨1464,by omega,rfl⟩
    · exact ⟨1533,by omega,rfl⟩
    · exact ⟨1534,by omega,rfl⟩
    · exact ⟨1535,by omega,rfl⟩
    · exact ⟨1431,by omega,rfl⟩
    · exact ⟨1432,by omega,rfl⟩
    · exact ⟨1466,by omega,rfl⟩
    · exact ⟨1365,by omega,rfl⟩
    · exact ⟨1465,by omega,rfl⟩
  have blockFix : ∀ h∈sqSites L, Square5Placement.blockPerm L 202 h=h := by
    intro h hh
    obtain ⟨k,hk,rfl⟩ := mem h hh
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) k (by omega)]
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have f (a b : Nat) (ha : a<2613) (hb : b<2613)
      (na : a<1362 ∨ 1535<a ∨ (1365<a ∧ a<1430) ∨ (1432<a ∧ a<1464) ∨ (1466<a ∧ a<1533))
      (nb : b<1362 ∨ 1535<b ∨ (1365<b ∧ b<1430) ∨ (1432<b ∧ b<1464) ∨ (1466<b ∧ b<1533)) :
      ∀ h∈sqSites L, Equiv.swap (L.core.poolWire a) (L.core.poolWire b) h=h := by
    intro h hh
    obtain ⟨k,hk,rfl⟩ := mem h hh
    exact pool_fix L hw hn k a b (by omega) ha hb (by omega) (by omega)
  simp only [SquareCarryLoan719BF.place]
  apply rename_ins_set _ _ _ _ _ (f 718 907 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins_set _ _ _ _ _ (f 768 775 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins_set _ _ _ _ _ (f 769 1539 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins_set _ _ _ _ _ (f 1286 1538 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins_set _ _ _ _ _ (f 1285 1537 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins_set _ _ _ _ _ (f 770 1536 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins_set _ _ _ _ _ (f 767 1532 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins_set _ _ _ _ _ (f 765 1531 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins_set _ _ _ _ _ (f 766 1530 (by omega) (by omega) (by omega) (by omega))
  exact rename_ins_set _ _ _ _ sub blockFix

include hw hn in
/-- New square support: the old square's support with site 760 replaced by the host sites. -/
theorem program760_support_subset :
    wires (program760 L)⊆sqSites L ∪ ((wires (ReflectionE1Low48Square.program L)).erase (L.core.poolWire 760)) := by
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have core := core760_ins L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic controlND (OwnDiagAll12Square.kext L) he.nodup he.away he.len
  rw [sqHost_pool1363 L,hosts_pool L] at core
  have core' : wires (fastCore760 L)⊆sqSites L ∪ wires (ReflectionE1Low48Square.fastCore L) := by
    intro q hq
    rcases Finset.mem_union.mp (core hq) with h|h
    · rcases Finset.mem_insert.mp h with e|e
      · exact Finset.mem_union_left _ (by simp [sqSites,e])
      · exact Finset.mem_union_right _ e
    · apply Finset.mem_union_left
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp only [sqSites,Finset.mem_insert,Finset.mem_singleton,eq_self_iff_true,true_or,or_true]
  have placed := place_ins_set L hw hn _ _ core'
  have free := square760_free L hw hn
  intro q hq
  rcases Finset.mem_union.mp (placed hq) with e|e
  · exact Finset.mem_union_left _ e
  · apply Finset.mem_union_right
    exact Finset.mem_erase.mpr ⟨fun h => free (h ▸ hq),e⟩

include hw hn in
theorem program760_support : wires (program760 L)⊆(OB5Support.sites L).toFinset := by
  have old := ReflectionE1Low48Square.support L hw hn
  intro q hq
  rcases Finset.mem_union.mp (program760_support_subset L hw hn hq) with e|e
  · simp only [sqSites,Finset.mem_insert,Finset.mem_singleton] at e
    rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1362,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1363,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1364,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1430,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1464,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1533,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1534,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1535,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1431,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1432,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1466,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1365,⟨by omega,by omega⟩,rfl⟩)))))
    · simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1465,⟨by omega,by omega⟩,rfl⟩)))))
  · exact old (Finset.mem_of_mem_erase e)

include hw hn in
theorem program760_free_old (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program760 L) := by
  intro used
  have ib : i<2613 := by simp at hi; omega
  rcases Finset.mem_union.mp (program760_support_subset L hw hn used) with e|e
  · simp only [sqSites,Finset.mem_insert,Finset.mem_singleton] at e
    rcases e with e|e|e|e|e|e|e|e|e|e|e|e|e <;>
      (have := pool_inj L hw hn i _ ib (by omega) e
       subst this; simp at hi)
  · exact ReflectionE1Low48Square.free L hw hn i hi (Finset.mem_of_mem_erase e)

end SupportPlaced

/-! ## Square: the host is clean when the body starts -/

theorem top_bits_zero (r : List Wire) (st : BasisState) (k : Nat) (h : regValue r st<2^k)
    (q : Wire) (hq : q∈r.drop k) : st q=false := by
  by_cases hk : k≤r.length
  · have e := regValue_append (r.take k) (r.drop k) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left hk] at e
    have z : regValue (r.drop k) st=0 := by
      by_contra nz
      have : 2^k≤2^k*regValue (r.drop k) st := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero nz)
      omega
    exact (regValue_zero _ _).mp z q hq
  · rw [List.drop_eq_nil_of_le (by omega)] at hq
    simp at hq

theorem host_not_drop (ext : List Wire) (hx : ext.Nodup) (hext : 300≤ext.length) (k : Nat) (hk : 131≤k) :
    sqHost ext∉ext.drop k := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_drop,sqHost,List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  omega

theorem host_not_take (ext : List Wire) (hx : ext.Nodup) (hext : 300≤ext.length) :
    sqHost ext∉ext.take 130 := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_take,sqHost,List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  simp at hi
  omega

                                                                                                   
                    
                                                                                   
             
                              

/-- After copy/make/erase the body host is zero: for 128-bit sources it is outside every kernel
register; for the 129-bit sum it is bit 130 of `T = 2·lo·hi < 2^130`. -/
theorem prefix_host_zero (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (s : State) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (r1 r2 r3 : List Bool) :
    (run (eraseMask control src (L.inputBank.take src.length)) r3
      (run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2
        (run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s))).basis (sqHost ext)=false := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have hostE := sqHost_in ext he
  -- erase does not touch the host
  have eraseOff : sqHost ext∉wires (eraseMask control src (L.inputBank.take src.length)) := by
    intro used
    have h := List.mem_toFinset.mp (eraseMask_wires_subset control src (L.inputBank.take src.length) used)
    rcases List.mem_cons.mp h with h|h
    · exact hdx _ hostE (by simp [h])
    · rcases List.mem_append.mp h with h|h
      · exact extSrc _ hostE h
      · exact extB _ hostE h
  rw [run_preserves_outside _ _ _ _ eraseOff]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := LowZero18Square.make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  rw [mkEq]
  rw [hKR] at mk
  by_cases h : src.length=128
  · -- the host lies in no kernel register
    have notT : sqHost ext∉(LowZero18LowK.oregs L ext src dst).T := by
      intro m
      have m' : sqHost ext∈(ext.take 132).take 130 := by
        simpa [LowZero18LowK.oregs,h] using m
      rw [List.take_take] at m'
      exact host_not_take ext hx he (by simpa using m')
    have notX : sqHost ext∉(LowZero18LowK.kg L ext src dst).X := by
      intro m
      rw [LowZero18LowK.kg,if_pos h] at m
      simp only [LowZero18LowK.kgH,KG.X,LowZero18LowK.iregs,LowZero18LowK.jregsH,List.mem_append,
        List.not_mem_nil,or_false] at m
      rcases m with ((m|m)|(m|m))
      · exact tmpE _ (List.mem_of_mem_drop (List.mem_of_mem_take m)) hostE
      · exact host_not_drop ext hx he 132 (by omega) (List.mem_of_mem_take m)
      · exact host_not_drop ext hx he 198 (by omega) (List.mem_of_mem_take (List.mem_of_mem_take m))
      · exact host_not_drop ext hx he 232 (by omega) (List.mem_of_mem_take m)
    have notD : sqHost ext∉(LowZero18LowK.oregs L ext src dst).dst := fun m =>
      (dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega) : ∀q∈ext,q∉dst) _ hostE m
    rw [mk.2.2.2.2.2.2.2 _ notD notT notX,u0s _ (extB _ hostE)]
    exact ext0 _ hostE
  · -- the host is bit 130 of T = 2·lo·hi < 2^130
    have h129 : src.length=129 := by omega
    have tv := mk.2.2.2.1
    have lo_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
    have hi_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
    have lol : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
      simp [LowZero18LowK.oregs,KRegs.lo,sizes.1,h129]
    have hil : (LowZero18LowK.oregs L ext src dst).hi.length=65 := by
      simp [LowZero18LowK.oregs,KRegs.hi,sizes.1,h129]
    rw [lol] at lo_lt
    rw [hil] at hi_lt
    have prod : 2*regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis*
        regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^130 := by
      have := Nat.mul_lt_mul'' lo_lt hi_lt
      have e : (2:Nat)^130=2*(2^64*2^65) := by norm_num
      rw [e,Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left this (by norm_num)
    rw [← tv] at prod
    apply top_bits_zero _ _ 130 prod
    have tl : (LowZero18LowK.oregs L ext src dst).T=ext.take 132 := by
      simp [LowZero18LowK.oregs,h129]
    rw [tl,sqHost,List.getD_eq_getElem _ _ (by omega)]
    have : ext[130]'(by omega)=((ext.take 132).drop 130)[0]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _

/-! ## Square: run equality -/

theorem mid_swap (Pre X Post : Program) (a b : Wire) (s : State) (m : List Bool)
    (ua : (run Pre (m.take (measurementCount Pre)) s).basis a=false)
    (ub : (run Pre (m.take (measurementCount Pre)) s).basis b=false)
    (bX : b∉wires X) (aPost : a∉wires Post)
    (fin : (run (Pre++X++Post) m s).basis a=false) :
    run (Pre++renameProgram (Equiv.swap a b) X++Post) m s=run (Pre++X++Post) m s := by
  have mc := (renameProgram_counts (Equiv.swap a b) X).2
  simp only [run_append,measurementCount_append,mc] at fin ⊢
  have e : List.take (measurementCount Pre) (List.take (measurementCount Pre+measurementCount X) m)=
      List.take (measurementCount Pre) m := by rw [List.take_take]; congr 1; omega
  simp only [e] at fin ⊢
  generalize run Pre (List.take (measurementCount Pre) m) s=u at ua ub fin ⊢
  rw [run_preserves_outside Post _ _ a aPost] at fin
  congr 1
  exact swap_run_eq a b X u _ ua ub fin ((run_preserves_outside X _ u b bX).trans ub)

theorem swaps_commute (a b c d : Wire) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (P : Program) :
    renameProgram (Equiv.swap c d) (renameProgram (Equiv.swap a b) P)=
      renameProgram (Equiv.swap a b) (renameProgram (Equiv.swap c d) P) := by
  rw [renameProgram_comp,renameProgram_comp]
  congr 1
  funext x
  simp only [Function.comp,Equiv.swap_apply_def]
  split_ifs <;> simp_all

                                                                                   
                                                                          
                                                               
                                                
                                                                                     
                                                                                              
                                                            
                                                          
                                                                  
                                                                                                 
                                                                                 
                                                                       
                                                                    
                                                                                        
                                                                       
                                                         
                                                                                       
                                                     
                                     
                                                                                  
                                                                                                                   
                                                            
                                             
                                                                            
                                                                                                                
                                                                             
                                       
                                                                                                                 
                                                              
                                                                          
                                                                    
                                                                               
                                                                                                                              
              
                                                                    
                
            
                                       
                                                        
                                    
                                                                                      
                                         
                                                         
                                   
                                           
                                       
                                                                   
                                                                                    
                                                                  
                            
                                                                                                        

theorem run3 (A W C : Program) (s : State) (m : List Bool) :
    run (A++W++C) m s=run C (m.drop (measurementCount A+measurementCount W))
      (run W ((m.drop (measurementCount A)).take (measurementCount W)) (run A (m.take (measurementCount A)) s)) := by
  simp only [run_append,measurementCount_append]
  have e1 : List.take (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=
      List.take (measurementCount A) m := by rw [List.take_take]; congr 1; omega
  have e2 : List.drop (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=
      List.take (measurementCount W) (List.drop (measurementCount A) m) := by
    rw [List.drop_take]; congr 1; omega
  rw [e1,e2]

                                                                                                  
                                         
                                                                                          
                                                                                
                                                                                                     

theorem withLowK2P_swap_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0)
    (fin : (run (ParkCopy.withLowK2P L ext control src dst B) m s).basis (sqRet L)=false) :
    run (ParkCopy.withLowK2P L ext control src dst (bodySwap L ext B)) m s=
      run (ParkCopy.withLowK2P L ext control src dst B) m s := by
  have masks := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have kern := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen he
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have rt := ne _ (target_outer L hw control ext src dst)
  have r0 := ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))
  have ht := sqHost_ne_target L hw control ext hdx he
  have h0 := sqHost_ne_ext0 ext hx he
  have pf := park_pieces_free L hw control hn ext hx hdx he src dst hs hd h128 hlen
  have com : renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)=
      renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
    rw [SquareCarryLoan719.foldPerm_eq L hw,bodySwap,sqSwap]
    exact swaps_commute _ _ _ _ rt r0 ht h0 B
  let Pre := ParkCopy.pA L control src++ParkCopy.pM L ext src dst++ParkCopy.pE1 L control src++
    ParkCopy.pD ext++ParkCopy.pMI L ext src
  let Post := ParkCopy.pC1 L ext control src dst++ParkCopy.pMO L ext src++ParkCopy.pCL L ext src dst++
    ParkCopy.pE L control src
  have s0 : ParkCopy.withLowK2P L ext control src dst B=
      Pre++renameProgram (SquareCarryLoan719.foldPerm L ext) B++Post := by
    simp only [ParkCopy.withLowK2P,ParkCopy.pB,LowZero18Square.foldPerm,Pre,Post,
      List.append_assoc]
  have s1 : ParkCopy.withLowK2P L ext control src dst (bodySwap L ext B)=
      Pre++renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B)++Post := by
    rw [← com]
    simp only [ParkCopy.withLowK2P,ParkCopy.pB,LowZero18Square.foldPerm,Pre,Post,
      List.append_assoc]
  rw [s0] at fin
  rw [s1,s0]
  have retPre : sqRet L∉wires Pre := by
    simp only [Pre,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨⟨⟨masks.1,kern.1⟩,pf.1⟩,pf.2.1⟩,pf.2.2.1⟩
  have retPost : sqRet L∉wires Post := by
    simp only [Post,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨⟨pf.2.2.2.1,pf.2.2.2.2.1⟩,kern.2⟩,masks.2⟩
  have retS : s.basis (sqRet L)=false := by
    apply (regValue_zero _ _).mp hc.pad
    exact DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega)
  have pre0 : ∀ r1 r2, (run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2
      (run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s)).basis (sqHost ext)=false := by
    intro r1 r2
    have q := prefix_host_zero L hw control hn src dst hs hd h128 hsmax hlen ext hx hdx he s hc hzero hz r1 r2 []
    rwa [run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.2.2] at q
  have ub : (run Pre (m.take (measurementCount Pre)) s).basis (sqHost ext)=false := by
    simp only [Pre,run_append]
    rw [run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.2.1,run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.1,
      run_preserves_outside _ _ _ _ pf.2.2.2.2.2.1]
    exact pre0 _ _
  exact mid_swap _ _ _ _ _ s m ((run_preserves_outside _ _ _ _ retPre).trans retS) ub
    (sqHost_fold_free L hw control ext hx hdx he B hb) retPost fin

theorem withLowK2P10_swap_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset)
    (g : Wire) (hgR : sqRet L≠g) (hgH : sqHost ext≠g) (hgB : g∉L.inputBank.take src.length)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0)
    (fin : (run (ParkCopy10.withLowK2P10 L ext control src dst B g) m s).basis (sqRet L)=false) :
    run (ParkCopy10.withLowK2P10 L ext control src dst (bodySwap L ext B) g) m s=
      run (ParkCopy10.withLowK2P10 L ext control src dst B g) m s := by
  have masks := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have kern := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen he
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have rt := ne _ (target_outer L hw control ext src dst)
  have r0 := ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))
  have ht := sqHost_ne_target L hw control ext hdx he
  have h0 := sqHost_ne_ext0 ext hx he
  have pf := park_pieces_free10 L hw control hn ext hx hdx he g src dst hs hd h128 hlen hgR hgH hgB
  have com : renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)=
      renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
    rw [SquareCarryLoan719.foldPerm_eq L hw,bodySwap,sqSwap]
    exact swaps_commute _ _ _ _ rt r0 ht h0 B
  let Pre := ParkCopy10.pA L control src++ParkCopy10.pM L ext src dst++ParkCopy10.pE1 L control src++
    ParkCopy10.pD ext g++ParkCopy10.pMI L ext src g
  let Post := ParkCopy10.pC1 L ext control src dst++ParkCopy10.pMO L ext src g++ParkCopy10.pCL L ext src dst++
    ParkCopy10.pE L control src
  have s0 : ParkCopy10.withLowK2P10 L ext control src dst B g=
      Pre++renameProgram (SquareCarryLoan719.foldPerm L ext) B++Post := by
    simp only [ParkCopy10.withLowK2P10,ParkCopy10.pB,LowZero18Square.foldPerm,Pre,Post,
      List.append_assoc]
  have s1 : ParkCopy10.withLowK2P10 L ext control src dst (bodySwap L ext B) g=
      Pre++renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B)++Post := by
    rw [← com]
    simp only [ParkCopy10.withLowK2P10,ParkCopy10.pB,LowZero18Square.foldPerm,Pre,Post,
      List.append_assoc]
  rw [s0] at fin
  rw [s1,s0]
  have retPre : sqRet L∉wires Pre := by
    simp only [Pre,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨⟨⟨masks.1,kern.1⟩,pf.1⟩,pf.2.1⟩,pf.2.2.1⟩
  have retPost : sqRet L∉wires Post := by
    simp only [Post,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨⟨pf.2.2.2.1,pf.2.2.2.2.1⟩,kern.2⟩,masks.2⟩
  have retS : s.basis (sqRet L)=false := by
    apply (regValue_zero _ _).mp hc.pad
    exact DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega)
  have pre0 : ∀ r1 r2, (run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2
      (run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s)).basis (sqHost ext)=false := by
    intro r1 r2
    have q := prefix_host_zero L hw control hn src dst hs hd h128 hsmax hlen ext hx hdx he s hc hzero hz r1 r2 []
    rwa [run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.2.2] at q
  have ub : (run Pre (m.take (measurementCount Pre)) s).basis (sqHost ext)=false := by
    simp only [Pre,run_append]
    rw [run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.2.1,run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.1,
      run_preserves_outside _ _ _ _ pf.2.2.2.2.2.1]
    exact pre0 _ _
  exact mid_swap _ _ _ _ _ s m ((run_preserves_outside _ _ _ _ retPre).trans retS) ub
    (sqHost_fold_free L hw control ext hx hdx he B hb) retPost fin

theorem withLowK2S_swap_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0)
    (fin : (run (ParkCopyS.withLowK2S L ext control src dst B) m s).basis (sqRet L)=false) :
    run (ParkCopyS.withLowK2S L ext control src dst (bodySwap L ext B)) m s=
      run (ParkCopyS.withLowK2S L ext control src dst B) m s := by
  have masks := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have kern := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen he
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have rt := ne _ (target_outer L hw control ext src dst)
  have r0 := ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))
  have ht := sqHost_ne_target L hw control ext hdx he
  have h0 := sqHost_ne_ext0 ext hx he
  have pf := park_pieces_freeS L hw control hn ext hx hdx he src dst hs hd h128 hlen
  have com : renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)=
      renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
    rw [SquareCarryLoan719.foldPerm_eq L hw,bodySwap,sqSwap]
    exact swaps_commute _ _ _ _ rt r0 ht h0 B
  let Pre := ParkCopyS.pA L control src++ParkCopyS.pM L ext src dst++ParkCopyS.pE1 L control src++
    ParkCopyS.pD ext++ParkCopyS.pMI L ext src
  let Post := ParkCopyS.pC1 L control src dst++ParkCopyS.pMO L ext src++ParkCopyS.pCL L ext src dst++
    ParkCopyS.pE L control src
  have s0 : ParkCopyS.withLowK2S L ext control src dst B=
      Pre++renameProgram (SquareCarryLoan719.foldPerm L ext) B++Post := by
    simp only [ParkCopyS.withLowK2S,ParkCopyS.pB,LowZero18Square.foldPerm,Pre,Post,
      List.append_assoc]
  have s1 : ParkCopyS.withLowK2S L ext control src dst (bodySwap L ext B)=
      Pre++renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B)++Post := by
    rw [← com]
    simp only [ParkCopyS.withLowK2S,ParkCopyS.pB,LowZero18Square.foldPerm,Pre,Post,
      List.append_assoc]
  rw [s0] at fin
  rw [s1,s0]
  have retPre : sqRet L∉wires Pre := by
    simp only [Pre,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨⟨⟨masks.1,kern.1⟩,pf.1⟩,pf.2.1⟩,pf.2.2.1⟩
  have retPost : sqRet L∉wires Post := by
    simp only [Post,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨⟨pf.2.2.2.1,pf.2.2.2.2.1⟩,kern.2⟩,masks.2⟩
  have retS : s.basis (sqRet L)=false := by
    apply (regValue_zero _ _).mp hc.pad
    exact DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega)
  have pre0 : ∀ r1 r2, (run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2
      (run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s)).basis (sqHost ext)=false := by
    intro r1 r2
    have q := prefix_host_zero L hw control hn src dst hs hd h128 hsmax hlen ext hx hdx he s hc hzero hz r1 r2 []
    rwa [run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.2.2] at q
  have ub : (run Pre (m.take (measurementCount Pre)) s).basis (sqHost ext)=false := by
    simp only [Pre,run_append]
    rw [run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.2.1,run_preserves_outside _ _ _ _ pf.2.2.2.2.2.2.1,
      run_preserves_outside _ _ _ _ pf.2.2.2.2.2.1]
    exact pre0 _ _
  exact mid_swap _ _ _ _ _ s m ((run_preserves_outside _ _ _ _ retPre).trans retS) ub
    (sqHost_fold_free L hw control ext hx hdx he B hb) retPost fin

theorem branchBFP_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum:s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256)
      (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) control)) records s).phase=s.phase ∧
    regValue L.core.out (run (ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256)
      (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) control)) records s).basis=
      ControlLoan1589BFFold.resBF ((if s.basis control then B else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256)
      (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) control)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  simp only [ParkCarry10Develop.hosted_eq L (LowZero18Square.foldPerm L ext) control
    (ParkCarryDevelop.fold_fixes_sumCarry L hw nd ext he.len (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h)))]
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (ParkCarry10Develop.body L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (ParkCarry10Develop.body_support L hw nd control hw'))
  apply ParkCopy.withLowK2P_correct L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) (L.core.high_length hw.core) ext he.nodup he.away he.len
    (ParkCarry10Develop.body L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [hb] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have sumProd:L.core.sumCarry∉L.core.product.take 256 := by
    intro h
    apply ParkCarryDevelop.sumCarry_away L nd
    simp [ParkCarryDevelop.restWires,List.mem_of_mem_take h]
  have hsumT:t.basis L.core.sumCarry=false := (same _ sumProd).trans hsum
  have sourceT:regValue L.core.high t.basis=B:=by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    apply same q
    intro bad
    have vy:q∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take hq)
    have yp:=List.count_pos_iff.mpr vy
    have pp:=List.count_pos_iff.mpr (List.mem_of_mem_take bad)
    have lc:=ControlLoan1589BFFold.layoutCount L nd q
    omega
  have hSource:M=if t.basis control then regValue L.core.high t.basis else 0:=by
    rw[sourceT,ctrlT]
  have frame := ParkCarry10Develop.body_frame L hw nd control hcw t.basis M mb full clean hsumT O hO hg hSource t m ⟨outO,fun _ _ => rfl⟩
  rw [ControlLoan1589BFFold.bO4_eq M O (t.basis control) mb hg hO,ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

                                                                               
                                                                                                             
                                                                          
                                                                                  
                                                                   
                                                                               
                                                                                
                                                                                                                   
                                                                                                    
                                                                                                          
                                                                                              
                                                                                                  
                                                                                                                           
                                      
                                                         
                                           
                                                                                                   
                                                                         
                                                                                           
                                                         
                                                                               
                                                                                        
                                                     
                                                                
                                                                                                
                                                                                               
                                                                                                                          
                                                                                                        
                                                                                                        
                                                                                                          
                                                                               
                                                                                                                 
                                                                                
                         
                     
                                                                   
                                                    
                                                                               
                                                                                                            
                                                                               
             
                                                                                         
                                              
                                                                       
                                                                     
                                                                                                          
                                                                       
                                             
                                        
                                                            
           
                                             
                                                            
                                                                         
                                                                                                                                            
                     
                                     

theorem eU_not_y (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    ControlLoan1589BFFold.eU L∉L.core.y := by
  intro h
  have c := List.nodup_iff_count_le_one.mp hn (ControlLoan1589BFFold.eU L)
  have hy := List.count_pos_iff.mpr h
  have hp := List.count_pos_iff.mpr (InverseCarryDevelop.eU_mem_product L hw)
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,
    List.count_cons] at c
  omega

/-- The A leaf with the five ext hosts plus `product[256]` (`eU`). -/
theorem branchAFP10_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum:s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (ParkCopy10.withLowK2P10 L ext control L.core.low (L.core.product.take 256)
      (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control) (ControlLoan1589BFFold.eU L)) records s).phase=s.phase ∧
    regValue L.core.out (run (ParkCopy10.withLowK2P10 L ext control L.core.low (L.core.product.take 256)
      (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control) (ControlLoan1589BFFold.eU L)) records s).basis=
      ControlLoan1589BFFold.resAF ((if s.basis control then A else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (ParkCopy10.withLowK2P10 L ext control L.core.low (L.core.product.take 256)
      (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control) (ControlLoan1589BFFold.eU L)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  simp only [FullASelectedDevelop.hostedASelected_eq L (LowZero18Square.foldPerm L ext) control
    (ParkCarryDevelop.fold_fixes_sumCarry L hw nd ext he.len
      (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h)))]
  have aSupport:=FullASelectedDevelop.aBodySelected_support L hw nd control
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (FullASelectedDevelop.aBodySelected L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (aSupport hw'))
  have eUw := InverseCarryDevelop.eU_mem_wires L hw
  have hgE : ControlLoan1589BFFold.eU L∉ext := fun h => he.away _ h (List.mem_cons_of_mem control eUw)
  have hgB : ControlLoan1589BFFold.eU L∉L.inputBank.take L.core.low.length := fun h =>
    InverseCarryDevelop.eU_off_aux L hw nd _ (by simp [List.mem_of_mem_take (List.mem_of_mem_take h)]) rfl
  have hgD : ControlLoan1589BFFold.eU L∉L.core.product.take 256 := InverseCarryDevelop.eU_not_low L hw nd
  have hgS : ControlLoan1589BFFold.eU L∉L.core.low := fun h => eU_not_y L hw nd (List.mem_of_mem_take h)
  have hgC : ControlLoan1589BFFold.eU L≠control := fun e => hcw (e ▸ eUw)
  have hgO : ControlLoan1589BFFold.eU L∉L.core.out := (ControlLoan1589BFFold.eReg_away L nd _ (ControlLoan1589BFFold.eK_mem L hw).2.1).1
  have hgK : ControlLoan1589BFFold.eU L∉LowZero18LowK.ktmp L := fun h =>
    InverseCarryDevelop.eU_off_aux L hw nd _ (by simp [List.mem_of_mem_drop h]) rfl
  have hgW : ControlLoan1589BFFold.eU L∉ECDSAAdd.wires (FullASelectedDevelop.aBodySelected L control) :=
    FullASelectedDevelop.eU_off_aBodySelected L hw nd control hcw
  have hg0 : s.basis (ControlLoan1589BFFold.eU L)=false :=
    (regValue_zero _ _).mp hp0 _ (InverseCarryDevelop.eU_mem_product L hw)
  apply ParkCopy10.withLowK2P10_correct L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) (L.core.low_length hw.core) ext he.nodup he.away he.len
    (FullASelectedDevelop.aBodySelected L control) hbody (ControlLoan1589BFFold.eU L) hgE hgB hgD hgS hgC hgO hgK hgW
    s records hc dstZero hz hg0
  intro t m dstValue same
  rw [ha] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have sumProd:L.core.sumCarry∉L.core.product.take 256 := by
    intro h;apply ParkCarryDevelop.sumCarry_away L nd
    simp [ParkCarryDevelop.restWires,List.mem_of_mem_take h]
  have hsumT:t.basis L.core.sumCarry=false := (same _ sumProd).trans hsum
  have frame := FullASelectedDevelop.aBodySelected_frame L hw nd control hcw t.basis M mb full clean hsumT O hO hg t m ⟨outO,fun _ _ => rfl⟩
  rw [ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩


section Branches
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire) (control : Wire)
  (hn : (control::L.wires).Nodup)

include hw in
theorem sqRet_not_out (hn' : L.wires.Nodup) : sqRet L∉L.core.out :=
  (L.pairAuxAway hn' (sqRet L) (by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega))))).2

include hw in
theorem sqRet_clean (st : BasisState) (hc : L.PairClean st) : st (sqRet L)=false :=
  (regValue_zero _ _).mp hc.pad _ (DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega))

include hw hn in
theorem branchBF760_run_eq (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum:s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchBF760 L ext control) records s=run (LowZero18Square.branchBF L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have newC := branchBFP_correct L hw ext control hn B O hO s records hb ho hp0 hc hsum he hz
  have oldC := LowZero18Square.branchBF_correct L hw ext control hn B O hO s records hb ho hp0 hc hsum he hz
  have fin := newC.2.2 (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at fin
  rw [show branchBF760 L ext control=ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256)
      (bodySwap L ext (ParkCarry10Develop.hostedBody L (LowZero18Square.foldPerm L ext) control)) from rfl,
    withLowK2P_swap_run_eq L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
      (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
      (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len _
      (ParkCarry10Develop.hosted_fold_support L hw nd ext control he.len
        (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h))) s records hc dstZero hz fin]
  exact park_state_eq L _ _ s newC.1 oldC.1 (newC.2.1.trans oldC.2.1.symm) newC.2.2 oldC.2.2

include hw hn in
theorem branchAF760_run_eq (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum:s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchAF760 L ext control) records s=run (LowZero18Square.branchAF L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have fU := eU_760_facts L hw control hn ext he.away he.len
  have newC := branchAFP10_correct L hw ext control hn A O hO s records ha ho hp0 hc hsum he hz
  have oldC := LowZero18Square.branchAF_correct L hw ext control hn A O hO s records ha ho hp0 hc hsum he hz
  have fin := newC.2.2 (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at fin
  rw [show branchAF760 L ext control=ParkCopy10.withLowK2P10 L ext control L.core.low (L.core.product.take 256)
      (bodySwap L ext (FullASelectedDevelop.hostedASelected L (LowZero18Square.foldPerm L ext) control)) (ControlLoan1589BFFold.eU L) from rfl,
    withLowK2P10_swap_run_eq L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
      (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
      (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len _
      (FullASelectedDevelop.hostedASelected_fold_support L hw nd ext control he.len (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h)))
      _ fU.1 fU.2.1 (fU.2.2.2 _) s records hc dstZero hz fin]
  exact park_state_eq L _ _ s newC.1 oldC.1 (newC.2.1.trans oldC.2.1.symm) newC.2.2 oldC.2.2

end Branches

theorem middleCKS_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (ParkCopyS.withLowK2S L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)) records s).phase=s.phase ∧
    regValue L.core.out (run (ParkCopyS.withLowK2S L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (ParkCopyS.withLowK2S L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (OwnDiagAll12Square.bodyCKTq L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (OwnDiagAll12Square.bodyCK_supportTq L hw nd control hw'))
  apply ParkCopyS.withLowK2S_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) (L.core.sum_length hw.core) ext he.nodup he.away he.len
    (OwnDiagAll12Square.bodyCKTq L control) hbody s records hc hp0 hz
  intro t m dstValue same
  have ctrlT : t.basis control=s.basis control :=
    same control (fun h => (List.nodup_cons.mp hn).1
      (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]))
  have pv : regValue L.core.product t.basis=M^2 := by simpa [M,hs] using dstValue
  have clean := L.measured_product_frame_clean nd L.core.product (fun _ => le_rfl) s.basis t.basis hc same
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q
      (fun hp => List.disjoint_left.mp (L.product_out_disjoint nd) hp hq))).trans ho
  have r := OwnDiagAll12Square.accMiddleCFK_bodyTq L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem branchCK760_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hsum : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchCK760 L ext control) records s=run (LowZero18Square.branchCK L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  let W := LowZero18Square.withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)
  let WS := ParkCopyS.withLowK2S L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)
  let W' := ParkCopyS.withLowK2S L ext control L.core.sum L.core.product
    (bodySwap L ext (OwnDiagAll12Square.bodyCKTq L control))
  let mp := measurementCount (OwnDiagAll12Square.gPrep L)
  let u := run (OwnDiagAll12Square.gPrep L) (records.take mp) s
  have prep := OwnDiagAll12Square.gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hsum,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (OwnDiagAll12Square.sum_in L control q bad)))).trans hz
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have key : ∀ m : List Bool, run W' m u=run W m u := by
    intro m
    have newC := middleCKS_correct L hw ext control hn (A+B) O hO u m prep.2.1 outU productU cleanU he hzU
    have oldC := LowZero18Square.middleCK_correct L hw ext control hn (A+B) O hO u m prep.2.1 outU productU cleanU he hzU
    have fin := newC.2.2 (sqRet L) (sqRet_not_out L hw nd)
    rw [sqRet_clean L hw _ cleanU] at fin
    have mid := withLowK2S_swap_run_eq L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
      (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
      (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len _
      (OwnDiagAll12Square.bodyCK_supportTq L hw nd control) u m cleanU productU hzU fin
    rw [show W'=ParkCopyS.withLowK2S L ext control L.core.sum L.core.product
      (bodySwap L ext (OwnDiagAll12Square.bodyCKTq L control)) from rfl,mid]
    exact park_state_eq L _ _ u newC.1 oldC.1 (newC.2.1.trans oldC.2.1.symm) newC.2.2 oldC.2.2
  have shapeOld : LowZero18Square.branchCK L ext control=OwnDiagAll12Square.gPrep L++W++OwnDiagAll12Square.gClear L := rfl
  have shapeNew : branchCK760 L ext control=OwnDiagAll12Square.gPrep L++W'++OwnDiagAll12Square.gClear L := rfl
  rw [shapeNew,shapeOld,run3,run3,withLowK2S_swap_mc L hw ext control _ _ _ (L.core.sum_length hw.core)]
  exact congrArg _ (key _)




































































section Final
open Secp256k1 CompressedPointDialog


























































































end Final

end ECDSAAdd.Entrant.R2SqEp760

end -- R2 square

-- ===== Exit-side merged tick (ExitMerge) in the multiplication kernel =====
section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed
section -- Scope the inlined inverse proof attributes

-- Verified Inverse14Physical
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ECDSAAdd.Entrant.Inverse14Width
open Arithmetic MappedCompressed Secp256k1 History5
def sites : List Wire := MorningFour.sites ++ [530]
def block0 : Program := [
 .X 527,
 .CX 526 527,
 .CX 526 786,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CCX 522 523 527,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 526 1551
]
def block1 : Program := [
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 524,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 528,
 .CX 522 524,
 .CX 524 522
]
def block2 : Program := [
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 525 524,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 524,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526
]
def block3 : Program := [
 .CX 524 526,
 .CX 524 523,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 523 522,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 522 524,
 .CCX 522 523 529,
 .CX 522 524,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 523 522,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 523,
 .CX 524 526,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 525 524,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551
]
def block4 : Program := [
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 528 1552,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1551 524,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 786
]
def block5 : Program := [
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 524,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1552 1553,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 528 1552,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552
]
def block6 : Program := [
 .CX 526 525,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 1551,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 787,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 525 1551,
 .CX 526 1551
]
def block7 : Program := [
 .CX 1551 526,
 .CX 526 1551,
 .CX 526 525,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 787 786,
 .CX 786 787,
 .CX 786 529,
 .CX 529 786,
 .CX 529 527,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 527 1553,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1551 525,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 526,
 .CX 525 524
]
def block8 : Program := [
 .CX 525 523,
 .CX 523 525,
 .CX 523 524,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 788,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 524,
 .CX 523 525,
 .CX 525 523,
 .CX 525 524,
 .CX 525 526,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 1551 525,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 527 1553,
 .CX 527 528,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529
]
def block9 : Program := [
 .CX 529 527,
 .CX 529 786,
 .CX 786 529,
 .CX 786 787,
 .CX 787 786,
 .CX 787 528,
 .CX 786 788,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 787,
 .CX 787 529,
 .CX 529 787,
 .CX 528 786,
 .CX 528 1553,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 529,
 .CX 529 527,
 .CX 527 529,
 .CX 1554 528,
 .CX 528 1554,
 .CX 1554 528,
 .CX 1553 527,
 .CX 1553 525,
 .CX 1552 1554,
 .CX 1554 1552,
 .CX 1552 1554,
 .CX 1551 1553,
 .CX 1553 1551,
 .CX 1551 1553
]
def block10 : Program := [
 .CX 526 1552,
 .CX 1552 526,
 .CX 526 1552,
 .CX 525 1551,
 .CX 525 526,
 .CX 526 525,
 .CX 525 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 526,
 .CX 526 523,
 .CX 523 526,
 .CX 522 525,
 .CX 525 522,
 .CX 522 525,
 .CCX 522 523 524,
 .CX 787 529,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 786,
 .CX 529 528,
 .CX 528 529,
 .CX 528 527,
 .CX 527 528,
 .CX 527 526,
 .CX 527 525,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1553 1554
]
def block11 : Program := [
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 526 525,
 .CX 526 524,
 .CX 525 1551,
 .CX 525 526,
 .CX 525 524,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 789,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525
]
def block12 : Program := [
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 525 524,
 .CX 525 526,
 .CX 525 1551,
 .CX 526 524,
 .CX 526 525,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 527 525,
 .CX 527 526,
 .CX 527 528,
 .CX 528 527,
 .CX 528 529,
 .CX 529 528,
 .CX 529 786,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 787 529
]
def block13 : Program := [
 .CX 787 529,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 786,
 .CX 529 1554,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 1554 527,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 526,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 526 524,
 .CX 525 522,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525
]
def block14 : Program := [
 .CX 522 524,
 .CCX 522 523 790,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 525 522,
 .CX 526 524,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 526,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 527,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 529 1554,
 .CX 529 786,
 .CX 786 787
]
def block15 : Program := [
 .CX 787 786,
 .CX 786 787,
 .CX 787 529,
 .CX 790 787,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 787 788,
 .CX 787 528,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 528 529,
 .CX 528 527,
 .CX 527 528,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1553 1551,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1551 526,
 .CX 1551 525
]
def block16 : Program := [
 .CX 525 1551,
 .CX 525 526,
 .CX 525 523,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 523 522,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 791,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 524,
 .CX 524 523,
 .CX 523 524,
 .CX 523 522,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 523,
 .CX 525 526,
 .CX 525 1551,
 .CX 1551 525
]
def block17 : Program := [
 .CX 1551 526,
 .CX 1551 1552,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 1551,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1554 527,
 .CX 527 1554,
 .CX 527 528,
 .CX 528 527,
 .CX 528 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 787 528,
 .CX 787 788,
 .CX 788 789,
 .CX 789 788,
 .CX 788 789,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 790 787,
 .CX 788 786,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788
]
def block18 : Program := [
 .CX 786 787,
 .CX 786 527,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1552,
 .CX 1554 1551,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 526,
 .CX 1551 1553,
 .CX 1551 522,
 .CX 526 1552,
 .CX 526 1551,
 .CX 526 524,
 .CX 526 522,
 .CX 525 1551,
 .CX 1551 525,
 .CX 525 1551,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523
]
def block19 : Program := [
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CCX 522 523 1556,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 525 1551,
 .CX 1551 525,
 .CX 525 1551,
 .CX 526 522,
 .CX 526 524,
 .CX 526 1551,
 .CX 526 1552,
 .CX 1551 522,
 .CX 1551 1553,
 .CX 1552 526,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 1551,
 .CX 1554 1552,
 .CX 1554 527,
 .CX 527 1554,
 .CX 527 528,
 .CX 528 529
]
def block20 : Program := [
 .CX 529 528,
 .CX 528 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 527,
 .CX 786 787,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 788 786,
 .CX 1556 788,
 .CX 791 1556,
 .CX 1556 791,
 .CX 791 1556,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 788 789,
 .CX 788 786,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 786 787,
 .CX 786 527,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 528 529
]
def block21 : Program := [
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1552,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1553,
 .CX 1552 526,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 526 1551,
 .CX 526 524,
 .CX 524 526,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CCX 522 523 1557,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523
]
def block22 : Program := [
 .CX 523 525,
 .CX 524 525,
 .CX 525 524,
 .CX 524 525,
 .CX 524 526,
 .CX 526 524,
 .CX 526 1551,
 .CX 1551 1552,
 .CX 1552 1551,
 .CX 1551 1552,
 .CX 1552 526,
 .CX 1552 1553,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 1552,
 .CX 1554 527,
 .CX 527 1554,
 .CX 527 528,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 527,
 .CX 786 787,
 .CX 787 788,
 .CX 788 787,
 .CX 787 788,
 .CX 788 786,
 .CX 788 789
]
def block23 : Program := [
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 791 1556,
 .CX 1556 791,
 .CX 791 1556,
 .CX 1556 788,
 .CX 786 1554,
 .CX 786 1552,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 1554 1553,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1553 527,
 .CX 1553 1554,
 .CX 1553 1552,
 .CX 1553 1551,
 .CX 1552 1554,
 .CX 1552 524,
 .CX 1551 1553
]
def block24 : Program := [
 .CX 1551 1552,
 .CX 1551 524,
 .CX 1551 523,
 .CX 526 1552,
 .CX 1552 526,
 .CX 526 1552,
 .CX 525 1551,
 .CX 1551 525,
 .CX 525 1551,
 .CX 524 526,
 .CX 524 522,
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 1558,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 524 522,
 .CX 524 526,
 .CX 525 1551,
 .CX 1551 525,
 .CX 525 1551,
 .CX 526 1552,
 .CX 1552 526,
 .CX 526 1552,
 .CX 1551 523,
 .CX 1551 524
]
def block25 : Program := [
 .CX 1551 1552,
 .CX 1551 1553,
 .CX 1552 524,
 .CX 1552 1554,
 .CX 1553 1551,
 .CX 1553 1552,
 .CX 1553 1554,
 .CX 1553 527,
 .CX 1554 527,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1553,
 .CX 527 528,
 .CX 528 527,
 .CX 527 528,
 .CX 528 529,
 .CX 529 528,
 .CX 528 529,
 .CX 529 786,
 .CX 786 529,
 .CX 529 786,
 .CX 786 1552,
 .CX 786 1554,
 .CX 1558 788,
 .CX 1557 1558,
 .CX 1558 1557,
 .CX 1557 1558,
 .CX 1556 1557,
 .CX 1557 1556,
 .CX 1556 1557,
 .CX 791 1556,
 .CX 1556 791
]
def block26 : Program := [
 .CX 791 1556,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 788 789,
 .CX 788 787,
 .CX 787 788,
 .CX 787 529,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 529 786,
 .CX 529 528,
 .CX 528 529,
 .CX 528 527,
 .CX 527 528,
 .CX 527 1554,
 .CX 1554 527,
 .CX 1554 1551,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 1552,
 .CX 1551 522,
 .CX 526 525,
 .CX 526 1551
]
def block27 : Program := [
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 1551,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 522 524,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CCX 522 523 530,
 .CX 522 523,
 .CX 523 522,
 .CX 522 523,
 .CX 522 524,
 .CX 523 525,
 .CX 525 523,
 .CX 523 525,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 525 1551,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 526 525,
 .CX 1551 522,
 .CX 1551 1552,
 .CX 1552 1553
]
def block28 : Program := [
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1553 1554,
 .CX 1554 1553,
 .CX 1553 1554,
 .CX 1554 1551,
 .CX 1554 527,
 .CX 527 1554,
 .CX 527 528,
 .CX 528 527,
 .CX 528 529,
 .CX 529 528,
 .CX 529 786,
 .CX 786 787,
 .CX 787 786,
 .CX 786 787,
 .CX 787 529,
 .CX 787 788,
 .CX 788 787,
 .CX 788 789,
 .CX 789 790,
 .CX 790 789,
 .CX 789 790,
 .CX 790 791,
 .CX 791 790,
 .CX 790 791,
 .CX 791 1556,
 .CX 1556 791,
 .CX 791 1556,
 .CX 1556 1557,
 .CX 1557 1556,
 .CX 1556 1557
]
def block29 : Program := [
 .CX 1557 1558,
 .CX 1558 1557,
 .CX 1557 1558,
 .CX 1558 788,
 .CX 530 1558,
 .CX 530 1556,
 .CX 530 788,
 .CX 1558 1556,
 .CX 1558 1554,
 .CX 1558 1553,
 .CX 1558 530,
 .CX 530 1558,
 .CX 1558 530,
 .CX 1557 1556,
 .CX 1557 791,
 .CX 1557 790,
 .CX 1557 787,
 .CX 1557 528,
 .CX 1557 1558,
 .CX 1558 1557,
 .CX 1557 1558,
 .CX 1556 530,
 .CX 1556 788,
 .CX 1556 527,
 .CX 1556 1553,
 .CX 1556 524,
 .CX 1556 1558,
 .CX 1558 1556,
 .CX 1556 1558,
 .CX 791 530,
 .CX 791 790,
 .CX 791 787
]
def block30 : Program := [
 .CX 791 528,
 .CX 791 1553,
 .CX 790 530,
 .CX 790 1558,
 .CX 790 527,
 .CX 790 1553,
 .CX 790 1551,
 .CX 790 524,
 .CX 790 1556,
 .CX 1556 790,
 .CX 790 1556,
 .CX 789 530,
 .CX 789 1558,
 .CX 789 1557,
 .CX 789 527,
 .CX 789 1553,
 .CX 789 524,
 .CX 789 522,
 .CX 789 1556,
 .CX 1556 789,
 .CX 789 1556,
 .CX 788 530,
 .CX 788 1558,
 .CX 788 786,
 .CX 788 527,
 .CX 788 1553,
 .CX 788 524,
 .CX 788 1557,
 .CX 1557 788,
 .CX 788 1557,
 .CX 787 530,
 .CX 787 528
]
def block31 : Program := [
 .CX 787 1553,
 .CX 787 523,
 .CX 787 791,
 .CX 791 787,
 .CX 787 791,
 .CX 786 1557,
 .CX 786 528,
 .CX 786 527,
 .CX 786 1556,
 .CX 1556 786,
 .CX 786 1556,
 .CX 529 1556,
 .CX 529 527,
 .CX 529 790,
 .CX 790 529,
 .CX 529 790,
 .CX 528 530,
 .CX 528 1556,
 .CX 528 527,
 .CX 528 1554,
 .CX 528 1553,
 .CX 528 790,
 .CX 790 528,
 .CX 528 790,
 .CX 527 1558,
 .CX 527 1554,
 .CX 527 1552,
 .CX 527 524,
 .CX 527 790,
 .CX 790 527,
 .CX 527 790,
 .CX 1554 530
]
def block32 : Program := [
 .CX 1554 1558,
 .CX 1554 1556,
 .CX 1554 791,
 .CX 1554 790,
 .CX 1554 786,
 .CX 1554 1553,
 .CX 1554 1552,
 .CX 1554 526,
 .CX 1554 524,
 .CX 1554 523,
 .CX 1554 522,
 .CX 1553 530,
 .CX 1553 787,
 .CX 1553 529,
 .CX 1553 528,
 .CX 528 1553,
 .CX 1553 528,
 .CX 1552 1558,
 .CX 1552 1556,
 .CX 1552 791,
 .CX 1552 790,
 .CX 1552 524,
 .CX 1552 523,
 .CX 1552 1553,
 .CX 1553 1552,
 .CX 1552 1553,
 .CX 1551 789,
 .CX 1551 788,
 .CX 1551 786,
 .CX 1551 528,
 .CX 1551 1553,
 .CX 1551 526
]
def block33 : Program := [
 .CX 1551 525,
 .CX 1551 522,
 .CX 526 786,
 .CX 526 527,
 .CX 526 1554,
 .CX 526 1553,
 .CX 526 522,
 .CX 526 1551,
 .CX 1551 526,
 .CX 526 1551,
 .CX 525 1558,
 .CX 525 1556,
 .CX 525 791,
 .CX 525 788,
 .CX 525 528,
 .CX 525 1554,
 .CX 525 1553,
 .CX 525 526,
 .CX 525 524,
 .CX 525 523,
 .CX 524 1558,
 .CX 524 1556,
 .CX 524 791,
 .CX 524 788,
 .CX 524 527,
 .CX 524 1553,
 .CX 524 1551,
 .CX 524 523,
 .CX 524 526,
 .CX 526 524,
 .CX 524 526,
 .CX 523 791
]
def block34 : Program := [
 .CX 523 787,
 .CX 523 1554,
 .CX 1554 523,
 .CX 523 1554,
 .CX 522 786,
 .CX 522 1553,
 .CX 522 526,
 .CX 522 525,
 .CX 522 524,
 .CX 524 522,
 .CX 522 524,
 .X 1551,
 .X 1553,
 .X 1554,
 .X 527,
 .measureX 530 [] [.Z 526, .Z 1553, .Z 527, .Z 786, .Z 788, .Z 790, .Z 791, .CZ 522 786, .CZ 522 787, .CZ 522 1558, .CZ 523 524, .CZ 523 525, .CZ 523 526, .CZ 523 1554, .CZ 523 789, .CZ 523 790, .CZ 523 1558, .CZ 524 786, .CZ 524 789, .CZ 1553 528, .CZ 1553 791, .CZ 1553 1558],
 .measureX 1558 [] [.Z 526, .Z 1551, .Z 1552, .Z 1553, .Z 1554, .Z 527, .Z 529, .Z 788, .Z 790, .Z 791, .Z 1556, .CZ 522 524, .CZ 522 1553, .CZ 522 1554, .CZ 522 791, .CZ 522 1556, .CZ 523 1554, .CZ 523 789, .CZ 523 1556, .CZ 524 525, .CZ 524 1553, .CZ 524 527, .CZ 524 528, .CZ 524 529, .CZ 524 786, .CZ 524 787, .CZ 524 789, .CZ 524 790, .CZ 524 791, .CZ 524 1556, .CZ 524 1557, .CZ 525 526, .CZ 525 1551, .CZ 525 786, .CZ 525 788, .CZ 525 1556, .CZ 526 528, .CZ 526 1556, .CZ 1551 1553, .CZ 1553 1554, .CZ 1553 528, .CZ 1553 791, .CZ 1553 1556, .CZ 1554 1556],
 .X 1557,
 .measureX 1557 [] [.Z 522, .Z 523, .Z 525, .Z 1551, .Z 1552, .Z 786, .Z 788, .Z 789, .Z 790, .CZ 522 523, .CZ 522 524, .CZ 522 526, .CZ 522 1554, .CZ 522 786, .CZ 522 788, .CZ 523 524, .CZ 523 526, .CZ 523 789, .CZ 523 790, .CZ 524 525, .CZ 524 526, .CZ 524 528, .CZ 524 529, .CZ 524 787, .CZ 524 789, .CZ 524 790, .CZ 525 526, .CZ 525 1553, .CZ 525 1554, .CZ 525 528, .CZ 525 786, .CZ 525 787, .CZ 525 788, .CZ 526 790, .CZ 1551 1553, .CZ 1551 1554, .CZ 1551 788],
 .X 1556,
 .measureX 1556 [] [.Z 523, .Z 526, .Z 1553, .Z 527, .Z 529, .Z 790, .CZ 522 523, .CZ 522 526, .CZ 522 1553, .CZ 522 527, .CZ 522 786, .CZ 522 787, .CZ 522 789, .CZ 522 790, .CZ 523 525, .CZ 523 1551, .CZ 523 1554, .CZ 523 790, .CZ 524 1553, .CZ 524 1554, .CZ 524 529, .CZ 524 789, .CZ 524 790, .CZ 525 1554, .CZ 525 527, .CZ 525 528, .CZ 525 790, .CZ 526 1553, .CZ 526 527, .CZ 526 528, .CZ 526 786, .CZ 526 788, .CZ 526 790, .CZ 1551 788, .CZ 1553 527, .CZ 1553 528, .CZ 1553 788],
 .measureX 791 [] [.Z 522, .Z 524, .Z 525, .Z 526, .Z 1553, .Z 1554, .Z 786, .Z 789, .Z 790, .CZ 522 524, .CZ 522 1553, .CZ 522 786, .CZ 522 787, .CZ 522 789, .CZ 523 524, .CZ 523 525, .CZ 523 526, .CZ 523 1551, .CZ 523 789, .CZ 523 790, .CZ 524 528, .CZ 524 529, .CZ 524 786, .CZ 525 528, .CZ 525 789],
 .X 790,
 .measureX 790 [] [.Z 522, .Z 525, .Z 1551, .Z 527, .Z 786, .Z 788, .CZ 522 524, .CZ 522 1554, .CZ 522 788, .CZ 523 525, .CZ 523 526, .CZ 523 1551, .CZ 524 1554, .CZ 524 528, .CZ 524 786, .CZ 524 788, .CZ 525 1551, .CZ 525 527, .CZ 525 528, .CZ 525 786, .CZ 525 787, .CZ 525 788, .CZ 526 1553, .CZ 526 527, .CZ 526 786, .CZ 526 788, .CZ 1551 1553, .CZ 1551 1554, .CZ 1551 786, .CZ 1551 788, .CZ 1553 1554, .CZ 1553 528, .CZ 1554 528],
 .measureX 789 [] [.Z 524, .Z 525, .Z 1553, .Z 786, .CZ 522 525, .CZ 522 1554, .CZ 524 525, .CZ 524 1551, .CZ 524 1553, .CZ 524 787, .CZ 525 786, .CZ 1553 1554, .CZ 1553 528, .CZ 1553 787, .CZ 1554 786],
 .measureX 788 [] [.Z 522, .Z 523, .Z 524, .Z 526, .CZ 523 524, .CZ 523 526, .CZ 523 1553, .CZ 523 527],
 .X 787,
 .measureX 787 [] [.Z 1554, .Z 528, .CZ 523 525, .CZ 523 1551, .CZ 523 1554, .CZ 523 528],
 .measureX 786 [] [.Z 522, .Z 523, .Z 524, .CZ 523 524, .CZ 523 1553],
 .CX 1551 527,
 .CX 527 1551,
 .CX 1551 527
]
def block35 : Program := [
 .CX 1552 528,
 .CX 528 1552,
 .CX 1552 528,
 .CX 1553 787,
 .CX 787 1553,
 .CX 1553 787,
 .CX 1554 788,
 .CX 788 1554,
 .CX 1554 788,
 .CX 1551 789,
 .CX 789 1551,
 .CX 1551 789,
 .CX 1552 790,
 .CX 790 1552,
 .CX 1552 790,
 .CX 529 791,
 .CX 791 529,
 .CX 529 791,
 .X 786,
 .CX 523 786,
 .measureX 530 [] []
]
def candidate : Program := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20 ++ block21 ++ block22 ++ block23 ++ block24 ++ block25 ++ block26 ++ block27 ++ block28 ++ block29 ++ block30 ++ block31 ++ block32 ++ block33 ++ block34 ++ block35
theorem counts0 : toffoliCount block0=1 ∧ measurementCount block0=0 ∧ Challenge.gateSlots block0=32 := by decide +kernel
theorem support0 : wires block0⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical0 : GatePhysical block0 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts1 : toffoliCount block1=1 ∧ measurementCount block1=0 ∧ Challenge.gateSlots block1=32 := by decide +kernel
theorem support1 : wires block1⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical1 : GatePhysical block1 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts2 : toffoliCount block2=0 ∧ measurementCount block2=0 ∧ Challenge.gateSlots block2=32 := by decide +kernel
theorem support2 : wires block2⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical2 : GatePhysical block2 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts3 : toffoliCount block3=1 ∧ measurementCount block3=0 ∧ Challenge.gateSlots block3=32 := by decide +kernel
theorem support3 : wires block3⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical3 : GatePhysical block3 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts4 : toffoliCount block4=1 ∧ measurementCount block4=0 ∧ Challenge.gateSlots block4=32 := by decide +kernel
theorem support4 : wires block4⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical4 : GatePhysical block4 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts5 : toffoliCount block5=0 ∧ measurementCount block5=0 ∧ Challenge.gateSlots block5=32 := by decide +kernel
theorem support5 : wires block5⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical5 : GatePhysical block5 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts6 : toffoliCount block6=1 ∧ measurementCount block6=0 ∧ Challenge.gateSlots block6=32 := by decide +kernel
theorem support6 : wires block6⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical6 : GatePhysical block6 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts7 : toffoliCount block7=0 ∧ measurementCount block7=0 ∧ Challenge.gateSlots block7=32 := by decide +kernel
theorem support7 : wires block7⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical7 : GatePhysical block7 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts8 : toffoliCount block8=1 ∧ measurementCount block8=0 ∧ Challenge.gateSlots block8=32 := by decide +kernel
theorem support8 : wires block8⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical8 : GatePhysical block8 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts9 : toffoliCount block9=0 ∧ measurementCount block9=0 ∧ Challenge.gateSlots block9=32 := by decide +kernel
theorem support9 : wires block9⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical9 : GatePhysical block9 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts10 : toffoliCount block10=1 ∧ measurementCount block10=0 ∧ Challenge.gateSlots block10=32 := by decide +kernel
theorem support10 : wires block10⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical10 : GatePhysical block10 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts11 : toffoliCount block11=1 ∧ measurementCount block11=0 ∧ Challenge.gateSlots block11=32 := by decide +kernel
theorem support11 : wires block11⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical11 : GatePhysical block11 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts12 : toffoliCount block12=0 ∧ measurementCount block12=0 ∧ Challenge.gateSlots block12=32 := by decide +kernel
theorem support12 : wires block12⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical12 : GatePhysical block12 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts13 : toffoliCount block13=0 ∧ measurementCount block13=0 ∧ Challenge.gateSlots block13=32 := by decide +kernel
theorem support13 : wires block13⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical13 : GatePhysical block13 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts14 : toffoliCount block14=1 ∧ measurementCount block14=0 ∧ Challenge.gateSlots block14=32 := by decide +kernel
theorem support14 : wires block14⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical14 : GatePhysical block14 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts15 : toffoliCount block15=0 ∧ measurementCount block15=0 ∧ Challenge.gateSlots block15=32 := by decide +kernel
theorem support15 : wires block15⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical15 : GatePhysical block15 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts16 : toffoliCount block16=1 ∧ measurementCount block16=0 ∧ Challenge.gateSlots block16=32 := by decide +kernel
theorem support16 : wires block16⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical16 : GatePhysical block16 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts17 : toffoliCount block17=0 ∧ measurementCount block17=0 ∧ Challenge.gateSlots block17=32 := by decide +kernel
theorem support17 : wires block17⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical17 : GatePhysical block17 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts18 : toffoliCount block18=0 ∧ measurementCount block18=0 ∧ Challenge.gateSlots block18=32 := by decide +kernel
theorem support18 : wires block18⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical18 : GatePhysical block18 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts19 : toffoliCount block19=1 ∧ measurementCount block19=0 ∧ Challenge.gateSlots block19=32 := by decide +kernel
theorem support19 : wires block19⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical19 : GatePhysical block19 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts20 : toffoliCount block20=0 ∧ measurementCount block20=0 ∧ Challenge.gateSlots block20=32 := by decide +kernel
theorem support20 : wires block20⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical20 : GatePhysical block20 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts21 : toffoliCount block21=1 ∧ measurementCount block21=0 ∧ Challenge.gateSlots block21=32 := by decide +kernel
theorem support21 : wires block21⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical21 : GatePhysical block21 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts22 : toffoliCount block22=0 ∧ measurementCount block22=0 ∧ Challenge.gateSlots block22=32 := by decide +kernel
theorem support22 : wires block22⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical22 : GatePhysical block22 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts23 : toffoliCount block23=0 ∧ measurementCount block23=0 ∧ Challenge.gateSlots block23=32 := by decide +kernel
theorem support23 : wires block23⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical23 : GatePhysical block23 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts24 : toffoliCount block24=1 ∧ measurementCount block24=0 ∧ Challenge.gateSlots block24=32 := by decide +kernel
theorem support24 : wires block24⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical24 : GatePhysical block24 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts25 : toffoliCount block25=0 ∧ measurementCount block25=0 ∧ Challenge.gateSlots block25=32 := by decide +kernel
theorem support25 : wires block25⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical25 : GatePhysical block25 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts26 : toffoliCount block26=0 ∧ measurementCount block26=0 ∧ Challenge.gateSlots block26=32 := by decide +kernel
theorem support26 : wires block26⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical26 : GatePhysical block26 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts27 : toffoliCount block27=1 ∧ measurementCount block27=0 ∧ Challenge.gateSlots block27=32 := by decide +kernel
theorem support27 : wires block27⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical27 : GatePhysical block27 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts28 : toffoliCount block28=0 ∧ measurementCount block28=0 ∧ Challenge.gateSlots block28=32 := by decide +kernel
theorem support28 : wires block28⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical28 : GatePhysical block28 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts29 : toffoliCount block29=0 ∧ measurementCount block29=0 ∧ Challenge.gateSlots block29=32 := by decide +kernel
theorem support29 : wires block29⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical29 : GatePhysical block29 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts30 : toffoliCount block30=0 ∧ measurementCount block30=0 ∧ Challenge.gateSlots block30=32 := by decide +kernel
theorem support30 : wires block30⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical30 : GatePhysical block30 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts31 : toffoliCount block31=0 ∧ measurementCount block31=0 ∧ Challenge.gateSlots block31=32 := by decide +kernel
theorem support31 : wires block31⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical31 : GatePhysical block31 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts32 : toffoliCount block32=0 ∧ measurementCount block32=0 ∧ Challenge.gateSlots block32=32 := by decide +kernel
theorem support32 : wires block32⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical32 : GatePhysical block32 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts33 : toffoliCount block33=0 ∧ measurementCount block33=0 ∧ Challenge.gateSlots block33=32 := by decide +kernel
theorem support33 : wires block33⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical33 : GatePhysical block33 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts34 : toffoliCount block34=0 ∧ measurementCount block34=10 ∧ Challenge.gateSlots block34=264 := by decide +kernel
theorem support34 : wires block34⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical34 : GatePhysical block34 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem counts35 : toffoliCount block35=0 ∧ measurementCount block35=1 ∧ Challenge.gateSlots block35=21 := by decide +kernel
theorem support35 : wires block35⊆sites.toFinset.erase 1559 := by decide +kernel
theorem physical35 : GatePhysical block35 := Forward11Width.physical_of_all _ (by decide +kernel)
theorem resources : toffoliCount candidate=14 ∧ measurementCount candidate=11 ∧ Challenge.gateSlots candidate=1373 := by
 simp only [candidate,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,counts0.1,counts0.2.1,counts0.2.2,counts1.1,counts1.2.1,counts1.2.2,counts2.1,counts2.2.1,counts2.2.2,counts3.1,counts3.2.1,counts3.2.2,counts4.1,counts4.2.1,counts4.2.2,counts5.1,counts5.2.1,counts5.2.2,counts6.1,counts6.2.1,counts6.2.2,counts7.1,counts7.2.1,counts7.2.2,counts8.1,counts8.2.1,counts8.2.2,counts9.1,counts9.2.1,counts9.2.2,counts10.1,counts10.2.1,counts10.2.2,counts11.1,counts11.2.1,counts11.2.2,counts12.1,counts12.2.1,counts12.2.2,counts13.1,counts13.2.1,counts13.2.2,counts14.1,counts14.2.1,counts14.2.2,counts15.1,counts15.2.1,counts15.2.2,counts16.1,counts16.2.1,counts16.2.2,counts17.1,counts17.2.1,counts17.2.2,counts18.1,counts18.2.1,counts18.2.2,counts19.1,counts19.2.1,counts19.2.2,counts20.1,counts20.2.1,counts20.2.2,counts21.1,counts21.2.1,counts21.2.2,counts22.1,counts22.2.1,counts22.2.2,counts23.1,counts23.2.1,counts23.2.2,counts24.1,counts24.2.1,counts24.2.2,counts25.1,counts25.2.1,counts25.2.2,counts26.1,counts26.2.1,counts26.2.2,counts27.1,counts27.2.1,counts27.2.2,counts28.1,counts28.2.1,counts28.2.2,counts29.1,counts29.2.1,counts29.2.2,counts30.1,counts30.2.1,counts30.2.2,counts31.1,counts31.2.1,counts31.2.2,counts32.1,counts32.2.1,counts32.2.2,counts33.1,counts33.2.1,counts33.2.2,counts34.1,counts34.2.1,counts34.2.2,counts35.1,counts35.2.1,counts35.2.2]
 decide +kernel
theorem support_live : wires candidate⊆sites.toFinset.erase 1559 := by
 simp only [candidate,wires_append,Finset.union_subset_iff]
 exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨support0,support1⟩,support2⟩,support3⟩,support4⟩,support5⟩,support6⟩,support7⟩,support8⟩,support9⟩,support10⟩,support11⟩,support12⟩,support13⟩,support14⟩,support15⟩,support16⟩,support17⟩,support18⟩,support19⟩,support20⟩,support21⟩,support22⟩,support23⟩,support24⟩,support25⟩,support26⟩,support27⟩,support28⟩,support29⟩,support30⟩,support31⟩,support32⟩,support33⟩,support34⟩,support35⟩
theorem physical : GatePhysical candidate := by
 simp only [candidate,gatePhysical_append]
 exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨physical0,physical1⟩,physical2⟩,physical3⟩,physical4⟩,physical5⟩,physical6⟩,physical7⟩,physical8⟩,physical9⟩,physical10⟩,physical11⟩,physical12⟩,physical13⟩,physical14⟩,physical15⟩,physical16⟩,physical17⟩,physical18⟩,physical19⟩,physical20⟩,physical21⟩,physical22⟩,physical23⟩,physical24⟩,physical25⟩,physical26⟩,physical27⟩,physical28⟩,physical29⟩,physical30⟩,physical31⟩,physical32⟩,physical33⟩,physical34⟩,physical35⟩
theorem support : wires candidate⊆sites.toFinset := support_live.trans (Finset.erase_subset _ _)
                                                                                              
                                                
                                              
                                              
                                                    
                                                      
                                                        
        
                      
end ECDSAAdd.Entrant.Inverse14Width

-- Verified CompactInverse14
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompactInverse14
open Arithmetic MappedCompressed Secp256k1 History5 CompactCertificates
def perm : Equiv.Perm Wire := Equiv.swap (0:Wire) 522 * Equiv.swap (1:Wire) 523 * Equiv.swap (2:Wire) 524 * Equiv.swap (3:Wire) 525 * Equiv.swap (4:Wire) 526 * Equiv.swap (5:Wire) 527 * Equiv.swap (6:Wire) 528 * Equiv.swap (7:Wire) 529 * Equiv.swap (8:Wire) 786 * Equiv.swap (9:Wire) 787 * Equiv.swap (10:Wire) 788 * Equiv.swap (11:Wire) 789 * Equiv.swap (12:Wire) 790 * Equiv.swap (13:Wire) 791 * Equiv.swap (14:Wire) 1551 * Equiv.swap (15:Wire) 1552 * Equiv.swap (16:Wire) 1553 * Equiv.swap (17:Wire) 1554 * Equiv.swap (18:Wire) 1556 * Equiv.swap (19:Wire) 1557 * Equiv.swap (20:Wire) 1558 * Equiv.swap (21:Wire) 1559 * Equiv.swap (22:Wire) 530
def block0 : Program := [
 .X 5,
 .CX 4 5,
 .CX 4 8,
 .CX 17 16,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CCX 0 1 5,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 4 14
]
theorem placement0 : renameProgram perm block0=Inverse14Width.block0 := by decide +kernel
def block1 : Program := [
 .CX 14 4,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 16,
 .CX 17 16,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 2,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 6,
 .CX 0 2,
 .CX 2 0
]
theorem placement1 : renameProgram perm block1=Inverse14Width.block1 := by decide +kernel
def block2 : Program := [
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 3 2,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 16,
 .CX 17 16,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 2,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4
]
theorem placement2 : renameProgram perm block2=Inverse14Width.block2 := by decide +kernel
def block3 : Program := [
 .CX 2 4,
 .CX 2 1,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 1 0,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 0 2,
 .CCX 0 1 7,
 .CX 0 2,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 1 0,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 1,
 .CX 2 4,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 3 2,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14
]
theorem placement3 : renameProgram perm block3=Inverse14Width.block3 := by decide +kernel
def block4 : Program := [
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 16,
 .CX 6 15,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 14 2,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 8
]
theorem placement4 : renameProgram perm block4=Inverse14Width.block4 := by decide +kernel
def block5 : Program := [
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 14 2,
 .CX 14 15,
 .CX 15 14,
 .CX 15 16,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 6 15,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15
]
theorem placement5 : renameProgram perm block5=Inverse14Width.block5 := by decide +kernel
def block6 : Program := [
 .CX 4 3,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 14,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 9,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 3 14,
 .CX 4 14
]
theorem placement6 : renameProgram perm block6=Inverse14Width.block6 := by decide +kernel
def block7 : Program := [
 .CX 14 4,
 .CX 4 14,
 .CX 4 3,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 9 8,
 .CX 8 9,
 .CX 8 7,
 .CX 7 8,
 .CX 7 5,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 5 16,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 16 17,
 .CX 16 15,
 .CX 15 16,
 .CX 15 14,
 .CX 14 15,
 .CX 14 3,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 4,
 .CX 3 2
]
theorem placement7 : renameProgram perm block7=Inverse14Width.block7 := by decide +kernel
def block8 : Program := [
 .CX 3 1,
 .CX 1 3,
 .CX 1 2,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 10,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 2,
 .CX 1 3,
 .CX 3 1,
 .CX 3 2,
 .CX 3 4,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 14 3,
 .CX 14 15,
 .CX 15 14,
 .CX 15 16,
 .CX 16 15,
 .CX 16 17,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 5 16,
 .CX 5 6,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7
]
theorem placement8 : renameProgram perm block8=Inverse14Width.block8 := by decide +kernel
def block9 : Program := [
 .CX 7 5,
 .CX 7 8,
 .CX 8 7,
 .CX 8 9,
 .CX 9 8,
 .CX 9 6,
 .CX 8 10,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 9,
 .CX 9 7,
 .CX 7 9,
 .CX 6 8,
 .CX 6 16,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 7,
 .CX 7 5,
 .CX 5 7,
 .CX 17 6,
 .CX 6 17,
 .CX 17 6,
 .CX 16 5,
 .CX 16 3,
 .CX 15 17,
 .CX 17 15,
 .CX 15 17,
 .CX 14 16,
 .CX 16 14,
 .CX 14 16
]
theorem placement9 : renameProgram perm block9=Inverse14Width.block9 := by decide +kernel
def block10 : Program := [
 .CX 4 15,
 .CX 15 4,
 .CX 4 15,
 .CX 3 14,
 .CX 3 4,
 .CX 4 3,
 .CX 3 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 4,
 .CX 4 1,
 .CX 1 4,
 .CX 0 3,
 .CX 3 0,
 .CX 0 3,
 .CCX 0 1 2,
 .CX 9 7,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 8,
 .CX 7 6,
 .CX 6 7,
 .CX 6 5,
 .CX 5 6,
 .CX 5 4,
 .CX 5 3,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 16 17
]
theorem placement10 : renameProgram perm block10=Inverse14Width.block10 := by decide +kernel
def block11 : Program := [
 .CX 17 16,
 .CX 16 17,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 4 3,
 .CX 4 2,
 .CX 3 14,
 .CX 3 4,
 .CX 3 2,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 11,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3
]
theorem placement11 : renameProgram perm block11=Inverse14Width.block11 := by decide +kernel
def block12 : Program := [
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 3 2,
 .CX 3 4,
 .CX 3 14,
 .CX 4 2,
 .CX 4 3,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 5 3,
 .CX 5 4,
 .CX 5 6,
 .CX 6 5,
 .CX 6 7,
 .CX 7 6,
 .CX 7 8,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 9 7
]
theorem placement12 : renameProgram perm block12=Inverse14Width.block12 := by decide +kernel
def block13 : Program := [
 .CX 9 7,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 8,
 .CX 7 17,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 17 5,
 .CX 17 16,
 .CX 16 17,
 .CX 16 4,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 4 2,
 .CX 3 0,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3
]
theorem placement13 : renameProgram perm block13=Inverse14Width.block13 := by decide +kernel
def block14 : Program := [
 .CX 0 2,
 .CCX 0 1 12,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 3 0,
 .CX 4 2,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 16 4,
 .CX 16 17,
 .CX 17 16,
 .CX 17 5,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 7 17,
 .CX 7 8,
 .CX 8 9
]
theorem placement14 : renameProgram perm block14=Inverse14Width.block14 := by decide +kernel
def block15 : Program := [
 .CX 9 8,
 .CX 8 9,
 .CX 9 7,
 .CX 12 9,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 9 10,
 .CX 9 6,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 6 7,
 .CX 6 5,
 .CX 5 6,
 .CX 5 17,
 .CX 17 5,
 .CX 17 16,
 .CX 16 17,
 .CX 16 14,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 14 4,
 .CX 14 3
]
theorem placement15 : renameProgram perm block15=Inverse14Width.block15 := by decide +kernel
def block16 : Program := [
 .CX 3 14,
 .CX 3 4,
 .CX 3 1,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 1 0,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 13,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 2,
 .CX 2 1,
 .CX 1 2,
 .CX 1 0,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 1,
 .CX 3 4,
 .CX 3 14,
 .CX 14 3
]
theorem placement16 : renameProgram perm block16=Inverse14Width.block16 := by decide +kernel
def block17 : Program := [
 .CX 14 4,
 .CX 14 15,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 16 14,
 .CX 16 17,
 .CX 17 16,
 .CX 17 5,
 .CX 5 17,
 .CX 5 6,
 .CX 6 5,
 .CX 6 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 9 6,
 .CX 9 10,
 .CX 10 11,
 .CX 11 10,
 .CX 10 11,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 12 9,
 .CX 10 8,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10
]
theorem placement17 : renameProgram perm block17=Inverse14Width.block17 := by decide +kernel
def block18 : Program := [
 .CX 8 9,
 .CX 8 5,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 5 17,
 .CX 17 5,
 .CX 17 15,
 .CX 17 14,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 4,
 .CX 14 16,
 .CX 14 0,
 .CX 4 15,
 .CX 4 14,
 .CX 4 2,
 .CX 4 0,
 .CX 3 14,
 .CX 14 3,
 .CX 3 14,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1
]
theorem placement18 : renameProgram perm block18=Inverse14Width.block18 := by decide +kernel
def block19 : Program := [
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CCX 0 1 18,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 3 14,
 .CX 14 3,
 .CX 3 14,
 .CX 4 0,
 .CX 4 2,
 .CX 4 14,
 .CX 4 15,
 .CX 14 0,
 .CX 14 16,
 .CX 15 4,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 14,
 .CX 17 15,
 .CX 17 5,
 .CX 5 17,
 .CX 5 6,
 .CX 6 7
]
theorem placement19 : renameProgram perm block19=Inverse14Width.block19 := by decide +kernel
def block20 : Program := [
 .CX 7 6,
 .CX 6 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 5,
 .CX 8 9,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 10 8,
 .CX 18 10,
 .CX 13 18,
 .CX 18 13,
 .CX 13 18,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 10 11,
 .CX 10 8,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 8 9,
 .CX 8 5,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 6 7
]
theorem placement20 : renameProgram perm block20=Inverse14Width.block20 := by decide +kernel
def block21 : Program := [
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 5 17,
 .CX 17 5,
 .CX 17 15,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 16,
 .CX 15 4,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 4 14,
 .CX 4 2,
 .CX 2 4,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CCX 0 1 19,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1
]
theorem placement21 : renameProgram perm block21=Inverse14Width.block21 := by decide +kernel
def block22 : Program := [
 .CX 1 3,
 .CX 2 3,
 .CX 3 2,
 .CX 2 3,
 .CX 2 4,
 .CX 4 2,
 .CX 4 14,
 .CX 14 15,
 .CX 15 14,
 .CX 14 15,
 .CX 15 4,
 .CX 15 16,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 15,
 .CX 17 5,
 .CX 5 17,
 .CX 5 6,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 5,
 .CX 8 9,
 .CX 9 10,
 .CX 10 9,
 .CX 9 10,
 .CX 10 8,
 .CX 10 11
]
theorem placement22 : renameProgram perm block22=Inverse14Width.block22 := by decide +kernel
def block23 : Program := [
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 13 18,
 .CX 18 13,
 .CX 13 18,
 .CX 18 10,
 .CX 8 17,
 .CX 8 15,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 17 16,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 16 5,
 .CX 16 17,
 .CX 16 15,
 .CX 16 14,
 .CX 15 17,
 .CX 15 2,
 .CX 14 16
]
theorem placement23 : renameProgram perm block23=Inverse14Width.block23 := by decide +kernel
def block24 : Program := [
 .CX 14 15,
 .CX 14 2,
 .CX 14 1,
 .CX 4 15,
 .CX 15 4,
 .CX 4 15,
 .CX 3 14,
 .CX 14 3,
 .CX 3 14,
 .CX 2 4,
 .CX 2 0,
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 20,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 2 0,
 .CX 2 4,
 .CX 3 14,
 .CX 14 3,
 .CX 3 14,
 .CX 4 15,
 .CX 15 4,
 .CX 4 15,
 .CX 14 1,
 .CX 14 2
]
theorem placement24 : renameProgram perm block24=Inverse14Width.block24 := by decide +kernel
def block25 : Program := [
 .CX 14 15,
 .CX 14 16,
 .CX 15 2,
 .CX 15 17,
 .CX 16 14,
 .CX 16 15,
 .CX 16 17,
 .CX 16 5,
 .CX 17 5,
 .CX 5 17,
 .CX 17 5,
 .CX 17 16,
 .CX 5 6,
 .CX 6 5,
 .CX 5 6,
 .CX 6 7,
 .CX 7 6,
 .CX 6 7,
 .CX 7 8,
 .CX 8 7,
 .CX 7 8,
 .CX 8 15,
 .CX 8 17,
 .CX 20 10,
 .CX 19 20,
 .CX 20 19,
 .CX 19 20,
 .CX 18 19,
 .CX 19 18,
 .CX 18 19,
 .CX 13 18,
 .CX 18 13
]
theorem placement25 : renameProgram perm block25=Inverse14Width.block25 := by decide +kernel
def block26 : Program := [
 .CX 13 18,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 10 11,
 .CX 10 9,
 .CX 9 10,
 .CX 9 7,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 7 8,
 .CX 7 6,
 .CX 6 7,
 .CX 6 5,
 .CX 5 6,
 .CX 5 17,
 .CX 17 5,
 .CX 17 14,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 15,
 .CX 14 0,
 .CX 4 3,
 .CX 4 14
]
theorem placement26 : renameProgram perm block26=Inverse14Width.block26 := by decide +kernel
def block27 : Program := [
 .CX 14 4,
 .CX 4 14,
 .CX 3 14,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 0 2,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CCX 0 1 22,
 .CX 0 1,
 .CX 1 0,
 .CX 0 1,
 .CX 0 2,
 .CX 1 3,
 .CX 3 1,
 .CX 1 3,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 3 14,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 4 3,
 .CX 14 0,
 .CX 14 15,
 .CX 15 16
]
theorem placement27 : renameProgram perm block27=Inverse14Width.block27 := by decide +kernel
def block28 : Program := [
 .CX 16 15,
 .CX 15 16,
 .CX 16 17,
 .CX 17 16,
 .CX 16 17,
 .CX 17 14,
 .CX 17 5,
 .CX 5 17,
 .CX 5 6,
 .CX 6 5,
 .CX 6 7,
 .CX 7 6,
 .CX 7 8,
 .CX 8 9,
 .CX 9 8,
 .CX 8 9,
 .CX 9 7,
 .CX 9 10,
 .CX 10 9,
 .CX 10 11,
 .CX 11 12,
 .CX 12 11,
 .CX 11 12,
 .CX 12 13,
 .CX 13 12,
 .CX 12 13,
 .CX 13 18,
 .CX 18 13,
 .CX 13 18,
 .CX 18 19,
 .CX 19 18,
 .CX 18 19
]
theorem placement28 : renameProgram perm block28=Inverse14Width.block28 := by decide +kernel
def block29 : Program := [
 .CX 19 20,
 .CX 20 19,
 .CX 19 20,
 .CX 20 10,
 .CX 22 20,
 .CX 22 18,
 .CX 22 10,
 .CX 20 18,
 .CX 20 17,
 .CX 20 16,
 .CX 20 22,
 .CX 22 20,
 .CX 20 22,
 .CX 19 18,
 .CX 19 13,
 .CX 19 12,
 .CX 19 9,
 .CX 19 6,
 .CX 19 20,
 .CX 20 19,
 .CX 19 20,
 .CX 18 22,
 .CX 18 10,
 .CX 18 5,
 .CX 18 16,
 .CX 18 2,
 .CX 18 20,
 .CX 20 18,
 .CX 18 20,
 .CX 13 22,
 .CX 13 12,
 .CX 13 9
]
theorem placement29 : renameProgram perm block29=Inverse14Width.block29 := by decide +kernel
def block30 : Program := [
 .CX 13 6,
 .CX 13 16,
 .CX 12 22,
 .CX 12 20,
 .CX 12 5,
 .CX 12 16,
 .CX 12 14,
 .CX 12 2,
 .CX 12 18,
 .CX 18 12,
 .CX 12 18,
 .CX 11 22,
 .CX 11 20,
 .CX 11 19,
 .CX 11 5,
 .CX 11 16,
 .CX 11 2,
 .CX 11 0,
 .CX 11 18,
 .CX 18 11,
 .CX 11 18,
 .CX 10 22,
 .CX 10 20,
 .CX 10 8,
 .CX 10 5,
 .CX 10 16,
 .CX 10 2,
 .CX 10 19,
 .CX 19 10,
 .CX 10 19,
 .CX 9 22,
 .CX 9 6
]
theorem placement30 : renameProgram perm block30=Inverse14Width.block30 := by decide +kernel
def block31 : Program := [
 .CX 9 16,
 .CX 9 1,
 .CX 9 13,
 .CX 13 9,
 .CX 9 13,
 .CX 8 19,
 .CX 8 6,
 .CX 8 5,
 .CX 8 18,
 .CX 18 8,
 .CX 8 18,
 .CX 7 18,
 .CX 7 5,
 .CX 7 12,
 .CX 12 7,
 .CX 7 12,
 .CX 6 22,
 .CX 6 18,
 .CX 6 5,
 .CX 6 17,
 .CX 6 16,
 .CX 6 12,
 .CX 12 6,
 .CX 6 12,
 .CX 5 20,
 .CX 5 17,
 .CX 5 15,
 .CX 5 2,
 .CX 5 12,
 .CX 12 5,
 .CX 5 12,
 .CX 17 22
]
theorem placement31 : renameProgram perm block31=Inverse14Width.block31 := by decide +kernel
def block32 : Program := [
 .CX 17 20,
 .CX 17 18,
 .CX 17 13,
 .CX 17 12,
 .CX 17 8,
 .CX 17 16,
 .CX 17 15,
 .CX 17 4,
 .CX 17 2,
 .CX 17 1,
 .CX 17 0,
 .CX 16 22,
 .CX 16 9,
 .CX 16 7,
 .CX 16 6,
 .CX 6 16,
 .CX 16 6,
 .CX 15 20,
 .CX 15 18,
 .CX 15 13,
 .CX 15 12,
 .CX 15 2,
 .CX 15 1,
 .CX 15 16,
 .CX 16 15,
 .CX 15 16,
 .CX 14 11,
 .CX 14 10,
 .CX 14 8,
 .CX 14 6,
 .CX 14 16,
 .CX 14 4
]
theorem placement32 : renameProgram perm block32=Inverse14Width.block32 := by decide +kernel
def block33 : Program := [
 .CX 14 3,
 .CX 14 0,
 .CX 4 8,
 .CX 4 5,
 .CX 4 17,
 .CX 4 16,
 .CX 4 0,
 .CX 4 14,
 .CX 14 4,
 .CX 4 14,
 .CX 3 20,
 .CX 3 18,
 .CX 3 13,
 .CX 3 10,
 .CX 3 6,
 .CX 3 17,
 .CX 3 16,
 .CX 3 4,
 .CX 3 2,
 .CX 3 1,
 .CX 2 20,
 .CX 2 18,
 .CX 2 13,
 .CX 2 10,
 .CX 2 5,
 .CX 2 16,
 .CX 2 14,
 .CX 2 1,
 .CX 2 4,
 .CX 4 2,
 .CX 2 4,
 .CX 1 13
]
theorem placement33 : renameProgram perm block33=Inverse14Width.block33 := by decide +kernel
def block34 : Program := [
 .CX 1 9,
 .CX 1 17,
 .CX 17 1,
 .CX 1 17,
 .CX 0 8,
 .CX 0 16,
 .CX 0 4,
 .CX 0 3,
 .CX 0 2,
 .CX 2 0,
 .CX 0 2,
 .X 14,
 .X 16,
 .X 17,
 .X 5,
 .measureX 22 [] [.Z 4, .Z 16, .Z 5, .Z 8, .Z 10, .Z 12, .Z 13, .CZ 0 8, .CZ 0 9, .CZ 0 20, .CZ 1 2, .CZ 1 3, .CZ 1 4, .CZ 1 17, .CZ 1 11, .CZ 1 12, .CZ 1 20, .CZ 2 8, .CZ 2 11, .CZ 16 6, .CZ 16 13, .CZ 16 20],
 .measureX 20 [] [.Z 4, .Z 14, .Z 15, .Z 16, .Z 17, .Z 5, .Z 7, .Z 10, .Z 12, .Z 13, .Z 18, .CZ 0 2, .CZ 0 16, .CZ 0 17, .CZ 0 13, .CZ 0 18, .CZ 1 17, .CZ 1 11, .CZ 1 18, .CZ 2 3, .CZ 2 16, .CZ 2 5, .CZ 2 6, .CZ 2 7, .CZ 2 8, .CZ 2 9, .CZ 2 11, .CZ 2 12, .CZ 2 13, .CZ 2 18, .CZ 2 19, .CZ 3 4, .CZ 3 14, .CZ 3 8, .CZ 3 10, .CZ 3 18, .CZ 4 6, .CZ 4 18, .CZ 14 16, .CZ 16 17, .CZ 16 6, .CZ 16 13, .CZ 16 18, .CZ 17 18],
 .X 19,
 .measureX 19 [] [.Z 0, .Z 1, .Z 3, .Z 14, .Z 15, .Z 8, .Z 10, .Z 11, .Z 12, .CZ 0 1, .CZ 0 2, .CZ 0 4, .CZ 0 17, .CZ 0 8, .CZ 0 10, .CZ 1 2, .CZ 1 4, .CZ 1 11, .CZ 1 12, .CZ 2 3, .CZ 2 4, .CZ 2 6, .CZ 2 7, .CZ 2 9, .CZ 2 11, .CZ 2 12, .CZ 3 4, .CZ 3 16, .CZ 3 17, .CZ 3 6, .CZ 3 8, .CZ 3 9, .CZ 3 10, .CZ 4 12, .CZ 14 16, .CZ 14 17, .CZ 14 10],
 .X 18,
 .measureX 18 [] [.Z 1, .Z 4, .Z 16, .Z 5, .Z 7, .Z 12, .CZ 0 1, .CZ 0 4, .CZ 0 16, .CZ 0 5, .CZ 0 8, .CZ 0 9, .CZ 0 11, .CZ 0 12, .CZ 1 3, .CZ 1 14, .CZ 1 17, .CZ 1 12, .CZ 2 16, .CZ 2 17, .CZ 2 7, .CZ 2 11, .CZ 2 12, .CZ 3 17, .CZ 3 5, .CZ 3 6, .CZ 3 12, .CZ 4 16, .CZ 4 5, .CZ 4 6, .CZ 4 8, .CZ 4 10, .CZ 4 12, .CZ 14 10, .CZ 16 5, .CZ 16 6, .CZ 16 10],
 .measureX 13 [] [.Z 0, .Z 2, .Z 3, .Z 4, .Z 16, .Z 17, .Z 8, .Z 11, .Z 12, .CZ 0 2, .CZ 0 16, .CZ 0 8, .CZ 0 9, .CZ 0 11, .CZ 1 2, .CZ 1 3, .CZ 1 4, .CZ 1 14, .CZ 1 11, .CZ 1 12, .CZ 2 6, .CZ 2 7, .CZ 2 8, .CZ 3 6, .CZ 3 11],
 .X 12,
 .measureX 12 [] [.Z 0, .Z 3, .Z 14, .Z 5, .Z 8, .Z 10, .CZ 0 2, .CZ 0 17, .CZ 0 10, .CZ 1 3, .CZ 1 4, .CZ 1 14, .CZ 2 17, .CZ 2 6, .CZ 2 8, .CZ 2 10, .CZ 3 14, .CZ 3 5, .CZ 3 6, .CZ 3 8, .CZ 3 9, .CZ 3 10, .CZ 4 16, .CZ 4 5, .CZ 4 8, .CZ 4 10, .CZ 14 16, .CZ 14 17, .CZ 14 8, .CZ 14 10, .CZ 16 17, .CZ 16 6, .CZ 17 6],
 .measureX 11 [] [.Z 2, .Z 3, .Z 16, .Z 8, .CZ 0 3, .CZ 0 17, .CZ 2 3, .CZ 2 14, .CZ 2 16, .CZ 2 9, .CZ 3 8, .CZ 16 17, .CZ 16 6, .CZ 16 9, .CZ 17 8],
 .measureX 10 [] [.Z 0, .Z 1, .Z 2, .Z 4, .CZ 1 2, .CZ 1 4, .CZ 1 16, .CZ 1 5],
 .X 9,
 .measureX 9 [] [.Z 17, .Z 6, .CZ 1 3, .CZ 1 14, .CZ 1 17, .CZ 1 6],
 .measureX 8 [] [.Z 0, .Z 1, .Z 2, .CZ 1 2, .CZ 1 16],
 .CX 14 5,
 .CX 5 14,
 .CX 14 5
]
theorem placement34 : renameProgram perm block34=Inverse14Width.block34 := by decide +kernel
def block35 : Program := [
 .CX 15 6,
 .CX 6 15,
 .CX 15 6,
 .CX 16 9,
 .CX 9 16,
 .CX 16 9,
 .CX 17 10,
 .CX 10 17,
 .CX 17 10,
 .CX 14 11,
 .CX 11 14,
 .CX 14 11,
 .CX 15 12,
 .CX 12 15,
 .CX 15 12,
 .CX 7 13,
 .CX 13 7,
 .CX 7 13,
 .X 8,
 .CX 1 8,
 .measureX 22 [] []
]
theorem placement35 : renameProgram perm block35=Inverse14Width.block35 := by decide +kernel
def blocks : List Program := [block0,block1,block2,block3,block4,block5,block6,block7,block8,block9,block10,block11,block12,block13,block14,block15,block16,block17,block18,block19,block20,block21,block22,block23,block24,block25,block26,block27,block28,block29,block30,block31,block32,block33,block34,block35]
def candidate : Program := blocks.flatten
theorem placement : renameProgram perm candidate=Inverse14Width.candidate := by
 rw [candidate,rename_flatten]
 simp only [blocks,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,placement0,placement1,placement2,placement3,placement4,placement5,placement6,placement7,placement8,placement9,placement10,placement11,placement12,placement13,placement14,placement15,placement16,placement17,placement18,placement19,placement20,placement21,placement22,placement23,placement24,placement25,placement26,placement27,placement28,placement29,placement30,placement31,placement32,placement33,placement34,placement35,List.append_nil,Inverse14Width.candidate,List.append_assoc]
def reference : Program := renameProgram perm.symm (tickMR8 ++ W.ReverseCarry.compactReceiverTick base 507)
theorem reference_placement : renameProgram perm reference=(tickMR8 ++ W.ReverseCarry.compactReceiverTick base 507) := rename_inverse _ _
def trace0 : List Nat := [286, 16398, 16408, 16402, 30, 16667, 286, 16646, 16918, 702, 33822, 50195, 99343, 50195, 115723, 54291, 100371, 100371, 54035, 102406, 53491, 59571, 124931, 58387, 250903, 218135, 54291, 124955, 4237331, 4248595, 4968467, 1215543, 7187, 7187, 228642, 2, 2]
theorem checked0 : checkTrace blocks trace0=true := by decide +kernel
theorem old0 : phaseClean508 reference 286=some 2 := by decide +kernel
theorem row0 (m n : List Bool) : run candidate m ⟨false,tbN_t8 286⟩=run reference n ⟨false,tbN_t8 286⟩ := by
 have h:=trace_sound blocks 286 [16398, 16408, 16402, 30, 16667, 286, 16646, 16918, 702, 33822, 50195, 99343, 50195, 115723, 54291, 100371, 100371, 54035, 102406, 53491, 59571, 124931, 58387, 250903, 218135, 54291, 124955, 4237331, 4248595, 4968467, 1215543, 7187, 7187, 228642, 2, 2] checked0 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old0 n]
 rfl
def trace1 : List Nat := [286, 16398, 16408, 16402, 30, 16667, 286, 16646, 16918, 702, 33822, 50195, 99343, 50195, 115723, 54291, 100371, 100371, 54035, 102406, 53491, 59571, 124931, 58387, 250903, 218135, 54291, 124955, 4237331, 4248595, 4968467, 1215543, 7187, 7187, 228642, 2, 2]
theorem checked1 : checkTrace blocks trace1=true := by decide +kernel
theorem old1 : phaseClean508 reference 286=some 2 := by decide +kernel
theorem row1 (m n : List Bool) : run candidate m ⟨false,tbN_t8 286⟩=run reference n ⟨false,tbN_t8 286⟩ := by
 have h:=trace_sound blocks 286 [16398, 16408, 16402, 30, 16667, 286, 16646, 16918, 702, 33822, 50195, 99343, 50195, 115723, 54291, 100371, 100371, 54035, 102406, 53491, 59571, 124931, 58387, 250903, 218135, 54291, 124955, 4237331, 4248595, 4968467, 1215543, 7187, 7187, 228642, 2, 2] checked1 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old1 n]
 rfl
def trace2 : List Nat := [287, 16399, 16413, 16403, 31, 16671, 287, 16647, 16919, 703, 33823, 50203, 115723, 50203, 115726, 50203, 116739, 116747, 49947, 114694, 49403, 51387, 641031, 574491, 771103, 738335, 1098779, 1165331, 1083419, 1098779, 1433727, 1110079, 4346523, 154650, 97574, 1, 257]
theorem checked2 : checkTrace blocks trace2=true := by decide +kernel
theorem old2 : phaseClean508 reference 287=some 257 := by decide +kernel
theorem row2 (m n : List Bool) : run candidate m ⟨false,tbN_t8 287⟩=run reference n ⟨false,tbN_t8 287⟩ := by
 have h:=trace_sound blocks 287 [16399, 16413, 16403, 31, 16671, 287, 16647, 16919, 703, 33823, 50203, 115723, 50203, 115726, 50203, 116739, 116747, 49947, 114694, 49403, 51387, 641031, 574491, 771103, 738335, 1098779, 1165331, 1083419, 1098779, 1433727, 1110079, 4346523, 154650, 97574, 1, 257] checked2 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old2 n]
 rfl
def trace3 : List Nat := [287, 16399, 16413, 16403, 31, 16671, 287, 16647, 16919, 703, 33823, 50203, 115723, 50203, 115726, 50203, 116739, 116747, 49947, 114694, 49403, 51387, 641031, 574491, 771103, 738335, 1098779, 1165331, 1083419, 1098779, 1433727, 1110079, 4346523, 154650, 97574, 1, 257]
theorem checked3 : checkTrace blocks trace3=true := by decide +kernel
theorem old3 : phaseClean508 reference 287=some 257 := by decide +kernel
theorem row3 (m n : List Bool) : run candidate m ⟨false,tbN_t8 287⟩=run reference n ⟨false,tbN_t8 287⟩ := by
 have h:=trace_sound blocks 287 [16399, 16413, 16403, 31, 16671, 287, 16647, 16919, 703, 33823, 50203, 115723, 50203, 115726, 50203, 116739, 116747, 49947, 114694, 49403, 51387, 641031, 574491, 771103, 738335, 1098779, 1165331, 1083419, 1098779, 1433727, 1110079, 4346523, 154650, 97574, 1, 257] checked3 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old3 n]
 rfl
def trace4 : List Nat := [284, 16396, 16400, 16400, 28, 16659, 284, 16644, 16916, 700, 33820, 50179, 99331, 50179, 99337, 50179, 116763, 116755, 49923, 65545, 311523, 51203, 100355, 51203, 508935, 476167, 574467, 624643, 559107, 312323, 5357607, 5357607, 217091, 154690, 31803, 4, 260]
theorem checked4 : checkTrace blocks trace4=true := by decide +kernel
theorem old4 : phaseClean508 reference 284=some 260 := by decide +kernel
theorem row4 (m n : List Bool) : run candidate m ⟨false,tbN_t8 284⟩=run reference n ⟨false,tbN_t8 284⟩ := by
 have h:=trace_sound blocks 284 [16396, 16400, 16400, 28, 16659, 284, 16644, 16916, 700, 33820, 50179, 99331, 50179, 99337, 50179, 116763, 116755, 49923, 65545, 311523, 51203, 100355, 51203, 508935, 476167, 574467, 624643, 559107, 312323, 5357607, 5357607, 217091, 154690, 31803, 4, 260] checked4 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old4 n]
 rfl
def trace5 : List Nat := [16668, 32796, 49168, 49176, 16412, 49169, 32796, 49156, 49172, 16412, 65564, 245767, 229403, 114695, 229401, 114695, 229383, 229383, 114695, 196633, 376839, 114855, 229395, 117767, 458791, 458791, 638983, 770054, 737287, 376839, 5293091, 639239, 180263, 5734048, 5603033, 213188, 16132]
theorem checked5 : checkTrace blocks trace5=true := by decide +kernel
theorem old5 : phaseClean508 reference 16668=some 16132 := by decide +kernel
theorem row5 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16668⟩=run reference n ⟨false,tbN_t8 16668⟩ := by
 have h:=trace_sound blocks 16668 [32796, 49168, 49176, 16412, 49169, 32796, 49156, 49172, 16412, 65564, 245767, 229403, 114695, 229401, 114695, 229383, 229383, 114695, 196633, 376839, 114855, 229395, 117767, 458791, 458791, 638983, 770054, 737287, 376839, 5293091, 639239, 180263, 5734048, 5603033, 213188, 16132] checked5 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old5 n]
 rfl
def trace6 : List Nat := [285, 16397, 16405, 16401, 29, 16663, 285, 16645, 16917, 701, 33821, 50187, 117767, 52235, 101388, 52235, 120851, 120859, 51979, 83977, 313579, 55307, 628743, 579595, 1035279, 1002511, 1625099, 1677323, 5806091, 5557259, 1042507, 5763118, 4281226, 89114, 163110, 65539, 515]
theorem checked6 : checkTrace blocks trace6=true := by decide +kernel
theorem old6 : phaseClean508 reference 285=some 515 := by decide +kernel
theorem row6 (m n : List Bool) : run candidate m ⟨false,tbN_t8 285⟩=run reference n ⟨false,tbN_t8 285⟩ := by
 have h:=trace_sound blocks 285 [16397, 16405, 16401, 29, 16663, 285, 16645, 16917, 701, 33821, 50187, 117767, 52235, 101388, 52235, 120851, 120859, 51979, 83977, 313579, 55307, 628743, 579595, 1035279, 1002511, 1625099, 1677323, 5806091, 5557259, 1042507, 5763118, 4281226, 89114, 163110, 65539, 515] checked6 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old6 n]
 rfl
def trace7 : List Nat := [16669, 32829, 49205, 49209, 16573, 49365, 32957, 49317, 49493, 16797, 66205, 246031, 246047, 115343, 229660, 115471, 247063, 247071, 115855, 214297, 378127, 116143, 754967, 642703, 983855, 983855, 1688207, 1819918, 1787151, 1426063, 4580047, 62159, 189165, 5757994, 5749799, 98367, 639]
theorem checked7 : checkTrace blocks trace7=true := by decide +kernel
theorem old7 : phaseClean508 reference 16669=some 639 := by decide +kernel
theorem row7 (m n : List Bool) : run candidate m ⟨false,tbN_t8 16669⟩=run reference n ⟨false,tbN_t8 16669⟩ := by
 have h:=trace_sound blocks 16669 [32829, 49205, 49209, 16573, 49365, 32957, 49317, 49493, 16797, 66205, 246031, 246047, 115343, 229660, 115471, 247063, 247071, 115855, 214297, 378127, 116143, 754967, 642703, 983855, 983855, 1688207, 1819918, 1787151, 1426063, 4580047, 62159, 189165, 5757994, 5749799, 98367, 639] checked7 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old7 n]
 rfl
def trace8 : List Nat := [282, 16394, 16396, 16406, 26, 16393, 26, 16386, 16414, 26, 26, 49170, 98318, 49170, 114698, 49170, 114698, 114690, 49170, 98317, 311314, 49330, 114690, 52242, 507926, 475158, 573458, 622619, 4800530, 4505618, 1753142, 1229878, 21522, 88386, 227643, 65542, 518]
theorem checked8 : checkTrace blocks trace8=true := by decide +kernel
theorem old8 : phaseClean508 reference 282=some 518 := by decide +kernel
theorem row8 (m n : List Bool) : run candidate m ⟨false,tbN_t8 282⟩=run reference n ⟨false,tbN_t8 282⟩ := by
 have h:=trace_sound blocks 282 [16394, 16396, 16406, 26, 16393, 26, 16386, 16414, 26, 26, 49170, 98318, 49170, 114698, 49170, 114698, 114690, 49170, 98317, 311314, 49330, 114690, 52242, 507926, 475158, 573458, 622619, 4800530, 4505618, 1753142, 1229878, 21522, 88386, 227643, 65542, 518] checked8 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old8 n]
 rfl
def trace9 : List Nat := [33050, 65562, 81998, 82014, 98394, 81929, 82010, 65618, 82066, 33882, 148754, 50736, 99884, 181520, 116256, 181776, 100912, 100912, 180752, 98863, 180752, 182800, 117288, 181520, 214032, 1295376, 450832, 117304, 35376, 704784, 1098036, 1098036, 4804656, 614304, 745433, 213190, 15878]
theorem checked9 : checkTrace blocks trace9=true := by decide +kernel
theorem old9 : phaseClean508 reference 33050=some 15878 := by decide +kernel
theorem row9 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33050⟩=run reference n ⟨false,tbN_t8 33050⟩ := by
 have h:=trace_sound blocks 33050 [65562, 81998, 82014, 98394, 81929, 82010, 65618, 82066, 33882, 148754, 50736, 99884, 181520, 116256, 181776, 100912, 100912, 180752, 98863, 180752, 182800, 117288, 181520, 214032, 1295376, 450832, 117304, 35376, 704784, 1098036, 1098036, 4804656, 614304, 745433, 213190, 15878] checked9 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old9 n]
 rfl
def trace10 : List Nat := [283, 16395, 16393, 16407, 27, 16397, 27, 16387, 16415, 27, 27, 49178, 114698, 49178, 114703, 53274, 98330, 98330, 53274, 118797, 315418, 57530, 647174, 584730, 1036318, 1003550, 1626138, 1679379, 1663002, 1363994, 4517978, 1095742, 4332186, 203083, 96575, 65541, 773]
theorem checked10 : checkTrace blocks trace10=true := by decide +kernel
theorem old10 : phaseClean508 reference 283=some 773 := by decide +kernel
theorem row10 (m n : List Bool) : run candidate m ⟨false,tbN_t8 283⟩=run reference n ⟨false,tbN_t8 283⟩ := by
 have h:=trace_sound blocks 283 [16395, 16393, 16407, 27, 16397, 27, 16387, 16415, 27, 27, 49178, 114698, 49178, 114703, 53274, 98330, 98330, 53274, 118797, 315418, 57530, 647174, 584730, 1036318, 1003550, 1626138, 1679379, 1663002, 1363994, 4517978, 1095742, 4332186, 203083, 96575, 65541, 773] checked10 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old10 n]
 rfl
def trace11 : List Nat := [33051, 65595, 82027, 82047, 98555, 82125, 82171, 65779, 82387, 34267, 149395, 51000, 116520, 182168, 116517, 181528, 118560, 118568, 181912, 116527, 182040, 184088, 642860, 706456, 739096, 1820440, 1500056, 1167152, 1085240, 1754008, 387032, 1700604, 4813562, 654634, 630055, 98365, 893]
theorem checked11 : checkTrace blocks trace11=true := by decide +kernel
theorem old11 : phaseClean508 reference 33051=some 893 := by decide +kernel
theorem row11 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33051⟩=run reference n ⟨false,tbN_t8 33051⟩ := by
 have h:=trace_sound blocks 33051 [65595, 82027, 82047, 98555, 82125, 82171, 65779, 82387, 34267, 149395, 51000, 116520, 182168, 116517, 181528, 118560, 118568, 181912, 116527, 182040, 184088, 642860, 706456, 739096, 1820440, 1500056, 1167152, 1085240, 1754008, 387032, 1700604, 4813562, 654634, 630055, 98365, 893] checked11 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old11 n]
 rfl
def trace12 : List Nat := [280, 16392, 16388, 16404, 24, 16385, 24, 16384, 16412, 24, 24, 49154, 98306, 49154, 98312, 49154, 114714, 114706, 49154, 65538, 49154, 49154, 98306, 49154, 245766, 212998, 49154, 114691, 81922, 49154, 49154, 49154, 49154, 1342804, 30762, 65544, 776]
theorem checked12 : checkTrace blocks trace12=true := by decide +kernel
theorem old12 : phaseClean508 reference 280=some 776 := by decide +kernel
theorem row12 (m n : List Bool) : run candidate m ⟨false,tbN_t8 280⟩=run reference n ⟨false,tbN_t8 280⟩ := by
 have h:=trace_sound blocks 280 [16392, 16388, 16404, 24, 16385, 24, 16384, 16412, 24, 24, 49154, 98306, 49154, 98312, 49154, 114714, 114706, 49154, 65538, 49154, 49154, 98306, 49154, 245766, 212998, 49154, 114691, 81922, 49154, 49154, 49154, 49154, 1342804, 30762, 65544, 776] checked12 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old12 n]
 rfl
def trace13 : List Nat := [33048, 65560, 81990, 82012, 98520, 82049, 82136, 65744, 82332, 33272, 148240, 180792, 98856, 180992, 98848, 180608, 116280, 116272, 181504, 67114, 181984, 181920, 99880, 180992, 213504, 1294848, 452352, 99872, 34336, 706304, 1099556, 639552, 6123558, 1933238, 613064, 147656, 15624]
theorem checked13 : checkTrace blocks trace13=true := by decide +kernel
theorem old13 : phaseClean508 reference 33048=some 15624 := by decide +kernel
theorem row13 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33048⟩=run reference n ⟨false,tbN_t8 33048⟩ := by
 have h:=trace_sound blocks 33048 [65560, 81990, 82012, 98520, 82049, 82136, 65744, 82332, 33272, 148240, 180792, 98856, 180992, 98848, 180608, 116280, 116272, 181504, 67114, 181984, 181920, 99880, 180992, 213504, 1294848, 452352, 99872, 34336, 706304, 1099556, 639552, 6123558, 1933238, 613064, 147656, 15624] checked13 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old13 n]
 rfl
def trace14 : List Nat := [281, 16393, 16385, 16405, 25, 16389, 25, 16385, 16413, 25, 25, 49162, 116742, 51210, 100365, 51210, 118802, 127002, 59402, 92162, 59402, 315402, 888838, 839690, 780302, 747534, 1361930, 1429515, 5591050, 5302282, 2021998, 5675567, 4274569, 15177, 162621, 131079, 1031]
theorem checked14 : checkTrace blocks trace14=true := by decide +kernel
theorem old14 : phaseClean508 reference 281=some 1031 := by decide +kernel
theorem row14 (m n : List Bool) : run candidate m ⟨false,tbN_t8 281⟩=run reference n ⟨false,tbN_t8 281⟩ := by
 have h:=trace_sound blocks 281 [16393, 16385, 16405, 25, 16389, 25, 16385, 16413, 25, 25, 49162, 116742, 51210, 100365, 51210, 118802, 127002, 59402, 92162, 59402, 315402, 888838, 839690, 780302, 747534, 1361930, 1429515, 5591050, 5302282, 2021998, 5675567, 4274569, 15177, 162621, 131079, 1031] checked14 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old14 n]
 rfl
def trace15 : List Nat := [33049, 65593, 82019, 82045, 98425, 81989, 82041, 65649, 82141, 32889, 147857, 181040, 115500, 180616, 99109, 180872, 99112, 107304, 188808, 90922, 189416, 443304, 885548, 967048, 745736, 1827080, 1238408, 1409832, 1344296, 1762696, 4576200, 5282732, 6203630, 695161, 760380, 163899, 1147]
theorem checked15 : checkTrace blocks trace15=true := by decide +kernel
theorem old15 : phaseClean508 reference 33049=some 1147 := by decide +kernel
theorem row15 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33049⟩=run reference n ⟨false,tbN_t8 33049⟩ := by
 have h:=trace_sound blocks 33049 [65593, 82019, 82045, 98425, 81989, 82041, 65649, 82141, 32889, 147857, 181040, 115500, 180616, 99109, 180872, 99112, 107304, 188808, 90922, 189416, 443304, 885548, 967048, 745736, 1827080, 1238408, 1409832, 1344296, 1762696, 4576200, 5282732, 6203630, 695161, 760380, 163899, 1147] checked15 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old15 n]
 rfl
def trace16 : List Nat := [278, 16390, 16412, 16390, 22, 16410, 22, 16398, 16390, 22, 22, 32785, 65549, 32785, 81923, 36881, 81929, 81921, 36881, 36865, 299025, 41137, 90121, 44049, 430101, 430101, 561169, 614425, 4792337, 4493329, 1740853, 4443153, 248849, 1536086, 218408, 131082, 1034]
theorem checked16 : checkTrace blocks trace16=true := by decide +kernel
theorem old16 : phaseClean508 reference 278=some 1034 := by decide +kernel
theorem row16 (m n : List Bool) : run candidate m ⟨false,tbN_t8 278⟩=run reference n ⟨false,tbN_t8 278⟩ := by
 have h:=trace_sound blocks 278 [16390, 16412, 16390, 22, 16410, 22, 16398, 16390, 22, 22, 32785, 65549, 32785, 81923, 36881, 81929, 81921, 36881, 36865, 299025, 41137, 90121, 44049, 430101, 430101, 561169, 614425, 4792337, 4493329, 1740853, 4443153, 248849, 1536086, 218408, 131082, 1034] checked16 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old16 n]
 rfl
def trace17 : List Nat := [65814, 131094, 147550, 147534, 163926, 147480, 16470, 606, 147590, 65782, 16702, 164431, 66143, 33079, 82521, 33335, 82511, 90695, 41271, 41555, 41687, 295575, 344659, 295223, 188499, 155731, 295223, 328286, 311895, 41271, 4240183, 5303059, 5958193, 1004726, 1798600, 147658, 15370]
theorem checked17 : checkTrace blocks trace17=true := by decide +kernel
theorem old17 : phaseClean508 reference 65814=some 15370 := by decide +kernel
theorem row17 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65814⟩=run reference n ⟨false,tbN_t8 65814⟩ := by
 have h:=trace_sound blocks 65814 [131094, 147550, 147534, 163926, 147480, 16470, 606, 147590, 65782, 16702, 164431, 66143, 33079, 82521, 33335, 82511, 90695, 41271, 41555, 41687, 295575, 344659, 295223, 188499, 155731, 295223, 328286, 311895, 41271, 4240183, 5303059, 5958193, 1004726, 1798600, 147658, 15370] checked17 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old17 n]
 rfl
def trace18 : List Nat := [279, 16391, 16409, 16391, 23, 16414, 23, 16399, 16391, 23, 23, 32793, 81929, 32793, 81926, 32793, 65561, 65561, 32793, 49153, 294937, 32953, 606221, 560153, 950301, 950301, 1605657, 1654801, 1638425, 1343513, 4497497, 4304921, 4293273, 1388639, 87340, 131081, 1289]
theorem checked18 : checkTrace blocks trace18=true := by decide +kernel
theorem old18 : phaseClean508 reference 279=some 1289 := by decide +kernel
theorem row18 (m n : List Bool) : run candidate m ⟨false,tbN_t8 279⟩=run reference n ⟨false,tbN_t8 279⟩ := by
 have h:=trace_sound blocks 279 [16391, 16409, 16391, 23, 16414, 23, 16399, 16391, 23, 23, 32793, 81929, 32793, 81926, 32793, 65561, 65561, 32793, 49153, 294937, 32953, 606221, 560153, 950301, 950301, 1605657, 1654801, 1638425, 1343513, 4497497, 4304921, 4293273, 1388639, 87340, 131081, 1289] checked18 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old18 n]
 rfl
def trace19 : List Nat := [65815, 131127, 147579, 147567, 164087, 147676, 16631, 767, 147911, 65911, 17343, 164679, 82779, 33727, 82780, 33087, 67423, 67423, 34239, 51027, 34783, 34719, 608087, 558015, 705371, 672603, 1082303, 1115990, 1099615, 1082303, 1419227, 635647, 5845753, 1618041, 1683772, 163897, 1401]
theorem checked19 : checkTrace blocks trace19=true := by decide +kernel
theorem old19 : phaseClean508 reference 65815=some 1401 := by decide +kernel
theorem row19 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65815⟩=run reference n ⟨false,tbN_t8 65815⟩ := by
 have h:=trace_sound blocks 65815 [131127, 147579, 147567, 164087, 147676, 16631, 767, 147911, 65911, 17343, 164679, 82779, 33727, 82780, 33087, 67423, 67423, 34239, 51027, 34783, 34719, 608087, 558015, 705371, 672603, 1082303, 1115990, 1099615, 1082303, 1419227, 635647, 5845753, 1618041, 1683772, 163897, 1401] checked19 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old19 n]
 rfl
def trace20 : List Nat := [276, 16388, 16404, 16388, 20, 16402, 20, 16396, 16388, 20, 20, 32769, 65537, 32769, 65537, 32769, 65537, 65537, 32769, 14, 32769, 32769, 65545, 32769, 163845, 163845, 32769, 65537, 65537, 32769, 32769, 32769, 32769, 1388551, 21553, 131084, 1292]
theorem checked20 : checkTrace blocks trace20=true := by decide +kernel
theorem old20 : phaseClean508 reference 276=some 1292 := by decide +kernel
theorem row20 (m n : List Bool) : run candidate m ⟨false,tbN_t8 276⟩=run reference n ⟨false,tbN_t8 276⟩ := by
 have h:=trace_sound blocks 276 [16388, 16404, 16388, 20, 16402, 20, 16396, 16388, 20, 20, 32769, 65537, 32769, 65537, 32769, 65537, 65537, 32769, 14, 32769, 32769, 65545, 32769, 163845, 163845, 32769, 65537, 65537, 32769, 32769, 32769, 32769, 1388551, 21553, 131084, 1292] checked20 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old20 n]
 rfl
def trace21 : List Nat := [65812, 131092, 147542, 147532, 164052, 147600, 16596, 732, 147848, 66900, 18236, 34375, 67163, 34599, 67161, 34215, 69191, 69191, 34343, 1622, 34343, 36391, 69203, 34599, 181827, 149059, 34599, 85574, 52807, 34599, 34599, 1671747, 5058597, 799461, 1668819, 82124, 15116]
theorem checked21 : checkTrace blocks trace21=true := by decide +kernel
theorem old21 : phaseClean508 reference 65812=some 15116 := by decide +kernel
theorem row21 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65812⟩=run reference n ⟨false,tbN_t8 65812⟩ := by
 have h:=trace_sound blocks 65812 [131092, 147542, 147532, 164052, 147600, 16596, 732, 147848, 66900, 18236, 34375, 67163, 34599, 67161, 34215, 69191, 69191, 34343, 1622, 34343, 36391, 69203, 34599, 181827, 149059, 34599, 85574, 52807, 34599, 34599, 1671747, 5058597, 799461, 1668819, 82124, 15116] checked21 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old21 n]
 rfl
def trace22 : List Nat := [277, 16389, 16401, 16389, 21, 16406, 21, 16397, 16389, 21, 21, 32777, 83973, 34825, 67588, 34825, 69641, 69641, 34825, 18446, 34825, 36873, 593933, 561161, 690189, 690189, 1083401, 1118217, 5312521, 5277705, 6203501, 438280, 4359048, 1454175, 152876, 196619, 1547]
theorem checked22 : checkTrace blocks trace22=true := by decide +kernel
theorem old22 : phaseClean508 reference 277=some 1547 := by decide +kernel
theorem row22 (m n : List Bool) : run candidate m ⟨false,tbN_t8 277⟩=run reference n ⟨false,tbN_t8 277⟩ := by
 have h:=trace_sound blocks 277 [16389, 16401, 16389, 21, 16406, 21, 16397, 16389, 21, 21, 32777, 83973, 34825, 67588, 34825, 69641, 69641, 34825, 18446, 34825, 36873, 593933, 561161, 690189, 690189, 1083401, 1118217, 5312521, 5277705, 6203501, 438280, 4359048, 1454175, 152876, 196619, 1547] checked22 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old22 n]
 rfl
def trace23 : List Nat := [65813, 131125, 147571, 147565, 163957, 147540, 16501, 637, 147657, 66773, 17853, 34639, 83807, 34223, 67420, 34479, 84823, 84831, 33455, 17238, 33583, 35631, 592727, 558511, 705867, 673099, 1082799, 1133390, 1100623, 1082799, 1417675, 1094027, 5051119, 823407, 1815597, 229431, 1655]
theorem checked23 : checkTrace blocks trace23=true := by decide +kernel
theorem old23 : phaseClean508 reference 65813=some 1655 := by decide +kernel
theorem row23 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65813⟩=run reference n ⟨false,tbN_t8 65813⟩ := by
 have h:=trace_sound blocks 65813 [131125, 147571, 147565, 163957, 147540, 16501, 637, 147657, 66773, 17853, 34639, 83807, 34223, 67420, 34479, 84823, 84831, 33455, 17238, 33583, 35631, 592727, 558511, 705867, 673099, 1082799, 1133390, 1100623, 1082799, 1417675, 1094027, 5051119, 823407, 1815597, 229431, 1655] checked23 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old23 n]
 rfl
def trace24 : List Nat := [274, 16386, 16392, 16386, 18, 16392, 18, 16394, 16386, 1042, 1042, 33808, 66572, 33808, 82946, 33808, 67600, 67600, 33552, 32778, 33008, 34992, 83976, 33808, 164884, 164884, 33808, 67609, 4245520, 4228112, 4947984, 4424720, 230416, 1455367, 217393, 196622, 1550]
theorem checked24 : checkTrace blocks trace24=true := by decide +kernel
theorem old24 : phaseClean508 reference 274=some 1550 := by decide +kernel
theorem row24 (m n : List Bool) : run candidate m ⟨false,tbN_t8 274⟩=run reference n ⟨false,tbN_t8 274⟩ := by
 have h:=trace_sound blocks 274 [16386, 16392, 16386, 18, 16392, 18, 16394, 16386, 1042, 1042, 33808, 66572, 33808, 82946, 33808, 67600, 67600, 33552, 32778, 33008, 34992, 83976, 33808, 164884, 164884, 33808, 67609, 4245520, 4228112, 4947984, 4424720, 230416, 1455367, 217393, 196622, 1550] checked24 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old24 n]
 rfl
def trace25 : List Nat := [65810, 131090, 147466, 147466, 163986, 147592, 16530, 666, 147726, 65810, 562, 32848, 65612, 33328, 81984, 33712, 66640, 66640, 33840, 33866, 33840, 33840, 83016, 33328, 164436, 164436, 33328, 83032, 66640, 33328, 33328, 4227696, 4628530, 1184741, 481235, 82126, 14862]
theorem checked25 : checkTrace blocks trace25=true := by decide +kernel
theorem old25 : phaseClean508 reference 65810=some 14862 := by decide +kernel
theorem row25 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65810⟩=run reference n ⟨false,tbN_t8 65810⟩ := by
 have h:=trace_sound blocks 65810 [131090, 147466, 147466, 163986, 147592, 16530, 666, 147726, 65810, 562, 32848, 65612, 33328, 81984, 33712, 66640, 66640, 33840, 33866, 33840, 33840, 83016, 33328, 164436, 164436, 33328, 83032, 66640, 33328, 33328, 4227696, 4628530, 1184741, 481235, 82126, 14862] checked25 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old25 n]
 rfl
def trace26 : List Nat := [275, 16387, 16397, 16387, 19, 16396, 19, 16395, 16387, 1043, 1043, 33816, 82952, 33816, 82951, 37912, 83968, 83976, 37656, 53258, 37112, 43192, 616460, 566296, 693276, 693276, 1086488, 1124369, 1107992, 1086488, 1421436, 4323352, 4311704, 1340686, 86325, 196621, 1805]
theorem checked26 : checkTrace blocks trace26=true := by decide +kernel
theorem old26 : phaseClean508 reference 275=some 1805 := by decide +kernel
theorem row26 (m n : List Bool) : run candidate m ⟨false,tbN_t8 275⟩=run reference n ⟨false,tbN_t8 275⟩ := by
 have h:=trace_sound blocks 275 [16387, 16397, 16387, 19, 16396, 19, 16395, 16387, 1043, 1043, 33816, 82952, 33816, 82951, 37912, 83968, 83976, 37656, 53258, 37112, 43192, 616460, 566296, 693276, 693276, 1086488, 1124369, 1107992, 1086488, 1421436, 4323352, 4311704, 1340686, 86325, 196621, 1805] checked26 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old26 n]
 rfl
def trace27 : List Nat := [65811, 131123, 147503, 147499, 163891, 147532, 16435, 571, 147535, 65683, 179, 33112, 82248, 32952, 82245, 32952, 82240, 82248, 32952, 49482, 33080, 33080, 606540, 557240, 688476, 688476, 1081528, 1130832, 1114456, 1081528, 1418460, 4829624, 4621048, 1225071, 365869, 229429, 1909]
theorem checked27 : checkTrace blocks trace27=true := by decide +kernel
theorem old27 : phaseClean508 reference 65811=some 1909 := by decide +kernel
theorem row27 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65811⟩=run reference n ⟨false,tbN_t8 65811⟩ := by
 have h:=trace_sound blocks 65811 [131123, 147503, 147499, 163891, 147532, 16435, 571, 147535, 65683, 179, 33112, 82248, 32952, 82245, 32952, 82240, 82248, 32952, 49482, 33080, 33080, 606540, 557240, 688476, 688476, 1081528, 1130832, 1114456, 1081528, 1418460, 4829624, 4621048, 1225071, 365869, 229429, 1909] checked27 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old27 n]
 rfl
def trace28 : List Nat := [272, 16384, 16384, 16384, 16, 16384, 16, 16392, 16384, 16, 16, 32768, 65536, 32768, 65536, 32768, 65536, 65536, 32768, 15, 32768, 32768, 65544, 32768, 163844, 163844, 32768, 65536, 65536, 32768, 32768, 32768, 32768, 1388550, 21552, 196624, 1808]
theorem checked28 : checkTrace blocks trace28=true := by decide +kernel
theorem old28 : phaseClean508 reference 272=some 1808 := by decide +kernel
theorem row28 (m n : List Bool) : run candidate m ⟨false,tbN_t8 272⟩=run reference n ⟨false,tbN_t8 272⟩ := by
 have h:=trace_sound blocks 272 [16384, 16384, 16384, 16, 16384, 16, 16392, 16384, 16, 16, 32768, 65536, 32768, 65536, 32768, 65536, 65536, 32768, 15, 32768, 32768, 65544, 32768, 163844, 163844, 32768, 65536, 65536, 32768, 32768, 32768, 32768, 1388550, 21552, 196624, 1808] checked28 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old28 n]
 rfl
def trace29 : List Nat := [65808, 131088, 147458, 147464, 163856, 147456, 16400, 536, 147456, 65712, 48, 163928, 65608, 32800, 65600, 32800, 82008, 82000, 32800, 69, 294944, 32896, 65608, 35872, 426052, 426052, 557088, 606273, 573504, 294944, 5342212, 557344, 5312548, 1053412, 349906, 16592, 14608]
theorem checked29 : checkTrace blocks trace29=true := by decide +kernel
theorem old29 : phaseClean508 reference 65808=some 14608 := by decide +kernel
theorem row29 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65808⟩=run reference n ⟨false,tbN_t8 65808⟩ := by
 have h:=trace_sound blocks 65808 [131088, 147458, 147464, 163856, 147456, 16400, 536, 147456, 65712, 48, 163928, 65608, 32800, 65600, 32800, 82008, 82000, 32800, 69, 294944, 32896, 65608, 35872, 426052, 426052, 557088, 606273, 573504, 294944, 5342212, 557344, 5312548, 1053412, 349906, 16592, 14608] checked29 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old29 n]
 rfl
def trace30 : List Nat := [273, 16385, 16389, 16385, 17, 16388, 17, 16393, 16385, 17, 17, 32776, 83972, 34824, 67589, 34824, 69640, 77832, 43016, 26639, 43016, 299016, 856076, 823304, 698380, 698380, 1345544, 1380360, 1380360, 1091592, 5611116, 5037833, 4386219, 1528620, 153367, 16399, 2063]
theorem checked30 : checkTrace blocks trace30=true := by decide +kernel
theorem old30 : phaseClean508 reference 273=some 2063 := by decide +kernel
theorem row30 (m n : List Bool) : run candidate m ⟨false,tbN_t8 273⟩=run reference n ⟨false,tbN_t8 273⟩ := by
 have h:=trace_sound blocks 273 [16385, 16389, 16385, 17, 16388, 17, 16393, 16385, 17, 17, 32776, 83972, 34824, 67589, 34824, 69640, 77832, 43016, 26639, 43016, 299016, 856076, 823304, 698380, 698380, 1345544, 1380360, 1380360, 1091592, 5611116, 5037833, 4386219, 1528620, 153367, 16399, 2063] checked30 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old30 n]
 rfl
def trace31 : List Nat := [65809, 131121, 147495, 147497, 164017, 147652, 16561, 697, 147777, 65841, 689, 164176, 82252, 33448, 65861, 33576, 66888, 75080, 42152, 25925, 304424, 296328, 853324, 822952, 959308, 959308, 1868456, 1918281, 6079816, 5546664, 5215464, 4972008, 5332172, 1168156, 497174, 49203, 2163]
theorem checked31 : checkTrace blocks trace31=true := by decide +kernel
theorem old31 : phaseClean508 reference 65809=some 2163 := by decide +kernel
theorem row31 (m n : List Bool) : run candidate m ⟨false,tbN_t8 65809⟩=run reference n ⟨false,tbN_t8 65809⟩ := by
 have h:=trace_sound blocks 65809 [131121, 147495, 147497, 164017, 147652, 16561, 697, 147777, 65841, 689, 164176, 82252, 33448, 65861, 33576, 66888, 75080, 42152, 25925, 304424, 296328, 853324, 822952, 959308, 959308, 1868456, 1918281, 6079816, 5546664, 5215464, 4972008, 5332172, 1168156, 497174, 49203, 2163] checked31 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old31 n]
 rfl
def trace32 : List Nat := [46, 14, 24, 18, 14, 283, 270, 270, 534, 686, 33806, 17427, 33807, 17427, 50187, 21523, 34835, 34835, 21267, 102409, 282867, 26643, 59395, 26643, 349203, 381971, 545811, 583707, 4827155, 4477971, 1725495, 1707319, 236595, 1453348, 223506, 16402, 2066]
theorem checked32 : checkTrace blocks trace32=true := by decide +kernel
theorem old32 : phaseClean508 reference 46=some 2066 := by decide +kernel
theorem row32 (m n : List Bool) : run candidate m ⟨false,tbN_t8 46⟩=run reference n ⟨false,tbN_t8 46⟩ := by
 have h:=trace_sound blocks 46 [14, 24, 18, 14, 283, 270, 270, 534, 686, 33806, 17427, 33807, 17427, 50187, 21523, 34835, 34835, 21267, 102409, 282867, 26643, 59395, 26643, 349203, 381971, 545811, 583707, 4827155, 4477971, 1725495, 1707319, 236595, 1453348, 223506, 16402, 2066] checked32 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old32 n]
 rfl
def trace33 : List Nat := [131118, 16414, 26, 26, 32910, 443, 131470, 131470, 826, 131854, 34382, 17555, 33935, 18003, 50313, 18387, 52363, 60547, 26451, 107657, 287859, 281811, 314499, 281171, 353939, 386707, 804435, 838811, 5082259, 4482643, 5928055, 5975351, 4365875, 1453540, 223698, 16594, 14354]
theorem checked33 : checkTrace blocks trace33=true := by decide +kernel
theorem old33 : phaseClean508 reference 131118=some 14354 := by decide +kernel
theorem row33 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131118⟩=run reference n ⟨false,tbN_t8 131118⟩ := by
 have h:=trace_sound blocks 131118 [16414, 26, 26, 32910, 443, 131470, 131470, 826, 131854, 34382, 17555, 33935, 18003, 50313, 18387, 52363, 60547, 26451, 107657, 287859, 281811, 314499, 281171, 353939, 386707, 804435, 838811, 5082259, 4482643, 5928055, 5975351, 4365875, 1453540, 223698, 16594, 14354] checked33 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old33 n]
 rfl
def trace34 : List Nat := [47, 15, 29, 19, 15, 287, 271, 271, 535, 687, 33807, 17435, 50187, 17435, 50190, 17435, 51203, 51211, 17179, 114697, 278779, 18459, 575495, 542747, 869403, 902171, 1590299, 1624083, 1673243, 1328155, 4482139, 1601855, 4313787, 1338669, 92438, 16401, 2321]
theorem checked34 : checkTrace blocks trace34=true := by decide +kernel
theorem old34 : phaseClean508 reference 47=some 2321 := by decide +kernel
theorem row34 (m n : List Bool) : run candidate m ⟨false,tbN_t8 47⟩=run reference n ⟨false,tbN_t8 47⟩ := by
 have h:=trace_sound blocks 47 [15, 29, 19, 15, 287, 271, 271, 535, 687, 33807, 17435, 50187, 17435, 50190, 17435, 51203, 51211, 17179, 114697, 278779, 18459, 575495, 542747, 869403, 902171, 1590299, 1624083, 1673243, 1328155, 4482139, 1601855, 4313787, 1338669, 92438, 16401, 2321] checked34 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old34 n]
 rfl
def trace35 : List Nat := [131119, 16447, 63, 59, 32815, 383, 131375, 131375, 635, 131727, 33999, 17819, 50571, 17627, 50572, 17627, 35227, 35227, 17371, 115081, 278907, 18907, 575879, 542939, 869787, 902555, 1590491, 1624467, 1673627, 1328347, 4482203, 1602047, 4379355, 1567772, 108822, 49201, 2417]
theorem checked35 : checkTrace blocks trace35=true := by decide +kernel
theorem old35 : phaseClean508 reference 131119=some 2417 := by decide +kernel
theorem row35 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131119⟩=run reference n ⟨false,tbN_t8 131119⟩ := by
 have h:=trace_sound blocks 131119 [16447, 63, 59, 32815, 383, 131375, 131375, 635, 131727, 33999, 17819, 50571, 17627, 50572, 17627, 35227, 35227, 17371, 115081, 278907, 18907, 575879, 542939, 869787, 902555, 1590491, 1624467, 1673627, 1328347, 4482203, 1602047, 4379355, 1567772, 108822, 49201, 2417] checked35 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old35 n]
 rfl
def trace36 : List Nat := [44, 12, 16, 16, 12, 275, 268, 268, 532, 684, 33804, 17411, 33795, 17411, 33801, 17411, 51227, 51219, 17155, 65542, 16611, 18595, 34819, 17411, 82947, 115715, 17411, 34819, 100355, 17411, 17411, 5849383, 53283, 1338741, 26635, 16404, 2324]
theorem checked36 : checkTrace blocks trace36=true := by decide +kernel
theorem old36 : phaseClean508 reference 44=some 2324 := by decide +kernel
theorem row36 (m n : List Bool) : run candidate m ⟨false,tbN_t8 44⟩=run reference n ⟨false,tbN_t8 44⟩ := by
 have h:=trace_sound blocks 44 [12, 16, 16, 12, 275, 268, 268, 532, 684, 33804, 17411, 33795, 17411, 33801, 17411, 51227, 51219, 17155, 65542, 16611, 18595, 34819, 17411, 82947, 115715, 17411, 34819, 100355, 17411, 17411, 5849383, 53283, 1338741, 26635, 16404, 2324] checked36 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old36 n]
 rfl
def trace37 : List Nat := [131116, 16412, 18, 24, 32780, 307, 131340, 131340, 564, 131756, 33868, 148635, 33931, 17475, 33929, 17475, 34947, 34947, 17219, 65670, 16483, 18531, 34947, 17475, 83075, 115843, 17475, 51330, 18563, 17475, 17475, 5849447, 5586951, 1396631, 92905, 196820, 14100]
theorem checked37 : checkTrace blocks trace37=true := by decide +kernel
theorem old37 : phaseClean508 reference 131116=some 14100 := by decide +kernel
theorem row37 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131116⟩=run reference n ⟨false,tbN_t8 131116⟩ := by
 have h:=trace_sound blocks 131116 [16412, 18, 24, 32780, 307, 131340, 131340, 564, 131756, 33868, 148635, 33931, 17475, 33929, 17475, 34947, 34947, 17219, 65670, 16483, 18531, 34947, 17475, 83075, 115843, 17475, 51330, 18563, 17475, 17475, 5849447, 5586951, 1396631, 92905, 196820, 14100] checked37 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old37 n]
 rfl
def trace38 : List Nat := [45, 13, 21, 17, 13, 279, 269, 269, 533, 685, 33805, 17419, 52231, 19467, 35852, 19467, 55315, 55323, 19211, 83974, 18667, 22699, 563207, 545803, 609291, 642059, 1068043, 1087499, 5347339, 5262347, 6188143, 6254894, 4379562, 1535277, 157974, 81939, 2579]
theorem checked38 : checkTrace blocks trace38=true := by decide +kernel
theorem old38 : phaseClean508 reference 45=some 2579 := by decide +kernel
theorem row38 (m n : List Bool) : run candidate m ⟨false,tbN_t8 45⟩=run reference n ⟨false,tbN_t8 45⟩ := by
 have h:=trace_sound blocks 45 [13, 21, 17, 13, 279, 269, 269, 533, 685, 33805, 17419, 52231, 19467, 35852, 19467, 55315, 55323, 19211, 83974, 18667, 22699, 563207, 545803, 609291, 642059, 1068043, 1087499, 5347339, 5262347, 6188143, 6254894, 4379562, 1535277, 157974, 81939, 2579] checked38 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old38 n]
 rfl
def trace39 : List Nat := [131117, 16445, 55, 57, 32941, 503, 131501, 131501, 885, 131885, 34509, 148883, 50575, 18123, 34188, 18251, 52627, 52635, 18379, 83334, 17771, 19819, 560519, 542411, 608139, 640907, 1066699, 1101194, 1068427, 1066699, 1401519, 5272239, 5595853, 1436957, 239639, 114735, 2671]
theorem checked39 : checkTrace blocks trace39=true := by decide +kernel
theorem old39 : phaseClean508 reference 131117=some 2671 := by decide +kernel
theorem row39 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131117⟩=run reference n ⟨false,tbN_t8 131117⟩ := by
 have h:=trace_sound blocks 131117 [16445, 55, 57, 32941, 503, 131501, 131501, 885, 131885, 34509, 148883, 50575, 18123, 34188, 18251, 52627, 52635, 18379, 83334, 17771, 19819, 560519, 542411, 608139, 640907, 1066699, 1101194, 1068427, 1066699, 1401519, 5272239, 5595853, 1436957, 239639, 114735, 2671] checked39 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old39 n]
 rfl
def trace40 : List Nat := [42, 10, 12, 22, 10, 9, 10, 10, 30, 10, 10, 16402, 32782, 16402, 49162, 16402, 49162, 49154, 16402, 98306, 16402, 16402, 49154, 16402, 81938, 114706, 16402, 32795, 4210706, 4210706, 4932626, 1721654, 250930, 1534069, 224523, 81942, 2582]
theorem checked40 : checkTrace blocks trace40=true := by decide +kernel
theorem old40 : phaseClean508 reference 42=some 2582 := by decide +kernel
theorem row40 (m n : List Bool) : run candidate m ⟨false,tbN_t8 42⟩=run reference n ⟨false,tbN_t8 42⟩ := by
 have h:=trace_sound blocks 42 [10, 12, 22, 10, 9, 10, 10, 30, 10, 10, 16402, 32782, 16402, 49162, 16402, 49162, 49154, 16402, 98306, 16402, 16402, 49154, 16402, 81938, 114706, 16402, 32795, 4210706, 4210706, 4932626, 1721654, 250930, 1534069, 224523, 81942, 2582] checked40 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old40 n]
 rfl
def trace41 : List Nat := [131114, 16410, 78, 94, 32842, 299, 131402, 131402, 690, 132842, 49474, 148108, 33436, 16724, 49808, 16980, 33428, 33428, 16724, 98970, 17012, 17012, 49816, 16724, 65684, 65684, 16724, 49820, 98964, 16724, 16724, 16724, 6213648, 749207, 2051049, 196822, 13846]
theorem checked41 : checkTrace blocks trace41=true := by decide +kernel
theorem old41 : phaseClean508 reference 131114=some 13846 := by decide +kernel
theorem row41 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131114⟩=run reference n ⟨false,tbN_t8 131114⟩ := by
 have h:=trace_sound blocks 131114 [16410, 78, 94, 32842, 299, 131402, 131402, 690, 132842, 49474, 148108, 33436, 16724, 49808, 16980, 33428, 33428, 16724, 98970, 17012, 17012, 49816, 16724, 65684, 65684, 16724, 49820, 98964, 16724, 16724, 16724, 6213648, 749207, 2051049, 196822, 13846] checked41 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old41 n]
 rfl
def trace42 : List Nat := [43, 11, 9, 23, 11, 13, 11, 11, 31, 11, 11, 16410, 49162, 16410, 49167, 20506, 32794, 32794, 20506, 118786, 20506, 24602, 581638, 548890, 610330, 643098, 1069082, 1089555, 1073178, 1069082, 1406078, 1587518, 4299450, 1386620, 93455, 81941, 2837]
theorem checked42 : checkTrace blocks trace42=true := by decide +kernel
theorem old42 : phaseClean508 reference 43=some 2837 := by decide +kernel
theorem row42 (m n : List Bool) : run candidate m ⟨false,tbN_t8 43⟩=run reference n ⟨false,tbN_t8 43⟩ := by
 have h:=trace_sound blocks 43 [11, 9, 23, 11, 13, 11, 11, 31, 11, 11, 16410, 49162, 16410, 49167, 20506, 32794, 32794, 20506, 118786, 20506, 24602, 581638, 548890, 610330, 643098, 1069082, 1089555, 1073178, 1069082, 1406078, 1587518, 4299450, 1386620, 93455, 81941, 2837] checked42 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old42 n]
 rfl
def trace43 : List Nat := [131115, 16443, 107, 127, 33003, 495, 131563, 131563, 1011, 132971, 50115, 148356, 50072, 17372, 50069, 16732, 51076, 51084, 17884, 116634, 18300, 18300, 575388, 541660, 590748, 590748, 1065948, 1099668, 1148828, 1065948, 1402808, 619164, 6222554, 773149, 1935639, 114733, 2925]
theorem checked43 : checkTrace blocks trace43=true := by decide +kernel
theorem old43 : phaseClean508 reference 131115=some 2925 := by decide +kernel
theorem row43 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131115⟩=run reference n ⟨false,tbN_t8 131115⟩ := by
 have h:=trace_sound blocks 131115 [16443, 107, 127, 33003, 495, 131563, 131563, 1011, 132971, 50115, 148356, 50072, 17372, 50069, 16732, 51076, 51084, 17884, 116634, 18300, 18300, 575388, 541660, 590748, 590748, 1065948, 1099668, 1148828, 1065948, 1402808, 619164, 6222554, 773149, 1935639, 114733, 2925] checked43 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old43 n]
 rfl
def trace44 : List Nat := [40, 8, 4, 20, 8, 1, 8, 8, 28, 8, 8, 16386, 32770, 16386, 32776, 16386, 49178, 49170, 16386, 65549, 278530, 16546, 32770, 19458, 344066, 376834, 540674, 573443, 540674, 278530, 5325862, 540930, 213026, 150627, 27674, 81944, 2840]
theorem checked44 : checkTrace blocks trace44=true := by decide +kernel
theorem old44 : phaseClean508 reference 40=some 2840 := by decide +kernel
theorem row44 (m n : List Bool) : run candidate m ⟨false,tbN_t8 40⟩=run reference n ⟨false,tbN_t8 40⟩ := by
 have h:=trace_sound blocks 40 [8, 4, 20, 8, 1, 8, 8, 28, 8, 8, 16386, 32770, 16386, 32776, 16386, 49178, 49170, 16386, 65549, 278530, 16546, 32770, 19458, 344066, 376834, 540674, 573443, 540674, 278530, 5325862, 540930, 213026, 150627, 27674, 81944, 2840] checked44 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old44 n]
 rfl
def trace45 : List Nat := [131112, 16408, 70, 92, 32968, 419, 131528, 131528, 956, 131912, 51008, 18052, 34456, 18244, 34448, 17860, 52892, 52884, 17988, 67231, 18052, 20164, 36504, 18244, 67204, 67204, 18244, 36484, 102020, 18244, 18244, 1655328, 4911110, 2051713, 1920760, 131288, 13592]
theorem checked45 : checkTrace blocks trace45=true := by decide +kernel
theorem old45 : phaseClean508 reference 131112=some 13592 := by decide +kernel
theorem row45 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131112⟩=run reference n ⟨false,tbN_t8 131112⟩ := by
 have h:=trace_sound blocks 131112 [16408, 70, 92, 32968, 419, 131528, 131528, 956, 131912, 51008, 18052, 34456, 18244, 34448, 17860, 52892, 52884, 17988, 67231, 18052, 20164, 36504, 18244, 67204, 67204, 18244, 36484, 102020, 18244, 18244, 1655328, 4911110, 2051713, 1920760, 131288, 13592] checked45 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old45 n]
 rfl
def trace46 : List Nat := [41, 9, 1, 21, 9, 5, 9, 9, 29, 9, 9, 16394, 51206, 18442, 34829, 18442, 53266, 61466, 26634, 92173, 288778, 282794, 823302, 809994, 878602, 911370, 1853450, 1888267, 6049802, 5531658, 5201482, 6167343, 4372905, 1444478, 159501, 147479, 3095]
theorem checked46 : checkTrace blocks trace46=true := by decide +kernel
theorem old46 : phaseClean508 reference 41=some 3095 := by decide +kernel
theorem row46 (m n : List Bool) : run candidate m ⟨false,tbN_t8 41⟩=run reference n ⟨false,tbN_t8 41⟩ := by
 have h:=trace_sound blocks 41 [9, 1, 21, 9, 5, 9, 9, 29, 9, 9, 16394, 51206, 18442, 34829, 18442, 53266, 61466, 26634, 92173, 288778, 282794, 823302, 809994, 878602, 911370, 1853450, 1888267, 6049802, 5531658, 5201482, 6167343, 4372905, 1444478, 159501, 147479, 3095] checked46 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old46 n]
 rfl
def trace47 : List Nat := [131113, 16441, 99, 125, 32873, 359, 131433, 131433, 765, 131785, 50625, 18316, 51100, 17868, 34709, 18124, 35724, 43916, 25292, 91039, 25484, 281548, 822172, 804300, 599436, 599436, 1328588, 1346444, 1411980, 1074636, 5591976, 4201420, 4794574, 567886, 2067980, 180267, 3179]
theorem checked47 : checkTrace blocks trace47=true := by decide +kernel
theorem old47 : phaseClean508 reference 131113=some 3179 := by decide +kernel
theorem row47 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131113⟩=run reference n ⟨false,tbN_t8 131113⟩ := by
 have h:=trace_sound blocks 131113 [16441, 99, 125, 32873, 359, 131433, 131433, 765, 131785, 50625, 18316, 51100, 17868, 34709, 18124, 35724, 43916, 25292, 91039, 25484, 281548, 822172, 804300, 599436, 599436, 1328588, 1346444, 1411980, 1074636, 5591976, 4201420, 4794574, 567886, 2067980, 180267, 3179] checked47 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old47 n]
 rfl
def trace48 : List Nat := [38, 6, 28, 6, 6, 26, 6, 6, 6, 6, 6, 17, 13, 17, 16387, 4113, 16393, 16385, 4113, 36878, 4113, 8209, 24585, 8209, 4113, 4113, 4113, 24601, 4202513, 4198417, 4920337, 4934929, 19505, 82273, 213272, 147482, 3098]
theorem checked48 : checkTrace blocks trace48=true := by decide +kernel
theorem old48 : phaseClean508 reference 38=some 3098 := by decide +kernel
theorem row48 (m n : List Bool) : run candidate m ⟨false,tbN_t8 38⟩=run reference n ⟨false,tbN_t8 38⟩ := by
 have h:=trace_sound blocks 38 [6, 28, 6, 6, 26, 6, 6, 6, 6, 6, 17, 13, 17, 16387, 4113, 16393, 16385, 4113, 36878, 4113, 8209, 24585, 8209, 4113, 4113, 4113, 24601, 4202513, 4198417, 4920337, 4934929, 19505, 82273, 213272, 147482, 3098] checked48 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old48 n]
 rfl
def trace49 : List Nat := [131110, 16406, 94, 78, 32838, 56, 131142, 131142, 166, 131142, 16718, 131727, 671, 343, 17049, 599, 17039, 25223, 8535, 41622, 8823, 262775, 279187, 262487, 24727, 57495, 262487, 262814, 377495, 8535, 4207447, 5270387, 6122001, 1926529, 2057720, 131290, 13338]
theorem checked49 : checkTrace blocks trace49=true := by decide +kernel
theorem old49 : phaseClean508 reference 131110=some 13338 := by decide +kernel
theorem row49 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131110⟩=run reference n ⟨false,tbN_t8 131110⟩ := by
 have h:=trace_sound blocks 131110 [16406, 94, 78, 32838, 56, 131142, 131142, 166, 131142, 16718, 131727, 671, 343, 17049, 599, 17039, 25223, 8535, 41622, 8823, 262775, 279187, 262487, 24727, 57495, 262487, 262814, 377495, 8535, 4207447, 5270387, 6122001, 1926529, 2057720, 131290, 13338] checked49 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old49 n]
 rfl
def trace50 : List Nat := [39, 7, 25, 7, 7, 30, 7, 7, 7, 7, 7, 25, 16393, 25, 16390, 25, 25, 25, 25, 49166, 25, 25, 540685, 524313, 524313, 524313, 1048601, 1064977, 1048601, 1048601, 1385597, 4796697, 4326073, 196968, 82204, 147481, 3353]
theorem checked50 : checkTrace blocks trace50=true := by decide +kernel
theorem old50 : phaseClean508 reference 39=some 3353 := by decide +kernel
theorem row50 (m n : List Bool) : run candidate m ⟨false,tbN_t8 39⟩=run reference n ⟨false,tbN_t8 39⟩ := by
 have h:=trace_sound blocks 39 [7, 25, 7, 7, 30, 7, 7, 7, 7, 7, 25, 16393, 25, 16390, 25, 25, 25, 25, 49166, 25, 25, 540685, 524313, 524313, 524313, 1048601, 1064977, 1048601, 1048601, 1385597, 4796697, 4326073, 196968, 82204, 147481, 3353] checked50 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old50 n]
 rfl
def trace51 : List Nat := [131111, 16439, 123, 111, 32999, 252, 131303, 131303, 487, 131527, 17359, 131975, 17307, 991, 17308, 351, 1951, 1951, 1503, 51094, 1919, 1919, 542615, 525279, 541599, 574367, 1049567, 1050518, 1165215, 1049567, 1386427, 602783, 6206169, 688462, 1942796, 180265, 3433]
theorem checked51 : checkTrace blocks trace51=true := by decide +kernel
theorem old51 : phaseClean508 reference 131111=some 3433 := by decide +kernel
theorem row51 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131111⟩=run reference n ⟨false,tbN_t8 131111⟩ := by
 have h:=trace_sound blocks 131111 [16439, 123, 111, 32999, 252, 131303, 131303, 487, 131527, 17359, 131975, 17307, 991, 17308, 351, 1951, 1951, 1503, 51094, 1919, 1919, 542615, 525279, 541599, 574367, 1049567, 1050518, 1165215, 1049567, 1386427, 602783, 6206169, 688462, 1942796, 180265, 3433] checked51 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old51 n]
 rfl
def trace52 : List Nat := [36, 4, 20, 4, 4, 18, 4, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 262145, 161, 9, 3073, 262145, 262145, 524289, 524289, 524289, 262145, 5309477, 524545, 196641, 196912, 16385, 147484, 3356]
theorem checked52 : checkTrace blocks trace52=true := by decide +kernel
theorem old52 : phaseClean508 reference 36=some 3356 := by decide +kernel
theorem row52 (m n : List Bool) : run candidate m ⟨false,tbN_t8 36⟩=run reference n ⟨false,tbN_t8 36⟩ := by
 have h:=trace_sound blocks 36 [4, 20, 4, 4, 18, 4, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 262145, 161, 9, 3073, 262145, 262145, 524289, 524289, 524289, 262145, 5309477, 524545, 196641, 196912, 16385, 147484, 3356] checked52 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old52 n]
 rfl
def trace53 : List Nat := [131108, 16404, 86, 76, 32964, 176, 131268, 131268, 424, 132580, 18252, 1671, 1691, 1863, 1689, 1479, 3719, 3719, 1607, 1683, 1671, 3783, 3731, 1863, 18055, 50823, 1863, 20102, 118407, 1863, 1863, 1638947, 4894725, 1967058, 1925859, 65756, 13084]
theorem checked53 : checkTrace blocks trace53=true := by decide +kernel
theorem old53 : phaseClean508 reference 131108=some 13084 := by decide +kernel
theorem row53 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131108⟩=run reference n ⟨false,tbN_t8 131108⟩ := by
 have h:=trace_sound blocks 131108 [16404, 86, 76, 32964, 176, 131268, 131268, 424, 132580, 18252, 1671, 1691, 1863, 1689, 1479, 3719, 3719, 1607, 1683, 1671, 3783, 3731, 1863, 18055, 50823, 1863, 20102, 118407, 1863, 1863, 1638947, 4894725, 1967058, 1925859, 65756, 13084] checked53 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old53 n]
 rfl
def trace54 : List Nat := [37, 5, 17, 5, 5, 22, 5, 5, 5, 5, 5, 9, 18437, 2057, 2052, 2057, 4105, 4105, 2057, 18433, 264201, 4265, 528397, 531465, 788489, 788489, 1574921, 1576969, 5771273, 5507081, 994377, 930056, 4260776, 360, 147740, 213019, 3611]
theorem checked54 : checkTrace blocks trace54=true := by decide +kernel
theorem old54 : phaseClean508 reference 37=some 3611 := by decide +kernel
theorem row54 (m n : List Bool) : run candidate m ⟨false,tbN_t8 37⟩=run reference n ⟨false,tbN_t8 37⟩ := by
 have h:=trace_sound blocks 37 [5, 17, 5, 5, 22, 5, 5, 5, 5, 5, 9, 18437, 2057, 2052, 2057, 4105, 4105, 2057, 18433, 264201, 4265, 528397, 531465, 788489, 788489, 1574921, 1576969, 5771273, 5507081, 994377, 930056, 4260776, 360, 147740, 213019, 3611] checked54 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old54 n]
 rfl
def trace55 : List Nat := [131109, 16437, 115, 109, 32869, 116, 131173, 131173, 233, 132197, 17869, 1935, 18335, 1487, 1948, 1743, 19351, 19359, 719, 17299, 911, 3023, 527255, 525775, 542095, 574863, 1050063, 1067918, 1166223, 1050063, 1384875, 1061355, 4887247, 2007384, 2072605, 245799, 3687]
theorem checked55 : checkTrace blocks trace55=true := by decide +kernel
theorem old55 : phaseClean508 reference 131109=some 3687 := by decide +kernel
theorem row55 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131109⟩=run reference n ⟨false,tbN_t8 131109⟩ := by
 have h:=trace_sound blocks 131109 [16437, 115, 109, 32869, 116, 131173, 131173, 233, 132197, 17869, 1935, 18335, 1487, 1948, 1743, 19351, 19359, 719, 17299, 911, 3023, 527255, 525775, 542095, 574863, 1050063, 1067918, 1166223, 1050063, 1384875, 1061355, 4887247, 2007384, 2072605, 245799, 3687] checked55 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old55 n]
 rfl
def trace56 : List Nat := [34, 2, 8, 2, 2, 8, 2, 2, 2, 1026, 1026, 1040, 1036, 1040, 17410, 1040, 2064, 2064, 784, 32773, 262384, 2064, 18440, 2064, 263184, 263184, 525328, 526361, 4835344, 4457488, 1705012, 4916496, 1072, 1072, 214273, 213022, 3614]
theorem checked56 : checkTrace blocks trace56=true := by decide +kernel
theorem old56 : phaseClean508 reference 34=some 3614 := by decide +kernel
theorem row56 (m n : List Bool) : run candidate m ⟨false,tbN_t8 34⟩=run reference n ⟨false,tbN_t8 34⟩ := by
 have h:=trace_sound blocks 34 [2, 8, 2, 2, 8, 2, 2, 2, 1026, 1026, 1040, 1036, 1040, 17410, 1040, 2064, 2064, 784, 32773, 262384, 2064, 18440, 2064, 263184, 263184, 525328, 526361, 4835344, 4457488, 1705012, 4916496, 1072, 1072, 214273, 213022, 3614] checked56 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old56 n]
 rfl
def trace57 : List Nat := [131106, 16402, 10, 10, 32898, 168, 131202, 131202, 302, 131490, 578, 144, 140, 592, 16512, 976, 1168, 1168, 1104, 33935, 1168, 1232, 17544, 592, 656, 656, 592, 17560, 1168, 592, 592, 4194832, 4268050, 8914, 213987, 65758, 12830]
theorem checked57 : checkTrace blocks trace57=true := by decide +kernel
theorem old57 : phaseClean508 reference 131106=some 12830 := by decide +kernel
theorem row57 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131106⟩=run reference n ⟨false,tbN_t8 131106⟩ := by
 have h:=trace_sound blocks 131106 [16402, 10, 10, 32898, 168, 131202, 131202, 302, 131490, 578, 144, 140, 592, 16512, 976, 1168, 1168, 1104, 33935, 1168, 1232, 17544, 592, 656, 656, 592, 17560, 1168, 592, 592, 4194832, 4268050, 8914, 213987, 65758, 12830] checked57 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old57 n]
 rfl
def trace58 : List Nat := [35, 3, 13, 3, 3, 12, 3, 3, 3, 1027, 1027, 1048, 17416, 1048, 17415, 5144, 18432, 18440, 4888, 53253, 266488, 10264, 550924, 534552, 791576, 791576, 1578008, 1583121, 1697816, 1315864, 4469848, 4815128, 4344504, 148537, 83205, 213021, 3869]
theorem checked58 : checkTrace blocks trace58=true := by decide +kernel
theorem old58 : phaseClean508 reference 35=some 3869 := by decide +kernel
theorem row58 (m n : List Bool) : run candidate m ⟨false,tbN_t8 35⟩=run reference n ⟨false,tbN_t8 35⟩ := by
 have h:=trace_sound blocks 35 [3, 13, 3, 3, 12, 3, 3, 3, 1027, 1027, 1048, 17416, 1048, 17415, 5144, 18432, 18440, 4888, 53253, 266488, 10264, 550924, 534552, 791576, 791576, 1578008, 1583121, 1697816, 1315864, 4469848, 4815128, 4344504, 148537, 83205, 213021, 3869] checked58 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old58 n]
 rfl
def trace59 : List Nat := [131107, 16435, 47, 43, 32803, 108, 131107, 131107, 111, 131107, 195, 408, 16776, 216, 16773, 216, 16768, 16776, 216, 49551, 408, 472, 541068, 524504, 524696, 524696, 1048792, 1065360, 1048984, 1048792, 1385660, 4796888, 4260568, 32856, 98589, 245797, 3941]
theorem checked59 : checkTrace blocks trace59=true := by decide +kernel
theorem old59 : phaseClean508 reference 131107=some 3941 := by decide +kernel
theorem row59 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131107⟩=run reference n ⟨false,tbN_t8 131107⟩ := by
 have h:=trace_sound blocks 131107 [16435, 47, 43, 32803, 108, 131107, 131107, 111, 131107, 195, 408, 16776, 216, 16773, 216, 16768, 16776, 216, 49551, 408, 472, 541068, 524504, 524696, 524696, 1048792, 1065360, 1048984, 1048792, 1385660, 4796888, 4260568, 32856, 98589, 245797, 3941] checked59 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old59 n]
 rfl
def trace60 : List Nat := [32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213024, 3872]
theorem checked60 : checkTrace blocks trace60=true := by decide +kernel
theorem old60 : phaseClean508 reference 32=some 3872 := by decide +kernel
theorem row60 (m n : List Bool) : run candidate m ⟨false,tbN_t8 32⟩=run reference n ⟨false,tbN_t8 32⟩ := by
 have h:=trace_sound blocks 32 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213024, 3872] checked60 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old60 n]
 rfl
def trace61 : List Nat := [131104, 16400, 2, 8, 32768, 32, 131072, 131072, 32, 131072, 64, 131224, 136, 64, 128, 64, 16536, 16528, 64, 128, 128, 192, 128, 64, 128, 128, 64, 16513, 114816, 64, 64, 64, 5607460, 74466, 66274, 224, 12576]
theorem checked61 : checkTrace blocks trace61=true := by decide +kernel
theorem old61 : phaseClean508 reference 131104=some 12576 := by decide +kernel
theorem row61 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131104⟩=run reference n ⟨false,tbN_t8 131104⟩ := by
 have h:=trace_sound blocks 131104 [16400, 2, 8, 32768, 32, 131072, 131072, 32, 131072, 64, 131224, 136, 64, 128, 64, 16536, 16528, 64, 128, 128, 192, 128, 64, 128, 128, 64, 16513, 114816, 64, 64, 64, 5607460, 74466, 66274, 224, 12576] checked61 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old61 n]
 rfl
def trace62 : List Nat := [33, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 8, 18436, 2056, 2053, 2056, 4104, 12296, 10248, 26624, 10248, 266248, 266244, 266248, 10248, 10248, 264200, 266248, 266248, 10248, 4209160, 355849, 28427, 90715, 148327, 95, 4127]
theorem checked62 : checkTrace blocks trace62=true := by decide +kernel
theorem old62 : phaseClean508 reference 33=some 4127 := by decide +kernel
theorem row62 (m n : List Bool) : run candidate m ⟨false,tbN_t8 33⟩=run reference n ⟨false,tbN_t8 33⟩ := by
 have h:=trace_sound blocks 33 [1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 8, 18436, 2056, 2053, 2056, 4104, 12296, 10248, 26624, 10248, 266248, 266244, 266248, 10248, 10248, 264200, 266248, 266248, 10248, 4209160, 355849, 28427, 90715, 148327, 95, 4127] checked62 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old62 n]
 rfl
def trace63 : List Nat := [131105, 16433, 39, 41, 32929, 228, 131233, 131233, 353, 131457, 705, 131472, 16780, 712, 389, 840, 1416, 9608, 9416, 25984, 9608, 263624, 263556, 262856, 9096, 9096, 262856, 279945, 4572552, 4203208, 734408, 683400, 1564268, 254571, 229990, 32867, 4195]
theorem checked63 : checkTrace blocks trace63=true := by decide +kernel
theorem old63 : phaseClean508 reference 131105=some 4195 := by decide +kernel
theorem row63 (m n : List Bool) : run candidate m ⟨false,tbN_t8 131105⟩=run reference n ⟨false,tbN_t8 131105⟩ := by
 have h:=trace_sound blocks 131105 [16433, 39, 41, 32929, 228, 131233, 131233, 353, 131457, 705, 131472, 16780, 712, 389, 840, 1416, 9608, 9416, 25984, 9608, 263624, 263556, 262856, 9096, 9096, 262856, 279945, 4572552, 4203208, 734408, 683400, 1564268, 254571, 229990, 32867, 4195] checked63 m
 change run candidate m _ = _ at h
 rw [h,checked_run reference _ _ old63 n]
 rfl
def trace64 : List Nat := [49432, 114696, 114758, 114772, 114776, 114947, 115032, 98640, 115344, 49912, 247056, 247332, 230968, 247044, 230962, 247300, 248380, 248372, 246276, 197178, 246276, 248324, 231992, 247044, 230432, 230432, 247044, 248357, 215588, 247044, 247044, 5947424, 4739076, 4808020, 6117418, 8, 264]
theorem checked64 : checkTrace blocks trace64=true := by decide +kernel
theorem old64 : phaseClean508 reference 49432=some 264 := by decide +kernel

end ECDSAAdd.Entrant.CompactInverse14
end
end
end
end
end
end

end
end
