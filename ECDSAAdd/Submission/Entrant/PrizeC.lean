import ECDSAAdd.Framework.Cost
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Math.SkywalkTrace
import ECDSAAdd.Submission.Entrant.MainPart07Core
import ECDSAAdd.Submission.Entrant.PrizeA
import ECDSAAdd.Submission.Entrant.PrizeB
import ECDSAAdd.Submission.Entrant.Prelude
import ECDSAAdd.Submission.Entrant.DeadCarry
import ECDSAAdd.Submission.Entrant.QTop

-- repack: PrizeTail10d9efffc lines 19120..22692
section
section
namespace ECDSAAdd.Entrant.StairPacket.Leave240FullArithmetic
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step
theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z))) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let out:=run program m s
    out.phase=s.phase ∧ regValue smallM out.basis=(mag/2^137)%2^11 ∧
    out.basis 1556=decide (2^136≤mag) ∧ (∀i<120,out.basis (live i)=(Leave240TrueMiddle.F z).testBit i) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  have front:=Leave240Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave240FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 120,105 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave240Hit.swaps i):=by decide +kernel
  have used:=Leave240Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave240EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave240EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave240RoutedRestore.result z sg a n (n.drop (measurementCount Leave240Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take]
  exact ⟨restored.1.trans (used.1.trans front.1),restored.2.2.1,restored.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave240FullArithmetic

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240RecordedParity
open Arithmetic IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem result (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^136) (odd : z.v % 2 = 1)
    (record : readCells (shape 11) 0 15 (mappedBasis 11 s.basis) =
      SkywalkTrace.trace 15 (encode g sg z.u z.v)) :
    Leave240EntryAction.oddRead s.basis = oddBits (letters 15 (Shadow.reduced 136 15 z)) := by
  have ports : Leave240EntryAction.oddRead s.basis =
      (readCells (shape 11) 0 15 (mappedBasis 11 s.basis)).map (fun pair => !pair.1) := by rfl
  rw [ports,record,←true_records 136 z small odd g sg]
  exact LeaveTraceLetters.parity _ _ _ _ (shadow_odd _ _ small odd)

end ECDSAAdd.Entrant.StairPacket.Leave240RecordedParity

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FrontPrepare
open Arithmetic Partial RecordedQuantum PortalValues LeaveCompanion LeaveCompanion255
open Leave255Front Leave255FrontReady LeaveSelector Leave255Selector Leave255Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem prepare (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (zero:∀q∈watched,s.basis q=false) (k:Mode) (smallU:Nat)
    (mode:k=farMode ((run entry m s).basis 1706) ((run entry m s).basis 1707) smallU)
    (exchange:right k=true → ∀i<15,i≤key k → (run entry m s).basis (swaps i)=decide (i=key k)) :
    let a:=run entry m s
    run (entry++fullPrefix false) m s=⟨a.phase,fun q=>(sim Leave255Selector.prepare (LeaveSelector.start ports false k) q).read a.basis⟩ := by
  let a:=run entry m s
  have keep:=Leave255FrontReady.frame s m z G sg small ready fresh scratch temp
  have clear (q:Wire) (h:q∈watched) : a.basis q=false := (keep q h).trans (zero q h)
  have cells (q:Nat) (lo:1561≤q) (hi:q≤1597) : q∈watched := by
    unfold watched
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q-1559,by omega,by omega⟩
  rw [run_append,run_take]
  apply preparedState false a _ a.basis smallU k mode (clear _ (by decide)) (clear _ (by decide))
  · exact beforeFresh ports k a.basis (fun q lo hi=>clear q (cells q lo hi)) (clear _ (by decide)) (clear _ (by decide))
  · exact exchange

end ECDSAAdd.Entrant.StairPacket.Leave255FrontPrepare

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FullArithmetic
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program:=leave255.take 2573
theorem shape : program=entry++(Leave255Routed.body++restore) := by decide +kernel
def unmodified (q:Wire) := q∉entry.map destination
instance (q:Wire):Decidable (unmodified q) := inferInstanceAs (Decidable (q∉_))
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z))) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let out:=run program m s
    out.phase=s.phase ∧ regValue smallM out.basis=(mag/2^130)%2^10 ∧
    out.basis 1556=decide (2^129≤mag) ∧ (∀i<127,out.basis (live i)=(Leave255TrueMiddle.F z).testBit i) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  have front:=Leave255Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave255FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 127,112 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave255Hit.swaps i):=by decide +kernel
  have used:=Leave255Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave255EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave255EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave255RoutedRestore.result z sg a n (n.drop (measurementCount Leave255Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take]
  exact ⟨restored.1.trans (used.1.trans front.1),restored.2.2.1,restored.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave255FullArithmetic

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255RecordedParity
open Arithmetic IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem result (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^129) (odd : z.v % 2 = 1)
    (record : readCells (shape 12) 0 15 (mappedBasis 12 s.basis) =
      SkywalkTrace.trace 15 (encode g sg z.u z.v)) :
    Leave255EntryAction.oddRead s.basis = oddBits (letters 15 (Shadow.reduced 129 15 z)) := by
  have ports : Leave255EntryAction.oddRead s.basis =
      (readCells (shape 12) 0 15 (mappedBasis 12 s.basis)).map (fun pair => !pair.1) := by rfl
  rw [ports,record,←true_records 129 z small odd g sg]
  exact LeaveTraceLetters.parity _ _ _ _ (shadow_odd _ _ small odd)

end ECDSAAdd.Entrant.StairPacket.Leave255RecordedParity

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket ArchivePortAction
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000
attribute [local irreducible] run routed measurementCount
theorem after_encoded (j:Fin 23) (P:Program) (outPorts:Ports) (d:Bool) (row:Nat) (src:State) (m:List Bool)
    (final:Frame outPorts (code d) row (run P (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m src)))
    (i:Fin 157) (hi:16 ≤ i.val) (q:Wire) (slot:outPorts i=q) (free:¬MayTouch j (windowNet j q)) :
    (run (body j P) m src).basis q=false:=by
  simp only [body,run_append,run_take]
  apply (route_outside j 1 14 (by decide) q (named_range j 1 14 q (by decide) free) _ _).trans
  rw [←slot,final,archive_blank _ _ hi,Nat.zero_testBit]
namespace NativePack240
open ArchiveBoundary240
theorem popped (d:Bool) (src:State) (m:List Bool) (row:Nat)
    (frame:Frame codePorts (code d) row (run (withArchive d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m src))) :
    ∀k:Fin 3,(run (body idx (withArchive d)) m src).basis (1716+k.val)=false:=by
  have phys:∀k:Fin 3,codePorts ⟨154+k.val,by omega⟩=1716+k.val ∧ ¬MayTouch idx (windowNet idx (1716+k.val)):=by decide +kernel
  intro k
  exact after_encoded idx (withArchive d) codePorts d row src m frame ⟨154+k.val,by omega⟩ (by dsimp;omega) _
    (phys k).1 (phys k).2
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem popped (d:Bool) (src:State) (m:List Bool) (row:Nat)
    (frame:Frame codePorts (code d) row (run (withArchive d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m src))) :
    ∀k:Fin 3,(run (body idx (withArchive d)) m src).basis (1709+k.val)=false:=by
  have phys:∀k:Fin 3,codePorts ⟨154+k.val,by omega⟩=1709+k.val ∧ ¬MayTouch idx (windowNet idx (1709+k.val)):=by decide +kernel
  intro k
  exact after_encoded idx (withArchive d) codePorts d row src m frame ⟨154+k.val,by omega⟩ (by dsimp;omega) _
    (phys k).1 (phys k).2
end NativePack255
#print axioms NativePack255.popped
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
attribute [local irreducible] run routed measurementCount body
theorem from_append {P Q:Program} {s:State} {t:List Bool} {prop:State→Prop}
    (after:prop (run Q (t.drop (measurementCount P)) (run P t s))) : prop (run (P++Q) t s):=by
  rwa [run_append,run_take]
namespace NativePack240
open ArchiveBoundary240
theorem archive_result (d:Bool) (row:Nat) (lim:row<63145) (s:State) (m:List Bool)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) m s)) :
    Frame codePorts (code d) row (run (withArchive d) m s) :=
  from_append (prop:=Frame codePorts (code d) row)
    (load_run d row lim _ (m.drop (measurementCount (program d))) raw).2.1
theorem receipt (d:Bool) (s:State) (m:List Bool) (row:Nat) (lim:row<63145)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m s))) :
    Kept codePorts d row (run (body idx (withArchive d)) m s) ∧
      ∀k:Fin 3,(run (body idx (withArchive d)) m s).basis (1716+k.val)=false:=by
  have frame:=archive_result d row lim _ _ raw
  exact ⟨body_keeps idx (withArchive d) codePorts d row s m encoded_outside frame,popped d s m row frame⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem archive_result (d:Bool) (row:Nat) (lim:row<63145) (s:State) (m:List Bool)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) m s)) :
    Frame codePorts (code d) row (run (withArchive d) m s) :=
  from_append (prop:=Frame codePorts (code d) row)
    (load_run d row lim _ (m.drop (measurementCount (program d))) raw).2.1
theorem receipt (d:Bool) (s:State) (m:List Bool) (row:Nat) (lim:row<63145)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m s))) :
    Kept codePorts d row (run (body idx (withArchive d)) m s) ∧
      ∀k:Fin 3,(run (body idx (withArchive d)) m s).basis (1709+k.val)=false:=by
  have frame:=archive_result d row lim _ _ raw
  exact ⟨body_keeps idx (withArchive d) codePorts d row s m encoded_outside frame,popped d s m row frame⟩
end NativePack255
#print axioms NativePack255.receipt
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave225FullArithmetic Leave225Join Leave225Word

def program:=leave225.take 2260
theorem shape:program=entry++Leave225Routed.body := by decide +kernel
def rawSites:=List.range' 1613 105 ++ List.range' 1726 87
def magSites:=fullM
def targets:List Wire:=List.range' 1559 39 ++ (List.finRange 18).map (fun j=>(row j).free) ++ rawSites ++ magSites

theorem geometry:∀q∈rawSites++magSites,(∀i:Fin 112,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
    q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597) := by decide +kernel
theorem rawSafe:∀q∈rawSites,q∉entry.map destination := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z))) :
    let out:=run program m s
    (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧
    (∀q∈rawSites,out.basis q=s.basis q) ∧ (∀q∈magSites,out.basis q=false) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  have front:=Leave225Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave225FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 112,97 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave225Hit.swaps i):=by decide +kernel
  have used:=Leave225Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave225EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave225EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have other (q:Wire) (mem:q∈rawSites++magSites) : (run Leave225Routed.body n a).basis q=a.basis q := by
    obtain ⟨away,cols,sel,mask⟩:=geometry q mem
    rw [used.2.2.2.2 q (fun i hi=>away ⟨i,hi⟩) cols,cleared,if_neg mask]
    exact preserved _ a n q sel
  dsimp only
  rw [shape,run_append,run_take]
  refine ⟨used.2.2.2.1,used.2.2.1,?_,?_⟩
  · intro q h
    exact (other _ (List.mem_append_left _ h)).trans (kept _ (rawSafe _ h))
  · intro q h
    have set:∀q∈magSites,q∈fullM:=by decide +kernel
    exact (other _ (List.mem_append_right _ h)).trans ((regValue_zero _ _).mp front.2.1 q (set _ h))

theorem oracle (s out:State) (scr:∀j:Fin 39,out.basis (1559+j.val)=false)
    (raw:∀q∈rawSites,out.basis q=s.basis q) (clean:∀q∈carries,s.basis q=false) :
    ∀q∈[1560,1576,1596,1613,1614],out.basis q=false := by
  have cases:∀q∈[1560,1576,1596,1613,1614],(∃j:Fin 39,q=1559+j.val) ∨ (q∈rawSites ∧ q∈carries) := by decide +kernel
  intro q mem
  rcases cases q mem with ⟨j,rfl⟩|⟨a,b⟩
  · exact scr j
  · exact (raw q a).trans (clean q b)

end ECDSAAdd.Entrant.StairPacket.Leave225CoreCheckpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FlagScratch
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave225FullArithmetic Leave225Join
def targets := (pendingPairs++clearFlagPairs).map Prod.snd

private theorem geometry : ∀q∈targets,q∉smallM ∧
    ((∃i:Fin 39,q=1559+i.val) ∨
      (q∈carries ∧ (∀i:Fin 112,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
       q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597))) := by decide +kernel

attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z))) :
    ∀q∈targets,(run program m s).basis q=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  have front:=Leave225Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave225FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 112,97 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave225Hit.swaps i):=by decide +kernel
  have used:=Leave225Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave225EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave225EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave225RoutedRestore.result z sg a n (n.drop (measurementCount Leave225Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  intro q hq
  obtain ⟨outsideMag,side⟩:=geometry q hq
  rw [Leave225FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ outsideMag]
  rcases side with ⟨i,rfl⟩|⟨carry,notWire,cols,noPrefix,noSelector⟩
  · exact used.2.2.2.1 i
  · rw [used.2.2.2.2 q (fun i hi=>notWire ⟨i,hi⟩) cols,cleared,if_neg noSelector]
    exact (preserved (fullPrefix false) a n q noPrefix).trans ((kept q (cs q carry)).trans (clean q carry))
end ECDSAAdd.Entrant.StairPacket.Leave225FlagScratch

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225InputScan Leave225Front
open LeaveReadoutFrame Leave225MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def beforeOpen := leave225.take 169
theorem beforeShape : beforeOpen=scanPart++(flipHistory++long) := by decide +kernel
theorem split : Leave225FullArithmetic.program=beforeOpen++(openPart++interior) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let v:=run Leave225FullArithmetic.program m s
    v.basis 930=decide (2^144≤mag%(2*2^144)) ∧
    ∀mm,run closePart mm v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  let sc:=run scanPart m s
  let a:=run flipHistory (m.drop (measurementCount scanPart)) sc
  have input:=Leave225InputScan.result s m h.u h.v G sg ready fresh
  have hist (q:Wire) (ok:q∉flipHistory.map destination):a.basis q=sc.basis q:=preserved _ _ _ q ok
  have safe (q:Wire) (ok:q∉flipHistory.map destination ∧ q≠1723 ∧ q∉RailPair.sites pairs):a.basis q=s.basis q:=
    (hist _ ok.1).trans (input.2.2.2 _ ok.2.1 ok.2.2)
  have temps:∀p∈longPairs,a.basis p.2=false := by
    intro p hq
    exact (safe _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1723 ∧ p.2∉RailPair.sites pairs) p hq)).trans (temp p hq)
  let e:=run beforeOpen m s
  have eq:e=⟨a.phase,writeBit a.basis 1556 (a.basis 1556 ^^ ((PortalAnd.digits 930 longPairs).any a.basis))⟩ := by
    change run beforeOpen m s=_
    rw [beforeShape,run_append,run_take,run_append,run_take,long_run _ _ temps]
  have keep (q:Wire) (neq:q≠1556):e.basis q=a.basis q := by rw [eq];simp [writeBit,neq]
  have x:e.basis 1557=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  have y:e.basis 1558=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  let n:=m.drop (measurementCount beforeOpen)
  let w:=run openPart n e
  let w':=n.drop (measurementCount openPart)
  have bit:(run interior w' w).basis 930=e.basis 930 :=
    (preserved _ _ _ _ (layout _ (by decide))).trans (preserved openPart e n _ (by decide +kernel))
  have raw:e.basis 930=((h.u-(negative sg h.u).toNat)/2^144).testBit 0 :=
    (keep _ (by decide)).trans ((hist _ (by decide)).trans (input.2.2.1 0 (by decide)).2)
  have tr:=LeaveRestoreTruth.truth 144 z small sg
  dsimp only
  rw [split,run_append,run_take,run_append,run_take]
  constructor
  · rw [bit,raw,thresholdBit _ _ (by decide),tr.2.2.2,tr.2.2.1]
  · exact fun mm=>released e n w' mm x y
end ECDSAAdd.Entrant.StairPacket.Leave225MaskCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225RecordedEvents
open Arithmetic IntegerPacket IntegerHigh SkywalkRails LeaveSelector
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem result (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^144) (odd : z.v % 2 = 1)
    (record : readCells (shape 10) 0 15 (mappedBasis 10 s.basis) =
      SkywalkTrace.trace 15 (encode g sg z.u z.v)) :
    let xs:=SkywalkTrace.trace 15 (encode g sg z.u z.v)
    Leave225Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd ∧
    (right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) →
      s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z))) := by
  let xs:=SkywalkTrace.trace 15 (encode g sg z.u z.v)
  have tape : (List.range 15).map (fun i=>s.basis (Leave225Hit.swaps i)) = xs.map Prod.snd := by
    change _ = (SkywalkTrace.trace 15 _).map _
    rw [←record]
    rfl
  constructor
  · rw [←record];rfl
  · intro rightSide i hi early
    have far : Shadow.far 144 15 z := by
      by_contra h
      simp [actualMode,farMode,ofFlags,right,h] at rightSide
    obtain ⟨keyEq,orientation,_⟩:=modeKey 144 z far
    have side : decide (2^144≤z.u)=false := by rw [orientation] at rightSide;simpa using rightSide
    have keyWait : key (actualMode 144 z)=wait 15 z.u := by
      rw [keyEq,place,if_neg (of_decide_eq_false side)]
    have hlen : i<xs.length := by simpa only [xs,SkywalkTrace.trace_length] using hi
    have phys := congrArg (fun a : List Bool => a[i]?) tape
    have before := LeaveTraceHistory.firstSwap 144 z g sg small odd far side i hlen (keyWait ▸ early)
    rw [keyWait]
    exact Eq.trans (by simpa [List.getElem?_eq_getElem hlen,hi] using phys) before

end ECDSAAdd.Entrant.StairPacket.Leave225RecordedEvents

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave240FullArithmetic Leave240Join Leave240Word

def program:=leave240.take 2395
theorem shape:program=entry++Leave240Routed.body := by decide +kernel
def rawSites:=List.range' 1613 97 ++ List.range' 1718 95
def magSites:=fullM
def targets:List Wire:=List.range' 1559 39 ++ (List.finRange 18).map (fun j=>(row j).free) ++ rawSites ++ magSites

theorem geometry:∀q∈rawSites++magSites,(∀i:Fin 120,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
    q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597) := by decide +kernel
theorem rawSafe:∀q∈rawSites,q∉entry.map destination := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z))) :
    let out:=run program m s
    (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧
    (∀q∈rawSites,out.basis q=s.basis q) ∧ (∀q∈magSites,out.basis q=false) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  have front:=Leave240Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave240FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 120,105 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave240Hit.swaps i):=by decide +kernel
  have used:=Leave240Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave240EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave240EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have other (q:Wire) (mem:q∈rawSites++magSites) : (run Leave240Routed.body n a).basis q=a.basis q := by
    obtain ⟨away,cols,sel,mask⟩:=geometry q mem
    rw [used.2.2.2.2 q (fun i hi=>away ⟨i,hi⟩) cols,cleared,if_neg mask]
    exact preserved _ a n q sel
  dsimp only
  rw [shape,run_append,run_take]
  refine ⟨used.2.2.2.1,used.2.2.1,?_,?_⟩
  · intro q h
    exact (other _ (List.mem_append_left _ h)).trans (kept _ (rawSafe _ h))
  · intro q h
    have set:∀q∈magSites,q∈fullM:=by decide +kernel
    exact (other _ (List.mem_append_right _ h)).trans ((regValue_zero _ _).mp front.2.1 q (set _ h))

theorem oracle (s out:State) (scr:∀j:Fin 39,out.basis (1559+j.val)=false)
    (raw:∀q∈rawSites,out.basis q=s.basis q) (clean:∀q∈carries,s.basis q=false) :
    ∀q∈[1560,1576,1596,1613,1614],out.basis q=false := by
  have cases:∀q∈[1560,1576,1596,1613,1614],(∃j:Fin 39,q=1559+j.val) ∨ (q∈rawSites ∧ q∈carries) := by decide +kernel
  intro q mem
  rcases cases q mem with ⟨j,rfl⟩|⟨a,b⟩
  · exact scr j
  · exact (raw q a).trans (clean q b)

end ECDSAAdd.Entrant.StairPacket.Leave240CoreCheckpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FlagScratch
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave240FullArithmetic Leave240Join
def targets := (pendingPairs++clearFlagPairs).map Prod.snd

private theorem geometry : ∀q∈targets,q∉smallM ∧
    ((∃i:Fin 39,q=1559+i.val) ∨
      (q∈carries ∧ (∀i:Fin 120,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
       q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597))) := by decide +kernel

attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z))) :
    ∀q∈targets,(run program m s).basis q=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  have front:=Leave240Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave240FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 120,105 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave240Hit.swaps i):=by decide +kernel
  have used:=Leave240Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave240EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave240EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave240RoutedRestore.result z sg a n (n.drop (measurementCount Leave240Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  intro q hq
  obtain ⟨outsideMag,side⟩:=geometry q hq
  rw [Leave240FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ outsideMag]
  rcases side with ⟨i,rfl⟩|⟨carry,notWire,cols,noPrefix,noSelector⟩
  · exact used.2.2.2.1 i
  · rw [used.2.2.2.2 q (fun i hi=>notWire ⟨i,hi⟩) cols,cleared,if_neg noSelector]
    exact (preserved (fullPrefix false) a n q noPrefix).trans ((kept q (cs q carry)).trans (clean q carry))
end ECDSAAdd.Entrant.StairPacket.Leave240FlagScratch

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240InputScan Leave240Front
open LeaveReadoutFrame Leave240MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def beforeOpen := leave240.take 169
theorem beforeShape : beforeOpen=scanPart++(flipHistory++long) := by decide +kernel
theorem split : Leave240FullArithmetic.program=beforeOpen++(openPart++interior) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let v:=run Leave240FullArithmetic.program m s
    v.basis 922=decide (2^136≤mag%(2*2^136)) ∧
    ∀mm,run closePart mm v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  let sc:=run scanPart m s
  let a:=run flipHistory (m.drop (measurementCount scanPart)) sc
  have input:=Leave240InputScan.result s m h.u h.v G sg ready fresh
  have hist (q:Wire) (ok:q∉flipHistory.map destination):a.basis q=sc.basis q:=preserved _ _ _ q ok
  have safe (q:Wire) (ok:q∉flipHistory.map destination ∧ q≠1715 ∧ q∉RailPair.sites pairs):a.basis q=s.basis q:=
    (hist _ ok.1).trans (input.2.2.2 _ ok.2.1 ok.2.2)
  have temps:∀p∈longPairs,a.basis p.2=false := by
    intro p hq
    exact (safe _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1715 ∧ p.2∉RailPair.sites pairs) p hq)).trans (temp p hq)
  let e:=run beforeOpen m s
  have eq:e=⟨a.phase,writeBit a.basis 1556 (a.basis 1556 ^^ ((PortalAnd.digits 922 longPairs).any a.basis))⟩ := by
    change run beforeOpen m s=_
    rw [beforeShape,run_append,run_take,run_append,run_take,long_run _ _ temps]
  have keep (q:Wire) (neq:q≠1556):e.basis q=a.basis q := by rw [eq];simp [writeBit,neq]
  have x:e.basis 1557=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  have y:e.basis 1558=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  let n:=m.drop (measurementCount beforeOpen)
  let w:=run openPart n e
  let w':=n.drop (measurementCount openPart)
  have bit:(run interior w' w).basis 922=e.basis 922 :=
    (preserved _ _ _ _ (layout _ (by decide))).trans (preserved openPart e n _ (by decide +kernel))
  have raw:e.basis 922=((h.u-(negative sg h.u).toNat)/2^136).testBit 0 :=
    (keep _ (by decide)).trans ((hist _ (by decide)).trans (input.2.2.1 0 (by decide)).2)
  have tr:=LeaveRestoreTruth.truth 136 z small sg
  dsimp only
  rw [split,run_append,run_take,run_append,run_take]
  constructor
  · rw [bit,raw,thresholdBit _ _ (by decide),tr.2.2.2,tr.2.2.1]
  · exact fun mm=>released e n w' mm x y
end ECDSAAdd.Entrant.StairPacket.Leave240MaskCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240RecordedEvents
open Arithmetic IntegerPacket IntegerHigh SkywalkRails LeaveSelector
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem result (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^136) (odd : z.v % 2 = 1)
    (record : readCells (shape 11) 0 15 (mappedBasis 11 s.basis) =
      SkywalkTrace.trace 15 (encode g sg z.u z.v)) :
    let xs:=SkywalkTrace.trace 15 (encode g sg z.u z.v)
    Leave240Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd ∧
    (right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) →
      s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z))) := by
  let xs:=SkywalkTrace.trace 15 (encode g sg z.u z.v)
  have tape : (List.range 15).map (fun i=>s.basis (Leave240Hit.swaps i)) = xs.map Prod.snd := by
    change _ = (SkywalkTrace.trace 15 _).map _
    rw [←record]
    rfl
  constructor
  · rw [←record];rfl
  · intro rightSide i hi early
    have far : Shadow.far 136 15 z := by
      by_contra h
      simp [actualMode,farMode,ofFlags,right,h] at rightSide
    obtain ⟨keyEq,orientation,_⟩:=modeKey 136 z far
    have side : decide (2^136≤z.u)=false := by rw [orientation] at rightSide;simpa using rightSide
    have keyWait : key (actualMode 136 z)=wait 15 z.u := by
      rw [keyEq,place,if_neg (of_decide_eq_false side)]
    have hlen : i<xs.length := by simpa only [xs,SkywalkTrace.trace_length] using hi
    have phys := congrArg (fun a : List Bool => a[i]?) tape
    have before := LeaveTraceHistory.firstSwap 136 z g sg small odd far side i hlen (keyWait ▸ early)
    rw [keyWait]
    exact Eq.trans (by simpa [List.getElem?_eq_getElem hlen,hi] using phys) before

end ECDSAAdd.Entrant.StairPacket.Leave240RecordedEvents

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave255FullArithmetic Leave255Join Leave255Word

def program:=leave255.take 2515
theorem shape:program=entry++Leave255Routed.body := by decide +kernel
def rawSites:=List.range' 1613 90 ++ List.range' 1711 89
def magSites:=fullM
def targets:List Wire:=List.range' 1559 39 ++ (List.finRange 18).map (fun j=>(row j).free) ++ rawSites ++ magSites

theorem geometry:∀q∈rawSites++magSites,(∀i:Fin 127,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
    q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597) := by decide +kernel
theorem rawSafe:∀q∈rawSites,q∉entry.map destination := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z))) :
    let out:=run program m s
    (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧
    (∀q∈rawSites,out.basis q=s.basis q) ∧ (∀q∈magSites,out.basis q=false) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  have front:=Leave255Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave255FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 127,112 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave255Hit.swaps i):=by decide +kernel
  have used:=Leave255Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave255EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave255EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have other (q:Wire) (mem:q∈rawSites++magSites) : (run Leave255Routed.body n a).basis q=a.basis q := by
    obtain ⟨away,cols,sel,mask⟩:=geometry q mem
    rw [used.2.2.2.2 q (fun i hi=>away ⟨i,hi⟩) cols,cleared,if_neg mask]
    exact preserved _ a n q sel
  dsimp only
  rw [shape,run_append,run_take]
  refine ⟨used.2.2.2.1,used.2.2.1,?_,?_⟩
  · intro q h
    exact (other _ (List.mem_append_left _ h)).trans (kept _ (rawSafe _ h))
  · intro q h
    have set:∀q∈magSites,q∈fullM:=by decide +kernel
    exact (other _ (List.mem_append_right _ h)).trans ((regValue_zero _ _).mp front.2.1 q (set _ h))

theorem oracle (s out:State) (scr:∀j:Fin 39,out.basis (1559+j.val)=false)
    (raw:∀q∈rawSites,out.basis q=s.basis q) (clean:∀q∈carries,s.basis q=false) :
    ∀q∈[1560,1576,1596,1613,1614],out.basis q=false := by
  have cases:∀q∈[1560,1576,1596,1613,1614],(∃j:Fin 39,q=1559+j.val) ∨ (q∈rawSites ∧ q∈carries) := by decide +kernel
  intro q mem
  rcases cases q mem with ⟨j,rfl⟩|⟨a,b⟩
  · exact scr j
  · exact (raw q a).trans (clean q b)

end ECDSAAdd.Entrant.StairPacket.Leave255CoreCheckpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FlagScratch
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave255FullArithmetic Leave255Join
def targets := (pendingPairs++clearFlagPairs).map Prod.snd

private theorem geometry : ∀q∈targets,q∉smallM ∧
    ((∃i:Fin 39,q=1559+i.val) ∨
      (q∈carries ∧ (∀i:Fin 127,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
       q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597))) := by decide +kernel

attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z))) :
    ∀q∈targets,(run program m s).basis q=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  have front:=Leave255Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave255FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 127,112 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave255Hit.swaps i):=by decide +kernel
  have used:=Leave255Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave255EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave255EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave255RoutedRestore.result z sg a n (n.drop (measurementCount Leave255Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  intro q hq
  obtain ⟨outsideMag,side⟩:=geometry q hq
  rw [Leave255FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ outsideMag]
  rcases side with ⟨i,rfl⟩|⟨carry,notWire,cols,noPrefix,noSelector⟩
  · exact used.2.2.2.1 i
  · rw [used.2.2.2.2 q (fun i hi=>notWire ⟨i,hi⟩) cols,cleared,if_neg noSelector]
    exact (preserved (fullPrefix false) a n q noPrefix).trans ((kept q (cs q carry)).trans (clean q carry))
end ECDSAAdd.Entrant.StairPacket.Leave255FlagScratch

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255InputScan Leave255Front
open LeaveReadoutFrame Leave255MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def beforeOpen := leave255.take 169
theorem beforeShape : beforeOpen=scanPart++(flipHistory++long) := by decide +kernel
theorem split : Leave255FullArithmetic.program=beforeOpen++(openPart++interior) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let v:=run Leave255FullArithmetic.program m s
    v.basis 915=decide (2^129≤mag%(2*2^129)) ∧
    ∀mm,run closePart mm v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  let sc:=run scanPart m s
  let a:=run flipHistory (m.drop (measurementCount scanPart)) sc
  have input:=Leave255InputScan.result s m h.u h.v G sg ready fresh
  have hist (q:Wire) (ok:q∉flipHistory.map destination):a.basis q=sc.basis q:=preserved _ _ _ q ok
  have safe (q:Wire) (ok:q∉flipHistory.map destination ∧ q≠1708 ∧ q∉RailPair.sites pairs):a.basis q=s.basis q:=
    (hist _ ok.1).trans (input.2.2.2 _ ok.2.1 ok.2.2)
  have temps:∀p∈longPairs,a.basis p.2=false := by
    intro p hq
    exact (safe _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1708 ∧ p.2∉RailPair.sites pairs) p hq)).trans (temp p hq)
  let e:=run beforeOpen m s
  have eq:e=⟨a.phase,writeBit a.basis 1556 (a.basis 1556 ^^ ((PortalAnd.digits 915 longPairs).any a.basis))⟩ := by
    change run beforeOpen m s=_
    rw [beforeShape,run_append,run_take,run_append,run_take,long_run _ _ temps]
  have keep (q:Wire) (neq:q≠1556):e.basis q=a.basis q := by rw [eq];simp [writeBit,neq]
  have x:e.basis 1557=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  have y:e.basis 1558=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  let n:=m.drop (measurementCount beforeOpen)
  let w:=run openPart n e
  let w':=n.drop (measurementCount openPart)
  have bit:(run interior w' w).basis 915=e.basis 915 :=
    (preserved _ _ _ _ (layout _ (by decide))).trans (preserved openPart e n _ (by decide +kernel))
  have raw:e.basis 915=((h.u-(negative sg h.u).toNat)/2^129).testBit 0 :=
    (keep _ (by decide)).trans ((hist _ (by decide)).trans (input.2.2.1 0 (by decide)).2)
  have tr:=LeaveRestoreTruth.truth 129 z small sg
  dsimp only
  rw [split,run_append,run_take,run_append,run_take]
  constructor
  · rw [bit,raw,thresholdBit _ _ (by decide),tr.2.2.2,tr.2.2.1]
  · exact fun mm=>released e n w' mm x y
end ECDSAAdd.Entrant.StairPacket.Leave255MaskCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255RecordedEvents
open Arithmetic IntegerPacket IntegerHigh SkywalkRails LeaveSelector
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem result (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^129) (odd : z.v % 2 = 1)
    (record : readCells (shape 12) 0 15 (mappedBasis 12 s.basis) =
      SkywalkTrace.trace 15 (encode g sg z.u z.v)) :
    let xs:=SkywalkTrace.trace 15 (encode g sg z.u z.v)
    Leave255Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd ∧
    (right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) →
      s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z))) := by
  let xs:=SkywalkTrace.trace 15 (encode g sg z.u z.v)
  have tape : (List.range 15).map (fun i=>s.basis (Leave255Hit.swaps i)) = xs.map Prod.snd := by
    change _ = (SkywalkTrace.trace 15 _).map _
    rw [←record]
    rfl
  constructor
  · rw [←record];rfl
  · intro rightSide i hi early
    have far : Shadow.far 129 15 z := by
      by_contra h
      simp [actualMode,farMode,ofFlags,right,h] at rightSide
    obtain ⟨keyEq,orientation,_⟩:=modeKey 129 z far
    have side : decide (2^129≤z.u)=false := by rw [orientation] at rightSide;simpa using rightSide
    have keyWait : key (actualMode 129 z)=wait 15 z.u := by
      rw [keyEq,place,if_neg (of_decide_eq_false side)]
    have hlen : i<xs.length := by simpa only [xs,SkywalkTrace.trace_length] using hi
    have phys := congrArg (fun a : List Bool => a[i]?) tape
    have before := LeaveTraceHistory.firstSwap 129 z g sg small odd far side i hlen (keyWait ▸ early)
    rw [keyWait]
    exact Eq.trans (by simpa [List.getElem?_eq_getElem hlen,hi] using phys) before

end ECDSAAdd.Entrant.StairPacket.Leave255RecordedEvents

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
theorem outside_between {i q:Nat} (lo:i+16<q) (hi:q<1044) : ¬ Earlier i q:=by
  rintro ⟨t,ht,h|h⟩
  · change q=t+16 at h;omega
  · change q=1028+t+16 at h;omega
theorem outside_above {i q:Nat} (hi:1044+i≤q) : ¬ Earlier i q:=by
  rintro ⟨t,ht,h|h⟩
  · change q=t+16 at h;omega
  · change q=1028+t+16 at h;omega
theorem carry {i x p:Nat} (hi:i≤512) {s:State} (dom:Domain i x p s) : s.basis 1812=false:=by
  obtain ⟨ref,stage,link⟩:=leaves_reference i x p hi true s dom
  exact (link.2 _ (outside_above (by omega))).trans (stock_carry_end true x p i hi ref stage)
theorem future_history {i j x p:Nat} (h:i≤j) (hj:j<512) {s:State} (dom:Domain i x p s) :
    s.basis (base (1028+j))=false:=by
  obtain ⟨ref,stage,link⟩:=leaves_reference i x p (by omega) true s dom
  have lim:1044+i≤base (1028+j):=by change 1044+i≤1028+j+16;omega
  exact (link.2 _ (outside_above lim)).trans (stock_history true x p i ref stage j h hj)
theorem terminal (d:Bool) (x:Nat) (s:State) (dom:Domain 270 x p s) :
    ∃ref:State,Rolling1588.Integer.Stage base d x p 270 ref.basis ∧ EndTick.Reads s ref ∧
    s.basis (base (1028+270))=false ∧ s.basis (base (2053-270))=false ∧
    ∀q∈ParkEndpoint.dst,(pullState (OB5.sig 269) s).basis q=false := by
  obtain ⟨ref,stage,link⟩:=leaves_reference 270 x p (by decide) d s dom
  have bounds:∀q∈ParkEndpoint.dst,270+16<OB5.sig 269 q ∧ OB5.sig 269 q<1044:=by decide +kernel
  refine ⟨ref,stage,reads_now (by decide) link,future_history (Nat.le_refl _) (by decide) dom,?_,?_⟩
  · exact (link.2 _ (outside_above (by decide))).trans ((Rolling1588.Integer.stage_zero d x 270 (by decide) _ stage).2 (by decide))
  · intro q hit
    exact (link.2 _ (outside_between (bounds _ hit).1 (bounds _ hit).2)).trans (ParkEndpoint.clear_dest d x p ref stage q hit)
#print axioms terminal
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic MappedCompressed IntegerPacket
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
attribute [local irreducible] run routed unrouted renameProgram portal225 enter225 enter240 enter255 leave225 leave240 leave255
  portal225Inv enter225Inv enter240Inv enter255Inv leave225Inv leave240Inv leave255Inv park270 park270Inv portal270 portal270Inv
  archiveLoad240 archiveLoad255 archiveLoad270 archiveRestore240 archiveRestore255 archiveRestore270
theorem assembly (d:Bool) : forward45plus1 d =
    NativePack225.firstWindow d ++ leave225 ++ NativePack240.nextWindow d ++ leave240 ++ NativePack255.nextWindow d ++ leave255 ++ NativePack270.lastWindow d := by
  simp only [forward45plus1,NativePack225.firstWindow,NativePack240.nextWindow,NativePack255.nextWindow,NativePack270.lastWindow,
    NativePack225.window,NativePack240.window,NativePack255.window,NativePack270.endSlice,body,
    NativePack240.withArchive,NativePack255.withArchive, List.append_assoc]
  rfl
theorem unwind_assembly (d:Bool) : reverse45plus1 d =
    NativePack270.lastUnwind d ++ leave255Inv ++ NativePack255.nextUnwind d ++ leave240Inv ++ NativePack240.nextUnwind d ++ leave225Inv ++ NativePack225.firstUnwind d := by
  simp only [reverse45plus1,NativePack270.lastUnwind,NativePack255.nextUnwind,NativePack240.nextUnwind,NativePack225.firstUnwind,
    NativePack225.unwind,NativePack240.unwind,NativePack255.unwind,NativePack270.endUndo,unbody,
    NativePack240.fromArchive,NativePack255.fromArchive,List.append_assoc]
  rfl
#print axioms assembly
#print axioms unwind_assembly
end ECDSAAdd.Entrant.StairPacket.Partial

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
attribute [local irreducible] run routed measurementCount body
namespace NativePack240
open ArchiveBoundary240
theorem real_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^136)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false) 
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    ∃row<63145, Kept codePorts d row out ∧ ∀k:Fin 3,out.basis (1716+k.val)=false:=by
  let pre:=run Partial.enter240 m s
  let tape:=m.drop (measurementCount Partial.enter240)
  let T:=Shadow.reduced 136 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 136 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter240.ready_pending raw s z G S m small cut input hist 
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have final:=receipt d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,final⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem real_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^129)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    ∃row<63145, Kept codePorts d row out ∧ ∀k:Fin 3,out.basis (1709+k.val)=false:=by
  let pre:=run Partial.enter255 m s
  let tape:=m.drop (measurementCount Partial.enter255)
  let T:=Shadow.reduced 129 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 129 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter255.ready_pending raw s z G S m small cut input hist endScratch
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have final:=receipt d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,final⟩
end NativePack255
#print axioms NativePack255.real_receipt
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program := leave225.take 2788
theorem shape : program=Leave225FullArithmetic.program++(Leave225MaskThrough.closePart++Leave225TailFlags.program) := by decide +kernel
def finalBits (v:BasisState) (f u:Bool) := writeBit (writeBit (writeBit v 1557 f) 1558 u) 1556 false
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let far:=decide (Shadow.far 136 15 a)
    let v:=run Leave225FullArithmetic.program m s
    let out:=run program m s
    out.phase=s.phase ∧ out.basis 1556=false ∧ out.basis 1557=far ∧ out.basis 1558=(far && decide (2^136≤a.u)) ∧
      regValue smallM out.basis=(mag/2^145)%2^10 ∧
      (∀i<112,out.basis (live i)=(Leave225TrueMiddle.F z).testBit i) ∧
      ∀q,q≠1556 → q≠1557 → q≠1558 → out.basis q=v.basis q := by
  let a:=SkywalkNat.step^[15] z
  let e:=(negative sg a.u).toNat
  let v:=run Leave225FullArithmetic.program m s
  let n:=m.drop (measurementCount Leave225FullArithmetic.program)
  let u:=run Leave225MaskThrough.closePart n v
  let n':=n.drop (measurementCount Leave225MaskThrough.closePart)
  have ar:=Leave225FullArithmetic.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have clears:=Leave225FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have mask:=Leave225MaskCut.result s m z G sg small ready fresh scratch temp
  have closed:u=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  have kept (q:Wire) (h:q≠1557 ∧ q≠1558) : u.basis q=v.basis q := by rw [closed];simp [writeBit,h.1,h.2]
  have lo:∀i:Fin 112,live i≠1557 ∧ live i≠1558 ∧ live i≠1556 := by decide +kernel
  have ms:∀q∈smallM,q≠1557 ∧ q≠1558 ∧ q≠1556 := by decide +kernel
  have bits:∀i<112,u.basis (live i)=(Leave225TrueMiddle.F z).testBit i := fun i h=>
    (kept _ ⟨(lo ⟨i,h⟩).1,(lo ⟨i,h⟩).2.1⟩).trans (ar.2.2.2 i h)
  have upper:regValue smallM u.basis=regValue smallM v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ ⟨(ms _ h).1,(ms _ h).2.1⟩)
  have scan:regValue scanned u.basis=Shadow.high 136 15 a := by
    rw [(outputRegisters u _ bits).2]
    have fit:Leave225TrueMiddle.F z/2^7<2^105 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
    rw [Nat.mod_eq_of_lt fit]
    exact Leave225NextFlagTruth.value z
  have cleanAt (q:Wire) (h:q∈Leave225FlagScratch.targets) : u.basis q=false := by
    have geom:∀q∈Leave225FlagScratch.targets,q≠1557 ∧ q≠1558 := by decide +kernel
    exact (kept _ (geom _ h)).trans (clears _ h)
  have tail:=Leave225TailFlags.result a u n' e (by dsimp [e];cases negative sg a.u <;> decide) nextSmall
    (by rw [closed];simp [writeBit]) (by rw [closed];simp [writeBit]) scan
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_left _ h,rfl⟩))
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_right _ h,rfl⟩))
    ((kept _ (by decide)).trans ar.2.2.1) ((kept _ (by decide)).trans mask.1)
    (by rw [upper,ar.2.1];rfl)
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take,tail]
  let f:=decide (Shadow.far 136 15 a)
  let side:=f && decide (2^136≤a.u)
  have frame (q:Wire) (hx:q≠1556) (hy:q≠1557) (hz:q≠1558):finalBits u.basis f side q=v.basis q := by
    simpa [finalBits,writeBit,hx,hy,hz] using kept q ⟨hy,hz⟩
  refine ⟨(show u.phase=v.phase by rw [closed]).trans ar.1,?_,?_,?_,?_,?_,frame⟩
  · simp [writeBit]
  · change finalBits u.basis f side 1557=f
    simp [finalBits,writeBit]
  · change finalBits u.basis f side 1558=side
    simp [finalBits,writeBit]
  · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>frame q (ms _ h).2.2 (ms _ h).1 (ms _ h).2.1)).trans ar.2.1
  · intro i h
    exact (frame _ (lo ⟨i,h⟩).2.2 (lo ⟨i,h⟩).1 (lo ⟨i,h⟩).2.1).trans (ar.2.2.2 i h)
end ECDSAAdd.Entrant.StairPacket.Leave225BeforeStore

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program := leave240.take 2961
theorem shape : program=Leave240FullArithmetic.program++(Leave240MaskThrough.closePart++Leave240TailFlags.program) := by decide +kernel
def finalBits (v:BasisState) (f u:Bool) := writeBit (writeBit (writeBit v 1557 f) 1558 u) 1556 false
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let far:=decide (Shadow.far 129 15 a)
    let v:=run Leave240FullArithmetic.program m s
    let out:=run program m s
    out.phase=s.phase ∧ out.basis 1556=false ∧ out.basis 1557=far ∧ out.basis 1558=(far && decide (2^129≤a.u)) ∧
      regValue smallM out.basis=(mag/2^137)%2^11 ∧
      (∀i<120,out.basis (live i)=(Leave240TrueMiddle.F z).testBit i) ∧
      ∀q,q≠1556 → q≠1557 → q≠1558 → out.basis q=v.basis q := by
  let a:=SkywalkNat.step^[15] z
  let e:=(negative sg a.u).toNat
  let v:=run Leave240FullArithmetic.program m s
  let n:=m.drop (measurementCount Leave240FullArithmetic.program)
  let u:=run Leave240MaskThrough.closePart n v
  let n':=n.drop (measurementCount Leave240MaskThrough.closePart)
  have ar:=Leave240FullArithmetic.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have clears:=Leave240FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have mask:=Leave240MaskCut.result s m z G sg small ready fresh scratch temp
  have closed:u=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  have kept (q:Wire) (h:q≠1557 ∧ q≠1558) : u.basis q=v.basis q := by rw [closed];simp [writeBit,h.1,h.2]
  have lo:∀i:Fin 120,live i≠1557 ∧ live i≠1558 ∧ live i≠1556 := by decide +kernel
  have ms:∀q∈smallM,q≠1557 ∧ q≠1558 ∧ q≠1556 := by decide +kernel
  have bits:∀i<120,u.basis (live i)=(Leave240TrueMiddle.F z).testBit i := fun i h=>
    (kept _ ⟨(lo ⟨i,h⟩).1,(lo ⟨i,h⟩).2.1⟩).trans (ar.2.2.2 i h)
  have upper:regValue smallM u.basis=regValue smallM v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ ⟨(ms _ h).1,(ms _ h).2.1⟩)
  have scan:regValue scanned u.basis=Shadow.high 129 15 a := by
    rw [(outputRegisters u _ bits).2]
    have fit:Leave240TrueMiddle.F z/2^8<2^112 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
    rw [Nat.mod_eq_of_lt fit]
    exact Leave240NextFlagTruth.value z
  have cleanAt (q:Wire) (h:q∈Leave240FlagScratch.targets) : u.basis q=false := by
    have geom:∀q∈Leave240FlagScratch.targets,q≠1557 ∧ q≠1558 := by decide +kernel
    exact (kept _ (geom _ h)).trans (clears _ h)
  have tail:=Leave240TailFlags.result a u n' e (by dsimp [e];cases negative sg a.u <;> decide) nextSmall
    (by rw [closed];simp [writeBit]) (by rw [closed];simp [writeBit]) scan
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_left _ h,rfl⟩))
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_right _ h,rfl⟩))
    ((kept _ (by decide)).trans ar.2.2.1) ((kept _ (by decide)).trans mask.1)
    (by rw [upper,ar.2.1];rfl)
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take,tail]
  let f:=decide (Shadow.far 129 15 a)
  let side:=f && decide (2^129≤a.u)
  have frame (q:Wire) (hx:q≠1556) (hy:q≠1557) (hz:q≠1558):finalBits u.basis f side q=v.basis q := by
    simpa [finalBits,writeBit,hx,hy,hz] using kept q ⟨hy,hz⟩
  refine ⟨(show u.phase=v.phase by rw [closed]).trans ar.1,?_,?_,?_,?_,?_,frame⟩
  · simp [writeBit]
  · change finalBits u.basis f side 1557=f
    simp [finalBits,writeBit]
  · change finalBits u.basis f side 1558=side
    simp [finalBits,writeBit]
  · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>frame q (ms _ h).2.2 (ms _ h).1 (ms _ h).2.1)).trans ar.2.1
  · intro i h
    exact (frame _ (lo ⟨i,h⟩).2.2 (lo ⟨i,h⟩).1 (lo ⟨i,h⟩).2.1).trans (ar.2.2.2 i h)
end ECDSAAdd.Entrant.StairPacket.Leave240BeforeStore

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program := leave255.take 3103
theorem shape : program=Leave255FullArithmetic.program++(Leave255MaskThrough.closePart++Leave255TailFlags.program) := by decide +kernel
def finalBits (v:BasisState) (f u:Bool) := writeBit (writeBit (writeBit v 1557 f) 1558 u) 1556 false
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let far:=decide (Shadow.far 121 15 a)
    let v:=run Leave255FullArithmetic.program m s
    let out:=run program m s
    out.phase=s.phase ∧ out.basis 1556=false ∧ out.basis 1557=far ∧ out.basis 1558=(far && decide (2^121≤a.u)) ∧
      regValue smallM out.basis=(mag/2^130)%2^10 ∧
      (∀i<127,out.basis (live i)=(Leave255TrueMiddle.F z).testBit i) ∧
      ∀q,q≠1556 → q≠1557 → q≠1558 → out.basis q=v.basis q := by
  let a:=SkywalkNat.step^[15] z
  let e:=(negative sg a.u).toNat
  let v:=run Leave255FullArithmetic.program m s
  let n:=m.drop (measurementCount Leave255FullArithmetic.program)
  let u:=run Leave255MaskThrough.closePart n v
  let n':=n.drop (measurementCount Leave255MaskThrough.closePart)
  have ar:=Leave255FullArithmetic.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have clears:=Leave255FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have mask:=Leave255MaskCut.result s m z G sg small ready fresh scratch temp
  have closed:u=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  have kept (q:Wire) (h:q≠1557 ∧ q≠1558) : u.basis q=v.basis q := by rw [closed];simp [writeBit,h.1,h.2]
  have lo:∀i:Fin 127,live i≠1557 ∧ live i≠1558 ∧ live i≠1556 := by decide +kernel
  have ms:∀q∈smallM,q≠1557 ∧ q≠1558 ∧ q≠1556 := by decide +kernel
  have bits:∀i<127,u.basis (live i)=(Leave255TrueMiddle.F z).testBit i := fun i h=>
    (kept _ ⟨(lo ⟨i,h⟩).1,(lo ⟨i,h⟩).2.1⟩).trans (ar.2.2.2 i h)
  have upper:regValue smallM u.basis=regValue smallM v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ ⟨(ms _ h).1,(ms _ h).2.1⟩)
  have scan:regValue scanned u.basis=Shadow.high 121 15 a := by
    rw [(outputRegisters u _ bits).2]
    have fit:Leave255TrueMiddle.F z/2^7<2^120 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
    rw [Nat.mod_eq_of_lt fit]
    exact Leave255NextFlagTruth.value z
  have cleanAt (q:Wire) (h:q∈Leave255FlagScratch.targets) : u.basis q=false := by
    have geom:∀q∈Leave255FlagScratch.targets,q≠1557 ∧ q≠1558 := by decide +kernel
    exact (kept _ (geom _ h)).trans (clears _ h)
  have tail:=Leave255TailFlags.result a u n' e (by dsimp [e];cases negative sg a.u <;> decide) nextSmall
    (by rw [closed];simp [writeBit]) (by rw [closed];simp [writeBit]) scan
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_left _ h,rfl⟩))
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_right _ h,rfl⟩))
    ((kept _ (by decide)).trans ar.2.2.1) ((kept _ (by decide)).trans mask.1)
    (by rw [upper,ar.2.1];rfl)
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take,tail]
  let f:=decide (Shadow.far 121 15 a)
  let side:=f && decide (2^121≤a.u)
  have frame (q:Wire) (hx:q≠1556) (hy:q≠1557) (hz:q≠1558):finalBits u.basis f side q=v.basis q := by
    simpa [finalBits,writeBit,hx,hy,hz] using kept q ⟨hy,hz⟩
  refine ⟨(show u.phase=v.phase by rw [closed]).trans ar.1,?_,?_,?_,?_,?_,frame⟩
  · simp [writeBit]
  · change finalBits u.basis f side 1557=f
    simp [finalBits,writeBit]
  · change finalBits u.basis f side 1558=side
    simp [finalBits,writeBit]
  · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>frame q (ms _ h).2.2 (ms _ h).1 (ms _ h).2.1)).trans ar.2.1
  · intro i h
    exact (frame _ (lo ⟨i,h⟩).2.2 (lo ⟨i,h⟩).1 (lo ⟨i,h⟩).2.1).trans (ar.2.2.2 i h)
end ECDSAAdd.Entrant.StairPacket.Leave255BeforeStore

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270 ParkEndpoint Portal270Flag StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
theorem empty_from_cut (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 n f u (pullState (OB5.sig 269) raw) (eraseSites src s))
    (source:∀q∈dst,(pullState (OB5.sig 269) raw).basis q=false) : ∀q∈dst,s.basis q=false:=by
  have regular:∀q∈dst,q∉src ∧ q≠1700 ∧ q≠1698 ∧ q≠1699 ∧ q∉RailPair.sites hiPairs:=by decide +kernel
  intro q member
  obtain ⟨out,hn,hf,hu,hh⟩:=regular _ member
  have eq:=cut.unchanged q hn hf hu hh
  simpa [eraseSites,out] using eq.trans (source _ member)
theorem from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 270 x p raw) (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty⟩:=WideReference.terminal d x raw domain
  exact last_window d x hx0 hx raw ref s m read stage history swapSlot z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
#print axioms from_domain
end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction StairArchiveTrace StairArchiveRaw CodecBitSliceVerify
attribute [local irreducible] onRails run routed measurementCount body
def RowTruth (past:SkywalkNat.State) (g sg:Bool) (row:Nat) : Prop :=
  ∀q:Fin 20,(rawCol q).testBit row=letterBit (read ((SkywalkTrace.trace 15 (encode g sg past.u past.v)).drop 5) (q.val/2)) q

theorem row_truth (j:Fin 23) (ps:Ports) (chron:∀i:Fin 20,ps ⟨i,by omega⟩=nativeRawPort j i)
    (row:Nat) (past:SkywalkNat.State) (g sg:Bool) (before out:State)
    (rec:physicalCells j before=SkywalkTrace.trace 15 (encode g sg past.u past.v))
    (bk:∀i:Fin 23,out.basis (ps ⟨i,by omega⟩)=before.basis (ps ⟨i,by omega⟩))
    (frame:Frame ps raw row out):RowTruth past g sg row:=by
  intro q
  let i:Fin 157:=⟨q,by omega⟩
  have eq:(rawCol q).testBit row=out.basis (ps i):=
    (congrArg (fun n:Nat=>n.testBit row) (io true true i).1).trans (frame i).symm
  have h:=native_raw_read j before q q.isLt
  change before.basis (nativeRawPort j q)=letterBit (read ((physicalCells j before).drop 5) (q.val/2)) q at h
  rw [rec] at h
  exact eq.trans ((bk ⟨q,by omega⟩).trans ((congrArg before.basis (chron q)).trans h))
namespace NativePack240
open ArchiveBoundary240
theorem matched_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^136)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false) 
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    ∃row<63145, RowTruth past pg ps row ∧ Kept codePorts d row out ∧ ∀k:Fin 3,out.basis (1716+k.val)=false:=by
  let pre:=run Partial.enter240 m s
  let tape:=m.drop (measurementCount Partial.enter240)
  let T:=Shadow.reduced 136 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 136 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter240.ready_pending raw s z G S m small cut input hist 
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have matchRow:=row_truth sourceIdx rawPorts chronological row past pg ps s _ prior.records (bank_kept d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1) frame
  have final:=receipt d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,matchRow,final⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem matched_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^129)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    ∃row<63145, RowTruth past pg ps row ∧ Kept codePorts d row out ∧ ∀k:Fin 3,out.basis (1709+k.val)=false:=by
  let pre:=run Partial.enter255 m s
  let tape:=m.drop (measurementCount Partial.enter255)
  let T:=Shadow.reduced 129 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 129 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter255.ready_pending raw s z G S m small cut input hist endScratch
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have matchRow:=row_truth sourceIdx rawPorts chronological row past pg ps s _ prior.records (bank_kept d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1) frame
  have final:=receipt d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,matchRow,final⟩
end NativePack255
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed IntegerPacket
set_option maxRecDepth 16000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
/-- Addresses outside the complete running A and B rails, current records, and
the carry and OB5 mirror bank. Historical packets remain observable here. -/
def Exterior (i top q:Nat):Prop :=
  ¬((i+15≤q ∧ q≤top) ∨ (786≤q ∧ q≤1042) ∨ (1556≤q ∧ q≤1812) ∨ (1044+i≤q ∧ q<1044+i+15))
instance (i top q:Nat) : Decidable (Exterior i top q):=by unfold Exterior;infer_instance
theorem raw_away {i top:Nat} (hpos:0 < i) (width:∀a:Fin 15,W.compactSkywalkTickPreWidth (i+a.val)≤257 ∧
    i+a.val+16+W.compactSkywalkTickPreWidth (i+a.val)≤top) {q:Wire} (clear:Exterior i top q):
    ∀a<15,¬RawRead (i+a) q:=by
  intro a ha hit
  obtain ⟨n1,n2⟩:=width ⟨a,ha⟩
  apply clear
  unfold RawRead at hit
  have pos:i+a≠0:=by omega
  simp only [skywalkPoolPreviousId,if_neg pos,base,Wire] at hit
  rcases hit with h|h|h|h|h <;> dsimp only at n1 n2 <;> omega
theorem exterior_origin {i top q:Nat} (lo:0 < i) (bound:i+15≤512)
    (width:∀a:Fin 15,W.compactSkywalkTickPreWidth (i+a.val)≤257 ∧ i+a.val+16+W.compactSkywalkTickPreWidth (i+a.val)≤top)
    (ext:Exterior i top q) (newMap:OB5.sig (i+14) q=q) (oldMap:OB5.sig (i-1) q=q)
    (raw history:State) (same:q∉sites i → history.basis q=(pullState (OB5.sig (i-1)) raw).basis q):
    history.basis q=(origin i raw history).basis q:=by
  by_cases h:q∈sites i
  · exact (inside i raw history q h).symm
  · rw [outside i raw history q h,newMap,span_unchanged i 15 q bound (raw_away lo width ext)]
    simpa only [pullState,oldMap] using same h
theorem ext_head (P:Program) (j:Fin 23) (Q:Program) (effects:List Wire) (s:State) (m n:List Bool) (q:Wire)
    (native:¬MayTouch j (windowNet j q)) (enter:q∉wires P) (admin:q∉effects) (cover:wires Q⊆effects.toFinset) :
    (run (body j Q) n (run P m s)).basis q=s.basis q:=
  (through_body j Q _ n q native (run_preserves_outside Q _ _ q (fun used=>admin (List.mem_toFinset.mp (cover used))))).trans
    (run_preserves_outside P _ _ q enter)
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225StoreCoordinates
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def afterFront:Program := (leave225.drop 242).take 2546
theorem shape : Leave225BeforeStore.program=entry++afterFront := by decide +kernel
def afterFlip:Program := (leave225.drop 93).take 2695
theorem flippedShape : Leave225BeforeStore.program=Leave225InputScan.scanPart++(flipHistory++afterFlip) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let out:=run Leave225BeforeStore.program m s
    out.basis 1723=negative sg a.u ∧ (∀q∈history,out.basis q= !s.basis q) ∧
    (∀i:Fin 11,out.basis (400+i.val)=(a.u+a.v).testBit (144+i.val) ∧
        out.basis (930+i.val)=mag.testBit (144+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  let out:=run Leave225BeforeStore.program m s
  have src:=Leave225Front.result s m z G sg small ready fresh scratch temp
  have stored:=Leave225BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have lowMag:=( Leave225MaskCut.result s m z G sg small ready fresh scratch temp).1
  have raw (q:Wire) (ok:q∉afterFront.map destination):out.basis q=(run entry m s).basis q := by
    change (run Leave225BeforeStore.program m s).basis q=_
    rw [shape,run_append,run_take];exact preserved _ _ _ _ ok
  have truth:=LeaveShadowRails.retainedLow 144 z small sg
  have hist (q:Wire) (hq:q∈history):out.basis q= !s.basis q := by
    let sc:=run Leave225InputScan.scanPart m s
    let tape:=m.drop (measurementCount Leave225InputScan.scanPart)
    let v:=run flipHistory tape sc
    have inv:v=⟨sc.phase,fun q=>if q∈history then !sc.basis q else sc.basis q⟩ := by
      change run flipHistory tape sc=_
      rw [Leave225EntryAction.flipped,notRegister_correct _ (by decide)]
    have bounds:∀q∈history,241≤q ∧ q≤255 := by decide +kernel
    have all : afterFlip.all (fun g=>decide (destination g<241 ∨ 255<destination g))=true := by decide +kernel
    have ok:∀q∈history,q∉afterFlip.map destination := by
      intro q member bad
      obtain ⟨g,hg,rfl⟩:=List.mem_map.mp bad
      have hit := of_decide_eq_true (List.all_eq_true.mp all g hg)
      obtain ⟨l,r⟩:=bounds _ member
      exact hit.elim (Nat.not_lt_of_ge l) (Nat.not_lt_of_ge r)
    change (run Leave225BeforeStore.program m s).basis q=_
    rw [flippedShape,run_append,run_take,run_append,run_take]
    change (run _ _ v).basis q=_
    rw [preserved _ _ _ _ (ok q hq),inv]
    change (if _ then !sc.basis q else sc.basis q)=_
    rw [if_pos hq,preserved _ _ _ _ ((Leave225EntryAction.historyGeom _ hq).1)]
  refine ⟨(raw 1723 (by decide +kernel)).trans (src.2.2.1.trans truth.1.symm),hist,?_⟩
  intro i
  cases ix:i.val with
  | zero =>
    simp only [Nat.add_zero]
    have same:=congrArg (fun n:Nat=>n.testBit 144) truth.2.1
    simp only [Nat.testBit_mod_two_pow,show decide (144<145)=true from rfl,Bool.true_and] at same
    have a0:=src.2.2.2.2.2 0 (by decide)
    rw [Nat.testBit_div_two_pow] at a0
    have bit:=thresholdBit (a.u-(negative sg a.u).toNat) (2^144) (by decide)
    rw [Nat.testBit_div_two_pow] at bit
    exact ⟨(raw 400 (by decide +kernel)).trans (a0.trans same.symm), (stored.2.2.2.2.2.2 _ (by decide) (by decide) (by decide)).trans (lowMag.trans bit.symm)⟩
  | succ j =>
    have hj:j<10:=by have lim:=i.isLt;omega
    have mapA : ∀u:Fin 10,live u.val=400+(u.val+1) := by decide +kernel
    have mapM : ∀u:Fin 10,smallM.getD u.val 0=930+(u.val+1) := by decide +kernel
    have pos:=stored.2.2.2.2.2.1 j (by omega)
    have signedBit:=HighBankAdjust.bit_read smallM j out.basis (by exact hj)
    rw [mapM ⟨j,hj⟩,stored.2.2.2.2.1,Nat.testBit_mod_two_pow,decide_eq_true_eq.mpr hj,Bool.true_and,Nat.testBit_div_two_pow] at signedBit
    change out.basis (live j)=((a.u+a.v)/2^145).testBit j at pos
    rw [mapA ⟨j,hj⟩,Nat.testBit_div_two_pow] at pos
    simpa only [show j+145=144+(j+1) by omega] using And.intro pos signedBit
end ECDSAAdd.Entrant.StairPacket.Leave225StoreCoordinates

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240StoreCoordinates
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def afterFront:Program := (leave240.drop 242).take 2719
theorem shape : Leave240BeforeStore.program=entry++afterFront := by decide +kernel
def afterFlip:Program := (leave240.drop 93).take 2868
theorem flippedShape : Leave240BeforeStore.program=Leave240InputScan.scanPart++(flipHistory++afterFlip) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let out:=run Leave240BeforeStore.program m s
    out.basis 1715=negative sg a.u ∧ (∀q∈history,out.basis q= !s.basis q) ∧
    (∀i:Fin 12,out.basis (407+i.val)=(a.u+a.v).testBit (136+i.val) ∧
        out.basis (922+i.val)=mag.testBit (136+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  let out:=run Leave240BeforeStore.program m s
  have src:=Leave240Front.result s m z G sg small ready fresh scratch temp
  have stored:=Leave240BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have lowMag:=( Leave240MaskCut.result s m z G sg small ready fresh scratch temp).1
  have raw (q:Wire) (ok:q∉afterFront.map destination):out.basis q=(run entry m s).basis q := by
    change (run Leave240BeforeStore.program m s).basis q=_
    rw [shape,run_append,run_take];exact preserved _ _ _ _ ok
  have truth:=LeaveShadowRails.retainedLow 136 z small sg
  have hist (q:Wire) (hq:q∈history):out.basis q= !s.basis q := by
    let sc:=run Leave240InputScan.scanPart m s
    let tape:=m.drop (measurementCount Leave240InputScan.scanPart)
    let v:=run flipHistory tape sc
    have inv:v=⟨sc.phase,fun q=>if q∈history then !sc.basis q else sc.basis q⟩ := by
      change run flipHistory tape sc=_
      rw [Leave240EntryAction.flipped,notRegister_correct _ (by decide)]
    have bounds:∀q∈history,256≤q ∧ q≤270 := by decide +kernel
    have all : afterFlip.all (fun g=>decide (destination g<256 ∨ 270<destination g))=true := by decide +kernel
    have ok:∀q∈history,q∉afterFlip.map destination := by
      intro q member bad
      obtain ⟨g,hg,rfl⟩:=List.mem_map.mp bad
      have hit := of_decide_eq_true (List.all_eq_true.mp all g hg)
      obtain ⟨l,r⟩:=bounds _ member
      exact hit.elim (Nat.not_lt_of_ge l) (Nat.not_lt_of_ge r)
    change (run Leave240BeforeStore.program m s).basis q=_
    rw [flippedShape,run_append,run_take,run_append,run_take]
    change (run _ _ v).basis q=_
    rw [preserved _ _ _ _ (ok q hq),inv]
    change (if _ then !sc.basis q else sc.basis q)=_
    rw [if_pos hq,preserved _ _ _ _ ((Leave240EntryAction.historyGeom _ hq).1)]
  refine ⟨(raw 1715 (by decide +kernel)).trans (src.2.2.1.trans truth.1.symm),hist,?_⟩
  intro i
  cases ix:i.val with
  | zero =>
    simp only [Nat.add_zero]
    have same:=congrArg (fun n:Nat=>n.testBit 136) truth.2.1
    simp only [Nat.testBit_mod_two_pow,show decide (136<137)=true from rfl,Bool.true_and] at same
    have a0:=src.2.2.2.2.2 0 (by decide)
    rw [Nat.testBit_div_two_pow] at a0
    have bit:=thresholdBit (a.u-(negative sg a.u).toNat) (2^136) (by decide)
    rw [Nat.testBit_div_two_pow] at bit
    exact ⟨(raw 407 (by decide +kernel)).trans (a0.trans same.symm), (stored.2.2.2.2.2.2 _ (by decide) (by decide) (by decide)).trans (lowMag.trans bit.symm)⟩
  | succ j =>
    have hj:j<11:=by have lim:=i.isLt;omega
    have mapA : ∀u:Fin 11,live u.val=407+(u.val+1) := by decide +kernel
    have mapM : ∀u:Fin 11,smallM.getD u.val 0=922+(u.val+1) := by decide +kernel
    have pos:=stored.2.2.2.2.2.1 j (by omega)
    have signedBit:=HighBankAdjust.bit_read smallM j out.basis (by exact hj)
    rw [mapM ⟨j,hj⟩,stored.2.2.2.2.1,Nat.testBit_mod_two_pow,decide_eq_true_eq.mpr hj,Bool.true_and,Nat.testBit_div_two_pow] at signedBit
    change out.basis (live j)=((a.u+a.v)/2^137).testBit j at pos
    rw [mapA ⟨j,hj⟩,Nat.testBit_div_two_pow] at pos
    simpa only [show j+137=136+(j+1) by omega] using And.intro pos signedBit
end ECDSAAdd.Entrant.StairPacket.Leave240StoreCoordinates

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255StoreCoordinates
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def afterFront:Program := (leave255.drop 242).take 2861
theorem shape : Leave255BeforeStore.program=entry++afterFront := by decide +kernel
def afterFlip:Program := (leave255.drop 93).take 3010
theorem flippedShape : Leave255BeforeStore.program=Leave255InputScan.scanPart++(flipHistory++afterFlip) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let out:=run Leave255BeforeStore.program m s
    out.basis 1708=negative sg a.u ∧ (∀q∈history,out.basis q= !s.basis q) ∧
    (∀i:Fin 11,out.basis (415+i.val)=(a.u+a.v).testBit (129+i.val) ∧
        out.basis (915+i.val)=mag.testBit (129+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  let out:=run Leave255BeforeStore.program m s
  have src:=Leave255Front.result s m z G sg small ready fresh scratch temp
  have stored:=Leave255BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have lowMag:=( Leave255MaskCut.result s m z G sg small ready fresh scratch temp).1
  have raw (q:Wire) (ok:q∉afterFront.map destination):out.basis q=(run entry m s).basis q := by
    change (run Leave255BeforeStore.program m s).basis q=_
    rw [shape,run_append,run_take];exact preserved _ _ _ _ ok
  have truth:=LeaveShadowRails.retainedLow 129 z small sg
  have hist (q:Wire) (hq:q∈history):out.basis q= !s.basis q := by
    let sc:=run Leave255InputScan.scanPart m s
    let tape:=m.drop (measurementCount Leave255InputScan.scanPart)
    let v:=run flipHistory tape sc
    have inv:v=⟨sc.phase,fun q=>if q∈history then !sc.basis q else sc.basis q⟩ := by
      change run flipHistory tape sc=_
      rw [Leave255EntryAction.flipped,notRegister_correct _ (by decide)]
    have bounds:∀q∈history,271≤q ∧ q≤285 := by decide +kernel
    have all : afterFlip.all (fun g=>decide (destination g<271 ∨ 285<destination g))=true := by decide +kernel
    have ok:∀q∈history,q∉afterFlip.map destination := by
      intro q member bad
      obtain ⟨g,hg,rfl⟩:=List.mem_map.mp bad
      have hit := of_decide_eq_true (List.all_eq_true.mp all g hg)
      obtain ⟨l,r⟩:=bounds _ member
      exact hit.elim (Nat.not_lt_of_ge l) (Nat.not_lt_of_ge r)
    change (run Leave255BeforeStore.program m s).basis q=_
    rw [flippedShape,run_append,run_take,run_append,run_take]
    change (run _ _ v).basis q=_
    rw [preserved _ _ _ _ (ok q hq),inv]
    change (if _ then !sc.basis q else sc.basis q)=_
    rw [if_pos hq,preserved _ _ _ _ ((Leave255EntryAction.historyGeom _ hq).1)]
  refine ⟨(raw 1708 (by decide +kernel)).trans (src.2.2.1.trans truth.1.symm),hist,?_⟩
  intro i
  cases ix:i.val with
  | zero =>
    simp only [Nat.add_zero]
    have same:=congrArg (fun n:Nat=>n.testBit 129) truth.2.1
    simp only [Nat.testBit_mod_two_pow,show decide (129<130)=true from rfl,Bool.true_and] at same
    have a0:=src.2.2.2.2.2 0 (by decide)
    rw [Nat.testBit_div_two_pow] at a0
    have bit:=thresholdBit (a.u-(negative sg a.u).toNat) (2^129) (by decide)
    rw [Nat.testBit_div_two_pow] at bit
    exact ⟨(raw 415 (by decide +kernel)).trans (a0.trans same.symm), (stored.2.2.2.2.2.2 _ (by decide) (by decide) (by decide)).trans (lowMag.trans bit.symm)⟩
  | succ j =>
    have hj:j<10:=by have lim:=i.isLt;omega
    have mapA : ∀u:Fin 10,live u.val=415+(u.val+1) := by decide +kernel
    have mapM : ∀u:Fin 10,smallM.getD u.val 0=915+(u.val+1) := by decide +kernel
    have pos:=stored.2.2.2.2.2.1 j (by omega)
    have signedBit:=HighBankAdjust.bit_read smallM j out.basis (by exact hj)
    rw [mapM ⟨j,hj⟩,stored.2.2.2.2.1,Nat.testBit_mod_two_pow,decide_eq_true_eq.mpr hj,Bool.true_and,Nat.testBit_div_two_pow] at signedBit
    change out.basis (live j)=((a.u+a.v)/2^130).testBit j at pos
    rw [mapA ⟨j,hj⟩,Nat.testBit_div_two_pow] at pos
    simpa only [show j+130=129+(j+1) by omega] using And.intro pos signedBit
end ECDSAAdd.Entrant.StairPacket.Leave255StoreCoordinates

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run body
theorem full_widths : ∀r:Fin 15,W.compactSkywalkTickPreWidth (225+r.val)≤257 ∧
    225+r.val+16+W.compactSkywalkTickPreWidth (225+r.val)≤512:=by decide +kernel
theorem placements (q:Nat) (ext:Exterior 225 512 q) :
    (OB5.sig (225+14) q=q ∧ OB5.sig (225-1) q=q) ∧ ¬MayTouch idx (windowNet idx q):=by
  unfold Exterior at ext
  have newid:OB5.sig (225+14) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  have oldid:OB5.sig (225-1) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  refine ⟨⟨newid,oldid⟩,?_⟩
  change ¬MayTouch idx (OB5.sig (225+14) q)
  rw [newid]
  change ¬((225+15≤q ∧ q≤225+14+16+161+2) ∨ (786≤q ∧ q≤787+161) ∨
    (1556≤q ∧ q≤1556+161) ∨ (1044+225≤q ∧ q<1044+225+15))
  simp only [Wire] at *
  omega
theorem local_set : ∀q∈ports225++[1723,1721,1722]++RailPair.sites Enter225.upperPairs++([]:List Wire),
    ¬Exterior 225 512 q:=by decide +kernel
theorem admin_set : ∀q∈support, ¬Exterior 225 512 q ∨ q∈sites 225:=by decide +kernel
theorem agree_origin (d:Bool) (raw s:State) (m t:List Bool) (neg far long:Bool)
    (packed:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long
      (pullState (OB5.sig 224) raw) s) (q:Wire) (ext:Exterior 225 512 q) :
    let history:=run (body idx (program d)) t (run Partial.enter225 m s)
    history.basis q=(origin 225 raw history).basis q:=by
  have maps:=placements q ext
  apply exterior_origin (by decide) (by decide) full_widths ext maps.1.1 maps.1.2
  intro prev
  have no:q∉ports225++[1723,1721,1722]++RailPair.sites Enter225.upperPairs++([]:List Wire):=fun h=>local_set q h ext
  have noPort : q∉ports225:=fun hit=>no (by simp [hit])
  have noHi : q∉RailPair.sites Enter225.upperPairs:=fun hit=>no (by simp [hit])
  have stay:=ext_head Partial.enter225 idx (program d) support s m t q maps.2
    (fun used=>noPort (List.mem_toFinset.mp (Enter225.programCover used)))
    (fun hit=>(admin_set q hit).elim (fun bad=>bad ext) prev) (packs d)
  have old:=packed.unchanged q (fun eq:q=1723=>no (by simp [eq])) (fun eq:q=1721=>no (by simp [eq])) (fun eq:q=1722=>no (by simp [eq])) noHi
  exact stay.trans old
#print axioms agree_origin
end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run body
theorem full_widths : ∀r:Fin 15,W.compactSkywalkTickPreWidth (240+r.val)≤257 ∧
    240+r.val+16+W.compactSkywalkTickPreWidth (240+r.val)≤527:=by decide +kernel
theorem placements (q:Nat) (ext:Exterior 240 527 q) :
    (OB5.sig (240+14) q=q ∧ OB5.sig (240-1) q=q) ∧ ¬MayTouch idx (windowNet idx q):=by
  unfold Exterior at ext
  have newid:OB5.sig (240+14) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  have oldid:OB5.sig (240-1) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  refine ⟨⟨newid,oldid⟩,?_⟩
  change ¬MayTouch idx (OB5.sig (240+14) q)
  rw [newid]
  change ¬((240+15≤q ∧ q≤240+14+16+153+2) ∨ (786≤q ∧ q≤787+153) ∨
    (1556≤q ∧ q≤1556+153) ∨ (1044+240≤q ∧ q<1044+240+15))
  simp only [Wire] at *
  omega
theorem local_set : ∀q∈ports240++[1715,1713,1714]++RailPair.sites Enter240.upperPairs++Enter240.pending,
    ¬Exterior 240 527 q:=by decide +kernel
theorem admin_set : ∀q∈(support++ArchiveBoundary240.rawPortsList), ¬Exterior 240 527 q ∨ q∈sites 240:=by decide +kernel
theorem agree_origin (d:Bool) (raw s:State) (m t:List Bool) (neg far long:Bool)
    (packed:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s)) (q:Wire) (ext:Exterior 240 527 q) :
    let history:=run (body idx (withArchive d)) t (run Partial.enter240 m s)
    history.basis q=(origin 240 raw history).basis q:=by
  have maps:=placements q ext
  apply exterior_origin (by decide) (by decide) full_widths ext maps.1.1 maps.1.2
  intro prev
  have no:q∉ports240++[1715,1713,1714]++RailPair.sites Enter240.upperPairs++Enter240.pending:=fun h=>local_set q h ext
  have noPort : q∉ports240:=fun hit=>no (by simp [hit])
  have noHi : q∉RailPair.sites Enter240.upperPairs:=fun hit=>no (by simp [hit])
  have stay:=ext_head Partial.enter240 idx (withArchive d) (support++ArchiveBoundary240.rawPortsList) s m t q maps.2
    (fun used=>noPort (List.mem_toFinset.mp (Enter240.programCover used)))
    (fun hit=>(admin_set q hit).elim (fun bad=>bad ext) prev) (admin_cover d)
  have old:=packed.unchanged q (fun eq:q=1715=>no (by simp [eq])) (fun eq:q=1713=>no (by simp [eq])) (fun eq:q=1714=>no (by simp [eq])) noHi
  have unmasked:q∉Enter240.pending:=fun hit=>no (by simp [hit])
  exact stay.trans (by simpa [eraseSites,unmasked] using old)
#print axioms agree_origin
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run body
theorem full_widths : ∀r:Fin 15,W.compactSkywalkTickPreWidth (255+r.val)≤257 ∧
    255+r.val+16+W.compactSkywalkTickPreWidth (255+r.val)≤529:=by decide +kernel
theorem placements (q:Nat) (ext:Exterior 255 529 q) :
    (OB5.sig (255+14) q=q ∧ OB5.sig (255-1) q=q) ∧ ¬MayTouch idx (windowNet idx q):=by
  unfold Exterior at ext
  have newid:OB5.sig (255+14) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  have oldid:OB5.sig (255-1) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  refine ⟨⟨newid,oldid⟩,?_⟩
  change ¬MayTouch idx (OB5.sig (255+14) q)
  rw [newid]
  change ¬((255+15≤q ∧ q≤255+14+16+146+2) ∨ (786≤q ∧ q≤787+146) ∨
    (1556≤q ∧ q≤1556+146) ∨ (1044+255≤q ∧ q<1044+255+15))
  simp only [Wire] at *
  omega
theorem local_set : ∀q∈ports255++[1708,1706,1707]++RailPair.sites Enter255.upperPairs++Enter255.pending,
    ¬Exterior 255 529 q:=by decide +kernel
theorem admin_set : ∀q∈(support++ArchiveBoundary255.rawPortsList), ¬Exterior 255 529 q ∨ q∈sites 255:=by decide +kernel
theorem agree_origin (d:Bool) (raw s:State) (m t:List Bool) (neg far long:Bool)
    (packed:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s)) (q:Wire) (ext:Exterior 255 529 q) :
    let history:=run (body idx (withArchive d)) t (run Partial.enter255 m s)
    history.basis q=(origin 255 raw history).basis q:=by
  have maps:=placements q ext
  apply exterior_origin (by decide) (by decide) full_widths ext maps.1.1 maps.1.2
  intro prev
  have no:q∉ports255++[1708,1706,1707]++RailPair.sites Enter255.upperPairs++Enter255.pending:=fun h=>local_set q h ext
  have noPort : q∉ports255:=fun hit=>no (by simp [hit])
  have noHi : q∉RailPair.sites Enter255.upperPairs:=fun hit=>no (by simp [hit])
  have stay:=ext_head Partial.enter255 idx (withArchive d) (support++ArchiveBoundary255.rawPortsList) s m t q maps.2
    (fun used=>noPort (List.mem_toFinset.mp (Enter255.programCover used)))
    (fun hit=>(admin_set q hit).elim (fun bad=>bad ext) prev) (admin_cover d)
  have old:=packed.unchanged q (fun eq:q=1708=>no (by simp [eq])) (fun eq:q=1706=>no (by simp [eq])) (fun eq:q=1707=>no (by simp [eq])) noHi
  have unmasked:q∉Enter255.pending:=fun hit=>no (by simp [hit])
  exact stay.trans (by simpa [eraseSites,unmasked] using old)
#print axioms agree_origin
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225StoreMapped
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def program := leave225.take 2847
theorem shape : program=Leave225BeforeStore.program++beforeTags := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

private theorem store (s v:State) (m:List Bool) (G sign:Bool) (sum mag:Nat)
    (previous:s.basis 255=G) (hist:∀q∈history,v.basis q= !s.basis q) (signed:v.basis 1723=sign)
    (words:∀i:Fin 11,v.basis (400+i.val)=sum.testBit (144+i.val) ∧ v.basis (930+i.val)=mag.testBit (144+i.val)) :
    let out:=run beforeTags m v
    out.phase=v.phase ∧ (∀q∈history,out.basis q=s.basis q) ∧
    (∀i:Fin 11,let pos:=sum.testBit (144+i.val);let neg:=mag.testBit (144+i.val) ^^ sign
                   out.basis (400+i.val)=(if G then neg else pos) ∧ out.basis (930+i.val)=(if G then pos else neg)) ∧
    ∀q,q∉RailPair.sites low → q∉history → out.basis q=v.basis q := by
  have wrote:=lowResult v m
  let h:=fun q:Wire=>if q∈history then !v.basis q else v.basis q
  have ctrl:h 255=G := by simp only [h,if_pos (by decide : 255∈history),hist 255 (by decide),Bool.not_not,previous]
  have signBit:h 1723=sign := by simpa only [h,if_neg (by decide : 1723∉history)] using signed
  refine ⟨wrote.1,?_,?_,?_⟩
  · intro q hq
    have sep:∀a∈history,a∉RailPair.sites low:=by decide +kernel
    rw [wrote.2.1 q (sep q hq)];simp only [if_pos hq,hist q hq,Bool.not_not]
  · intro i
    let pair:Wire×Wire:=(400+i.val,930+i.val)
    have sites:∀j:Fin 11,(400+j.val,930+j.val)∈low ∧ 400+j.val∉history ∧ 930+j.val∉history:=by decide +kernel
    have l:=wrote.2.2 pair (sites i).1
    change _=(if h 255 then h pair.2 ^^ h 1723 else h pair.1) ∧ _=(if h 255 then h pair.1 else h pair.2 ^^ h 1723) at l
    have pos:h pair.1=sum.testBit (144+i.val):=by simpa only [h,pair,if_neg (sites i).2.1] using (words i).1
    have neg:h pair.2=mag.testBit (144+i.val):=by simpa only [h,pair,if_neg (sites i).2.2] using (words i).2
    rw [ctrl,signBit,pos,neg] at l
    exact l
  · intro q lo hn
    exact (wrote.2.1 q lo).trans (if_neg hn)

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) :
    let a:=SkywalkNat.step^[15] z
    let sign:=negative sg a.u
    let mag:=a.u-sign.toNat
    let before:=run Leave225BeforeStore.program m s
    let out:=run program m s
    out.phase=s.phase ∧ (∀q∈history,out.basis q=s.basis q) ∧
    (∀i:Fin 11,let pos:=(a.u+a.v).testBit (144+i.val);let neg:=mag.testBit (144+i.val) ^^ sign
                   out.basis (400+i.val)=(if G then neg else pos) ∧ out.basis (930+i.val)=(if G then pos else neg)) ∧
    ∀q,q∉RailPair.sites low → q∉history → out.basis q=before.basis q := by
  have coords:=Leave225StoreCoordinates.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have prev:s.basis 255=G := by have h:=ready.2.2.1;cases G <;> exact h
  have phase:=(Leave225BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).1
  have done:=store s _ (m.drop (measurementCount Leave225BeforeStore.program)) G _ _ _ prev coords.2.1 coords.1 coords.2.2
  dsimp only
  rw [shape,run_append,run_take]
  exact ⟨done.1.trans phase,done.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave225StoreMapped

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240StoreMapped
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def program := leave240.take 3024
theorem shape : program=Leave240BeforeStore.program++beforeTags := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

private theorem store (s v:State) (m:List Bool) (G sign:Bool) (sum mag:Nat)
    (previous:s.basis 270=G) (hist:∀q∈history,v.basis q= !s.basis q) (signed:v.basis 1715=sign)
    (words:∀i:Fin 12,v.basis (407+i.val)=sum.testBit (136+i.val) ∧ v.basis (922+i.val)=mag.testBit (136+i.val)) :
    let out:=run beforeTags m v
    out.phase=v.phase ∧ (∀q∈history,out.basis q=s.basis q) ∧
    (∀i:Fin 12,let pos:=sum.testBit (136+i.val);let neg:=mag.testBit (136+i.val) ^^ sign
                   out.basis (407+i.val)=(if G then neg else pos) ∧ out.basis (922+i.val)=(if G then pos else neg)) ∧
    ∀q,q∉RailPair.sites low → q∉history → out.basis q=v.basis q := by
  have wrote:=lowResult v m
  let h:=fun q:Wire=>if q∈history then !v.basis q else v.basis q
  have ctrl:h 270=G := by simp only [h,if_pos (by decide : 270∈history),hist 270 (by decide),Bool.not_not,previous]
  have signBit:h 1715=sign := by simpa only [h,if_neg (by decide : 1715∉history)] using signed
  refine ⟨wrote.1,?_,?_,?_⟩
  · intro q hq
    have sep:∀a∈history,a∉RailPair.sites low:=by decide +kernel
    rw [wrote.2.1 q (sep q hq)];simp only [if_pos hq,hist q hq,Bool.not_not]
  · intro i
    let pair:Wire×Wire:=(407+i.val,922+i.val)
    have sites:∀j:Fin 12,(407+j.val,922+j.val)∈low ∧ 407+j.val∉history ∧ 922+j.val∉history:=by decide +kernel
    have l:=wrote.2.2 pair (sites i).1
    change _=(if h 270 then h pair.2 ^^ h 1715 else h pair.1) ∧ _=(if h 270 then h pair.1 else h pair.2 ^^ h 1715) at l
    have pos:h pair.1=sum.testBit (136+i.val):=by simpa only [h,pair,if_neg (sites i).2.1] using (words i).1
    have neg:h pair.2=mag.testBit (136+i.val):=by simpa only [h,pair,if_neg (sites i).2.2] using (words i).2
    rw [ctrl,signBit,pos,neg] at l
    exact l
  · intro q lo hn
    exact (wrote.2.1 q lo).trans (if_neg hn)

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) :
    let a:=SkywalkNat.step^[15] z
    let sign:=negative sg a.u
    let mag:=a.u-sign.toNat
    let before:=run Leave240BeforeStore.program m s
    let out:=run program m s
    out.phase=s.phase ∧ (∀q∈history,out.basis q=s.basis q) ∧
    (∀i:Fin 12,let pos:=(a.u+a.v).testBit (136+i.val);let neg:=mag.testBit (136+i.val) ^^ sign
                   out.basis (407+i.val)=(if G then neg else pos) ∧ out.basis (922+i.val)=(if G then pos else neg)) ∧
    ∀q,q∉RailPair.sites low → q∉history → out.basis q=before.basis q := by
  have coords:=Leave240StoreCoordinates.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have prev:s.basis 270=G := by have h:=ready.2.2.1;cases G <;> exact h
  have phase:=(Leave240BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).1
  have done:=store s _ (m.drop (measurementCount Leave240BeforeStore.program)) G _ _ _ prev coords.2.1 coords.1 coords.2.2
  dsimp only
  rw [shape,run_append,run_take]
  exact ⟨done.1.trans phase,done.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave240StoreMapped

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255StoreMapped
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def program := leave255.take 3162
theorem shape : program=Leave255BeforeStore.program++beforeTags := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

private theorem store (s v:State) (m:List Bool) (G sign:Bool) (sum mag:Nat)
    (previous:s.basis 285=G) (hist:∀q∈history,v.basis q= !s.basis q) (signed:v.basis 1708=sign)
    (words:∀i:Fin 11,v.basis (415+i.val)=sum.testBit (129+i.val) ∧ v.basis (915+i.val)=mag.testBit (129+i.val)) :
    let out:=run beforeTags m v
    out.phase=v.phase ∧ (∀q∈history,out.basis q=s.basis q) ∧
    (∀i:Fin 11,let pos:=sum.testBit (129+i.val);let neg:=mag.testBit (129+i.val) ^^ sign
                   out.basis (415+i.val)=(if G then neg else pos) ∧ out.basis (915+i.val)=(if G then pos else neg)) ∧
    ∀q,q∉RailPair.sites low → q∉history → out.basis q=v.basis q := by
  have wrote:=lowResult v m
  let h:=fun q:Wire=>if q∈history then !v.basis q else v.basis q
  have ctrl:h 285=G := by simp only [h,if_pos (by decide : 285∈history),hist 285 (by decide),Bool.not_not,previous]
  have signBit:h 1708=sign := by simpa only [h,if_neg (by decide : 1708∉history)] using signed
  refine ⟨wrote.1,?_,?_,?_⟩
  · intro q hq
    have sep:∀a∈history,a∉RailPair.sites low:=by decide +kernel
    rw [wrote.2.1 q (sep q hq)];simp only [if_pos hq,hist q hq,Bool.not_not]
  · intro i
    let pair:Wire×Wire:=(415+i.val,915+i.val)
    have sites:∀j:Fin 11,(415+j.val,915+j.val)∈low ∧ 415+j.val∉history ∧ 915+j.val∉history:=by decide +kernel
    have l:=wrote.2.2 pair (sites i).1
    change _=(if h 285 then h pair.2 ^^ h 1708 else h pair.1) ∧ _=(if h 285 then h pair.1 else h pair.2 ^^ h 1708) at l
    have pos:h pair.1=sum.testBit (129+i.val):=by simpa only [h,pair,if_neg (sites i).2.1] using (words i).1
    have neg:h pair.2=mag.testBit (129+i.val):=by simpa only [h,pair,if_neg (sites i).2.2] using (words i).2
    rw [ctrl,signBit,pos,neg] at l
    exact l
  · intro q lo hn
    exact (wrote.2.1 q lo).trans (if_neg hn)

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) :
    let a:=SkywalkNat.step^[15] z
    let sign:=negative sg a.u
    let mag:=a.u-sign.toNat
    let before:=run Leave255BeforeStore.program m s
    let out:=run program m s
    out.phase=s.phase ∧ (∀q∈history,out.basis q=s.basis q) ∧
    (∀i:Fin 11,let pos:=(a.u+a.v).testBit (129+i.val);let neg:=mag.testBit (129+i.val) ^^ sign
                   out.basis (415+i.val)=(if G then neg else pos) ∧ out.basis (915+i.val)=(if G then pos else neg)) ∧
    ∀q,q∉RailPair.sites low → q∉history → out.basis q=before.basis q := by
  have coords:=Leave255StoreCoordinates.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have prev:s.basis 285=G := by have h:=ready.2.2.1;cases G <;> exact h
  have phase:=(Leave255BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).1
  have done:=store s _ (m.drop (measurementCount Leave255BeforeStore.program)) G _ _ _ prev coords.2.1 coords.1 coords.2.2
  dsimp only
  rw [shape,run_append,run_take]
  exact ⟨done.1.trans phase,done.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave255StoreMapped

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open ArchiveBoundary270 ParkEndpoint Portal270Flag Secp256k1 SkywalkRails StairArchiveTrace
theorem matched_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past G S cross s) :
    let out:=run (p ++ (program d ++ Partial.archiveLoad270 d)) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (Partial.archiveRestore270 d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=row_truth sourceIdx rawPorts chronological row past G S s pre prior.records
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have enc:=source_law d tick e legal
  have act:=load_run d row limit pre f frame
  exact sequence_law p (program d) (Partial.archiveLoad270 d) (Partial.archiveRestore270 d)
    (reverse d) q s m (fun out=>∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run (Partial.archiveLoad270 d) f pre) rfl act.1
    ⟨row,limit,truth,act.2.1⟩ (fun n=>roundtrip d row limit pre f n frame)

theorem matched_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (endUndo d) n out=s :=
  matched_generic EndTick.physP EndTick.physQ d s m step past G S cross odd small prior
theorem matched_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 270 original.basis)
    (hist:raw.basis (base (1028+270))=false) (swapSlot:raw.basis (base (2053-270))=false)
    (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount Partial.park270)
  let one:=run Partial.portal270Inv n (run Partial.park270 m s)
  let tape:=n.drop (measurementCount Partial.portal270Inv)
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot tape
  have eqOne:one=stash s (pullState (OB5.sig 269) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 129 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick.physP tape one):=by rw [eqOne];exact tick
  have body:=matched_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem matched_from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 270 x p raw) (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty⟩:=WideReference.terminal d x raw domain
  exact matched_last d x hx0 hx raw ref s m read stage history swapSlot z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def writesInside (g:Instr) := decide (¬Exterior 225 512 (target g))
private theorem maskleave225Part0 : leave225Part0.all writesInside=true:=by decide +kernel
private theorem maskleave225Part1 : leave225Part1.all writesInside=true:=by decide +kernel
private theorem maskleave225Part2 : leave225Part2.all writesInside=true:=by decide +kernel
private theorem maskleave225Part3 : leave225Part3.all writesInside=true:=by decide +kernel
private theorem maskleave225Part4 : leave225Part4.all writesInside=true:=by decide +kernel
private theorem maskleave225Part5 : leave225Part5.all writesInside=true:=by decide +kernel
private theorem maskleave225Part6 : leave225Part6.all writesInside=true:=by decide +kernel
private theorem maskleave225Part7 : leave225Part7.all writesInside=true:=by decide +kernel
private theorem maskleave225Part8 : leave225Part8.all writesInside=true:=by decide +kernel
private theorem maskleave225Part9 : leave225Part9.all writesInside=true:=by decide +kernel
private theorem maskleave225Part10 : leave225Part10.all writesInside=true:=by decide +kernel
private theorem maskleave225Part11 : leave225Part11.all writesInside=true:=by decide +kernel
private theorem maskleave225Part12 : leave225Part12.all writesInside=true:=by decide +kernel
private theorem maskleave225Part13 : leave225Part13.all writesInside=true:=by decide +kernel
private theorem maskleave225Part14 : leave225Part14.all writesInside=true:=by decide +kernel
private theorem maskleave225Part15 : leave225Part15.all writesInside=true:=by decide +kernel
private theorem maskleave225Part16 : leave225Part16.all writesInside=true:=by decide +kernel
private theorem maskleave225Part17 : leave225Part17.all writesInside=true:=by decide +kernel
private theorem maskleave225Part18 : leave225Part18.all writesInside=true:=by decide +kernel
private theorem maskleave225Part19 : leave225Part19.all writesInside=true:=by decide +kernel
private theorem maskleave225Part20 : leave225Part20.all writesInside=true:=by decide +kernel
private theorem maskleave225Part21 : leave225Part21.all writesInside=true:=by decide +kernel
private theorem maskleave225Part22 : leave225Part22.all writesInside=true:=by decide +kernel
private theorem maskleave225Part23 : leave225Part23.all writesInside=true:=by decide +kernel
private theorem maskleave225Part24 : leave225Part24.all writesInside=true:=by decide +kernel
private theorem maskleave225Part25 : leave225Part25.all writesInside=true:=by decide +kernel
private theorem maskleave225Part26 : leave225Part26.all writesInside=true:=by decide +kernel
private theorem maskleave225Part27 : leave225Part27.all writesInside=true:=by decide +kernel
private theorem maskleave225Part28 : leave225Part28.all writesInside=true:=by decide +kernel
private theorem maskleave225Part29 : leave225Part29.all writesInside=true:=by decide +kernel
private theorem maskleave225Part30 : leave225Part30.all writesInside=true:=by decide +kernel
private theorem maskleave225Part31 : leave225Part31.all writesInside=true:=by decide +kernel
private theorem maskleave225Part32 : leave225Part32.all writesInside=true:=by decide +kernel
private theorem maskleave225Part33 : leave225Part33.all writesInside=true:=by decide +kernel
theorem writes : leave225.all writesInside=true:=by
  simp only [leave225,List.all_append,maskleave225Part0,maskleave225Part1,maskleave225Part2,maskleave225Part3,maskleave225Part4,maskleave225Part5,maskleave225Part6,maskleave225Part7,maskleave225Part8,maskleave225Part9,maskleave225Part10,maskleave225Part11,maskleave225Part12,maskleave225Part13,maskleave225Part14,maskleave225Part15,maskleave225Part16,maskleave225Part17,maskleave225Part18,maskleave225Part19,maskleave225Part20,maskleave225Part21,maskleave225Part22,maskleave225Part23,maskleave225Part24,maskleave225Part25,maskleave225Part26,maskleave225Part27,maskleave225Part28,maskleave225Part29,maskleave225Part30,maskleave225Part31,maskleave225Part32,maskleave225Part33,Bool.and_self]
theorem exterior (s:State) (m:List Bool) (q:Wire) (ext:Exterior 225 512 q):
    (run leave225 m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 225 512 (target g):=of_decide_eq_true (List.all_eq_true.mp writes g hit)
  exact clean (eq.symm ▸ ext)
private theorem maskleave225InvPart0 : leave225InvPart0.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart1 : leave225InvPart1.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart2 : leave225InvPart2.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart3 : leave225InvPart3.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart4 : leave225InvPart4.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart5 : leave225InvPart5.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart6 : leave225InvPart6.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart7 : leave225InvPart7.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart8 : leave225InvPart8.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart9 : leave225InvPart9.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart10 : leave225InvPart10.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart11 : leave225InvPart11.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart12 : leave225InvPart12.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart13 : leave225InvPart13.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart14 : leave225InvPart14.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart15 : leave225InvPart15.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart16 : leave225InvPart16.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart17 : leave225InvPart17.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart18 : leave225InvPart18.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart19 : leave225InvPart19.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart20 : leave225InvPart20.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart21 : leave225InvPart21.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart22 : leave225InvPart22.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart23 : leave225InvPart23.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart24 : leave225InvPart24.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart25 : leave225InvPart25.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart26 : leave225InvPart26.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart27 : leave225InvPart27.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart28 : leave225InvPart28.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart29 : leave225InvPart29.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart30 : leave225InvPart30.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart31 : leave225InvPart31.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart32 : leave225InvPart32.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart33 : leave225InvPart33.all writesInside=true:=by decide +kernel
theorem writesInv : leave225Inv.all writesInside=true:=by
  simp only [leave225Inv,List.all_append,maskleave225InvPart0,maskleave225InvPart1,maskleave225InvPart2,maskleave225InvPart3,maskleave225InvPart4,maskleave225InvPart5,maskleave225InvPart6,maskleave225InvPart7,maskleave225InvPart8,maskleave225InvPart9,maskleave225InvPart10,maskleave225InvPart11,maskleave225InvPart12,maskleave225InvPart13,maskleave225InvPart14,maskleave225InvPart15,maskleave225InvPart16,maskleave225InvPart17,maskleave225InvPart18,maskleave225InvPart19,maskleave225InvPart20,maskleave225InvPart21,maskleave225InvPart22,maskleave225InvPart23,maskleave225InvPart24,maskleave225InvPart25,maskleave225InvPart26,maskleave225InvPart27,maskleave225InvPart28,maskleave225InvPart29,maskleave225InvPart30,maskleave225InvPart31,maskleave225InvPart32,maskleave225InvPart33,Bool.and_self]
theorem exteriorInv (s:State) (m:List Bool) (q:Wire) (ext:Exterior 225 512 q):
    (run leave225Inv m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 225 512 (target g):=of_decide_eq_true (List.all_eq_true.mp writesInv g hit)
  exact clean (eq.symm ▸ ext)
#print axioms exteriorInv
end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def writesInside (g:Instr) := decide (¬Exterior 240 527 (target g))
private theorem maskleave240Part0 : leave240Part0.all writesInside=true:=by decide +kernel
private theorem maskleave240Part1 : leave240Part1.all writesInside=true:=by decide +kernel
private theorem maskleave240Part2 : leave240Part2.all writesInside=true:=by decide +kernel
private theorem maskleave240Part3 : leave240Part3.all writesInside=true:=by decide +kernel
private theorem maskleave240Part4 : leave240Part4.all writesInside=true:=by decide +kernel
private theorem maskleave240Part5 : leave240Part5.all writesInside=true:=by decide +kernel
private theorem maskleave240Part6 : leave240Part6.all writesInside=true:=by decide +kernel
private theorem maskleave240Part7 : leave240Part7.all writesInside=true:=by decide +kernel
private theorem maskleave240Part8 : leave240Part8.all writesInside=true:=by decide +kernel
private theorem maskleave240Part9 : leave240Part9.all writesInside=true:=by decide +kernel
private theorem maskleave240Part10 : leave240Part10.all writesInside=true:=by decide +kernel
private theorem maskleave240Part11 : leave240Part11.all writesInside=true:=by decide +kernel
private theorem maskleave240Part12 : leave240Part12.all writesInside=true:=by decide +kernel
private theorem maskleave240Part13 : leave240Part13.all writesInside=true:=by decide +kernel
private theorem maskleave240Part14 : leave240Part14.all writesInside=true:=by decide +kernel
private theorem maskleave240Part15 : leave240Part15.all writesInside=true:=by decide +kernel
private theorem maskleave240Part16 : leave240Part16.all writesInside=true:=by decide +kernel
private theorem maskleave240Part17 : leave240Part17.all writesInside=true:=by decide +kernel
private theorem maskleave240Part18 : leave240Part18.all writesInside=true:=by decide +kernel
private theorem maskleave240Part19 : leave240Part19.all writesInside=true:=by decide +kernel
private theorem maskleave240Part20 : leave240Part20.all writesInside=true:=by decide +kernel
private theorem maskleave240Part21 : leave240Part21.all writesInside=true:=by decide +kernel
private theorem maskleave240Part22 : leave240Part22.all writesInside=true:=by decide +kernel
private theorem maskleave240Part23 : leave240Part23.all writesInside=true:=by decide +kernel
private theorem maskleave240Part24 : leave240Part24.all writesInside=true:=by decide +kernel
private theorem maskleave240Part25 : leave240Part25.all writesInside=true:=by decide +kernel
private theorem maskleave240Part26 : leave240Part26.all writesInside=true:=by decide +kernel
private theorem maskleave240Part27 : leave240Part27.all writesInside=true:=by decide +kernel
private theorem maskleave240Part28 : leave240Part28.all writesInside=true:=by decide +kernel
private theorem maskleave240Part29 : leave240Part29.all writesInside=true:=by decide +kernel
private theorem maskleave240Part30 : leave240Part30.all writesInside=true:=by decide +kernel
private theorem maskleave240Part31 : leave240Part31.all writesInside=true:=by decide +kernel
private theorem maskleave240Part32 : leave240Part32.all writesInside=true:=by decide +kernel
private theorem maskleave240Part33 : leave240Part33.all writesInside=true:=by decide +kernel
private theorem maskleave240Part34 : leave240Part34.all writesInside=true:=by decide +kernel
private theorem maskleave240Part35 : leave240Part35.all writesInside=true:=by decide +kernel
theorem writes : leave240.all writesInside=true:=by
  simp only [leave240,List.all_append,maskleave240Part0,maskleave240Part1,maskleave240Part2,maskleave240Part3,maskleave240Part4,maskleave240Part5,maskleave240Part6,maskleave240Part7,maskleave240Part8,maskleave240Part9,maskleave240Part10,maskleave240Part11,maskleave240Part12,maskleave240Part13,maskleave240Part14,maskleave240Part15,maskleave240Part16,maskleave240Part17,maskleave240Part18,maskleave240Part19,maskleave240Part20,maskleave240Part21,maskleave240Part22,maskleave240Part23,maskleave240Part24,maskleave240Part25,maskleave240Part26,maskleave240Part27,maskleave240Part28,maskleave240Part29,maskleave240Part30,maskleave240Part31,maskleave240Part32,maskleave240Part33,maskleave240Part34,maskleave240Part35,Bool.and_self]
theorem exterior (s:State) (m:List Bool) (q:Wire) (ext:Exterior 240 527 q):
    (run leave240 m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 240 527 (target g):=of_decide_eq_true (List.all_eq_true.mp writes g hit)
  exact clean (eq.symm ▸ ext)
private theorem maskleave240InvPart0 : leave240InvPart0.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart1 : leave240InvPart1.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart2 : leave240InvPart2.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart3 : leave240InvPart3.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart4 : leave240InvPart4.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart5 : leave240InvPart5.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart6 : leave240InvPart6.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart7 : leave240InvPart7.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart8 : leave240InvPart8.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart9 : leave240InvPart9.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart10 : leave240InvPart10.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart11 : leave240InvPart11.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart12 : leave240InvPart12.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart13 : leave240InvPart13.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart14 : leave240InvPart14.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart15 : leave240InvPart15.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart16 : leave240InvPart16.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart17 : leave240InvPart17.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart18 : leave240InvPart18.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart19 : leave240InvPart19.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart20 : leave240InvPart20.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart21 : leave240InvPart21.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart22 : leave240InvPart22.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart23 : leave240InvPart23.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart24 : leave240InvPart24.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart25 : leave240InvPart25.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart26 : leave240InvPart26.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart27 : leave240InvPart27.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart28 : leave240InvPart28.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart29 : leave240InvPart29.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart30 : leave240InvPart30.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart31 : leave240InvPart31.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart32 : leave240InvPart32.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart33 : leave240InvPart33.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart34 : leave240InvPart34.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart35 : leave240InvPart35.all writesInside=true:=by decide +kernel
theorem writesInv : leave240Inv.all writesInside=true:=by
  simp only [leave240Inv,List.all_append,maskleave240InvPart0,maskleave240InvPart1,maskleave240InvPart2,maskleave240InvPart3,maskleave240InvPart4,maskleave240InvPart5,maskleave240InvPart6,maskleave240InvPart7,maskleave240InvPart8,maskleave240InvPart9,maskleave240InvPart10,maskleave240InvPart11,maskleave240InvPart12,maskleave240InvPart13,maskleave240InvPart14,maskleave240InvPart15,maskleave240InvPart16,maskleave240InvPart17,maskleave240InvPart18,maskleave240InvPart19,maskleave240InvPart20,maskleave240InvPart21,maskleave240InvPart22,maskleave240InvPart23,maskleave240InvPart24,maskleave240InvPart25,maskleave240InvPart26,maskleave240InvPart27,maskleave240InvPart28,maskleave240InvPart29,maskleave240InvPart30,maskleave240InvPart31,maskleave240InvPart32,maskleave240InvPart33,maskleave240InvPart34,maskleave240InvPart35,Bool.and_self]
theorem exteriorInv (s:State) (m:List Bool) (q:Wire) (ext:Exterior 240 527 q):
    (run leave240Inv m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 240 527 (target g):=of_decide_eq_true (List.all_eq_true.mp writesInv g hit)
  exact clean (eq.symm ▸ ext)
#print axioms exteriorInv
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def writesInside (g:Instr) := decide (¬Exterior 255 529 (target g))
private theorem maskleave255Part0 : leave255Part0.all writesInside=true:=by decide +kernel
private theorem maskleave255Part1 : leave255Part1.all writesInside=true:=by decide +kernel
private theorem maskleave255Part2 : leave255Part2.all writesInside=true:=by decide +kernel
private theorem maskleave255Part3 : leave255Part3.all writesInside=true:=by decide +kernel
private theorem maskleave255Part4 : leave255Part4.all writesInside=true:=by decide +kernel
private theorem maskleave255Part5 : leave255Part5.all writesInside=true:=by decide +kernel
private theorem maskleave255Part6 : leave255Part6.all writesInside=true:=by decide +kernel
private theorem maskleave255Part7 : leave255Part7.all writesInside=true:=by decide +kernel
private theorem maskleave255Part8 : leave255Part8.all writesInside=true:=by decide +kernel
private theorem maskleave255Part9 : leave255Part9.all writesInside=true:=by decide +kernel
private theorem maskleave255Part10 : leave255Part10.all writesInside=true:=by decide +kernel
private theorem maskleave255Part11 : leave255Part11.all writesInside=true:=by decide +kernel
private theorem maskleave255Part12 : leave255Part12.all writesInside=true:=by decide +kernel
private theorem maskleave255Part13 : leave255Part13.all writesInside=true:=by decide +kernel
private theorem maskleave255Part14 : leave255Part14.all writesInside=true:=by decide +kernel
private theorem maskleave255Part15 : leave255Part15.all writesInside=true:=by decide +kernel
private theorem maskleave255Part16 : leave255Part16.all writesInside=true:=by decide +kernel
private theorem maskleave255Part17 : leave255Part17.all writesInside=true:=by decide +kernel
private theorem maskleave255Part18 : leave255Part18.all writesInside=true:=by decide +kernel
private theorem maskleave255Part19 : leave255Part19.all writesInside=true:=by decide +kernel
private theorem maskleave255Part20 : leave255Part20.all writesInside=true:=by decide +kernel
private theorem maskleave255Part21 : leave255Part21.all writesInside=true:=by decide +kernel
private theorem maskleave255Part22 : leave255Part22.all writesInside=true:=by decide +kernel
private theorem maskleave255Part23 : leave255Part23.all writesInside=true:=by decide +kernel
private theorem maskleave255Part24 : leave255Part24.all writesInside=true:=by decide +kernel
private theorem maskleave255Part25 : leave255Part25.all writesInside=true:=by decide +kernel
private theorem maskleave255Part26 : leave255Part26.all writesInside=true:=by decide +kernel
private theorem maskleave255Part27 : leave255Part27.all writesInside=true:=by decide +kernel
private theorem maskleave255Part28 : leave255Part28.all writesInside=true:=by decide +kernel
private theorem maskleave255Part29 : leave255Part29.all writesInside=true:=by decide +kernel
private theorem maskleave255Part30 : leave255Part30.all writesInside=true:=by decide +kernel
private theorem maskleave255Part31 : leave255Part31.all writesInside=true:=by decide +kernel
private theorem maskleave255Part32 : leave255Part32.all writesInside=true:=by decide +kernel
private theorem maskleave255Part33 : leave255Part33.all writesInside=true:=by decide +kernel
private theorem maskleave255Part34 : leave255Part34.all writesInside=true:=by decide +kernel
private theorem maskleave255Part35 : leave255Part35.all writesInside=true:=by decide +kernel
private theorem maskleave255Part36 : leave255Part36.all writesInside=true:=by decide +kernel
theorem writes : leave255.all writesInside=true:=by
  simp only [leave255,List.all_append,maskleave255Part0,maskleave255Part1,maskleave255Part2,maskleave255Part3,maskleave255Part4,maskleave255Part5,maskleave255Part6,maskleave255Part7,maskleave255Part8,maskleave255Part9,maskleave255Part10,maskleave255Part11,maskleave255Part12,maskleave255Part13,maskleave255Part14,maskleave255Part15,maskleave255Part16,maskleave255Part17,maskleave255Part18,maskleave255Part19,maskleave255Part20,maskleave255Part21,maskleave255Part22,maskleave255Part23,maskleave255Part24,maskleave255Part25,maskleave255Part26,maskleave255Part27,maskleave255Part28,maskleave255Part29,maskleave255Part30,maskleave255Part31,maskleave255Part32,maskleave255Part33,maskleave255Part34,maskleave255Part35,maskleave255Part36,Bool.and_self]
theorem exterior (s:State) (m:List Bool) (q:Wire) (ext:Exterior 255 529 q):
    (run leave255 m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 255 529 (target g):=of_decide_eq_true (List.all_eq_true.mp writes g hit)
  exact clean (eq.symm ▸ ext)
private theorem maskleave255InvPart0 : leave255InvPart0.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart1 : leave255InvPart1.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart2 : leave255InvPart2.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart3 : leave255InvPart3.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart4 : leave255InvPart4.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart5 : leave255InvPart5.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart6 : leave255InvPart6.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart7 : leave255InvPart7.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart8 : leave255InvPart8.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart9 : leave255InvPart9.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart10 : leave255InvPart10.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart11 : leave255InvPart11.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart12 : leave255InvPart12.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart13 : leave255InvPart13.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart14 : leave255InvPart14.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart15 : leave255InvPart15.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart16 : leave255InvPart16.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart17 : leave255InvPart17.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart18 : leave255InvPart18.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart19 : leave255InvPart19.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart20 : leave255InvPart20.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart21 : leave255InvPart21.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart22 : leave255InvPart22.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart23 : leave255InvPart23.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart24 : leave255InvPart24.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart25 : leave255InvPart25.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart26 : leave255InvPart26.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart27 : leave255InvPart27.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart28 : leave255InvPart28.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart29 : leave255InvPart29.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart30 : leave255InvPart30.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart31 : leave255InvPart31.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart32 : leave255InvPart32.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart33 : leave255InvPart33.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart34 : leave255InvPart34.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart35 : leave255InvPart35.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart36 : leave255InvPart36.all writesInside=true:=by decide +kernel
theorem writesInv : leave255Inv.all writesInside=true:=by
  simp only [leave255Inv,List.all_append,maskleave255InvPart0,maskleave255InvPart1,maskleave255InvPart2,maskleave255InvPart3,maskleave255InvPart4,maskleave255InvPart5,maskleave255InvPart6,maskleave255InvPart7,maskleave255InvPart8,maskleave255InvPart9,maskleave255InvPart10,maskleave255InvPart11,maskleave255InvPart12,maskleave255InvPart13,maskleave255InvPart14,maskleave255InvPart15,maskleave255InvPart16,maskleave255InvPart17,maskleave255InvPart18,maskleave255InvPart19,maskleave255InvPart20,maskleave255InvPart21,maskleave255InvPart22,maskleave255InvPart23,maskleave255InvPart24,maskleave255InvPart25,maskleave255InvPart26,maskleave255InvPart27,maskleave255InvPart28,maskleave255InvPart29,maskleave255InvPart30,maskleave255InvPart31,maskleave255InvPart32,maskleave255InvPart33,maskleave255InvPart34,maskleave255InvPart35,maskleave255InvPart36,Bool.and_self]
theorem exteriorInv (s:State) (m:List Bool) (q:Wire) (ext:Exterior 255 529 q):
    (run leave255Inv m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 255 529 (target g):=of_decide_eq_true (List.all_eq_true.mp writesInv g hit)
  exact clean (eq.symm ▸ ext)
#print axioms exteriorInv
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave225FullArithmetic Leave225Word Leave225Join Leave225Close
theorem untouchedHigh (q:Nat) (h:419≤q ∧ q≤512) : q∉Leave225StoreMapped.program.map destination := by
  have all:Leave225StoreMapped.program.all (fun g=>decide (destination g<419 ∨ 512<destination g))=true:=by decide +kernel
  intro m
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp m
  exact (of_decide_eq_true (List.all_eq_true.mp all g hg)).elim (Nat.not_lt_of_ge h.1) (Nat.not_lt_of_ge h.2)
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z))) (top:∀q:Nat,419≤q → q≤512 → s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) :
    ∀i:Fin 102,(run Leave225StoreMapped.program m s).basis (411+i.val)=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  have front:=Leave225Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave225FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 112,97 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave225Hit.swaps i):=by decide +kernel
  have used:=Leave225Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave225EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave225EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave225RoutedRestore.result z sg a n (n.drop (measurementCount Leave225Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  have store:=(Leave225StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flag:=(Leave225BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  let q:Nat:=411+i.val
  by_cases ext:419≤q
  · have hi:q≤512 := by dsimp [q]; have h:=i.isLt;omega
    exact (preserved Leave225StoreMapped.program s m q (untouchedHigh q ⟨ext,hi⟩)).trans (top q ext hi)
  · have lim:i.val<8 := by dsimp [q] at ext;omega
    let j:Fin 8:=⟨i.val,lim⟩
    have geom:∀j:Fin 8,let q:Nat:=411+j.val
        q∉RailPair.sites low ∧ q∉history ∧ q≠1556 ∧ q≠1557 ∧ q≠1558 ∧ q∉smallM ∧ ∃i:Fin 18,q=(row i).free := by decide +kernel
    obtain ⟨l,h,x,y,z,mr,idx,e⟩:=geom j
    rw [store _ l h,flag _ x y z]
    rw [Leave225FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ mr]
    exact e ▸ used.2.2.1 idx
end ECDSAAdd.Entrant.StairPacket.Leave225HighZero

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225PostReady
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def suffix:= (leave225.drop 334).take 2513
theorem split : Leave225StoreMapped.program=(entry++fullPrefix false)++suffix := by decide +kernel
def rawSites := [1721,1722]++(Leave225Close.events.map Prod.fst)

private theorem avoid (prg:Program) (sites:List Wire) (checked:prg.all (fun g=>decide (destination g∉sites))=true) (q:Wire) (mem:q∈sites) :
    q∉prg.map destination := by
  intro bad
  obtain ⟨g,h,rfl⟩:=List.mem_map.mp bad
  exact (of_decide_eq_true (List.all_eq_true.mp checked _ h)) mem

theorem rawLayout:∀q∈rawSites,q∉Leave225StoreMapped.program.map destination := avoid _ _ (by decide +kernel)
theorem keptLayout:∀q∈[1724,1725],q∉suffix.map destination := avoid _ _ (by decide +kernel)

private theorem nearOf (p:Ports) (k:Mode) (sym:Sym) (controls:reads p sym=LeaveSelector.controls p k):
    sym p.near=.bit (nearby k) := by
  simp only [reads,LeaveSelector.controls,List.cons.injEq,and_true,eq_self] at controls
  exact controls.1
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) :
    let out:=run Leave225StoreMapped.program m s
    let f:=decide (Shadow.far 144 15 z)
    out.basis 1721=s.basis 1721 ∧ out.basis 1722=s.basis 1722 ∧
    out.basis 1725=nearby (actualMode 144 z) ∧
    out.basis 1724=(f && HighBankSum.cross (Leave225TrueMiddle.d z)) ∧
    (∀p∈Leave225Close.events,out.basis p.1=s.basis p.1 ∧ out.basis p.2=false) := by
  let a:=run entry m s
  let k:=actualMode 144 z
  let o:=run Leave225StoreMapped.program m s
  have selRaw (q:Wire) (ok:q∉entry.map destination):a.basis q=s.basis q := preserved entry s m q ok
  have sw:∀i:Fin 15,Leave225Hit.swaps i∉entry.map destination:=by decide +kernel
  have prepared:=Leave225FrontPrepare.prepare s m z G sg small ready fresh scratch temp zero k z.u
    (by change k=farMode (a.basis _) (a.basis _) z.u;rw [selRaw _ (by decide),selRaw _ (by decide)];exact mode)
    (fun on i hi h=>(selRaw _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  have hit (q:Wire) (ok:q∈[1724,1725]):o.basis q=(Leave225RetireActual.prior k q).read a.basis := by
    change (run Leave225StoreMapped.program m s).basis q=_
    rw [split,run_append,run_take,preserved _ _ _ q (keptLayout q ok),prepared];rfl
  have h:=Leave225Front.result s m z G sg small ready fresh scratch temp
  have act:=Leave225EntryAction.upperBits _ a.basis h.2.2.2.2.2
  have math:=Leave225Loaded.signed z a.basis small odd room (fun i hi=>act i (Nat.lt_trans hi (by decide : 16<18)))
    ((Leave225EntryAction.parity s m).trans par)
  have near:Leave225RetireActual.prior k 1725=.bit (nearby k) := nearOf ports k _ (controlCert k)
  have plain (q:Wire) (ok:q∈rawSites):o.basis q=s.basis q:=preserved _ _ _ _ (rawLayout q ok)
  have store:=(Leave225StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave225BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have cleared:=Leave225FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  refine ⟨plain _ (by decide),plain _ (by decide),(hit _ (by decide)).trans (congrArg (Expr.read a.basis) near),?_,?_⟩
  · refine (hit _ (by decide)).trans (math.1.trans ?_);by_cases g:Shadow.far 144 15 z <;> simp [g]
  · intro p member
    have geom:∀p∈Leave225Close.events,p.1∈rawSites ∧ p.2∉RailPair.sites low ∧ p.2∉history ∧
      (p.2=1556 ∨ (p.2≠1556 ∧ p.2≠1557 ∧ p.2≠1558 ∧ p.2∈Leave225FlagScratch.targets)) := by decide +kernel
    obtain ⟨src,nl,nh,dst⟩:=geom _ member
    refine ⟨plain _ src,(store _ nl nh).trans ?_⟩
    rcases dst with e|⟨a,b,c,hq⟩
    · rw [e];exact flags.2.1
    · exact (flags.2.2.2.2.2.2 _ a b c).trans (cleared _ hq)
end ECDSAAdd.Entrant.StairPacket.Leave225PostReady

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave240FullArithmetic Leave240Word Leave240Join Leave240Close
theorem untouchedHigh (q:Nat) (h:426≤q ∧ q≤527) : q∉Leave240StoreMapped.program.map destination := by
  have all:Leave240StoreMapped.program.all (fun g=>decide (destination g<426 ∨ 527<destination g))=true:=by decide +kernel
  intro m
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp m
  exact (of_decide_eq_true (List.all_eq_true.mp all g hg)).elim (Nat.not_lt_of_ge h.1) (Nat.not_lt_of_ge h.2)
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z))) (top:∀q:Nat,426≤q → q≤527 → s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) :
    ∀i:Fin 109,(run Leave240StoreMapped.program m s).basis (419+i.val)=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  have front:=Leave240Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave240FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 120,105 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave240Hit.swaps i):=by decide +kernel
  have used:=Leave240Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave240EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave240EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave240RoutedRestore.result z sg a n (n.drop (measurementCount Leave240Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  have store:=(Leave240StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flag:=(Leave240BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  let q:Nat:=419+i.val
  by_cases ext:426≤q
  · have hi:q≤527 := by dsimp [q]; have h:=i.isLt;omega
    exact (preserved Leave240StoreMapped.program s m q (untouchedHigh q ⟨ext,hi⟩)).trans (top q ext hi)
  · have lim:i.val<7 := by dsimp [q] at ext;omega
    let j:Fin 7:=⟨i.val,lim⟩
    have geom:∀j:Fin 7,let q:Nat:=419+j.val
        q∉RailPair.sites low ∧ q∉history ∧ q≠1556 ∧ q≠1557 ∧ q≠1558 ∧ q∉smallM ∧ ∃i:Fin 18,q=(row i).free := by decide +kernel
    obtain ⟨l,h,x,y,z,mr,idx,e⟩:=geom j
    rw [store _ l h,flag _ x y z]
    rw [Leave240FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ mr]
    exact e ▸ used.2.2.1 idx
end ECDSAAdd.Entrant.StairPacket.Leave240HighZero

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240PostReady
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def suffix:= (leave240.drop 334).take 2690
theorem split : Leave240StoreMapped.program=(entry++fullPrefix false)++suffix := by decide +kernel
def rawSites := [1713,1714]++(Leave240Close.events.map Prod.fst)

private theorem avoid (prg:Program) (sites:List Wire) (checked:prg.all (fun g=>decide (destination g∉sites))=true) (q:Wire) (mem:q∈sites) :
    q∉prg.map destination := by
  intro bad
  obtain ⟨g,h,rfl⟩:=List.mem_map.mp bad
  exact (of_decide_eq_true (List.all_eq_true.mp checked _ h)) mem

theorem rawLayout:∀q∈rawSites,q∉Leave240StoreMapped.program.map destination := avoid _ _ (by decide +kernel)
theorem keptLayout:∀q∈[1716,1717],q∉suffix.map destination := avoid _ _ (by decide +kernel)

private theorem nearOf (p:Ports) (k:Mode) (sym:Sym) (controls:reads p sym=LeaveSelector.controls p k):
    sym p.near=.bit (nearby k) := by
  simp only [reads,LeaveSelector.controls,List.cons.injEq,and_true,eq_self] at controls
  exact controls.1
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) :
    let out:=run Leave240StoreMapped.program m s
    let f:=decide (Shadow.far 136 15 z)
    out.basis 1713=s.basis 1713 ∧ out.basis 1714=s.basis 1714 ∧
    out.basis 1717=nearby (actualMode 136 z) ∧
    out.basis 1716=(f && HighBankSum.cross (Leave240TrueMiddle.d z)) ∧
    (∀p∈Leave240Close.events,out.basis p.1=s.basis p.1 ∧ out.basis p.2=false) := by
  let a:=run entry m s
  let k:=actualMode 136 z
  let o:=run Leave240StoreMapped.program m s
  have selRaw (q:Wire) (ok:q∉entry.map destination):a.basis q=s.basis q := preserved entry s m q ok
  have sw:∀i:Fin 15,Leave240Hit.swaps i∉entry.map destination:=by decide +kernel
  have prepared:=Leave240FrontPrepare.prepare s m z G sg small ready fresh scratch temp zero k z.u
    (by change k=farMode (a.basis _) (a.basis _) z.u;rw [selRaw _ (by decide),selRaw _ (by decide)];exact mode)
    (fun on i hi h=>(selRaw _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  have hit (q:Wire) (ok:q∈[1716,1717]):o.basis q=(Leave240RetireActual.prior k q).read a.basis := by
    change (run Leave240StoreMapped.program m s).basis q=_
    rw [split,run_append,run_take,preserved _ _ _ q (keptLayout q ok),prepared];rfl
  have h:=Leave240Front.result s m z G sg small ready fresh scratch temp
  have act:=Leave240EntryAction.upperBits _ a.basis h.2.2.2.2.2
  have math:=Leave240Loaded.signed z a.basis small odd room (fun i hi=>act i (Nat.lt_trans hi (by decide : 16<18)))
    ((Leave240EntryAction.parity s m).trans par)
  have near:Leave240RetireActual.prior k 1717=.bit (nearby k) := nearOf ports k _ (controlCert k)
  have plain (q:Wire) (ok:q∈rawSites):o.basis q=s.basis q:=preserved _ _ _ _ (rawLayout q ok)
  have store:=(Leave240StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave240BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have cleared:=Leave240FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  refine ⟨plain _ (by decide),plain _ (by decide),(hit _ (by decide)).trans (congrArg (Expr.read a.basis) near),?_,?_⟩
  · refine (hit _ (by decide)).trans (math.1.trans ?_);by_cases g:Shadow.far 136 15 z <;> simp [g]
  · intro p member
    have geom:∀p∈Leave240Close.events,p.1∈rawSites ∧ p.2∉RailPair.sites low ∧ p.2∉history ∧
      (p.2=1556 ∨ (p.2≠1556 ∧ p.2≠1557 ∧ p.2≠1558 ∧ p.2∈Leave240FlagScratch.targets)) := by decide +kernel
    obtain ⟨src,nl,nh,dst⟩:=geom _ member
    refine ⟨plain _ src,(store _ nl nh).trans ?_⟩
    rcases dst with e|⟨a,b,c,hq⟩
    · rw [e];exact flags.2.1
    · exact (flags.2.2.2.2.2.2 _ a b c).trans (cleared _ hq)
end ECDSAAdd.Entrant.StairPacket.Leave240PostReady

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave255FullArithmetic Leave255Word Leave255Join Leave255Close
theorem untouchedHigh (q:Nat) (h:434≤q ∧ q≤528) : q∉Leave255StoreMapped.program.map destination := by
  have all:Leave255StoreMapped.program.all (fun g=>decide (destination g<434 ∨ 528<destination g))=true:=by decide +kernel
  intro m
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp m
  exact (of_decide_eq_true (List.all_eq_true.mp all g hg)).elim (Nat.not_lt_of_ge h.1) (Nat.not_lt_of_ge h.2)
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z))) (top:∀q:Nat,434≤q → q≤528 → s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) :
    ∀i:Fin 103,(run Leave255StoreMapped.program m s).basis (426+i.val)=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  have front:=Leave255Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave255FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 127,112 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave255Hit.swaps i):=by decide +kernel
  have used:=Leave255Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave255EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave255EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave255RoutedRestore.result z sg a n (n.drop (measurementCount Leave255Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  have store:=(Leave255StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flag:=(Leave255BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  let q:Nat:=426+i.val
  by_cases ext:434≤q
  · have hi:q≤528 := by dsimp [q]; have h:=i.isLt;omega
    exact (preserved Leave255StoreMapped.program s m q (untouchedHigh q ⟨ext,hi⟩)).trans (top q ext hi)
  · have lim:i.val<8 := by dsimp [q] at ext;omega
    let j:Fin 8:=⟨i.val,lim⟩
    have geom:∀j:Fin 8,let q:Nat:=426+j.val
        q∉RailPair.sites low ∧ q∉history ∧ q≠1556 ∧ q≠1557 ∧ q≠1558 ∧ q∉smallM ∧ ∃i:Fin 18,q=(row i).free := by decide +kernel
    obtain ⟨l,h,x,y,z,mr,idx,e⟩:=geom j
    rw [store _ l h,flag _ x y z]
    rw [Leave255FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ mr]
    exact e ▸ used.2.2.1 idx
end ECDSAAdd.Entrant.StairPacket.Leave255HighZero

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255PostReady
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def suffix:= (leave255.drop 334).take 2828
theorem split : Leave255StoreMapped.program=(entry++fullPrefix false)++suffix := by decide +kernel
def rawSites := [1706,1707]++(Leave255Close.events.map Prod.fst)

private theorem avoid (prg:Program) (sites:List Wire) (checked:prg.all (fun g=>decide (destination g∉sites))=true) (q:Wire) (mem:q∈sites) :
    q∉prg.map destination := by
  intro bad
  obtain ⟨g,h,rfl⟩:=List.mem_map.mp bad
  exact (of_decide_eq_true (List.all_eq_true.mp checked _ h)) mem

theorem rawLayout:∀q∈rawSites,q∉Leave255StoreMapped.program.map destination := avoid _ _ (by decide +kernel)
theorem keptLayout:∀q∈[1709,1710],q∉suffix.map destination := avoid _ _ (by decide +kernel)

private theorem nearOf (p:Ports) (k:Mode) (sym:Sym) (controls:reads p sym=LeaveSelector.controls p k):
    sym p.near=.bit (nearby k) := by
  simp only [reads,LeaveSelector.controls,List.cons.injEq,and_true,eq_self] at controls
  exact controls.1
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) :
    let out:=run Leave255StoreMapped.program m s
    let f:=decide (Shadow.far 129 15 z)
    out.basis 1706=s.basis 1706 ∧ out.basis 1707=s.basis 1707 ∧
    out.basis 1710=nearby (actualMode 129 z) ∧
    out.basis 1709=(f && HighBankSum.cross (Leave255TrueMiddle.d z)) ∧
    (∀p∈Leave255Close.events,out.basis p.1=s.basis p.1 ∧ out.basis p.2=false) := by
  let a:=run entry m s
  let k:=actualMode 129 z
  let o:=run Leave255StoreMapped.program m s
  have selRaw (q:Wire) (ok:q∉entry.map destination):a.basis q=s.basis q := preserved entry s m q ok
  have sw:∀i:Fin 15,Leave255Hit.swaps i∉entry.map destination:=by decide +kernel
  have prepared:=Leave255FrontPrepare.prepare s m z G sg small ready fresh scratch temp zero k z.u
    (by change k=farMode (a.basis _) (a.basis _) z.u;rw [selRaw _ (by decide),selRaw _ (by decide)];exact mode)
    (fun on i hi h=>(selRaw _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  have hit (q:Wire) (ok:q∈[1709,1710]):o.basis q=(Leave255RetireActual.prior k q).read a.basis := by
    change (run Leave255StoreMapped.program m s).basis q=_
    rw [split,run_append,run_take,preserved _ _ _ q (keptLayout q ok),prepared];rfl
  have h:=Leave255Front.result s m z G sg small ready fresh scratch temp
  have act:=Leave255EntryAction.upperBits _ a.basis h.2.2.2.2.2
  have math:=Leave255Loaded.signed z a.basis small odd room (fun i hi=>act i (Nat.lt_trans hi (by decide : 16<18)))
    ((Leave255EntryAction.parity s m).trans par)
  have near:Leave255RetireActual.prior k 1710=.bit (nearby k) := nearOf ports k _ (controlCert k)
  have plain (q:Wire) (ok:q∈rawSites):o.basis q=s.basis q:=preserved _ _ _ _ (rawLayout q ok)
  have store:=(Leave255StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave255BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have cleared:=Leave255FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  refine ⟨plain _ (by decide),plain _ (by decide),(hit _ (by decide)).trans (congrArg (Expr.read a.basis) near),?_,?_⟩
  · refine (hit _ (by decide)).trans (math.1.trans ?_);by_cases g:Shadow.far 129 15 z <;> simp [g]
  · intro p member
    have geom:∀p∈Leave255Close.events,p.1∈rawSites ∧ p.2∉RailPair.sites low ∧ p.2∉history ∧
      (p.2=1556 ∨ (p.2≠1556 ∧ p.2≠1557 ∧ p.2≠1558 ∧ p.2∈Leave255FlagScratch.targets)) := by decide +kernel
    obtain ⟨src,nl,nh,dst⟩:=geom _ member
    refine ⟨plain _ src,(store _ nl nh).trans ?_⟩
    rcases dst with e|⟨a,b,c,hq⟩
    · rw [e];exact flags.2.1
    · exact (flags.2.2.2.2.2.2 _ a b c).trans (cleared _ hq)
end ECDSAAdd.Entrant.StairPacket.Leave255PostReady

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
attribute [local irreducible] run body
namespace NativePack225
def tailTemps := List.range' 1724 89
theorem tail_routing:∀q∈tailTemps,¬MayTouch idx (windowNet idx q) ∧ q∉support ∧ q∉ports225 ∧
    OB5.sig 224 q=q ∧ q≠1723 ∧ q≠1721 ∧ q≠1722 ∧ q∉RailPair.sites Enter225.upperPairs ∧ q∉([]:List Wire):=by decide +kernel
theorem tail_inputs:∀q∈tailTemps,q=1812 ∨ q∈(W.compactSkywalkTickLayout base 225).carry:=by
  have range:(W.compactSkywalkTickLayout base 225).carry=List.range' 1556 256:=by decide +kernel
  rw [range];intro q seen;have b:=List.mem_range'_1.mp seen;rw [List.mem_range'_1]
  simp only [Wire] at *;omega
theorem tail_clean (d:Bool) (raw s:State) (a b:List Bool) (neg far long G:Bool) (A B:Int)
    (cut:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long (pullState (OB5.sig 224) raw) s)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) A B G raw.basis) (endBit:raw.basis 1812=false) :
    ∀q∈tailTemps,(run (body idx (program d)) b (run Partial.enter225 a s)).basis q=false:=by
  intro q hit
  obtain ⟨live,away,head,same,hn,hf,hu,hi,mask⟩:=tail_routing q hit
  have stay:=ext_head Partial.enter225 idx (program d) support s a b q live
    (fun used=>head (List.mem_toFinset.mp (Enter225.programCover used))) away (packs d)
  have read:=cut.unchanged q hn hf hu hi
  have canon:s.basis q=raw.basis q:=by simpa only [pullState,same] using read
  rcases tail_inputs q hit with rfl|carry
  · exact stay.trans (canon.trans endBit)
  · exact stay.trans (canon.trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ carry))
end NativePack225
namespace NativePack240
def tailTemps := List.range' 1719 94
theorem tail_routing:∀q∈tailTemps,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary240.rawPortsList) ∧ q∉ports240 ∧
    OB5.sig 239 q=q ∧ q≠1715 ∧ q≠1713 ∧ q≠1714 ∧ q∉RailPair.sites Enter240.upperPairs ∧ q∉Enter240.pending:=by decide +kernel
theorem tail_inputs:∀q∈tailTemps,q=1812 ∨ q∈(W.compactSkywalkTickLayout base 240).carry:=by
  have range:(W.compactSkywalkTickLayout base 240).carry=List.range' 1556 256:=by decide +kernel
  rw [range];intro q seen;have b:=List.mem_range'_1.mp seen;rw [List.mem_range'_1]
  simp only [Wire] at *;omega
theorem tail_clean (d:Bool) (raw s:State) (a b:List Bool) (neg far long G:Bool) (A B:Int)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) A B G raw.basis) (endBit:raw.basis 1812=false) :
    ∀q∈tailTemps,(run (body idx (withArchive d)) b (run Partial.enter240 a s)).basis q=false:=by
  intro q hit
  obtain ⟨live,away,head,same,hn,hf,hu,hi,mask⟩:=tail_routing q hit
  have stay:=ext_head Partial.enter240 idx (withArchive d) (support++ArchiveBoundary240.rawPortsList) s a b q live
    (fun used=>head (List.mem_toFinset.mp (Enter240.programCover used))) away (admin_cover d)
  have read:=cut.unchanged q hn hf hu hi
  have canon:s.basis q=raw.basis q:=by simpa only [pullState,same,eraseSites,if_neg mask] using read
  rcases tail_inputs q hit with rfl|carry
  · exact stay.trans (canon.trans endBit)
  · exact stay.trans (canon.trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ carry))
end NativePack240
namespace NativePack255
def tailTemps := List.range' 1712 88
theorem tail_routing:∀q∈tailTemps,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary255.rawPortsList) ∧ q∉ports255 ∧
    OB5.sig 254 q=q ∧ q≠1708 ∧ q≠1706 ∧ q≠1707 ∧ q∉RailPair.sites Enter255.upperPairs ∧ q∉Enter255.pending:=by decide +kernel
theorem tail_inputs:∀q∈tailTemps,q=1812 ∨ q∈(W.compactSkywalkTickLayout base 255).carry:=by
  have range:(W.compactSkywalkTickLayout base 255).carry=List.range' 1556 256:=by decide +kernel
  rw [range];intro q seen;have b:=List.mem_range'_1.mp seen;rw [List.mem_range'_1]
  simp only [Wire] at *;omega
theorem tail_clean (d:Bool) (raw s:State) (a b:List Bool) (neg far long G:Bool) (A B:Int)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) A B G raw.basis) (endBit:raw.basis 1812=false) :
    ∀q∈tailTemps,(run (body idx (withArchive d)) b (run Partial.enter255 a s)).basis q=false:=by
  intro q hit
  obtain ⟨live,away,head,same,hn,hf,hu,hi,mask⟩:=tail_routing q hit
  have stay:=ext_head Partial.enter255 idx (withArchive d) (support++ArchiveBoundary255.rawPortsList) s a b q live
    (fun used=>head (List.mem_toFinset.mp (Enter255.programCover used))) away (admin_cover d)
  have read:=cut.unchanged q hn hf hu hi
  have canon:s.basis q=raw.basis q:=by simpa only [pullState,same,eraseSites,if_neg mask] using read
  rcases tail_inputs q hit with rfl|carry
  · exact stay.trans (canon.trans endBit)
  · exact stay.trans (canon.trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ carry))
end NativePack255
#print axioms NativePack255.tail_clean
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
attribute [local irreducible] run SkywalkNat.step
theorem result (s : State) (m n : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112)
    (phase:∀o,(run leave225 o s).phase=s.phase)
    (initial:∀q,1556≤q→q≤1717→s.basis q=false)
    : run leave225Inv n (run leave225 m s)=s:=by
  have atCore:=Leave225CoreCheckpoint.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have atPost:=Leave225PostReady.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  apply Leave225Mirror.inverts s phase initial  _ _ m n
  · exact Leave225CoreCheckpoint.oracle s _ atCore.1 atCore.2.2.1 clean
  · exact (atPost.2.2.2.2 (1269,1556) (by decide)).2
end ECDSAAdd.Entrant.StairPacket.Leave225Roundtrip

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Whole
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem split : leave225=Leave225StoreMapped.program++afterLow := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 144 15 z → chain (decide (2^144≤z.u)) xs)
    (first:Shadow.far 144 15 z → decide (2^144≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave225Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1721=decide (Shadow.far 144 15 z))
    (side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u))) :
    let u:=decide (2^144≤z.u)
    let active:=decide (Shadow.far 144 15 z)
    let v:=run Leave225StoreMapped.program m s
    let out:=run leave225 m s
    out.phase=s.phase ∧ out.basis 1716=active ∧ out.basis 1717=(active && afterFlags u (xs.take 5)) ∧
      out.basis 1718=(active && HighBankSum.cross (Leave225TrueMiddle.d z)) ∧
      ∀q,out.basis q=writeBit v.basis 1722 false (LeaveRelocation.source moves q) := by
  let v:=run Leave225StoreMapped.program m s
  let u:=decide (2^144≤z.u)
  let active:=decide (Shadow.far 144 15 z)
  let w:Fin 16:=⟨wait 15 z.u,by have h:=wait_le 15 z.u;omega⟩
  have h:=Leave225PostReady.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have pre:=(Leave225StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).1
  have reads:Leave225Close.events.map (fun p=>v.basis p.1)=(xs.take 5).map Prod.snd :=
    (List.map_congr_left (fun p hp=>(h.2.2.2.2 p hp).1)).trans saved
  have done:=Leave225Posted.result v (m.drop (measurementCount Leave225StoreMapped.program)) active u (HighBankSum.cross (Leave225TrueMiddle.d z)) w xs len
    (fun hf=>historyOK (of_decide_eq_true hf)) (fun hf hu=>first (of_decide_eq_true hf) hu)
    reads (h.1.trans far) (h.2.1.trans side) h.2.2.1 h.2.2.2.1 (fun p hp=>(h.2.2.2.2 p hp).2)
  dsimp only
  rw [split,run_append,run_take]
  exact ⟨done.1.trans pre,done.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave225Whole

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
attribute [local irreducible] run SkywalkNat.step
theorem result (s : State) (m n : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120)
    (phase:∀o,(run leave240 o s).phase=s.phase)
    (initial:∀q,1556≤q→q≤1709→s.basis q=false)
    : run leave240Inv n (run leave240 m s)=s:=by
  have atCore:=Leave240CoreCheckpoint.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have atPost:=Leave240PostReady.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  apply Leave240Mirror.inverts s phase initial  _ _ m n
  · exact Leave240CoreCheckpoint.oracle s _ atCore.1 atCore.2.2.1 clean
  · exact (atPost.2.2.2.2 (1284,1556) (by decide)).2
end ECDSAAdd.Entrant.StairPacket.Leave240Roundtrip

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Whole
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem split : leave240=Leave240StoreMapped.program++afterLow := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 136 15 z → chain (decide (2^136≤z.u)) xs)
    (first:Shadow.far 136 15 z → decide (2^136≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave240Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1713=decide (Shadow.far 136 15 z))
    (side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u))) :
    let u:=decide (2^136≤z.u)
    let active:=decide (Shadow.far 136 15 z)
    let v:=run Leave240StoreMapped.program m s
    let out:=run leave240 m s
    out.phase=s.phase ∧ out.basis 1709=active ∧ out.basis 1710=(active && afterFlags u (xs.take 5)) ∧
      out.basis 1711=(active && HighBankSum.cross (Leave240TrueMiddle.d z)) ∧
      ∀q,out.basis q=writeBit v.basis 1714 false (LeaveRelocation.source moves q) := by
  let v:=run Leave240StoreMapped.program m s
  let u:=decide (2^136≤z.u)
  let active:=decide (Shadow.far 136 15 z)
  let w:Fin 16:=⟨wait 15 z.u,by have h:=wait_le 15 z.u;omega⟩
  have h:=Leave240PostReady.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have pre:=(Leave240StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).1
  have reads:Leave240Close.events.map (fun p=>v.basis p.1)=(xs.take 5).map Prod.snd :=
    (List.map_congr_left (fun p hp=>(h.2.2.2.2 p hp).1)).trans saved
  have done:=Leave240Posted.result v (m.drop (measurementCount Leave240StoreMapped.program)) active u (HighBankSum.cross (Leave240TrueMiddle.d z)) w xs len
    (fun hf=>historyOK (of_decide_eq_true hf)) (fun hf hu=>first (of_decide_eq_true hf) hu)
    reads (h.1.trans far) (h.2.1.trans side) h.2.2.1 h.2.2.2.1 (fun p hp=>(h.2.2.2.2 p hp).2)
  dsimp only
  rw [split,run_append,run_take]
  exact ⟨done.1.trans pre,done.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave240Whole

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
attribute [local irreducible] run SkywalkNat.step
theorem result (s : State) (m n : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127)
    (phase:∀o,(run leave255 o s).phase=s.phase)
    (initial:∀q,1556≤q→q≤1702→s.basis q=false)
    (extra:∀q,1713≤q→q≤1718→s.basis q=false)
    : run leave255Inv n (run leave255 m s)=s:=by
  have atCore:=Leave255CoreCheckpoint.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have atPost:=Leave255PostReady.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  apply Leave255Mirror.inverts s phase initial extra  _ _ m n
  · exact Leave255CoreCheckpoint.oracle s _ atCore.1 atCore.2.2.1 clean
  · exact (atPost.2.2.2.2 (1299,1556) (by decide)).2
end ECDSAAdd.Entrant.StairPacket.Leave255Roundtrip

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Whole
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem split : leave255=Leave255StoreMapped.program++afterLow := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 129 15 z → chain (decide (2^129≤z.u)) xs)
    (first:Shadow.far 129 15 z → decide (2^129≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave255Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1706=decide (Shadow.far 129 15 z))
    (side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u))) :
    let u:=decide (2^129≤z.u)
    let active:=decide (Shadow.far 129 15 z)
    let v:=run Leave255StoreMapped.program m s
    let out:=run leave255 m s
    out.phase=s.phase ∧ out.basis 1701=active ∧ out.basis 1702=(active && afterFlags u (xs.take 5)) ∧
      out.basis 1703=(active && HighBankSum.cross (Leave255TrueMiddle.d z)) ∧
      ∀q,out.basis q=writeBit v.basis 1707 false (LeaveRelocation.source moves q) := by
  let v:=run Leave255StoreMapped.program m s
  let u:=decide (2^129≤z.u)
  let active:=decide (Shadow.far 129 15 z)
  let w:Fin 16:=⟨wait 15 z.u,by have h:=wait_le 15 z.u;omega⟩
  have h:=Leave255PostReady.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have pre:=(Leave255StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).1
  have reads:Leave255Close.events.map (fun p=>v.basis p.1)=(xs.take 5).map Prod.snd :=
    (List.map_congr_left (fun p hp=>(h.2.2.2.2 p hp).1)).trans saved
  have done:=Leave255Posted.result v (m.drop (measurementCount Leave255StoreMapped.program)) active u (HighBankSum.cross (Leave255TrueMiddle.d z)) w xs len
    (fun hf=>historyOK (of_decide_eq_true hf)) (fun hf hu=>first (of_decide_eq_true hf) hu)
    reads (h.1.trans far) (h.2.1.trans side) h.2.2.1 h.2.2.2.1 (fun p hp=>(h.2.2.2.2 p hp).2)
  dsimp only
  rw [split,run_append,run_take]
  exact ⟨done.1.trans pre,done.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave255Whole

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem full_carry (i n x p:Nat) (lim:i+n≤512) (good:Bounds x p) (raw:State) (domain:Domain i x p raw)
    (m:List Bool) (q:Nat) (low:1556≤q) (high:q≤1812) :
    (run (span i n) m raw).basis q=false:=by
  obtain ⟨ref,match',stage⟩:=domain
  have finish:=full_span i n x p lim good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime ref m stage
  have fields:=(W.compactSkywalkStage_fields_iff base _ (i+n) lim base_pool_nodup _).mp finish
  have outside:=outside_above (q:=q) (i:=i) (by omega)
  have link:=fixed_span i i n (Nat.le_refl _) lim raw ref m match'
  apply (link.2 q outside).trans
  apply (regValue_zero _ _).mp fields.2.2.2.2.2.1
  exact List.mem_map.mpr ⟨q-16,List.mem_range'_1.mpr (by omega),by change (q-16)+16=q;omega⟩
theorem carry_origin {i upper x p:Nat} (limit:i+15≤512) (upper_ok:upper≤1812) (good:Bounds x p) (raw history:State)
    (domain:Domain i x p raw)
    (fixed:∀q:Nat,1556≤q → q≤upper → OB5.sig (i+14) q=q)
    (q:Nat) (low:1556≤q) (high:q≤upper) : (origin i raw history).basis q=false:=by
  have clear:q∉sites i:=by
    intro hit
    obtain ⟨r,hr,eq⟩:=List.mem_flatMap.mp hit
    have bound:=List.mem_range'_1.mp hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,base,Wire] at eq
    unfold oldStart oldCount at bound
    split at bound <;> rcases eq with h|h <;> omega
  rw [outside i raw history q clear,fixed _ low high]
  exact full_carry i 15 x p limit good raw domain [] q low (Nat.le_trans high upper_ok)
theorem same_c225 (q:Nat) (lo:1556≤q) (hi:q≤1812):OB5.sig (225+14) q=q:=by
  unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
theorem same_c240 (q:Nat) (lo:1556≤q) (hi:q≤1812):OB5.sig (240+14) q=q:=by
  unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
theorem same_c255 (q:Nat) (lo:1556≤q) (hi:q≤1799):OB5.sig (255+14) q=q:=by
  unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
#print axioms carry_origin
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
theorem incoming_free_A (i x p:Nat) (lim:i≤512) (raw:State) (domain:Domain i x p raw)
    (q:Nat) (lower:i+16<q) (upper:q<1044)
    (free:q∈(W.compactSkywalkSignPoolA base i).released ∨ (i+274≤q ∧ q<786)) :
    raw.basis q=false:=by
  obtain ⟨ref,match',stage⟩:=domain
  apply (match'.2 _ (outside_between lower upper)).trans
  rcases free with sign|later
  · exact stage.2.1 q sign
  · let j:=q-274
    have hj:i≤j ∧ j<512:=by dsimp [j];omega
    have eq:q=base (j+258):=by change q=j+258+16;dsimp [j];omega
    rw [eq]
    exact ((W.compactSkywalkStage_fields_iff base _ i lim base_pool_nodup _).mp stage).2.2.2.2.1 j hj.1 hj.2 |>.1
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave225Word

def zeros := (List.range' 1556 157)++(List.range' 1719 94)
def retired (q:Wire):Prop:=
  q=1722 ∨ (q≠1722 ∧ q∉RailPair.sites low ∧ q∉history ∧
  (q=1556 ∨ (q≠1556 ∧ q≠1557 ∧ q≠1558 ∧
   ((q∈Leave225CoreCheckpoint.targets ∧ q∉smallM)))))
instance (q:Wire):Decidable (retired q):=by unfold retired;infer_instance
theorem routed:∀q∈zeros,retired (LeaveRelocation.source moves q) := by decide +kernel
theorem restoreShape : Leave225FullArithmetic.program=Leave225CoreCheckpoint.program++restore := by decide +kernel
private theorem intervalIndex (n : Nat) (lo : 1559 ≤ n) (hi : n < 1559+39) : ∃ j : Fin 39, 1559+j.val=n := by
  exact ⟨⟨n-1559, by omega⟩, by change 1559+(n-1559)=n; omega⟩
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 144 15 z → chain (decide (2^144≤z.u)) xs)
    (first:Shadow.far 144 15 z → decide (2^144≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave225Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1721=decide (Shadow.far 144 15 z))
    (side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u))) (quiet:∀q∈Leave225CoreCheckpoint.rawSites,s.basis q=false) :
    ∀q∈zeros,(run leave225 m s).basis q=false := by
  let c:=run Leave225CoreCheckpoint.program m s
  have h:=Leave225CoreCheckpoint.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have zerosAt (q:Wire) (mem:q∈Leave225CoreCheckpoint.targets):c.basis q=false := by
    simp only [Leave225CoreCheckpoint.targets,List.mem_append,List.mem_map] at mem
    rcases mem with ((scr|free)|raw)|mag
    · obtain ⟨lo,hi⟩:=List.mem_range'_1.mp scr
      obtain ⟨j,id⟩:=intervalIndex q lo hi
      rw [←id];exact h.1 j
    · obtain ⟨j,_,rfl⟩:=free;exact h.2.1 j
    · exact (h.2.2.1 q raw).trans (quiet q raw)
    · exact h.2.2.2 q mag
  have cleanCs:∀q∈smallC,c.basis q=false := fun q hq=>zerosAt _ ((by decide +kernel : ∀q∈smallC,q∈Leave225CoreCheckpoint.targets) q hq)
  have clearM:regValue smallM c.basis=0:=(regValue_zero _ _).mpr (fun q hq=>h.2.2.2 q ((by decide +kernel : ∀q∈smallM,q∈Leave225CoreCheckpoint.magSites) q hq))
  have rest:=restore_run c (m.drop (measurementCount Leave225CoreCheckpoint.program)) cleanCs clearM
  have coreDone (q:Wire) (mem:q∈Leave225CoreCheckpoint.targets) (notM:q∉smallM):(run Leave225FullArithmetic.program m s).basis q=false:=by
    rw [restoreShape,run_append,run_take,rest.2.1 _ notM];exact zerosAt q mem
  have whole:=Leave225Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=(Leave225StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave225BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  intro q hq
  rw [whole.2.2.2.2]
  rcases routed q hq with eq|⟨diff,out,hist,src⟩
  · rw [eq];simp [writeBit]
  simp only [writeBit,Function.update_of_ne diff]
  rw [store _ out hist]
  rcases src with eq|⟨x,y,z,origin⟩
  · rw [eq];exact flags.2.1
  · exact (flags.2.2.2.2.2.2 _ x y z).trans (coreDone _ origin.1 origin.2)
end ECDSAAdd.Entrant.StairPacket.Leave225BoundaryClean

end

end

-- repack: PrizeTail752d1574c lines 3..3116
section
section

namespace ECDSAAdd.Entrant.StairPacket.Leave225EndWords
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 144 15 z → chain (decide (2^144≤z.u)) xs)
    (first:Shadow.far 144 15 z → decide (2^144≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave225Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1721=decide (Shadow.far 144 15 z))
    (side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u))) :
    let a:=SkywalkNat.step^[15] z
    let sign:=negative sg a.u
    let mag:=a.u-sign.toNat
    let next:=decide (Shadow.far 136 15 a)
    let out:=run leave225 m s
    out.basis 1713=next ∧ out.basis 1714=(next && decide (2^136≤a.u)) ∧ out.basis 1715=sign ∧
      (∀q∈history,out.basis q=s.basis q) ∧
      (∀i:Fin 11,let pos:=(a.u+a.v).testBit (144+i.val);let neg:=mag.testBit (144+i.val) ^^ sign
                   out.basis (400+i.val)=(if G then neg else pos) ∧ out.basis (930+i.val)=(if G then pos else neg)) ∧
      ∀i:Fin 102,out.basis (941+i.val)=(a.u+a.v).testBit (155+i.val) := by
  let out:=run leave225 m s
  let v:=run Leave225StoreMapped.program m s
  let b:=run Leave225BeforeStore.program m s
  have whole:=Leave225Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=Leave225StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have before:=Leave225BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have coords:=Leave225StoreCoordinates.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have atSite (q src:Wire) (link:LeaveRelocation.source moves q=src) (clear:src≠1722):out.basis q=v.basis src := by
    rw [whole.2.2.2.2,link];simp [writeBit,clear,v]
  have flagAt (q src:Wire) (link:LeaveRelocation.source moves q=src)
      (outside:src≠1722 ∧ src∉RailPair.sites low ∧ src∉history):out.basis q=b.basis src :=
    (atSite q src link outside.1).trans (store.2.2.2 _ outside.2.1 outside.2.2)
  refine ⟨(flagAt 1713 1557 (by decide +kernel) (by decide)).trans before.2.2.1,
    (flagAt 1714 1558 (by decide +kernel) (by decide)).trans before.2.2.2.1,
    (flagAt 1715 1723 (by decide +kernel) (by decide)).trans coords.1,?_,?_,?_⟩
  · intro q hq
    have intact:∀q∈history,LeaveRelocation.source moves q=q ∧ q≠1722:=by decide +kernel
    exact (atSite q q (intact q hq).1 (intact q hq).2).trans (store.2.1 q hq)
  · intro i
    have intact:∀j:Fin 11,LeaveRelocation.source moves (400+j.val)=400+j.val ∧
      LeaveRelocation.source moves (930+j.val)=930+j.val ∧ 400+j.val≠1722 ∧ 930+j.val≠1722 := by decide +kernel
    obtain ⟨hx,hy,dx,dy⟩:=intact i
    exact ⟨(atSite _ _ hx dx).trans (store.2.2.1 i).1,(atSite _ _ hy dy).trans (store.2.2.1 i).2⟩
  · intro i
    have geo:∀j:Fin 102,live (10+j.val)≠1722 ∧ live (10+j.val)∉RailPair.sites low ∧ live (10+j.val)∉history := by decide +kernel
    have a:=flagAt _ _ (upperMap i).1 (geo i)
    have n:10+i.val<112 := by have h:=i.isLt;omega
    have hi:=(before.2.2.2.2.2.1 _ n)
    unfold Leave225TrueMiddle.F at hi
    rw [Nat.testBit_div_two_pow] at hi
    exact a.trans (by simpa only [show (10+i.val)+145=155+i.val by omega] using hi)
end ECDSAAdd.Entrant.StairPacket.Leave225EndWords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave240Word

def zeros := (List.range' 1556 150)++(List.range' 1712 101)
def retired (q:Wire):Prop:=
  q=1714 ∨ (q≠1714 ∧ q∉RailPair.sites low ∧ q∉history ∧
  (q=1556 ∨ (q≠1556 ∧ q≠1557 ∧ q≠1558 ∧
   ((q∈Leave240CoreCheckpoint.targets ∧ q∉smallM)))))
instance (q:Wire):Decidable (retired q):=by unfold retired;infer_instance
theorem routed:∀q∈zeros,retired (LeaveRelocation.source moves q) := by decide +kernel
theorem restoreShape : Leave240FullArithmetic.program=Leave240CoreCheckpoint.program++restore := by decide +kernel
private theorem intervalIndex (n : Nat) (lo : 1559 ≤ n) (hi : n < 1559+39) : ∃ j : Fin 39, 1559+j.val=n := by
  exact ⟨⟨n-1559, by omega⟩, by change 1559+(n-1559)=n; omega⟩
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 136 15 z → chain (decide (2^136≤z.u)) xs)
    (first:Shadow.far 136 15 z → decide (2^136≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave240Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1713=decide (Shadow.far 136 15 z))
    (side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u))) (quiet:∀q∈Leave240CoreCheckpoint.rawSites,s.basis q=false) :
    ∀q∈zeros,(run leave240 m s).basis q=false := by
  let c:=run Leave240CoreCheckpoint.program m s
  have h:=Leave240CoreCheckpoint.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have zerosAt (q:Wire) (mem:q∈Leave240CoreCheckpoint.targets):c.basis q=false := by
    simp only [Leave240CoreCheckpoint.targets,List.mem_append,List.mem_map] at mem
    rcases mem with ((scr|free)|raw)|mag
    · obtain ⟨lo,hi⟩:=List.mem_range'_1.mp scr
      obtain ⟨j,id⟩:=intervalIndex q lo hi
      rw [←id];exact h.1 j
    · obtain ⟨j,_,rfl⟩:=free;exact h.2.1 j
    · exact (h.2.2.1 q raw).trans (quiet q raw)
    · exact h.2.2.2 q mag
  have cleanCs:∀q∈smallC,c.basis q=false := fun q hq=>zerosAt _ ((by decide +kernel : ∀q∈smallC,q∈Leave240CoreCheckpoint.targets) q hq)
  have clearM:regValue smallM c.basis=0:=(regValue_zero _ _).mpr (fun q hq=>h.2.2.2 q ((by decide +kernel : ∀q∈smallM,q∈Leave240CoreCheckpoint.magSites) q hq))
  have rest:=restore_run c (m.drop (measurementCount Leave240CoreCheckpoint.program)) cleanCs clearM
  have coreDone (q:Wire) (mem:q∈Leave240CoreCheckpoint.targets) (notM:q∉smallM):(run Leave240FullArithmetic.program m s).basis q=false:=by
    rw [restoreShape,run_append,run_take,rest.2.1 _ notM];exact zerosAt q mem
  have whole:=Leave240Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=(Leave240StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave240BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  intro q hq
  rw [whole.2.2.2.2]
  rcases routed q hq with eq|⟨diff,out,hist,src⟩
  · rw [eq];simp [writeBit]
  simp only [writeBit,Function.update_of_ne diff]
  rw [store _ out hist]
  rcases src with eq|⟨x,y,z,origin⟩
  · rw [eq];exact flags.2.1
  · exact (flags.2.2.2.2.2.2 _ x y z).trans (coreDone _ origin.1 origin.2)
end ECDSAAdd.Entrant.StairPacket.Leave240BoundaryClean

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240EndWords
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 136 15 z → chain (decide (2^136≤z.u)) xs)
    (first:Shadow.far 136 15 z → decide (2^136≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave240Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1713=decide (Shadow.far 136 15 z))
    (side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u))) :
    let a:=SkywalkNat.step^[15] z
    let sign:=negative sg a.u
    let mag:=a.u-sign.toNat
    let next:=decide (Shadow.far 129 15 a)
    let out:=run leave240 m s
    out.basis 1706=next ∧ out.basis 1707=(next && decide (2^129≤a.u)) ∧ out.basis 1708=sign ∧
      (∀q∈history,out.basis q=s.basis q) ∧
      (∀i:Fin 12,let pos:=(a.u+a.v).testBit (136+i.val);let neg:=mag.testBit (136+i.val) ^^ sign
                   out.basis (407+i.val)=(if G then neg else pos) ∧ out.basis (922+i.val)=(if G then pos else neg)) ∧
      ∀i:Fin 109,out.basis (934+i.val)=(a.u+a.v).testBit (148+i.val) := by
  let out:=run leave240 m s
  let v:=run Leave240StoreMapped.program m s
  let b:=run Leave240BeforeStore.program m s
  have whole:=Leave240Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=Leave240StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have before:=Leave240BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have coords:=Leave240StoreCoordinates.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have atSite (q src:Wire) (link:LeaveRelocation.source moves q=src) (clear:src≠1714):out.basis q=v.basis src := by
    rw [whole.2.2.2.2,link];simp [writeBit,clear,v]
  have flagAt (q src:Wire) (link:LeaveRelocation.source moves q=src)
      (outside:src≠1714 ∧ src∉RailPair.sites low ∧ src∉history):out.basis q=b.basis src :=
    (atSite q src link outside.1).trans (store.2.2.2 _ outside.2.1 outside.2.2)
  refine ⟨(flagAt 1706 1557 (by decide +kernel) (by decide)).trans before.2.2.1,
    (flagAt 1707 1558 (by decide +kernel) (by decide)).trans before.2.2.2.1,
    (flagAt 1708 1715 (by decide +kernel) (by decide)).trans coords.1,?_,?_,?_⟩
  · intro q hq
    have intact:∀q∈history,LeaveRelocation.source moves q=q ∧ q≠1714:=by decide +kernel
    exact (atSite q q (intact q hq).1 (intact q hq).2).trans (store.2.1 q hq)
  · intro i
    have intact:∀j:Fin 12,LeaveRelocation.source moves (407+j.val)=407+j.val ∧
      LeaveRelocation.source moves (922+j.val)=922+j.val ∧ 407+j.val≠1714 ∧ 922+j.val≠1714 := by decide +kernel
    obtain ⟨hx,hy,dx,dy⟩:=intact i
    exact ⟨(atSite _ _ hx dx).trans (store.2.2.1 i).1,(atSite _ _ hy dy).trans (store.2.2.1 i).2⟩
  · intro i
    have geo:∀j:Fin 109,live (11+j.val)≠1714 ∧ live (11+j.val)∉RailPair.sites low ∧ live (11+j.val)∉history := by decide +kernel
    have a:=flagAt _ _ (upperMap i).1 (geo i)
    have n:11+i.val<120 := by have h:=i.isLt;omega
    have hi:=(before.2.2.2.2.2.1 _ n)
    unfold Leave240TrueMiddle.F at hi
    rw [Nat.testBit_div_two_pow] at hi
    exact a.trans (by simpa only [show (11+i.val)+137=148+i.val by omega] using hi)
end ECDSAAdd.Entrant.StairPacket.Leave240EndWords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave255Word

def zeros := (List.range' 1556 142)++(List.range' 1704 96)++List.range' 1029 14
def retired (q:Wire):Prop:=
  q=1707 ∨ (q≠1707 ∧ q∉RailPair.sites low ∧ q∉history ∧
  (q=1556 ∨ (q≠1556 ∧ q≠1557 ∧ q≠1558 ∧
   ((q∈Leave255CoreCheckpoint.targets ∧ q∉smallM) ∨ (∃i:Fin 14,q=live (113+i.val))))))
instance (q:Wire):Decidable (retired q):=by unfold retired;infer_instance
theorem routed:∀q∈zeros,retired (LeaveRelocation.source moves q) := by decide +kernel
theorem restoreShape : Leave255FullArithmetic.program=Leave255CoreCheckpoint.program++restore := by decide +kernel
private theorem intervalIndex (n : Nat) (lo : 1559 ≤ n) (hi : n < 1559+39) : ∃ j : Fin 39, 1559+j.val=n := by
  exact ⟨⟨n-1559, by omega⟩, by change 1559+(n-1559)=n; omega⟩
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 129 15 z → chain (decide (2^129≤z.u)) xs)
    (first:Shadow.far 129 15 z → decide (2^129≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave255Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1706=decide (Shadow.far 129 15 z))
    (side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u))) (quiet:∀q∈Leave255CoreCheckpoint.rawSites,s.basis q=false) (narrow:Leave255TrueMiddle.F z<2^113) :
    ∀q∈zeros,(run leave255 m s).basis q=false := by
  let c:=run Leave255CoreCheckpoint.program m s
  have h:=Leave255CoreCheckpoint.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have zerosAt (q:Wire) (mem:q∈Leave255CoreCheckpoint.targets):c.basis q=false := by
    simp only [Leave255CoreCheckpoint.targets,List.mem_append,List.mem_map] at mem
    rcases mem with ((scr|free)|raw)|mag
    · obtain ⟨lo,hi⟩:=List.mem_range'_1.mp scr
      obtain ⟨j,id⟩:=intervalIndex q lo hi
      rw [←id];exact h.1 j
    · obtain ⟨j,_,rfl⟩:=free;exact h.2.1 j
    · exact (h.2.2.1 q raw).trans (quiet q raw)
    · exact h.2.2.2 q mag
  have cleanCs:∀q∈smallC,c.basis q=false := fun q hq=>zerosAt _ ((by decide +kernel : ∀q∈smallC,q∈Leave255CoreCheckpoint.targets) q hq)
  have clearM:regValue smallM c.basis=0:=(regValue_zero _ _).mpr (fun q hq=>h.2.2.2 q ((by decide +kernel : ∀q∈smallM,q∈Leave255CoreCheckpoint.magSites) q hq))
  have rest:=restore_run c (m.drop (measurementCount Leave255CoreCheckpoint.program)) cleanCs clearM
  have coreDone (q:Wire) (mem:q∈Leave255CoreCheckpoint.targets) (notM:q∉smallM):(run Leave255FullArithmetic.program m s).basis q=false:=by
    rw [restoreShape,run_append,run_take,rest.2.1 _ notM];exact zerosAt q mem
  have whole:=Leave255Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=(Leave255StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave255BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  intro q hq
  rw [whole.2.2.2.2]
  rcases routed q hq with eq|⟨diff,out,hist,src⟩
  · rw [eq];simp [writeBit]
  simp only [writeBit,Function.update_of_ne diff]
  rw [store _ out hist]
  rcases src with eq|⟨x,y,z,origin⟩
  · rw [eq];exact flags.2.1
  · rcases origin with ⟨mem,notM⟩|⟨i,eq⟩
    · exact (flags.2.2.2.2.2.2 _ x y z).trans (coreDone _ mem notM)
    · rw [eq,flags.2.2.2.2.2.1 _ (by have h:=i.isLt;omega)]
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le narrow (Nat.pow_le_pow_right (by decide) (by omega))
end ECDSAAdd.Entrant.StairPacket.Leave255BoundaryClean

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255EndWords
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 129 15 z → chain (decide (2^129≤z.u)) xs)
    (first:Shadow.far 129 15 z → decide (2^129≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave255Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1706=decide (Shadow.far 129 15 z))
    (side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u))) :
    let a:=SkywalkNat.step^[15] z
    let sign:=negative sg a.u
    let mag:=a.u-sign.toNat
    let next:=decide (Shadow.far 121 15 a)
    let out:=run leave255 m s
    out.basis 1698=next ∧ out.basis 1699=(next && decide (2^121≤a.u)) ∧ out.basis 1700=sign ∧
      (∀q∈history,out.basis q=s.basis q) ∧
      (∀i:Fin 11,let pos:=(a.u+a.v).testBit (129+i.val);let neg:=mag.testBit (129+i.val) ^^ sign
                   out.basis (415+i.val)=(if G then neg else pos) ∧ out.basis (915+i.val)=(if G then pos else neg)) ∧
      ∀i:Fin 103,out.basis (926+i.val)=(a.u+a.v).testBit (140+i.val) := by
  let out:=run leave255 m s
  let v:=run Leave255StoreMapped.program m s
  let b:=run Leave255BeforeStore.program m s
  have whole:=Leave255Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=Leave255StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have before:=Leave255BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have coords:=Leave255StoreCoordinates.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have atSite (q src:Wire) (link:LeaveRelocation.source moves q=src) (clear:src≠1707):out.basis q=v.basis src := by
    rw [whole.2.2.2.2,link];simp [writeBit,clear,v]
  have flagAt (q src:Wire) (link:LeaveRelocation.source moves q=src)
      (outside:src≠1707 ∧ src∉RailPair.sites low ∧ src∉history):out.basis q=b.basis src :=
    (atSite q src link outside.1).trans (store.2.2.2 _ outside.2.1 outside.2.2)
  refine ⟨(flagAt 1698 1557 (by decide +kernel) (by decide)).trans before.2.2.1,
    (flagAt 1699 1558 (by decide +kernel) (by decide)).trans before.2.2.2.1,
    (flagAt 1700 1708 (by decide +kernel) (by decide)).trans coords.1,?_,?_,?_⟩
  · intro q hq
    have intact:∀q∈history,LeaveRelocation.source moves q=q ∧ q≠1707:=by decide +kernel
    exact (atSite q q (intact q hq).1 (intact q hq).2).trans (store.2.1 q hq)
  · intro i
    have intact:∀j:Fin 11,LeaveRelocation.source moves (415+j.val)=415+j.val ∧
      LeaveRelocation.source moves (915+j.val)=915+j.val ∧ 415+j.val≠1707 ∧ 915+j.val≠1707 := by decide +kernel
    obtain ⟨hx,hy,dx,dy⟩:=intact i
    exact ⟨(atSite _ _ hx dx).trans (store.2.2.1 i).1,(atSite _ _ hy dy).trans (store.2.2.1 i).2⟩
  · intro i
    have geo:∀j:Fin 103,live (10+j.val)≠1707 ∧ live (10+j.val)∉RailPair.sites low ∧ live (10+j.val)∉history := by decide +kernel
    have a:=flagAt _ _ (upperMap i).1 (geo i)
    have n:10+i.val<127 := by have h:=i.isLt;omega
    have hi:=(before.2.2.2.2.2.1 _ n)
    unfold Leave255TrueMiddle.F at hi
    rw [Nat.testBit_div_two_pow] at hi
    exact a.trans (by simpa only [show (10+i.val)+130=140+i.val by omega] using hi)
end ECDSAAdd.Entrant.StairPacket.Leave255EndWords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ReleasedOrigin
open Arithmetic MappedCompressed WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000

def releasedSite (q:Nat) := q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1313)
instance (q:Nat):Decidable (releasedSite q) := by unfold releasedSite;infer_instance

theorem released (x p:Nat) (good:Bounds x p) (raw history:State) (dom:Domain 255 x p raw) (q:Nat)
    (site:q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1313)) :
    (origin 255 raw history).basis q=false := by
  have off:∀i:Fin 1314,releasedSite i.val →
      i.val∉sites 255 := by decide +kernel
  have bound:q<1314:=by omega
  rw [outside _ _ _ _ (off ⟨q,bound⟩ site)]
  by_cases mirror:1301≤q ∧ q≤1313
  · have map:OB5.sig 269 q=3113-q:=by simp [OB5.sig,mirror.1,show q≤1044+269 by omega]
    rw [show 255+14=269 by decide,map]
    exact full_carry 255 15 x p (by decide) good raw dom [] _ (by omega) (by omega)
  have small:q=529 ∨ (1029≤q ∧ q≤1042):=by tauto
  have ident:OB5.sig (255+14) q=q:=by unfold OB5.sig;rw [if_neg];simp only [Wire] at *;omega
  rw [ident]
  obtain ⟨reference,same,stage⟩:=dom
  have finish:=full_span 255 15 x p (by decide) good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime reference [] stage
  have offHist:¬Earlier 255 q:=outside_between (by omega) (by omega)
  have link:=fixed_span 255 255 15 (Nat.le_refl _) (by decide) raw reference [] same
  apply (link.2 q offHist).trans
  rcases small with rfl|⟨lo,hi⟩
  · exact finish.2.1 _ (by decide +kernel)
  · have members : ∀i∈List.range' 1029 14,i∈(W.compactSkywalkSignPoolB base 270).released := by decide +kernel
    exact finish.2.2 q (members _ (List.mem_range'_1.mpr ⟨lo,by omega⟩))

end ECDSAAdd.Entrant.StairPacket.Leave255ReleasedOrigin

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run body
namespace NativePack225
def upperA:=List.range' 419 94
theorem upper_layout:∀q∈upperA,¬MayTouch idx (windowNet idx q) ∧ q∉support ∧ q∉ports225 ∧ q∉([]:List Wire) ∧
    OB5.sig 224 q=q ∧ q≠1723 ∧ q≠1721 ∧ q≠1722 ∧ 225+16<q ∧ q<1044:=by decide +kernel
theorem upper_sources:∀q∈upperA,q∈Enter225.upperPairs.map Prod.fst ∨
    (q∉RailPair.sites Enter225.upperPairs ∧ (q∈(W.compactSkywalkSignPoolA base 225).released ∨ (225+274≤q ∧ q<786))):=by decide +kernel
theorem upper_clear (d:Bool) (raw s:State) (x p:Nat) (domain:Domain 225 x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long (pullState (OB5.sig 224) raw) s)
    (q:Nat) (low:419≤q) (high:q≤512) :
    (run (body idx (program d)) b (run Partial.enter225 a s)).basis q=false:=by
  have seen:q∈upperA:=List.mem_range'_1.mpr ⟨low,Nat.lt_succ_of_le high⟩
  obtain ⟨off,adminOff,enterOff,mask,source,hn,hf,hu,lower,upper⟩:=upper_layout q seen
  have normal:=ext_head Partial.enter225 idx (program d) support s a b q off
    (fun h=>enterOff (List.mem_toFinset.mp (Enter225.programCover h))) adminOff (packs d)
  apply normal.trans
  have clean:(s).basis q=false:=by
    rcases upper_sources q seen with old|⟨away,fresh⟩
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp old
      exact (cut.upper _ hp).1
    · have cleared:=incoming_free_A 225 x p (by decide) raw domain q lower upper fresh
      exact (cut.unchanged q hn hf hu away).trans (by simpa only [pullState,source] using cleared)
  exact clean
end NativePack225
namespace NativePack240
def upperA:=List.range' 426 102
theorem upper_layout:∀q∈upperA,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary240.rawPortsList) ∧ q∉ports240 ∧ q∉Enter240.pending ∧
    OB5.sig 239 q=q ∧ q≠1715 ∧ q≠1713 ∧ q≠1714 ∧ 240+16<q ∧ q<1044:=by decide +kernel
theorem upper_sources:∀q∈upperA,q∈Enter240.upperPairs.map Prod.fst ∨
    (q∉RailPair.sites Enter240.upperPairs ∧ (q∈(W.compactSkywalkSignPoolA base 240).released ∨ (240+274≤q ∧ q<786))):=by decide +kernel
theorem upper_clear (d:Bool) (raw s:State) (x p:Nat) (domain:Domain 240 x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (q:Nat) (low:426≤q) (high:q≤527) :
    (run (body idx (withArchive d)) b (run Partial.enter240 a s)).basis q=false:=by
  have seen:q∈upperA:=List.mem_range'_1.mpr ⟨low,Nat.lt_succ_of_le high⟩
  obtain ⟨off,adminOff,enterOff,mask,source,hn,hf,hu,lower,upper⟩:=upper_layout q seen
  have normal:=ext_head Partial.enter240 idx (withArchive d) (support++ArchiveBoundary240.rawPortsList) s a b q off
    (fun h=>enterOff (List.mem_toFinset.mp (Enter240.programCover h))) adminOff (admin_cover d)
  apply normal.trans
  have clean:((eraseSites Enter240.pending s)).basis q=false:=by
    rcases upper_sources q seen with old|⟨away,fresh⟩
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp old
      exact (cut.upper _ hp).1
    · have cleared:=incoming_free_A 240 x p (by decide) raw domain q lower upper fresh
      exact (cut.unchanged q hn hf hu away).trans (by simpa only [pullState,source] using cleared)
  simpa [eraseSites,mask] using clean
end NativePack240
namespace NativePack255
def upperA:=List.range' 434 96
theorem upper_layout:∀q∈upperA,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary255.rawPortsList) ∧ q∉ports255 ∧ q∉Enter255.pending ∧
    OB5.sig 254 q=q ∧ q≠1708 ∧ q≠1706 ∧ q≠1707 ∧ 255+16<q ∧ q<1044:=by decide +kernel
theorem upper_sources:∀q∈upperA,q∈Enter255.upperPairs.map Prod.fst ∨
    (q∉RailPair.sites Enter255.upperPairs ∧ (q∈(W.compactSkywalkSignPoolA base 255).released ∨ (255+274≤q ∧ q<786))):=by decide +kernel
theorem upper_clear (d:Bool) (raw s:State) (x p:Nat) (domain:Domain 255 x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (q:Nat) (low:434≤q) (high:q≤529) :
    (run (body idx (withArchive d)) b (run Partial.enter255 a s)).basis q=false:=by
  have seen:q∈upperA:=List.mem_range'_1.mpr ⟨low,Nat.lt_succ_of_le high⟩
  obtain ⟨off,adminOff,enterOff,mask,source,hn,hf,hu,lower,upper⟩:=upper_layout q seen
  have normal:=ext_head Partial.enter255 idx (withArchive d) (support++ArchiveBoundary255.rawPortsList) s a b q off
    (fun h=>enterOff (List.mem_toFinset.mp (Enter255.programCover h))) adminOff (admin_cover d)
  apply normal.trans
  have clean:((eraseSites Enter255.pending s)).basis q=false:=by
    rcases upper_sources q seen with old|⟨away,fresh⟩
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp old
      exact (cut.upper _ hp).1
    · have cleared:=incoming_free_A 255 x p (by decide) raw domain q lower upper fresh
      exact (cut.unchanged q hn hf hu away).trans (by simpa only [pullState,source] using cleared)
  simpa [eraseSites,mask] using clean
end NativePack255
#print axioms NativePack225.upper_clear
#print axioms NativePack240.upper_clear
#print axioms NativePack255.upper_clear
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

theorem lowFrame (i:Fin 144) (s:State) (m:List Bool) :
    let v:=run leave225 m s
    v.basis (256+i.val)=s.basis (256+i.val) ∧ v.basis (786+i.val)=s.basis (786+i.val) := by
  have cover:leave225.all (fun g=>decide ((destination g<256 ∨ 400≤destination g) ∧ (destination g<786 ∨ 930≤destination g)))=true := by decide +kernel
  have safe (q:Nat) (inside:(256≤q ∧ q<400) ∨ (786≤q ∧ q<930)):q∉leave225.map destination := by
    intro h;obtain ⟨g,hg,rfl⟩:=List.mem_map.mp h
    obtain ⟨a,d⟩:=of_decide_eq_true (List.all_eq_true.mp cover g hg)
    rcases inside with ⟨l,r⟩|⟨l,r⟩
    · exact a.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
    · exact d.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
  have hi:=i.isLt
  exact ⟨preserved _ s m _ (safe _ (Or.inl ⟨by omega,by omega⟩)),
    preserved _ s m _ (safe _ (Or.inr ⟨by omega,by omega⟩))⟩

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 144 15 z → chain (decide (2^144≤z.u)) xs)
    (first:Shadow.far 144 15 z → decide (2^144≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave225Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1721=decide (Shadow.far 144 15 z))
    (side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u)))
    (highZero:∀q:Nat,419≤q → q≤512 → s.basis q=false)
    (raw:State) (input:let a:=SkywalkNat.step^[15] z
       SkywalkIntegerInput Leave225WideWords.L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis) :
    let o:=pullState (OB5.sig 239) raw
    let out:=run leave225 m s
    (∀i:Fin 155,out.basis (256+i.val)=o.basis (256+i.val) ∧ out.basis (786+i.val)=o.basis (786+i.val)) ∧
    ∀i:Fin 102,out.basis (411+i.val)=false ∧
      out.basis (941+i.val)=(if o.basis 255 then o.basis (941+i.val) else o.basis (411+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  let o:=pullState (OB5.sig 239) raw
  let out:=run leave225 m s
  have word:=Leave225EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole:=Leave225Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared:=Leave225HighZero.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero nextSmall bound
  have orient:o.basis 255=G := by
    have geo:Leave225WideWords.L.previous=OB5.sig 239 255:=by decide +kernel
    change raw.basis (OB5.sig 239 255)=G
    rw [←geo];exact input.2.2.1
  have law:=LeaveShadowRails.retainedLow 144 z small sg
  constructor
  · intro i
    have fit:i.val<257:=by have h:=i.isLt;omega
    have ref:=Leave225WideWords.wide a G sg raw input ⟨i.val,fit⟩
    by_cases low:i.val<144
    · have hw:=Leave225WideWords.short h G sg s ready ⟨i.val,low⟩
      have untouched:=lowFrame ⟨i.val,low⟩ s m
      have spos:=LeaveSignedCoordinates.sharedDigit _ _ 144 i.val law.2.1 (Nat.le_of_lt low)
      have smag:=LeaveSignedCoordinates.sharedDigit _ _ 144 i.val law.2.2 (Nat.le_of_lt low)
      dsimp only at ref hw
      rw [law.1,spos,smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm),untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · let j:Fin 11:=⟨i.val-144,by have h:=i.isLt;omega⟩
      have eq:144+j.val=i.val:=by dsimp [j];omega
      have vals:=word.2.2.2.2.1 j
      dsimp only at ref vals
      rw [eq,show (400:Nat)+j.val=256+i.val by omega,show (930:Nat)+j.val=786+i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm,vals.2.trans ref.2.symm⟩
  · intro i
    let j:Fin 257:=⟨155+i.val,by have h:=i.isLt;omega⟩
    have ref:=Leave225WideWords.wide a G sg raw input j
    dsimp only [j] at ref
    rw [show 256+(155+i.val)=411+i.val by omega,show 786+(155+i.val)=941+i.val by omega] at ref
    have free:(run leave225 m s).basis (411+i.val)=false := by
      rw [whole.2.2.2.2,(upperMap i).2]
      exact (Function.update_of_ne (by have h:=i.isLt;change (411:Nat)+i.val≠1722;omega) _ _).trans (cleared i)
    refine ⟨free,?_⟩
    change out.basis (941+i.val)=(if o.basis 255 then o.basis (941+i.val) else o.basis (411+i.val))
    rw [orient,word.2.2.2.2.2 i];cases G <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using (by first | exact ref.1.symm | exact ref.2.symm)
end ECDSAAdd.Entrant.StairPacket.Leave225BoundaryRails

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225PreservedRecords
open LeaveSelector LeaveReadoutFrame Arithmetic IntegerPacket Partial LeaveCompanion LeaveCompanion225 Leave225Front Leave225Selector
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000

theorem swapPolarity : ∀i:Fin 15, LeaveSelector.parityAt (Leave225Hit.swaps i.val) leave225=some false := by decide +kernel

theorem result (s : State) (m : List Bool)
    (previous : ∀q∈Leave225Close.history,(run leave225 m s).basis q=s.basis q) :
    readCells (shape 10) 0 15 (mappedBasis 10 (run leave225 m s).basis) =
      readCells (shape 10) 0 15 (mappedBasis 10 s.basis) := by
  let rows (v : BasisState) := (List.range 15).map (fun i=>(v (241+i),v (Leave225Hit.swaps i)))
  have geometry (v : BasisState) : readCells (shape 10) 0 15 (mappedBasis 10 v)=rows v := by rfl
  rw [geometry,geometry]
  apply List.map_congr_left
  intro i hi
  have port : ∀i∈List.range 15,241+i∈Leave225Close.history := by decide +kernel
  exact Prod.ext (previous _ (port _ hi)) (by simpa using polarity _ _ _ (swapPolarity ⟨i,List.mem_range.mp hi⟩) s m)

end ECDSAAdd.Entrant.StairPacket.Leave225PreservedRecords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

theorem lowFrame (i:Fin 136) (s:State) (m:List Bool) :
    let v:=run leave240 m s
    v.basis (271+i.val)=s.basis (271+i.val) ∧ v.basis (786+i.val)=s.basis (786+i.val) := by
  have cover:leave240.all (fun g=>decide ((destination g<271 ∨ 407≤destination g) ∧ (destination g<786 ∨ 922≤destination g)))=true := by decide +kernel
  have safe (q:Nat) (inside:(271≤q ∧ q<407) ∨ (786≤q ∧ q<922)):q∉leave240.map destination := by
    intro h;obtain ⟨g,hg,rfl⟩:=List.mem_map.mp h
    obtain ⟨a,d⟩:=of_decide_eq_true (List.all_eq_true.mp cover g hg)
    rcases inside with ⟨l,r⟩|⟨l,r⟩
    · exact a.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
    · exact d.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
  have hi:=i.isLt
  exact ⟨preserved _ s m _ (safe _ (Or.inl ⟨by omega,by omega⟩)),
    preserved _ s m _ (safe _ (Or.inr ⟨by omega,by omega⟩))⟩

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 136 15 z → chain (decide (2^136≤z.u)) xs)
    (first:Shadow.far 136 15 z → decide (2^136≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave240Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1713=decide (Shadow.far 136 15 z))
    (side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u)))
    (highZero:∀q:Nat,426≤q → q≤527 → s.basis q=false)
    (raw:State) (input:let a:=SkywalkNat.step^[15] z
       SkywalkIntegerInput Leave240WideWords.L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis) :
    let o:=pullState (OB5.sig 254) raw
    let out:=run leave240 m s
    (∀i:Fin 148,out.basis (271+i.val)=o.basis (271+i.val) ∧ out.basis (786+i.val)=o.basis (786+i.val)) ∧
    ∀i:Fin 109,out.basis (419+i.val)=false ∧
      out.basis (934+i.val)=(if o.basis 270 then o.basis (934+i.val) else o.basis (419+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  let o:=pullState (OB5.sig 254) raw
  let out:=run leave240 m s
  have word:=Leave240EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole:=Leave240Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared:=Leave240HighZero.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero nextSmall bound
  have orient:o.basis 270=G := by
    have geo:Leave240WideWords.L.previous=OB5.sig 254 270:=by decide +kernel
    change raw.basis (OB5.sig 254 270)=G
    rw [←geo];exact input.2.2.1
  have law:=LeaveShadowRails.retainedLow 136 z small sg
  constructor
  · intro i
    have fit:i.val<257:=by have h:=i.isLt;omega
    have ref:=Leave240WideWords.wide a G sg raw input ⟨i.val,fit⟩
    by_cases low:i.val<136
    · have hw:=Leave240WideWords.short h G sg s ready ⟨i.val,low⟩
      have untouched:=lowFrame ⟨i.val,low⟩ s m
      have spos:=LeaveSignedCoordinates.sharedDigit _ _ 136 i.val law.2.1 (Nat.le_of_lt low)
      have smag:=LeaveSignedCoordinates.sharedDigit _ _ 136 i.val law.2.2 (Nat.le_of_lt low)
      dsimp only at ref hw
      rw [law.1,spos,smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm),untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · let j:Fin 12:=⟨i.val-136,by have h:=i.isLt;omega⟩
      have eq:136+j.val=i.val:=by dsimp [j];omega
      have vals:=word.2.2.2.2.1 j
      dsimp only at ref vals
      rw [eq,show (407:Nat)+j.val=271+i.val by omega,show (922:Nat)+j.val=786+i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm,vals.2.trans ref.2.symm⟩
  · intro i
    let j:Fin 257:=⟨148+i.val,by have h:=i.isLt;omega⟩
    have ref:=Leave240WideWords.wide a G sg raw input j
    dsimp only [j] at ref
    rw [show 271+(148+i.val)=419+i.val by omega,show 786+(148+i.val)=934+i.val by omega] at ref
    have free:(run leave240 m s).basis (419+i.val)=false := by
      rw [whole.2.2.2.2,(upperMap i).2]
      exact (Function.update_of_ne (by have h:=i.isLt;change (419:Nat)+i.val≠1714;omega) _ _).trans (cleared i)
    refine ⟨free,?_⟩
    change out.basis (934+i.val)=(if o.basis 270 then o.basis (934+i.val) else o.basis (419+i.val))
    rw [orient,word.2.2.2.2.2 i];cases G <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using (by first | exact ref.1.symm | exact ref.2.symm)
end ECDSAAdd.Entrant.StairPacket.Leave240BoundaryRails

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240PreservedRecords
open LeaveSelector LeaveReadoutFrame Arithmetic IntegerPacket Partial LeaveCompanion LeaveCompanion240 Leave240Front Leave240Selector
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000

theorem swapPolarity : ∀i:Fin 15, LeaveSelector.parityAt (Leave240Hit.swaps i.val) leave240=some false := by decide +kernel

theorem result (s : State) (m : List Bool)
    (previous : ∀q∈Leave240Close.history,(run leave240 m s).basis q=s.basis q) :
    readCells (shape 11) 0 15 (mappedBasis 11 (run leave240 m s).basis) =
      readCells (shape 11) 0 15 (mappedBasis 11 s.basis) := by
  let rows (v : BasisState) := (List.range 15).map (fun i=>(v (256+i),v (Leave240Hit.swaps i)))
  have geometry (v : BasisState) : readCells (shape 11) 0 15 (mappedBasis 11 v)=rows v := by rfl
  rw [geometry,geometry]
  apply List.map_congr_left
  intro i hi
  have port : ∀i∈List.range 15,256+i∈Leave240Close.history := by decide +kernel
  exact Prod.ext (previous _ (port _ hi)) (by simpa using polarity _ _ _ (swapPolarity ⟨i,List.mem_range.mp hi⟩) s m)

end ECDSAAdd.Entrant.StairPacket.Leave240PreservedRecords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

theorem lowFrame (i:Fin 129) (s:State) (m:List Bool) :
    let v:=run leave255 m s
    v.basis (286+i.val)=s.basis (286+i.val) ∧ v.basis (786+i.val)=s.basis (786+i.val) := by
  have cover:leave255.all (fun g=>decide ((destination g<286 ∨ 415≤destination g) ∧ (destination g<786 ∨ 915≤destination g)))=true := by decide +kernel
  have safe (q:Nat) (inside:(286≤q ∧ q<415) ∨ (786≤q ∧ q<915)):q∉leave255.map destination := by
    intro h;obtain ⟨g,hg,rfl⟩:=List.mem_map.mp h
    obtain ⟨a,d⟩:=of_decide_eq_true (List.all_eq_true.mp cover g hg)
    rcases inside with ⟨l,r⟩|⟨l,r⟩
    · exact a.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
    · exact d.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
  have hi:=i.isLt
  exact ⟨preserved _ s m _ (safe _ (Or.inl ⟨by omega,by omega⟩)),
    preserved _ s m _ (safe _ (Or.inr ⟨by omega,by omega⟩))⟩

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 129 15 z → chain (decide (2^129≤z.u)) xs)
    (first:Shadow.far 129 15 z → decide (2^129≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave255Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1706=decide (Shadow.far 129 15 z))
    (side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u)))
    (highZero:∀q:Nat,434≤q → q≤528 → s.basis q=false)
    (raw:State) (input:let a:=SkywalkNat.step^[15] z
       SkywalkIntegerInput Leave255WideWords.L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis) :
    let o:=pullState (OB5.sig 269) raw
    let out:=run leave255 m s
    (∀i:Fin 140,out.basis (286+i.val)=o.basis (286+i.val) ∧ out.basis (786+i.val)=o.basis (786+i.val)) ∧
    ∀i:Fin 103,out.basis (426+i.val)=false ∧
      out.basis (926+i.val)=(if o.basis 285 then o.basis (926+i.val) else o.basis (426+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  let o:=pullState (OB5.sig 269) raw
  let out:=run leave255 m s
  have word:=Leave255EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole:=Leave255Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared:=Leave255HighZero.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero nextSmall bound
  have orient:o.basis 285=G := by
    have geo:Leave255WideWords.L.previous=OB5.sig 269 285:=by decide +kernel
    change raw.basis (OB5.sig 269 285)=G
    rw [←geo];exact input.2.2.1
  have law:=LeaveShadowRails.retainedLow 129 z small sg
  constructor
  · intro i
    have fit:i.val<243:=by have h:=i.isLt;omega
    have ref:=Leave255WideWords.wide a G sg raw input ⟨i.val,fit⟩
    by_cases low:i.val<129
    · have hw:=Leave255WideWords.short h G sg s ready ⟨i.val,low⟩
      have untouched:=lowFrame ⟨i.val,low⟩ s m
      have spos:=LeaveSignedCoordinates.sharedDigit _ _ 129 i.val law.2.1 (Nat.le_of_lt low)
      have smag:=LeaveSignedCoordinates.sharedDigit _ _ 129 i.val law.2.2 (Nat.le_of_lt low)
      dsimp only at ref hw
      rw [law.1,spos,smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm),untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · let j:Fin 11:=⟨i.val-129,by have h:=i.isLt;omega⟩
      have eq:129+j.val=i.val:=by dsimp [j];omega
      have vals:=word.2.2.2.2.1 j
      dsimp only at ref vals
      rw [eq,show (415:Nat)+j.val=286+i.val by omega,show (915:Nat)+j.val=786+i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm,vals.2.trans ref.2.symm⟩
  · intro i
    let j:Fin 243:=⟨140+i.val,by have h:=i.isLt;omega⟩
    have ref:=Leave255WideWords.wide a G sg raw input j
    dsimp only [j] at ref
    rw [show 286+(140+i.val)=426+i.val by omega,show 786+(140+i.val)=926+i.val by omega] at ref
    have free:(run leave255 m s).basis (426+i.val)=false := by
      rw [whole.2.2.2.2,(upperMap i).2]
      exact (Function.update_of_ne (by have h:=i.isLt;change (426:Nat)+i.val≠1707;omega) _ _).trans (cleared i)
    refine ⟨free,?_⟩
    change out.basis (926+i.val)=(if o.basis 285 then o.basis (926+i.val) else o.basis (426+i.val))
    rw [orient,word.2.2.2.2.2 i];cases G <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using (by first | exact ref.1.symm | exact ref.2.symm)
end ECDSAAdd.Entrant.StairPacket.Leave255BoundaryRails

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255PreservedRecords
open LeaveSelector LeaveReadoutFrame Arithmetic IntegerPacket Partial LeaveCompanion LeaveCompanion255 Leave255Front Leave255Selector
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000

theorem swapPolarity : ∀i:Fin 15, LeaveSelector.parityAt (Leave255Hit.swaps i.val) leave255=some false := by decide +kernel

theorem result (s : State) (m : List Bool)
    (previous : ∀q∈Leave255Close.history,(run leave255 m s).basis q=s.basis q) :
    readCells (shape 12) 0 15 (mappedBasis 12 (run leave255 m s).basis) =
      readCells (shape 12) 0 15 (mappedBasis 12 s.basis) := by
  let rows (v : BasisState) := (List.range 15).map (fun i=>(v (271+i),v (Leave255Hit.swaps i)))
  have geometry (v : BasisState) : readCells (shape 12) 0 15 (mappedBasis 12 v)=rows v := by rfl
  rw [geometry,geometry]
  apply List.map_congr_left
  intro i hi
  have port : ∀i∈List.range 15,271+i∈Leave255Close.history := by decide +kernel
  exact Prod.ext (previous _ (port _ hi)) (by simpa using polarity _ _ _ (swapPolarity ⟨i,List.mem_range.mp hi⟩) s m)

end ECDSAAdd.Entrant.StairPacket.Leave255PreservedRecords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112)
    (far:s.basis 1721=decide (Shadow.far 144 15 z))
    (side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u))) (g0 s0 : Bool)
    (record : readCells (shape 10) 0 15 (mappedBasis 10 s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out:=run leave225 m s
    let cells:=readCells (shape 10) 0 15 (mappedBasis 10 out.basis)
    cells=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis 1716=decide (Shadow.far 144 15 z) ∧
      out.basis 1717=(decide (Shadow.far 144 15 z) && afterFlags (decide (z.v<z.u)) (cells.take 5)) ∧
      out.basis 1718=(decide (Shadow.far 144 15 z) && HighBankSum.cross (Leave225TrueMiddle.d z)) := by
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave225RecordedParity.result s z g0 s0 small odd record
  have mode : actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u:=by
    rw [far,side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave225RecordedEvents.result s z g0 s0 small odd record
  have all:=Leave225Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have words:=Leave225EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept:=(Leave225PreservedRecords.result s m words.2.2.2.1).trans record
  refine ⟨kept,all.2.1,?_,all.2.2.2.1⟩
  rw [kept,all.2.2.1]
  by_cases active:Shadow.far 144 15 z
  · rw [LeaveTraceHistory.orient _ _ small active]
  · simp [active]
end ECDSAAdd.Entrant.StairPacket.Leave225ActualHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

def leftovers (q : Wire) : Prop :=
  (240≤q ∧ q<256) ∨ (1269≤q ∧ q<1284)

private theorem indexOfRange (q start count:Nat) (a:start≤q) (b:q<start+count) :
    ∃i:Fin count, start+i.val=q :=
  ⟨⟨q-start,by omega⟩,by change start+(q-start)=q;omega⟩

theorem result (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis 1715=neg) (mode : s.basis 1713=far) (side : s.basis 1714=long)
    (low : ∀i:Fin 155, s.basis (256+i.val)=o.basis (256+i.val) ∧ s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin 102, s.basis (411+i.val)=false ∧
      s.basis (941+i.val)=(if o.basis 255 then o.basis (941+i.val) else o.basis (411+i.val)))
    (ext : ∀q,Exterior 225 512 q → s.basis q=o.basis q)
    (left : ∀q,leftovers q → s.basis q=o.basis q)
    (clear : ∀q∈Leave225BoundaryClean.zeros,s.basis q=false)
    (carry : ∀q:Wire,1556≤q → q≤1812 → o.basis q=false) :
    PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long o (eraseSites Enter240.pending s) := by
  have loShape : Enter240.lowerPairs=(List.finRange 3).map (fun j=>(256+(152+j.val),786+(152+j.val))) := by decide +kernel
  have hiShape : Enter240.upperPairs=(List.finRange 102).map (fun j=>(411+j.val,941+j.val)) := by decide +kernel
  have away (q:Wire) (small:q<1556) : (eraseSites Enter240.pending s).basis q=s.basis q := by
    have no:q∉Enter240.pending:=by simp [Enter240.pending,Wire] at *;omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · simpa [eraseSites,Enter240.pending] using sign
  · simpa [eraseSites,Enter240.pending] using mode
  · simpa [eraseSites,Enter240.pending] using side
  · intro pair mem
    rw [loShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (256+(152+j.val)) (by change 256+(152+j.val)<1556;omega),away (786+(152+j.val)) (by change 786+(152+j.val)<1556;omega)]
    exact low ⟨152+j.val,by omega⟩
  · intro pair mem
    rw [hiShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (411+j.val) (by change 411+j.val<1556;omega),away (941+j.val) (by change 941+j.val<1556;omega)]
    exact high j
  · intro q notN notF notU _ notHi
    by_cases pending:q∈Enter240.pending
    · have range : ∀q∈Enter240.pending,1556≤q ∧ q≤1812 := by decide +kernel
      obtain ⟨lo,hi⟩:=range q pending
      simp [eraseSites,pending,carry q lo hi]
    simp only [eraseSites,if_neg pending]
    by_cases external:Exterior 225 512 q
    · exact ext q external
    by_cases residual:leftovers q
    · exact left q residual
    have hiA (i:Fin 102) : 411+i.val∈sites Enter240.upperPairs := by
      exact (by decide +kernel : ∀i:Fin 102,411+i.val∈sites Enter240.upperPairs) i
    have hiB (i:Fin 102) : 941+i.val∈sites Enter240.upperPairs := by
      exact (by decide +kernel : ∀i:Fin 102,941+i.val∈sites Enter240.upperPairs) i
    have outside (start count:Nat) (h:∀i:Fin count,start+i.val∈sites Enter240.upperPairs) : ¬(start≤q ∧ q<start+count) := by
      rintro ⟨a,b⟩
      obtain ⟨i,eq⟩:=indexOfRange q start count a b
      exact notHi (eq ▸ h i)
    have notA:=outside _ _ hiA
    have notB:=outside _ _ hiB
    by_cases a:256≤q ∧ q<411
    · obtain ⟨l,r⟩:=a
      obtain ⟨i,eq⟩:=indexOfRange q 256 155 l r
      exact eq ▸ (low i).1
    by_cases b:786≤q ∧ q<941
    · obtain ⟨l,r⟩:=b
      obtain ⟨i,eq⟩:=indexOfRange q 786 155 l r
      exact eq ▸ (low i).2
    have bounds : 1556≤q ∧ q≤1812 := by
      unfold Exterior at external;unfold leftovers at residual
      simp only [Wire] at *
      omega
    rw [carry _ bounds.1 bounds.2]
    apply clear
    simp only [Leave225BoundaryClean.zeros,List.mem_append,List.mem_range'_1]
    simp [Enter240.pending,Wire] at pending
    simp only [Wire] at *
    omega
end ECDSAAdd.Entrant.StairPacket.Leave225AssembleCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120)
    (far:s.basis 1713=decide (Shadow.far 136 15 z))
    (side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u))) (g0 s0 : Bool)
    (record : readCells (shape 11) 0 15 (mappedBasis 11 s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out:=run leave240 m s
    let cells:=readCells (shape 11) 0 15 (mappedBasis 11 out.basis)
    cells=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis 1709=decide (Shadow.far 136 15 z) ∧
      out.basis 1710=(decide (Shadow.far 136 15 z) && afterFlags (decide (z.v<z.u)) (cells.take 5)) ∧
      out.basis 1711=(decide (Shadow.far 136 15 z) && HighBankSum.cross (Leave240TrueMiddle.d z)) := by
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave240RecordedParity.result s z g0 s0 small odd record
  have mode : actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u:=by
    rw [far,side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave240RecordedEvents.result s z g0 s0 small odd record
  have all:=Leave240Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have words:=Leave240EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept:=(Leave240PreservedRecords.result s m words.2.2.2.1).trans record
  refine ⟨kept,all.2.1,?_,all.2.2.2.1⟩
  rw [kept,all.2.2.1]
  by_cases active:Shadow.far 136 15 z
  · rw [LeaveTraceHistory.orient _ _ small active]
  · simp [active]
end ECDSAAdd.Entrant.StairPacket.Leave240ActualHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

def leftovers (q : Wire) : Prop :=
  (255≤q ∧ q<271) ∨ (1284≤q ∧ q<1299)

private theorem indexOfRange (q start count:Nat) (a:start≤q) (b:q<start+count) :
    ∃i:Fin count, start+i.val=q :=
  ⟨⟨q-start,by omega⟩,by change start+(q-start)=q;omega⟩

theorem result (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis 1708=neg) (mode : s.basis 1706=far) (side : s.basis 1707=long)
    (low : ∀i:Fin 148, s.basis (271+i.val)=o.basis (271+i.val) ∧ s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin 109, s.basis (419+i.val)=false ∧
      s.basis (934+i.val)=(if o.basis 270 then o.basis (934+i.val) else o.basis (419+i.val)))
    (ext : ∀q,Exterior 240 527 q → s.basis q=o.basis q)
    (left : ∀q,leftovers q → s.basis q=o.basis q)
    (clear : ∀q∈Leave240BoundaryClean.zeros,s.basis q=false)
    (carry : ∀q:Wire,1556≤q → q≤1812 → o.basis q=false) :
    PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long o (eraseSites Enter255.pending s) := by
  have loShape : Enter255.lowerPairs=(List.finRange 3).map (fun j=>(271+(145+j.val),786+(145+j.val))) := by decide +kernel
  have hiShape : Enter255.upperPairs=(List.finRange 109).map (fun j=>(419+j.val,934+j.val)) := by decide +kernel
  have away (q:Wire) (small:q<1556) : (eraseSites Enter255.pending s).basis q=s.basis q := by
    have no:q∉Enter255.pending:=by simp [Enter255.pending,Wire] at *;omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · simpa [eraseSites,Enter255.pending] using sign
  · simpa [eraseSites,Enter255.pending] using mode
  · simpa [eraseSites,Enter255.pending] using side
  · intro pair mem
    rw [loShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (271+(145+j.val)) (by change 271+(145+j.val)<1556;omega),away (786+(145+j.val)) (by change 786+(145+j.val)<1556;omega)]
    exact low ⟨145+j.val,by omega⟩
  · intro pair mem
    rw [hiShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (419+j.val) (by change 419+j.val<1556;omega),away (934+j.val) (by change 934+j.val<1556;omega)]
    exact high j
  · intro q notN notF notU _ notHi
    by_cases pending:q∈Enter255.pending
    · have range : ∀q∈Enter255.pending,1556≤q ∧ q≤1812 := by decide +kernel
      obtain ⟨lo,hi⟩:=range q pending
      simp [eraseSites,pending,carry q lo hi]
    simp only [eraseSites,if_neg pending]
    by_cases external:Exterior 240 527 q
    · exact ext q external
    by_cases residual:leftovers q
    · exact left q residual
    have hiA (i:Fin 109) : 419+i.val∈sites Enter255.upperPairs := by
      exact (by decide +kernel : ∀i:Fin 109,419+i.val∈sites Enter255.upperPairs) i
    have hiB (i:Fin 109) : 934+i.val∈sites Enter255.upperPairs := by
      exact (by decide +kernel : ∀i:Fin 109,934+i.val∈sites Enter255.upperPairs) i
    have outside (start count:Nat) (h:∀i:Fin count,start+i.val∈sites Enter255.upperPairs) : ¬(start≤q ∧ q<start+count) := by
      rintro ⟨a,b⟩
      obtain ⟨i,eq⟩:=indexOfRange q start count a b
      exact notHi (eq ▸ h i)
    have notA:=outside _ _ hiA
    have notB:=outside _ _ hiB
    by_cases a:271≤q ∧ q<419
    · obtain ⟨l,r⟩:=a
      obtain ⟨i,eq⟩:=indexOfRange q 271 148 l r
      exact eq ▸ (low i).1
    by_cases b:786≤q ∧ q<934
    · obtain ⟨l,r⟩:=b
      obtain ⟨i,eq⟩:=indexOfRange q 786 148 l r
      exact eq ▸ (low i).2
    have bounds : 1556≤q ∧ q≤1812 := by
      unfold Exterior at external;unfold leftovers at residual
      simp only [Wire] at *
      omega
    rw [carry _ bounds.1 bounds.2]
    apply clear
    simp only [Leave240BoundaryClean.zeros,List.mem_append,List.mem_range'_1]
    simp [Enter255.pending,Wire] at pending
    simp only [Wire] at *
    omega
end ECDSAAdd.Entrant.StairPacket.Leave240AssembleCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127)
    (far:s.basis 1706=decide (Shadow.far 129 15 z))
    (side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u))) (g0 s0 : Bool)
    (record : readCells (shape 12) 0 15 (mappedBasis 12 s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out:=run leave255 m s
    let cells:=readCells (shape 12) 0 15 (mappedBasis 12 out.basis)
    cells=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis 1701=decide (Shadow.far 129 15 z) ∧
      out.basis 1702=(decide (Shadow.far 129 15 z) && afterFlags (decide (z.v<z.u)) (cells.take 5)) ∧
      out.basis 1703=(decide (Shadow.far 129 15 z) && HighBankSum.cross (Leave255TrueMiddle.d z)) := by
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave255RecordedParity.result s z g0 s0 small odd record
  have mode : actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u:=by
    rw [far,side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave255RecordedEvents.result s z g0 s0 small odd record
  have all:=Leave255Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have words:=Leave255EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept:=(Leave255PreservedRecords.result s m words.2.2.2.1).trans record
  refine ⟨kept,all.2.1,?_,all.2.2.2.1⟩
  rw [kept,all.2.2.1]
  by_cases active:Shadow.far 129 15 z
  · rw [LeaveTraceHistory.orient _ _ small active]
  · simp [active]
end ECDSAAdd.Entrant.StairPacket.Leave255ActualHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

def leftovers (q : Wire) : Prop :=
  (270≤q ∧ q<286) ∨ (1299≤q ∧ q<1314) ∨ q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1800≤q ∧ q≤1812)

private theorem indexOfRange (q start count:Nat) (a:start≤q) (b:q<start+count) :
    ∃i:Fin count, start+i.val=q :=
  ⟨⟨q-start,by omega⟩,by change start+(q-start)=q;omega⟩

theorem result (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis 1700=neg) (mode : s.basis 1698=far) (side : s.basis 1699=long)
    (low : ∀i:Fin 140, s.basis (286+i.val)=o.basis (286+i.val) ∧ s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin 103, s.basis (426+i.val)=false ∧
      s.basis (926+i.val)=(if o.basis 285 then o.basis (926+i.val) else o.basis (426+i.val)))
    (ext : ∀q,Exterior 255 529 q → s.basis q=o.basis q)
    (left : ∀q,leftovers q → s.basis q=o.basis q)
    (clear : ∀q∈Leave255BoundaryClean.zeros,s.basis q=false)
    (carry : ∀q:Wire,1556≤q → q≤1799 → o.basis q=false) :
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 neg far long o (eraseSites ParkEndpoint.src s) := by
  have loShape : Portal270Flag.loPairs=(List.finRange 3).map (fun j=>(286+(137+j.val),786+(137+j.val))) := by decide +kernel
  have hiShape : Portal270Flag.hiPairs=(List.finRange 103).map (fun j=>(426+j.val,926+j.val)) := by decide +kernel
  have away (q:Wire) (small:q<1556) : (eraseSites ParkEndpoint.src s).basis q=s.basis q := by
    have no:q∉ParkEndpoint.src:=by simp [ParkEndpoint.src,Wire] at *;omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · simpa [eraseSites,ParkEndpoint.src] using sign
  · simpa [eraseSites,ParkEndpoint.src] using mode
  · simpa [eraseSites,ParkEndpoint.src] using side
  · intro pair mem
    rw [loShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (286+(137+j.val)) (by change 286+(137+j.val)<1556;omega),away (786+(137+j.val)) (by change 786+(137+j.val)<1556;omega)]
    exact low ⟨137+j.val,by omega⟩
  · intro pair mem
    rw [hiShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (426+j.val) (by change 426+j.val<1556;omega),away (926+j.val) (by change 926+j.val<1556;omega)]
    exact high j
  · intro q notN notF notU _ notHi
    by_cases pending:q∈ParkEndpoint.src
    · have range : ∀q∈ParkEndpoint.src,1556≤q ∧ q≤1799 := by decide +kernel
      obtain ⟨lo,hi⟩:=range q pending
      simp [eraseSites,pending,carry q lo hi]
    simp only [eraseSites,if_neg pending]
    by_cases external:Exterior 255 529 q
    · exact ext q external
    by_cases residual:leftovers q
    · exact left q residual
    have hiA (i:Fin 103) : 426+i.val∈sites Portal270Flag.hiPairs := by
      exact (by decide +kernel : ∀i:Fin 103,426+i.val∈sites Portal270Flag.hiPairs) i
    have hiB (i:Fin 103) : 926+i.val∈sites Portal270Flag.hiPairs := by
      exact (by decide +kernel : ∀i:Fin 103,926+i.val∈sites Portal270Flag.hiPairs) i
    have outside (start count:Nat) (h:∀i:Fin count,start+i.val∈sites Portal270Flag.hiPairs) : ¬(start≤q ∧ q<start+count) := by
      rintro ⟨a,b⟩
      obtain ⟨i,eq⟩:=indexOfRange q start count a b
      exact notHi (eq ▸ h i)
    have notA:=outside _ _ hiA
    have notB:=outside _ _ hiB
    by_cases a:286≤q ∧ q<426
    · obtain ⟨l,r⟩:=a
      obtain ⟨i,eq⟩:=indexOfRange q 286 140 l r
      exact eq ▸ (low i).1
    by_cases b:786≤q ∧ q<926
    · obtain ⟨l,r⟩:=b
      obtain ⟨i,eq⟩:=indexOfRange q 786 140 l r
      exact eq ▸ (low i).2
    have bounds : 1556≤q ∧ q≤1799 := by
      unfold Exterior at external;unfold leftovers at residual
      simp only [Wire] at *
      omega
    rw [carry _ bounds.1 bounds.2]
    apply clear
    simp only [Leave255BoundaryClean.zeros,List.mem_append,List.mem_range'_1]
    simp [ParkEndpoint.src,Wire] at pending
    simp only [Wire] at *
    omega
end ECDSAAdd.Entrant.StairPacket.Leave255AssembleCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ReleasedActual
open Arithmetic MappedCompressed IntegerPacket WideReference EnterProof NativePack255 Partial LeaveReadoutFrame
set_option maxRecDepth 32000
set_option maxHeartbeats 2700000

def mirrorSites:=List.range' 1301 13
def untouched:=529::mirrorSites

theorem agree (d:Bool) (raw s:State) (x p:Nat) (good:Bounds x p) (dom:Domain 255 x p raw)
    (a b m:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (clear:∀q∈Leave255BoundaryClean.zeros,
      (run leave255 m (run (body idx (withArchive d)) b (run enter255 a s))).basis q=false) :
    let v:=run (body idx (withArchive d)) b (run enter255 a s)
    ∀q:Wire, q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1313) →
      (run leave255 m v).basis q=(origin 255 raw v).basis q := by
  let v:=run (body idx (withArchive d)) b (run enter255 a s)
  have stable : ∀q∈untouched,q∉leave255.map LeaveReadoutFrame.destination := by decide +kernel
  have mirror (q:Wire) (lo:1301≤q) (hi:q≤1313) : v.basis q=false := by
    have mem:q∈mirrorSites:=List.mem_range'_1.mpr ⟨lo,Nat.lt_succ_of_le hi⟩
    have marks : ∀q∈mirrorSites,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary255.rawPortsList) ∧
        q∉ports255 ∧ q∉Enter255.pending ∧ OB5.sig 254 q=q ∧ q≠1708 ∧ q≠1706 ∧ q≠1707 ∧
        q∉RailPair.sites Enter255.upperPairs := by decide +kernel
    obtain ⟨off,adminOff,enterOff,mask,source,hn,hf,hu,no⟩:=marks q mem
    have normal:=ext_head enter255 idx (withArchive d) (support++ArchiveBoundary255.rawPortsList) s a b q off
      (fun h=>enterOff (List.mem_toFinset.mp (Enter255.programCover h))) adminOff (admin_cover d)
    apply normal.trans
    have original:raw.basis q=false:=by
      obtain ⟨ref,match',stage⟩:=dom
      apply (match'.2 q (outside_above (by change 1044+255≤q;simp only [Wire] at *;omega))).trans
      have fields:=(W.compactSkywalkStage_fields_iff base _ 255 (by decide) base_pool_nodup _).mp stage
      have qid:q=base (1028+(q-1044)):=by change q=1028+(q-1044)+16;simp only [Wire] at *;omega
      have jlo:255≤q-1044:=by simp only [Wire] at *;omega
      have jhi:q-1044<512:=by simp only [Wire] at *;omega
      exact qid ▸ (fields.2.2.2.2.1 _ jlo jhi).2
    have cleared:((eraseSites Enter255.pending s)).basis q=false:=
      (cut.unchanged q hn hf hu no).trans (by simpa only [pullState,source] using original)
    simpa [eraseSites,mask] using cleared
  dsimp only
  intro q site
  rw [Leave255ReleasedOrigin.released _ _ good _ _ dom _ site]
  rcases site with rfl|band|⟨lo,hi⟩
  · rw [preserved _ _ _ _ (stable 529 (by decide))]
    exact upper_clear _ _ _ _ _ dom _ _ _ _ _ cut 529 (by decide) (by decide)
  · exact clear q (by simp only [Leave255BoundaryClean.zeros,List.mem_append,List.mem_range'_1];simp only [Wire] at *;omega)
  · have mem:q∈mirrorSites:=List.mem_range'_1.mpr ⟨lo,Nat.lt_succ_of_le hi⟩
    rw [preserved _ _ _ _ (stable q (List.mem_cons_of_mem _ mem))]
    exact mirror q lo hi
end ECDSAAdd.Entrant.StairPacket.Leave255ReleasedActual

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
structure Numeric (z:SkywalkNat.State):Prop where
  small:min z.u z.v<2^144
  odd:z.v%2=1
  room:Shadow.high 144 15 z+1<2^97
  nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136
  bound:Leave225TrueMiddle.F z<2^112

theorem actualNumbers (x p:Nat) (hp0:0<p) (odd:p%2=1) (hx:x<2^256) (hp:p<2^256):
    Numeric (SkywalkNat.step^[225] (SkywalkNat.init x p)):=by
  let z:=SkywalkNat.step^[225] (SkywalkNat.init x p)
  have env:z.u+z.v≤2^256+2^255:=LeaveBankEnvelope.after_first x p (2^256) hx.le hp.le 224
  have short:=true_small x p 240 hx hp (by decide)
  have it:SkywalkNat.step^[15] z=SkywalkNat.step^[240] (SkywalkNat.init x p):=by
    exact (Function.iterate_add_apply SkywalkNat.step 15 225 _).symm
  refine ⟨true_small x p 225 hx hp (by decide),(SkywalkNat.iter_valid 225 (SkywalkNat.init x p) hp0 odd).2.1,
    (LeaveBankEnvelope.bounds z env).1,?_,(LeaveBankEnvelope.outputs z (by omega) 15).1⟩
  rw [it];exact short

def flags (z:SkywalkNat.State) (g0 s0:Bool):Bool×Bool:=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
structure Inputs (s:State) (z:SkywalkNat.State) (g0 s0:Bool):Prop extends Numeric z where
  ready:onRails 10 15 (encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis
  fresh:s.basis 1723=false
  scratch:∀q∈1556::1557::1558::fullC,s.basis q=false
  temp:∀p∈longPairs,s.basis p.2=false
  clean:∀q∈carries,s.basis q=false
  padding:∀t:Nat,97≤t→t<112→s.basis (wire t)=false
  bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0
  zero:∀q∈Leave225FrontReady.watched,s.basis q=false
  far:s.basis 1721=decide (Shadow.far 144 15 z)
  side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u))
  record:readCells (shape 10) 0 15 (mappedBasis 10 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
def spare:List Wire:=[1724, 1725]
private def touch:= (1556::1557::1558::fullC) ++ longPairs.map Prod.snd ++ carries ++ ((List.range' 97 15).map wire) ++ Leave225FrontReady.watched
private theorem geometry:∀q∈touch,(1556≤q ∧ q≤1717) ∨ q∈spare:=by decide +kernel
theorem assemble (s:State) (z:SkywalkNat.State) (g0 s0:Bool) (numbers:Numeric z)
    (rails:onRails 10 15 (SkywalkTrace.next^[15] (encode g0 s0 (Shadow.reduced 144 15 z).u (Shadow.reduced 144 15 z).v)) s.basis)
    (record:readCells (shape 10) 0 15 (mappedBasis 10 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
    (saved:regValue ys s.basis=(if Shadow.far 144 15 z then Shadow.high 144 15 z else 0) ∧
      s.basis 1723=false ∧ s.basis 1721=decide (Shadow.far 144 15 z) ∧ s.basis 1722=decide (Shadow.far 144 15 z ∧ 2^144≤z.u))
    (ex:∀q∈spare,s.basis q=false):Inputs s z g0 s0:=by
  have cl:=carry225 _ s rails
  have all (q:Wire) (hit:q∈touch):s.basis q=false:=by
    rcases geometry q hit with h|h
    · exact cl q h.1 h.2
    · exact ex q h
  refine ⟨numbers,?_,saved.2.1,?_,?_,?_,?_,saved.1,?_,saved.2.2.1,?_,record⟩
  · exact (SharedSigned.same _ z numbers.small numbers.odd g0 s0).1 ▸ rails
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · intro t h;apply all;have mem:=List.mem_map_of_mem (f:=Prod.snd) h;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inr mem)))
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inr h))
  · intro t lo hi
    have hit:t∈List.range' 97 15:=List.mem_range'_1.mpr ⟨lo,hi⟩
    apply all
    have mem:=List.mem_map_of_mem (f:=wire) hit
    simp only [touch,List.mem_append];exact Or.inl (Or.inr mem)
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inr h
  · rw [saved.2.2.2]
    by_cases f:Shadow.far 144 15 z <;> simp [f]
end ECDSAAdd.Entrant.StairPacket.Leave225Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

theorem result (x p : Nat) (good:Bounds x p) (raw s:State) (m:List Bool) (g sg:Bool)
    (domain:Domain 225 x p raw)
    (input:InputAt 225 (encode g sg (unsigned 225 x p).u (unsigned 225 x p).v) raw)
    (record:physicalCells 10 s=SkywalkTrace.trace 15 (encode g sg (unsigned 225 x p).u (unsigned 225 x p).v))
    (kept:physicalCells 10 (run leave225 m s)=physicalCells 10 s)
     :
    ∀q,Leave225AssembleCut.leftovers q → (run leave225 m s).basis q=(origin 225 raw s).basis q := by
  let out:=run leave225 m s
  let o:=origin 225 raw s
  have geo : ∀i:Fin 15,windowNet 10 (ports (shape 10) i.val).a0=241+i.val ∧
      windowNet 10 (ports (shape 10) i.val).history=Leave225Hit.swaps i.val := by decide +kernel
  have agree (i:Fin 15) : out.basis (241+i.val)=o.basis (241+i.val) ∧
      out.basis (Leave225Hit.swaps i.val)=o.basis (Leave225Hit.swaps i.val) := by
    have old:=recorded_equal _ _ _ _ (by decide) places225 good raw s domain g sg input record i
    have now:=congrArg (fun a=>StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (shape 10) 0 15 (mappedBasis 10 out.basis)) i.val =
      StairArchiveRaw.read (readCells (shape 10) 0 15 (mappedBasis 10 s.basis)) i.val at now
    rw [read_cells _ _ _ _ _ i.isLt,read_cells _ _ _ _ _ i.isLt,Nat.zero_add] at now
    have eq:=now.trans old
    change (out.basis (windowNet 10 (ports (shape 10) i.val).a0),out.basis (windowNet 10 (ports (shape 10) i.val).history)) =
      (o.basis (windowNet 10 (ports (shape 10) i.val).a0),o.basis (windowNet 10 (ports (shape 10) i.val).history)) at eq
    rw [(geo i).1,(geo i).2] at eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  have previous : out.basis 240=o.basis 240 := by
    rw [show o.basis 240=s.basis 240 from inside _ _ _ _ (by decide +kernel)]
    have stable : LeaveSelector.parityAt 240 leave225=some false := by decide +kernel
    simpa [out] using polarity _ _ _ stable s m
  let gs:=(List.finRange 15).map (fun i=>241+i.val)
  let ss:=(List.finRange 15).map (fun i=>Leave225Hit.swaps i.val)
  intro q residual
  by_cases prev:q=240
  · subst q;exact previous
  by_cases gg:q∈gs
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp gg;exact (agree i).1
  by_cases sw:q∈ss
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp sw;exact (agree i).2
  have census : ∀a:Fin 1813,Leave225AssembleCut.leftovers a.val → a.val≠240 → a.val∉gs → a.val∉ss →
      False := by
    unfold Leave225AssembleCut.leftovers; dsimp only [gs,ss];decide +kernel
  have bound:q<1813:=by unfold Leave225AssembleCut.leftovers at residual;simp only [Wire] at *;omega
  exact False.elim (census ⟨q,bound⟩ residual prev gg sw)
end ECDSAAdd.Entrant.StairPacket.Leave225FrameHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
structure Numeric (z:SkywalkNat.State):Prop where
  small:min z.u z.v<2^136
  odd:z.v%2=1
  room:Shadow.high 136 15 z+1<2^105
  nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129
  bound:Leave240TrueMiddle.F z<2^120

theorem actualNumbers (x p:Nat) (hp0:0<p) (odd:p%2=1) (hx:x<2^256) (hp:p<2^256):
    Numeric (SkywalkNat.step^[240] (SkywalkNat.init x p)):=by
  let z:=SkywalkNat.step^[240] (SkywalkNat.init x p)
  have env:z.u+z.v≤2^256+2^255:=LeaveBankEnvelope.after_first x p (2^256) hx.le hp.le 239
  have short:=true_small x p 255 hx hp (by decide)
  have it:SkywalkNat.step^[15] z=SkywalkNat.step^[255] (SkywalkNat.init x p):=by
    exact (Function.iterate_add_apply SkywalkNat.step 15 240 _).symm
  refine ⟨true_small x p 240 hx hp (by decide),(SkywalkNat.iter_valid 240 (SkywalkNat.init x p) hp0 odd).2.1,
    (LeaveBankEnvelope.bounds z env).2.1,?_,(LeaveBankEnvelope.outputs z (by omega) 15).2.1⟩
  rw [it];exact short

def flags (z:SkywalkNat.State) (g0 s0:Bool):Bool×Bool:=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
structure Inputs (s:State) (z:SkywalkNat.State) (g0 s0:Bool):Prop extends Numeric z where
  ready:onRails 11 15 (encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis
  fresh:s.basis 1715=false
  scratch:∀q∈1556::1557::1558::fullC,s.basis q=false
  temp:∀p∈longPairs,s.basis p.2=false
  clean:∀q∈carries,s.basis q=false
  padding:∀t:Nat,105≤t→t<120→s.basis (wire t)=false
  bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0
  zero:∀q∈Leave240FrontReady.watched,s.basis q=false
  far:s.basis 1713=decide (Shadow.far 136 15 z)
  side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u))
  record:readCells (shape 11) 0 15 (mappedBasis 11 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
def spare:List Wire:=[1716, 1717]
private def touch:= (1556::1557::1558::fullC) ++ longPairs.map Prod.snd ++ carries ++ ((List.range' 105 15).map wire) ++ Leave240FrontReady.watched
private theorem geometry:∀q∈touch,(1556≤q ∧ q≤1709) ∨ q∈spare:=by decide +kernel
theorem assemble (s:State) (z:SkywalkNat.State) (g0 s0:Bool) (numbers:Numeric z)
    (rails:onRails 11 15 (SkywalkTrace.next^[15] (encode g0 s0 (Shadow.reduced 136 15 z).u (Shadow.reduced 136 15 z).v)) s.basis)
    (record:readCells (shape 11) 0 15 (mappedBasis 11 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
    (saved:regValue ys s.basis=(if Shadow.far 136 15 z then Shadow.high 136 15 z else 0) ∧
      s.basis 1715=false ∧ s.basis 1713=decide (Shadow.far 136 15 z) ∧ s.basis 1714=decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
    (ex:∀q∈spare,s.basis q=false):Inputs s z g0 s0:=by
  have cl:=carry240 _ s rails
  have all (q:Wire) (hit:q∈touch):s.basis q=false:=by
    rcases geometry q hit with h|h
    · exact cl q h.1 h.2
    · exact ex q h
  refine ⟨numbers,?_,saved.2.1,?_,?_,?_,?_,saved.1,?_,saved.2.2.1,?_,record⟩
  · exact (SharedSigned.same _ z numbers.small numbers.odd g0 s0).1 ▸ rails
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · intro t h;apply all;have mem:=List.mem_map_of_mem (f:=Prod.snd) h;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inr mem)))
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inr h))
  · intro t lo hi
    have hit:t∈List.range' 105 15:=List.mem_range'_1.mpr ⟨lo,hi⟩
    apply all
    have mem:=List.mem_map_of_mem (f:=wire) hit
    simp only [touch,List.mem_append];exact Or.inl (Or.inr mem)
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inr h
  · rw [saved.2.2.2]
    by_cases f:Shadow.far 136 15 z <;> simp [f]
end ECDSAAdd.Entrant.StairPacket.Leave240Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

theorem result (x p : Nat) (good:Bounds x p) (raw s:State) (m:List Bool) (g sg:Bool)
    (domain:Domain 240 x p raw)
    (input:InputAt 240 (encode g sg (unsigned 240 x p).u (unsigned 240 x p).v) raw)
    (record:physicalCells 11 s=SkywalkTrace.trace 15 (encode g sg (unsigned 240 x p).u (unsigned 240 x p).v))
    (kept:physicalCells 11 (run leave240 m s)=physicalCells 11 s)
     :
    ∀q,Leave240AssembleCut.leftovers q → (run leave240 m s).basis q=(origin 240 raw s).basis q := by
  let out:=run leave240 m s
  let o:=origin 240 raw s
  have geo : ∀i:Fin 15,windowNet 11 (ports (shape 11) i.val).a0=256+i.val ∧
      windowNet 11 (ports (shape 11) i.val).history=Leave240Hit.swaps i.val := by decide +kernel
  have agree (i:Fin 15) : out.basis (256+i.val)=o.basis (256+i.val) ∧
      out.basis (Leave240Hit.swaps i.val)=o.basis (Leave240Hit.swaps i.val) := by
    have old:=recorded_equal _ _ _ _ (by decide) places240 good raw s domain g sg input record i
    have now:=congrArg (fun a=>StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (shape 11) 0 15 (mappedBasis 11 out.basis)) i.val =
      StairArchiveRaw.read (readCells (shape 11) 0 15 (mappedBasis 11 s.basis)) i.val at now
    rw [read_cells _ _ _ _ _ i.isLt,read_cells _ _ _ _ _ i.isLt,Nat.zero_add] at now
    have eq:=now.trans old
    change (out.basis (windowNet 11 (ports (shape 11) i.val).a0),out.basis (windowNet 11 (ports (shape 11) i.val).history)) =
      (o.basis (windowNet 11 (ports (shape 11) i.val).a0),o.basis (windowNet 11 (ports (shape 11) i.val).history)) at eq
    rw [(geo i).1,(geo i).2] at eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  have previous : out.basis 255=o.basis 255 := by
    rw [show o.basis 255=s.basis 255 from inside _ _ _ _ (by decide +kernel)]
    have stable : LeaveSelector.parityAt 255 leave240=some false := by decide +kernel
    simpa [out] using polarity _ _ _ stable s m
  let gs:=(List.finRange 15).map (fun i=>256+i.val)
  let ss:=(List.finRange 15).map (fun i=>Leave240Hit.swaps i.val)
  intro q residual
  by_cases prev:q=255
  · subst q;exact previous
  by_cases gg:q∈gs
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp gg;exact (agree i).1
  by_cases sw:q∈ss
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp sw;exact (agree i).2
  have census : ∀a:Fin 1813,Leave240AssembleCut.leftovers a.val → a.val≠255 → a.val∉gs → a.val∉ss →
      False := by
    unfold Leave240AssembleCut.leftovers; dsimp only [gs,ss];decide +kernel
  have bound:q<1813:=by unfold Leave240AssembleCut.leftovers at residual;simp only [Wire] at *;omega
  exact False.elim (census ⟨q,bound⟩ residual prev gg sw)
end ECDSAAdd.Entrant.StairPacket.Leave240FrameHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
structure Numeric (z:SkywalkNat.State):Prop where
  small:min z.u z.v<2^129
  odd:z.v%2=1
  room:Shadow.high 129 15 z+1<2^112
  nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121
  bound:Leave255TrueMiddle.F z<2^127

theorem actualNumbers (x p:Nat) (hp0:0<p) (odd:p%2=1) (hx:x<2^256) (hp:p<2^256):
    Numeric (SkywalkNat.step^[255] (SkywalkNat.init x p)):=by
  let z:=SkywalkNat.step^[255] (SkywalkNat.init x p)
  have env:z.u+z.v≤2^256+2^255:=LeaveBankEnvelope.after_first x p (2^256) hx.le hp.le 254
  have short:=true_small x p 270 hx hp (by decide)
  have it:SkywalkNat.step^[15] z=SkywalkNat.step^[270] (SkywalkNat.init x p):=by
    exact (Function.iterate_add_apply SkywalkNat.step 15 255 _).symm
  refine ⟨true_small x p 255 hx hp (by decide),(SkywalkNat.iter_valid 255 (SkywalkNat.init x p) hp0 odd).2.1,
    (LeaveBankEnvelope.bounds z env).2.2,?_,(LeaveBankEnvelope.outputs z (by omega) 15).2.2⟩
  rw [it];exact short

def flags (z:SkywalkNat.State) (g0 s0:Bool):Bool×Bool:=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
structure Inputs (s:State) (z:SkywalkNat.State) (g0 s0:Bool):Prop extends Numeric z where
  ready:onRails 12 15 (encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis
  fresh:s.basis 1708=false
  scratch:∀q∈1556::1557::1558::fullC,s.basis q=false
  temp:∀p∈longPairs,s.basis p.2=false
  clean:∀q∈carries,s.basis q=false
  padding:∀t:Nat,112≤t→t<127→s.basis (wire t)=false
  bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0
  zero:∀q∈Leave255FrontReady.watched,s.basis q=false
  far:s.basis 1706=decide (Shadow.far 129 15 z)
  side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u))
  record:readCells (shape 12) 0 15 (mappedBasis 12 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  extra:∀q,1713≤q→q≤1718→s.basis q=false
def spare:List Wire:=[1709, 1710, 1713, 1714, 1715, 1716, 1717, 1718]
private def touch:= (1556::1557::1558::fullC) ++ longPairs.map Prod.snd ++ carries ++ ((List.range' 112 15).map wire) ++ Leave255FrontReady.watched
private theorem geometry:∀q∈touch,(1556≤q ∧ q≤1702) ∨ q∈spare:=by decide +kernel
theorem assemble (s:State) (z:SkywalkNat.State) (g0 s0:Bool) (numbers:Numeric z)
    (rails:onRails 12 15 (SkywalkTrace.next^[15] (encode g0 s0 (Shadow.reduced 129 15 z).u (Shadow.reduced 129 15 z).v)) s.basis)
    (record:readCells (shape 12) 0 15 (mappedBasis 12 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
    (saved:regValue ys s.basis=(if Shadow.far 129 15 z then Shadow.high 129 15 z else 0) ∧
      s.basis 1708=false ∧ s.basis 1706=decide (Shadow.far 129 15 z) ∧ s.basis 1707=decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
    (ex:∀q∈spare,s.basis q=false):Inputs s z g0 s0:=by
  have cl:=carry255 _ s rails
  have all (q:Wire) (hit:q∈touch):s.basis q=false:=by
    rcases geometry q hit with h|h
    · exact cl q h.1 h.2
    · exact ex q h
  refine ⟨numbers,?_,saved.2.1,?_,?_,?_,?_,saved.1,?_,saved.2.2.1,?_,record,?_⟩
  · exact (SharedSigned.same _ z numbers.small numbers.odd g0 s0).1 ▸ rails
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · intro t h;apply all;have mem:=List.mem_map_of_mem (f:=Prod.snd) h;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inr mem)))
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inr h))
  · intro t lo hi
    have hit:t∈List.range' 112 15:=List.mem_range'_1.mpr ⟨lo,hi⟩
    apply all
    have mem:=List.mem_map_of_mem (f:=wire) hit
    simp only [touch,List.mem_append];exact Or.inl (Or.inr mem)
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inr h
  · rw [saved.2.2.2]
    by_cases f:Shadow.far 129 15 z <;> simp [f]
  · intro q lo hi
    apply ex
    have inc:∀q∈List.range' 1713 6,q∈spare:=by decide
    exact inc q (List.mem_range'_1.mpr ⟨lo,Nat.lt_succ_of_le hi⟩)
end ECDSAAdd.Entrant.StairPacket.Leave255Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

theorem result (x p : Nat) (good:Bounds x p) (raw s:State) (m:List Bool) (g sg:Bool)
    (domain:Domain 255 x p raw)
    (input:InputAt 255 (encode g sg (unsigned 255 x p).u (unsigned 255 x p).v) raw)
    (record:physicalCells 12 s=SkywalkTrace.trace 15 (encode g sg (unsigned 255 x p).u (unsigned 255 x p).v))
    (kept:physicalCells 12 (run leave255 m s)=physicalCells 12 s)
    (extra:∀q:Wire,q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1313) → (run leave255 m s).basis q=(origin 255 raw s).basis q) :
    ∀q,Leave255AssembleCut.leftovers q → (run leave255 m s).basis q=(origin 255 raw s).basis q := by
  let out:=run leave255 m s
  let o:=origin 255 raw s
  have geo : ∀i:Fin 15,windowNet 12 (ports (shape 12) i.val).a0=271+i.val ∧
      windowNet 12 (ports (shape 12) i.val).history=Leave255Hit.swaps i.val := by decide +kernel
  have agree (i:Fin 15) : out.basis (271+i.val)=o.basis (271+i.val) ∧
      out.basis (Leave255Hit.swaps i.val)=o.basis (Leave255Hit.swaps i.val) := by
    have old:=recorded_equal _ _ _ _ (by decide) places255 good raw s domain g sg input record i
    have now:=congrArg (fun a=>StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (shape 12) 0 15 (mappedBasis 12 out.basis)) i.val =
      StairArchiveRaw.read (readCells (shape 12) 0 15 (mappedBasis 12 s.basis)) i.val at now
    rw [read_cells _ _ _ _ _ i.isLt,read_cells _ _ _ _ _ i.isLt,Nat.zero_add] at now
    have eq:=now.trans old
    change (out.basis (windowNet 12 (ports (shape 12) i.val).a0),out.basis (windowNet 12 (ports (shape 12) i.val).history)) =
      (o.basis (windowNet 12 (ports (shape 12) i.val).a0),o.basis (windowNet 12 (ports (shape 12) i.val).history)) at eq
    rw [(geo i).1,(geo i).2] at eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  have previous : out.basis 270=o.basis 270 := by
    rw [show o.basis 270=s.basis 270 from inside _ _ _ _ (by decide +kernel)]
    have stable : LeaveSelector.parityAt 270 leave255=some false := by decide +kernel
    simpa [out] using polarity _ _ _ stable s m
  let gs:=(List.finRange 15).map (fun i=>271+i.val)
  let ss:=(List.finRange 15).map (fun i=>Leave255Hit.swaps i.val)
  intro q residual
  by_cases prev:q=270
  · subst q;exact previous
  by_cases gg:q∈gs
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp gg;exact (agree i).1
  by_cases sw:q∈ss
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp sw;exact (agree i).2
  have census : ∀a:Fin 1813,Leave255AssembleCut.leftovers a.val → a.val≠270 → a.val∉gs → a.val∉ss →
      Leave255ReleasedOrigin.releasedSite a.val := by
    unfold Leave255AssembleCut.leftovers; dsimp only [gs,ss];set_option synthInstance.maxSize 4096 in decide +kernel
  have bound:q<1813:=by unfold Leave255AssembleCut.leftovers at residual;simp only [Wire] at *;omega
  exact extra q (census ⟨q,bound⟩ residual prev gg sw)
end ECDSAAdd.Entrant.StairPacket.Leave255FrameHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
theorem Inputs.roundtrip {s:State} {z:SkywalkNat.State} {g0 s0:Bool} (h:Inputs s z g0 s0) (m n:List Bool):
    run leave225Inv n (run leave225 m s)=s:=by
  let u:=flags z g0 s0
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave225RecordedParity.result s z g0 s0 h.small h.odd h.record
  have mode : actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave225RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have ph (o:List Bool) : (run leave225 o s).phase=s.phase:=by
    exact (Leave225Whole.result s o z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side).1
  exact Leave225Roundtrip.result s m n z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound ph (carry225 _ s h.ready)
end ECDSAAdd.Entrant.StairPacket.Leave225Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

theorem result (x p : Nat) (good:Bounds x p) (raw s : State) (m:List Bool) (g0 s0:Bool)
    (dom:Domain 225 x p raw)
    (input:InputAt 225 (encode g0 s0 (unsigned 225 x p).u (unsigned 225 x p).v) raw)
    (h:Leave225Admission.Inputs s (unsigned 225 x p) g0 s0)
    (phase:s.phase=(origin 225 raw s).phase)
    (ext:∀q,Exterior 225 512 q → s.basis q=(origin 225 raw s).basis q)
    (upper:∀q:Nat,419≤q → q≤512 → s.basis q=false)
    (quiet:∀q∈Leave225CoreCheckpoint.rawSites,s.basis q=false)
     :
    let z:=unsigned 225 x p
    let flags:=Leave225Admission.flags z g0 s0
    let a:=unsigned 240 x p
    let out:=run leave225 m s
    PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 136 15 a)) (decide (Shadow.far 136 15 a ∧ 2^136≤a.u))
      (pullState (OB5.sig 239) (endRaw 225 raw s)) (eraseSites Enter240.pending out) := by
  let z:=unsigned 225 x p
  let flags:=Leave225Admission.flags z g0 s0
  let a:=SkywalkNat.step^[15] z
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have endpointState : a=unsigned 240 x p := (Function.iterate_add_apply SkywalkNat.step 15 225 _).symm
  have signed:= (advance_signed 225 144 x p (by decide) (by decide) fixed225 good raw s dom g0 s0 input h.small).2
  have nextInput : SkywalkIntegerInput Leave225WideWords.L (encode flags.1 flags.2 a.u a.v).a
      (encode flags.1 flags.2 a.u a.v).b flags.1 (endRaw 225 raw s).basis := by
    rw [endpointState]
    change SkywalkIntegerInput _ (encode flags.1 flags.2 _ _).a (encode flags.1 flags.2 _ _).b (encode flags.1 flags.2 _ _).g _ at signed
    simpa only [flagEq] using signed
  have par:=Leave225RecordedParity.result s z g0 s0 h.small h.odd h.record
  have md : actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave225RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have bits:=Leave225EndWords.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have whole:=Leave225Whole.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have kept:=Leave225PreservedRecords.result s m bits.2.2.2.1
  have left:=Leave225FrameHistory.result x p good raw s m g0 s0 dom input h.record kept
  have rails:=Leave225BoundaryRails.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side upper (endRaw _ raw s) nextInput
  have clear:=Leave225BoundaryClean.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet
  dsimp only
  rw [←endpointState,endpoint 225 (by decide)]
  rw [endpoint 225 (by decide)] at rails
  apply Leave225AssembleCut.result _ _ _ _ _ (whole.1.trans phase) bits.2.2.1 bits.1
  · exact bits.2.1.trans (both _ _)
  · exact rails.1
  · exact rails.2
  · exact fun q hq=>(NativePack225.exterior s m q hq).trans (ext q hq)
  · exact left
  · exact clear
  · exact carry_origin (by decide) (by decide) good raw s dom same_c225
end ECDSAAdd.Entrant.StairPacket.Leave225CertifiedCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
theorem Inputs.roundtrip {s:State} {z:SkywalkNat.State} {g0 s0:Bool} (h:Inputs s z g0 s0) (m n:List Bool):
    run leave240Inv n (run leave240 m s)=s:=by
  let u:=flags z g0 s0
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave240RecordedParity.result s z g0 s0 h.small h.odd h.record
  have mode : actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave240RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have ph (o:List Bool) : (run leave240 o s).phase=s.phase:=by
    exact (Leave240Whole.result s o z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side).1
  exact Leave240Roundtrip.result s m n z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound ph (carry240 _ s h.ready)
end ECDSAAdd.Entrant.StairPacket.Leave240Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

theorem result (x p : Nat) (good:Bounds x p) (raw s : State) (m:List Bool) (g0 s0:Bool)
    (dom:Domain 240 x p raw)
    (input:InputAt 240 (encode g0 s0 (unsigned 240 x p).u (unsigned 240 x p).v) raw)
    (h:Leave240Admission.Inputs s (unsigned 240 x p) g0 s0)
    (phase:s.phase=(origin 240 raw s).phase)
    (ext:∀q,Exterior 240 527 q → s.basis q=(origin 240 raw s).basis q)
    (upper:∀q:Nat,426≤q → q≤527 → s.basis q=false)
    (quiet:∀q∈Leave240CoreCheckpoint.rawSites,s.basis q=false)
     :
    let z:=unsigned 240 x p
    let flags:=Leave240Admission.flags z g0 s0
    let a:=unsigned 255 x p
    let out:=run leave240 m s
    PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 129 15 a)) (decide (Shadow.far 129 15 a ∧ 2^129≤a.u))
      (pullState (OB5.sig 254) (endRaw 240 raw s)) (eraseSites Enter255.pending out) := by
  let z:=unsigned 240 x p
  let flags:=Leave240Admission.flags z g0 s0
  let a:=SkywalkNat.step^[15] z
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have endpointState : a=unsigned 255 x p := (Function.iterate_add_apply SkywalkNat.step 15 240 _).symm
  have signed:= (advance_signed 240 136 x p (by decide) (by decide) fixed240 good raw s dom g0 s0 input h.small).2
  have nextInput : SkywalkIntegerInput Leave240WideWords.L (encode flags.1 flags.2 a.u a.v).a
      (encode flags.1 flags.2 a.u a.v).b flags.1 (endRaw 240 raw s).basis := by
    rw [endpointState]
    change SkywalkIntegerInput _ (encode flags.1 flags.2 _ _).a (encode flags.1 flags.2 _ _).b (encode flags.1 flags.2 _ _).g _ at signed
    simpa only [flagEq] using signed
  have par:=Leave240RecordedParity.result s z g0 s0 h.small h.odd h.record
  have md : actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave240RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have bits:=Leave240EndWords.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have whole:=Leave240Whole.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have kept:=Leave240PreservedRecords.result s m bits.2.2.2.1
  have left:=Leave240FrameHistory.result x p good raw s m g0 s0 dom input h.record kept
  have rails:=Leave240BoundaryRails.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side upper (endRaw _ raw s) nextInput
  have clear:=Leave240BoundaryClean.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet
  dsimp only
  rw [←endpointState,endpoint 240 (by decide)]
  rw [endpoint 240 (by decide)] at rails
  apply Leave240AssembleCut.result _ _ _ _ _ (whole.1.trans phase) bits.2.2.1 bits.1
  · exact bits.2.1.trans (both _ _)
  · exact rails.1
  · exact rails.2
  · exact fun q hq=>(NativePack240.exterior s m q hq).trans (ext q hq)
  · exact left
  · exact clear
  · exact carry_origin (by decide) (by decide) good raw s dom same_c240
end ECDSAAdd.Entrant.StairPacket.Leave240CertifiedCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
theorem Inputs.roundtrip {s:State} {z:SkywalkNat.State} {g0 s0:Bool} (h:Inputs s z g0 s0) (m n:List Bool):
    run leave255Inv n (run leave255 m s)=s:=by
  let u:=flags z g0 s0
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave255RecordedParity.result s z g0 s0 h.small h.odd h.record
  have mode : actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave255RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have ph (o:List Bool) : (run leave255 o s).phase=s.phase:=by
    exact (Leave255Whole.result s o z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side).1
  exact Leave255Roundtrip.result s m n z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound ph (carry255 _ s h.ready) h.extra
end ECDSAAdd.Entrant.StairPacket.Leave255Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

theorem result (x p : Nat) (good:Bounds x p) (raw s : State) (m:List Bool) (g0 s0:Bool)
    (dom:Domain 255 x p raw)
    (input:InputAt 255 (encode g0 s0 (unsigned 255 x p).u (unsigned 255 x p).v) raw)
    (h:Leave255Admission.Inputs s (unsigned 255 x p) g0 s0)
    (phase:s.phase=(origin 255 raw s).phase)
    (ext:∀q,Exterior 255 529 q → s.basis q=(origin 255 raw s).basis q)
    (upper:∀q:Nat,434≤q → q≤529 → s.basis q=false)
    (quiet:∀q∈Leave255CoreCheckpoint.rawSites,s.basis q=false)
    (extra:∀q:Wire,Leave255ReleasedOrigin.releasedSite q → (run leave255 m s).basis q=(origin 255 raw s).basis q) :
    let z:=unsigned 255 x p
    let flags:=Leave255Admission.flags z g0 s0
    let a:=unsigned 270 x p
    let out:=run leave255 m s
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 121 15 a)) (decide (Shadow.far 121 15 a ∧ 2^121≤a.u))
      (pullState (OB5.sig 269) (endRaw 255 raw s)) (eraseSites ParkEndpoint.src out) := by
  let z:=unsigned 255 x p
  let flags:=Leave255Admission.flags z g0 s0
  let a:=SkywalkNat.step^[15] z
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have endpointState : a=unsigned 270 x p := (Function.iterate_add_apply SkywalkNat.step 15 255 _).symm
  have signed:= (advance_signed 255 129 x p (by decide) (by decide) fixed255 good raw s dom g0 s0 input h.small).2
  have nextInput : SkywalkIntegerInput Leave255WideWords.L (encode flags.1 flags.2 a.u a.v).a
      (encode flags.1 flags.2 a.u a.v).b flags.1 (endRaw 255 raw s).basis := by
    rw [endpointState]
    change SkywalkIntegerInput _ (encode flags.1 flags.2 _ _).a (encode flags.1 flags.2 _ _).b (encode flags.1 flags.2 _ _).g _ at signed
    simpa only [flagEq] using signed
  have par:=Leave255RecordedParity.result s z g0 s0 h.small h.odd h.record
  have md : actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave255RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have bits:=Leave255EndWords.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have whole:=Leave255Whole.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have kept:=Leave255PreservedRecords.result s m bits.2.2.2.1
  have left:=Leave255FrameHistory.result x p good raw s m g0 s0 dom input h.record kept extra
  have rails:=Leave255BoundaryRails.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side (fun q lo hi=>upper q lo (Nat.le_trans hi (by decide))) (endRaw _ raw s) nextInput
  have clear:=Leave255BoundaryClean.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet (LeaveTerminalBound.fit x p good.nonzero good.positive good.odd good.cap good.small good.coprime)
  dsimp only
  rw [←endpointState,endpoint 255 (by decide)]
  rw [endpoint 255 (by decide)] at rails
  apply Leave255AssembleCut.result _ _ _ _ _ (whole.1.trans phase) bits.2.2.1 bits.1
  · exact bits.2.1.trans (both _ _)
  · exact rails.1
  · exact rails.2
  · exact fun q hq=>(NativePack255.exterior s m q hq).trans (ext q hq)
  · exact left
  · exact clear
  · exact carry_origin (by decide) (by decide) good raw s dom same_c255
end ECDSAAdd.Entrant.StairPacket.Leave255CertifiedCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run body measurementCount onRails
theorem admitted_with_input (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d seed p 225 raw.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 224) raw
    let out:=run (firstWindow d) m origin
    ∃g0 s0:Bool,SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (encode g0 s0 z.u z.v).a (encode g0 s0 z.u z.v).b g0 raw.basis ∧ Leave225Admission.Inputs out z g0 s0:=by
  let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
  let origin:=pullState (OB5.sig 224) raw
  let cut:=run Partial.portal225 m origin
  let n:=m.drop (measurementCount Partial.portal225)
  let pre:=run Partial.enter225 n cut
  let tape:=n.drop (measurementCount Partial.enter225)
  let T:=Shadow.reduced 144 15 z
  have small:min z.u z.v<2^144:=true_small seed p 225 (by omega) hp (by decide)
  obtain ⟨G,S,input⟩:=PortalValues.real_input d seed p 225 hp0 hx0 hpo hp hq hx hc (by decide) raw stage
  have pcut:=Portal225Flag.physical_frame_for d seed p hp0 hx0 hpo hp hq hx hc raw m stage G S input
  have same:Shadow.far 144 15 z=(3*2^160≤z.u+z.v):=by
    apply propext
    unfold Shadow.far Shadow.high Shadow.limb
    exact Nat.le_div_iff_mul_le (by positivity)
  have normalized:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 (PortalValues.negative S z.u)
      (decide (Shadow.far 144 15 z)) (decide (Shadow.far 144 15 z ∧ 2^144≤z.u)) origin cut:=by
    simpa only [same] using pcut
  have numbers:=Leave225Admission.actualNumbers seed p hp0 hpo (lt_trans hx hp) hp
  have values:=saved_at_leave d raw cut z G S n (n.drop (measurementCount Partial.enter225)) small normalized input
  have more:=extra_clean d raw cut n (n.drop (measurementCount Partial.enter225)) _ _ _ _ _ _ normalized input
  have ready:=Enter225.ready_from_cut raw cut z G S n small normalized input
    (fun r=>by simpa only [Nat.add_assoc] using stock_history d seed p 225 raw stage (225+r) (by omega) (by have hr:=r.isLt;omega))
  have zo:z.v%2=1:=(SkywalkNat.iter_valid 225 (SkywalkNat.init seed p) hp0 hpo).2.1
  have to':T.v%2=1:=shadow_odd 144 z small zo
  have parity:((encode G S T.u T.v).a+(encode G S T.u T.v).b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have initial:=original_legal d seed p hp0 hpo raw stage
  have legal:=legal_congr (history_from_stock raw cut pre pcut n tape rfl _ parity ready.2) initial
  have whole:=window_run d pre tape _ parity ready.2 legal
  refine ⟨G,S,input,Leave225Admission.assemble _ _ _ _ numbers ?_ ?_ ?_ ?_⟩
  · simpa only [firstWindow,run_append,run_take,origin,n,pre,tape,cut] using whole.2.1
  · simpa only [firstWindow,run_append,run_take,origin,n,pre,tape,cut] using whole.2.2.1.trans (true_records 144 z small zo G S)
  · simpa only [firstWindow,window,run_append,run_take,origin,cut,n] using values
  · intro q h
    have inc:∀q∈Leave225Admission.spare,q∈spares:=by decide
    simpa only [firstWindow,window,run_append,run_take,origin,cut,n] using more q (inc q h)
theorem admitted (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d seed p 225 raw.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 224) raw
    let out:=run (firstWindow d) m origin
    ∃g0 s0:Bool,Leave225Admission.Inputs out z g0 s0:=by
  obtain ⟨g,sg,_,facts⟩:=admitted_with_input d seed p hp0 hx0 hpo hp hq hx hc raw m stage
  exact ⟨g,sg,facts⟩
end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run body measurementCount onRails
open ArchiveBoundary240
theorem admitted (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (numbers:Leave240Admission.Numeric z)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave240Admission.Inputs out z G S:=by
  let tape:=m.drop (measurementCount Partial.enter240)
  have saved:=saved_with_pending d raw s z G S m tape numbers.small cut input
  have all:=next_window d raw s m z G S numbers.odd numbers.small cut input hist past pg ps cross po pm prior
  obtain ⟨_,_,_,tags⟩:=real_receipt d raw s m z G S numbers.odd numbers.small cut input hist past pg ps cross po pm prior
  apply Leave240Admission.assemble _ _ _ _ numbers all.2.1 all.2.2.1
  · simpa only [nextWindow,window,run_append,run_take,tape] using saved
  · intro q h
    have inc:∀q∈Leave240Admission.spare,∃t:Fin 3,q=1716+t.val:=by decide
    obtain ⟨t,rfl⟩:=inc q h
    exact tags t
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run body measurementCount onRails
open ArchiveBoundary255
theorem admitted (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (numbers:Leave255Admission.Numeric z)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave255Admission.Inputs out z G S:=by
  let tape:=m.drop (measurementCount Partial.enter255)
  have saved:=saved_with_pending d raw s z G S m tape numbers.small cut input
  have all:=next_window d raw s m z G S numbers.odd numbers.small cut input hist endScratch past pg ps cross po pm prior
  obtain ⟨_,_,_,tags⟩:=real_receipt d raw s m z G S numbers.odd numbers.small cut input hist endScratch past pg ps cross po pm prior
  apply Leave255Admission.assemble _ _ _ _ numbers all.2.1 all.2.2.1
  · simpa only [nextWindow,window,run_append,run_take,tape] using saved
  · intro q h
    have inc:∀q∈Leave255Admission.spare,(∃t:Fin 3,q=1709+t.val) ∨ q∈spares:=by decide
    rcases inc q h with ⟨t,rfl⟩|hm
    · exact tags t
    · have ex:=extra_clean d raw s m tape _ _ _ _ _ _ cut input q hm
      simpa only [nextWindow,window,run_append,run_take,tape] using ex
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
theorem result (s:State) (m:List Bool) (z:SkywalkNat.State) (g sg:Bool)
    (h:Leave225Admission.Inputs s z g sg) :
    let out:=run leave225 m s
    PastFacts 10 ArchiveBoundary240.rawPorts 144 z g sg (HighBankSum.cross (Leave225TrueMiddle.d z)) out := by
  let flags:=Leave225Admission.flags z g sg
  have all:=Leave225ActualHistory.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero h.nextSmall h.bound h.far h.side g sg h.record
  exact ⟨all.1,all.2.1,all.2.2.1,all.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave225ArchiveCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
theorem result (s:State) (m:List Bool) (z:SkywalkNat.State) (g sg:Bool)
    (h:Leave240Admission.Inputs s z g sg) :
    let out:=run leave240 m s
    PastFacts 11 ArchiveBoundary255.rawPorts 136 z g sg (HighBankSum.cross (Leave240TrueMiddle.d z)) out := by
  let flags:=Leave240Admission.flags z g sg
  have all:=Leave240ActualHistory.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero h.nextSmall h.bound h.far h.side g sg h.record
  exact ⟨all.1,all.2.1,all.2.2.1,all.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave240ArchiveCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
theorem result (s:State) (m:List Bool) (z:SkywalkNat.State) (g sg:Bool)
    (h:Leave255Admission.Inputs s z g sg) :
    let out:=run leave255 m s
    physicalCells 12 out=SkywalkTrace.trace 15 (encode g sg z.u z.v) ∧
      out.basis 1701=decide (Shadow.far 129 15 z) ∧
      out.basis 1702=(decide (Shadow.far 129 15 z) && StairArchiveTrace.afterFlags (decide (z.v<z.u)) ((physicalCells 12 out).take 5)) ∧
      out.basis 1703=(decide (Shadow.far 129 15 z) && HighBankSum.cross (Leave255TrueMiddle.d z)) := by
  let flags:=Leave255Admission.flags z g sg
  have all:=Leave255ActualHistory.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero h.nextSmall h.bound h.far h.side g sg h.record
  exact all
end ECDSAAdd.Entrant.StairPacket.Leave255ArchiveCut

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference
attribute [local irreducible] run SkywalkNat.step onRails
namespace NativePack240
open ArchiveBoundary240
theorem from_domain (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m:List Bool)
    (domain:Domain 240 x p raw) (G S:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S (unsigned 240 x p).u)
      (decide (Shadow.far 136 15 (unsigned 240 x p))) (decide (Shadow.far 136 15 (unsigned 240 x p) ∧ 2^136≤(unsigned 240 x p).u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).a (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 144 (unsigned 225 x p) pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave240Admission.Inputs out (unsigned 240 x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,Kept codePorts d row out) ∧ ∀n,run (nextUnwind d) n out=s:=by
  let z:=unsigned 240 x p
  let prev:=unsigned 225 x p
  have nums:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave225Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have a:=next_window d raw s m z G S nums.odd nums.small cut input hist prev pg ps cross old.odd old.small prior
  obtain ⟨row,limit,code,_⟩:=real_receipt d raw s m z G S nums.odd nums.small cut input hist prev pg ps cross old.odd old.small prior
  exact ⟨admitted d raw s m z G S nums cut input hist prev pg ps cross old.odd old.small prior,a.1,⟨row,limit,code⟩,a.2.2.2⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem from_domain (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m:List Bool)
    (domain:Domain 255 x p raw) (G S:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S (unsigned 255 x p).u)
      (decide (Shadow.far 129 15 (unsigned 255 x p))) (decide (Shadow.far 129 15 (unsigned 255 x p) ∧ 2^129≤(unsigned 255 x p).u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).a (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 136 (unsigned 240 x p) pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave255Admission.Inputs out (unsigned 255 x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,Kept codePorts d row out) ∧ ∀n,run (nextUnwind d) n out=s:=by
  let z:=unsigned 255 x p
  let prev:=unsigned 240 x p
  have nums:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have clear:=WideReference.carry (by decide) domain
  have a:=next_window d raw s m z G S nums.odd nums.small cut input hist clear prev pg ps cross old.odd old.small prior
  obtain ⟨row,limit,code,_⟩:=real_receipt d raw s m z G S nums.odd nums.small cut input hist clear prev pg ps cross old.odd old.small prior
  exact ⟨admitted d raw s m z G S nums cut input hist clear prev pg ps cross old.odd old.small prior,a.1,⟨row,limit,code⟩,a.2.2.2⟩
end NativePack255
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference
attribute [local irreducible] run SkywalkNat.step onRails
namespace NativePack240
open ArchiveBoundary240
theorem from_domain_matched (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m:List Bool)
    (domain:Domain 240 x p raw) (G S:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S (unsigned 240 x p).u)
      (decide (Shadow.far 136 15 (unsigned 240 x p))) (decide (Shadow.far 136 15 (unsigned 240 x p) ∧ 2^136≤(unsigned 240 x p).u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).a (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 144 (unsigned 225 x p) pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave240Admission.Inputs out (unsigned 240 x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,RowTruth (unsigned 225 x p) pg ps row ∧ Kept codePorts d row out) ∧ ∀n,run (nextUnwind d) n out=s:=by
  let z:=unsigned 240 x p
  let prev:=unsigned 225 x p
  have nums:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave225Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have a:=next_window d raw s m z G S nums.odd nums.small cut input hist prev pg ps cross old.odd old.small prior
  obtain ⟨row,limit,truth,code,_⟩:=matched_receipt d raw s m z G S nums.odd nums.small cut input hist prev pg ps cross old.odd old.small prior
  exact ⟨admitted d raw s m z G S nums cut input hist prev pg ps cross old.odd old.small prior,a.1,⟨row,limit,truth,code⟩,a.2.2.2⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem from_domain_matched (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m:List Bool)
    (domain:Domain 255 x p raw) (G S:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S (unsigned 255 x p).u)
      (decide (Shadow.far 129 15 (unsigned 255 x p))) (decide (Shadow.far 129 15 (unsigned 255 x p) ∧ 2^129≤(unsigned 255 x p).u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).a (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 136 (unsigned 240 x p) pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave255Admission.Inputs out (unsigned 255 x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,RowTruth (unsigned 240 x p) pg ps row ∧ Kept codePorts d row out) ∧ ∀n,run (nextUnwind d) n out=s:=by
  let z:=unsigned 255 x p
  let prev:=unsigned 240 x p
  have nums:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have clear:=WideReference.carry (by decide) domain
  have a:=next_window d raw s m z G S nums.odd nums.small cut input hist clear prev pg ps cross old.odd old.small prior
  obtain ⟨row,limit,truth,code,_⟩:=matched_receipt d raw s m z G S nums.odd nums.small cut input hist clear prev pg ps cross old.odd old.small prior
  exact ⟨admitted d raw s m z G S nums cut input hist clear prev pg ps cross old.odd old.small prior,a.1,⟨row,limit,truth,code⟩,a.2.2.2⟩
end NativePack255
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockRows
open Arithmetic IntegerPacket SkywalkRails WideReference StairArchiveRaw StairArchiveTrace CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 16000

def Chronology (i x p row:Nat) : Prop :=
  ∀q:Fin 20,(rawCol q).testBit row=letterBit (read ((SkywalkTrace.trace 15 (WideReference.canonical i x p)).drop 5) (q.val/2)) q

theorem chronology (i x p row:Nat) (less:i<512) (good:Bounds x p) (raw:State) (domain:Domain i x p raw) (g sg:Bool)
    (input:InputAt i (encode g sg (unsigned i x p).u (unsigned i x p).v) raw)
    (truth:RowTruth (unsigned i x p) g sg row) : Chronology i x p row := by
  have same:=unique_input input (fixed_input i x p less good raw domain)
  unfold Chronology
  rw [←same]
  exact truth

structure Final (d:Bool) (x p:Nat) (out:State) : Prop where
  first : ∃row<63145,Chronology 225 x p row ∧ Kept ArchiveBoundary240.codePorts d row out
  middle : ∃row<63145,Chronology 240 x p row ∧ Kept ArchiveBoundary255.codePorts d row out
  last : ∃row<63145,Chronology 255 x p row ∧ Frame ArchiveBoundary270.codePorts (code d) row out

end ECDSAAdd.Entrant.StairPacket.ArchiveStockRows

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffix
open Arithmetic MappedCompressed
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
def logical (sw:Bool) (r:Nat):Wire:=if sw then base (1028+r) else base r
def site (sw:Bool) (r:Nat):Wire:=OB5.sig 270 (logical sw r)
theorem stable (i:Nat) (lo:270 ≤ i) (hi:i ≤ 511) (r:Nat) (old:r < 270) (sw:Bool):
    OB5.sig i (logical sw r)=site sw r:=by
  cases sw <;> simp only [logical,Bool.false_eq_true,if_false,if_true,site,
    StairField2V3JuncRefWalk.sig_base i hi,StairField2V3JuncRefWalk.sig_base 270 (by decide)]
  all_goals split_ifs <;> first | rfl | omega
private theorem no_pack (i:Nat) (lo:271 ≤ i) (hi:i < 512) (r:Nat) (old:r < 270) (d sw:Bool):
    logical sw r∉wires (Rolling1588.Integer.packFirst base d i) ∧
    logical sw r∉wires (Rolling1588.unpackAtTick d i):=by
  by_cases early:i < 275
  · have mem:i∈[271,272,273,274]:=by simp;omega
    have none:∀k∈[271,272,273,274],Rolling1588.Integer.packFirst base d k=[] ∧ Rolling1588.unpackAtTick d k=[]:=by
      cases d <;> decide +kernel
    rw [(none i mem).1,(none i mem).2];simp [wires]
  · have disjoint (j:Fin 10):logical sw r≠History5.historyMap base (i-5) j:=by
      have lim:=j.isLt
      cases sw <;> simp only [logical,Bool.false_eq_true,if_false,if_true,History5.historyMap,History5.historyId,base,Wire]
      all_goals split_ifs <;> omega
    constructor
    · intro h
      rw [Rolling1588.Integer.packFirst,if_neg (show i≠5 by omega),Rolling1588.Integer.pack_support_eq] at h
      unfold History5.packAfter at h
      split at h
      · obtain ⟨j,e⟩:=History5.history_gate_mem base (i-5) _ (Or.inl rfl) _ h
        exact disjoint j e
      · simp [wires] at h
    · intro h
      rw [←Rolling1588.Integer.unpackFirst_base,Rolling1588.Integer.unpackFirst,if_neg (show i≠5 by omega),
        Rolling1588.Integer.decodeBefore_support_eq] at h
      unfold History5.decodeBefore at h
      split at h
      · obtain ⟨j,e⟩:=History5.history_gate_mem base (i-5) _ (Or.inr rfl) _ h
        exact disjoint j e
      · simp [wires] at h
private theorem one (d sw:Bool) (r i:Nat) (old:r < 270) (lo:271 ≤ i) (hi:i < 512):
    site sw r∉wires (renameProgram (OB5.sig i) (TickRanges.tick base i ++ Rolling1588.Integer.packFirst base d i)) ∧
    site sw r∉wires (renameProgram (OB5.sig i) (Rolling1588.unpackAtTick d i ++ W.ReverseCarry.compactReceiverTick base i)):=by
  have past:WideReference.Earlier i (logical sw r):=⟨r,by omega,by cases sw <;> simp [logical]⟩
  have off:=WideReference.away hi past
  have pack:=no_pack i lo hi r old d sw
  have pre (q:Wire) (eq:OB5.sig i q=site sw r):q=logical sw r:=by
    rw [←stable i (by omega) (by omega) r old sw] at eq
    have inj:Function.Injective (OB5.sig i):=(OB5.sig_injective i (by omega))
    exact inj eq
  constructor <;> intro h <;> rw [renameProgram_support] at h <;>
    obtain ⟨q,mem,eq⟩:=Finset.mem_image.mp h <;> rw [pre q eq,wires_append,Finset.mem_union] at mem
  · rcases mem with tick|packet
    · exact off (List.mem_toFinset.mp (W.repairedTick_support base i hi base_pool_nodup (TickRanges.tick_support base i hi base_pool_nodup tick)))
    · exact pack.1 packet
  · rcases mem with packet|tick
    · exact pack.2 packet
    · exact off (List.mem_toFinset.mp (W.ReverseCarry.compactReceiverTick_support base i hi base_pool_nodup tick))
theorem suffix (d sw:Bool) (r i n:Nat) (old:r < 270) (lo:271 ≤ i) (hi:i+n≤512):
    site sw r∉wires (Rolling1588TickGap.forward d i n) ∧ site sw r∉wires (Rolling1588.reverse d i n):=by
  induction n generalizing i with
  | zero=>simp [Rolling1588TickGap.forward,Rolling1588.reverse,wires]
  | succ n ih=>
    have a:=one d sw r i old lo (by omega)
    have b:=ih (i+1) (by omega) (by omega)
    simp only [Rolling1588TickGap.forward,Rolling1588.reverse,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨a.1,b.1⟩,⟨b.2,a.2⟩⟩
def offset (j:Fin 16):Nat:=5*(j.val/8)+[0,0,1,1,2,3,3,4].getD (j.val%8) 0
def swap (j:Fin 16):Bool:=j.val%8∈[1,3,6]
theorem sites240:∀j:Fin 16,ArchiveBoundary240.codePorts ⟨j,by omega⟩=site (swap j) (230+offset j):=by decide +kernel
theorem old240:∀j:Fin 16,230+offset j<270:=by decide
theorem sites255:∀j:Fin 16,ArchiveBoundary255.codePorts ⟨j,by omega⟩=site (swap j) (245+offset j):=by decide +kernel
theorem old255:∀j:Fin 16,245+offset j<270:=by decide
theorem sites270:∀j:Fin 16,ArchiveBoundary270.codePorts ⟨j,by omega⟩=site (swap j) (260+offset j):=by decide +kernel
theorem old270:∀j:Fin 16,260+offset j<270:=by decide
def bank (n:Nat) (ports:ArchivePortAction.Ports):Finset Wire:=
  ((List.finRange n).map (fun j=>ports (Fin.ofNat 157 j.val))).toFinset
def archives:Finset Wire:=bank 16 ArchiveBoundary240.codePorts ∪ bank 16 ArchiveBoundary255.codePorts ∪ bank 16 ArchiveBoundary270.codePorts
theorem safe (d:Bool) (i n:Nat) (lo:271 ≤ i) (hi:i+n≤512) (q:Wire) (mem:q∈archives):
    q∉wires (Rolling1588TickGap.forward d i n) ∧ q∉wires (Rolling1588.reverse d i n):=by
  simp only [archives,bank,Finset.mem_union,List.mem_toFinset,List.mem_map,List.mem_finRange,true_and] at mem
  rcases mem with (⟨j,rfl⟩|⟨j,rfl⟩)|⟨j,rfl⟩
  · rw [show Fin.ofNat 157 j.val=(⟨j,by omega⟩:Fin 157) from Fin.ext (Nat.mod_eq_of_lt (by omega)),sites240]
    exact suffix d _ _ i n (old240 j) lo hi
  · rw [show Fin.ofNat 157 j.val=(⟨j,by omega⟩:Fin 157) from Fin.ext (Nat.mod_eq_of_lt (by omega)),sites255]
    exact suffix d _ _ i n (old255 j) lo hi
  · rw [show Fin.ofNat 157 j.val=(⟨j,by omega⟩:Fin 157) from Fin.ext (Nat.mod_eq_of_lt (by omega)),sites270]
    exact suffix d _ _ i n (old270 j) lo hi
def Same (a b:State):Prop:=a.phase=b.phase ∧ ∀q∉archives,a.basis q=b.basis q
theorem independent (P:Program) (off:∀q∈archives,q∉wires P)
    (m:List Bool) (s t:State) (same:Same s t):
    Same (run P m s) (run P m t) ∧ ∀q∈archives,(run P m s).basis q=s.basis q:=by
  have eqs:=pool_run_agrees P (wires P) (Finset.Subset.refl _) m s t same.1
    (fun q h=>same.2 q (fun mem=>off q mem h))
  refine ⟨⟨eqs.1,?_⟩,fun q mem=>run_preserves_outside _ m s _ (off q mem)⟩
  intro q ext
  by_cases use:q∈wires P
  · exact eqs.2 q use
  · rw [run_preserves_outside _ m s _ use,run_preserves_outside _ m t _ use]
    exact same.2 q ext
end ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffix

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack225 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step

theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain 225 x p raw)
    (cut:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722
      neg far long (pullState (OB5.sig 224) raw) s)
    (input:InputAt 225 (encode g0 s0 (unsigned 225 x p).u (unsigned 225 x p).v) raw)
    (h:Leave225Admission.Inputs (run (body idx (program d)) b (run enter225 a s)) (unsigned 225 x p) g0 s0)
    (phase:(run (body idx (program d)) b (run enter225 a s)).phase=s.phase) :
    let v:=run (body idx (program d)) b (run enter225 a s)
    let z:=unsigned 225 x p
    let flags:=Leave225Admission.flags z g0 s0
    let z':=unsigned 240 x p
    PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative flags.2 z'.u)
      (decide (Shadow.far 136 15 z')) (decide (Shadow.far 136 15 z' ∧ 2^136≤z'.u))
      (pullState (OB5.sig 239) (endRaw 225 raw v)) (eraseSites Enter240.pending (run leave225 m v)) := by
  let v:=run (body idx (program d)) b (run enter225 a s)
  let z:=unsigned 225 x p
  let flags:=Leave225Admission.flags z g0 s0
  have bank:=carry225 _ v h.ready
  have tail:=tail_clean d raw s a b neg far long _ _ _ cut input (carry (by decide) domain)
  have quiet (q:Wire) (mem:q∈Leave225CoreCheckpoint.rawSites) : v.basis q=false := by
    have layout:∀q∈Leave225CoreCheckpoint.rawSites,(1556≤q ∧ q≤1717) ∨ q∈tailTemps := by decide +kernel
    rcases layout q mem with ⟨lo,hi⟩|endSite
    · exact bank q lo hi
    · exact tail q endSite
  have ph:v.phase=(origin 225 raw v).phase := phase.trans (cut.phase.trans (origin_phase _ _ _ (by decide) good raw v domain).symm)
  have up:=upper_clear d raw s x p domain a b neg far long cut
  have ext:=agree_origin d raw s a b neg far long cut
  exact Leave225CertifiedCut.result x p good raw v m g0 s0 domain input h ph ext up quiet
end ECDSAAdd.Entrant.StairPacket.Leave225BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack240 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step

theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain 240 x p raw)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714
      neg far long (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:InputAt 240 (encode g0 s0 (unsigned 240 x p).u (unsigned 240 x p).v) raw)
    (h:Leave240Admission.Inputs (run (body idx (withArchive d)) b (run enter240 a s)) (unsigned 240 x p) g0 s0)
    (phase:(run (body idx (withArchive d)) b (run enter240 a s)).phase=s.phase)
    (popped:(run (body idx (withArchive d)) b (run enter240 a s)).basis 1718=false) :
    let v:=run (body idx (withArchive d)) b (run enter240 a s)
    let z:=unsigned 240 x p
    let flags:=Leave240Admission.flags z g0 s0
    let z':=unsigned 255 x p
    PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative flags.2 z'.u)
      (decide (Shadow.far 129 15 z')) (decide (Shadow.far 129 15 z' ∧ 2^129≤z'.u))
      (pullState (OB5.sig 254) (endRaw 240 raw v)) (eraseSites Enter255.pending (run leave240 m v)) := by
  let v:=run (body idx (withArchive d)) b (run enter240 a s)
  let z:=unsigned 240 x p
  let flags:=Leave240Admission.flags z g0 s0
  have bank:=carry240 _ v h.ready
  have tail:=tail_clean d raw s a b neg far long _ _ _ cut input (carry (by decide) domain)
  have quiet (q:Wire) (mem:q∈Leave240CoreCheckpoint.rawSites) : v.basis q=false := by
    have layout:∀q∈Leave240CoreCheckpoint.rawSites,(1556≤q ∧ q≤1709) ∨ q=1718 ∨ q∈tailTemps := by decide +kernel
    rcases layout q mem with ⟨lo,hi⟩|rfl|endSite
    · exact bank q lo hi
    · exact popped
    · exact tail q endSite
  have ph:v.phase=(origin 240 raw v).phase := phase.trans (cut.phase.trans (origin_phase _ _ _ (by decide) good raw v domain).symm)
  have up:=upper_clear d raw s x p domain a b neg far long cut
  have ext:=agree_origin d raw s a b neg far long cut
  exact Leave240CertifiedCut.result x p good raw v m g0 s0 domain input h ph ext up quiet
end ECDSAAdd.Entrant.StairPacket.Leave240BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack255 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step

theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain 255 x p raw)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707
      neg far long (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:InputAt 255 (encode g0 s0 (unsigned 255 x p).u (unsigned 255 x p).v) raw)
    (h:Leave255Admission.Inputs (run (body idx (withArchive d)) b (run enter255 a s)) (unsigned 255 x p) g0 s0)
    (phase:(run (body idx (withArchive d)) b (run enter255 a s)).phase=s.phase)
    (popped:(run (body idx (withArchive d)) b (run enter255 a s)).basis 1711=false) :
    let v:=run (body idx (withArchive d)) b (run enter255 a s)
    let z:=unsigned 255 x p
    let flags:=Leave255Admission.flags z g0 s0
    let z':=unsigned 270 x p
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (PortalValues.negative flags.2 z'.u)
      (decide (Shadow.far 121 15 z')) (decide (Shadow.far 121 15 z' ∧ 2^121≤z'.u))
      (pullState (OB5.sig 269) (endRaw 255 raw v)) (eraseSites ParkEndpoint.src (run leave255 m v)) := by
  let v:=run (body idx (withArchive d)) b (run enter255 a s)
  let z:=unsigned 255 x p
  let flags:=Leave255Admission.flags z g0 s0
  have bank:=carry255 _ v h.ready
  have tail:=tail_clean d raw s a b neg far long _ _ _ cut input (carry (by decide) domain)
  have quiet (q:Wire) (mem:q∈Leave255CoreCheckpoint.rawSites) : v.basis q=false := by
    have layout:∀q∈Leave255CoreCheckpoint.rawSites,(1556≤q ∧ q≤1702) ∨ q=1711 ∨ q∈tailTemps := by decide +kernel
    rcases layout q mem with ⟨lo,hi⟩|rfl|endSite
    · exact bank q lo hi
    · exact popped
    · exact tail q endSite
  have ph:v.phase=(origin 255 raw v).phase := phase.trans (cut.phase.trans (origin_phase _ _ _ (by decide) good raw v domain).symm)
  have up:=upper_clear d raw s x p domain a b neg far long cut
  have ext:=agree_origin d raw s a b neg far long cut
  have par:=Leave255RecordedParity.result v z g0 s0 h.small h.odd h.record
  have md:actualMode 129 z=farMode (v.basis 1706) (v.basis 1707) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave255RecordedEvents.result v z g0 s0 h.small h.odd h.record
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have clear:=Leave255BoundaryClean.result v m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet (LeaveTerminalBound.fit x p good.nonzero good.positive good.odd good.cap good.small good.coprime)
  have extra:=Leave255ReleasedActual.agree d raw s x p good domain a b m neg far long cut clear
  exact Leave255CertifiedCut.result x p good raw v m g0 s0 domain input h ph ext up quiet extra
end ECDSAAdd.Entrant.StairPacket.Leave255BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePersistence
open Arithmetic MappedCompressed IntegerPacket EnterProof ArchivePortAction ArchiveStockSuffix WideReference CodecBitSliceVerify Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body routed
def older:=bank 16 ArchiveBoundary240.codePorts
def two:=older ∪ bank 16 ArchiveBoundary255.codePorts
def first (q:Wire):Bool:=(246≤q && q≤255)||(1274≤q && q≤1283)
def next (q:Wire):Bool:=first q || (261≤q && q≤270)||(1289≤q && q≤1298)
theorem earlier:∀q∈older,first q=true:=by decide +kernel
theorem early:∀q∈two,next q=true:=by decide +kernel
private theorem keep (P:Program) (f:Wire→Bool) (test:P.all (fun g=> !f (target g))=true) (q:Wire) (mem:f q=true) (t:List Bool) (s:State):
    (run P t s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have h:=List.all_eq_true.mp test g hit
  rw [eq,mem] at h
  contradiction
private theorem cleave240Part0:leave240Part0.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part1:leave240Part1.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part2:leave240Part2.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part3:leave240Part3.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part4:leave240Part4.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part5:leave240Part5.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part6:leave240Part6.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part7:leave240Part7.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part8:leave240Part8.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part9:leave240Part9.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part10:leave240Part10.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part11:leave240Part11.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part12:leave240Part12.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part13:leave240Part13.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part14:leave240Part14.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part15:leave240Part15.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part16:leave240Part16.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part17:leave240Part17.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part18:leave240Part18.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part19:leave240Part19.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part20:leave240Part20.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part21:leave240Part21.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part22:leave240Part22.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part23:leave240Part23.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part24:leave240Part24.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part25:leave240Part25.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part26:leave240Part26.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part27:leave240Part27.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part28:leave240Part28.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part29:leave240Part29.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part30:leave240Part30.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part31:leave240Part31.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part32:leave240Part32.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part33:leave240Part33.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part34:leave240Part34.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part35:leave240Part35.all (fun g=> !first (target g))=true:=by decide +kernel
theorem leave240_keeps (q:Wire) (mem:q∈older) (t:List Bool) (s:State):(run leave240 t s).basis q=s.basis q:=by
  apply keep _ first _ _ (earlier _ mem)
  simp only [leave240,List.all_append,cleave240Part0,cleave240Part1,cleave240Part2,cleave240Part3,cleave240Part4,cleave240Part5,cleave240Part6,cleave240Part7,cleave240Part8,cleave240Part9,cleave240Part10,cleave240Part11,cleave240Part12,cleave240Part13,cleave240Part14,cleave240Part15,cleave240Part16,cleave240Part17,cleave240Part18,cleave240Part19,cleave240Part20,cleave240Part21,cleave240Part22,cleave240Part23,cleave240Part24,cleave240Part25,cleave240Part26,cleave240Part27,cleave240Part28,cleave240Part29,cleave240Part30,cleave240Part31,cleave240Part32,cleave240Part33,cleave240Part34,cleave240Part35,Bool.and_self]
private theorem cleave255Part0:leave255Part0.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part1:leave255Part1.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part2:leave255Part2.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part3:leave255Part3.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part4:leave255Part4.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part5:leave255Part5.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part6:leave255Part6.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part7:leave255Part7.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part8:leave255Part8.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part9:leave255Part9.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part10:leave255Part10.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part11:leave255Part11.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part12:leave255Part12.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part13:leave255Part13.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part14:leave255Part14.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part15:leave255Part15.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part16:leave255Part16.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part17:leave255Part17.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part18:leave255Part18.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part19:leave255Part19.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part20:leave255Part20.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part21:leave255Part21.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part22:leave255Part22.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part23:leave255Part23.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part24:leave255Part24.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part25:leave255Part25.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part26:leave255Part26.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part27:leave255Part27.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part28:leave255Part28.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part29:leave255Part29.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part30:leave255Part30.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part31:leave255Part31.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part32:leave255Part32.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part33:leave255Part33.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part34:leave255Part34.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part35:leave255Part35.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part36:leave255Part36.all (fun g=> !next (target g))=true:=by decide +kernel
theorem leave255_keeps (q:Wire) (mem:q∈two) (t:List Bool) (s:State):(run leave255 t s).basis q=s.basis q:=by
  apply keep _ next _ _ (early _ mem)
  simp only [leave255,List.all_append,cleave255Part0,cleave255Part1,cleave255Part2,cleave255Part3,cleave255Part4,cleave255Part5,cleave255Part6,cleave255Part7,cleave255Part8,cleave255Part9,cleave255Part10,cleave255Part11,cleave255Part12,cleave255Part13,cleave255Part14,cleave255Part15,cleave255Part16,cleave255Part17,cleave255Part18,cleave255Part19,cleave255Part20,cleave255Part21,cleave255Part22,cleave255Part23,cleave255Part24,cleave255Part25,cleave255Part26,cleave255Part27,cleave255Part28,cleave255Part29,cleave255Part30,cleave255Part31,cleave255Part32,cleave255Part33,cleave255Part34,cleave255Part35,cleave255Part36,Bool.and_self]
private theorem cpark270Part0:park270Part0.all (fun g=> !next (target g))=true:=by decide +kernel
theorem park270_keeps (q:Wire) (mem:q∈two) (t:List Bool) (s:State):(run park270 t s).basis q=s.basis q:=by
  apply keep _ next _ _ (early _ mem)
  simp only [park270,cpark270Part0]
private theorem cportal270InvPart0:portal270InvPart0.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart1:portal270InvPart1.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart2:portal270InvPart2.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart3:portal270InvPart3.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart4:portal270InvPart4.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart5:portal270InvPart5.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart6:portal270InvPart6.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart7:portal270InvPart7.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart8:portal270InvPart8.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart9:portal270InvPart9.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart10:portal270InvPart10.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart11:portal270InvPart11.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart12:portal270InvPart12.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart13:portal270InvPart13.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart14:portal270InvPart14.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart15:portal270InvPart15.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart16:portal270InvPart16.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart17:portal270InvPart17.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart18:portal270InvPart18.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart19:portal270InvPart19.all (fun g=> !next (target g))=true:=by decide +kernel
theorem portal270Inv_keeps (q:Wire) (mem:q∈two) (t:List Bool) (s:State):(run portal270Inv t s).basis q=s.basis q:=by
  apply keep _ next _ _ (early _ mem)
  simp only [portal270Inv,List.all_append,cportal270InvPart0,cportal270InvPart1,cportal270InvPart2,cportal270InvPart3,cportal270InvPart4,cportal270InvPart5,cportal270InvPart6,cportal270InvPart7,cportal270InvPart8,cportal270InvPart9,cportal270InvPart10,cportal270InvPart11,cportal270InvPart12,cportal270InvPart13,cportal270InvPart14,cportal270InvPart15,cportal270InvPart16,cportal270InvPart17,cportal270InvPart18,cportal270InvPart19,Bool.and_self]
theorem next255_keeps (d:Bool) (q:Wire) (mem:q∈older) (t:List Bool) (s:State):
    (run (NativePack255.nextWindow d) t s).basis q=s.basis q:=by
  have layout:∀q∈older,¬MayTouch NativePack255.idx (windowNet NativePack255.idx q) ∧
      q∉ports255 ∧ q∉(NativePack255.support++ArchiveBoundary255.rawPortsList):=by decide +kernel
  obtain ⟨unseen,notEnter,notAdmin⟩:=layout q mem
  simp only [NativePack255.nextWindow,NativePack255.window,run_append,run_take]
  exact ext_head _ _ _ _ _ _ _ _ unseen
    (fun hit=>notEnter (List.mem_toFinset.mp (Enter255.programCover hit))) notAdmin (NativePack255.admin_cover d)
theorem last270_keeps (d:Bool) (q:Wire) (mem:q∈two) (t:List Bool) (s:State):
    (run (NativePack270.lastWindow d) t s).basis q=s.basis q:=by
  have layout:∀q∈two,q∉ArchiveBoundary270.rawPortsList ∧ ∀v:Fin 10,q≠NativePack270.history v:=by decide +kernel
  obtain ⟨notLoad,notPack⟩:=layout q mem
  have notTick:OB5.sig 270 q∉EndTick.L.wires:=by
    apply WideReference.away (i:=270) (by decide)
    have olderSites:∀q∈two,∃r∈List.range' 230 25,∃sw:Bool,q=site sw r:=by decide +kernel
    obtain ⟨r,hr,sw,rfl⟩:=olderSites q mem
    obtain ⟨_,hi⟩:=List.mem_range'_1.mp hr
    rw [site,OB5.sig_invol 270 (by decide)]
    exact ⟨r,by omega,by cases sw <;> simp [logical]⟩
  have nT:=EndTick.physical_free EndTick.P EndTick.supports.1 q notTick
  have nL:q∉wires (archiveLoad270 d):=fun hit=>notLoad (List.mem_toFinset.mp (ArchiveBoundary270.load_cover d hit))
  simp only [NativePack270.lastWindow,NativePack270.endSlice,run_append,run_take]
  rw [run_preserves_outside (archiveLoad270 d) _ _ _ nL,NativePack270.outside _ _ notPack,
    run_preserves_outside EndTick.physP _ _ _ nT,portal270Inv_keeps _ mem,park270_keeps _ mem]
end ECDSAAdd.Entrant.StairPacket.ArchivePersistence

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed
set_option maxRecDepth 35000
set_option maxHeartbeats 3500000
attribute [local irreducible] run body SkywalkNat.step

theorem stock_endpoint (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    let z:=unsigned 225 x p
    let a:=unsigned 240 x p
    let v:=run (firstWindow d) m (pullState (OB5.sig 224) raw)
    let out:=run leave225 n v
    ∃g s:Bool,let flags:=Leave225Admission.flags z g s
      InputAt 225 (encode g s z.u z.v) raw ∧ Leave225Admission.Inputs v z g s ∧
      PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative flags.2 a.u)
        (decide (Shadow.far 136 15 a)) (decide (Shadow.far 136 15 a ∧ 2^136≤a.u))
        (pullState (OB5.sig 239) (endRaw 225 raw v)) (eraseSites Enter240.pending out) ∧
      PastFacts 10 ArchiveBoundary240.rawPorts 144 z g s (HighBankSum.cross (Leave225TrueMiddle.d z)) out := by
  let z:=unsigned 225 x p
  let o:=pullState (OB5.sig 224) raw
  let w:=run portal225 m o
  let v:=run (firstWindow d) m o
  let n1:=m.drop (measurementCount portal225)
  let n2:=n1.drop (measurementCount enter225)
  obtain ⟨g,s,inp,h⟩:=admitted_with_input d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have input:InputAt 225 (encode g s z.u z.v) raw:=by
    unfold InputAt;rw [gg];exact inp
  have packed:=Portal225Flag.physical_frame_for d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage g s inp
  have ph: v.phase=w.phase :=
    (first_window d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage).1.trans packed.phase.symm
  have split:v=run (body idx (program d)) n2 (run enter225 n1 w):=by
    unfold v firstWindow
    rw [run_append,run_take,run_append,run_take]
    rfl
  refine ⟨g,s,input,h,?_,Leave225ArchiveCut.result v n z g s h⟩
  change PackedCut _ _ _ _ _ _ _ _ _ (pullState (OB5.sig 239) (endRaw 225 raw v)) (eraseSites Enter240.pending (run leave225 n v))
  rw [split]
  exact Leave225BodyCut.result d x p good raw w n1 n2 n _ _ _ g s
    (initial 225 x p (by decide) d raw stage) packed input (split ▸ h) (split ▸ ph)

end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference Partial ArchiveBoundary240
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step
theorem stock_endpoint (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m n:List Bool)
    (domain:Domain 240 x p raw) (G S:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S (unsigned 240 x p).u)
      (decide (Shadow.far 136 15 (unsigned 240 x p))) (decide (Shadow.far 136 15 (unsigned 240 x p) ∧ 2^136≤(unsigned 240 x p).u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).a (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 144 (unsigned 225 x p) pg ps cross s) :
    let z:=unsigned 240 x p
    let a:=unsigned 255 x p
    let flags:=Leave240Admission.flags z G S
    let v:=run (nextWindow d) m s
    let out:=run leave240 n v
    Leave240Admission.Inputs v z G S ∧
    PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 129 15 a)) (decide (Shadow.far 129 15 a ∧ 2^129≤a.u))
      (pullState (OB5.sig 254) (endRaw 240 raw v)) (eraseSites Enter255.pending out) ∧
    PastFacts 11 ArchiveBoundary255.rawPorts 136 z G S (HighBankSum.cross (Leave240TrueMiddle.d z)) out := by
  let z:=unsigned 240 x p
  let v:=run (nextWindow d) m s
  let tape:=m.drop (measurementCount enter240)
  have native:=from_domain d x p good raw s m domain G S cut input pg ps cross prior
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have old:=Leave225Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  obtain ⟨_,_,_,popped⟩:=real_receipt d raw s m z G S native.1.odd native.1.small cut input hist (unsigned 225 x p) pg ps cross old.odd old.small prior
  have split:v=run (body idx (withArchive d)) tape (run enter240 m s):=by
    unfold v nextWindow
    rw [run_append,run_take]
    rfl
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have orig:InputAt 240 (encode G S z.u z.v) raw:=by unfold InputAt;rw [gg];exact input
  refine ⟨native.1,?_,Leave240ArchiveCut.result v n z G S native.1⟩
  change PackedCut _ _ _ _ _ _ _ _ _ (pullState (OB5.sig 254) (endRaw 240 raw v)) (eraseSites Enter255.pending (run leave240 n v))
  rw [split]
  have bit:v.basis 1718=false:=popped (2:Fin 3)
  exact Leave240BodyCut.result d x p good raw s m tape n _ _ _ G S domain cut orig (split ▸ native.1)
    (split ▸ native.2.1) (split ▸ bit)
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference Partial ArchiveBoundary255
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step
theorem stock_endpoint (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m n:List Bool)
    (domain:Domain 255 x p raw) (G S:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S (unsigned 255 x p).u)
      (decide (Shadow.far 129 15 (unsigned 255 x p))) (decide (Shadow.far 129 15 (unsigned 255 x p) ∧ 2^129≤(unsigned 255 x p).u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).a (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 136 (unsigned 240 x p) pg ps cross s) :
    let z:=unsigned 255 x p
    let a:=unsigned 270 x p
    let flags:=Leave255Admission.flags z G S
    let v:=run (nextWindow d) m s
    let out:=run leave255 n v
    Leave255Admission.Inputs v z G S ∧
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 121 15 a)) (decide (Shadow.far 121 15 a ∧ 2^121≤a.u))
      (pullState (OB5.sig 269) (endRaw 255 raw v)) (eraseSites ParkEndpoint.src out) ∧
    (physicalCells 12 out=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      out.basis 1701=decide (Shadow.far 129 15 z) ∧
      out.basis 1702=(decide (Shadow.far 129 15 z) && StairArchiveTrace.afterFlags (decide (z.v<z.u)) ((physicalCells 12 out).take 5)) ∧
      out.basis 1703=(decide (Shadow.far 129 15 z) && HighBankSum.cross (Leave255TrueMiddle.d z))) := by
  let z:=unsigned 255 x p
  let v:=run (nextWindow d) m s
  let tape:=m.drop (measurementCount enter255)
  have native:=from_domain d x p good raw s m domain G S cut input pg ps cross prior
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have old:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  obtain ⟨_,_,_,popped⟩:=real_receipt d raw s m z G S native.1.odd native.1.small cut input hist (carry (by decide) domain) (unsigned 240 x p) pg ps cross old.odd old.small prior
  have split:v=run (body idx (withArchive d)) tape (run enter255 m s):=by
    unfold v nextWindow
    rw [run_append,run_take]
    rfl
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have orig:InputAt 255 (encode G S z.u z.v) raw:=by unfold InputAt;rw [gg];exact input
  refine ⟨native.1,?_,Leave255ArchiveCut.result v n z G S native.1⟩
  change PackedCut _ _ _ _ _ _ _ _ _ (pullState (OB5.sig 269) (endRaw 255 raw v)) (eraseSites ParkEndpoint.src (run leave255 n v))
  rw [split]
  have bit:v.basis 1711=false:=popped (2:Fin 3)
  exact Leave255BodyCut.result d x p good raw s m tape n _ _ _ G S domain cut orig (split ▸ native.1)
    (split ▸ native.2.1) (split ▸ bit)
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveWindowPreserve
open Arithmetic IntegerPacket Partial ArchivePortAction WideReference LeaveReadoutFrame
set_option maxRecDepth 60000
set_option maxHeartbeats 5000000

def bank (ps:Ports):List Wire:=(List.finRange 16).map (fun j=>ps ⟨j.val,by omega⟩)
def bank1:=bank ArchiveBoundary240.codePorts
def bank2:=bank ArchiveBoundary255.codePorts
def both:=bank1++bank2

theorem keep {d:Bool} {row:Nat} {s t:State} {ps:Ports} (h:Kept ps d row s)
    (stable:∀q∈bank ps,t.basis q=s.basis q) : Kept ps d row t := by
  intro i
  rw [stable _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩),h i]

private theorem firstBank (q:Wire) (h:q∈bank1) : q∈ArchivePersistence.older :=
  (by decide +kernel : ∀q∈bank1,q∈ArchivePersistence.older) q h

private theorem bothBanks (q:Wire) (h:q∈both) : q∈ArchivePersistence.two :=
  (by decide +kernel : ∀q∈both,q∈ArchivePersistence.two) q h

theorem after240 (s:State) (m:List Bool) (q:Wire) (h:q∈bank1) : (run leave240 m s).basis q=s.basis q :=
  ArchivePersistence.leave240_keeps q (firstBank q h) m s

theorem entering255 (d:Bool) (s:State) (m:List Bool) (q:Wire) (h:q∈bank1) :
    (run (NativePack255.nextWindow d) m s).basis q=s.basis q :=
  ArchivePersistence.next255_keeps d q (firstBank q h) m s

theorem after255 (s:State) (m:List Bool) (q:Wire) (h:q∈both) : (run leave255 m s).basis q=s.basis q :=
  ArchivePersistence.leave255_keeps q (bothBanks q h) m s

theorem last (d:Bool) (s:State) (m:List Bool) (q:Wire) (h:q∈both) :
    (run (NativePack270.lastWindow d) m s).basis q=s.basis q :=
  ArchivePersistence.last270_keeps d q (bothBanks q h) m s
end ECDSAAdd.Entrant.StairPacket.ArchiveWindowPreserve

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 25000
attribute [local irreducible] run body SkywalkNat.step

def signedAt (i x p:Nat) (g s:Bool) := encode g s (unsigned i x p).u (unsigned i x p).v
def flagNeg (i x p:Nat) (sg:Bool) := PortalValues.negative sg (unsigned i x p).u
def farAt (b i x p:Nat) := Shadow.far b 15 (unsigned i x p)
instance (b i x p:Nat) : Decidable (farAt b i x p) := by unfold farAt;infer_instance

theorem readInput (i x p:Nat) (raw:State) (g sg:Bool) (h:InputAt i (signedAt i x p g sg) raw) :
    SkywalkIntegerInput (W.compactSkywalkTickLayout base i) (signedAt i x p g sg).a (signedAt i x p g sg).b g raw.basis := by
  have eq:(signedAt i x p g sg).g=g:=by cases g <;> rfl
  unfold InputAt at h
  rwa [eq] at h

theorem stepInput (i b x p:Nat) (lo:15 ≤ i) (hi:i+15<512) (fixed:Fixed i) (good:Bounds x p)
    (raw v:State) (g sg:Bool) (domain:Domain i x p raw) (input:InputAt i (signedAt i x p g sg) raw)
    (small:min (unsigned i x p).u (unsigned i x p).v<2^b) :
    let next:=SharedSigned.flags g sg (SkywalkTrace.trace 15 (signedAt i x p g sg))
    Domain (i+15) x p (endRaw i raw v) ∧ InputAt (i+15) (signedAt (i+15) x p next.1 next.2) (endRaw i raw v) := by
  exact ⟨advance i x p lo (Nat.le_of_lt hi) fixed good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw v domain,
    (advance_signed i b x p lo hi fixed good raw v domain g sg input small).2⟩

def Saved (i x p:Nat) (ports:Ports) (d:Bool) (out:State) := ∃row<63145,Chronology i x p row ∧ Kept ports d row out

structure At240 (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain:Domain 240 x p raw
  input:InputAt 240 (signedAt 240 x p g sg) raw
  cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (flagNeg 240 x p sg)
      (decide (farAt 136 240 x p)) (decide (farAt 136 240 x p ∧ 2^136≤(unsigned 240 x p).u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s)
  facts:PastFacts 10 ArchiveBoundary240.rawPorts 144 (unsigned 225 x p) pg ps
      (HighBankSum.cross (Leave225TrueMiddle.d (unsigned 225 x p))) s
  pastCanonical:signedAt 225 x p pg ps=WideReference.canonical 225 x p

def Ready240 (d:Bool) (x p:Nat) (s:State) := ∃raw g sg pg ps,At240 d x p raw s g sg pg ps

structure At255 (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain:Domain 255 x p raw
  input:InputAt 255 (signedAt 255 x p g sg) raw
  cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (flagNeg 255 x p sg)
      (decide (farAt 129 255 x p)) (decide (farAt 129 255 x p ∧ 2^129≤(unsigned 255 x p).u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s)
  facts:PastFacts 11 ArchiveBoundary255.rawPorts 136 (unsigned 240 x p) pg ps
      (HighBankSum.cross (Leave240TrueMiddle.d (unsigned 240 x p))) s
  pastCanonical:signedAt 240 x p pg ps=WideReference.canonical 240 x p
  saved225:Saved 225 x p ArchiveBoundary240.codePorts d s

def Ready255 (d:Bool) (x p:Nat) (s:State) := ∃raw g sg pg ps,At255 d x p raw s g sg pg ps

structure At270 (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain:Domain 270 x p raw
  input:InputAt 270 (signedAt 270 x p g sg) raw
  cut:PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (flagNeg 270 x p sg)
      (decide (farAt 121 270 x p)) (decide (farAt 121 270 x p ∧ 2^121≤(unsigned 270 x p).u))
      (pullState (OB5.sig 269) raw) (eraseSites ParkEndpoint.src s)
  records:physicalCells 12 s=SkywalkTrace.trace 15 (signedAt 255 x p pg ps)
  mode:s.basis 1701=decide (farAt 129 255 x p)
  side:s.basis 1702=(decide (farAt 129 255 x p) && StairArchiveTrace.afterFlags (decide ((unsigned 255 x p).v<(unsigned 255 x p).u)) ((physicalCells 12 s).take 5))
  cross:s.basis 1703=(decide (farAt 129 255 x p) && HighBankSum.cross (Leave255TrueMiddle.d (unsigned 255 x p)))
  pastCanonical:signedAt 255 x p pg ps=WideReference.canonical 255 x p
  saved225:Saved 225 x p ArchiveBoundary240.codePorts d s
  saved240:Saved 240 x p ArchiveBoundary255.codePorts d s

def Ready270 (d:Bool) (x p:Nat) (s:State) := ∃raw g sg pg ps,At270 d x p raw s g sg pg ps
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed
attribute [local irreducible] run measurementCount

def Checked (F R:Program) (pre post:State→Prop) := ∀s m,pre s →
  let out:=run F m s
  out.phase=s.phase ∧ post out ∧ ∀n,run R n out=s

theorem composition {F R F' R':Program} {A B C:State→Prop}
    (left:Checked F R A B) (right:Checked F' R' B C) : Checked (F++F') (R'++R) A C := by
  intro s m h
  obtain ⟨ph,mid,undo⟩:=left s m h
  obtain ⟨ph',post,undo'⟩:=right _ (m.drop (measurementCount F)) mid
  dsimp only
  rw [run_append,run_take]
  refine ⟨ph'.trans ph,post,?_⟩
  intro n
  rw [run_append,run_take,undo',undo]

theorem pair {F R F' R':Program} {A B:State→Prop}
    (law:∀s m, A s →
      let first:=run F m s
      let out:=run F' (m.drop (measurementCount F)) first
      out.phase=s.phase ∧ B out ∧ (∀k,run R' k out=first) ∧ (∀k,run R k first=s)) :
    Checked (F++F') (R'++R) A B := by
  intro s m h
  obtain ⟨ph,post,inv,inv'⟩:=law s m h
  dsimp only
  rw [run_append,run_take]
  refine ⟨ph,post,?_⟩
  intro n
  rw [run_append,run_take,inv,inv']

theorem cutPhase {lo hi:List (Wire×Wire)} {g n f u:Wire} {neg far long:Bool}
    {sig:Wire→Wire} {raw s:State} {pending:List Wire}
    (cut:PackedCut lo hi g n f u neg far long (pullState sig raw) (eraseSites pending s)) :
    s.phase=raw.phase := cut.phase

def Before (d:Bool) (x p:Nat) (s:State) := ∃raw:State,
  Rolling1588.Integer.Stage base d x p 225 raw.basis ∧ s=pullState (OB5.sig 224) raw

end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3200000
attribute [local irreducible] run body measurementCount leave225 leave225Inv NativePack225.firstWindow NativePack225.firstUnwind

private theorem physical (d:Bool) (x p:Nat) (good:Bounds x p) (s:State) (m n:List Bool)
    (pre:Before d x p s) :
    let v:=run (NativePack225.firstWindow d) m s
    let out:=run leave225 n v
    out.phase=s.phase ∧ Ready240 d x p out ∧ (∀k,run leave225Inv k out=v) ∧ (∀k,run (NativePack225.firstUnwind d) k v=s) := by
  obtain ⟨raw,stage,rfl⟩:=pre
  let s:=pullState (OB5.sig 224) raw
  let v:=run (NativePack225.firstWindow d) m s
  let out:=run leave225 n v
  let raw':=endRaw 225 raw v
  obtain ⟨g,sg,input,h,cut,facts⟩:=NativePack225.stock_endpoint d x p good raw m n stage
  let flags:=Leave225Admission.flags (unsigned 225 x p) g sg
  have dom:=initial 225 x p (by decide) d raw stage
  have carried:=stepInput 225 144 x p (by decide) (by decide) fixed225 good raw v g sg dom input h.small
  have base:out.phase=raw'.phase:=cutPhase cut
  have ph:=base.trans (endRaw_phase 225 x p (by decide) good raw v dom)
  have back:=NativePack225.first_window d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage
  exact ⟨ph,⟨raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,unique_input input (fixed_input 225 x p (by decide) good raw dom)⟩,
    h.roundtrip n,back.2.2⟩

theorem step225 (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (NativePack225.firstWindow d++leave225) (leave225Inv++NativePack225.firstUnwind d) (Before d x p) (Ready240 d x p) := by
  apply pair (F:=NativePack225.firstWindow d) (F':=leave225) (R:=NativePack225.firstUnwind d) (R':=leave225Inv)
  intro s m h
  exact physical d x p good s m _ h
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed ArchivePortAction ArchiveStockRows
set_option maxRecDepth 30000
set_option maxHeartbeats 3300000
attribute [local irreducible] run body measurementCount leave240 leave240Inv NativePack240.nextWindow NativePack240.nextUnwind

private theorem finalWindowPhysical (d:Bool) (x p:Nat) (good:Bounds x p) (s:State) (m n:List Bool)
    (pre:Ready240 d x p s) :
    let v:=run (NativePack240.nextWindow d) m s
    let out:=run leave240 n v
    out.phase=s.phase ∧ Ready255 d x p out ∧ (∀k,run leave240Inv k out=v) ∧ (∀k,run (NativePack240.nextUnwind d) k v=s) := by
  obtain ⟨raw,g,sg,pg,ps,pre⟩:=pre
  let v:=run (NativePack240.nextWindow d) m s
  let out:=run leave240 n v
  let raw':=endRaw 240 raw v
  let flags:=Leave240Admission.flags (unsigned 240 x p) g sg
  have curr:=readInput 240 x p raw g sg pre.input
  have native:=NativePack240.from_domain_matched d x p good raw s m pre.domain g sg pre.cut curr pg ps _ pre.facts
  obtain ⟨h,cut,facts⟩:=NativePack240.stock_endpoint d x p good raw s m n pre.domain g sg pre.cut curr pg ps _ pre.facts
  have carried:=stepInput 240 136 x p (by decide) (by decide) fixed240 good raw v g sg pre.domain pre.input h.small
  have lastPhase:out.phase=raw'.phase:=cutPhase cut
  have prevPhase:s.phase=raw.phase:=cutPhase pre.cut
  have ph:=lastPhase.trans ((endRaw_phase 240 x p (by decide) good raw v pre.domain).trans prevPhase.symm)
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology 225 x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  have accepted:Saved 225 x p ArchiveBoundary240.codePorts d out:=by
    refine ⟨row,bound,chr,ArchiveWindowPreserve.keep kept ?_⟩
    intro q hq
    exact ArchiveWindowPreserve.after240 v n q hq
  have same:=unique_input pre.input (fixed_input _ _ _ (by decide) good raw pre.domain)
  exact ⟨ph,⟨raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,same,accepted⟩,h.roundtrip n,native.2.2.2⟩

theorem step240 (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (NativePack240.nextWindow d++leave240) (leave240Inv++NativePack240.nextUnwind d) (Ready240 d x p) (Ready255 d x p) := by
  apply pair (F:=NativePack240.nextWindow d) (F':=leave240) (R:=NativePack240.nextUnwind d) (R':=leave240Inv)
  intro s m h
  exact finalWindowPhysical d x p good s m _ h
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

end
