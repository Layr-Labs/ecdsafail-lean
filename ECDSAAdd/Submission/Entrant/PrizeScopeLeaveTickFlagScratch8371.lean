import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickFullArithmetic39b7
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRoutedRestore88ff

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
