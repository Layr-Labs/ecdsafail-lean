import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickClosed7f1
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickPostReadyf724
import ECDSAAdd.Submission.Entrant.PrizeTail227303371

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Posted
open Leave225Close Leave225Relocated LeaveSelector StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem result (s:State) (m:List Bool) (f u c:Bool) (w:Fin 16) (xs:List (Bool×Bool))
    (len:xs.length=15) (chainOK:f=true → chain u xs)
    (first:f=true → u=false → ∀i(h:i<xs.length),i≤w.val → xs[i].2=decide (i=w.val))
    (swaps:events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1721=f) (old:s.basis 1722=(f && u)) (suffix:s.basis 1725=nearby (ofFlags f u w))
    (cross:s.basis 1724=(f && c)) (cold:∀p∈events,s.basis p.2=false) :
    let out:=run afterLow m s
    out.phase=s.phase ∧ out.basis 1716=f ∧ out.basis 1717=(f && afterFlags u (xs.take 5)) ∧
      out.basis 1718=(f && c) ∧
      ∀q,out.basis q=writeBit s.basis 1722 false (LeaveRelocation.source moves q) := by
  have vp:=LeavePendingHistory.pending f u xs w len chainOK first
  have ev:events.all (fun p=> !s.basis p.1)= !(xs.take 5).any Prod.snd := by
    have mapped:events.any (fun p=>s.basis p.1)=(xs.take 5).any Prod.snd := by
      simpa only [List.any_map,Function.comp_def,id_eq] using congrArg (List.any · id) swaps
    rw [←mapped]
    simp only [List.all_eq_not_any_not,Bool.not_not]
  have cleared: (s.basis 1722 ^^ (s.basis 1725 && events.all (fun p=> !s.basis p.1)))=false := by
    rw [old,suffix,ev];exact vp.2
  rw [after _ _ cold]
  dsimp only
  rw [cleared]
  have geom:LeaveRelocation.source moves 1716=1721 ∧ LeaveRelocation.source moves 1717=1725 ∧ LeaveRelocation.source moves 1718=1724 := by decide +kernel
  rw [geom.1,geom.2.1,geom.2.2]
  exact ⟨rfl,far,suffix.trans vp.1,cross,fun _=>rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave225Posted


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Posted
open Leave240Close Leave240Relocated LeaveSelector StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem result (s:State) (m:List Bool) (f u c:Bool) (w:Fin 16) (xs:List (Bool×Bool))
    (len:xs.length=15) (chainOK:f=true → chain u xs)
    (first:f=true → u=false → ∀i(h:i<xs.length),i≤w.val → xs[i].2=decide (i=w.val))
    (swaps:events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1713=f) (old:s.basis 1714=(f && u)) (suffix:s.basis 1717=nearby (ofFlags f u w))
    (cross:s.basis 1716=(f && c)) (cold:∀p∈events,s.basis p.2=false) :
    let out:=run afterLow m s
    out.phase=s.phase ∧ out.basis 1709=f ∧ out.basis 1710=(f && afterFlags u (xs.take 5)) ∧
      out.basis 1711=(f && c) ∧
      ∀q,out.basis q=writeBit s.basis 1714 false (LeaveRelocation.source moves q) := by
  have vp:=LeavePendingHistory.pending f u xs w len chainOK first
  have ev:events.all (fun p=> !s.basis p.1)= !(xs.take 5).any Prod.snd := by
    have mapped:events.any (fun p=>s.basis p.1)=(xs.take 5).any Prod.snd := by
      simpa only [List.any_map,Function.comp_def,id_eq] using congrArg (List.any · id) swaps
    rw [←mapped]
    simp only [List.all_eq_not_any_not,Bool.not_not]
  have cleared: (s.basis 1714 ^^ (s.basis 1717 && events.all (fun p=> !s.basis p.1)))=false := by
    rw [old,suffix,ev];exact vp.2
  rw [after _ _ cold]
  dsimp only
  rw [cleared]
  have geom:LeaveRelocation.source moves 1709=1713 ∧ LeaveRelocation.source moves 1710=1717 ∧ LeaveRelocation.source moves 1711=1716 := by decide +kernel
  rw [geom.1,geom.2.1,geom.2.2]
  exact ⟨rfl,far,suffix.trans vp.1,cross,fun _=>rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave240Posted


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Posted
open Leave255Close Leave255Relocated LeaveSelector StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem result (s:State) (m:List Bool) (f u c:Bool) (w:Fin 16) (xs:List (Bool×Bool))
    (len:xs.length=15) (chainOK:f=true → chain u xs)
    (first:f=true → u=false → ∀i(h:i<xs.length),i≤w.val → xs[i].2=decide (i=w.val))
    (swaps:events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1706=f) (old:s.basis 1707=(f && u)) (suffix:s.basis 1710=nearby (ofFlags f u w))
    (cross:s.basis 1709=(f && c)) (cold:∀p∈events,s.basis p.2=false) :
    let out:=run afterLow m s
    out.phase=s.phase ∧ out.basis 1701=f ∧ out.basis 1702=(f && afterFlags u (xs.take 5)) ∧
      out.basis 1703=(f && c) ∧
      ∀q,out.basis q=writeBit s.basis 1707 false (LeaveRelocation.source moves q) := by
  have vp:=LeavePendingHistory.pending f u xs w len chainOK first
  have ev:events.all (fun p=> !s.basis p.1)= !(xs.take 5).any Prod.snd := by
    have mapped:events.any (fun p=>s.basis p.1)=(xs.take 5).any Prod.snd := by
      simpa only [List.any_map,Function.comp_def,id_eq] using congrArg (List.any · id) swaps
    rw [←mapped]
    simp only [List.all_eq_not_any_not,Bool.not_not]
  have cleared: (s.basis 1707 ^^ (s.basis 1710 && events.all (fun p=> !s.basis p.1)))=false := by
    rw [old,suffix,ev];exact vp.2
  rw [after _ _ cold]
  dsimp only
  rw [cleared]
  have geom:LeaveRelocation.source moves 1701=1706 ∧ LeaveRelocation.source moves 1702=1710 ∧ LeaveRelocation.source moves 1703=1709 := by decide +kernel
  rw [geom.1,geom.2.1,geom.2.2]
  exact ⟨rfl,far,suffix.trans vp.1,cross,fun _=>rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave255Posted


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
