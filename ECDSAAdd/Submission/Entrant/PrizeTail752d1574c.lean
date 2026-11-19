import ECDSAAdd.Submission.Entrant.PrizeTail10d9efffc

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

theorem swapPolarity : ∀i:Fin 15, parityAt (Leave225Hit.swaps i.val) leave225=some false := by decide +kernel

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

theorem swapPolarity : ∀i:Fin 15, parityAt (Leave240Hit.swaps i.val) leave240=some false := by decide +kernel

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

theorem swapPolarity : ∀i:Fin 15, parityAt (Leave255Hit.swaps i.val) leave255=some false := by decide +kernel

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
    have stable : parityAt 240 leave225=some false := by decide +kernel
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
    have stable : parityAt 255 leave240=some false := by decide +kernel
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
    have stable : parityAt 270 leave255=some false := by decide +kernel
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
