import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickBeforeStore0786
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickFullArithmetic39b7
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRoutedRestore88ff

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FrontPrepare
open Arithmetic Partial RecordedQuantum PortalValues LeaveCompanion LeaveCompanion225
open Leave225Front Leave225FrontReady LeaveSelector Leave225Selector Leave225Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem prepare (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (zero:∀q∈watched,s.basis q=false) (k:Mode) (smallU:Nat)
    (mode:k=farMode ((run entry m s).basis 1721) ((run entry m s).basis 1722) smallU)
    (exchange:right k=true → ∀i<15,i≤key k → (run entry m s).basis (swaps i)=decide (i=key k)) :
    let a:=run entry m s
    run (entry++fullPrefix false) m s=⟨a.phase,fun q=>(sim Leave225Selector.prepare (LeaveSelector.start ports false k) q).read a.basis⟩ := by
  let a:=run entry m s
  have keep:=Leave225FrontReady.frame s m z G sg small ready fresh scratch temp
  have clear (q:Wire) (h:q∈watched) : a.basis q=false := (keep q h).trans (zero q h)
  have cells (q:Nat) (lo:1561≤q) (hi:q≤1597) : q∈watched := by
    unfold watched
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q-1559,by omega,by omega⟩
  rw [run_append,run_take]
  apply preparedState false a _ a.basis smallU k mode (clear _ (by decide)) (clear _ (by decide))
  · exact beforeFresh ports k a.basis (fun q lo hi=>clear q (cells q lo hi)) (clear _ (by decide)) (clear _ (by decide))
  · exact exchange

end ECDSAAdd.Entrant.StairPacket.Leave225FrontPrepare


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FrontPrepare
open Arithmetic Partial RecordedQuantum PortalValues LeaveCompanion LeaveCompanion240
open Leave240Front Leave240FrontReady LeaveSelector Leave240Selector Leave240Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem prepare (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (zero:∀q∈watched,s.basis q=false) (k:Mode) (smallU:Nat)
    (mode:k=farMode ((run entry m s).basis 1713) ((run entry m s).basis 1714) smallU)
    (exchange:right k=true → ∀i<15,i≤key k → (run entry m s).basis (swaps i)=decide (i=key k)) :
    let a:=run entry m s
    run (entry++fullPrefix false) m s=⟨a.phase,fun q=>(sim Leave240Selector.prepare (LeaveSelector.start ports false k) q).read a.basis⟩ := by
  let a:=run entry m s
  have keep:=Leave240FrontReady.frame s m z G sg small ready fresh scratch temp
  have clear (q:Wire) (h:q∈watched) : a.basis q=false := (keep q h).trans (zero q h)
  have cells (q:Nat) (lo:1561≤q) (hi:q≤1597) : q∈watched := by
    unfold watched
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q-1559,by omega,by omega⟩
  rw [run_append,run_take]
  apply preparedState false a _ a.basis smallU k mode (clear _ (by decide)) (clear _ (by decide))
  · exact beforeFresh ports k a.basis (fun q lo hi=>clear q (cells q lo hi)) (clear _ (by decide)) (clear _ (by decide))
  · exact exchange

end ECDSAAdd.Entrant.StairPacket.Leave240FrontPrepare


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
