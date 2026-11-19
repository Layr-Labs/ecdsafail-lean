import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickClosed7f1
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickEraseActualc63a
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickPrepared375e
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRoutedRestore88ff

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Front
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def flipHistory := ((leave225.drop 78).take 15)
def entry := leave225.take 242
theorem emitted : entry=scanPart++(flipHistory++Leave225EraseActual.program) := by decide +kernel

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
    let e:=negative sg a.u
    let out:=run entry m s
    out.phase=s.phase ∧ regValue fullM out.basis=0 ∧ out.basis 1723=e ∧
      out.basis 1556=decide (2^144≤a.u-e.toNat) ∧ (out.basis 1558).toNat=upperBorrow (2^144) a.u a.v e.toNat ∧
      ∀i<19,out.basis (400+i)=((a.u+a.v)/2^144).testBit i := by
  let a:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  let e:=negative sg a.u
  let u:=run scanPart m s
  let t:=m.drop (measurementCount scanPart)
  let v:=run flipHistory t u
  let tape:=t.drop (measurementCount flipHistory)
  have scanActual:=Leave225InputScan.result s m a.u a.v G sg ready fresh
  have hist (q:Wire) (h:q∉flipHistory.map destination) : v.basis q=u.basis q := preserved _ _ _ _ h
  have phase : v.phase=u.phase := by rfl
  have outputBits (i:Nat) (hi:i<19) : v.basis (400+i)=((a.u+a.v)/2^144).testBit i ∧ v.basis (930+i)=((a.u-e.toNat)/2^144).testBit i := by
    have ok : ∀j:Fin 19,400+j.val∉flipHistory.map destination ∧ 930+j.val∉flipHistory.map destination := by decide +kernel
    rw [hist _ (ok ⟨i,hi⟩).1,hist _ (ok ⟨i,hi⟩).2];exact scanActual.2.2.1 i hi
  have same (q:Wire) (good:q∉flipHistory.map destination ∧ q≠1723 ∧ q∉RailPair.sites pairs) : v.basis q=s.basis q :=
    (hist _ good.1).trans (scanActual.2.2.2 _ good.2.1 good.2.2)
  have clean : ∀q∈1556::1557::1558::fullC,v.basis q=false := by
    intro q h
    rw [same _ ((by decide +kernel : ∀q∈1556::1557::1558::fullC,q∉flipHistory.map destination ∧ q≠1723 ∧ q∉RailPair.sites pairs) q h)]
    exact scratch _ h
  have temps : ∀p∈longPairs,v.basis p.2=false := by
    intro p h
    rw [same _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1723 ∧ p.2∉RailPair.sites pairs) p h)]
    exact temp _ h
  have cap:=LeaveShadowRails.inputFit 144 z small
  have fit : (a.u-e.toNat)/2^144 < 2^19 := lt_of_le_of_lt (Nat.div_le_div_right (show a.u-e.toNat≤a.u+a.v by omega)) cap.2
  have se : e.toNat≤1 := by cases e <;> decide
  have su : e.toNat≤a.u := by
    by_cases h : 0<a.u
    · omega
    · simp [e,negative,h]
  have done:=Leave225EraseActual.result v tape a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  dsimp only
  rw [emitted,run_append,run_take,run_append,run_take]
  refine ⟨done.1.trans (phase.trans scanActual.1),done.2.1,?_,done.2.2.1,done.2.2.2.1,?_⟩
  · exact (done.2.2.2.2 _ (by decide)).trans ((hist _ (by decide)).trans scanActual.2.1)
  · intro i hi
    have clear : ∀j:Fin 19,400+j.val∉1556::1557::1558::fullM := by decide +kernel
    exact (done.2.2.2.2 _ (clear ⟨i,hi⟩)).trans (outputBits i hi).1

end ECDSAAdd.Entrant.StairPacket.Leave225Front


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Front
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def flipHistory := ((leave240.drop 78).take 15)
def entry := leave240.take 242
theorem emitted : entry=scanPart++(flipHistory++Leave240EraseActual.program) := by decide +kernel

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
    let e:=negative sg a.u
    let out:=run entry m s
    out.phase=s.phase ∧ regValue fullM out.basis=0 ∧ out.basis 1715=e ∧
      out.basis 1556=decide (2^136≤a.u-e.toNat) ∧ (out.basis 1558).toNat=upperBorrow (2^136) a.u a.v e.toNat ∧
      ∀i<19,out.basis (407+i)=((a.u+a.v)/2^136).testBit i := by
  let a:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  let e:=negative sg a.u
  let u:=run scanPart m s
  let t:=m.drop (measurementCount scanPart)
  let v:=run flipHistory t u
  let tape:=t.drop (measurementCount flipHistory)
  have scanActual:=Leave240InputScan.result s m a.u a.v G sg ready fresh
  have hist (q:Wire) (h:q∉flipHistory.map destination) : v.basis q=u.basis q := preserved _ _ _ _ h
  have phase : v.phase=u.phase := by rfl
  have outputBits (i:Nat) (hi:i<19) : v.basis (407+i)=((a.u+a.v)/2^136).testBit i ∧ v.basis (922+i)=((a.u-e.toNat)/2^136).testBit i := by
    have ok : ∀j:Fin 19,407+j.val∉flipHistory.map destination ∧ 922+j.val∉flipHistory.map destination := by decide +kernel
    rw [hist _ (ok ⟨i,hi⟩).1,hist _ (ok ⟨i,hi⟩).2];exact scanActual.2.2.1 i hi
  have same (q:Wire) (good:q∉flipHistory.map destination ∧ q≠1715 ∧ q∉RailPair.sites pairs) : v.basis q=s.basis q :=
    (hist _ good.1).trans (scanActual.2.2.2 _ good.2.1 good.2.2)
  have clean : ∀q∈1556::1557::1558::fullC,v.basis q=false := by
    intro q h
    rw [same _ ((by decide +kernel : ∀q∈1556::1557::1558::fullC,q∉flipHistory.map destination ∧ q≠1715 ∧ q∉RailPair.sites pairs) q h)]
    exact scratch _ h
  have temps : ∀p∈longPairs,v.basis p.2=false := by
    intro p h
    rw [same _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1715 ∧ p.2∉RailPair.sites pairs) p h)]
    exact temp _ h
  have cap:=LeaveShadowRails.inputFit 136 z small
  have fit : (a.u-e.toNat)/2^136 < 2^19 := lt_of_le_of_lt (Nat.div_le_div_right (show a.u-e.toNat≤a.u+a.v by omega)) cap.2
  have se : e.toNat≤1 := by cases e <;> decide
  have su : e.toNat≤a.u := by
    by_cases h : 0<a.u
    · omega
    · simp [e,negative,h]
  have done:=Leave240EraseActual.result v tape a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  dsimp only
  rw [emitted,run_append,run_take,run_append,run_take]
  refine ⟨done.1.trans (phase.trans scanActual.1),done.2.1,?_,done.2.2.1,done.2.2.2.1,?_⟩
  · exact (done.2.2.2.2 _ (by decide)).trans ((hist _ (by decide)).trans scanActual.2.1)
  · intro i hi
    have clear : ∀j:Fin 19,407+j.val∉1556::1557::1558::fullM := by decide +kernel
    exact (done.2.2.2.2 _ (clear ⟨i,hi⟩)).trans (outputBits i hi).1

end ECDSAAdd.Entrant.StairPacket.Leave240Front


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Front
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def flipHistory := ((leave255.drop 78).take 15)
def entry := leave255.take 242
theorem emitted : entry=scanPart++(flipHistory++Leave255EraseActual.program) := by decide +kernel

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
    let e:=negative sg a.u
    let out:=run entry m s
    out.phase=s.phase ∧ regValue fullM out.basis=0 ∧ out.basis 1708=e ∧
      out.basis 1556=decide (2^129≤a.u-e.toNat) ∧ (out.basis 1558).toNat=upperBorrow (2^129) a.u a.v e.toNat ∧
      ∀i<19,out.basis (415+i)=((a.u+a.v)/2^129).testBit i := by
  let a:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  let e:=negative sg a.u
  let u:=run scanPart m s
  let t:=m.drop (measurementCount scanPart)
  let v:=run flipHistory t u
  let tape:=t.drop (measurementCount flipHistory)
  have scanActual:=Leave255InputScan.result s m a.u a.v G sg ready fresh
  have hist (q:Wire) (h:q∉flipHistory.map destination) : v.basis q=u.basis q := preserved _ _ _ _ h
  have phase : v.phase=u.phase := by rfl
  have outputBits (i:Nat) (hi:i<19) : v.basis (415+i)=((a.u+a.v)/2^129).testBit i ∧ v.basis (915+i)=((a.u-e.toNat)/2^129).testBit i := by
    have ok : ∀j:Fin 19,415+j.val∉flipHistory.map destination ∧ 915+j.val∉flipHistory.map destination := by decide +kernel
    rw [hist _ (ok ⟨i,hi⟩).1,hist _ (ok ⟨i,hi⟩).2];exact scanActual.2.2.1 i hi
  have same (q:Wire) (good:q∉flipHistory.map destination ∧ q≠1708 ∧ q∉RailPair.sites pairs) : v.basis q=s.basis q :=
    (hist _ good.1).trans (scanActual.2.2.2 _ good.2.1 good.2.2)
  have clean : ∀q∈1556::1557::1558::fullC,v.basis q=false := by
    intro q h
    rw [same _ ((by decide +kernel : ∀q∈1556::1557::1558::fullC,q∉flipHistory.map destination ∧ q≠1708 ∧ q∉RailPair.sites pairs) q h)]
    exact scratch _ h
  have temps : ∀p∈longPairs,v.basis p.2=false := by
    intro p h
    rw [same _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1708 ∧ p.2∉RailPair.sites pairs) p h)]
    exact temp _ h
  have cap:=LeaveShadowRails.inputFit 129 z small
  have fit : (a.u-e.toNat)/2^129 < 2^19 := lt_of_le_of_lt (Nat.div_le_div_right (show a.u-e.toNat≤a.u+a.v by omega)) cap.2
  have se : e.toNat≤1 := by cases e <;> decide
  have su : e.toNat≤a.u := by
    by_cases h : 0<a.u
    · omega
    · simp [e,negative,h]
  have done:=Leave255EraseActual.result v tape a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  dsimp only
  rw [emitted,run_append,run_take,run_append,run_take]
  refine ⟨done.1.trans (phase.trans scanActual.1),done.2.1,?_,done.2.2.1,done.2.2.2.1,?_⟩
  · exact (done.2.2.2.2 _ (by decide)).trans ((hist _ (by decide)).trans scanActual.2.1)
  · intro i hi
    have clear : ∀j:Fin 19,415+j.val∉1556::1557::1558::fullM := by decide +kernel
    exact (done.2.2.2.2 _ (clear ⟨i,hi⟩)).trans (outputBits i hi).1

end ECDSAAdd.Entrant.StairPacket.Leave255Front


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225EntryAction
open Arithmetic Partial LeaveSelector Leave225Selector Leave225Close Leave225InputScan Leave225Front LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def oddRead (v:BasisState) := (List.range 15).map (fun i=> !v (ports.g+i))
theorem flipped : flipHistory=notRegister history := by decide +kernel
theorem historyGeom : ∀q∈history,q∉scanPart.map destination ∧ q∉Leave225EraseActual.program.map destination := by decide +kernel
theorem parity (s:State) (m:List Bool) : parityBits ports (run entry m s).basis=oddRead s.basis := by
  let u:=run scanPart m s
  let n:=m.drop (measurementCount scanPart)
  let v:=run flipHistory n u
  have inv:v=⟨u.phase,fun q=>if q∈history then !u.basis q else u.basis q⟩ := by
    change run flipHistory n u=_
    rw [flipped,notRegister_correct _ (by decide)]
  have sites : ∀j:Fin 15,ports.g+j.val∈history := by decide +kernel
  unfold parityBits oddRead
  apply List.map_congr_left
  intro i hi
  have mem:=sites ⟨i,List.mem_range.mp hi⟩
  obtain ⟨before,after⟩:=historyGeom _ mem
  rw [Leave225Front.emitted,run_append,run_take,run_append,run_take]
  change (run _ _ v).basis _=_
  rw [preserved _ v _ _ after,inv]
  change (if _ then !u.basis _ else u.basis _)=_
  rw [if_pos mem,preserved _ s m _ before]

theorem upperBits (a:SkywalkNat.State) (v:BasisState)
    (bits:∀i<19,v (400+i)=((a.u+a.v)/2^144).testBit i) :
    ∀i<18,v (401+i)=((a.u+a.v)/2^145).testBit i := by
  intro i hi
  have div:(a.u+a.v)/2^145=((a.u+a.v)/2^144)/2^1 := by rw [Nat.div_div_eq_div_mul];rfl
  rw [div,Nat.testBit_div_two_pow]
  rw [show (401:Nat)+i=400+(i+1) by omega]
  exact bits (i+1) (Nat.succ_lt_succ hi)
end ECDSAAdd.Entrant.StairPacket.Leave225EntryAction


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FrontReady
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

open Leave225Front LeaveSelector Leave225Selector

def watched : List Wire := [1724,1725]++List.range' 1559 39

theorem frame (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    ∀q∈watched,(run entry m s).basis q=s.basis q := by
  let a:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  let e:=negative sg a.u
  let u:=run scanPart m s
  let t:=m.drop (measurementCount scanPart)
  let v:=run flipHistory t u
  let tape:=t.drop (measurementCount flipHistory)
  have scanActual:=Leave225InputScan.result s m a.u a.v G sg ready fresh
  have hist (q:Wire) (h:q∉flipHistory.map destination) : v.basis q=u.basis q := preserved _ _ _ _ h
  have phase : v.phase=u.phase := by rfl
  have outputBits (i:Nat) (hi:i<19) : v.basis (400+i)=((a.u+a.v)/2^144).testBit i ∧ v.basis (930+i)=((a.u-e.toNat)/2^144).testBit i := by
    have ok : ∀j:Fin 19,400+j.val∉flipHistory.map destination ∧ 930+j.val∉flipHistory.map destination := by decide +kernel
    rw [hist _ (ok ⟨i,hi⟩).1,hist _ (ok ⟨i,hi⟩).2];exact scanActual.2.2.1 i hi
  have same (q:Wire) (good:q∉flipHistory.map destination ∧ q≠1723 ∧ q∉RailPair.sites pairs) : v.basis q=s.basis q :=
    (hist _ good.1).trans (scanActual.2.2.2 _ good.2.1 good.2.2)
  have clean : ∀q∈1556::1557::1558::fullC,v.basis q=false := by
    intro q h
    rw [same _ ((by decide +kernel : ∀q∈1556::1557::1558::fullC,q∉flipHistory.map destination ∧ q≠1723 ∧ q∉RailPair.sites pairs) q h)]
    exact scratch _ h
  have temps : ∀p∈longPairs,v.basis p.2=false := by
    intro p h
    rw [same _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1723 ∧ p.2∉RailPair.sites pairs) p h)]
    exact temp _ h
  have cap:=LeaveShadowRails.inputFit 144 z small
  have fit : (a.u-e.toNat)/2^144 < 2^19 := lt_of_le_of_lt (Nat.div_le_div_right (show a.u-e.toNat≤a.u+a.v by omega)) cap.2
  have se : e.toNat≤1 := by cases e <;> decide
  have su : e.toNat≤a.u := by
    by_cases h : 0<a.u
    · omega
    · simp [e,negative,h]
  have done:=Leave225EraseActual.result v tape a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  rw [Leave225Front.emitted,run_append,run_take,run_append,run_take]
  intro q h
  have geometry : ∀q∈watched,q∉1556::1557::1558::fullM ∧ q∉flipHistory.map destination ∧ q≠1723 ∧ q∉RailPair.sites pairs := by decide +kernel
  have g:=geometry q h
  exact (done.2.2.2.2 q g.1).trans (same q g.2)

end ECDSAAdd.Entrant.StairPacket.Leave225FrontReady


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240EntryAction
open Arithmetic Partial LeaveSelector Leave240Selector Leave240Close Leave240InputScan Leave240Front LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def oddRead (v:BasisState) := (List.range 15).map (fun i=> !v (ports.g+i))
theorem flipped : flipHistory=notRegister history := by decide +kernel
theorem historyGeom : ∀q∈history,q∉scanPart.map destination ∧ q∉Leave240EraseActual.program.map destination := by decide +kernel
theorem parity (s:State) (m:List Bool) : parityBits ports (run entry m s).basis=oddRead s.basis := by
  let u:=run scanPart m s
  let n:=m.drop (measurementCount scanPart)
  let v:=run flipHistory n u
  have inv:v=⟨u.phase,fun q=>if q∈history then !u.basis q else u.basis q⟩ := by
    change run flipHistory n u=_
    rw [flipped,notRegister_correct _ (by decide)]
  have sites : ∀j:Fin 15,ports.g+j.val∈history := by decide +kernel
  unfold parityBits oddRead
  apply List.map_congr_left
  intro i hi
  have mem:=sites ⟨i,List.mem_range.mp hi⟩
  obtain ⟨before,after⟩:=historyGeom _ mem
  rw [Leave240Front.emitted,run_append,run_take,run_append,run_take]
  change (run _ _ v).basis _=_
  rw [preserved _ v _ _ after,inv]
  change (if _ then !u.basis _ else u.basis _)=_
  rw [if_pos mem,preserved _ s m _ before]

theorem upperBits (a:SkywalkNat.State) (v:BasisState)
    (bits:∀i<19,v (407+i)=((a.u+a.v)/2^136).testBit i) :
    ∀i<18,v (408+i)=((a.u+a.v)/2^137).testBit i := by
  intro i hi
  have div:(a.u+a.v)/2^137=((a.u+a.v)/2^136)/2^1 := by rw [Nat.div_div_eq_div_mul];rfl
  rw [div,Nat.testBit_div_two_pow]
  rw [show (408:Nat)+i=407+(i+1) by omega]
  exact bits (i+1) (Nat.succ_lt_succ hi)
end ECDSAAdd.Entrant.StairPacket.Leave240EntryAction


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FrontReady
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

open Leave240Front LeaveSelector Leave240Selector

def watched : List Wire := [1716,1717]++List.range' 1559 39

theorem frame (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    ∀q∈watched,(run entry m s).basis q=s.basis q := by
  let a:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  let e:=negative sg a.u
  let u:=run scanPart m s
  let t:=m.drop (measurementCount scanPart)
  let v:=run flipHistory t u
  let tape:=t.drop (measurementCount flipHistory)
  have scanActual:=Leave240InputScan.result s m a.u a.v G sg ready fresh
  have hist (q:Wire) (h:q∉flipHistory.map destination) : v.basis q=u.basis q := preserved _ _ _ _ h
  have phase : v.phase=u.phase := by rfl
  have outputBits (i:Nat) (hi:i<19) : v.basis (407+i)=((a.u+a.v)/2^136).testBit i ∧ v.basis (922+i)=((a.u-e.toNat)/2^136).testBit i := by
    have ok : ∀j:Fin 19,407+j.val∉flipHistory.map destination ∧ 922+j.val∉flipHistory.map destination := by decide +kernel
    rw [hist _ (ok ⟨i,hi⟩).1,hist _ (ok ⟨i,hi⟩).2];exact scanActual.2.2.1 i hi
  have same (q:Wire) (good:q∉flipHistory.map destination ∧ q≠1715 ∧ q∉RailPair.sites pairs) : v.basis q=s.basis q :=
    (hist _ good.1).trans (scanActual.2.2.2 _ good.2.1 good.2.2)
  have clean : ∀q∈1556::1557::1558::fullC,v.basis q=false := by
    intro q h
    rw [same _ ((by decide +kernel : ∀q∈1556::1557::1558::fullC,q∉flipHistory.map destination ∧ q≠1715 ∧ q∉RailPair.sites pairs) q h)]
    exact scratch _ h
  have temps : ∀p∈longPairs,v.basis p.2=false := by
    intro p h
    rw [same _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1715 ∧ p.2∉RailPair.sites pairs) p h)]
    exact temp _ h
  have cap:=LeaveShadowRails.inputFit 136 z small
  have fit : (a.u-e.toNat)/2^136 < 2^19 := lt_of_le_of_lt (Nat.div_le_div_right (show a.u-e.toNat≤a.u+a.v by omega)) cap.2
  have se : e.toNat≤1 := by cases e <;> decide
  have su : e.toNat≤a.u := by
    by_cases h : 0<a.u
    · omega
    · simp [e,negative,h]
  have done:=Leave240EraseActual.result v tape a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  rw [Leave240Front.emitted,run_append,run_take,run_append,run_take]
  intro q h
  have geometry : ∀q∈watched,q∉1556::1557::1558::fullM ∧ q∉flipHistory.map destination ∧ q≠1715 ∧ q∉RailPair.sites pairs := by decide +kernel
  have g:=geometry q h
  exact (done.2.2.2.2 q g.1).trans (same q g.2)

end ECDSAAdd.Entrant.StairPacket.Leave240FrontReady


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255EntryAction
open Arithmetic Partial LeaveSelector Leave255Selector Leave255Close Leave255InputScan Leave255Front LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def oddRead (v:BasisState) := (List.range 15).map (fun i=> !v (ports.g+i))
theorem flipped : flipHistory=notRegister history := by decide +kernel
theorem historyGeom : ∀q∈history,q∉scanPart.map destination ∧ q∉Leave255EraseActual.program.map destination := by decide +kernel
theorem parity (s:State) (m:List Bool) : parityBits ports (run entry m s).basis=oddRead s.basis := by
  let u:=run scanPart m s
  let n:=m.drop (measurementCount scanPart)
  let v:=run flipHistory n u
  have inv:v=⟨u.phase,fun q=>if q∈history then !u.basis q else u.basis q⟩ := by
    change run flipHistory n u=_
    rw [flipped,notRegister_correct _ (by decide)]
  have sites : ∀j:Fin 15,ports.g+j.val∈history := by decide +kernel
  unfold parityBits oddRead
  apply List.map_congr_left
  intro i hi
  have mem:=sites ⟨i,List.mem_range.mp hi⟩
  obtain ⟨before,after⟩:=historyGeom _ mem
  rw [Leave255Front.emitted,run_append,run_take,run_append,run_take]
  change (run _ _ v).basis _=_
  rw [preserved _ v _ _ after,inv]
  change (if _ then !u.basis _ else u.basis _)=_
  rw [if_pos mem,preserved _ s m _ before]

theorem upperBits (a:SkywalkNat.State) (v:BasisState)
    (bits:∀i<19,v (415+i)=((a.u+a.v)/2^129).testBit i) :
    ∀i<18,v (416+i)=((a.u+a.v)/2^130).testBit i := by
  intro i hi
  have div:(a.u+a.v)/2^130=((a.u+a.v)/2^129)/2^1 := by rw [Nat.div_div_eq_div_mul];rfl
  rw [div,Nat.testBit_div_two_pow]
  rw [show (416:Nat)+i=415+(i+1) by omega]
  exact bits (i+1) (Nat.succ_lt_succ hi)
end ECDSAAdd.Entrant.StairPacket.Leave255EntryAction


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FrontReady
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

open Leave255Front LeaveSelector Leave255Selector

def watched : List Wire := [1709,1710]++List.range' 1559 39

theorem frame (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    ∀q∈watched,(run entry m s).basis q=s.basis q := by
  let a:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  let e:=negative sg a.u
  let u:=run scanPart m s
  let t:=m.drop (measurementCount scanPart)
  let v:=run flipHistory t u
  let tape:=t.drop (measurementCount flipHistory)
  have scanActual:=Leave255InputScan.result s m a.u a.v G sg ready fresh
  have hist (q:Wire) (h:q∉flipHistory.map destination) : v.basis q=u.basis q := preserved _ _ _ _ h
  have phase : v.phase=u.phase := by rfl
  have outputBits (i:Nat) (hi:i<19) : v.basis (415+i)=((a.u+a.v)/2^129).testBit i ∧ v.basis (915+i)=((a.u-e.toNat)/2^129).testBit i := by
    have ok : ∀j:Fin 19,415+j.val∉flipHistory.map destination ∧ 915+j.val∉flipHistory.map destination := by decide +kernel
    rw [hist _ (ok ⟨i,hi⟩).1,hist _ (ok ⟨i,hi⟩).2];exact scanActual.2.2.1 i hi
  have same (q:Wire) (good:q∉flipHistory.map destination ∧ q≠1708 ∧ q∉RailPair.sites pairs) : v.basis q=s.basis q :=
    (hist _ good.1).trans (scanActual.2.2.2 _ good.2.1 good.2.2)
  have clean : ∀q∈1556::1557::1558::fullC,v.basis q=false := by
    intro q h
    rw [same _ ((by decide +kernel : ∀q∈1556::1557::1558::fullC,q∉flipHistory.map destination ∧ q≠1708 ∧ q∉RailPair.sites pairs) q h)]
    exact scratch _ h
  have temps : ∀p∈longPairs,v.basis p.2=false := by
    intro p h
    rw [same _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1708 ∧ p.2∉RailPair.sites pairs) p h)]
    exact temp _ h
  have cap:=LeaveShadowRails.inputFit 129 z small
  have fit : (a.u-e.toNat)/2^129 < 2^19 := lt_of_le_of_lt (Nat.div_le_div_right (show a.u-e.toNat≤a.u+a.v by omega)) cap.2
  have se : e.toNat≤1 := by cases e <;> decide
  have su : e.toNat≤a.u := by
    by_cases h : 0<a.u
    · omega
    · simp [e,negative,h]
  have done:=Leave255EraseActual.result v tape a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  rw [Leave255Front.emitted,run_append,run_take,run_append,run_take]
  intro q h
  have geometry : ∀q∈watched,q∉1556::1557::1558::fullM ∧ q∉flipHistory.map destination ∧ q≠1708 ∧ q∉RailPair.sites pairs := by decide +kernel
  have g:=geometry q h
  exact (done.2.2.2.2 q g.1).trans (same q g.2)

end ECDSAAdd.Entrant.StairPacket.Leave255FrontReady


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FullArithmetic
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program:=leave225.take 2318
theorem shape : program=entry++(Leave225Routed.body++restore) := by decide +kernel
def unmodified (q:Wire) := q∉entry.map destination
instance (q:Wire):Decidable (unmodified q) := inferInstanceAs (Decidable (q∉_))
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
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let out:=run program m s
    out.phase=s.phase ∧ regValue smallM out.basis=(mag/2^145)%2^10 ∧
    out.basis 1556=decide (2^144≤mag) ∧ (∀i<112,out.basis (live i)=(Leave225TrueMiddle.F z).testBit i) := by
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
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take]
  exact ⟨restored.1.trans (used.1.trans front.1),restored.2.2.1,restored.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave225FullArithmetic


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FullArithmetic
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program:=leave240.take 2459
theorem shape : program=entry++(Leave240Routed.body++restore) := by decide +kernel
def unmodified (q:Wire) := q∉entry.map destination
instance (q:Wire):Decidable (unmodified q) := inferInstanceAs (Decidable (q∉_))
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
