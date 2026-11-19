import ECDSAAdd.Math.SkywalkTrace
import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickFullArithmetic39b7
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickWholeac0c
import ECDSAAdd.Submission.Entrant.PrizeTail227303371
import ECDSAAdd.Submission.Entrant.PrizeTail46901f669

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveTraceHistory
open SkywalkNat SkywalkRails IntegerHigh LeaveSelector StairArchiveTrace

theorem flags (b : Nat) (z : SkywalkNat.State) : actualMode b z =
    farMode (decide (Shadow.far b 15 z)) (decide (Shadow.far b 15 z) && decide (2^b≤z.u)) z.u := by
  by_cases f : Shadow.far b 15 z <;> simp [actualMode,farMode,ofFlags,f]

theorem orient (b : Nat) (z : SkywalkNat.State) (small : min z.u z.v < 2^b) (far : Shadow.far b 15 z) :
    decide (2^b≤z.u)=decide (z.v<z.u) := by
  have rail:=LeaveShadowRails.rail b z small far
  by_cases lhs : 2^b≤z.u
  · have hv : z.v<2^b := by omega
    simp [lhs,show z.v<z.u by omega]
  · obtain ⟨u,v,guarded⟩:=rail.2 (by omega)
    have g:=guard_gt 15 (Shadow.reduced b 15 z).u
    simp [lhs,show ¬z.v<z.u by omega]

theorem certifiedChain (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : min z.u z.v < 2^b) (odd : z.v%2=1) (far : Shadow.far b 15 z) :
    chain (decide (2^b≤z.u)) (SkywalkTrace.trace 15 (encode g s z.u z.v)) := by
  rw [orient b z small far]
  exact signed (Shadow.represented b 15 z small far).1 g s (by omega) odd

theorem swapLetters {k : Nat} {z t : SkywalkNat.State} (h : Rel k z t)
    (g s : Bool) (odd : z.v%2=1) :
    (SkywalkTrace.trace k (encode g s z.u z.v)).map Prod.snd =
      (letters k t).map (fun a => decide (a=2)) := by
  induction k generalizing z t g s with
  | zero => rfl
  | succ k ih =>
    have pos : 0<z.v := by omega
    obtain ⟨eq,tail⟩:=advance h
    simp only [SkywalkTrace.trace,letters,List.map_cons,recorded z g s pos odd (different h).1,eq,
      SkywalkTrace.next,step_reencode g s z pos odd]
    exact congrArg (_ :: ·) (ih tail _ _ (step_v_odd_pos z pos odd).2)

theorem firstSwap (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : min z.u z.v < 2^b) (odd : z.v%2=1) (far : Shadow.far b 15 z)
    (side : decide (2^b≤z.u)=false) :
    let xs:=SkywalkTrace.trace 15 (encode g s z.u z.v)
    ∀ i (hi : i<xs.length), i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u) := by
  let xs:=SkywalkTrace.trace 15 (encode g s z.u z.v)
  let r:=Shadow.reduced b 15 z
  have h:= (LeaveShadowRails.rail b z small far).2 (Nat.lt_of_not_ge (of_decide_eq_false side))
  have eq : r=⟨z.u,r.v⟩:=SkywalkNat.State.ext h.1 rfl
  have guard : IntegerHigh.guard 15 z.u≤r.v:=h.1 ▸ h.2.2
  have tape:=swapLetters (Shadow.represented b 15 z small far).1 g s odd
  change xs.map Prod.snd=(letters 15 r).map _ at tape
  rw [eq] at tape
  let v : BasisState:=fun q => (xs[q]?.getD (false,false)).2
  have raw:=raw_exchange r.v z.u guard v id (by
    intro i
    have hi : i.val<xs.length := by simpa only [xs,SkywalkTrace.trace_length] using i.isLt
    have bit:=congrArg (fun a : List Bool => a[i.val]?) tape
    have len := congrArg List.length tape
    simp only [List.length_map] at len
    have hi2 : i.val < (letters 15 ⟨z.u,r.v⟩).length := len ▸ hi
    simpa [v, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi2] using bit)
  dsimp only
  intro i hi early
  change i<xs.length at hi
  have idx : i<15 := by simpa only [xs,SkywalkTrace.trace_length] using hi
  simpa only [v,id_eq,List.getElem?_eq_getElem hi,Option.getD_some] using raw i idx early

end ECDSAAdd.Entrant.StairPacket.LeaveTraceHistory


end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveTraceLetters
open IntegerHigh SkywalkNat SkywalkRails

theorem parity (k : Nat) (z : SkywalkNat.State) (g s : Bool) (odd : z.v % 2 = 1) :
    (SkywalkTrace.trace k (encode g s z.u z.v)).map (fun pair => !pair.1) =
      oddBits (letters k z) := by
  induction k generalizing z g s with
  | zero => rfl
  | succ k ih =>
    have pos : 0 < z.v := by omega
    have bit := (SkywalkTrace.code_classified g s z pos odd).1
    have tail := (step_v_odd_pos z pos odd).2
    simp only [SkywalkTrace.trace, List.map_cons, letters, oddBits]
    rw [bit, SkywalkTrace.next, step_reencode g s z pos odd]
    congr 1
    · by_cases even : z.u%2=0 <;> by_cases lt : z.u<z.v <;> simp [letter,even,lt]
    · exact ih _ _ _ tail

end ECDSAAdd.Entrant.StairPacket.LeaveTraceLetters


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225RecordedParity
open Arithmetic IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem result (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^144) (odd : z.v % 2 = 1)
    (record : readCells (shape 10) 0 15 (mappedBasis 10 s.basis) =
      SkywalkTrace.trace 15 (encode g sg z.u z.v)) :
    Leave225EntryAction.oddRead s.basis = oddBits (letters 15 (Shadow.reduced 144 15 z)) := by
  have ports : Leave225EntryAction.oddRead s.basis =
      (readCells (shape 10) 0 15 (mappedBasis 10 s.basis)).map (fun pair => !pair.1) := by rfl
  rw [ports,record,←true_records 144 z small odd g sg]
  exact LeaveTraceLetters.parity _ _ _ _ (shadow_odd _ _ small odd)

end ECDSAAdd.Entrant.StairPacket.Leave225RecordedParity


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
