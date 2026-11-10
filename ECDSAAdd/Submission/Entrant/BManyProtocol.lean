import ECDSAAdd.Submission.Entrant.ParkAMany
import ECDSAAdd.Submission.Entrant.BThreeStagedProof

section
namespace ECDSAAdd.Entrant.BThreeTemp
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop
def hostR (L : CuccaroStreamedSquareWideLayout) : Wire := L.core.work.getD 171 0
def hostP (L : CuccaroStreamedSquareWideLayout) : Wire := L.core.work.getD 172 0
def hostU (L : CuccaroStreamedSquareWideLayout) : Wire := L.core.work.getD 173 0
def hosts (L : CuccaroStreamedSquareWideLayout) : List Wire := [hostR L,hostP L,hostU L]
def middle (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  LowBitCarryDevelop.wMidFullCCC0 L c

def HostReady (L : CuccaroStreamedSquareWideLayout) (c x : Wire) : Prop :=
  LoanReady L c x ∧ x ∉ mR L ∧ x ≠ w192 L ∧ x ≠ c ∧
    hasWire (ParkCarry10Develop.body L c) x = true

def oldLoop (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry ++
    middle L c ++
    unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry


end ECDSAAdd.Entrant.BThreeTemp

end

section

/-! Retain a bank of B-side carries using the inherited exact rewrite and scatter proofs. -/
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.BWideTemp
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop

def hostR := BThreeTemp.hostR
def hostP := BThreeTemp.hostP
def hostU := BThreeTemp.hostU
def pad (L : CuccaroStreamedSquareWideLayout) : List Wire := (accZ L).take 31

def loans (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 (L.core.work.drop 173).take 19 ++ (L.core.work.drop 193).take 3 ++ (L.core.work.drop 255).take 1 ++ (L.core.work.drop 227).take 28
def hosts (L : CuccaroStreamedSquareWideLayout) : List Wire := hostR L::hostP L::loans L
def middle := BThreeTemp.middle
def LoanReadyTrim (L : CuccaroStreamedSquareWideLayout) (g u : Wire) : Prop :=
 u∈L.core.work ∧ u∉L.core.cin::(hiReg L++accReg L++pad L++accBank L) ∧
 u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L ∧ True
def HostReady (L : CuccaroStreamedSquareWideLayout) (c x : Wire) : Prop :=
 LoanReadyTrim L c x ∧ x∉mR L ∧ x≠w192 L ∧ x≠c ∧ hasWire (ParkCarry10Develop.body L c) x=true
def Ready (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Prop :=
 (loans L).length=51 ∧ (L.core.sumCarry::hosts L).Nodup ∧ ∀x∈hosts L,HostReady L c x
instance (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Decidable (Ready L c) := by
 unfold Ready HostReady LoanReadyTrim
 unfold pad
 infer_instance

def checkedMiddle (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 Option (CheckedMany (hosts L) (middle L c)) := compileManyChunked? (hosts L) (middle L c)
def oldLoop := BThreeTemp.oldLoop
def newLoop (L : CuccaroStreamedSquareWideLayout) (c : Wire)
 (cm : CheckedMany (hosts L) (middle L c)) : Program :=
 ManyACarryDevelop.buildMany 51 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  (loans L) L.core.sumCarry (hostR L) (hostP L) ++ cm.out ++
 ManyACarryDevelop.unbuildMany 51 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  (loans L) L.core.sumCarry (hostR L) (hostP L)
def newFold (L : CuccaroStreamedSquareWideLayout) (c : Wire)
 (cm : CheckedMany (hosts L) (middle L c)) : Program :=
 eAddLo L ++ (newLoop L c cm ++ (ParkCarryDevelop.program (eU L) L.core.sumCarry ++ eSubK L))
def newBody (L : CuccaroStreamedSquareWideLayout) (c : Wire)
 (cm : CheckedMany (hosts L) (middle L c)) : Program :=
 measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++
  (newFold L c cm ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L)))
def mechanismEnabled : Bool := true
def bodyWith (enabled : Bool) (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
 if enabled then
  if Ready L c then
   match checkedMiddle L c with
   | none => ParkCarry10Develop.body L c
   | some cm => newBody L c cm
  else ParkCarry10Develop.body L c
 else ParkCarry10Develop.body L c
def selectedBody (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program := bodyWith mechanismEnabled L c
def hostedSelectedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 selectedBody (ParkCarryDevelop.hostLayout L rho) c

theorem off_exact (L : CuccaroStreamedSquareWideLayout) (c : Wire) : bodyWith false L c=ParkCarry10Develop.body L c := rfl
theorem geometry_fallback (L : CuccaroStreamedSquareWideLayout) (c : Wire) (h : ¬Ready L c) : bodyWith true L c=ParkCarry10Develop.body L c := by simp [bodyWith,h]
theorem compiler_fallback (L : CuccaroStreamedSquareWideLayout) (c : Wire) (h : checkedMiddle L c=none) : bodyWith true L c=ParkCarry10Develop.body L c := by simp [bodyWith,h]

theorem middle_subset_old (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (middle L c) ⊆ wires (ParkCarry10Develop.body L c) := by
 intro q member
 simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,wires_append,Finset.mem_union]
 exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl member)))))

theorem host_ready (L : CuccaroStreamedSquareWideLayout) (c : Wire) (h : Ready L c) :
 HostReady L c (hostR L) ∧ HostReady L c (hostP L) ∧ ∀x∈loans L,HostReady L c x := by
 exact ⟨h.2.2 _ (by simp [hosts]),h.2.2 _ (by simp [hosts]),fun x hx=>h.2.2 x (by simp [hosts,hx])⟩
theorem loan_ne (L : CuccaroStreamedSquareWideLayout) (c : Wire) (h : Ready L c) :
 (loans L).Nodup ∧ hostP L≠hostR L ∧ ∀x∈loans L,x≠L.core.sumCarry ∧ x≠hostR L ∧ x≠hostP L := by
 have nd := h.2.1
 change (L.core.sumCarry::hostR L::hostP L::loans L).Nodup at nd
 simp only [List.nodup_cons,List.mem_cons,not_or] at nd
 refine ⟨nd.2.2.2,fun e=>nd.2.1.1 e.symm,?_⟩
 intro x hx
 exact ⟨fun e=>nd.1.2.2 (e ▸ hx),fun e=>nd.2.1.2 (e ▸ hx),fun e=>nd.2.2.1 (e ▸ hx)⟩

theorem pad_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : 5≤(pad L).length := by
 have h:=acc_lengths L hw
 simp only [pad,List.length_take]
 omega
 theorem terms_fits (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (accReg L) (pad L) (accBank L) L.core.cin 163 f :=
 BTrimCore.fits_trim _ _ _ _ _ (hiReg_length L hw) (wTerms_fits L hw hn)
 theorem sumCarry_trim (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
 L.core.sumCarry ∉ L.core.cin::(hiReg L++accReg L++pad L++accBank L) := by
 intro h
 exact sumCarry_fresh_domain L hn ((BTrimCore.domain_sublist _ _ _ _ _).subset h)
theorem host_zero_of_bstate (L : CuccaroStreamedSquareWideLayout)
    (hn : L.wires.Nodup) (c x : Wire) (ready : HostReady L c x)
    (base : BasisState) (clean : L.PairClean base) (O E A : Nat)
    (s : BasisState) (hs : BState L base O E A s) : s x = false := by
  have work : x ∈ L.core.work := ready.1.1
  have away := L.pairAuxAway hn x (by simp [work])
  have notE : x ∉ eReg L := fun h => away.1 (eReg_product L _ h)
  have notAcc : x ∉ accReg L := by
    intro member
    exact ready.1.2.1 (by simp [member])
  exact (hs.2.2.2 x away.2 notE notAcc).trans ((regValue_zero _ _).mp clean.work x work)

/-- Source support bounds, rather than a false no-write assumption, establish endpoint freshness. -/
theorem endpoint_off (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (x : Wire) (xq : x ≠ L.core.sumCarry) (xr : x ≠ hostR L) (xp : x ≠ hostP L)
    (offF : x ∉ wires (NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)))
    (offI : x ∉ wires (SourceAddFourDevelop.unbuild (accReg L) (pad L) (accBank L) L.core.cin (hiReg L))) :
    x ∉ wires (buildDual (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) ∧
    x ∉ wires (unbuildDual (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) ∧
    x ∉ wires (buildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L)) ∧
    x ∉ wires (unbuildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L)) := by
  have lens := acc_lengths L hw
  have plen := pad_length L hw
  have cF : x ∉ wires (buildCached (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := by
    intro h
    rcases Finset.mem_insert.mp (buildCached_support _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) (by omega) h) with eq | h
    · exact xq eq
    · exact offF h
  have cI : x ∉ wires (unbuildConsumed (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := by
    intro h
    rcases Finset.mem_insert.mp (unbuildConsumed_support _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) h) with eq | h
    · exact xq eq
    · exact offI h
  have dF : x ∉ wires (buildDual (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
    intro h
    rcases Finset.mem_insert.mp (buildDual_support _ _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) (by omega) h) with eq | h
    · exact xr eq
    · exact cF h
  have dI : x ∉ wires (unbuildDual (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
    intro h
    rcases Finset.mem_insert.mp (unbuildDual_support _ _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) h) with eq | h
    · exact xr eq
    · exact cI h
  refine ⟨dF,dI,?_,?_⟩
  · intro h
    rcases Finset.mem_insert.mp (buildTriple_support _ _ _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) (by omega) h) with eq | h
    · exact xp eq
    · exact dF h
  · intro h
    rcases Finset.mem_insert.mp (unbuildTriple_support _ _ _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) h) with eq | h
    · exact xp eq
    · exact dI h

theorem off_cached (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Wire) (fresh : x ∉ L.core.cin::(hiReg L++accReg L++pad L++accBank L))
    (xq : x ≠ L.core.sumCarry) :
    x ∉ wires (buildCached (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) ∧
    x ∉ wires (unbuildConsumed (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := by
  have lens := acc_lengths L hw
  have plen := pad_length L hw
  have old := wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
    x lens.1 (hiReg_length L hw) (terms_fits L hw hn) fresh
  constructor
  · intro h
    exact (Finset.mem_insert.mp (buildCached_support _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) (by omega) h)).elim xq old.1
  · intro h
    exact (Finset.mem_insert.mp (unbuildConsumed_support _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) h)).elim xq old.2


theorem build_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) = wBuild L :=
 BTrimCore.build8_trim _ _ _ _ _ (hiReg_length L hw)
 theorem cached_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (q : Wire) :
 buildCached (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) q =
 buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) q :=
 BTrimCore.buildCached_trim _ _ _ _ _ _ (hiReg_length L hw)
 theorem consumed_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (q : Wire) :
 unbuildConsumed (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) q =
 unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) q :=
 BTrimCore.unbuildConsumed_trim _ _ _ _ _ _ (hiReg_length L hw)

theorem loop_bstate_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) (hcw : c∉L.wires) (ready : Ready L c)
 (cm : CheckedMany (hosts L) (middle L c))
 (base : BasisState) (clean : L.PairClean base) (hsum : base L.core.sumCarry=false)
 (O E O' : Nat)
 (mid : Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (middle L c)
  (BState L base O' E (4294968272*regValue (hiReg L) base)))
 (s : State) (records : List Bool) (hs : BState L base O E 0 s.basis) :
 run (newLoop L c cm) records s=run (oldLoop L c) records s := by
 have lens:=acc_lengths L hw
 have plen:=pad_length L hw
 have rr:=(host_ready L c ready).1
 have pp:=(host_ready L c ready).2.1
 have uu:=(host_ready L c ready).2.2
 have nd:=loan_ne L c ready
 have away:=ParkCarryDevelop.sumCarry_off_regs L hn
 have zeroQ:s.basis L.core.sumCarry=false := (hs.2.2.2 _ away.1 away.2.1 away.2.2).trans hsum
 have zeroR:=host_zero_of_bstate L hn c (hostR L) rr base clean O E 0 s.basis hs
 have zeroP:=host_zero_of_bstate L hn c (hostP L) pp base clean O E 0 s.basis hs
 have zeroU:∀x∈loans L,s.basis x=false := fun x hx=>host_zero_of_bstate L hn c x (uu x hx) base clean O E 0 s.basis hs
 have freshQ:=sumCarry_trim L hn
 have offQ:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry lens.1 (hiReg_length L hw) (terms_fits L hw hn) freshQ
 have offR:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (hostR L) lens.1 (hiReg_length L hw) (terms_fits L hw hn) rr.1.2.1
 have offP:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (hostP L) lens.1 (hiReg_length L hw) (terms_fits L hw hn) pp.1.2.1
 have pF:hostP L∉wires (buildDual (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
  intro h
  rcases Finset.mem_insert.mp (buildDual_support _ _ _ _ _ _ _ lens.1 (hiReg_length L hw) (by omega) (by omega) h) with eq|h
  · exact nd.2.1 eq
  rcases Finset.mem_insert.mp (buildCached_support _ _ _ _ _ _ lens.1 (hiReg_length L hw) (by omega) (by omega) h) with eq|h
  · exact pp.1.2.2.1 eq
  · exact offP.1 h
 have pI:hostP L∉wires (unbuildDual (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
  intro h
  rcases Finset.mem_insert.mp (unbuildDual_support _ _ _ _ _ _ _ lens.1 (hiReg_length L hw) (by omega) h) with eq|h
  · exact nd.2.1 eq
  rcases Finset.mem_insert.mp (unbuildConsumed_support _ _ _ _ _ _ lens.1 (hiReg_length L hw) (by omega) h) with eq|h
  · exact pp.1.2.2.1 eq
  · exact offP.2 h
 have endpoints:∀x∈loans L,
  x∉wires (buildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L)) ∧
  x∉wires (unbuildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L)) := by
  intro x hx
  have off:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) x lens.1 (hiReg_length L hw) (terms_fits L hw hn) (uu x hx).1.2.1
  exact (endpoint_off L hw x (nd.2.2 x hx).1 (nd.2.2 x hx).2.1 (nd.2.2 x hx).2.2 off.1 off.2).2.2
 have offMiddle:L.core.sumCarry∉wires (middle L c):=ParkCarry10Develop.mid_sumCarry_free L hw hn c hcw
 obtain ⟨hzFull,hb,hi,_,_⟩:=zero_regs L hn base clean O E 0 s.basis hs
 have hz:∀w∈pad L,s.basis w=false := fun w hw=>hzFull w (List.mem_of_mem_take hw)
 have source0:regValue (hiReg L) s.basis=regValue (hiReg L) base := regValue_congr _ _ _ (fun q hq=>bstate_other L hn base O E 0 s.basis hs q (Or.inl hq))
 have good:WReady (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (regValue (hiReg L) s.basis)
  (middleState (wBuild L) (middle L c) s records) := by
  let first:=run (wBuild L) (records.take (measurementCount (wBuild L))) s
  have firstGood:=(wBuild_step L hw hn base clean O E) s (records.take (measurementCount (wBuild L))) hs
  have midGood:=mid first ((records.drop (measurementCount (wBuild L))).take (measurementCount (middle L c))) firstGood.2
  obtain ⟨mz,mb,mi,_,_⟩:=zero_regs L hn base clean O' E _ _ midGood.2
  have source1:=regValue_congr (hiReg L) _ base (fun q hq=>bstate_other L hn base O' E _ _ midGood.2 q (Or.inl hq))
  exact ⟨midGood.2.2.2.1.trans (by rw [source0]),source1.trans source0.symm,(fun w hw=>mz w (List.mem_of_mem_take hw)),mb,mi⟩
 have zeros:∀x∈hosts L,s.basis x=false := by
  intro x hx; simp only [hosts,List.mem_cons] at hx
  rcases hx with rfl|rfl|hx
  · exact zeroR
  · exact zeroP
  · exact zeroU x hx
 have offOriginal:∀x∈hosts L,x∉wires (NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)) := by
  intro x hx
  exact (wloop_original_off _ _ _ _ _ _ lens.1 (hiReg_length L hw) (terms_fits L hw hn) (ready.2.2 x hx).1.2.1).1
 simp only [build_eq L hw] at offOriginal
 have midEq:=cm.proof.middle_eq (hosts L) (middle L c) cm.out (wBuild L) s records zeros offOriginal
 have goodNew:WReady (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (regValue (hiReg L) s.basis)
  (middleState (wBuild L) cm.out s records) := by rw [midEq];exact good
 have support:=cm.proof.support (hosts L) (middle L c) cm.out
 have nq:L.core.sumCarry∉wires cm.out := fun h=>offMiddle (support.1 h)
 have nr:hostR L∉wires cm.out := support.2 _ (by simp [hosts])
 have np:hostP L∉wires cm.out := support.2 _ (by simp [hosts])
 have triple:=triple_middle_ready (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (hostR L) (hostP L) cm.out lens.1 (hiReg_length L hw) (terms_fits L hw hn)
  s records hz hb hi hs.2.2.1 zeroQ zeroR zeroP freshQ rr.1.2.1 rr.1.2.2.1 pp.1.2.1 pp.1.2.2.1 nd.2.1
  offQ.1 nq offQ.2 offR.1 nr offR.2 pF np pI (by simpa only [build_eq L hw] using goodNew)
 have many:=ManyACarryDevelop.cached_wloop_many_eq 51 (accReg L) (pad L) (accBank L) L.core.cin
  (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) cm.out lens.1 (hiReg_length L hw)
  (terms_fits L hw hn) s records hz hb hi hs.2.2.1 zeroQ zeroR zeroP zeroU freshQ rr.1.2.1 rr.1.2.2.1
  pp.1.2.1 pp.1.2.2.1 nd.2.1 (by decide) nd.1 ready.1 (fun x hx=>(uu x hx).1.2.1) nd.2.2
  offQ.1 offQ.2 offR.1 offR.2 pF pI (fun x hx=>(endpoints x hx).1)
  (fun x hx=>support.2 x (by simp [hosts,hx])) (fun x hx=>(endpoints x hx).2)
  triple.1 triple.2.1 triple.2.2.1 triple.2.2.2
 have tr:=cached_wloop_triple_eq (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (hostR L) (hostP L) cm.out lens.1 (hiReg_length L hw) (terms_fits L hw hn)
  s records hz hb hi hs.2.2.1 zeroQ zeroR zeroP freshQ rr.1.2.1 rr.1.2.2.1 pp.1.2.1 pp.1.2.2.1 nd.2.1
  offQ.1 nq offQ.2 offR.1 nr offR.2 pF np pI (by simpa only [build_eq L hw] using goodNew)
 have du:=cached_wloop_dual_eq (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (hostR L) cm.out lens.1 (hiReg_length L hw) (terms_fits L hw hn)
  s records hz hb hi hs.2.2.1 zeroQ zeroR freshQ rr.1.2.1 rr.1.2.2.1 offQ.1 nq offQ.2 offR.1 nr offR.2 (by simpa only [build_eq L hw] using goodNew)
 have re:=cm.proof.surround_eq (hosts L) (middle L c) cm.out (wBuild L)
  (SourceAddFourDevelop.unbuild (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)) s records zeros offOriginal
 have ca:=cached_wloop_eq (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (middle L c) lens.1 (hiReg_length L hw) (terms_fits L hw hn)
  s records hz hb hi hs.2.2.1 zeroQ freshQ offQ.1 offMiddle offQ.2 (by simpa only [build_eq L hw] using good)
 rw [← build_eq L hw] at re
 simpa only [newLoop,oldLoop,BThreeTemp.oldLoop,cached_eq L hw,consumed_eq L hw] using many.trans (tr.trans (du.trans (re.trans ca.symm)))

theorem loop_bstate_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (c : Wire) (hcw : c ∉ L.wires) (ready : Ready L c)
    (cm : CheckedMany (hosts L) (middle L c))
    (base : BasisState) (clean : L.PairClean base) (hsum : base L.core.sumCarry = false)
    (O E O' : Nat)
    (mid : Triple (BState L base O E (4294968272 * regValue (hiReg L) base)) (middle L c)
      (BState L base O' E (4294968272 * regValue (hiReg L) base))) :
    Triple (BState L base O E 0) (newLoop L c cm) (BState L base O' E 0) := by
  have off := b_wloop_sumCarry_free L hw hn c hcw
  have old := cached_wloop_bstate_step L hw hn base clean hsum O E O' (middle L c)
    mid off.1 (ParkCarry10Develop.mid_sumCarry_free L hw hn c hcw) off.2.2
  intro s records hs
  rw [loop_bstate_eq L hw hn c hcw ready cm base clean hsum O E O' mid s records hs]
  exact old s records hs

section
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
  LowBitCarryDevelop ParkCarry7Develop ParkCarry10Develop

-- Conditional full B10 frame: original arithmetic/source relations are retained verbatim.
theorem newBody_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (ready : Ready L c)
    (cm : CheckedMany (hosts L) (middle L c)) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) (hSource:M=if base c then regValue L.core.high base else 0) :
    Triple (SquareFrame L.core.out base O) (newBody L c cm) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0


  let u := b1/2^96
  let d := W/2^128 - u
  let H := b0/2^32
  let l' := (b0%2^32 + u)%2^32
  let K := (b0%2^32 + u)/2^32
  let O3 := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := (2^32*H + l' + 2^130 - b1) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu32 : u < 2^32 := by
    show b1/2^96 < 2^32
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ = 2^32*2^96 := by norm_num
  have hH : H < 2^96 := by show b0/2^32 < 2^96; omega
  have hl' : l' < 2^32 := Nat.mod_lt _ (by positivity)
  have hK : K ≤ 1 := by show (b0%2^32 + u)/2^32 ≤ 1; omega
  have hKif : (if l' < u then 1 else 0) = K := by
    show (if (b0%2^32 + u)%2^32 < u then 1 else 0) = (b0%2^32 + u)/2^32
    by_cases hc' : (b0%2^32 + u)%2^32 < u
    · rw [if_pos hc']; omega
    · rw [if_neg hc']; omega
  let kap:Bool:=decide (K=1)
  let baseK:=writeBit base L.core.sumCarry kap
  have kapNat:kap.toNat=K := by
    have kk:K=0 ∨ K=1 := by omega
    rcases kk with kk|kk <;> simp [kap,kk]
  have hcK:L.PairClean baseK := ParkCarryDevelop.base_clean L hn base hc kap
  have productOff:L.core.sumCarry∉L.core.product := by
    intro h;apply ParkCarryDevelop.sumCarry_away L hn;simp [ParkCarryDevelop.restWires,h]
  have highOff:L.core.sumCarry∉hiReg L := by
    intro h;exact productOff (List.mem_of_mem_take (List.mem_of_mem_drop h))
  have hb1K:regValue (hiReg L) baseK=b1 := by
    dsimp only [baseK]
    rw [ParkCarryDevelop.reg_update_off _ _ _ _ highOff]
    exact hb1
  have cq:c≠L.core.sumCarry := by
    intro h;apply hcw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
  have gc:baseK c=base c := by simp [baseK,writeBit,cq]
  have resetBase:writeBit baseK L.core.sumCarry false=base := by
    funext q
    by_cases hq:q=L.core.sumCarry
    · subst q;simp [writeBit,Function.update,hsum]
    · simp [baseK,writeBit,Function.update,hq]
  -- Park the completed low-window carry instead of recomputing it.
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have squareBit : (b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw[Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have loanFact : ((2^32*H+l'+2^128*K)/2%2==1)=
      ((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
        ((b1/2^96%2==1)&&((2^32*H+l'+2^128*K)%2==1))) := by
    have low0:(2^32*H+l'+2^128*K)%2=(b0%2^32+u)%2:=by dsimp[l'];omega
    have low1:(2^32*H+l'+2^128*K)/2%2=(b0%2^32+u)/2%2:=by dsimp[l'];omega
    rw[low0,low1]
    exact known_second_loan (b0%2^32) u squareBit
  let originalM:=regValue L.core.high base
  have source1:base (bit1 L.core.high)=digit originalM 1:=by
    simpa only[digit,pow_one]using bit1_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE:(2^32*H+l'+2^128*K)%16=lowSum (base c) originalM u%16:=by
    rw[lowSum,←hSource]
    exact folded_low_mod16 M u H l' K rfl rfl
  have loanFact2:=loan2_from_mod16 (base c) originalM u (2^32*H+l'+2^128*K) modE
  rw[←source1]at loanFact2
  have source0:base (L.core.high.headD 0)=digit originalM 0:=by
    simpa only[digit,pow_zero,Nat.div_one]using head_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE2:(2^32*H+l'+2^128*K)%2=lowSum (base c) originalM u%2:=by omega
  have loanFact0:=LowBitCarryNumbers.loan0_from_mod2 (base c) originalM u (2^32*H+l'+2^128*K)
    (by simpa only[lowSum]using modE2)
  rw[←source0]at loanFact0
  have wm := wMidFullCCC0_step L hw hn c hcw base hc O2 (2^32*H+l'+2^128*K) b1 hb1 hb1lt hO2
    H l' K hH hl' hK rfl loanFact loanFact2 loanFact0
  have wmBase : Triple (BState L base O2 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base))
      (wMidFullCCC0 L c)
      (BState L base O3 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base)) := by
    simpa only [hb1] using wm
  have loop := loop_bstate_step L hw hn c hcw ready cm base hc hsum
    O2 (2^32*H+l'+2^128*K) O3 wmBase
  have kc:=ParkCarryDevelop.park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (newFold L c cm) (BState L baseK O3 E1 0) :=
    by simpa only [newFold,newLoop,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
  -- eFoldTq
  have f1 := eFlip_step L hw hn baseK c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn baseK hcK O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn baseK c hcw O4 (flipE g E1) 0
  rw [gc] at f1 f3
  rw [flipE_flipE] at f3
  have tf : Triple (BState L baseK O3 E1 0) (eFoldTq L c) (BState L baseK O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestoreT
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn baseK hcK O4 E1 0 b1 hb1K (by rw [bk]; omega)
  rw [bk] at r2
  have bit32:(b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw [Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have total:l'+2^32*(baseK L.core.sumCarry).toNat=b0%2^32+regValue (hiReg L) baseK/2^96 := by
    have atq:baseK L.core.sumCarry=kap := by simp [baseK,writeBit]
    rw [atq,kapNat,hb1K]
    show ((b0%2^32+u)%2^32)+2^32*((b0%2^32+u)/2^32)=b0%2^32+u
    exact Nat.mod_add_div _ _
  have r3:=ParkCarryDevelop.restore_step L hw hn baseK hcK O4 0 H l' (b0%2^32) hH hl'
    (Nat.mod_lt _ (by positivity)) bit32 total
  have bb:2^32*H+b0%2^32=b0 := by dsimp [H];omega
  rw [resetBase,bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 744
  have tr : Triple (BState L baseK O4 E1 0) (ParkCarry10Develop.rebuild L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have conv0 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have key : O4 = bO4 (M^2) (base c) O := by
    have hg' : g = false → b1 = 0 ∧ b0 = 0 := by
      intro h0
      have : M = 0 := hg h0
      subst this
      simp [b1, b0, P]
    have e3 : O3 = (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p := by
      simp only [O3, u, d, K, W]
      congr 1; ring
    have e4 : O4 = (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) +
        (SquareReduction.p-1-((((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
      show (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p = _
      rw [e3]
    rw [e4, o4K b0 b1 O2 _ g hb0 hb1lt hO2 hg']
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv0))
  rw [key] at all
  exact all

end


/-- All selected branches retain the old square specification, including the full phase relation. -/
theorem bodyWith_frame (enabled : Bool) (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (c : Wire) (hcw : c ∉ L.wires)
    (base : BasisState) (M : Nat) (hM : M < 2^128) (hP : regValue L.core.product base = M^2)
    (hc : L.PairClean base) (hsum : base L.core.sumCarry = false)
    (O : Nat) (hO : O < SquareReduction.p) (hg : base c = false → M = 0)
    (hSource : M = if base c then regValue L.core.high base else 0) :
    Triple (SquareFrame L.core.out base O) (bodyWith enabled L c)
      (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
  have old := ParkCarry10Develop.body_frame L hw hn c hcw base M hM hP hc hsum O hO hg hSource
  cases enabled with
  | false => exact old
  | true =>
      by_cases ready : Ready L c
      · cases h : checkedMiddle L c with
        | none => simpa only [bodyWith,if_true,if_pos ready,h] using old
        | some cm =>
            simpa only [bodyWith,if_true,if_pos ready,h] using
              newBody_frame L hw hn c hcw ready cm base M hM hP hc hsum O hO hg hSource
      · simpa only [bodyWith,if_true,if_neg ready] using old



def extras (L : CuccaroStreamedSquareWideLayout) : Finset Wire := (hosts L).toFinset

theorem newLoop_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
 (ready : Ready L c) (cm : CheckedMany (hosts L) (middle L c)) :
 toffoliCount (newLoop L c cm)+53≤toffoliCount (oldLoop L c) ∧
 measurementCount (newLoop L c cm)=measurementCount (oldLoop L c) ∧
 Challenge.gateSlots (newLoop L c cm)+159≤Challenge.gateSlots (oldLoop L c) := by
 have lens:=acc_lengths L hw
 have plen:=pad_length L hw
 have f1:=buildDual_counts (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) (by omega)
 have f2:=buildTriple_counts (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega)
 have f3:=ManyACarryDevelop.buildMany_counts 51 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide) ready.1
 have i1:=unbuildDual_counts (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega)
 have i2:=unbuildTriple_counts (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega)
 have i3:=ManyACarryDevelop.unbuildMany_counts 51 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by decide) ready.1
 simp only [cached_eq L hw,consumed_eq L hw] at f1 i1
 have mt:=cm.proof.toffoli (hosts L) (middle L c) cm.out
 have mm:=cm.proof.measurements (hosts L) (middle L c) cm.out
 have ms:=cm.proof.slots (hosts L) (middle L c) cm.out
 simp only [middle] at mt mm ms
 simp only [newLoop,oldLoop,BThreeTemp.oldLoop,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

theorem newBody_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
 (ready : Ready L c) (cm : CheckedMany (hosts L) (middle L c)) :
 toffoliCount (newBody L c cm)+53≤toffoliCount (ParkCarry10Develop.body L c) ∧
 measurementCount (newBody L c cm)=measurementCount (ParkCarry10Develop.body L c) ∧
 Challenge.gateSlots (newBody L c cm)+159≤Challenge.gateSlots (ParkCarry10Develop.body L c) := by
 have loop:=newLoop_resources L hw c ready cm
 simp only [newLoop,oldLoop,BThreeTemp.oldLoop,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at loop
 simp only [newBody,newFold,newLoop,ParkCarry10Develop.body,ParkCarry10Develop.fold,middle,BThreeTemp.middle,
 toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at loop ⊢
 exact ⟨by omega,by omega,by omega⟩

theorem newLoop_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
 (cm : CheckedMany (hosts L) (middle L c)) : wires (newLoop L c cm)⊆extras L∪wires (oldLoop L c) := by
 have lens:=acc_lengths L hw
 have plen:=pad_length L hw
 have b3:=ManyACarryDevelop.buildMany_support 51 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide)
 have i3:=ManyACarryDevelop.unbuildMany_support 51 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by decide)
 have b2:=buildTriple_support (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega)
 have i2:=unbuildTriple_support (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega)
 have b1:=buildDual_support (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) (by omega)
 have i1:=unbuildDual_support (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega)
 simp only [cached_eq L hw,consumed_eq L hw] at b1 i1
 have mids:=cm.proof.support (hosts L) (middle L c) cm.out
 intro x hx
 simp only [newLoop,wires_append,Finset.mem_union] at hx
 simp only [oldLoop,BThreeTemp.oldLoop,wires_append,Finset.mem_union]
 rcases hx with (hx|hx)|hx
 · rcases Finset.mem_union.mp (b3 hx) with hx|hx
   · rcases Finset.mem_insert.mp (b2 hx) with eq|hx
     · subst x;exact Or.inl (by simp [extras,hosts])
     rcases Finset.mem_insert.mp (b1 hx) with eq|hx
     · subst x;exact Or.inl (by simp [extras,hosts])
     exact Or.inr (Or.inl (Or.inl hx))
   · exact Or.inl (by simpa [extras,hosts] using List.mem_cons_of_mem (hostR L) (List.mem_cons_of_mem (hostP L) (List.mem_toFinset.mp hx)))
 · exact Or.inr (Or.inl (Or.inr (mids.1 hx)))
 · rcases Finset.mem_union.mp (i3 hx) with hx|hx
   · rcases Finset.mem_insert.mp (i2 hx) with eq|hx
     · subst x;exact Or.inl (by simp [extras,hosts])
     rcases Finset.mem_insert.mp (i1 hx) with eq|hx
     · subst x;exact Or.inl (by simp [extras,hosts])
     exact Or.inr (Or.inr hx)
   · exact Or.inl (by simpa [extras,hosts] using List.mem_cons_of_mem (hostR L) (List.mem_cons_of_mem (hostP L) (List.mem_toFinset.mp hx)))
def prefixP (L : CuccaroStreamedSquareWideLayout) : Program :=
  measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++ eAddLo L)
def suffixP (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  ParkCarryDevelop.program (eU L) L.core.sumCarry ++
    (eSubK L ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L))

theorem newBody_shape (L : CuccaroStreamedSquareWideLayout) (c : Wire)
    (cm : CheckedMany (hosts L) (middle L c)) :
    newBody L c cm = prefixP L ++ (newLoop L c cm ++ suffixP L c) := by
  simp only [newBody,newFold,prefixP,suffixP,List.append_assoc]

theorem oldBody_shape (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
    ParkCarry10Develop.body L c = prefixP L ++ (oldLoop L c ++ suffixP L c) := by
  simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,oldLoop,BThreeTemp.oldLoop,middle,BThreeTemp.middle,prefixP,suffixP,List.append_assoc]

theorem newBody_refined (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (cm : CheckedMany (hosts L) (middle L c)) :
    wires (newBody L c cm) ⊆ extras L ∪ wires (ParkCarry10Develop.body L c) := by
  have support := newLoop_support L hw c cm
  rw [newBody_shape,oldBody_shape]
  intro x member
  simp only [wires_append,Finset.mem_union] at member ⊢
  rcases member with before | changed | after
  · exact Or.inr (Or.inl before)
  · rcases Finset.mem_union.mp (support changed) with extra | inside
    · exact Or.inl extra
    · exact Or.inr (Or.inr (Or.inl inside))
  · exact Or.inr (Or.inr (Or.inr after))

theorem newBody_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
 (ready : Ready L c) (cm : CheckedMany (hosts L) (middle L c)) :
 wires (newBody L c cm)⊆wires (ParkCarry10Develop.body L c) := by
 intro x hx
 rcases Finset.mem_union.mp (newBody_refined L hw c cm hx) with hx|hx
 · exact (hasWire_iff _ _).mp (ready.2.2 x (List.mem_toFinset.mp hx)).2.2.2.2
 · exact hx

theorem loop_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) (ready : Ready L c)
 (cm : CheckedMany (hosts L) (middle L c)) (old : GatePhysical (oldLoop L c)) :
 GatePhysical (newLoop L c cm) := by
 have lens:=acc_lengths L hw
 have plen:=pad_length L hw
 have rr:=(host_ready L c ready).1
 have pp:=(host_ready L c ready).2.1
 have uu:=(host_ready L c ready).2.2
 have nd:=loan_ne L c ready
 have offR:=off_cached L hw hn (hostR L) rr.1.2.1 rr.1.2.2.1
 have offP:=off_cached L hw hn (hostP L) pp.1.2.1 pp.1.2.2.1
 have offPDual:hostP L∉wires (buildDual (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) ∧
  hostP L∉wires (unbuildDual (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
  constructor
  · intro h;exact (Finset.mem_insert.mp (buildDual_support _ _ _ _ _ _ _ lens.1 (hiReg_length L hw) (by omega) (by omega) h)).elim nd.2.1 offP.1
  · intro h;exact (Finset.mem_insert.mp (unbuildDual_support _ _ _ _ _ _ _ lens.1 (hiReg_length L hw) (by omega) h)).elim nd.2.1 offP.2
 simp only [oldLoop,BThreeTemp.oldLoop,gatePhysical_append] at old
 have f1:=buildDual_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) (by omega) offR.1 (by simpa only [cached_eq L hw] using old.1.1)
 have i1:=unbuildDual_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) offR.2 (by simpa only [consumed_eq L hw] using old.2)
 have f2:=buildTriple_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) offPDual.1 f1
 have i2:=unbuildTriple_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) offPDual.2 i1
 have fresh:∀x∈loans L,x∉accBank L := by
  intro x hx h;exact (uu x hx).1.2.1 (by simp [h])
 have f3:=ManyACarryDevelop.buildMany_physical 51 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide) fresh f2
 have i3:=ManyACarryDevelop.unbuildMany_physical 51 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by decide) fresh i2
 simpa only [newLoop,gatePhysical_append] using
  And.intro (And.intro f3 (cm.proof.physical (hosts L) (middle L c) cm.out old.1.2)) i3
theorem newBody_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (c : Wire) (hn : (c::L.wires).Nodup) (ready : Ready L c)
    (cm : CheckedMany (hosts L) (middle L c)) : GatePhysical (newBody L c cm) := by
  have old := ParkCarry10Develop.body_physical L hw c hn
  rw [oldBody_shape] at old
  simp only [gatePhysical_append] at old
  rw [newBody_shape]
  simp only [gatePhysical_append]
  exact ⟨old.1,loop_physical L hw (List.nodup_cons.mp hn).2 c ready cm old.2.1,old.2.2⟩

theorem bodyWith_resources (enabled : Bool) (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (c : Wire) :
    toffoliCount (bodyWith enabled L c) ≤ toffoliCount (ParkCarry10Develop.body L c) ∧
    measurementCount (bodyWith enabled L c) = measurementCount (ParkCarry10Develop.body L c) ∧
    Challenge.gateSlots (bodyWith enabled L c) ≤ Challenge.gateSlots (ParkCarry10Develop.body L c) := by
  cases enabled with
  | false => simp only [off_exact]; exact ⟨le_rfl,True.intro,le_rfl⟩
  | true =>
      by_cases ready : Ready L c
      · cases h : checkedMiddle L c with
        | none => simp only [compiler_fallback L c h]; exact ⟨le_rfl,True.intro,le_rfl⟩
        | some cm =>
            have improved := newBody_resources L hw c ready cm
            simp only [bodyWith,if_true,if_pos ready,h]
            exact ⟨by omega,improved.2.1,by omega⟩
      · simp only [geometry_fallback L c ready]; exact ⟨le_rfl,True.intro,le_rfl⟩

theorem bodyWith_support (enabled : Bool) (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (c : Wire) : wires (bodyWith enabled L c) ⊆ wires (ParkCarry10Develop.body L c) := by
  cases enabled with
  | false => exact Finset.Subset.refl _
  | true =>
      by_cases ready : Ready L c
      · cases h : checkedMiddle L c with
        | none => simpa only [compiler_fallback L c h] using Finset.Subset.refl (wires (ParkCarry10Develop.body L c))
        | some cm => simpa only [bodyWith,if_true,if_pos ready,h] using newBody_support L hw c ready cm
      · simpa only [geometry_fallback L c ready] using Finset.Subset.refl (wires (ParkCarry10Develop.body L c))

theorem bodyWith_physical (enabled : Bool) (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (c : Wire) (hn : (c::L.wires).Nodup) : GatePhysical (bodyWith enabled L c) := by
  have old := ParkCarry10Develop.body_physical L hw c hn
  cases enabled with
  | false => exact old
  | true =>
      by_cases ready : Ready L c
      · cases h : checkedMiddle L c with
        | none => simpa only [compiler_fallback L c h] using old
        | some cm => simpa only [bodyWith,if_true,if_pos ready,h] using newBody_physical L hw c hn ready cm
      · simpa only [geometry_fallback L c ready] using old

end ECDSAAdd.Entrant.BWideTemp

end

section
set_option Elab.async false

set_option maxRecDepth 100000

set_option maxHeartbeats 100000000

namespace ECDSAAdd.Entrant.BExtraSteps

open ECDSAAdd ZeroReadDevelop

theorem step0_bool : ParkAOptionBool.optionEq ((compileChunked? 4756 BExtraData.p0).map (fun c=>c.out)) (some BExtraData.p1)=true := by decide +kernel

theorem step0_eq : (compileChunked? 4756 BExtraData.p0).map (fun c=>c.out)=some BExtraData.p1 := ParkAOptionBool.optionEq_sound _ _ step0_bool

theorem step1_bool : ParkAOptionBool.optionEq ((compileChunked? 4728 BExtraData.p1).map (fun c=>c.out)) (some BExtraData.p2)=true := by decide +kernel

theorem step1_eq : (compileChunked? 4728 BExtraData.p1).map (fun c=>c.out)=some BExtraData.p2 := ParkAOptionBool.optionEq_sound _ _ step1_bool

theorem step2_bool : ParkAOptionBool.optionEq ((compileChunked? 4729 BExtraData.p2).map (fun c=>c.out)) (some BExtraData.p3)=true := by decide +kernel

theorem step2_eq : (compileChunked? 4729 BExtraData.p2).map (fun c=>c.out)=some BExtraData.p3 := ParkAOptionBool.optionEq_sound _ _ step2_bool

theorem step3_bool : ParkAOptionBool.optionEq ((compileChunked? 4730 BExtraData.p3).map (fun c=>c.out)) (some BExtraData.p4)=true := by decide +kernel

theorem step3_eq : (compileChunked? 4730 BExtraData.p3).map (fun c=>c.out)=some BExtraData.p4 := ParkAOptionBool.optionEq_sound _ _ step3_bool

theorem step4_bool : ParkAOptionBool.optionEq ((compileChunked? 4731 BExtraData.p4).map (fun c=>c.out)) (some BExtraData.p5)=true := by decide +kernel

theorem step4_eq : (compileChunked? 4731 BExtraData.p4).map (fun c=>c.out)=some BExtraData.p5 := ParkAOptionBool.optionEq_sound _ _ step4_bool

theorem step5_bool : ParkAOptionBool.optionEq ((compileChunked? 4732 BExtraData.p5).map (fun c=>c.out)) (some BExtraData.p6)=true := by decide +kernel

theorem step5_eq : (compileChunked? 4732 BExtraData.p5).map (fun c=>c.out)=some BExtraData.p6 := ParkAOptionBool.optionEq_sound _ _ step5_bool

theorem step6_bool : ParkAOptionBool.optionEq ((compileChunked? 4733 BExtraData.p6).map (fun c=>c.out)) (some BExtraData.p7)=true := by decide +kernel

theorem step6_eq : (compileChunked? 4733 BExtraData.p6).map (fun c=>c.out)=some BExtraData.p7 := ParkAOptionBool.optionEq_sound _ _ step6_bool

theorem step7_bool : ParkAOptionBool.optionEq ((compileChunked? 4734 BExtraData.p7).map (fun c=>c.out)) (some BExtraData.p8)=true := by decide +kernel

theorem step7_eq : (compileChunked? 4734 BExtraData.p7).map (fun c=>c.out)=some BExtraData.p8 := ParkAOptionBool.optionEq_sound _ _ step7_bool

theorem step8_bool : ParkAOptionBool.optionEq ((compileChunked? 4735 BExtraData.p8).map (fun c=>c.out)) (some BExtraData.p9)=true := by decide +kernel

theorem step8_eq : (compileChunked? 4735 BExtraData.p8).map (fun c=>c.out)=some BExtraData.p9 := ParkAOptionBool.optionEq_sound _ _ step8_bool

theorem step9_bool : ParkAOptionBool.optionEq ((compileChunked? 4736 BExtraData.p9).map (fun c=>c.out)) (some BExtraData.p10)=true := by decide +kernel

theorem step9_eq : (compileChunked? 4736 BExtraData.p9).map (fun c=>c.out)=some BExtraData.p10 := ParkAOptionBool.optionEq_sound _ _ step9_bool

theorem step10_bool : ParkAOptionBool.optionEq ((compileChunked? 4737 BExtraData.p10).map (fun c=>c.out)) (some BExtraData.p11)=true := by decide +kernel

theorem step10_eq : (compileChunked? 4737 BExtraData.p10).map (fun c=>c.out)=some BExtraData.p11 := ParkAOptionBool.optionEq_sound _ _ step10_bool

theorem step11_bool : ParkAOptionBool.optionEq ((compileChunked? 4738 BExtraData.p11).map (fun c=>c.out)) (some BExtraData.p12)=true := by decide +kernel

theorem step11_eq : (compileChunked? 4738 BExtraData.p11).map (fun c=>c.out)=some BExtraData.p12 := ParkAOptionBool.optionEq_sound _ _ step11_bool

theorem step12_bool : ParkAOptionBool.optionEq ((compileChunked? 4739 BExtraData.p12).map (fun c=>c.out)) (some BExtraData.p13)=true := by decide +kernel

theorem step12_eq : (compileChunked? 4739 BExtraData.p12).map (fun c=>c.out)=some BExtraData.p13 := ParkAOptionBool.optionEq_sound _ _ step12_bool

theorem step13_bool : ParkAOptionBool.optionEq ((compileChunked? 4740 BExtraData.p13).map (fun c=>c.out)) (some BExtraData.p14)=true := by decide +kernel

theorem step13_eq : (compileChunked? 4740 BExtraData.p13).map (fun c=>c.out)=some BExtraData.p14 := ParkAOptionBool.optionEq_sound _ _ step13_bool

theorem step14_bool : ParkAOptionBool.optionEq ((compileChunked? 4741 BExtraData.p14).map (fun c=>c.out)) (some BExtraData.p15)=true := by decide +kernel

theorem step14_eq : (compileChunked? 4741 BExtraData.p14).map (fun c=>c.out)=some BExtraData.p15 := ParkAOptionBool.optionEq_sound _ _ step14_bool

theorem step15_bool : ParkAOptionBool.optionEq ((compileChunked? 4742 BExtraData.p15).map (fun c=>c.out)) (some BExtraData.p16)=true := by decide +kernel

theorem step15_eq : (compileChunked? 4742 BExtraData.p15).map (fun c=>c.out)=some BExtraData.p16 := ParkAOptionBool.optionEq_sound _ _ step15_bool

theorem step16_bool : ParkAOptionBool.optionEq ((compileChunked? 4743 BExtraData.p16).map (fun c=>c.out)) (some BExtraData.p17)=true := by decide +kernel

theorem step16_eq : (compileChunked? 4743 BExtraData.p16).map (fun c=>c.out)=some BExtraData.p17 := ParkAOptionBool.optionEq_sound _ _ step16_bool

theorem step17_bool : ParkAOptionBool.optionEq ((compileChunked? 4744 BExtraData.p17).map (fun c=>c.out)) (some BExtraData.p18)=true := by decide +kernel

theorem step17_eq : (compileChunked? 4744 BExtraData.p17).map (fun c=>c.out)=some BExtraData.p18 := ParkAOptionBool.optionEq_sound _ _ step17_bool

theorem step18_bool : ParkAOptionBool.optionEq ((compileChunked? 4745 BExtraData.p18).map (fun c=>c.out)) (some BExtraData.p19)=true := by decide +kernel

theorem step18_eq : (compileChunked? 4745 BExtraData.p18).map (fun c=>c.out)=some BExtraData.p19 := ParkAOptionBool.optionEq_sound _ _ step18_bool

theorem step19_bool : ParkAOptionBool.optionEq ((compileChunked? 4746 BExtraData.p19).map (fun c=>c.out)) (some BExtraData.p20)=true := by decide +kernel

theorem step19_eq : (compileChunked? 4746 BExtraData.p19).map (fun c=>c.out)=some BExtraData.p20 := ParkAOptionBool.optionEq_sound _ _ step19_bool

theorem step20_bool : ParkAOptionBool.optionEq ((compileChunked? 4747 BExtraData.p20).map (fun c=>c.out)) (some BExtraData.p21)=true := by decide +kernel

theorem step20_eq : (compileChunked? 4747 BExtraData.p20).map (fun c=>c.out)=some BExtraData.p21 := ParkAOptionBool.optionEq_sound _ _ step20_bool

theorem step21_bool : ParkAOptionBool.optionEq ((compileChunked? 4748 BExtraData.p21).map (fun c=>c.out)) (some BExtraData.p22)=true := by decide +kernel

theorem step21_eq : (compileChunked? 4748 BExtraData.p21).map (fun c=>c.out)=some BExtraData.p22 := ParkAOptionBool.optionEq_sound _ _ step21_bool

theorem step22_bool : ParkAOptionBool.optionEq ((compileChunked? 4749 BExtraData.p22).map (fun c=>c.out)) (some BExtraData.p23)=true := by decide +kernel

theorem step22_eq : (compileChunked? 4749 BExtraData.p22).map (fun c=>c.out)=some BExtraData.p23 := ParkAOptionBool.optionEq_sound _ _ step22_bool

theorem step23_bool : ParkAOptionBool.optionEq ((compileChunked? 4750 BExtraData.p23).map (fun c=>c.out)) (some BExtraData.p24)=true := by decide +kernel

theorem step23_eq : (compileChunked? 4750 BExtraData.p23).map (fun c=>c.out)=some BExtraData.p24 := ParkAOptionBool.optionEq_sound _ _ step23_bool

theorem step24_bool : ParkAOptionBool.optionEq ((compileChunked? 4751 BExtraData.p24).map (fun c=>c.out)) (some BExtraData.p25)=true := by decide +kernel

theorem step24_eq : (compileChunked? 4751 BExtraData.p24).map (fun c=>c.out)=some BExtraData.p25 := ParkAOptionBool.optionEq_sound _ _ step24_bool

theorem step25_bool : ParkAOptionBool.optionEq ((compileChunked? 4752 BExtraData.p25).map (fun c=>c.out)) (some BExtraData.p26)=true := by decide +kernel

theorem step25_eq : (compileChunked? 4752 BExtraData.p25).map (fun c=>c.out)=some BExtraData.p26 := ParkAOptionBool.optionEq_sound _ _ step25_bool

theorem step26_bool : ParkAOptionBool.optionEq ((compileChunked? 4753 BExtraData.p26).map (fun c=>c.out)) (some BExtraData.p27)=true := by decide +kernel

theorem step26_eq : (compileChunked? 4753 BExtraData.p26).map (fun c=>c.out)=some BExtraData.p27 := ParkAOptionBool.optionEq_sound _ _ step26_bool

theorem step27_bool : ParkAOptionBool.optionEq ((compileChunked? 4754 BExtraData.p27).map (fun c=>c.out)) (some BExtraData.p28)=true := by decide +kernel

theorem step27_eq : (compileChunked? 4754 BExtraData.p27).map (fun c=>c.out)=some BExtraData.p28 := ParkAOptionBool.optionEq_sound _ _ step27_bool

theorem step28_bool : ParkAOptionBool.optionEq ((compileChunked? 4755 BExtraData.p28).map (fun c=>c.out)) (some BExtraData.p29)=true := by decide +kernel

theorem step28_eq : (compileChunked? 4755 BExtraData.p28).map (fun c=>c.out)=some BExtraData.p29 := ParkAOptionBool.optionEq_sound _ _ step28_bool

theorem chain : ParkAChain.Steps [4756,4728,4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755] BExtraData.p0 BExtraData.p29 := .cons 4756 _ _ _ _ step0_eq (.cons 4728 _ _ _ _ step1_eq (.cons 4729 _ _ _ _ step2_eq (.cons 4730 _ _ _ _ step3_eq (.cons 4731 _ _ _ _ step4_eq (.cons 4732 _ _ _ _ step5_eq (.cons 4733 _ _ _ _ step6_eq (.cons 4734 _ _ _ _ step7_eq (.cons 4735 _ _ _ _ step8_eq (.cons 4736 _ _ _ _ step9_eq (.cons 4737 _ _ _ _ step10_eq (.cons 4738 _ _ _ _ step11_eq (.cons 4739 _ _ _ _ step12_eq (.cons 4740 _ _ _ _ step13_eq (.cons 4741 _ _ _ _ step14_eq (.cons 4742 _ _ _ _ step15_eq (.cons 4743 _ _ _ _ step16_eq (.cons 4744 _ _ _ _ step17_eq (.cons 4745 _ _ _ _ step18_eq (.cons 4746 _ _ _ _ step19_eq (.cons 4747 _ _ _ _ step20_eq (.cons 4748 _ _ _ _ step21_eq (.cons 4749 _ _ _ _ step22_eq (.cons 4750 _ _ _ _ step23_eq (.cons 4751 _ _ _ _ step24_eq (.cons 4752 _ _ _ _ step25_eq (.cons 4753 _ _ _ _ step26_eq (.cons 4754 _ _ _ _ step27_eq (.cons 4755 _ _ _ _ step28_eq (.nil _)))))))))))))))))))))))))))))

end ECDSAAdd.Entrant.BExtraSteps

end

section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ECDSAAdd.Entrant.BWideStaged
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ZeroReadDevelop BWideTemp

def L := BThreeStaged301.L
def c := BThreeStaged301.c

theorem append {qs rs : List Wire} {p r t : Program}
 (h : ParkAChain.Steps qs p r) (k : ParkAChain.Steps rs r t) :
 ParkAChain.Steps (qs++rs) p t := by
 induction h with
 | nil => exact k
 | cons q qs p r u head tail ih => exact .cons q _ _ _ _ head (ih k)

theorem hosts_eq : hosts L = [4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4694,4695,4696,4756,4728,4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755] := by decide +kernel
 def suffix : List Wire := [4756,4728,4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755]
theorem hosts_split : hosts L = [4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4694,4695,4696] ++ suffix := by decide +kernel
theorem prefix_chain : ParkAChain.Steps [4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4694,4695,4696] BData301.p0 BManyData.p22 :=
 .cons 4672 _ _ _ _ BThreeStaged301.step0_eq (.cons 4673 _ _ _ _ BThreeStaged301.step1_eq BManySteps.chain)
theorem tail_compiled : (compileManyChunked? suffix BManyData.p22).isSome=true :=
 ParkAChain.isSome _ _ _ BExtraSteps.chain
theorem actual_compiled : (compileManyChunked? (hosts L) (middle L c)).isSome=true := by
 have allSome:=ParkAChain.extend_isSome prefix_chain tail_compiled
 rw [hosts_split]
 exact BThreeStaged301.compilerSome_transport _ _ _ BThreeStaged301.input_eq allSome

theorem used_data : ∀x∈hosts L,FourthASavedCarryDevelop.hasWire BData301.p0 x=true := by
 rw [hosts_eq]
 decide +kernel

theorem geometry : ∀x∈hosts L,LoanReadyTrim L c x ∧ x∉ControlLoan1589BFFold.mR L ∧ x≠ControlLoan1589BFFold.w192 L ∧ x≠c := by
 rw [hosts_eq]
 unfold LoanReadyTrim
 decide +kernel

private theorem hasWire_transport (p q : Program) (e : p=q) (x : Wire)
 (h : FourthASavedCarryDevelop.hasWire p x=true) :
 FourthASavedCarryDevelop.hasWire q x=true := e ▸ h
private theorem hasWire_middle_to_body (K : CuccaroStreamedSquareWideLayout) (g x : Wire)
 (h : FourthASavedCarryDevelop.hasWire (middle K g) x=true) :
 FourthASavedCarryDevelop.hasWire (ParkCarry10Develop.body K g) x=true := by
 apply (FourthASavedCarryDevelop.hasWire_iff _ _).mpr
 exact BWideTemp.middle_subset_old K g ((FourthASavedCarryDevelop.hasWire_iff _ _).mp h)

theorem actual_ready : Ready L c := by
 refine ⟨by decide +kernel,by decide +kernel,?_⟩
 intro x hx
 have g:=geometry x hx
 exact ⟨g.1,g.2.1,g.2.2.1,g.2.2.2,
   hasWire_middle_to_body L c x (hasWire_transport _ _ BThreeStaged301.input_eq x (used_data x hx))⟩
#print axioms actual_compiled
#print axioms actual_ready
end ECDSAAdd.Entrant.BWideStaged

end
