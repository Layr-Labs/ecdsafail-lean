import ECDSAAdd.Submission.Entrant.FullLogic
import ECDSAAdd.Submission.Entrant.MainPart04

section

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.WholePadConcrete
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
 def oldCachedBuild := buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
 def newCachedBuild := buildCached (accReg L) pad (accBank L) L.core.cin (hiReg L) L.core.sumCarry
 def oldCachedUnbuild := unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
 def newCachedUnbuild := unbuildConsumed (accReg L) pad (accBank L) L.core.cin (hiReg L) L.core.sumCarry
 theorem cached_build_counts : SeedPadDevelop.Counts newCachedBuild oldCachedBuild := by unfold SeedPadDevelop.Counts; decide +kernel
 theorem cached_unbuild_counts : SeedPadDevelop.Counts newCachedUnbuild oldCachedUnbuild := by unfold SeedPadDevelop.Counts; decide +kernel
#print axioms cached_build_counts
#print axioms cached_unbuild_counts
end ECDSAAdd.Entrant.WholePadConcrete

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullBMeta
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
 def MetricReady (L:CuccaroStreamedSquareWideLayout):Prop :=
 SeedPadDevelop.Counts
  (buildCached (accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
  (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) ∧
 SeedPadDevelop.Counts
  (unbuildConsumed (accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
  (unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
 instance (L:CuccaroStreamedSquareWideLayout):Decidable (MetricReady L):=by
  unfold MetricReady SeedPadDevelop.Counts
  infer_instance
 theorem actual_metric : MetricReady Baselines.layout.dialogStreamedSquareWide :=
  ⟨WholePadConcrete.cached_build_counts, WholePadConcrete.cached_unbuild_counts⟩
 def supportDomain (L:CuccaroStreamedSquareWideLayout):List Wire :=
  BThreeTemp.hostP L::BThreeTemp.hostR L::L.core.sumCarry::L.core.cin::(hiReg L++accReg L++FullPadDevelop.pad L++accBank L)
 def SupportReady (L:CuccaroStreamedSquareWideLayout) (c:Wire):Prop :=
  ∀w∈supportDomain L,hasWire (ParkCarry10Develop.body L c) w=true
 instance (L:CuccaroStreamedSquareWideLayout) (c:Wire):Decidable (SupportReady L c):=by
  unfold SupportReady
  infer_instance
 def L := Baselines.layout.dialogStreamedSquareWide
 def c := Baselines.layout.core.generic

end ECDSAAdd.Entrant.FullBMeta

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullBMeta
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
 theorem used0 : ∀w∈((supportDomain L).drop 0).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel
#print axioms used0
 theorem used1 : ∀w∈((supportDomain L).drop 80).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel
#print axioms used1
 theorem used2 : ∀w∈((supportDomain L).drop 160).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel
#print axioms used2
 theorem used3 : ∀w∈((supportDomain L).drop 240).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel
#print axioms used3
 theorem used4 : ∀w∈((supportDomain L).drop 320).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel
#print axioms used4
 theorem used5 : ∀w∈((supportDomain L).drop 400).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel
#print axioms used5
 theorem used6 : ∀w∈((supportDomain L).drop 480).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel
#print axioms used6
 theorem domain_split : supportDomain L = ((supportDomain L).drop 0).take 80 ++ ((supportDomain L).drop 80).take 80 ++ ((supportDomain L).drop 160).take 80 ++ ((supportDomain L).drop 240).take 80 ++ ((supportDomain L).drop 320).take 80 ++ ((supportDomain L).drop 400).take 80 ++ ((supportDomain L).drop 480).take 80 := by decide +kernel
 theorem actual_support_ready : SupportReady L c := by
  unfold SupportReady
  rw [domain_split]
  simp only [List.mem_append,or_imp,forall_and]
  exact ⟨⟨⟨⟨⟨⟨used0, used1⟩, used2⟩, used3⟩, used4⟩, used5⟩, used6⟩
#print axioms actual_metric
#print axioms actual_support_ready
end ECDSAAdd.Entrant.FullBMeta

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FullBTemp
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop

def hostR := BThreeTemp.hostR
def hostP := BThreeTemp.hostP
                             
def pad (L : CuccaroStreamedSquareWideLayout) : List Wire := FullPadDevelop.pad L

def loans (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 (L.core.work.drop 173).take 19 ++ (L.core.work.drop 193).take 3 ++ (L.core.work.drop 255).take 1 ++ (L.core.work.drop 227).take 28 ++ (L.core.work.drop 201).take 11 ++ (L.core.work.drop 213).take 14 ++ (L.core.work.drop 212).take 1 ++ (L.core.work.drop 196).take 5
def hosts (L : CuccaroStreamedSquareWideLayout) : List Wire := hostR L::hostP L::loans L
def middle := BThreeTemp.middle
def LoanReadyTrim (L : CuccaroStreamedSquareWideLayout) (g u : Wire) : Prop :=
 u∈L.core.work ∧ u∉L.core.cin::(hiReg L++accReg L++pad L++accBank L) ∧
 u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L ∧ True
def HostReady (L : CuccaroStreamedSquareWideLayout) (c x : Wire) : Prop :=
 LoanReadyTrim L c x ∧ x∉mR L ∧ x≠w192 L ∧ x≠c ∧ hasWire (ParkCarry10Develop.body L c) x=true
def PadReady (L:CuccaroStreamedSquareWideLayout) (c:Wire):Prop :=
 FullBMeta.MetricReady L ∧ FullFitReady.Ready L ∧ FullBMeta.SupportReady L c
def Ready (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Prop :=
 (loans L).length=82 ∧ (L.core.sumCarry::hosts L).Nodup ∧ (∀x∈hosts L,HostReady L c x) ∧ PadReady L c
instance (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Decidable (Ready L c) := by
 unfold Ready HostReady LoanReadyTrim PadReady
 unfold pad
 infer_instance

def checkedMiddle (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 Option (ZeroSetDevelop.CheckedS (hosts L) (middle L c)) := ZeroSetDevelop.compileS? (hosts L) (middle L c)
def oldLoop := BThreeTemp.oldLoop
def newLoop (L : CuccaroStreamedSquareWideLayout) (c : Wire)
 (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) : Program :=
 ManyACarryDevelop.buildMany 82 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  (loans L) L.core.sumCarry (hostR L) (hostP L) ++ cm.out ++
 ManyACarryDevelop.unbuildMany 82 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  (loans L) L.core.sumCarry (hostR L) (hostP L)
def newFold (L : CuccaroStreamedSquareWideLayout) (c : Wire)
 (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) : Program :=
 eAddLo L ++ (newLoop L c cm ++ (ParkCarryDevelop.program (eU L) L.core.sumCarry ++ eSubK L))
def newBody (L : CuccaroStreamedSquareWideLayout) (c : Wire)
 (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) : Program :=
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
 exact ⟨h.2.2.1 _ (by simp [hosts]),h.2.2.1 _ (by simp [hosts]),fun x hx=>h.2.2.1 x (by simp [hosts,hx])⟩
theorem loan_ne (L : CuccaroStreamedSquareWideLayout) (c : Wire) (h : Ready L c) :
 (loans L).Nodup ∧ hostP L≠hostR L ∧ ∀x∈loans L,x≠L.core.sumCarry ∧ x≠hostR L ∧ x≠hostP L := by
 have nd := h.2.1
 change (L.core.sumCarry::hostR L::hostP L::loans L).Nodup at nd
 simp only [List.nodup_cons,List.mem_cons,not_or] at nd
 refine ⟨nd.2.2.2,fun e=>nd.2.1.1 e.symm,?_⟩
 intro x hx
 exact ⟨fun e=>nd.1.2.2 (e ▸ hx),fun e=>nd.2.1.2 (e ▸ hx),fun e=>nd.2.2.1 (e ▸ hx)⟩

theorem pad_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : 5≤(pad L).length := by
 rw [pad,FullPadDevelop.pad_length L hw]
 decide
 theorem terms_fits (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (accReg L) (pad L) (accBank L) L.core.cin 163 f :=
 FullPadDevelop.terms_fits L hw hn
 theorem sumCarry_trim (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
 L.core.sumCarry ∉ L.core.cin::(hiReg L++accReg L++pad L++accBank L) := by
 intro h
 exact sumCarry_fresh_domain L hn ((FullPadDevelop.domain_sublist L _).subset h)
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


theorem loop_bstate_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) (hcw : c∉L.wires) (ready : Ready L c)
 (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c))
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
 have hz:∀w∈pad L,s.basis w=false := fun w hw=>hzFull w ((FullPadDevelop.pad_sublist L).subset hw)
 have source0:regValue (hiReg L) s.basis=regValue (hiReg L) base := regValue_congr _ _ _ (fun q hq=>bstate_other L hn base O E 0 s.basis hs q (Or.inl hq))
 have goodFull:WReady (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (regValue (hiReg L) s.basis)
  (middleState (wBuild L) (middle L c) s records) := by
  let first:=run (wBuild L) (records.take (measurementCount (wBuild L))) s
  have firstGood:=(wBuild_step L hw hn base clean O E) s (records.take (measurementCount (wBuild L))) hs
  have midGood:=mid first ((records.drop (measurementCount (wBuild L))).take (measurementCount (middle L c))) firstGood.2
  obtain ⟨mz,mb,mi,_,_⟩:=zero_regs L hn base clean O' E _ _ midGood.2
  have source1:=regValue_congr (hiReg L) _ base (fun q hq=>bstate_other L hn base O' E _ _ midGood.2 q (Or.inl hq))
  exact ⟨midGood.2.2.2.1.trans (by rw [source0]),source1.trans source0.symm,mz,mb,mi⟩
 have midPadEq:=WholePadDevelop.middle_repad (accReg L) (accZ L) (pad L) (accBank L) L.core.cin
  (hiReg L) (middle L c) lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) (terms_fits L hw hn)
  s records hzFull hz hb hi hs.2.2.1
 have good:WReady (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (regValue (hiReg L) s.basis)
  (middleState (NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)) (middle L c) s records) := by
  rw [←midPadEq]
  exact ⟨goodFull.1,goodFull.2.1,(fun w hw=>goodFull.2.2.1 w ((FullPadDevelop.pad_sublist L).subset hw)),goodFull.2.2.2⟩
 have zeros:∀x∈hosts L,s.basis x=false := by
  intro x hx; simp only [hosts,List.mem_cons] at hx
  rcases hx with rfl|rfl|hx
  · exact zeroR
  · exact zeroP
  · exact zeroU x hx
 have offOriginal:∀x∈hosts L,x∉wires (NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)) := by
  intro x hx
  exact (wloop_original_off _ _ _ _ _ _ lens.1 (hiReg_length L hw) (terms_fits L hw hn) (ready.2.2.1 x hx).1.2.1).1
 have midEq:=cm.proof.middle_eq (hosts L) (middle L c) cm.out (NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)) s records zeros offOriginal
 have goodNew:WReady (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (regValue (hiReg L) s.basis)
  (middleState (NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)) cm.out s records) := by rw [midEq];exact good
 have support:=cm.proof.support (hosts L) (middle L c) cm.out
 have nq:L.core.sumCarry∉wires cm.out := fun h=>offMiddle (support.1 h)
 have nr:hostR L∉wires cm.out := support.2 _ (by simp [hosts])
 have np:hostP L∉wires cm.out := support.2 _ (by simp [hosts])
 have triple:=triple_middle_ready (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (hostR L) (hostP L) cm.out lens.1 (hiReg_length L hw) (terms_fits L hw hn)
  s records hz hb hi hs.2.2.1 zeroQ zeroR zeroP freshQ rr.1.2.1 rr.1.2.2.1 pp.1.2.1 pp.1.2.2.1 nd.2.1
  offQ.1 nq offQ.2 offR.1 nr offR.2 pF np pI goodNew
 have many:=ManyACarryDevelop.cached_wloop_many_eq 82 (accReg L) (pad L) (accBank L) L.core.cin
  (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) cm.out lens.1 (hiReg_length L hw)
  (terms_fits L hw hn) s records hz hb hi hs.2.2.1 zeroQ zeroR zeroP zeroU freshQ rr.1.2.1 rr.1.2.2.1
  pp.1.2.1 pp.1.2.2.1 nd.2.1 (by decide) nd.1 ready.1 (fun x hx=>(uu x hx).1.2.1) nd.2.2
  offQ.1 offQ.2 offR.1 offR.2 pF pI (fun x hx=>(endpoints x hx).1)
  (fun x hx=>support.2 x (by simp [hosts,hx])) (fun x hx=>(endpoints x hx).2)
  triple.1 triple.2.1 triple.2.2.1 triple.2.2.2
 have tr:=cached_wloop_triple_eq (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (hostR L) (hostP L) cm.out lens.1 (hiReg_length L hw) (terms_fits L hw hn)
  s records hz hb hi hs.2.2.1 zeroQ zeroR zeroP freshQ rr.1.2.1 rr.1.2.2.1 pp.1.2.1 pp.1.2.2.1 nd.2.1
  offQ.1 nq offQ.2 offR.1 nr offR.2 pF np pI goodNew
 have du:=cached_wloop_dual_eq (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (hostR L) cm.out lens.1 (hiReg_length L hw) (terms_fits L hw hn)
  s records hz hb hi hs.2.2.1 zeroQ zeroR freshQ rr.1.2.1 rr.1.2.2.1 offQ.1 nq offQ.2 offR.1 nr offR.2 goodNew
 have re:=cm.proof.surround_eq (hosts L) (middle L c) cm.out (NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L))
  (SourceAddFourDevelop.unbuild (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)) s records zeros offOriginal
 have origOff:=b_wloop_sumCarry_free L hw hn c hcw
 have ca:=cached_wloop_eq (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (middle L c) lens.1 (hiReg_length L hw) (wTerms_fits L hw hn)
  s records hzFull hb hi hs.2.2.1 zeroQ (sumCarry_fresh_domain L hn)
  origOff.1 offMiddle origOff.2.2 goodFull
 have repad:=WholePadDevelop.plain_loop_repad (accReg L) (accZ L) (pad L) (accBank L) L.core.cin
  (hiReg L) (middle L c) lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) (terms_fits L hw hn)
  (FullPadDevelop.pad_sublist L).subset s records hzFull hb hi hs.2.2.1 (regValue (hiReg L) s.basis)
  (by simpa only [wBuild,middleState,run_take] using goodFull)
 simpa only [newLoop,oldLoop,BThreeTemp.oldLoop] using many.trans (tr.trans (du.trans (re.trans (repad.symm.trans ca.symm))))

#print axioms loop_bstate_eq
theorem loop_bstate_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (c : Wire) (hcw : c ∉ L.wires) (ready : Ready L c)
    (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c))
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
    (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) (base : BasisState) (M : Nat) (hM : M<2^128)
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



                                                                                                     

theorem newLoop_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
 (ready : Ready L c) (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) :
 toffoliCount (newLoop L c cm)+84≤toffoliCount (oldLoop L c) ∧
 measurementCount (newLoop L c cm)=measurementCount (oldLoop L c) ∧
 Challenge.gateSlots (newLoop L c cm)+252≤Challenge.gateSlots (oldLoop L c) := by
 have lens:=acc_lengths L hw
 have plen:=pad_length L hw
 have f1:=buildDual_counts (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) (by omega)
 have f2:=buildTriple_counts (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega)
 have f3:=ManyACarryDevelop.buildMany_counts 82 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide) ready.1
 have i1:=unbuildDual_counts (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega)
 have i2:=unbuildTriple_counts (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega)
 have i3:=ManyACarryDevelop.unbuildMany_counts 82 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by decide) ready.1
 have f4 := ready.2.2.2.1.1
 have i4 := ready.2.2.2.1.2
 change SeedPadDevelop.Counts (buildCached (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
  (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) at f4
 change SeedPadDevelop.Counts (unbuildConsumed (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
  (unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) at i4
 simp only [f4.1,f4.2.1,f4.2.2,i4.1,i4.2.1,i4.2.2] at f1 i1
 have mt:=cm.proof.toffoli (hosts L) (middle L c) cm.out
 have mm:=cm.proof.measurements (hosts L) (middle L c) cm.out
 have ms:=cm.proof.slots (hosts L) (middle L c) cm.out
 simp only [middle] at mt mm ms
 simp only [newLoop,oldLoop,BThreeTemp.oldLoop,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

theorem newBody_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
 (ready : Ready L c) (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) :
 toffoliCount (newBody L c cm)+84≤toffoliCount (ParkCarry10Develop.body L c) ∧
 measurementCount (newBody L c cm)=measurementCount (ParkCarry10Develop.body L c) ∧
 Challenge.gateSlots (newBody L c cm)+252≤Challenge.gateSlots (ParkCarry10Develop.body L c) := by
 have loop:=newLoop_resources L hw c ready cm
 simp only [newLoop,oldLoop,BThreeTemp.oldLoop,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at loop
 simp only [newBody,newFold,newLoop,ParkCarry10Develop.body,ParkCarry10Develop.fold,middle,BThreeTemp.middle,
 toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at loop ⊢
 exact ⟨by omega,by omega,by omega⟩

theorem newLoop_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire)
 (ready:Ready L c) (cm:ZeroSetDevelop.CheckedS (hosts L) (middle L c)):
 wires (newLoop L c cm) ⊆ wires (ParkCarry10Develop.body L c) := by
 have lens:=acc_lengths L hw
 have plen:=pad_length L hw
 have bf:=ManyACarryDevelop.buildMany_support 82 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L)
  L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide)
 have bi:=ManyACarryDevelop.unbuildMany_support 82 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L)
  L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by decide)
 have tri:=WholePadTriple.support (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (FullFitReady.sound L ready.2.2.2.2.1)
 have dom (x:Wire) (hx:x∈(hostP L::hostR L::L.core.sumCarry::L.core.cin::(hiReg L++accReg L++pad L++accBank L)).toFinset):
  x∈wires (ParkCarry10Develop.body L c) := by
  apply (hasWire_iff _ _).mp
  apply ready.2.2.2.2.2 x
  exact List.mem_toFinset.mp hx
 have mid : wires (middle L c) ⊆ wires (ParkCarry10Develop.body L c) := by
  intro x hx
  simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,middle,BThreeTemp.middle,wires_append,Finset.mem_union] at hx ⊢
  aesop
 have used (x:Wire) (hx:x∈(loans L).toFinset):x∈wires (ParkCarry10Develop.body L c) :=
  (hasWire_iff _ _).mp (ready.2.2.1 x (by simp [hosts,List.mem_toFinset.mp hx])).2.2.2.2
 intro x hx
 simp only [newLoop,wires_append,Finset.mem_union] at hx
 rcases hx with (hx|hx)|hx
 · rcases Finset.mem_union.mp (bf hx) with hx|hx
   · exact dom x (tri.1 hx)
   · exact used x hx
 · exact mid ((cm.proof.support (hosts L) (middle L c) cm.out).1 hx)
 · rcases Finset.mem_union.mp (bi hx) with hx|hx
   · exact dom x (tri.2 hx)
   · exact used x hx

def prefixP (L : CuccaroStreamedSquareWideLayout) : Program :=
  measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++ eAddLo L)
def suffixP (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  ParkCarryDevelop.program (eU L) L.core.sumCarry ++
    (eSubK L ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L))

theorem newBody_shape (L : CuccaroStreamedSquareWideLayout) (c : Wire)
    (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) :
    newBody L c cm = prefixP L ++ (newLoop L c cm ++ suffixP L c) := by
  simp only [newBody,newFold,prefixP,suffixP,List.append_assoc]

theorem oldBody_shape (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
    ParkCarry10Develop.body L c = prefixP L ++ (oldLoop L c ++ suffixP L c) := by
  simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,oldLoop,BThreeTemp.oldLoop,middle,BThreeTemp.middle,prefixP,suffixP,List.append_assoc]

theorem newBody_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire)
 (ready:Ready L c) (cm:ZeroSetDevelop.CheckedS (hosts L) (middle L c)):
 wires (newBody L c cm)⊆wires (ParkCarry10Develop.body L c) := by
 have loop:=newLoop_support L hw c ready cm
 have shape:=oldBody_shape L c
 rw [newBody_shape]
 intro x hx
 simp only [wires_append,Finset.mem_union] at hx
 rcases hx with before|changed|after
 · rw [shape];simp only [wires_append,Finset.mem_union];exact Or.inl before
 · exact loop changed
 · rw [shape];simp only [wires_append,Finset.mem_union];exact Or.inr (Or.inr after)

theorem loop_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) (ready : Ready L c)
 (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) (old : GatePhysical (oldLoop L c)) :
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
 have plainF:=(NarrowAcc.build8_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) lens.1 (by rw [hiReg_length L hw]) (terms_fits L hw hn)).1
 have plainI:=SourceAddFourDevelop.unbuild_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) lens.1 (hiReg_length L hw) (terms_fits L hw hn)
 have offQ:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry lens.1 (hiReg_length L hw) (terms_fits L hw hn) ?_
 · have cachedF:=buildCached_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry lens.1 (hiReg_length L hw) (by omega) (by omega) offQ.1 plainF
   have cachedI:=unbuildConsumed_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry lens.1 (hiReg_length L hw) (by omega) offQ.2 plainI
   rw [oldLoop,BThreeTemp.oldLoop,gatePhysical_append,gatePhysical_append] at old
   have old : (GatePhysical (buildCached (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) ∧ GatePhysical (middle L c)) ∧ GatePhysical (unbuildConsumed (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := ⟨⟨cachedF,old.1.2⟩,cachedI⟩
   have f1:=buildDual_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) (by omega) offR.1 old.1.1
   have i1:=unbuildDual_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) offR.2 old.2
   have f2:=buildTriple_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) offPDual.1 f1
   have i2:=unbuildTriple_physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) offPDual.2 i1
   have fresh:∀x∈loans L,x∉accBank L := by
    intro x hx h;exact (uu x hx).1.2.1 (by simp [h])
   have f3:=ManyACarryDevelop.buildMany_physical 82 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide) fresh f2
   have i3:=ManyACarryDevelop.unbuildMany_physical 82 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by decide) fresh i2
   simpa only [newLoop,gatePhysical_append] using
    And.intro (And.intro f3 (cm.proof.physical (hosts L) (middle L c) cm.out old.1.2)) i3
 · intro h
   exact sumCarry_fresh_domain L hn ((FullPadDevelop.domain_sublist L _).subset h)

theorem newBody_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (c : Wire) (hn : (c::L.wires).Nodup) (ready : Ready L c)
    (cm : ZeroSetDevelop.CheckedS (hosts L) (middle L c)) : GatePhysical (newBody L c cm) := by
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


end ECDSAAdd.Entrant.FullBTemp

end

section
open ECDSAAdd ECDSAAdd.Entrant ZeroReadDevelop
namespace ECDSAAdd.Entrant.FullPadBSteps
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem step0_bool : ParkAOptionBool.optionEq ((compileChunked? 4697 FullPadBData.p0).map (fun c=>c.out)) (some FullPadBData.p1)=true := by decide +kernel
                                                                                                                                                  
                      
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                          
                                                                                                                                                  
                      
                                                                                                                                                                                                                                                           
                   
end ECDSAAdd.Entrant.FullPadBSteps

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullBReady
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ZeroReadDevelop
open ECDSAAdd.Entrant.FullBTemp
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000

def L := BThreeStaged301.L
def c := BThreeStaged301.c
                                                                                                                                                                                   
                               
                                                                                                                                                                                


                         


end ECDSAAdd.Entrant.FullBReady

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullBReady
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ZeroReadDevelop FullBTemp
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
                                                                                     
                                                                                                                                        
                                                                    
                                                                                       
                                                                                     
                                                                                                                                                                                                                  
                                                                                                   

                            

theorem onePass_output_bool : ((ZeroSetDevelop.compileS? (hosts L) BData301.p0).map
 (fun r=>ParkAProgramBool.programEq r.out FullPadBData.p5))=some true := by
 decide +kernel

theorem onePass_literal_output : (ZeroSetDevelop.compileS? (hosts L) BData301.p0).map (fun r=>r.out)=some FullPadBData.p5 :=
 OnePassOutputResearch.output_of_bool _ _ _ _ onePass_output_bool

theorem onePass_input_eq : BData301.p0=middle L c := BThreeStaged301.input_eq
attribute [local irreducible] ZeroSetDevelop.compileS?

theorem onePass_actual_output : (ZeroSetDevelop.compileS? (hosts L) (middle L c)).map (fun r=>r.out)=some FullPadBData.p5 :=
 (congrArg (fun p=>(ZeroSetDevelop.compileS? (hosts L) p).map (fun r=>r.out)) onePass_input_eq).symm.trans onePass_literal_output

theorem actual_compiled : (ZeroSetDevelop.compileS? (hosts L) (middle L c)).isSome=true :=
 OnePassOutputResearch.some_of_output _ _ _ _ onePass_actual_output
#print axioms actual_compiled

end ECDSAAdd.Entrant.FullBReady

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullBReady
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ZeroReadDevelop
open ECDSAAdd.Entrant.FullBTemp
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
theorem geometry : (loans L).length=82 ∧ (L.core.sumCarry::hosts L).Nodup ∧
 ∀x∈hosts L,LoanReadyTrim L c x ∧ x∉mR L ∧ x≠w192 L ∧ x≠c := by
 unfold LoanReadyTrim
 decide +kernel

theorem used_data : ∀x∈hosts L,FourthASavedCarryDevelop.hasWire BData301.p0 x=true := by decide +kernel

#print axioms geometry
#print axioms used_data
end ECDSAAdd.Entrant.FullBReady

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullBReady
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ZeroReadDevelop
open ECDSAAdd.Entrant.FullBTemp
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
private theorem hasWire_transport (p q:Program) (e:p=q) (x:Wire)
 (h:FourthASavedCarryDevelop.hasWire p x=true):FourthASavedCarryDevelop.hasWire q x=true := e ▸ h

private theorem hasWire_middle_to_body (K:CuccaroStreamedSquareWideLayout) (g x:Wire)
 (h:FourthASavedCarryDevelop.hasWire (middle K g) x=true):
 FourthASavedCarryDevelop.hasWire (ParkCarry10Develop.body K g) x=true := by
 exact (FourthASavedCarryDevelop.hasWire_iff _ _).mpr
  (middle_subset_old K g ((FourthASavedCarryDevelop.hasWire_iff _ _).mp h))

private theorem used_to_body (x:Wire) (h:FourthASavedCarryDevelop.hasWire BData301.p0 x=true):
 FourthASavedCarryDevelop.hasWire (ParkCarry10Develop.body L c) x=true :=
 hasWire_middle_to_body L c x (hasWire_transport _ _ BThreeStaged301.input_eq x h)

theorem actual_ready : Ready L c := by
 refine ⟨geometry.1,geometry.2.1,?_,FullBMeta.actual_metric,FullFitReady.actual,FullBMeta.actual_support_ready⟩
 intro x hx
 have g:=geometry.2.2 x hx
 exact ⟨g.1,g.2.1,g.2.2.1,g.2.2.2,used_to_body x (used_data x hx)⟩

#print axioms actual_ready
#print axioms FullBTemp.bodyWith_frame
#print axioms FullBTemp.newBody_resources
#print axioms FullBTemp.bodyWith_support
#print axioms FullBTemp.bodyWith_physical
end ECDSAAdd.Entrant.FullBReady

end

end


-- Verified gate replacement helper: computable layout equality
section
namespace FastGuardResearch
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 10000000
def wideEq : DecidableEq CuccaroStreamedSquareWideLayout := by
 intro a b
 rcases a with ⟨ac,ap⟩
 rcases b with ⟨bc,bp⟩
 cases ac
 cases bc
 simp only [CuccaroStreamedSquareWideLayout.mk.injEq,CuccaroStreamedSquareLayout.mk.injEq]
 infer_instance

end FastGuardResearch

end


-- Verified gate replacement helper: compiler chain output helpers
section
namespace FastFoldResearch
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ZeroReadDevelop
                                                         
                                                               
                                    
                 
                  
                                  
                                           

                                                               
                                  
                                                               
                                                             
         
        
        

end FastFoldResearch

end


-- Verified gate replacement helper: explicit selected B constructor
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ZeroReadDevelop
namespace FastBodyResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem actual_output :
 (ZeroSetDevelop.compileS? (FullBTemp.hosts FullBReady.L)
  (FullBTemp.middle FullBReady.L FullBReady.c)).map (fun c=>c.out)
  =some FullPadBData.p5 := FullBReady.onePass_actual_output

def loopFromOut (L : CuccaroStreamedSquareWideLayout) (c : Wire) (out : Program) : Program :=
 ManyACarryDevelop.buildMany 82 (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  (FullBTemp.loans L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ++ out ++
 ManyACarryDevelop.unbuildMany 82 (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  (FullBTemp.loans L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)

def foldFromOut (L : CuccaroStreamedSquareWideLayout) (c : Wire) (out : Program) : Program :=
 eAddLo L ++ (loopFromOut L c out ++ (ParkCarryDevelop.program (eU L) L.core.sumCarry ++ eSubK L))

def bodyFromOut (L : CuccaroStreamedSquareWideLayout) (c : Wire) (out : Program) : Program :=
 measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++
  (foldFromOut L c out ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L)))

theorem bodyFromOut_eq (L : CuccaroStreamedSquareWideLayout) (c : Wire)
 (cm : ZeroSetDevelop.CheckedS (FullBTemp.hosts L) (FullBTemp.middle L c)) :
 bodyFromOut L c cm.out=FullBTemp.newBody L c cm := rfl

theorem selected_of_output (L : CuccaroStreamedSquareWideLayout) (c : Wire)
 (out : Program) (ready : FullBTemp.Ready L c)
 (hout : (ZeroSetDevelop.compileS? (FullBTemp.hosts L) (FullBTemp.middle L c)).map (fun r=>r.out)=some out) :
 bodyFromOut L c out=FullBTemp.selectedBody L c := by
 simp only [FullBTemp.selectedBody,FullBTemp.mechanismEnabled,FullBTemp.bodyWith,
  Bool.true_eq,ite_true]
 rw [if_pos ready]
 cases he : FullBTemp.checkedMiddle L c with
 | none =>
  have bad:=hout
  change (FullBTemp.checkedMiddle L c).map (fun r=>r.out)=some out at bad
  simp [he] at bad
 | some cm =>
  have e : cm.out=out := by
   change (FullBTemp.checkedMiddle L c).map (fun r=>r.out)=some out at hout
   simpa [he] using hout
  dsimp only
  rw [←bodyFromOut_eq,e]

def directBody : Program := bodyFromOut FullBReady.L FullBReady.c FullPadBData.p5

theorem direct_eq_selected : directBody=FullBTemp.selectedBody FullBReady.L FullBReady.c :=
 selected_of_output _ _ _ FullBReady.actual_ready actual_output

end FastBodyResearch

end


-- Verified gate replacement helper: B84BodyContextShape
section
namespace B84BodyContextResearch
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant FastBodyResearch
open ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

def L := FullBReady.L

def before : Program := measuredFoldQTq L (negP L) ++
 measuredFoldQTq L (rot128F L) ++ eAddLo L ++
 buildPre (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) ++
 ManyACarryDevelop.cachedSubMany 82 (Acc.tx (FullBTemp.pad L) 139 (Acc.earlyTerm (hiReg L) true 6))
  (Acc.ty ((accReg L).take 139) (Acc.earlyTerm (hiReg L) true 6))
  (Acc.tc (accBank L) 139 (Acc.earlyTerm (hiReg L) true 6))
  (FullBTemp.loans L) L.core.cin L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)

def block : Program := buildPost (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) ++ FullPadBData.p5

def after : Program :=
 ManyACarryDevelop.unbuildMany 82 (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
 (FullBTemp.loans L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ++
 ParkCarryDevelop.program (eU L) L.core.sumCarry ++ eSubK L ++ eFoldTq L FullBReady.c ++
 ParkCarry10Develop.rebuild L

theorem body_shape : directBody = before ++ (block ++ after) := by
 simp only [directBody, bodyFromOut, foldFromOut, loopFromOut, ManyACarryDevelop.buildMany,
  before,block,after,L,List.append_assoc]

#print axioms body_shape
end B84BodyContextResearch

end


-- Verified gate replacement helper: B84BodyBlockEquality
section
namespace B84BodyBlockEqualityResearch
open ECDSAAdd
attribute [local irreducible] ECDSAAdd.Entrant.InverseCarryDevelop.buildPost

theorem block_eq_post : B84BodyContextResearch.block =
 B84PostLiteralResearch.actualPost ++ FullPadBData.p5 := rfl

#print axioms block_eq_post
end B84BodyBlockEqualityResearch

end


-- Verified gate replacement helper: B84CertifiedBodyShape
section
namespace B84CertifiedWholeBodyResearch
open ECDSAAdd ECDSAAdd.Challenge B84CachedBlockResearch B84CertifiedBlockResearch B84ContextResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.Entrant.InverseCarryDevelop.buildPost

theorem block_eq : B84BodyContextResearch.block = original :=
 B84BodyBlockEqualityResearch.block_eq_post.trans B84CertifiedBlockResearch.original_post_eq.symm

def optimizedBody : Program := B84BodyContextResearch.before ++
 (optimized ++ B84BodyContextResearch.after)
attribute [local irreducible] B84CachedBlockResearch.original B84CachedBlockResearch.headPart
 B84CachedBlockResearch.remainder FastBodyResearch.directBody
 B84BodyContextResearch.before B84BodyContextResearch.after B84BodyContextResearch.block
 B84PostLiteralResearch.actualPost

theorem body_shape : FastBodyResearch.directBody =
 B84BodyContextResearch.before ++ (original ++ B84BodyContextResearch.after) :=
 B84BodyContextResearch.body_shape.trans
  (congrArg (fun p=> B84BodyContextResearch.before ++ (p ++ B84BodyContextResearch.after)) block_eq)

#print axioms body_shape
end B84CertifiedWholeBodyResearch

end


-- Verified gate replacement helper: B84CertifiedWholeBody
section
namespace B84CertifiedWholeBodyResearch
open ECDSAAdd ECDSAAdd.Challenge B84CachedBlockResearch B84CertifiedBlockResearch B84ContextResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] B84CachedBlockResearch.original B84CachedBlockResearch.headPart
 B84CachedBlockResearch.remainder FastBodyResearch.directBody
 B84BodyContextResearch.before B84BodyContextResearch.after B84BodyContextResearch.block
 B84PostLiteralResearch.actualPost

theorem optimized_eq_context : optimizedBody = (B84BodyContextResearch.before ++ (optimized ++ B84BodyContextResearch.after)) := rfl

theorem body_run_eq (s : State) (m : List Bool) :
 run FastBodyResearch.directBody m s = run optimizedBody m s :=
 (congrArg (fun p=>run p m s) body_shape).trans
  ((replace_context original optimized run_eq block_measurements B84BodyContextResearch.before B84BodyContextResearch.after s m).trans
   (congrArg (fun p=>run p m s) optimized_eq_context.symm))

theorem body_toffoli : toffoliCount optimizedBody + 1 = toffoliCount FastBodyResearch.directBody :=
 (congrArg (fun p=>toffoliCount p+1) optimized_eq_context).trans
  ((context_one_less original optimized block_toffoli B84BodyContextResearch.before B84BodyContextResearch.after).trans
   (congrArg toffoliCount body_shape.symm))

theorem body_measurements : measurementCount FastBodyResearch.directBody = measurementCount optimizedBody :=
 (congrArg measurementCount body_shape).trans
  ((context_measurements original optimized block_measurements B84BodyContextResearch.before B84BodyContextResearch.after).trans
   (congrArg measurementCount optimized_eq_context.symm))

theorem body_slots : gateSlots optimizedBody = gateSlots FastBodyResearch.directBody + 4 :=
 (congrArg gateSlots optimized_eq_context).trans
  ((context_slots original optimized block_slots B84BodyContextResearch.before B84BodyContextResearch.after).trans
   (congrArg (fun p=>gateSlots p+4) body_shape.symm))

theorem body_support : wires optimizedBody ⊆ wires FastBodyResearch.directBody := by
 have h0 : wires (B84BodyContextResearch.before ++ (optimized ++ B84BodyContextResearch.after)) ⊆ wires (B84BodyContextResearch.before ++ (original ++ B84BodyContextResearch.after)) :=
  B84SupportResearch.context_support original optimized block_support B84BodyContextResearch.before B84BodyContextResearch.after
 have h1 : wires (B84BodyContextResearch.before ++ (optimized ++ B84BodyContextResearch.after)) ⊆ wires FastBodyResearch.directBody :=
  Eq.mp (congrArg (fun p=>wires (B84BodyContextResearch.before ++ (optimized ++ B84BodyContextResearch.after)) ⊆ wires p) body_shape.symm) h0
 exact Eq.mp (congrArg (fun p=>wires p ⊆ wires FastBodyResearch.directBody) optimized_eq_context.symm) h1

theorem body_physical (hp : ECDSAAdd.Arithmetic.GatePhysical FastBodyResearch.directBody) :
 ECDSAAdd.Arithmetic.GatePhysical optimizedBody := by
 have h := Eq.mp (congrArg ECDSAAdd.Arithmetic.GatePhysical body_shape) hp
 have h' := (ECDSAAdd.Arithmetic.gatePhysical_append B84BodyContextResearch.before (original ++ B84BodyContextResearch.after)).mp h
 have h'' := (ECDSAAdd.Arithmetic.gatePhysical_append original B84BodyContextResearch.after).mp h'.2
 have hnew : ECDSAAdd.Arithmetic.GatePhysical (B84BodyContextResearch.before ++ (optimized ++ B84BodyContextResearch.after)) :=
  (ECDSAAdd.Arithmetic.gatePhysical_append B84BodyContextResearch.before (optimized ++ B84BodyContextResearch.after)).mpr
   ⟨h'.1,(ECDSAAdd.Arithmetic.gatePhysical_append optimized B84BodyContextResearch.after).mpr ⟨block_physical h''.1,h''.2⟩⟩
 exact Eq.mp (congrArg ECDSAAdd.Arithmetic.GatePhysical optimized_eq_context.symm) hnew

#print axioms body_run_eq
#print axioms body_toffoli
#print axioms body_support
end B84CertifiedWholeBodyResearch

end


-- Verified gate replacement helper: B84OptimizedSelector
section
namespace B84OptimizedSelectorResearch
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Challenge
open B84CertifiedWholeBodyResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] FullBTemp.selectedBody FastBodyResearch.directBody optimizedBody

def selectedBody (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
 match FastGuardResearch.wideEq L FullBReady.L with
 | .isFalse _ => FullBTemp.selectedBody L g
 | .isTrue _ => if g=FullBReady.c then optimizedBody else FullBTemp.selectedBody L g

theorem actual_run (s : State) (m : List Bool) :
 run optimizedBody m s = run (FullBTemp.selectedBody FullBReady.L FullBReady.c) m s :=
 (body_run_eq s m).symm.trans
  (congrArg (fun p=>run p m s) FastBodyResearch.direct_eq_selected)

theorem actual_toffoli : toffoliCount optimizedBody + 1 =
 toffoliCount (FullBTemp.selectedBody FullBReady.L FullBReady.c) :=
 body_toffoli.trans (congrArg toffoliCount FastBodyResearch.direct_eq_selected)

theorem actual_measurements : measurementCount optimizedBody =
 measurementCount (FullBTemp.selectedBody FullBReady.L FullBReady.c) :=
 body_measurements.symm.trans (congrArg measurementCount FastBodyResearch.direct_eq_selected)

theorem actual_slots : gateSlots optimizedBody =
 gateSlots (FullBTemp.selectedBody FullBReady.L FullBReady.c) + 4 :=
 body_slots.trans (congrArg (fun p=>gateSlots p+4) FastBodyResearch.direct_eq_selected)

theorem actual_support : wires optimizedBody ⊆ wires (FullBTemp.selectedBody FullBReady.L FullBReady.c) :=
 Eq.mp (congrArg (fun p=>wires optimizedBody ⊆ wires p) FastBodyResearch.direct_eq_selected) body_support

theorem actual_physical (hp : GatePhysical (FullBTemp.selectedBody FullBReady.L FullBReady.c)) :
 GatePhysical optimizedBody :=
 body_physical (Eq.mp (congrArg GatePhysical FastBodyResearch.direct_eq_selected.symm) hp)

theorem selected_run (L : CuccaroStreamedSquareWideLayout) (g : Wire) (s : State) (m : List Bool) :
 run (selectedBody L g) m s = run (FullBTemp.selectedBody L g) m s := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq L FullBReady.L with
 | isFalse hn => rfl
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg
    subst L
    subst g
    exact actual_run s m
  · rfl

theorem selected_toffoli (L : CuccaroStreamedSquareWideLayout) (g : Wire) :
 toffoliCount (selectedBody L g) ≤ toffoliCount (FullBTemp.selectedBody L g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq L FullBReady.L with
 | isFalse hn => exact Nat.le_refl _
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg
    subst L
    subst g
    exact (Nat.le_add_right (toffoliCount optimizedBody) 1).trans actual_toffoli.le
  · exact Nat.le_refl _

theorem selected_measurements (L : CuccaroStreamedSquareWideLayout) (g : Wire) :
 measurementCount (selectedBody L g) = measurementCount (FullBTemp.selectedBody L g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq L FullBReady.L with
 | isFalse hn => rfl
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg
    subst L
    subst g
    exact actual_measurements
  · rfl

                                                                         
                                                                                
                    
                                                        
                                           
               
            
       
               
           
           
                         
                              

theorem selected_support (L : CuccaroStreamedSquareWideLayout) (g : Wire) :
 wires (selectedBody L g) ⊆ wires (FullBTemp.selectedBody L g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq L FullBReady.L with
 | isFalse hn => exact Finset.Subset.refl _
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg
    subst L
    subst g
    exact actual_support
  · exact Finset.Subset.refl _

theorem selected_physical (L : CuccaroStreamedSquareWideLayout) (g : Wire)
 (hp : GatePhysical (FullBTemp.selectedBody L g)) : GatePhysical (selectedBody L g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq L FullBReady.L with
 | isFalse hn => exact hp
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg
    subst L
    subst g
    exact actual_physical hp
  · exact hp

theorem selected_actual : selectedBody FullBReady.L FullBReady.c = optimizedBody := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq FullBReady.L FullBReady.L with
 | isFalse hn => exact False.elim (hn rfl)
 | isTrue hl => exact if_pos rfl

#print axioms selected_run
#print axioms selected_toffoli
end B84OptimizedSelectorResearch

end


-- Verified gate replacement helper: B84OptimizedResources
section
namespace B84OptimizedResourcesResearch
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

-- Apply the inherited generic compiler resource theorem before specializing layout.
theorem old_gain (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
 (ready : FullBTemp.Ready L c) (success : (FullBTemp.checkedMiddle L c).isSome=true) :
 toffoliCount (FullBTemp.selectedBody L c)+84 ≤ toffoliCount (ParkCarry10Develop.body L c) ∧
 measurementCount (FullBTemp.selectedBody L c)=measurementCount (ParkCarry10Develop.body L c) ∧
 gateSlots (FullBTemp.selectedBody L c)+252 ≤ gateSlots (ParkCarry10Develop.body L c) := by
 cases h : FullBTemp.checkedMiddle L c with
 | none => simp only [h,Option.isSome_none,Bool.false_eq_true] at success
 | some cm =>
  simpa only [FullBTemp.selectedBody,FullBTemp.mechanismEnabled,FullBTemp.bodyWith,
   if_true,if_pos ready,h] using FullBTemp.newBody_resources L hw c ready cm

theorem old_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (FullBTemp.selectedBody L c) ≤ toffoliCount (ParkCarry10Develop.body L c) ∧
 measurementCount (FullBTemp.selectedBody L c)=measurementCount (ParkCarry10Develop.body L c) ∧
 gateSlots (FullBTemp.selectedBody L c) ≤ gateSlots (ParkCarry10Develop.body L c) :=
 FullBTemp.bodyWith_resources FullBTemp.mechanismEnabled L hw c

theorem selected_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 gateSlots (B84OptimizedSelectorResearch.selectedBody L c) ≤ gateSlots (ParkCarry10Develop.body L c) := by
 unfold B84OptimizedSelectorResearch.selectedBody
 cases he : FastGuardResearch.wideEq L FullBReady.L with
 | isFalse hn => exact (old_resources L hw c).2.2
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg
    subst L
    subst c
    have hsuccess : (FullBTemp.checkedMiddle FullBReady.L FullBReady.c).isSome=true :=
     FullBReady.actual_compiled
    have gain := old_gain FullBReady.L hw FullBReady.c FullBReady.actual_ready hsuccess
    exact B84OptimizedSelectorResearch.actual_slots.le.trans
     ((Nat.add_le_add_left (by decide : (4:Nat)≤252) _).trans gain.2.2)
  · exact (old_resources L hw c).2.2

theorem selected_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (B84OptimizedSelectorResearch.selectedBody L c) ≤ toffoliCount (ParkCarry10Develop.body L c) ∧
 measurementCount (B84OptimizedSelectorResearch.selectedBody L c)=measurementCount (ParkCarry10Develop.body L c) ∧
 gateSlots (B84OptimizedSelectorResearch.selectedBody L c) ≤ gateSlots (ParkCarry10Develop.body L c) :=
 ⟨(B84OptimizedSelectorResearch.selected_toffoli L c).trans (old_resources L hw c).1,
  (B84OptimizedSelectorResearch.selected_measurements L c).trans (old_resources L hw c).2.1,
  selected_slots L hw c⟩

#print axioms selected_resources
end B84OptimizedResourcesResearch

end


-- Verified gate replacement helper: B84OptimizedInterface
section
namespace B84TripleTransferResearch
open ECDSAAdd

theorem of_run_eq (p q : Program)
 (he : ∀ (s : State) (m : List Bool), run p m s = run q m s)
 (P Q : BasisState → Prop) (hq : Triple P q Q) : Triple P p Q := by
 intro s m hs
 rw [he s m]
 exact hq s m hs
end B84TripleTransferResearch

namespace ECDSAAdd.Entrant.FullBOptTemp
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

abbrev selectedBody := B84OptimizedSelectorResearch.selectedBody

def hostedSelectedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 selectedBody (ParkCarryDevelop.hostLayout L rho) c

theorem selected_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 wires (selectedBody L c) ⊆ wires (ParkCarry10Develop.body L c) :=
 (B84OptimizedSelectorResearch.selected_support L c).trans
  (FullBTemp.bodyWith_support FullBTemp.mechanismEnabled L hw c)

theorem selected_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) : wires (selectedBody L c) ⊆ (c::L.wires).toFinset :=
 (selected_subset L hw c).trans (ParkCarry10Develop.body_support L hw hn c)

theorem selected_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (c : Wire) (hn : (c::L.wires).Nodup) : GatePhysical (selectedBody L c) :=
 B84OptimizedSelectorResearch.selected_physical L c
  (FullBTemp.bodyWith_physical FullBTemp.mechanismEnabled L hw c hn)

theorem selected_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base)
 (hsum : base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (selectedBody L c)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) :=
 B84TripleTransferResearch.of_run_eq (selectedBody L c) (FullBTemp.selectedBody L c)
  (B84OptimizedSelectorResearch.selected_run L c) _ _
  (FullBTemp.bodyWith_frame FullBTemp.mechanismEnabled L hw hn c hcw base M hM hP hc hsum O hO hg hSource)

theorem hostedSelectedBody_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire)
 (c : Wire) (fixed : rho L.core.sumCarry=L.core.sumCarry) :
 hostedSelectedBody L rho c = selectedBody L c :=
 congrArg (fun K=>selectedBody K c) (ParkCarryDevelop.host_eq L rho fixed)

theorem hosted_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedSelectedBody L rho c) ≤ toffoliCount (ParkCarry10Develop.hostedBody L rho c) ∧
 measurementCount (hostedSelectedBody L rho c)=measurementCount (ParkCarry10Develop.hostedBody L rho c) ∧
 Challenge.gateSlots (hostedSelectedBody L rho c) ≤ Challenge.gateSlots (ParkCarry10Develop.hostedBody L rho c) :=
 B84OptimizedResourcesResearch.selected_resources (ParkCarryDevelop.hostLayout L rho)
  (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 wires (hostedSelectedBody L rho c) ⊆ wires (ParkCarry10Develop.hostedBody L rho c) :=
 selected_subset (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen : 300≤ext.length)
 (away : ∀q∈ext,q∉L.wires) :
 wires (hostedSelectedBody L (LowZero18Square.foldPerm L ext) c) ⊆ (c::L.wires).toFinset := by
 rw [hostedSelectedBody_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact selected_support L hw hn c

#print axioms selected_frame
#print axioms hosted_resources
end ECDSAAdd.Entrant.FullBOptTemp

end


-- Verified gate replacement helper: B84OptimizedRanked
section
namespace ECDSAAdd.Entrant.FullBOptTemp
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

def actualLayout : CuccaroStreamedSquareWideLayout := Baselines.layout.dialogStreamedSquareWide
def actualControl : Wire := Baselines.layout.core.generic
def actualExt : List Wire := OwnDiagAll12Square.kext Baselines.layout
def actualFoldPerm : Equiv.Perm Wire := LowZero18Square.foldPerm actualLayout actualExt
def actualHostedLayout : CuccaroStreamedSquareWideLayout := ParkCarryDevelop.hostLayout actualLayout actualFoldPerm

theorem actualHostedLayout_eq : actualHostedLayout = actualLayout := by
 apply ParkCarryDevelop.host_eq
 have hw := Baselines.layout.dialogStreamedSquareWide_widths Baselines.layout_widths
 have nd : actualLayout.wires.Nodup := by
  change Baselines.layout.dialogStreamedSquareWide.wires.Nodup
  have full := Baselines.layout.streamedSquare_control_nodup Baselines.layout_widths Baselines.layout_nodup
  exact (List.nodup_cons.mp (List.nodup_cons.mp full).2).2
 have he := OwnDiagAll12Square.kext_ok Baselines.layout Baselines.layout_widths Baselines.layout_nodup
 exact ParkCarryDevelop.fold_fixes_sumCarry actualLayout hw nd actualExt he.len
  (fun q hq h => he.away q hq (List.mem_cons_of_mem actualControl h))

theorem actualLayout_eq_ready : actualLayout = FullBReady.L := rfl
theorem actualControl_eq_ready : actualControl = FullBReady.c := rfl

theorem ranked_selected_exact :
 hostedSelectedBody actualLayout actualFoldPerm actualControl = selectedBody actualLayout actualControl :=
 congrArg (fun L=>selectedBody L actualControl) actualHostedLayout_eq

theorem ranked_optimized_exact :
 hostedSelectedBody actualLayout actualFoldPerm actualControl = B84CertifiedWholeBodyResearch.optimizedBody :=
 ranked_selected_exact.trans
  ((congrArg (fun L=>selectedBody L actualControl) actualLayout_eq_ready).trans
   ((congrArg (fun c=>selectedBody FullBReady.L c) actualControl_eq_ready).trans
    B84OptimizedSelectorResearch.selected_actual))

theorem add_eightyfive (n : Nat) : n+85=(n+1)+84 := by omega

theorem optimized_ranked_gain :
 toffoliCount B84CertifiedWholeBodyResearch.optimizedBody+85≤4762 ∧
 measurementCount B84CertifiedWholeBodyResearch.optimizedBody=5924 := by
 have hw : FullBReady.L.Widths :=
  Baselines.layout.dialogStreamedSquareWide_widths Baselines.layout_widths
 have hs : (FullBTemp.checkedMiddle FullBReady.L FullBReady.c).isSome=true :=
  FullBReady.actual_compiled
 have gain := B84OptimizedResourcesResearch.old_gain FullBReady.L hw FullBReady.c FullBReady.actual_ready hs
 have old := ParkCarry10Develop.body_counts FullBReady.L hw FullBReady.c
 refine ⟨?_,B84OptimizedSelectorResearch.actual_measurements.trans (gain.2.1.trans old.2)⟩
 exact (add_eightyfive (toffoliCount B84CertifiedWholeBodyResearch.optimizedBody)).le.trans
  ((congrArg (fun n=>n+84) B84OptimizedSelectorResearch.actual_toffoli).le.trans
   (gain.1.trans old.1.le))

theorem ranked_certified_gain :
 toffoliCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)+85≤4762 ∧
 measurementCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)=5924 :=
 ⟨Eq.mp (congrArg (fun p=>toffoliCount p+85≤4762) ranked_optimized_exact.symm) optimized_ranked_gain.1,
  Eq.mp (congrArg (fun p=>measurementCount p=5924) ranked_optimized_exact.symm) optimized_ranked_gain.2⟩

#print axioms ranked_certified_gain
end ECDSAAdd.Entrant.FullBOptTemp

end
