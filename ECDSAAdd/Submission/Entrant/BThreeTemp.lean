import ECDSAAdd.Submission.Entrant.ParkAWorkLoan
import ECDSAAdd.Submission.Entrant.ParkCarry10

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000

namespace ECDSAAdd.Entrant.BThreeLoop285
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop

/-- Source-only generic proposal. No fixed compiler success or ranked caller is changed. -/
theorem compiled_cached_quad_eq
    (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p u : Wire)
    (oldMiddle newMiddle : Program)
    (hacc : acc.length = 163) (hsrc : src.length = 128)
    (hf : ∀f ∈ earlyHTerms src, Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool)
    (hz : ∀w ∈ Z, s.basis w = false) (hb : ∀w ∈ bank, s.basis w = false)
    (hi : s.basis cin = false) (ha : regValue acc s.basis = 0)
    (zq : s.basis q = false) (zr : s.basis r = false)
    (zp : s.basis p = false) (zu : s.basis u = false)
    (fq : q ∉ cin::(src++acc++Z++bank)) (fr : r ∉ cin::(src++acc++Z++bank))
    (fp : p ∉ cin::(src++acc++Z++bank)) (fu : u ∉ cin::(src++acc++Z++bank))
    (rq : r ≠ q) (pq : p ≠ q) (pr : p ≠ r)
    (uq : u ≠ q) (ur : u ≠ r) (up : u ≠ p)
    (ofq : q ∉ wires (NarrowAcc.build8 acc Z bank cin src))
    (oiq : q ∉ wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (ofr : r ∉ wires (NarrowAcc.build8 acc Z bank cin src))
    (oir : r ∉ wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (ofp : p ∉ wires (NarrowAcc.build8 acc Z bank cin src))
    (ofu : u ∉ wires (NarrowAcc.build8 acc Z bank cin src))
    (ofp2 : p ∉ wires (buildDual acc Z bank cin src q r))
    (oip2 : p ∉ wires (unbuildDual acc Z bank cin src q r))
    (ofu3 : u ∉ wires (buildTriple acc Z bank cin src q r p))
    (oiu3 : u ∉ wires (unbuildTriple acc Z bank cin src q r p))
    (omq : q ∉ wires oldMiddle)
    (cert : ManyRewrites [r,p,u] oldMiddle newMiddle)
    (good : WReady acc Z bank cin src (regValue src s.basis)
      (middleState (NarrowAcc.build8 acc Z bank cin src) oldMiddle s m)) :
    run (buildQuad acc Z bank cin src q r p u ++ newMiddle ++
      unbuildQuad acc Z bank cin src q r p u) m s =
    run (buildCached acc Z bank cin src q ++ oldMiddle ++
      unbuildConsumed acc Z bank cin src q) m s := by
  have zeroLoans : ∀w ∈ [r,p,u], s.basis w = false := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact zr
    · exact zp
    · exact zu
  have offLoans : ∀w ∈ [r,p,u], w ∉ wires (NarrowAcc.build8 acc Z bank cin src) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ofr
    · exact ofp
    · exact ofu
  have midEq := cert.middle_eq [r,p,u] oldMiddle newMiddle
    (NarrowAcc.build8 acc Z bank cin src) s m zeroLoans offLoans
  have goodNew : WReady acc Z bank cin src (regValue src s.basis)
      (middleState (NarrowAcc.build8 acc Z bank cin src) newMiddle s m) := by
    rw [midEq]
    exact good
  have support := cert.support [r,p,u] oldMiddle newMiddle
  have onq : q ∉ wires newMiddle := fun h => omq (support.1 h)
  have onr : r ∉ wires newMiddle := support.2 r (by simp)
  have onp : p ∉ wires newMiddle := support.2 p (by simp)
  have onu : u ∉ wires newMiddle := support.2 u (by simp)
  have tripleReady := triple_middle_ready acc Z bank cin src q r p newMiddle
    hacc hsrc hf s m hz hb hi ha zq zr zp fq fr rq fp pq pr
    ofq onq oiq ofr onr oir ofp2 onp oip2 goodNew
  have quadEq := cached_wloop_quad_eq acc Z bank cin src q r p u newMiddle
    hacc hsrc hf s m hz hb hi ha zq zr zp zu fq fr rq fp pq pr fu uq ur up
    ofq oiq ofr oir ofp2 oip2 ofu3 onu oiu3
    tripleReady.1 tripleReady.2.1 tripleReady.2.2.1 tripleReady.2.2.2
  have tripleEq := cached_wloop_triple_eq acc Z bank cin src q r p newMiddle
    hacc hsrc hf s m hz hb hi ha zq zr zp fq fr rq fp pq pr
    ofq onq oiq ofr onr oir ofp2 onp oip2 goodNew
  have dualEq := cached_wloop_dual_eq acc Z bank cin src q r newMiddle
    hacc hsrc hf s m hz hb hi ha zq zr fq fr rq ofq onq oiq ofr onr oir goodNew
  have replaceEq := cert.surround_eq [r,p,u] oldMiddle newMiddle
    (NarrowAcc.build8 acc Z bank cin src) (SourceAddFourDevelop.unbuild acc Z bank cin src)
    s m zeroLoans offLoans
  have cachedEq := cached_wloop_eq acc Z bank cin src q oldMiddle
    hacc hsrc hf s m hz hb hi ha zq fq ofq omq oiq good
  exact quadEq.trans (tripleEq.trans (dualEq.trans (replaceEq.trans cachedEq.symm)))

/-- Three retained carries cost no extra forward CCX and remove three inverse CCX. -/
theorem compiled_cached_quad_resources
    (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p u : Wire)
    (oldMiddle newMiddle : Program)
    (ha : acc.length = 163) (hs : src.length = 128)
    (hz : 5 ≤ Z.length) (hb : 132 ≤ bank.length)
    (cert : ManyRewrites [r,p,u] oldMiddle newMiddle) :
    toffoliCount (buildQuad acc Z bank cin src q r p u ++ newMiddle ++
      unbuildQuad acc Z bank cin src q r p u) + 3 ≤
      toffoliCount (buildCached acc Z bank cin src q ++ oldMiddle ++
        unbuildConsumed acc Z bank cin src q) ∧
    measurementCount (buildQuad acc Z bank cin src q r p u ++ newMiddle ++
      unbuildQuad acc Z bank cin src q r p u) =
      measurementCount (buildCached acc Z bank cin src q ++ oldMiddle ++
        unbuildConsumed acc Z bank cin src q) ∧
    Challenge.gateSlots (buildQuad acc Z bank cin src q r p u ++ newMiddle ++
      unbuildQuad acc Z bank cin src q r p u) + 9 ≤
      Challenge.gateSlots (buildCached acc Z bank cin src q ++ oldMiddle ++
        unbuildConsumed acc Z bank cin src q) := by
  have f1 := buildDual_counts acc Z bank cin src q r ha hs hz hb
  have f2 := buildTriple_counts acc Z bank cin src q r p ha hs hz hb
  have f3 := buildQuad_counts acc Z bank cin src q r p u ha hs hz hb
  have i1 := unbuildDual_counts acc Z bank cin src q r ha hs hb
  have i2 := unbuildTriple_counts acc Z bank cin src q r p ha hs hb
  have i3 := unbuildQuad_counts acc Z bank cin src q r p u ha hs hb
  have mt := cert.toffoli [r,p,u] oldMiddle newMiddle
  have mm := cert.measurements [r,p,u] oldMiddle newMiddle
  have ms := cert.slots [r,p,u] oldMiddle newMiddle
  simp only [toffoliCount_append, measurementCount_append, Challenge.gateSlots_append]
  exact ⟨by omega, by omega, by omega⟩

end ECDSAAdd.Entrant.BThreeLoop285


namespace ECDSAAdd.Entrant.BThreeTemp
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open ControlLoan1589BFFold InverseCarryDevelop ZeroReadDevelop
open ThirdSavedCarryDevelop FourthASavedCarryDevelop

/-- This helper is unhooked. OFF and every failed guard retain old B10 exactly. -/
def mechanismEnabled : Bool := true

def hostR (L : CuccaroStreamedSquareWideLayout) : Wire := L.core.work.getD 171 0
def hostP (L : CuccaroStreamedSquareWideLayout) : Wire := L.core.work.getD 172 0
def hostU (L : CuccaroStreamedSquareWideLayout) : Wire := L.core.work.getD 173 0
def hosts (L : CuccaroStreamedSquareWideLayout) : List Wire := [hostR L,hostP L,hostU L]
def middle (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  LowBitCarryDevelop.wMidFullCCC0 L c

def HostReady (L : CuccaroStreamedSquareWideLayout) (c x : Wire) : Prop :=
  LoanReady L c x ∧ x ∉ mR L ∧ x ≠ w192 L ∧ x ≠ c ∧
    hasWire (ParkCarry10Develop.body L c) x = true

def Ready (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Prop :=
  HostReady L c (hostR L) ∧ HostReady L c (hostP L) ∧ HostReady L c (hostU L) ∧
    [L.core.sumCarry,hostR L,hostP L,hostU L].Nodup

instance (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Decidable (Ready L c) := by
  unfold Ready HostReady
  infer_instance

def checkedMiddle (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
    Option (CheckedMany (hosts L) (middle L c)) := compileManyChunked? (hosts L) (middle L c)

def oldLoop (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry ++
    middle L c ++
    unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry

def newLoop (L : CuccaroStreamedSquareWideLayout) (c : Wire)
    (cm : CheckedMany (hosts L) (middle L c)) : Program :=
  buildQuad (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      L.core.sumCarry (hostR L) (hostP L) (hostU L) ++ cm.out ++
    unbuildQuad (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      L.core.sumCarry (hostR L) (hostP L) (hostU L)

def newFold (L : CuccaroStreamedSquareWideLayout) (c : Wire)
    (cm : CheckedMany (hosts L) (middle L c)) : Program :=
  eAddLo L ++ (newLoop L c cm ++
    (ParkCarryDevelop.program (eU L) L.core.sumCarry ++ eSubK L))

def newBody (L : CuccaroStreamedSquareWideLayout) (c : Wire)
    (cm : CheckedMany (hosts L) (middle L c)) : Program :=
  measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++
    (newFold L c cm ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L)))

def bodyWith (enabled : Bool) (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  if enabled then
    if Ready L c then
      match checkedMiddle L c with
      | none => ParkCarry10Develop.body L c
      | some cm => newBody L c cm
    else ParkCarry10Develop.body L c
  else ParkCarry10Develop.body L c

def selectedBody (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  bodyWith mechanismEnabled L c

def hostedSelectedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire)
    (c : Wire) : Program := selectedBody (ParkCarryDevelop.hostLayout L rho) c

theorem off_exact (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
    bodyWith false L c = ParkCarry10Develop.body L c := rfl

theorem geometry_fallback (L : CuccaroStreamedSquareWideLayout) (c : Wire)
    (h : ¬ Ready L c) : bodyWith true L c = ParkCarry10Develop.body L c := by
  simp [bodyWith,h]

theorem compiler_fallback (L : CuccaroStreamedSquareWideLayout) (c : Wire)
    (h : checkedMiddle L c = none) : bodyWith true L c = ParkCarry10Develop.body L c := by
  simp [bodyWith,h]

/-- Generalized B1 zero-host argument; it applies to each of the three work hosts. -/
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
    (offF : x ∉ wires (NarrowAcc.build8 (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)))
    (offI : x ∉ wires (SourceAddFourDevelop.unbuild (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L))) :
    x ∉ wires (buildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) ∧
    x ∉ wires (unbuildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) ∧
    x ∉ wires (buildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L)) ∧
    x ∉ wires (unbuildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L)) := by
  have lens := acc_lengths L hw
  have cF : x ∉ wires (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := by
    intro h
    rcases Finset.mem_insert.mp (buildCached_support _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) (by omega) h) with eq | h
    · exact xq eq
    · exact offF h
  have cI : x ∉ wires (unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := by
    intro h
    rcases Finset.mem_insert.mp (unbuildConsumed_support _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) h) with eq | h
    · exact xq eq
    · exact offI h
  have dF : x ∉ wires (buildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
    intro h
    rcases Finset.mem_insert.mp (buildDual_support _ _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) (by omega) h) with eq | h
    · exact xr eq
    · exact cF h
  have dI : x ∉ wires (unbuildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
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

/-- The old BState arithmetic is invoked only before caching, on the original uncached middle. -/
theorem loop_bstate_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (c : Wire) (hcw : c ∉ L.wires) (ready : Ready L c)
    (cm : CheckedMany (hosts L) (middle L c))
    (base : BasisState) (clean : L.PairClean base) (hsum : base L.core.sumCarry = false)
    (O E O' : Nat)
    (mid : Triple (BState L base O E (4294968272 * regValue (hiReg L) base)) (middle L c)
      (BState L base O' E (4294968272 * regValue (hiReg L) base)))
    (s : State) (records : List Bool) (hs : BState L base O E 0 s.basis) :
    run (newLoop L c cm) records s = run (oldLoop L c) records s := by
  have lens := acc_lengths L hw
  have away := ParkCarryDevelop.sumCarry_off_regs L hn
  have zeroQ : s.basis L.core.sumCarry = false :=
    (hs.2.2.2 _ away.1 away.2.1 away.2.2).trans hsum
  have zeroR := host_zero_of_bstate L hn c (hostR L) ready.1 base clean O E 0 s.basis hs
  have zeroP := host_zero_of_bstate L hn c (hostP L) ready.2.1 base clean O E 0 s.basis hs
  have zeroU := host_zero_of_bstate L hn c (hostU L) ready.2.2.1 base clean O E 0 s.basis hs
  have nd := ready.2.2.2
  have pr : hostP L ≠ hostR L := by
    have h := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    intro eq; exact h (by simp [eq])
  have ur : hostU L ≠ hostR L := by
    have h := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    intro eq; exact h (by simp [eq])
  have up : hostU L ≠ hostP L := by
    have h := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp nd).2).2).1
    intro eq; exact h (by simp [eq])
  have freshQ := sumCarry_fresh_domain L hn
  have freshR := ready.1.1.2.1
  have freshP := ready.2.1.1.2.1
  have freshU := ready.2.2.1.1.2.1
  have offQ := wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin
    (hiReg L) L.core.sumCarry (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_fits L hw hn) freshQ
  have offR := wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin
    (hiReg L) (hostR L) (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_fits L hw hn) freshR
  have offP := wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin
    (hiReg L) (hostP L) (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_fits L hw hn) freshP
  have offU := wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin
    (hiReg L) (hostU L) (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_fits L hw hn) freshU
  have pDualF : hostP L ∉ wires (buildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
    intro h
    rcases Finset.mem_insert.mp (buildDual_support _ _ _ _ _ _ _ (acc_lengths L hw).1
      (hiReg_length L hw) (by omega) (by omega) h) with eq | h
    · exact pr eq
    · rcases Finset.mem_insert.mp (buildCached_support _ _ _ _ _ _ (acc_lengths L hw).1
        (hiReg_length L hw) (by omega) (by omega) h) with eq | h
      · exact ready.2.1.1.2.2.1 eq
      · exact offP.1 h
  have pDualI : hostP L ∉ wires (unbuildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
    intro h
    rcases Finset.mem_insert.mp (unbuildDual_support _ _ _ _ _ _ _ (acc_lengths L hw).1
      (hiReg_length L hw) (by omega) h) with eq | h
    · exact pr eq
    · rcases Finset.mem_insert.mp (unbuildConsumed_support _ _ _ _ _ _ (acc_lengths L hw).1
        (hiReg_length L hw) (by omega) h) with eq | h
      · exact ready.2.1.1.2.2.1 eq
      · exact offP.2 h
  have eu := endpoint_off L hw (hostU L) ready.2.2.1.1.2.2.1 ur up offU.1 offU.2
  have offMiddle : L.core.sumCarry ∉ wires (middle L c) :=
    ParkCarry10Develop.mid_sumCarry_free L hw hn c hcw
  obtain ⟨hz, hb, hi, _, _⟩ := zero_regs L hn base clean O E 0 s.basis hs
  have source0 : regValue (hiReg L) s.basis = regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E 0 s.basis hs q (Or.inl hq))
  have good : WReady (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      (regValue (hiReg L) s.basis) (middleState (wBuild L) (middle L c) s records) := by
    let first := run (wBuild L) (records.take (measurementCount (wBuild L))) s
    have firstGood := (wBuild_step L hw hn base clean O E) s
      (records.take (measurementCount (wBuild L))) hs
    have midGood := mid first ((records.drop (measurementCount (wBuild L))).take
      (measurementCount (middle L c))) firstGood.2
    obtain ⟨mz, mb, mi, _, _⟩ := zero_regs L hn base clean O' E _ _ midGood.2
    have source1 := regValue_congr (hiReg L) _ base
      (fun q hq => bstate_other L hn base O' E _ _ midGood.2 q (Or.inl hq))
    exact ⟨midGood.2.2.2.1.trans (by rw [source0]), source1.trans source0.symm, mz, mb, mi⟩
  exact BThreeLoop285.compiled_cached_quad_eq (accReg L) (accZ L) (accBank L) L.core.cin
    (hiReg L) L.core.sumCarry (hostR L) (hostP L) (hostU L) (middle L c) cm.out
    (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_fits L hw hn) s records
    hz hb hi hs.2.2.1 zeroQ zeroR zeroP zeroU freshQ freshR freshP freshU
    ready.1.1.2.2.1 ready.2.1.1.2.2.1 pr ready.2.2.1.1.2.2.1 ur up
    offQ.1 offQ.2 offR.1 offR.2 offP.1 offU.1 pDualF pDualI eu.2.2.1 eu.2.2.2
    offMiddle cm.proof good

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

/-- The proved generic ledger applies only when the sequential checkedMany certificate exists. -/
theorem newLoop_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (cm : CheckedMany (hosts L) (middle L c)) :
    toffoliCount (newLoop L c cm) + 3 ≤ toffoliCount (oldLoop L c) ∧
    measurementCount (newLoop L c cm) = measurementCount (oldLoop L c) ∧
    Challenge.gateSlots (newLoop L c cm) + 9 ≤ Challenge.gateSlots (oldLoop L c) := by
  have lens := acc_lengths L hw
  exact BThreeLoop285.compiled_cached_quad_resources (accReg L) (accZ L) (accBank L)
    L.core.cin (hiReg L) L.core.sumCarry (hostR L) (hostP L) (hostU L)
    (middle L c) cm.out (acc_lengths L hw).1 (hiReg_length L hw) (by omega) (by omega) cm.proof

theorem newBody_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (cm : CheckedMany (hosts L) (middle L c)) :
    toffoliCount (newBody L c cm) + 3 ≤ toffoliCount (ParkCarry10Develop.body L c) ∧
    measurementCount (newBody L c cm) = measurementCount (ParkCarry10Develop.body L c) ∧
    Challenge.gateSlots (newBody L c cm) + 9 ≤ Challenge.gateSlots (ParkCarry10Develop.body L c) := by
  have loop := newLoop_resources L hw c cm
  simp only [newLoop,oldLoop,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at loop
  simp only [newBody,newFold,newLoop,ParkCarry10Develop.body,ParkCarry10Develop.fold,middle,
    toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at loop ⊢
  exact ⟨by omega,by omega,by omega⟩

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


/-- These three hosts add no new wires when the guard proves their old B10 occurrence. -/
def extras (L : CuccaroStreamedSquareWideLayout) : Finset Wire :=
  {hostR L,hostP L,hostU L}

theorem newLoop_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (cm : CheckedMany (hosts L) (middle L c)) :
    wires (newLoop L c cm) ⊆ extras L ∪ wires (oldLoop L c) := by
  have lens := acc_lengths L hw
  have b3 := buildQuad_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) (hostU L) lens.1 (hiReg_length L hw) (by omega) (by omega)
  have b2 := buildTriple_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega)
  have b1 := buildDual_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) (by omega)
  have i3 := unbuildQuad_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) (hostU L) lens.1 (hiReg_length L hw) (by omega)
  have i2 := unbuildTriple_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega)
  have i1 := unbuildDual_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega)
  have mids := cm.proof.support (hosts L) (middle L c) cm.out
  intro x member
  simp only [newLoop,wires_append,Finset.mem_union] at member
  simp only [oldLoop,wires_append,Finset.mem_union]
  rcases member with (h | h) | h
  · rcases Finset.mem_insert.mp (b3 h) with eq | h
    · subst x; exact Or.inl (by simp [extras])
    rcases Finset.mem_insert.mp (b2 h) with eq | h
    · subst x; exact Or.inl (by simp [extras])
    rcases Finset.mem_insert.mp (b1 h) with eq | h
    · subst x; exact Or.inl (by simp [extras])
    exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr (mids.1 h)))
  · rcases Finset.mem_insert.mp (i3 h) with eq | h
    · subst x; exact Or.inl (by simp [extras])
    rcases Finset.mem_insert.mp (i2 h) with eq | h
    · subst x; exact Or.inl (by simp [extras])
    rcases Finset.mem_insert.mp (i1 h) with eq | h
    · subst x; exact Or.inl (by simp [extras])
    exact Or.inr (Or.inr h)

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
  simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,oldLoop,middle,prefixP,suffixP,List.append_assoc]

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
    wires (newBody L c cm) ⊆ wires (ParkCarry10Develop.body L c) := by
  have usedR := (hasWire_iff _ _).mp ready.1.2.2.2.2
  have usedP := (hasWire_iff _ _).mp ready.2.1.2.2.2.2
  have usedU := (hasWire_iff _ _).mp ready.2.2.1.2.2.2.2
  intro x member
  rcases Finset.mem_union.mp (newBody_refined L hw c cm member) with extra | inside
  · simp only [extras,Finset.mem_insert,Finset.mem_singleton] at extra
    rcases extra with eq | eq | eq
    · exact eq.symm ▸ usedR
    · exact eq.symm ▸ usedP
    · exact eq.symm ▸ usedU
  · exact inside

/-- A later host is disjoint from the cached endpoints by exact support, not no-write folklore. -/
theorem off_cached (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Wire) (fresh : x ∉ L.core.cin::(hiReg L++accReg L++accZ L++accBank L))
    (xq : x ≠ L.core.sumCarry) :
    x ∉ wires (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) ∧
    x ∉ wires (unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := by
  have lens := acc_lengths L hw
  have old := wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    x lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) fresh
  constructor
  · intro h
    exact (Finset.mem_insert.mp (buildCached_support _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) (by omega) h)).elim xq old.1
  · intro h
    exact (Finset.mem_insert.mp (unbuildConsumed_support _ _ _ _ _ _ lens.1
      (hiReg_length L hw) (by omega) h)).elim xq old.2

theorem loop_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (c : Wire) (ready : Ready L c)
    (cm : CheckedMany (hosts L) (middle L c)) (old : GatePhysical (oldLoop L c)) :
    GatePhysical (newLoop L c cm) := by
  have lens := acc_lengths L hw
  have rr := ready.1.1
  have pp := ready.2.1.1
  have uu := ready.2.2.1.1
  have nd := ready.2.2.2
  have pr : hostP L ≠ hostR L := by
    have h := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    intro eq; exact h (by simp [eq])
  have ur : hostU L ≠ hostR L := by
    have h := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    intro eq; exact h (by simp [eq])
  have up : hostU L ≠ hostP L := by
    have h := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp nd).2).2).1
    intro eq; exact h (by simp [eq])
  have offR := off_cached L hw hn (hostR L) rr.2.1 rr.2.2.1
  have offP := off_cached L hw hn (hostP L) pp.2.1 pp.2.2.1
  have offPDual : hostP L ∉ wires (buildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) ∧
      hostP L ∉ wires (unbuildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (hostR L)) := by
    constructor
    · intro h
      exact (Finset.mem_insert.mp (buildDual_support _ _ _ _ _ _ _ lens.1
        (hiReg_length L hw) (by omega) (by omega) h)).elim pr offP.1
    · intro h
      exact (Finset.mem_insert.mp (unbuildDual_support _ _ _ _ _ _ _ lens.1
        (hiReg_length L hw) (by omega) h)).elim pr offP.2
  have offU := fresh_off_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) (hostU L) lens.1 (hiReg_length L hw)
    (wTerms_fits L hw hn) uu.2.1 uu.2.2.1 ur up
  simp only [oldLoop,gatePhysical_append] at old
  have f1 := buildDual_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) (by omega) offR.1 old.1.1
  have i1 := unbuildDual_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) lens.1 (hiReg_length L hw) (by omega) offR.2 old.2
  have f2 := buildTriple_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega) offPDual.1 f1
  have i2 := unbuildTriple_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) lens.1 (hiReg_length L hw) (by omega) offPDual.2 i1
  have f3 := buildQuad_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) (hostU L) lens.1 (hiReg_length L hw) (by omega) (by omega) offU.1 f2
  have i3 := unbuildQuad_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (hostR L) (hostP L) (hostU L) lens.1 (hiReg_length L hw) (by omega) offU.2 i2
  have middlePhysical := cm.proof.physical (hosts L) (middle L c) cm.out old.1.2
  simpa only [newLoop,gatePhysical_append] using And.intro (And.intro f3 middlePhysical) i3

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
            have improved := newBody_resources L hw c cm
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

end ECDSAAdd.Entrant.BThreeTemp
