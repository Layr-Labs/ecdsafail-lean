import ECDSAAdd.Submission.Entrant.LowAccGeometry
namespace ECDSAAdd.Entrant.LowAccCarryDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ManyACarryDevelop FullBTemp ZeroReadDevelop FourthASavedCarryDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots
attribute [local irreducible] ECDSAAdd.regValue ECDSAAdd.Arithmetic.GatePhysical
attribute [local irreducible] hasWire

theorem layout_control_nodup : (c::L.wires).Nodup := by
 have full:=Baselines.layout.streamedSquare_control_nodup Baselines.layout_widths Baselines.layout_nodup
 exact List.nodup_cons.mpr ⟨(fun h=>(List.nodup_cons.mp full).1 (List.mem_cons_of_mem _ h)),layout_nodup⟩
theorem control_outside : c∉L.wires := (List.nodup_cons.mp layout_control_nodup).1
theorem endpoints_support :
 wires (buildMany 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L))⊆wires (ParkCarry10Develop.body L c) ∧
 wires (unbuildMany 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L))⊆wires (ParkCarry10Develop.body L c) := by
 have hw:=layout_widths
 have ready : FullBTemp.Ready L c := FullBReady.actual_ready
 have lens:=acc_lengths L hw
 have bf:=ManyACarryDevelop.buildMany_support 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ga_length src_length (by rw [pad_length];omega) (by rw [bank_length];omega) (by decide)
 have bi:=ManyACarryDevelop.unbuildMany_support 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ga_length src_length (by rw [bank_length];omega) (by decide)
 rw [ghost_build] at bf
 rw [ghost_unbuild] at bi
 have tri:=WholePadTriple.support (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) lens.1 src_length (FullFitReady.sound L ready.2.2.2.2.1)
 have dom (x:Wire) (hx:x∈(FullBTemp.hostP L::FullBTemp.hostR L::L.core.sumCarry::L.core.cin::(hiReg L++accReg L++FullBTemp.pad L++accBank L)).toFinset):
  x∈wires (ParkCarry10Develop.body L c) := by
  apply (hasWire_iff _ _).mp
  exact ready.2.2.2.2.2 x (List.mem_toFinset.mp hx)
 have used (x:Wire) (hx:x∈loans88.toFinset):x∈wires (ParkCarry10Develop.body L c) := by
  have hh:=List.mem_toFinset.mp hx
  simp only [loans88,List.mem_append] at hh
  rcases hh with hh|hh
  · have member : x∈FullBTemp.hosts L :=
     List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh)
    exact (hasWire_iff _ _).mp (ready.2.2.1 x member).2.2.2.2
  · exact dom x (by simp [List.mem_of_mem_take hh])
 constructor
 · intro x hx
   rcases Finset.mem_union.mp (bf hx) with hx|hx
   · exact dom x (tri.1 hx)
   · exact used x hx
 · intro x hx
   rcases Finset.mem_union.mp (bi hx) with hx|hx
   · exact dom x (tri.2 hx)
   · exact used x hx

theorem middle_support : wires (FullBTemp.middle L c)⊆wires (ParkCarry10Develop.body L c) := by
 intro x hx
 simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,FullBTemp.middle,BThreeTemp.middle,wires_append,Finset.mem_union] at hx ⊢
 aesop

theorem prefix_support : wires beforeLoop⊆wires (ParkCarry10Develop.body L c) := by
 have oldShape:=FullBTemp.oldBody_shape L c
 intro x hx
 simp only [beforeLoop,wires_append,Finset.mem_union] at hx
 rcases hx with hx|hx|(hx|hx)
 · rw [oldShape];simp only [FullBTemp.prefixP,wires_append,Finset.mem_union];aesop
 · rw [oldShape];simp only [FullBTemp.prefixP,wires_append,Finset.mem_union];aesop
 · rw [oldShape];simp only [FullBTemp.prefixP,wires_append,Finset.mem_union];aesop
 · exact endpoints_support.1 hx

theorem suffix_support : wires afterLoop⊆wires (ParkCarry10Develop.body L c) := by
 intro x hx
 change x∈wires (_ ++ FullBTemp.suffixP L c) at hx
 rw [wires_append,Finset.mem_union] at hx
 rcases hx with hx|hx
 · exact endpoints_support.2 hx
 · rw [FullBTemp.oldBody_shape];simp only [wires_append,Finset.mem_union];exact Or.inr (Or.inr hx)

theorem body_support (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c)) :
 wires (bodyWith cm)⊆wires (ParkCarry10Develop.body L c) := by
 rw [body_shape]
 simp only [wires_append,Finset.union_subset_iff]
 exact ⟨⟨prefix_support,(cm.proof.support hosts88 (FullBTemp.middle L c) cm.out).1.trans middle_support⟩,suffix_support⟩


theorem loop_physical (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c))
 (mid : GatePhysical (FullBTemp.middle L c)) : GatePhysical (loopWith cm) := by
 have offQ:=wloop_original_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry ga_length src_length fit fresh_q
 have offR:=wloop_original_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) (FullBTemp.hostR L) ga_length src_length fit fresh_r
 have offP:=wloop_original_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) (FullBTemp.hostP L) ga_length src_length fit fresh_p
 have dualOff:=SeedPadDevelop.dual_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ga_length src_length
  (by rw [pad_length];omega) (by rw [bank_length];omega) offP.1 offP.2 (by decide +kernel) (by decide +kernel)
 have plainF:=(NarrowAcc.build8_physical ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) ga_length (by rw [src_length]) fit).1
 have plainI:=SourceAddFourDevelop.unbuild_physical ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) ga_length src_length fit
 have cachedF:=buildCached_physical ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry ga_length src_length
  (by rw [pad_length];omega) (by rw [bank_length];omega) offQ.1 plainF
 have cachedI:=unbuildConsumed_physical ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry ga_length src_length
  (by rw [bank_length];omega) offQ.2 plainI
 have supportF:=buildCached_support ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
  ga_length src_length (by rw [pad_length];omega) (by rw [bank_length];omega)
 have supportI:=unbuildConsumed_support ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
  ga_length src_length (by rw [bank_length];omega)
 have rne : FullBTemp.hostR L≠L.core.sumCarry := by decide +kernel
 have cachedOffR :
  FullBTemp.hostR L∉wires (buildCached ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) ∧
  FullBTemp.hostR L∉wires (unbuildConsumed ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) :=
  ⟨fun h=>(Finset.mem_insert.mp (supportF h)).elim rne offR.1,
   fun h=>(Finset.mem_insert.mp (supportI h)).elim rne offR.2⟩
 have dualF:=buildDual_physical ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L)
  ga_length src_length (by rw [pad_length];omega) (by rw [bank_length];omega) cachedOffR.1 cachedF
 have dualI:=unbuildDual_physical ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L)
  ga_length src_length (by rw [bank_length];omega) cachedOffR.2 cachedI
 have triF:=buildTriple_physical ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)
  ga_length src_length (by rw [pad_length];omega) (by rw [bank_length];omega) dualOff.1 dualF
 have triI:=unbuildTriple_physical ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)
  ga_length src_length (by rw [bank_length];omega) dualOff.2 dualI
 have bankOff : ∀u∈loans88,u∉accBank L := by
  intro u hu h
  exact fresh_hosts u hu (by simp [h])
 have manyF:=ManyACarryDevelop.buildMany_physical 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ga_length src_length
  (by rw [pad_length];omega) (by rw [bank_length];omega) (by decide) bankOff triF
 have manyI:=ManyACarryDevelop.unbuildMany_physical 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ga_length src_length
  (by rw [bank_length];omega) (by decide) bankOff triI
 simp only [loopWith,gatePhysical_append]
 exact ⟨⟨manyF,cm.proof.physical hosts88 (FullBTemp.middle L c) cm.out mid⟩,manyI⟩

theorem body_physical (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c)) : GatePhysical (bodyWith cm) := by
 have old:=ParkCarry10Develop.body_physical L layout_widths c layout_control_nodup
 have oldMid:=old
 simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,gatePhysical_append] at oldMid
 have mid : GatePhysical (FullBTemp.middle L c) := oldMid.2.2.1.2.2.1
 rw [FullBTemp.oldBody_shape] at old
 simp only [gatePhysical_append] at old
 have shape : bodyWith cm=FullBTemp.prefixP L++(loopWith cm++FullBTemp.suffixP L c) := by
  simp only [bodyWith,foldWith,FullBTemp.prefixP,FullBTemp.suffixP,List.append_assoc]
 rw [shape]
 simp only [gatePhysical_append]
 exact ⟨old.1,loop_physical cm mid,old.2.2⟩


open FourthASavedCarryDevelop

theorem loop_resources (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c)) :
 toffoliCount (loopWith cm)+88≤toffoliCount (FullBTemp.oldLoop L c) ∧
 measurementCount (loopWith cm)=measurementCount (FullBTemp.oldLoop L c) ∧
 Challenge.gateSlots (loopWith cm)+264≤Challenge.gateSlots (FullBTemp.oldLoop L c) := by
 have hw:=layout_widths
 have ready : FullBTemp.Ready L c := FullBReady.actual_ready
 have lens:=acc_lengths L hw
 have plen:=FullBTemp.pad_length L hw
 have f1:=buildDual_counts (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L) lens.1 (hiReg_length L hw) (by omega) (by omega)
 have f2:=buildTriple_counts (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) lens.1 (hiReg_length L hw) (by omega) (by omega)
 have f3:=ManyACarryDevelop.buildMany_counts 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ga_length src_length (by rw [pad_length];omega) (by rw [bank_length];omega) (by decide) loans_length
 have i1:=unbuildDual_counts (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L) lens.1 (hiReg_length L hw) (by omega)
 have i2:=unbuildTriple_counts (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) lens.1 (hiReg_length L hw) (by omega)
 have i3:=ManyACarryDevelop.unbuildMany_counts 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ga_length src_length (by rw [bank_length];omega) (by decide) loans_length
 rw [ghost_build] at f3
 rw [ghost_unbuild] at i3
 have f4 := ready.2.2.2.1.1
 have i4 := ready.2.2.2.1.2
 change SeedPadDevelop.Counts (buildCached (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
  (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) at f4
 change SeedPadDevelop.Counts (unbuildConsumed (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
  (unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) at i4
 simp only [f4.1,f4.2.1,f4.2.2,i4.1,i4.2.1,i4.2.2] at f1 i1
 have mt:=cm.proof.toffoli hosts88 (FullBTemp.middle L c) cm.out
 have mm:=cm.proof.measurements hosts88 (FullBTemp.middle L c) cm.out
 have ms:=cm.proof.slots hosts88 (FullBTemp.middle L c) cm.out
 simp only [FullBTemp.middle] at mt mm ms
 simp only [loopWith,FullBTemp.oldLoop,BThreeTemp.oldLoop,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩


theorem body_resource_context (oldBody newBody pre oldMiddle newMiddle post : Program)
 (oldShape : oldBody=pre++(oldMiddle++post))
 (newShape : newBody=pre++(newMiddle++post))
 (h : toffoliCount newMiddle+88≤toffoliCount oldMiddle ∧
  measurementCount newMiddle=measurementCount oldMiddle ∧
  Challenge.gateSlots newMiddle+264≤Challenge.gateSlots oldMiddle) :
 toffoliCount newBody+88≤toffoliCount oldBody ∧
 measurementCount newBody=measurementCount oldBody ∧
 Challenge.gateSlots newBody+264≤Challenge.gateSlots oldBody := by
 rw [oldShape,newShape]
 simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

theorem body_resources (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c)) :
 toffoliCount (bodyWith cm)+88≤toffoliCount (ParkCarry10Develop.body L c) ∧
 measurementCount (bodyWith cm)=measurementCount (ParkCarry10Develop.body L c) ∧
 Challenge.gateSlots (bodyWith cm)+264≤Challenge.gateSlots (ParkCarry10Develop.body L c) := by
 have newShape : bodyWith cm=FullBTemp.prefixP L++(loopWith cm++FullBTemp.suffixP L c) := by
  simp only [bodyWith,foldWith,FullBTemp.prefixP,FullBTemp.suffixP,List.append_assoc]
 exact body_resource_context (ParkCarry10Develop.body L c) (bodyWith cm) (FullBTemp.prefixP L)
  (FullBTemp.oldLoop L c) (loopWith cm) (FullBTemp.suffixP L c)
  (FullBTemp.oldBody_shape L c) newShape (loop_resources cm)





theorem ga_bstate_value (base b : BasisState) (clean : L.PairClean base)
 (O E A : Nat) (hs : BState L base O E A b) (hd : A%16=0) : regValue ga b=A := by
 have hv : regValue (reg L) b=16*(A/16) := by
  change regValue (accReg L) b=16*(A/16)
  have hh:=hs.2.2.1
  omega
 have bridge:=ghostAcc_value L layout_widths b (A/16) hv
  (ghost_zero_bstate L layout_nodup base b clean O E A hs)
 exact bridge.trans hs.2.2.1

theorem initial_hosts_zero (base b : BasisState) (clean : L.PairClean base)
 (O E : Nat) (hs : BState L base O E 0 b) : ∀q∈hosts88,b q=false := by
 have geometry : ∀q∈hosts88,q∈L.core.work ∧ q∉L.core.out ∧ q∉eReg L := by decide +kernel
 intro q hq
 have geo:=geometry q hq
 by_cases ha:q∈accReg L
 · exact (regValue_zero _ _).mp hs.2.2.1 q ha
 · exact (hs.2.2.2 q geo.2.1 geo.2.2 ha).trans ((regValue_zero _ _).mp clean.work q geo.1)


theorem loop_eq_plain
 (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c))
 (s : State) (records : List Bool)
 (hz : ∀w∈FullBTemp.pad L,s.basis w=false)
 (hb : ∀w∈accBank L,s.basis w=false) (hi : s.basis L.core.cin=false)
 (ha : regValue ga s.basis=0) (zeroQ : s.basis L.core.sumCarry=false)
 (zeros : ∀q∈hosts88,s.basis q=false)
 (good : WReady ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  (regValue (hiReg L) s.basis)
  (middleState (NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L))
   (FullBTemp.middle L c) s records)) :
 run (loopWith cm) records s=
 run (NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) ++
  FullBTemp.middle L c ++ SourceAddFourDevelop.unbuild ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)) records s := by
 have zeroR : s.basis (FullBTemp.hostR L)=false := zeros _ (by simp [hosts88])
 have zeroP : s.basis (FullBTemp.hostP L)=false := zeros _ (by simp [hosts88])
 have zeroU : ∀u∈loans88,s.basis u=false := fun u hu=>zeros u (by simp [hosts88,hu])
 have offQ:=wloop_original_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry ga_length src_length fit fresh_q
 have offR:=wloop_original_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) (FullBTemp.hostR L) ga_length src_length fit fresh_r
 have offP:=wloop_original_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) (FullBTemp.hostP L) ga_length src_length fit fresh_p
 have pBoth:=SeedPadDevelop.dual_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ga_length src_length
  (by rw [pad_length];omega) (by rw [bank_length];omega) offP.1 offP.2 (by decide +kernel) (by decide +kernel)
 have endpoints : ∀u∈loans88,
  u∉wires (buildTriple ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)) ∧
  u∉wires (unbuildTriple ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)) := by
  intro u hu
  exact fresh_off_triple ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
   L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) u ga_length src_length fit
   (fresh_hosts u hu) (host_ne u hu).1 (host_ne u hu).2.1 (host_ne u hu).2.2
 have offOriginal : ∀u∈hosts88,u∉wires (NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)) := by
  intro u hu
  exact (wloop_original_off ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) u ga_length src_length fit (fresh_all_hosts u hu)).1
 have midEq:=cm.proof.middle_eq hosts88 (FullBTemp.middle L c) cm.out
  (NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)) s records zeros offOriginal
 have goodNew : WReady ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  (regValue (hiReg L) s.basis)
  (middleState (NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)) cm.out s records) := by
  rw [midEq];exact good
 have support:=cm.proof.support hosts88 (FullBTemp.middle L c) cm.out
 have rawAway : L.core.sumCarry∉wires (FullBTemp.middle L c) :=
  ParkCarry10Develop.mid_sumCarry_free L layout_widths layout_nodup c control_outside
 have nq : L.core.sumCarry∉wires cm.out := fun h=>rawAway (support.1 h)
 have nr : FullBTemp.hostR L∉wires cm.out := support.2 _ (by simp [hosts88])
 have np : FullBTemp.hostP L∉wires cm.out := support.2 _ (by simp [hosts88])
 have triple:=triple_middle_ready ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) cm.out ga_length src_length fit
  s records hz hb hi ha zeroQ zeroR zeroP fresh_q fresh_r (by decide +kernel) fresh_p
  (by decide +kernel) (by decide +kernel) offQ.1 nq offQ.2 offR.1 nr offR.2 pBoth.1 np pBoth.2 goodNew
 have many:=ManyACarryDevelop.cached_wloop_many_eq 86 ga (FullBTemp.pad L) (accBank L) L.core.cin
  (hiReg L) loans88 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) cm.out ga_length src_length fit
  s records hz hb hi ha zeroQ zeroR zeroP zeroU fresh_q fresh_r (by decide +kernel)
  fresh_p (by decide +kernel) (by decide +kernel) (by decide) loans_nd loans_length fresh_hosts host_ne
  offQ.1 offQ.2 offR.1 offR.2 pBoth.1 pBoth.2 (fun u hu=>(endpoints u hu).1)
  (fun u hu=>support.2 u (by simp [hosts88,hu])) (fun u hu=>(endpoints u hu).2)
  triple.1 triple.2.1 triple.2.2.1 triple.2.2.2
 have tr:=cached_wloop_triple_eq ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) cm.out ga_length src_length fit
  s records hz hb hi ha zeroQ zeroR zeroP fresh_q fresh_r (by decide +kernel) fresh_p
  (by decide +kernel) (by decide +kernel) offQ.1 nq offQ.2 offR.1 nr offR.2 pBoth.1 np pBoth.2 goodNew
 have du:=cached_wloop_dual_eq ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (FullBTemp.hostR L) cm.out ga_length src_length fit
  s records hz hb hi ha zeroQ zeroR fresh_q fresh_r (by decide +kernel) offQ.1 nq offQ.2 offR.1 nr offR.2 goodNew
 have re:=cm.proof.surround_eq hosts88 (FullBTemp.middle L c) cm.out
  (NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L))
  (SourceAddFourDevelop.unbuild ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)) s records zeros offOriginal
 simpa only [loopWith] using many.trans (tr.trans (du.trans re))


theorem ghost_wready (b : State) (H : Nat)
 (old : WReady (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) H b)
 (hz : ∀q∈ghosts L,b.basis q=false) :
 WReady ga (accZ L) (accBank L) L.core.cin (hiReg L) H b := by
 have hv : regValue (reg L) b.basis=16*(268435517*H) := by
  change regValue (accReg L) _=_
  have h:=old.1
  omega
 have bridge:=ghostAcc_value L layout_widths b.basis _ hv hz
 exact ⟨bridge.trans old.1,old.2⟩


theorem middle_state_post (P Q R : BasisState → Prop) (first middle : Program)
 (hf : Triple P first Q) (hm : Triple Q middle R) (s : State) (records : List Bool)
 (hs : P s.basis) : R (middleState first middle s records).basis := by
 exact (hm (run first (records.take (measurementCount first)) s)
  ((records.drop (measurementCount first)).take (measurementCount middle))
  (hf s (records.take (measurementCount first)) hs).2).2


theorem loop_bstate_step
 (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c))
 (base : BasisState) (clean : L.PairClean base) (hsum : base L.core.sumCarry=false)
 (O E O' : Nat)
 (mid : Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (FullBTemp.middle L c)
  (BState L base O' E (4294968272*regValue (hiReg L) base))) :
 Triple (BState L base O E 0) (loopWith cm) (BState L base O' E 0) := by
 intro s records hs
 have hw:=layout_widths
 have hn:=layout_nodup
 have lens:=acc_lengths L hw
 obtain ⟨hzFull,hb,hi,_,_⟩:=zero_regs L hn base clean O E 0 s.basis hs
 have hz : ∀q∈FullBTemp.pad L,s.basis q=false := fun q hq=>hzFull q ((FullPadDevelop.pad_sublist L).subset hq)
 have source0 : regValue (hiReg L) s.basis=regValue (hiReg L) base :=
  regValue_congr _ _ _ (fun q hq=>bstate_other L hn base O E 0 s.basis hs q (Or.inl hq))
 have fullInfo :
  WReady (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
   (regValue (hiReg L) s.basis) (middleState (wBuild L) (FullBTemp.middle L c) s records) ∧
  (∀q∈ghosts L,(middleState (wBuild L) (FullBTemp.middle L c) s records).basis q=false) := by
  have midGood := middle_state_post (BState L base O E 0)
   (BState L base O E (4294968272*regValue (hiReg L) base))
   (BState L base O' E (4294968272*regValue (hiReg L) base))
   (wBuild L) (FullBTemp.middle L c) (wBuild_step L hw hn base clean O E) mid s records hs
  obtain ⟨mz,mb,mi,_,_⟩:=zero_regs L hn base clean O' E _ _ midGood
  have source1:=regValue_congr (hiReg L) _ base (fun q hq=>bstate_other L hn base O' E _ _ midGood q (Or.inl hq))
  exact ⟨⟨midGood.2.2.1.trans (by rw [source0]),source1.trans source0.symm,mz,mb,mi⟩,
   ghost_zero_bstate L hn base _ clean O' E _ midGood⟩
 have goodGhost : WReady ga (accZ L) (accBank L) L.core.cin (hiReg L)
  (regValue (hiReg L) s.basis) (middleState (wBuild L) (FullBTemp.middle L c) s records) :=
  ghost_wready _ _ fullInfo.1 fullInfo.2
 have midPadEq:=WholePadDevelop.middle_repad (accReg L) (accZ L) (FullBTemp.pad L) (accBank L) L.core.cin
  (hiReg L) (FullBTemp.middle L c) lens.1 src_length (wTerms_fits L hw hn) (FullBTemp.terms_fits L hw hn)
  s records hzFull hz hb hi hs.2.2.1
 have goodPad : WReady ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
  (regValue (hiReg L) s.basis)
  (middleState (NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)) (FullBTemp.middle L c) s records) := by
  rw [ghost_plain_build,←midPadEq]
  exact ⟨goodGhost.1,goodGhost.2.1,(fun q hq=>goodGhost.2.2.1 q ((FullPadDevelop.pad_sublist L).subset hq)),goodGhost.2.2.2⟩
 have away:=ParkCarryDevelop.sumCarry_off_regs L hn
 have zeroQ : s.basis L.core.sumCarry=false := (hs.2.2.2 _ away.1 away.2.1 away.2.2).trans hsum
 have eqNew:=loop_eq_plain cm s records hz hb hi (ga_bstate_value base s.basis clean O E 0 hs (by decide))
  zeroQ (initial_hosts_zero base s.basis clean O E hs) goodPad
 have repad:=WholePadDevelop.plain_loop_repad (accReg L) (accZ L) (FullBTemp.pad L) (accBank L) L.core.cin
  (hiReg L) (FullBTemp.middle L c) lens.1 src_length (wTerms_fits L hw hn) (FullBTemp.terms_fits L hw hn)
  (FullPadDevelop.pad_sublist L).subset s records hzFull hb hi hs.2.2.1 (regValue (hiReg L) s.basis)
  (by simpa only [wBuild,middleState,run_take] using fullInfo.1)
 have finalEq : run (loopWith cm) records s=run (wBuild L++FullBTemp.middle L c++wUnbuildKnown L) records s := by
  rw [eqNew,ghost_plain_build,ghost_plain_unbuild]
  simpa only [wBuild,wUnbuildKnown] using repad.symm
 rw [finalEq]
 exact (((wBuild_step L hw hn base clean O E).seq mid).seq (wUnbuildKnown_step L hw hn base clean O' E)) s records hs



end ECDSAAdd.Entrant.LowAccCarryDevelop
