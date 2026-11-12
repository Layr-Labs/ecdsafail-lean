import ECDSAAdd.Submission.Entrant.FullB
section
-- Proof source component: LowAccGeometry
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowAccCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run

def ghosts (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.normFlag]
def reg (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 163
def ghostAcc (L : CuccaroStreamedSquareWideLayout) : List Wire := ghosts L ++ (reg L).drop 4

theorem ghostAcc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (b : BasisState) (K : Nat) (hv : regValue (reg L) b=16*K)
 (hz : ∀w∈ghosts L,b w=false) : regValue (ghostAcc L) b=regValue (reg L) b := by
 have len : (reg L).length=163 := by simp [reg,hw.core.work]
 have low : regValue ((reg L).take 4) b=0 := by
  rw [regValue_take_mod _ 4 (by omega) b,hv]
  omega
 have old : regValue (reg L) b=16*regValue ((reg L).drop 4) b := by
  calc
   _=regValue (((reg L).take 4)++(reg L).drop 4) b := by rw [List.take_append_drop]
   _=_ := by rw [regValue_append,low];simp [len]
 have gz : regValue (ghosts L) b=0 := (regValue_zero _ _).mpr hz
 rw [ghostAcc,regValue_append,gz]
 simpa [ghosts] using old.symm


theorem ghostAcc_drop (L : CuccaroStreamedSquareWideLayout) (n : Nat) (hn : 4≤n) :
 (ghostAcc L).drop n = (reg L).drop n := by
 have gl : (ghosts L).length=4 := rfl
 have gd : (ghosts L).drop n=[] := List.drop_eq_nil_of_le (by omega)
 rw [ghostAcc,List.drop_append,gd,List.nil_append,gl,List.drop_drop]
 congr 1
 omega

theorem ghostAcc_take_drop (L : CuccaroStreamedSquareWideLayout) (w n : Nat) (hn : 4≤n) :
 ((ghostAcc L).take w).drop n = ((reg L).take w).drop n := by
 rw [List.drop_take,List.drop_take,ghostAcc_drop L n hn]


namespace Structural
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open LowAccCarryDevelop InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem ty (L : CuccaroStreamedSquareWideLayout) (src : List Wire) (neg : Bool) (n : Nat) (hn : 4≤n) :
 Acc.ty (ghostAcc L) (Acc.earlyTerm src neg n)=Acc.ty (accReg L) (Acc.earlyTerm src neg n) := by
 change (ghostAcc L).drop n=(accReg L).drop n
 exact ghostAcc_drop L n hn

theorem ty_take (L : CuccaroStreamedSquareWideLayout) (src : List Wire) (neg : Bool) (w n : Nat) (hn : 4≤n) :
 Acc.ty ((ghostAcc L).take w) (Acc.earlyTerm src neg n)=Acc.ty ((accReg L).take w) (Acc.earlyTerm src neg n) := by
 change ((ghostAcc L).take w).drop n=((accReg L).take w).drop n
 exact ghostAcc_take_drop L w n hn

theorem buildTriple_eq (L : CuccaroStreamedSquareWideLayout) (Z bank src : List Wire) (cin q r p : Wire) :
 buildTriple (ghostAcc L) Z bank cin src q r p=buildTriple (accReg L) Z bank cin src q r p := by
 simp only [buildTriple,buildPre,buildPost,Acc.seedOp,Acc.op]
 rw [ty L src false 4 (by decide +kernel),ty_take L src false 139 10 (by decide +kernel),
  ty_take L src true 139 6 (by decide +kernel),ty_take L src false 161 32 (by decide +kernel)]

theorem unbuildTriple_eq (L : CuccaroStreamedSquareWideLayout) (Z bank src : List Wire) (cin q r p : Wire) :
 unbuildTriple (ghostAcc L) Z bank cin src q r p=unbuildTriple (accReg L) Z bank cin src q r p := by
 simp only [unbuildTriple,unbuildPre,unbuildPost,CodexKnownOnesTail.accSub,SourceTailDevelop.tail,Acc.seedOp]
 rw [ty_take L src false 161 32 (by decide +kernel),
  ghostAcc_take_drop L 139 6 (by decide +kernel),ghostAcc_take_drop L 139 10 (by decide +kernel),
  ty L src false 4 (by decide +kernel)]
 simp only [LowAccCarryDevelop.reg,accReg]

theorem plain_build_eq (L : CuccaroStreamedSquareWideLayout) (Z bank src : List Wire) (cin : Wire) :
 NarrowAcc.build8 (ghostAcc L) Z bank cin src=NarrowAcc.build8 (accReg L) Z bank cin src := by
 simp only [NarrowAcc.build8,NarrowAcc.pre8,CodexNarrowSub.accSub,Acc.seedOp,Acc.op]
 rw [ty L src false 4 (by decide +kernel),ty_take L src false 139 10 (by decide +kernel),
  ty_take L src true 139 6 (by decide +kernel),ty_take L src false 161 32 (by decide +kernel)]

theorem plain_unbuild_eq (L : CuccaroStreamedSquareWideLayout) (Z bank src : List Wire) (cin : Wire) :
 SourceAddFourDevelop.unbuild (ghostAcc L) Z bank cin src=SourceAddFourDevelop.unbuild (accReg L) Z bank cin src := by
 simp only [SourceAddFourDevelop.unbuild,CodexKnownOnesTail.accSub,SourceAddFourDevelop.add,SourceTailDevelop.tail,Acc.seedOp]
 rw [ty_take L src false 161 32 (by decide +kernel),
  ghostAcc_take_drop L 139 6 (by decide +kernel),ghostAcc_take_drop L 139 10 (by decide +kernel),
  ty L src false 4 (by decide +kernel)]
 simp only [LowAccCarryDevelop.reg,accReg]
end Structural

theorem ghost_zero_bstate (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup)
 (base b : BasisState) (clean : L.PairClean base) (O E A : Nat)
 (hs : ControlLoan1589BFFold.BState L base O E A b) : ∀q∈ghosts L,b q=false := by
 intro q hq
 simp only [ghosts,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl|rfl
 · exact (ControlLoan1589BFFold.bstate_other L hn base O E A b hs _ (by simp)).trans clean.productHigh
 · exact (ControlLoan1589BFFold.bstate_other L hn base O E A b hs _ (by simp)).trans clean.outHigh
 · exact (ControlLoan1589BFFold.bstate_other L hn base O E A b hs _ (by simp)).trans clean.workHigh
 · exact (ControlLoan1589BFFold.bstate_other L hn base O E A b hs _ (by simp)).trans clean.normFlag


open InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ManyACarryDevelop FullBTemp ZeroReadDevelop

def L : CuccaroStreamedSquareWideLayout := FullBReady.L
def c : Wire := FullBReady.c
def ga : List Wire := ghostAcc L
def loans88 : List Wire := FullBTemp.loans L ++ (accReg L).take 4
def hosts88 : List Wire := FullBTemp.hostR L :: FullBTemp.hostP L :: loans88

theorem ga_length : ga.length=163 := by decide +kernel
theorem src_length : (hiReg L).length=128 := by decide +kernel
theorem pad_length : (FullBTemp.pad L).length=31 := by decide +kernel
theorem bank_length : (accBank L).length=160 := by decide +kernel
theorem loans_length : loans88.length=86 := by decide +kernel
theorem loans_nd : loans88.Nodup := by decide +kernel
theorem fit_nodup : (L.core.cin::(hiReg L++ga++(FullBTemp.pad L)++accBank L)).Nodup := by decide +kernel

theorem fit : ∀f∈earlyHTerms (hiReg L),Acc.Fits ga (FullBTemp.pad L) (accBank L) L.core.cin 163 f := by
 intro f hf
 simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
 rcases hf with rfl|rfl|rfl|rfl
 all_goals exact {len:=by decide +kernel,zpad:=by decide +kernel,bankLen:=by decide +kernel,nd:=fit_nodup}

theorem fresh_q : L.core.sumCarry∉L.core.cin::(hiReg L++ga++FullBTemp.pad L++accBank L) := by decide +kernel
theorem fresh_r : FullBTemp.hostR L∉L.core.cin::(hiReg L++ga++FullBTemp.pad L++accBank L) := by decide +kernel
theorem fresh_p : FullBTemp.hostP L∉L.core.cin::(hiReg L++ga++FullBTemp.pad L++accBank L) := by decide +kernel
theorem fresh_hosts : ∀u∈loans88,u∉L.core.cin::(hiReg L++ga++FullBTemp.pad L++accBank L) := by decide +kernel
theorem host_ne : ∀u∈loans88,u≠L.core.sumCarry ∧ u≠FullBTemp.hostR L ∧ u≠FullBTemp.hostP L := by decide +kernel


theorem ghost_build : buildTriple ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) =
 buildTriple (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) :=
 Structural.buildTriple_eq L (FullBTemp.pad L) (accBank L) (hiReg L) L.core.cin L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)

theorem ghost_unbuild : unbuildTriple ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) =
 unbuildTriple (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) :=
 Structural.unbuildTriple_eq L (FullBTemp.pad L) (accBank L) (hiReg L) L.core.cin L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)

theorem ghost_plain_build : NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) =
 NarrowAcc.build8 (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) :=
 Structural.plain_build_eq L (FullBTemp.pad L) (accBank L) (hiReg L) L.core.cin


theorem ghost_plain_unbuild : SourceAddFourDevelop.unbuild ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) =
 SourceAddFourDevelop.unbuild (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) :=
 Structural.plain_unbuild_eq L (FullBTemp.pad L) (accBank L) (hiReg L) L.core.cin


theorem fresh_all_hosts : ∀u∈hosts88,u∉L.core.cin::(hiReg L++ga++FullBTemp.pad L++accBank L) := by decide +kernel

theorem specials_nd : (L.core.sumCarry::FullBTemp.hostR L::FullBTemp.hostP L::loans88).Nodup := by decide +kernel

theorem success_literal : (ZeroSetDevelop.compileS? hosts88 BData301.p0).isSome=true := by decide +kernel

attribute [local irreducible] ZeroSetDevelop.compileS?

theorem success : (ZeroSetDevelop.compileS? hosts88 (FullBTemp.middle L c)).isSome=true :=
 (congrArg (fun p=>(ZeroSetDevelop.compileS? hosts88 p).isSome) FullBReady.onePass_input_eq).symm.trans success_literal


def loopWith (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c)) : Program :=
 buildMany 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ++ cm.out ++
 unbuildMany 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)

def foldWith (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c)) : Program :=
 eAddLo L ++ (loopWith cm ++ (ParkCarryDevelop.program (eU L) L.core.sumCarry ++ eSubK L))

def bodyWith (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c)) : Program :=
 measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++
  (foldWith cm ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L)))



def beforeLoop : Program :=
 measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++ (eAddLo L ++
  buildMany 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
   L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)))

def afterLoop : Program :=
 unbuildMany 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) loans88
  L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) ++
 (ParkCarryDevelop.program (eU L) L.core.sumCarry ++
  (eSubK L ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L)))

theorem body_shape (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c)) :
 bodyWith cm=beforeLoop++cm.out++afterLoop := by
 simp only [bodyWith,foldWith,loopWith,beforeLoop,afterLoop,List.append_assoc]

theorem layout_widths : L.Widths :=
 Baselines.layout.dialogStreamedSquareWide_widths Baselines.layout_widths

theorem layout_nodup : L.wires.Nodup := by
 have full := Baselines.layout.streamedSquare_control_nodup Baselines.layout_widths Baselines.layout_nodup
 exact (List.nodup_cons.mp (List.nodup_cons.mp full).2).2



end ECDSAAdd.Entrant.LowAccCarryDevelop

end

section
-- Proof source component: LowAccLoop
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

end

section
-- Proof source component: LowAccCarry
namespace ECDSAAdd.Entrant.LowAccCarryDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ManyACarryDevelop FullBTemp ZeroReadDevelop FourthASavedCarryDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
def fromLiteral (cm : ZeroSetDevelop.CheckedS hosts88 BData301.p0) :
 ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c) :=
 ⟨cm.out, Eq.mp (congrArg (fun p=>ZeroSetDevelop.SRewrites hosts88 p cm.out)
  (show BData301.p0=FullBTemp.middle L c from FullBReady.onePass_input_eq)) cm.proof⟩

open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
open LowBitCarryDevelop ParkCarry7Develop ParkCarry10Develop

def foldFor (L : CuccaroStreamedSquareWideLayout) (loop : Program) : Program :=
 eAddLo L ++ (loop ++ (ParkCarryDevelop.program (eU L) L.core.sumCarry ++ eSubK L))
def bodyFor (L : CuccaroStreamedSquareWideLayout) (c : Wire) (loop : Program) : Program :=
 measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++
  (foldFor L loop ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L)))

theorem body_frame_generic
 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hcw : c∉L.wires) (loopProgram : Program)
 (loopSpec : ∀ (base : BasisState) (clean : L.PairClean base) (hsum : base L.core.sumCarry=false)
  (O E O' : Nat),
  Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (FullBTemp.middle L c)
   (BState L base O' E (4294968272*regValue (hiReg L) base)) →
  Triple (BState L base O E 0) loopProgram (BState L base O' E 0))
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (bodyFor L c loopProgram)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by

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
  have loop := loopSpec base hc hsum
    O2 (2^32*H+l'+2^128*K) O3 wmBase
  have kc:=ParkCarryDevelop.park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (foldFor L loopProgram) (BState L baseK O3 E1 0) :=
    by simpa only [foldFor,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
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
  simpa only [bodyFor] using all




theorem body_frame
 (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c))
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (bodyWith cm)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) :=
 by
  have hcw : c∉L.wires := control_outside
  simpa only [bodyWith,foldWith,bodyFor,foldFor] using
   body_frame_generic L layout_widths layout_nodup c hcw (loopWith cm) (loop_bstate_step cm)
    base M hM hP hc hsum O hO hg hSource



end ECDSAAdd.Entrant.LowAccCarryDevelop
namespace ECDSAAdd.Entrant.FullB88OptTemp
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ECDSAAdd.Arithmetic.GatePhysical
attribute [local irreducible] ZeroSetDevelop.compileS? ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots ECDSAAdd.regValue
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem option_property {α : Type} (P : Program → Prop) (fallback : Program) (body : α → Program)
 (hf : P fallback) (hb : ∀a,P (body a)) (result : Option α) : P (result.elim fallback body) := by
 cases result with
 | none => exact hf
 | some a => exact hb a

theorem option_some_property {α : Type} (P : Program → Prop) (fallback : Program) (body : α → Program)
 (hb : ∀a,P (body a)) (result : Option α) (success : result.isSome=true) : P (result.elim fallback body) := by
 cases result with
 | none => simp only [Option.isSome_none,Bool.false_eq_true] at success
 | some a => exact hb a

theorem option_map_success {α β : Type} (result : Option α) (f : α → β) :
 (result.map f).isSome=result.isSome := by
 cases result <;> rfl

theorem actual_resources :
 toffoliCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)+88≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 measurementCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 Challenge.gateSlots (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)+264≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 exact option_some_property (fun p=>
  toffoliCount p+88≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
  measurementCount p=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
  Challenge.gateSlots p+264≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))
  (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith LowAccCarryDevelop.body_resources ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)
  ((option_map_success (ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0) LowAccCarryDevelop.fromLiteral).trans LowAccCarryDevelop.success_literal)

theorem actual_subset : wires (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 exact option_property (fun p=>wires p⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))
  (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith (Finset.Subset.refl (wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))) LowAccCarryDevelop.body_support ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

theorem actual_physical : GatePhysical (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := by
 exact option_property GatePhysical (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith
  (ParkCarry10Develop.body_physical LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths
   LowAccCarryDevelop.c LowAccCarryDevelop.layout_control_nodup)
  LowAccCarryDevelop.body_physical ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

theorem actual_frame (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue LowAccCarryDevelop.L.core.product base=M^2) (hc : LowAccCarryDevelop.L.PairClean base)
 (hsum : base LowAccCarryDevelop.L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base LowAccCarryDevelop.c=false → M=0)
 (hSource : M=if base LowAccCarryDevelop.c then regValue LowAccCarryDevelop.L.core.high base else 0) :
 Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O)) := by
 exact option_property (fun p=>Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) p
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O))) (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith
  (ParkCarry10Develop.body_frame LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths
   LowAccCarryDevelop.layout_nodup LowAccCarryDevelop.c LowAccCarryDevelop.control_outside
   base M hM hP hc hsum O hO hg hSource)
  (fun cm=>LowAccCarryDevelop.body_frame cm base M hM hP hc hsum O hO hg hSource) ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

def selectedBody (K : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
 match FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse _ => ParkCarry10Develop.body K g
 | isTrue _ => if g=LowAccCarryDevelop.c then (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) else ParkCarry10Develop.body K g

theorem selected_body_transport (K K' : CuccaroStreamedSquareWideLayout) (g g' : Wire)
 (he : K=K') (hg : g=g') : selectedBody K g=selectedBody K' g' := by
 cases he
 cases hg
 rfl

def hostedSelectedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 selectedBody (ParkCarryDevelop.hostLayout L rho) c

theorem selected_subset (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 wires (selectedBody K g)⊆wires (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact Finset.Subset.refl _
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_subset
  · exact Finset.Subset.refl _

theorem selected_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) : wires (selectedBody L c)⊆(c::L.wires).toFinset :=
 (selected_subset L hw c).trans (ParkCarry10Develop.body_support L hw hn c)

theorem selected_physical (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths)
 (g : Wire) (nd : (g::K.wires).Nodup) : GatePhysical (selectedBody K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact ParkCarry10Develop.body_physical K hw g nd
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_physical
  · exact ParkCarry10Develop.body_physical K hw g nd

theorem selected_frame (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (hn : K.wires.Nodup)
 (g : Wire) (hcw : g∉K.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue K.core.product base=M^2) (hc : K.PairClean base)
 (hsum : base K.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base g=false → M=0) (hSource : M=if base g then regValue K.core.high base else 0) :
 Triple (SquareFrame K.core.out base O) (selectedBody K g)
  (SquareFrame K.core.out base (bO4 (M^2) (base g) O)) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hne => exact ParkCarry10Develop.body_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource
 | isTrue hl =>
  dsimp only
  split
  · rename_i hgc;subst K;subst g;exact actual_frame base M hM hP hc hsum O hO hg hSource
  · exact ParkCarry10Develop.body_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource

theorem selected_resources (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 toffoliCount (selectedBody K g)≤toffoliCount (ParkCarry10Develop.body K g) ∧
 measurementCount (selectedBody K g)=measurementCount (ParkCarry10Develop.body K g) ∧
 Challenge.gateSlots (selectedBody K g)≤Challenge.gateSlots (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g
    have h:=actual_resources
    exact ⟨by omega,h.2.1,by omega⟩
  · exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩

theorem hostedSelectedBody_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire)
 (c : Wire) (fixed : rho L.core.sumCarry=L.core.sumCarry) :
 hostedSelectedBody L rho c=selectedBody L c :=
 congrArg (fun K=>selectedBody K c) (ParkCarryDevelop.host_eq L rho fixed)

theorem hosted_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedSelectedBody L rho c)≤toffoliCount (ParkCarry10Develop.hostedBody L rho c) ∧
 measurementCount (hostedSelectedBody L rho c)=measurementCount (ParkCarry10Develop.hostedBody L rho c) ∧
 Challenge.gateSlots (hostedSelectedBody L rho c)≤Challenge.gateSlots (ParkCarry10Develop.hostedBody L rho c) :=
 selected_resources (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 wires (hostedSelectedBody L rho c)⊆wires (ParkCarry10Develop.hostedBody L rho c) :=
 selected_subset (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen : 300≤ext.length)
 (away : ∀q∈ext,q∉L.wires) :
 wires (hostedSelectedBody L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
 rw [hostedSelectedBody_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact selected_support L hw hn c

abbrev actualLayout := FullBOptTemp.actualLayout
abbrev actualControl := FullBOptTemp.actualControl
abbrev actualExt := FullBOptTemp.actualExt
abbrev actualFoldPerm := FullBOptTemp.actualFoldPerm

theorem selected_actual : selectedBody LowAccCarryDevelop.L LowAccCarryDevelop.c=(((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq LowAccCarryDevelop.L LowAccCarryDevelop.L with
 | isFalse hn => exact False.elim (hn rfl)
 | isTrue hl => exact if_pos rfl

theorem ranked_selected_exact : hostedSelectedBody actualLayout actualFoldPerm actualControl=(((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := by
 have he : ParkCarryDevelop.hostLayout actualLayout actualFoldPerm=actualLayout :=
  FullBOptTemp.actualHostedLayout_eq
 exact (congrArg (fun K=>selectedBody K actualControl) he).trans
  ((selected_body_transport actualLayout LowAccCarryDevelop.L actualControl LowAccCarryDevelop.c rfl rfl).trans selected_actual)

theorem ranked_certified_gain :
 toffoliCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)+88≤4762 ∧
 measurementCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)=5924 := by
 rw [ranked_selected_exact]
 have h:=actual_resources
 have old:=ParkCarry10Develop.body_counts LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths LowAccCarryDevelop.c
 exact ⟨h.1.trans old.1.le,h.2.1.trans old.2⟩

end ECDSAAdd.Entrant.FullB88OptTemp

end

