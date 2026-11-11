import ECDSAAdd.Submission.Entrant.FullB

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
 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) := by decide +kernel

theorem ghost_unbuild : unbuildTriple ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) =
 unbuildTriple (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)
 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L) := by decide +kernel

theorem ghost_plain_build : NarrowAcc.build8 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) =
 NarrowAcc.build8 (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) := by decide +kernel


theorem ghost_plain_unbuild : SourceAddFourDevelop.unbuild ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) =
 SourceAddFourDevelop.unbuild (accReg L) (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) := by decide +kernel


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
