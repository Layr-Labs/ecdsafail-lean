import ECDSAAdd.Submission.Entrant.DirectDecoder.FiniteBase
import ECDSAAdd.Submission.Entrant.DirectDecoder.FiniteHigh
import ECDSAAdd.Submission.Entrant.DirectDecoder.FiniteInitial

/-! Reference arithmetic, certified initial/high polynomials, and generic phase-correct
triangular erasure helpers for CompareDecoder. Unused four-product runtime proofs and
low enumeration modules have been removed. -/
set_option autoImplicit false

-- Proof component: NoDoubleCarry
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCellCarryMath DecoderCells5 DecoderMeasuredTail

theorem no_double_step (p y a c : Bool) (h : (a && c)=false) :
 (carryBit p y a && ((p ^^ y ^^ a) && c))=false := by
 cases p <;> cases y <;> cases a <;> cases c <;> simp_all [carryBit]

theorem no_double_h0 (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j)
 (hs : b L.sigma=false) (hh : b L.h=false)
 (j : Nat) (hj : j<255) : (b (L.A j) && bExpected L b (j+1))=false := by
 induction j with
 | zero => rw [adds 0 (by decide)]; simp [aExpected,hs,carryBit]
 | succ n ih =>
   have hn : n<255 := by omega
   have aa := add_step L b adds (n+1) (by omega) hj
   simp only [Nat.add_sub_cancel,hs,Bool.xor_false] at aa
   rw [aa]
   by_cases first : n=0
   · subst n
     have a0 : b (L.A 0)=false := by rw [adds 0 (by decide)]; simp [aExpected,hs,carryBit]
     have c1 := g 1 (by decide) (by decide)
     have c2 := g 2 (by decide) (by decide)
     simp [correction,MappedBit.value,rawSources,parity,hh,carryBit] at c1
     simp only [Nat.reduceSub,show ¬2=1 by decide,ite_false] at c2
     rw [c1,raw_middle L b 1 (by decide) (by decide),a0,hs] at c2
     simp [correction,MappedBit.value] at c2
     rw [c2,a0]
     generalize b (L.Y 0)=p,b (L.Y 1)=y,b L.bias=d
     cases p <;> cases y <;> cases d <;> decide
   · have corr : (correction L (n+1)).value b=false := by
       simp only [correction,show ¬n+1=1 by omega,ite_false]
       split <;> simp [MappedBit.value,hh]
     rw [graph_zero_step L b g (n+1) (by omega) hj corr]
     simp only [Nat.add_sub_cancel,hs,Bool.xor_false]
     exact no_double_step _ _ _ _ (ih hn)

theorem no_double_invariant (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j)
 (_hh : (b L.sigma && b L.h)=false) (hb : (b L.sigma && b L.bias)=false)
 (j : Nat) (hj : j<255) : (b (L.A j) && bExpected L b (j+1) && !b L.h)=false := by
 cases he : b L.h
 · simp only [he,Bool.not_false,Bool.and_true]
   cases se : b L.sigma
   · exact no_double_h0 L b g adds se he j hj
   · have bz : b L.bias=false := by simpa [se] using hb
     have cz:=b_sigma_zero L b g he bz j hj
     rw [cz]
     simp
 · simp [he]
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: ReferenceChunk
-- This recurrence is kept independent of the experimental finite certificates.
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCellCarryMath DecoderCells5 DecoderMeasuredTail

def referenceSteps : List Bool → List Bool → Bool → Bool → Bool → Bool → List Bool
 | [],_,_,_,_,_=>[]
 | y::ys,d::ds,prev,sigma,a,c=>
   let raw:=prev ^^ y ^^ sigma ^^ a
   (raw ^^ d ^^ c)::referenceSteps ys ds y sigma (carryBit prev (y ^^ sigma) a) (carryBit d raw c)
 | _::_,[],_,_,_,_=>[]

theorem ref_r_middle (L : DecoderLayout) (b : BasisState) (j : Nat) (lo : 1≤j) (hi : j<255) :
 b (L.R j)=((b (L.Y (j-1)) ^^ b (L.Y j) ^^ b L.sigma ^^ b (L.A (j-1))) ^^
  (correction L j).value b ^^ bExpected L b j) := by
 rw [bExpected]
 have r:=raw_middle L b j lo hi
 simp only [bSources,parity_cat,correctionSources_parity,r]
 generalize b (L.R j)=v,b (L.Y (j-1))=p,b (L.Y j)=y,b L.sigma=s,b (L.A (j-1))=a,
   (correction L j).value b=d
 cases v <;> cases p <;> cases y <;> cases s <;> cases a <;> cases d <;> rfl

theorem reference_chunk (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j)
 (n i : Nat) (lo : 1 ≤ i) (hi : i + n ≤ 255) :
 referenceSteps ((List.range' i n).map (fun j=>b (L.Y j)))
   ((List.range' i n).map (fun j=>(correction L j).value b))
   (b (L.Y (i-1))) (b L.sigma) (b (L.A (i-1))) (bExpected L b i)=
 (List.range' i n).map (fun j=>b (L.R j)) := by
 induction n generalizing i with
 | zero=>rfl
 | succ n ih=>
   have il : i<255 := by omega
   simp only [List.range'_succ,List.map_cons,referenceSteps]
   rw [←ref_r_middle L b i lo il]
   have aa:=add_step L b adds i lo il
   have cc:=g (i+1) (by omega) (by omega)
   simp only [Nat.add_sub_cancel,show ¬i+1=1 by omega,ite_false] at cc
   rw [raw_middle L b i lo il] at cc
   rw [←aa,←cc]
   have done:=ih (i+1) (by omega) (by omega)
   simpa only [Nat.add_sub_cancel] using congrArg (List.cons (b (L.R i))) done

theorem ref_r_zero (L : DecoderLayout) (b : BasisState) (j : Nat) (lo : 1 ≤ j) (hi : j<255)
 (corr : (correction L j).value b=false) :
 b (L.R j)=(b (L.Y (j-1)) ^^ b (L.Y j) ^^ b L.sigma ^^ b (L.A (j-1)) ^^ bExpected L b j) := by
 rw [ref_r_middle L b j lo hi,corr,Bool.xor_false]

theorem reference_zero_pair (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j)
 (hh : (b L.sigma && b L.h)=false) (hb : (b L.sigma && b L.bias)=false)
 (j : Nat) (lo : 4 ≤ j) (hi : j<255)
 (corr : ∀k,j-3 ≤ k → k ≤ j → (correction L k).value b=false) :
 b (L.R j)=poly (b (L.Y (j-3))) (b (L.Y (j-2))) (b (L.Y (j-1)))
  (b (L.Y j)) (b L.sigma) (b (L.R (j-1))) := by
 have seed:=seed_graph L b g adds hh hb (j-3) (by omega) (by omega) (corr _ (by omega) (by omega))
 have ca:=add_step L b adds (j-2) (by omega) (by omega)
 have cb:=add_step L b adds (j-1) (by omega) (by omega)
 have qa:=graph_zero_step L b g (j-2) (by omega) (by omega) (corr _ (by omega) (by omega))
 have qb:=graph_zero_step L b g (j-1) (by omega) (by omega) (corr _ (by omega) (by omega))
 have rr:=ref_r_zero L b (j-1) (by omega) (by omega) (corr _ (by omega) (by omega))
 have rz:=ref_r_zero L b j (by omega) hi (corr _ (by omega) (by omega))
 have e1:j-3+1=j-2:=by omega
 have e2:j-2-1=j-3:=by omega
 have e3:j-1-1=j-2:=by omega
 have e4:j-2+1=j-1:=by omega
 have e5:j-1+1=j:=by omega
 rw [e1] at seed
 rw [e2] at ca qa
 rw [e3] at cb qb rr
 rw [e4] at qa
 rw [e5] at qb
 rw [rz,rr,cb,qb,ca,qa]
 exact pair_identity _ _ _ _ _ _ _ seed
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: PolynomialErasure
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder

def phaseValue : List Correction → BasisState → Bool
 | [],_=>false
 | .Z q::cs,b=>b q ^^ phaseValue cs b
 | .CZ a c::cs,b=>(b a && b c) ^^ phaseValue cs b

theorem correct_value (cs : List Correction) (s : State) :
 correct cs s=⟨s.phase ^^ phaseValue cs s.basis,s.basis⟩ := by
 induction cs generalizing s with
 | nil=>simp [correct,phaseValue]
 | cons c cs ih=>cases c <;> simp [correct,ih,phaseValue,Bool.xor_assoc]

theorem measure_poly (t : Wire) (cs : List Correction) (s : State) (m : List Bool)
 (known : s.basis t=phaseValue cs (writeBit s.basis t false)) :
 run [.measureX t [] cs] m s=⟨s.phase,writeBit s.basis t false⟩ := by
 simp only [run,measureAndCorrect]
 cases hm:m.headD false
 · simp [hm,correct]
 · simp only [hm,ite_true,Bool.true_and,correct_value]
   rw [known]
   simp [Bool.xor_assoc]

theorem phaseValue_congr (cs : List Correction) (b c : BasisState)
 (h : ∀q∈correctionWires cs,b q=c q) : phaseValue cs b=phaseValue cs c := by
 induction cs with
 | nil=>rfl
 | cons op cs ih=>
   cases op <;> simp only [phaseValue]
   all_goals
     rw [ih (fun q hq=>h q (by simp [correctionWires,hq]))]
   · rw [h _ (by simp [correctionWires])]
   · rw [h _ (by simp [correctionWires]),h _ (by simp [correctionWires])]

theorem phaseValue_update (cs : List Correction) (b : BasisState) (t : Wire)
 (ht : t∉correctionWires cs) : phaseValue cs (writeBit b t false)=phaseValue cs b := by
 apply phaseValue_congr
 intro q hq
 have ne : q≠t := by intro e;subst q;exact ht hq
 exact Function.update_of_ne ne _ _

theorem measure_poly_away (t : Wire) (cs : List Correction) (s : State) (m : List Bool)
 (away : t∉correctionWires cs) (known : s.basis t=phaseValue cs s.basis) :
 run [.measureX t [] cs] m s=⟨s.phase,writeBit s.basis t false⟩ := by
 apply measure_poly
 rw [phaseValue_update cs s.basis t away]
 exact known
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: TriangularErasure
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder

def eraseRange (target : Nat → Wire) (cs : Nat → List Correction) : Nat → Program
 | 0=>[]
 | n+1=>[.measureX (target n) [] (cs n)]++eraseRange target cs n







structure ErasedRange (target : Nat → Wire) (n : Nat) (s t : State) : Prop where
 phase:t.phase=s.phase
 outside:∀q,(∀i,i<n → q≠target i) → t.basis q=s.basis q
 cleared:∀i,i<n → t.basis (target i)=false

theorem eraseRange_correct (target : Nat → Wire) (cs : Nat → List Correction)
 (n : Nat)
 (inj : ∀i,i<n → ∀j,j<n → target i=target j → i=j)
 (away : ∀i,i<n → target i∉correctionWires (cs i))
 (tri : ∀i,i<n → ∀j,i<j → j<n → target j∉correctionWires (cs i))
 (s : State) (known : ∀i,i<n → s.basis (target i)=phaseValue (cs i) s.basis) (m : List Bool) :
 ErasedRange target n s (run (eraseRange target cs n) m s) := by
 induction n generalizing s m with
 | zero=>exact ⟨rfl,fun _ _=>rfl,fun _ h=>by omega⟩
 | succ n ih=>
   have er:=measure_poly_away (target n) (cs n) s m (away n (by omega)) (known n (by omega))
   let u:State:=⟨s.phase,writeBit s.basis (target n) false⟩
   have nk : ∀i,i<n → u.basis (target i)=phaseValue (cs i) u.basis := by
     intro i hi
     have ne : target i≠target n := by intro eq;have z:=inj i (by omega) n (by omega) eq;omega
     change writeBit s.basis (target n) false (target i)=phaseValue (cs i) (writeBit s.basis (target n) false)
     rw [phaseValue_update (cs i) s.basis (target n) (tri i (by omega) n hi (by omega))]
     exact (Function.update_of_ne ne _ _).trans (known i (by omega))
   have done:=ih (fun i hi j hj=>inj i (by omega) j (by omega))
     (fun i hi=>away i (by omega)) (fun i hi j hij hj=>tri i (by omega) j hij (by omega))
     u nk (m.drop 1)
   simp only [eraseRange,run_append,run_take]
   rw [er]
   change ErasedRange target (n+1) s (run (eraseRange target cs n) (m.drop 1) u)
   refine ⟨done.phase,?_,?_⟩
   · intro q hq
     exact (done.outside q (fun i hi=>hq i (by omega))).trans
       (Function.update_of_ne (hq n (by omega)) _ _)
   · intro i hi
     by_cases hn:i<n
     · exact done.cleared i hn
     · have eq:i=n:=by omega
       subst i
       rw [done.outside (target n) (by
         intro j hj e
         have z:=inj n (by omega) j (by omega) e
         omega)]
       exact Function.update_self _ _ _
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: AndWrapper
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder

def prepared (s : State) (a b t : Wire) : State :=
 ⟨s.phase,writeBit s.basis t (s.basis a && s.basis b)⟩
def andWrap (a b t : Wire) (P : Program) : Program :=
 [.CCX a b t]++P++[.measureX t [] [.CZ a b]]

theorem andWrap_erased (target : Nat→Wire) (n : Nat) (a b t : Wire) (P : Program)
 (ha : a≠t) (hb : b≠t)
 (aa : ∀i,i<n → a≠target i) (ba : ∀i,i<n → b≠target i) (ta : ∀i,i<n → t≠target i)
 (s : State) (clean : s.basis t=false) (m : List Bool)
 (body : ErasedRange target n (prepared s a b t) (run P m (prepared s a b t))) :
 ErasedRange target n s (run (andWrap a b t P) m s) := by
 let u:=prepared s a b t
 let v:=run P m u
 have av : v.basis a=s.basis a :=
  (body.outside a aa).trans (Function.update_of_ne ha _ _)
 have bv : v.basis b=s.basis b :=
  (body.outside b ba).trans (Function.update_of_ne hb _ _)
 have tv : v.basis t=(s.basis a && s.basis b) :=
  (body.outside t ta).trans (Function.update_self _ _ _)
 have known : v.basis t=(v.basis a && v.basis b) := by rw [av,bv];exact tv
 have er : run [.measureX t [] [.CZ a b]] (m.drop (measurementCount P)) v=
   ⟨v.phase,writeBit v.basis t false⟩ := by
  simp only [run]
  exact DHGadget.measure_erase t a b _ v ha hb known
 have cc : ∀mm : List Bool,run [.CCX a b t] mm s=u := by intro mm;simp [run,u,prepared,clean]
 have parts : run (andWrap a b t P) m s=⟨v.phase,writeBit v.basis t false⟩ := by
  simp only [andWrap,run_append,run_take,measurementCount_append,measurementCount,List.drop_zero,Nat.zero_add]
  rw [cc]
  exact er
 rw [parts]
 refine ⟨body.phase,?_,?_⟩
 · intro q hq
   by_cases qt:q=t
   · subst q
     simp [writeBit,clean]
   · exact (Function.update_of_ne qt _ _).trans
       ((body.outside q hq).trans (Function.update_of_ne qt _ _))
 · intro i hi
   exact (Function.update_of_ne (Ne.symm (ta i hi)) _ _).trans (body.cleared i hi)
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: DirectDecoderProgram2
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCells5 DecoderMeasuredTail DecoderBiasReuse

def correctionsFor (ws : List Wire) (p : Polynomial) : List Correction := p.filterMap fun term=>
 match term with
 | [i]=>some (.Z (ws.getD i 0))
 | [i,j]=>some (.CZ (ws.getD i 0) (ws.getD j 0))
 | _=>none

def lowWires (L : DecoderLayout) : List Wire := [L.bias]++
 (List.range 13).map L.Y++[L.sigma,L.h,L.Y 255,L.A 0,L.A 1,L.A 2]++(List.range 13).map L.R




def lowCorrections (L : DecoderLayout) (j : Nat) : List Correction :=
 correctionsFor (lowWires L) (lowPolys.getD j [])





def highWires (L : DecoderLayout) : List Wire :=
 [L.bias,L.Y 32,L.Y 33,L.Y 34,L.Y 35,L.Y 31,L.Y 30,L.Y 29,
 L.R 31,L.R 30,L.bias,L.sigma,L.h,L.bias,L.A 0]++(List.range' 32 4).map L.R
def highPhysical (L : DecoderLayout) (b : BasisState) : List Bool :=
 [true,b (L.Y 32),b (L.Y 33),b (L.Y 34),b (L.Y 35),b (L.Y 31),b (L.Y 30),b (L.Y 29),
 b (L.R 31),b (L.R 30),false,b L.sigma,b L.h,false,b (L.A 0)]++
 (List.range' 32 4).map (fun j=>b (L.R j))
def highCorrections (L : DecoderLayout) (j : Nat) : List Correction :=
 correctionsFor (highWires L) (highPolys.getD j [])

theorem high_correction_value (L : DecoderLayout) (b : BasisState) (j : Fin 4) :
 phaseValue (highCorrections L j.val) b=evalPoly (highPolys.getD j.val []) (highPhysical L b) := by
 fin_cases j <;> simp [highCorrections,correctionsFor,highWires,highPolys,phaseValue,evalPoly,highPhysical,List.range'_succ]

def upper (L : DecoderLayout) : Program := eraseRange (fun i=>L.R (36+i))
 (fun i=>polyCorrections (L.Y (36+i-3)) (L.Y (36+i-2)) (L.Y (36+i-1))
  (L.Y (36+i)) L.sigma (L.R (36+i-1)) (decide (36+i<255))) 220

def highErase (L : DecoderLayout) : Program := eraseRange (fun i=>L.R (32+i)) (highCorrections L) 4

def middle (L : DecoderLayout) : Program := eraseRange (fun i=>L.R (13+i))
 (fun i=>polyCorrections (L.Y (13+i-3)) (L.Y (13+i-2)) (L.Y (13+i-1))
  (L.Y (13+i)) L.sigma (L.R (13+i-1)) true) 19


def lowErase (L : DecoderLayout) : Program := eraseRange L.R (lowCorrections L) 13


















end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: DirectDecoderMath
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCellCarryMath DecoderCells5 DecoderMeasuredTail CodecBitSliceVerify

theorem chunk_eq_reference : chunk=referenceSteps := by
 funext ys ds p sig a c
 induction ys generalizing ds p a c with
 | nil=>rfl
 | cons y ys ih=>
   cases ds with
   | nil=>rfl
   | cons d ds=>simp only [chunk,referenceSteps];rw [ih]

theorem seedOK_iff (p s a c : Bool) : seedOK p s a c=true ↔ seedValid p s a c := by
 cases p <;> cases s <;> cases a <;> cases c <;> simp [seedOK,seedValid]

def lowRoot (L : DecoderLayout) (b : BasisState) : Nat := packBits
 [b (L.Y 3),b (L.Y 4),b (L.Y 5),b (L.Y 6),b (L.Y 7),b (L.Y 8),b (L.Y 9),
 b (L.Y 10),b (L.Y 11),b (L.Y 12),b L.sigma,b L.h,b (L.A 3),bExpected L b 4]



















theorem cb4 : (4294968273:Nat).testBit 4=true := by decide +kernel
theorem cb5 : (4294968273:Nat).testBit 5=false := by decide +kernel
theorem cb6 : (4294968273:Nat).testBit 6=true := by decide +kernel
theorem cb7 : (4294968273:Nat).testBit 7=true := by decide +kernel
theorem cb8 : (4294968273:Nat).testBit 8=true := by decide +kernel
theorem cb9 : (4294968273:Nat).testBit 9=true := by decide +kernel
theorem cb10 : (4294968273:Nat).testBit 10=false := by decide +kernel
theorem cb11 : (4294968273:Nat).testBit 11=false := by decide +kernel
theorem cb12 : (4294968273:Nat).testBit 12=false := by decide +kernel
theorem cb30 : (4294968273:Nat).testBit 30=false := by decide +kernel
theorem cb31 : (4294968273:Nat).testBit 31=false := by decide +kernel
theorem cb32 : (4294968273:Nat).testBit 32=true := by decide +kernel
theorem cb33 : (4294968273:Nat).testBit 33=false := by decide +kernel
theorem cb34 : (4294968273:Nat).testBit 34=false := by decide +kernel
theorem cb35 : (4294968273:Nat).testBit 35=false := by decide +kernel
theorem lb4 : (977:Nat).testBit 4=true := by decide +kernel
theorem lb5 : (977:Nat).testBit 5=false := by decide +kernel
theorem lb6 : (977:Nat).testBit 6=true := by decide +kernel
theorem lb7 : (977:Nat).testBit 7=true := by decide +kernel
theorem lb8 : (977:Nat).testBit 8=true := by decide +kernel
theorem lb9 : (977:Nat).testBit 9=true := by decide +kernel
theorem lb10 : (977:Nat).testBit 10=false := by decide +kernel
theorem lb11 : (977:Nat).testBit 11=false := by decide +kernel
theorem lb12 : (977:Nat).testBit 12=false := by decide +kernel

theorem lowRoot_results (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j) :
 lowRs (lowRoot L b)=[false,false,false,false]++(List.range' 4 9).map (fun j=>b (L.R j)) := by
 simp only [lowRs,lowRoot,pack_testBit,chunk_eq_reference]
 simpa [List.range_succ,List.range'_succ,correction,MappedBit.value,cb4,cb5,cb6,cb7,cb8,cb9,cb10,cb11,cb12,cb30,cb31,cb32,cb33,cb34,cb35,lb4,lb5,lb6,lb7,lb8,lb9,lb10,lb11,lb12] using
  congrArg (fun xs=>[false,false,false,false]++xs)
   (reference_chunk L b g adds 9 4 (by decide) (by decide))

def lowExpected (L : DecoderLayout) (b : BasisState) : List Bool :=
 [true]++(List.range 13).map (fun j=>b (L.Y j))++[b L.sigma,b L.h,b (L.Y 255)]++
 [b (L.Y 4) && b L.h,b (L.Y 5) && b (L.Y 6),b (L.Y 8) && b L.h]++
 (List.range 13).map (fun j=>b (L.R j))
def lowCanonical (L : DecoderLayout) (b : BasisState) : List Bool :=
 [true,false,false,false]++(List.range' 3 10).map (fun j=>b (L.Y j))++[b L.sigma,b L.h,false]++
 [b (L.Y 4) && b L.h,b (L.Y 5) && b (L.Y 6),b (L.Y 8) && b L.h]++
 [false,false,false,false]++(List.range' 4 9).map (fun j=>b (L.R j))






























def highRoot (L : DecoderLayout) (b : BasisState) : Nat := packBits
 [b (L.Y 29),b (L.Y 30),b (L.Y 31),b (L.Y 32),b (L.Y 33),b (L.Y 34),b (L.Y 35),
 b L.sigma,b L.h,b (L.A 29),bExpected L b 30]
theorem highRoot_bound (L : DecoderLayout) (b : BasisState) : highRoot L b<2048 := by
 have h:=pack_bound [b (L.Y 29),b (L.Y 30),b (L.Y 31),b (L.Y 32),b (L.Y 33),b (L.Y 34),b (L.Y 35),
 b L.sigma,b L.h,b (L.A 29),bExpected L b 30]
 norm_num only [List.length_cons,List.length_nil] at h
 exact h

theorem highRoot_valid (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j)
 (hh : (b L.sigma && b L.h)=false) (hb : (b L.sigma && b L.bias)=false) :
 highValid (highRoot L b)=true := by
 have seed:=seed_graph L b g adds hh hb 29 (by decide) (by decide) (by rfl)
 have nd:=no_double_invariant L b g adds hh hb 29 (by decide)
 simp only [highValid,highRoot,pack_testBit]
 change (!(b L.sigma && b L.h) && seedOK (b (L.Y 29)) (b L.sigma) (b (L.A 29)) (bExpected L b 30) &&
  !(b (L.A 29) && bExpected L b 30 && !b L.h))=true
 simp only [Bool.and_eq_true,Bool.not_eq_true',hh,nd,seedOK_iff]
 exact ⟨⟨trivial,seed⟩,trivial⟩

theorem highRoot_results (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j) :
 highRs (highRoot L b)=(List.range' 30 6).map (fun j=>b (L.R j)) := by
 simp only [highRs,highRoot,pack_testBit,chunk_eq_reference]
 simpa [List.range_succ,List.range'_succ,correction,MappedBit.value,cb4,cb5,cb6,cb7,cb8,cb9,cb10,cb11,cb12,cb30,cb31,cb32,cb33,cb34,cb35,lb4,lb5,lb6,lb7,lb8,lb9,lb10,lb11,lb12] using
  reference_chunk L b g adds 6 30 (by decide) (by decide)

def highExpected (L : DecoderLayout) (b : BasisState) : List Bool :=
 [true,b (L.Y 32),b (L.Y 33),b (L.Y 34),b (L.Y 35),b (L.Y 31),b (L.Y 30),b (L.Y 29),
 b (L.R 31),b (L.R 30),false,b L.sigma,b L.h,false,b (L.Y 32) && b L.h]++
 (List.range' 32 4).map (fun j=>b (L.R j))

theorem highRoot_vars (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j) :
 highVars (highRoot L b)=highExpected L b := by
 unfold highVars
 rw [highRoot_results L b g adds]
 simp only [highRoot,highExpected,List.range'_succ,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
 simp only [pack_testBit]
 simp

theorem high_math (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255 → b (L.A j)=aExpected L b j)
 (hh : (b L.sigma && b L.h)=false) (hb : (b L.sigma && b L.bias)=false) (i : Fin 4) :
 evalPoly (highPolys.getD i.val []) (highExpected L b)=b (L.R (i.val+32)) := by
 have result:=high_local_checked ⟨highRoot L b,highRoot_bound L b⟩ (highRoot_valid L b g adds hh hb) i
 rw [highRoot_vars L b g adds,highRoot_results L b g adds] at result
 rw [result]
 fin_cases i <;> simp [List.range_succ,List.range'_succ]

theorem initialRs_word : ∀x : Fin 512, initialRs x.val=
 [(firstR x.val).testBit 0,(firstR x.val).testBit 1,(firstR x.val).testBit 2,
 (firstR x.val).testBit 3,(firstR x.val).testBit 4,(firstR x.val).testBit 5] := by decide +kernel

theorem initialRs_ref (L : DecoderLayout) (hw : L.Widths) (b : BasisState)
 (bias : b L.bias=(b (L.Y 255) && !b L.sigma))
 (scalar : regValue L.r b=
      ((if b L.sigma then regValue (L.y.take 255) b else 3*regValue (L.y.take 255) b)+
        2*(b L.bias).toNat+(b L.h).toNat*(2^32+977))%2^256) :
 initialRs (firstRoot L b)=(List.range 6).map (fun j=>b (L.R j)) := by
 rw [initialRs_word ⟨firstRoot L b,firstRoot_bound L hw b⟩]
 simp only [firstR_bit L hw b bias scalar 0 (by decide),firstR_bit L hw b bias scalar 1 (by decide),
 firstR_bit L hw b bias scalar 2 (by decide),firstR_bit L hw b bias scalar 3 (by decide),
 firstR_bit L hw b bias scalar 4 (by decide),firstR_bit L hw b bias scalar 5 (by decide)]
 rfl

def initialCanonical (L : DecoderLayout) (b : BasisState) : List Bool :=
 [true]++(List.range 6).map (fun j=>b (L.Y j))++List.replicate 7 false++
 [b L.sigma,b L.h,b (L.Y 255),b (L.Y 4) && b L.h,false,false]++
 (List.range 6).map (fun j=>b (L.R j))

theorem initialRoot_vars (L : DecoderLayout) (hw : L.Widths) (b : BasisState)
 (bias : b L.bias=(b (L.Y 255) && !b L.sigma))
 (scalar : regValue L.r b=
      ((if b L.sigma then regValue (L.y.take 255) b else 3*regValue (L.y.take 255) b)+
        2*(b L.bias).toNat+(b L.h).toNat*(2^32+977))%2^256) :
 initialVars (firstRoot L b)=initialCanonical L b := by
 unfold initialVars
 rw [initialRs_ref L hw b bias scalar]
 simp [initialCanonical,firstRoot_bits L hw b,List.range_succ]

theorem initial_math (L : DecoderLayout) (hw : L.Widths) (b : BasisState)
 (bias : b L.bias=(b (L.Y 255) && !b L.sigma))
 (scalar : regValue L.r b=
      ((if b L.sigma then regValue (L.y.take 255) b else 3*regValue (L.y.take 255) b)+
        2*(b L.bias).toNat+(b L.h).toNat*(2^32+977))%2^256)
 (hh : (b L.sigma && b L.h)=false) (i : Fin 6) :
 evalPoly (lowPolys.getD i.val []) (lowExpected L b)=b (L.R i.val) := by
 have valid : ((firstRoot L b).testBit 6 && (firstRoot L b).testBit 7)=false := by
   simpa [firstRoot_bits L hw b] using hh
 have result:=initial_local_checked ⟨firstRoot L b,firstRoot_bound L hw b⟩ valid i
 rw [initialRoot_vars L hw b bias scalar,initialRs_ref L hw b bias scalar] at result
 have pe : evalPoly (lowPolys.getD i.val []) (lowExpected L b)=
   evalPoly (lowPolys.getD i.val []) (initialCanonical L b) := by
   fin_cases i <;> simp [lowPolys,evalPoly,lowExpected,lowCanonical,initialCanonical,List.range_succ,List.range'_succ]
 rw [pe,result]
 fin_cases i <;> simp [List.range_succ,List.range'_succ]
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: DirectDecoderTriangularFacts
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCells5 DecoderMeasuredTail DecoderBiasReuse



theorem high_away : ∀i : Fin 4,fixedLayout.R (32+i.val)∉correctionWires (highCorrections fixedLayout i.val) := by decide +kernel
theorem high_tri : ∀i j : Fin 4,i.val<j.val → fixedLayout.R (32+j.val)∉correctionWires (highCorrections fixedLayout i.val) := by decide +kernel

theorem result_inj (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<256) (eq : L.R i=L.R j) : i=j :=
 getD_inj L.r (register_nodup L hn).2.1 i j (by rw [hw.2.1];exact hi) (by rw [hw.2.1];exact hj) eq

theorem poly_r_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (lo : 3 ≤ i) (hi : i<256) (hj : j<256) (ne : j≠i-1) (enabled : Bool) :
 L.R j∉correctionWires (polyCorrections (L.Y (i-3)) (L.Y (i-2)) (L.Y (i-1))
  (L.Y i) L.sigma (L.R (i-1)) enabled) := by
 have p: L.R j≠L.Y (i-3):=(y_ne_r L hw hn _ _ (by omega) hj).symm
 have x: L.R j≠L.Y (i-2):=(y_ne_r L hw hn _ _ (by omega) hj).symm
 have y: L.R j≠L.Y (i-1):=(y_ne_r L hw hn _ _ (by omega) hj).symm
 have z: L.R j≠L.Y i:=(y_ne_r L hw hn _ _ hi hj).symm
 have sig: L.R j≠L.sigma:=(flag_ne_r L hw hn _ (by tauto) j hj).symm
 have r: L.R j≠L.R (i-1):=r_ne_r L hw hn _ _ hj (by omega) ne
 cases enabled <;> simp [polyCorrections,correctionWires,p,x,y,z,sig,r]

theorem poly_correction_value (p x y z sig r : Wire) (enabled : Bool) (b : BasisState) :
 phaseValue (polyCorrections p x y z sig r enabled) b=
 poly (b p) (b x) (b y) (if enabled then b z else false) (b sig) (b r) := by
 cases enabled <;> simp [polyCorrections,phaseValue,poly,Bool.xor_assoc]
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: DirectDecoderStages
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCells5 DecoderMeasuredTail DecoderBiasReuse

structure SourceData (L : DecoderLayout) (ref : BasisState) (s : State) : Prop where
 source : ∀j,j<256 → s.basis (L.Y j)=ref (L.Y j)
 sigma : s.basis L.sigma=ref L.sigma
 h : s.basis L.h=ref L.h

def Pending (L : DecoderLayout) (ref : BasisState) (n : Nat) (s : State) : Prop :=
 ∀j,j<n → s.basis (L.R j)=ref (L.R j)


































theorem highPhysical_eq (L : DecoderLayout) (ref : BasisState) (s : State)
 (src : SourceData L ref s) (rs : Pending L ref 36 s)
 (a0 : s.basis (L.A 0)=(ref (L.Y 32) && ref L.h)) :
 highPhysical L s.basis=highExpected L ref := by
 have rr : (List.range' 32 4).map (fun j=>s.basis (L.R j))=(List.range' 32 4).map (fun j=>ref (L.R j)) := by
   apply List.map_congr_left
   intro j hj
   exact rs j (by have z:=List.mem_range'.mp hj;omega)
 unfold highPhysical highExpected
 rw [rr,src.source 32 (by decide),src.source 33 (by decide),src.source 34 (by decide),
   src.source 35 (by decide),src.source 31 (by decide),src.source 30 (by decide),src.source 29 (by decide),
   rs 31 (by decide),rs 30 (by decide),src.sigma,src.h,a0]

theorem high_known (L : DecoderLayout) (ref : BasisState) (r : Reference L ref)
 (s : State) (src : SourceData L ref s) (rs : Pending L ref 36 s)
 (a0 : s.basis (L.A 0)=(ref (L.Y 32) && ref L.h)) (j : Fin 4) :
 s.basis (L.R (32+j.val))=phaseValue (highCorrections L j.val) s.basis := by
 rw [rs (32+j.val) (by have h:=j.isLt;omega),high_correction_value L s.basis j,
  highPhysical_eq L ref s src rs a0]
 symm
 simpa only [Nat.add_comm] using high_math L ref r.graph r.adds r.exclusive r.exclusiveBias j














theorem high_correct (ref : BasisState) (r : Reference fixedLayout ref)
 (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 36 s)
 (a0 : s.basis (fixedLayout.A 0)=(ref (fixedLayout.Y 32) && ref fixedLayout.h)) (m : List Bool) :
 ErasedRange (fun i=>fixedLayout.R (32+i)) 4 s (run (highErase fixedLayout) m s) := by
 apply eraseRange_correct
 · intro i hi j hj eq
   have z:=result_inj _ fixed_widths fixed_nodup (32+i) (32+j) (by omega) (by omega) eq
   omega
 · intro i hi;exact high_away ⟨i,hi⟩
 · intro i hi j hij hj;exact high_tri ⟨i,hi⟩ ⟨j,hj⟩ hij
 · intro i hi;exact high_known _ ref r s src rs a0 ⟨i,hi⟩

theorem upper_known (L : DecoderLayout) (ref : BasisState) (r : Reference L ref)
 (s : State) (src : SourceData L ref s) (rs : Pending L ref 256 s) (i : Nat) (hi : i<220) :
 s.basis (L.R (36+i))=phaseValue
 (polyCorrections (L.Y (36+i-3)) (L.Y (36+i-2)) (L.Y (36+i-1))
  (L.Y (36+i)) L.sigma (L.R (36+i-1)) (decide (36+i<255))) s.basis := by
 rw [rs _ (by omega),poly_correction_value,
  src.source (36+i-3) (by omega),src.source (36+i-2) (by omega),
  src.source (36+i-1) (by omega),src.source (36+i) (by omega),src.sigma,rs _ (by omega)]
 have h:=reference_pair L ref r.graph r.adds r.exclusive r.exclusiveBias (34+i) (by omega) (by omega)
 have a:34+i+2=36+i:=by omega
 have b:34+i-1=36+i-3:=by omega
 have c:34+i=36+i-2:=by omega
 have d:34+i+1=36+i-1:=by omega
 rw [a,b,d,c] at h
 simpa only [sourceAt,decide_eq_true_eq] using h

theorem middle_known (L : DecoderLayout) (ref : BasisState) (r : Reference L ref)
 (s : State) (src : SourceData L ref s) (rs : Pending L ref 32 s) (i : Nat) (hi : i<19) :
 s.basis (L.R (13+i))=phaseValue
 (polyCorrections (L.Y (13+i-3)) (L.Y (13+i-2)) (L.Y (13+i-1))
  (L.Y (13+i)) L.sigma (L.R (13+i-1)) true) s.basis := by
 rw [rs _ (by omega),poly_correction_value,
  src.source (13+i-3) (by omega),src.source (13+i-2) (by omega),
  src.source (13+i-1) (by omega),src.source (13+i) (by omega),src.sigma,rs _ (by omega)]
 exact reference_zero_pair L ref r.graph r.adds r.exclusive r.exclusiveBias (13+i) (by omega) (by omega)
  (fun k lo hi=>region_correction_value L ref k (Or.inl ⟨by omega,by omega⟩))

theorem upper_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (ref : BasisState) (r : Reference L ref) (s : State) (src : SourceData L ref s)
 (rs : Pending L ref 256 s) (m : List Bool) :
 ErasedRange (fun i=>L.R (36+i)) 220 s (run (upper L) m s) := by
 apply eraseRange_correct
 · intro i hi j hj eq
   have z:=result_inj L hw hn (36+i) (36+j) (by omega) (by omega) eq
   omega
 · intro i hi
   exact poly_r_away L hw hn (36+i) (36+i) (by omega) (by omega) (by omega) (by omega) _
 · intro i hi j hij hj
   exact poly_r_away L hw hn (36+i) (36+j) (by omega) (by omega) (by omega) (by omega) _
 · intro i hi
   exact upper_known L ref r s src rs i hi

theorem middle_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (ref : BasisState) (r : Reference L ref) (s : State) (src : SourceData L ref s)
 (rs : Pending L ref 32 s) (m : List Bool) :
 ErasedRange (fun i=>L.R (13+i)) 19 s (run (middle L) m s) := by
 apply eraseRange_correct
 · intro i hi j hj eq
   have z:=result_inj L hw hn (13+i) (13+j) (by omega) (by omega) eq
   omega
 · intro i hi
   exact poly_r_away L hw hn (13+i) (13+i) (by omega) (by omega) (by omega) (by omega) _
 · intro i hi j hij hj
   exact poly_r_away L hw hn (13+i) (13+j) (by omega) (by omega) (by omega) (by omega) _
 · intro i hi
   exact middle_known L ref r s src rs i hi
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: ErasedFrames
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCells5 DecoderMeasuredTail DecoderBiasReuse

theorem range_source (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (off n : Nat) (bound : off+n≤256) (ref : BasisState) (s t : State)
 (e : ErasedRange (fun i=>L.R (off+i)) n s t) (src : SourceData L ref s) : SourceData L ref t := by
 refine ⟨?_,?_,?_⟩
 · intro j hj
   exact (e.outside (L.Y j) (fun i hi=>y_ne_r L hw hn j (off+i) hj (by omega))).trans (src.source j hj)
 · exact (e.outside L.sigma (fun i hi=>flag_ne_r L hw hn L.sigma (by tauto) (off+i) (by omega))).trans src.sigma
 · exact (e.outside L.h (fun i hi=>flag_ne_r L hw hn L.h (by tauto) (off+i) (by omega))).trans src.h

theorem range_pending (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (off n : Nat) (bound : off+n≤256) (ref : BasisState) (s t : State)
 (e : ErasedRange (fun i=>L.R (off+i)) n s t) (rs : Pending L ref off s) : Pending L ref off t := by
 intro j hj
 exact (e.outside (L.R j) (fun i hi=>r_ne_r L hw hn j (off+i) (by omega) (by omega) (by omega))).trans (rs j hj)

theorem range_carry (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (off n : Nat) (bound : off+n≤256) (s t : State)
 (e : ErasedRange (fun i=>L.R (off+i)) n s t) (k : Nat) (hk : k<255) : t.basis (L.A k)=s.basis (L.A k) :=
 e.outside (L.A k) (fun i hi=>(r_ne_a L hw hn (off+i) k (by omega) hk).symm)

theorem range_above (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (off n : Nat) (bound : off+n≤256) (s t : State)
 (e : ErasedRange (fun i=>L.R (off+i)) n s t) (j : Nat) (lo : off+n≤j) (hi : j<256) :
 t.basis (L.R j)=s.basis (L.R j) :=
 e.outside (L.R j) (fun i ih=>r_ne_r L hw hn j (off+i) hi (by omega) (by omega))

theorem range_outside (L : DecoderLayout) (hw : L.Widths)
 (off n : Nat) (bound : off+n≤256) (s t : State)
 (e : ErasedRange (fun i=>L.R (off+i)) n s t) (q : Wire) (hr : q∉L.r) : t.basis q=s.basis q := by
 apply e.outside
 intro i hi eq
 exact hr (eq.symm ▸ r_mem L hw (off+i) (by omega))
end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: DirectDecoderBlocks
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCells5 DecoderMeasuredTail DecoderBiasReuse

def highBlock (L : DecoderLayout) : Program := andWrap (L.Y 32) L.h (L.A 0) (highErase L)
def lowBlock (L : DecoderLayout) : Program := andWrap (L.Y 4) L.h (L.A 0)
 (andWrap (L.Y 5) (L.Y 6) (L.A 1) (andWrap (L.Y 8) L.h (L.A 2) (lowErase L)))
def directGraph3 (L : DecoderLayout) : Program := upper L++(highBlock L++(middle L++lowBlock L))

theorem prepared_source (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (ref : BasisState) (s : State) (src : SourceData L ref s) (a b : Wire) (k : Nat) (hk : k<255) :
 SourceData L ref (prepared s a b (L.A k)) := by
 refine ⟨?_,?_,?_⟩
 · intro j hj
   exact (Function.update_of_ne (y_ne_a L hw hn j k hj hk) _ _).trans (src.source j hj)
 · exact (Function.update_of_ne (sigma_ne_a L hw hn k hk) _ _).trans src.sigma
 · exact (Function.update_of_ne (h_ne_a L hw hn k hk) _ _).trans src.h

theorem prepared_pending (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (ref : BasisState) (s : State) (n : Nat) (hnn : n≤256) (rs : Pending L ref n s)
 (a b : Wire) (k : Nat) (hk : k<255) : Pending L ref n (prepared s a b (L.A k)) := by
 intro j hj
 exact (Function.update_of_ne (r_ne_a L hw hn j k (by omega) hk) _ _).trans (rs j hj)

theorem highBlock_correct (ref : BasisState) (r : Reference fixedLayout ref)
 (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 36 s)
 (clean : s.basis (fixedLayout.A 0)=false) (m : List Bool) :
 ErasedRange (fun i=>fixedLayout.R (32+i)) 4 s (run (highBlock fixedLayout) m s) := by
 let L:=fixedLayout
 let u:=prepared s (L.Y 32) L.h (L.A 0)
 have us : SourceData L ref u:=prepared_source L fixed_widths fixed_nodup ref s src _ _ 0 (by decide)
 have ur : Pending L ref 36 u:=prepared_pending L fixed_widths fixed_nodup ref s 36 (by decide) rs _ _ 0 (by decide)
 have ua : u.basis (L.A 0)=(ref (L.Y 32) && ref L.h) := by
   change writeBit s.basis (L.A 0) (s.basis (L.Y 32) && s.basis L.h) (L.A 0)=_
   simp only [writeBit]
   rw [Function.update_self,src.source 32 (by decide),src.h]
 apply andWrap_erased
 · exact y_ne_a L fixed_widths fixed_nodup 32 0 (by decide) (by decide)
 · exact h_ne_a L fixed_widths fixed_nodup 0 (by decide)
 · intro i hi;exact y_ne_r L fixed_widths fixed_nodup 32 (32+i) (by decide) (by omega)
 · intro i hi;exact flag_ne_r L fixed_widths fixed_nodup L.h (by tauto) (32+i) (by omega)
 · intro i hi;exact (r_ne_a L fixed_widths fixed_nodup (32+i) 0 (by omega) (by decide)).symm
 · exact clean
 · exact high_correct ref r u us ur ua m







































































end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: DirectGraphCorrect
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCells5 DecoderMeasuredTail DecoderBiasReuse
attribute [local irreducible] run







































































end ECDSAAdd.Entrant.DirectDecoder


-- Proof component: DirectDecoderFinal
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Secp256k1 BalancedField Challenge Baselines
attribute [local irreducible] run

def cellDecoder : Program := frontFast fixedLayout++directGraph3 fixedLayout++
 clearQuotient fixedLayout++restoreSource fixedLayout++copySource fixedLayout













































































































































































end ECDSAAdd.Entrant.DirectDecoder
