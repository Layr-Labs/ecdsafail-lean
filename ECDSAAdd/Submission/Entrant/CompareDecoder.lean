import ECDSAAdd.Submission.Entrant.ExitMerge
import Mathlib.Data.Nat.Bitwise

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph

abbrev Polynomial := List (List Nat)

def evalPoly (p : Polynomial) (v : List Bool) : Bool :=
 p.foldr (fun t z => (t.foldr (fun i z => v.getD i false && z) true) ^^ z) false

def chunk : List Bool → List Bool → Bool → Bool → Bool → Bool → List Bool
 | [],_,_,_,_,_=>[]
 | y::ys,d::ds,prev,sigma,a,c=>
   let raw:=prev ^^ y ^^ sigma ^^ a
   (raw ^^ d ^^ c)::chunk ys ds y sigma (carryBit prev (y ^^ sigma) a) (carryBit d raw c)
 | _::_,[],_,_,_,_=>[]

def seedOK (p s a c : Bool) : Bool :=
 (!s || ((a == !p) && !c)) && !(c && a && !p)

def lowPolys : List Polynomial := [[[1], [15]], [[1], [2], [16], [1, 14], [1, 15], [14, 16]], [[1], [2], [3], [21], [1, 14], [2, 14], [2, 16], [2, 21], [16, 21]], [[2], [3], [4], [22], [1, 3], [1, 22], [2, 14], [3, 14], [3, 22]], [[3], [4], [5], [15], [23], [2, 4], [2, 23], [3, 14], [4, 14], [4, 23]], [[4], [5], [6], [17], [24], [3, 5], [3, 15], [3, 24], [4, 14], [5, 14], [5, 24], [15, 24]], [[5], [6], [7], [15], [25], [4, 6], [4, 15], [4, 17], [4, 25], [5, 14], [6, 14], [6, 15], [6, 17], [6, 25], [15, 25], [17, 25]], [[6], [8], [18], [6, 14], [6, 15], [6, 17], [6, 26], [7, 14], [7, 15], [7, 17], [7, 26], [15, 26], [17, 26]], [[7], [8], [9], [27], [6, 8], [6, 27], [7, 14], [8, 14], [8, 18], [8, 27], [18, 27]], [[8], [9], [10], [28], [7, 9], [7, 28], [8, 14], [9, 14], [9, 28]], [[9], [10], [11], [15], [29], [8, 10], [8, 29], [9, 14], [10, 14], [10, 29]], [[10], [11], [12], [19], [30], [9, 11], [9, 30], [10, 14], [11, 14], [11, 15], [11, 30], [15, 30]], [[11], [12], [13], [31], [10, 12], [10, 19], [10, 31], [11, 14], [12, 14], [12, 19], [12, 31], [19, 31]]]

def highPolys : List Polynomial := [[[1], [5], [6], [8], [12], [5, 7], [5, 8], [5, 11], [6, 11], [7, 8]], [[1], [2], [5], [14], [15], [1, 6], [1, 11], [1, 15], [5, 11], [6, 12], [6, 15], [12, 15]], [[1], [2], [3], [16], [1, 11], [2, 5], [2, 11], [2, 12], [2, 14], [2, 16], [5, 12], [5, 14], [5, 16], [12, 16], [14, 16]], [[2], [4], [14], [2, 3], [2, 11], [2, 14], [2, 17], [3, 11], [3, 14], [3, 17], [14, 17]]]

def lowYs (x : Nat) : List Bool := [false,false,false]++(List.range 10).map x.testBit

def lowRs (x : Nat) : List Bool := [false,false,false,false]++
 chunk ((List.range 9).map (fun j=>x.testBit (j+1)))
   ((List.range 9).map (fun j=>x.testBit 11 && (977:Nat).testBit (j+4)))
   (x.testBit 0) (x.testBit 10) (x.testBit 12) (x.testBit 13)

def lowVars (x : Nat) : List Bool := [true]++lowYs x++[x.testBit 10,x.testBit 11,false]++
 [x.testBit 1 && x.testBit 11,x.testBit 2 && x.testBit 3,x.testBit 5 && x.testBit 11]++lowRs x

def lowValid (x : Nat) : Bool :=
 !(x.testBit 10 && x.testBit 11) && seedOK (x.testBit 0) (x.testBit 10) (x.testBit 12) (x.testBit 13) &&
 !(x.testBit 12 && x.testBit 13 && !(x.testBit 11))

def highRs (x : Nat) : List Bool := chunk ((List.range 6).map (fun j=>x.testBit (j+1)))
 [false,false,x.testBit 8,false,false,false] (x.testBit 0) (x.testBit 7) (x.testBit 9) (x.testBit 10)

def highVars (x : Nat) : List Bool :=
 [true,x.testBit 3,x.testBit 4,x.testBit 5,x.testBit 6,x.testBit 2,x.testBit 1,x.testBit 0,
 (highRs x).getD 1 false,(highRs x).getD 0 false,false,x.testBit 7,x.testBit 8,false,
 x.testBit 3 && x.testBit 8]++(highRs x).drop 2

def highValid (x : Nat) : Bool :=
 !(x.testBit 7 && x.testBit 8) && seedOK (x.testBit 0) (x.testBit 7) (x.testBit 9) (x.testBit 10) &&
 !(x.testBit 9 && x.testBit 10 && !(x.testBit 8))

def initialRs (x : Nat) : List Bool := chunk ((List.range 6).map x.testBit)
 [x.testBit 7,x.testBit 8 && !(x.testBit 6),false,false,x.testBit 7,false]
 false (x.testBit 6) (x.testBit 6) false

def initialVars (x : Nat) : List Bool := [true]++((List.range 13).map (fun j=>if j<6 then x.testBit j else false))++
 [x.testBit 6,x.testBit 7,x.testBit 8,x.testBit 4 && x.testBit 7,false,false]++initialRs x

end ECDSAAdd.Entrant.DirectDecoder

end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph

theorem high_local_checked : ∀x : Fin 2048,highValid x.val=true → ∀i : Fin 4,
 evalPoly (highPolys.getD i.val []) (highVars x.val)=(highRs x.val).getD (i.val+2) false := by decide +kernel

end ECDSAAdd.Entrant.DirectDecoder

end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph

theorem initial_local_checked : ∀x : Fin 512,(x.val.testBit 6 && x.val.testBit 7)=false → ∀i : Fin 6,
 evalPoly (lowPolys.getD i.val []) (initialVars x.val)=(initialRs x.val).getD i.val false := by decide +kernel

end ECDSAAdd.Entrant.DirectDecoder

end

section

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

end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder
def comparePolys : List Polynomial := [[[2], [3], [4], [12], [25], [1, 3], [1, 12], [1, 13], [1, 25], [2, 11], [3, 11], [3, 12], [3, 13], [3, 25], [12, 25], [13, 25]], [[3], [5], [3, 4], [3, 11], [3, 12], [3, 13], [3, 26], [4, 11], [4, 12], [4, 13], [4, 26], [12, 26], [13, 26]], [[4], [6], [17], [18], [27], [4, 11], [5, 11], [5, 16], [5, 27], [16, 27], [17, 27]], [[5], [6], [7], [28], [4, 6], [4, 28], [5, 11], [6, 11], [6, 28]], [[6], [7], [8], [12], [29], [5, 7], [5, 29], [6, 11], [7, 11], [7, 29]], [[7], [8], [9], [30], [6, 8], [6, 12], [6, 30], [7, 11], [8, 11], [8, 12], [8, 30], [12, 30]], [[8], [9], [10], [20], [21], [31], [7, 9], [7, 31], [8, 11], [9, 11], [9, 19], [9, 31], [11, 20], [11, 21], [12, 21], [19, 31]]]
def cmpSteps : List Bool → List Bool → Bool → List Bool
 | [],_,_=>[]
 | y::ys,k::ks,t=>let v:=if k then y && t else y || t;v::cmpSteps ys ks v
 | _,[],_=>[]
def seedIndex (x : Nat) : Nat :=
 (x.testBit 0).toNat+2*(x.testBit 10).toNat+4*(x.testBit 11).toNat+
 8*(x.testBit 12).toNat+16*(x.testBit 13).toNat+32*(x.testBit 14).toNat
def valid (x : Nat) : Bool := (2305880426972133179:Nat).testBit (seedIndex x)
def compareVars (x : Nat) : List Bool :=
 [true]++((List.range 10).map x.testBit)++
 [x.testBit 10,x.testBit 11,x.testBit 1 && x.testBit 11]++
 [x.testBit 14]++cmpSteps ((List.range 9).map (fun i=>x.testBit (i+1)))
 [true,false,true,false,true,true,true,true,true] (x.testBit 14)++(lowRs x).drop 4
end ECDSAAdd.Entrant.CompareDecoder

end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CertificateBits
open Arithmetic DirectDecoder

def mask (w : Nat) : Nat := 2^(2^w)-1

def input : Nat → Nat → Nat
 | 0,_=>0
 | w+1,k=>
   if k=w then (2^(2^w)-1) <<< (2^w)
   else if k<w then input w k ||| (input w k <<< (2^w)) else 0

theorem input_bound (w k : Nat) : input w k<2^(2^w) := by
 induction w with
 | zero=>simp [input]
 | succ w ih=>
  simp only [input]
  split
  · have h:(2^(2^w):Nat)-1<2^(2^w):=Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    have sh:=Nat.shiftLeft_lt (m:=2^w) h
    simpa only [Nat.pow_succ,Nat.mul_two] using sh
  · split
    · have left:input w k<2^(2^w+2^w):=
       lt_of_lt_of_le (ih) (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
      have right:=Nat.shiftLeft_lt (m:=2^w) ih
      simpa only [Nat.pow_succ,Nat.mul_two] using Nat.or_lt_two_pow left right
    · exact Nat.two_pow_pos _

theorem input_bit (w k r : Nat) (bound : r<2^w) : (input w k).testBit r=r.testBit k := by
 induction w generalizing k r with
 | zero=>
  have eq:r=0:=by simpa using bound
  subst r
  simp [input]
 | succ w ih=>
  have lim:r<2^w+2^w:=by simpa only [Nat.pow_succ,Nat.mul_two] using bound
  simp only [input]
  by_cases top:k=w
  · rw [if_pos top]
    subst k
    by_cases low:r<2^w
    · simp only [Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,
       show ¬r≥2^w by omega,decide_false,Bool.false_and,Nat.testBit_lt_two_pow low]
    · have ge:r≥2^w:=by omega
      have sub:r-2^w<2^w:=by omega
      have bit:r.testBit w=true:=Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt ge bound
      simp only [Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,ge,decide_true,sub,Bool.true_and,bit]
  · rw [if_neg top]
    by_cases small:k<w
    · rw [if_pos small,Nat.testBit_or,Nat.testBit_shiftLeft]
      by_cases low:r<2^w
      · simp only [show ¬r≥2^w by omega,decide_false,Bool.false_and,Bool.or_false]
        exact ih k r low
      · have ge:r≥2^w:=by omega
        have sub:r-2^w<2^w:=by omega
        have off:(input w k).testBit r=false:=Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (input_bound w k) (Nat.pow_le_pow_right (by decide) ge))
        rw [off]
        simp only [ge,decide_true,Bool.true_and,Bool.false_or]
        rw [ih k (r-2^w) sub]
        have eq:r=2^w+(r-2^w):=by omega
        conv_rhs=>rw [eq,Nat.testBit_two_pow_add_gt small]
    · rw [if_neg small]
      have le:w+1≤k:=by omega
      have bit:r.testBit k=false:=Nat.testBit_lt_two_pow
       (lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) le))
      simp only [Nat.zero_testBit,bit]

theorem mask_bit (w r : Nat) (bound : r<2^w) : (mask w).testBit r=true := by
 simp only [mask,Nat.testBit_two_pow_sub_one,bound,decide_true]

def carry (a b c : Nat) : Nat := ((a &&& b) ^^^ (a &&& c)) ^^^ (b &&& c)

theorem carry_bit (a b c r : Nat) : (carry a b c).testBit r=carryBit (a.testBit r) (b.testBit r) (c.testBit r) := by
 simp only [carry,carryBit,Nat.testBit_xor,Nat.testBit_and]

def poly (w : Nat) (p : Polynomial) (cols : List Nat) : Nat :=
 p.foldr (fun term acc=>(term.foldr (fun i v=>(cols.getD i 0) &&& v) (mask w)) ^^^ acc) 0

theorem get_bit (cs : List Nat) (i r : Nat) :
 ((cs.map (fun v=>v.testBit r)).getD i false)=(cs.getD i 0).testBit r := by
 simp only [List.getD,List.getElem?_map]
 cases cs[i]? <;> simp

theorem term_bit (w r : Nat) (bound : r<2^w) (term : List Nat) (cols : List Nat) :
 (term.foldr (fun i v=>(cols.getD i 0) &&& v) (mask w)).testBit r=
 term.foldr (fun i v=>((cols.map (fun n=>n.testBit r)).getD i false) && v) true := by
 induction term with
 | nil=>exact mask_bit w r bound
 | cons i t ih=>simp only [List.foldr_cons,Nat.testBit_and,ih,get_bit]

theorem poly_bit (w r : Nat) (bound : r<2^w) (p : Polynomial) (cols : List Nat) :
 (poly w p cols).testBit r=evalPoly p (cols.map (fun n=>n.testBit r)) := by
 induction p with
 | nil=>simp [poly,evalPoly]
 | cons t p ih=>simp only [poly,List.foldr_cons,Nat.testBit_xor,term_bit w r bound,evalPoly] at *;rw [ih]

end ECDSAAdd.Entrant.CertificateBits
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.CertificateBits
open Arithmetic DirectDecoder CompareDecoder

def chunkCols : List Nat → List Nat → Nat → Nat → Nat → Nat → List Nat
 | [],_,_,_,_,_=>[]
 | y::ys,d::ds,prev,sigma,a,c=>
   let raw:=prev ^^^ y ^^^ sigma ^^^ a
   (raw ^^^ d ^^^ c)::chunkCols ys ds y sigma (carry prev (y ^^^ sigma) a) (carry d raw c)
 | _::_,[],_,_,_,_=>[]

theorem chunkCols_bit (ys ds : List Nat) (p s a c r : Nat) :
 (chunkCols ys ds p s a c).map (fun n=>n.testBit r)=
 chunk (ys.map (fun n=>n.testBit r)) (ds.map (fun n=>n.testBit r))
 (p.testBit r) (s.testBit r) (a.testBit r) (c.testBit r) := by
 induction ys generalizing ds p a c with
 | nil=>simp [chunkCols,chunk]
 | cons y ys ih=>
  cases ds with
  | nil=>simp [chunkCols,chunk]
  | cons d ds=>simp only [chunkCols,chunk,List.map_cons,Nat.testBit_xor,carry_bit,ih]

def lowRsCols : List Nat := [0,0,0,0]++chunkCols
 ((List.range 9).map (fun j=>input 15 (j+1)))
 ((List.range 9).map (fun j=>if (977:Nat).testBit (j+4) then input 15 11 else 0))
 (input 15 0) (input 15 10) (input 15 12) (input 15 13)

theorem lowRsCols_bit (r : Nat) (hr:r<32768) : lowRsCols.map (fun n=>n.testBit r)=lowRs r := by
 have h:r<2^15:=hr
 simp only [lowRsCols,lowRs,List.map_append,List.map_cons,List.map_nil,Nat.zero_testBit,
 chunkCols_bit,List.map_map,Function.comp_def,input_bit 15 _ _ h]
 congr 2
 apply List.map_congr_left
 intro j hj
 split <;> simp_all [input_bit 15 _ r hr]

def cmpCols : List Nat → List Bool → Nat → List Nat
 | [],_,_=>[]
 | y::ys,k::ks,t=>let v:=if k then y &&& t else y ||| t;v::cmpCols ys ks v
 | _,[],_=>[]

theorem cmpCols_bit (ys : List Nat) (ks : List Bool) (t r : Nat) :
 (cmpCols ys ks t).map (fun n=>n.testBit r)=cmpSteps (ys.map (fun n=>n.testBit r)) ks (t.testBit r) := by
 induction ys generalizing ks t with
 | nil=>simp [cmpCols,cmpSteps]
 | cons y ys ih=>
  cases ks with
  | nil=>simp [cmpCols,cmpSteps]
  | cons k ks=>cases k <;> simp [cmpCols,cmpSteps,Nat.testBit_and,Nat.testBit_or,ih]

def varsCols : List Nat := [mask 15]++(List.range 10).map (input 15)++
 [input 15 10,input 15 11,input 15 1 &&& input 15 11]++[input 15 14]++
 cmpCols ((List.range 9).map (fun i=>input 15 (i+1)))
 [true,false,true,false,true,true,true,true,true] (input 15 14)++lowRsCols.drop 4

theorem varsCols_bit (r : Nat) (hr:r<32768) : varsCols.map (fun n=>n.testBit r)=compareVars r := by
 have h:r<2^15:=hr
 simp only [varsCols,compareVars,List.map_append,List.map_cons,List.map_nil,
 mask_bit 15 r h,List.map_map,Function.comp_def,input_bit 15 _ _ h,Nat.testBit_and,
 cmpCols_bit,List.map_drop,lowRsCols_bit r hr]

-- Each cube is one of the eighteen reachable seed states.
def states : List Nat := [0,1,3,4,5,8,9,10,12,13,16,17,20,21,35,41,45,61]
def seedVars : List Nat := [0,10,11,12,13,14]
def cube (s : Nat) : Nat := (List.range 6).foldr
 (fun j v=>(if s.testBit j then input 15 (seedVars.getD j 0) else mask 15 ^^^ input 15 (seedVars.getD j 0)) &&& v) (mask 15)
def validCols : Nat := states.foldr (fun s v=>cube s ||| v) 0

def cubeBool (s : Nat) (bs : List Bool) : Bool :=
 (List.range 6).foldr (fun j v=>((bs.getD j false == s.testBit j) && v)) true

theorem cube_bit (s r : Nat) (hr:r<32768) :
 (cube s).testBit r=cubeBool s (seedVars.map r.testBit) := by
 have bit (j : Nat) :
  (if s.testBit j then input 15 (seedVars.getD j 0) else mask 15 ^^^ input 15 (seedVars.getD j 0)).testBit r=
  (r.testBit (seedVars.getD j 0) == s.testBit j) := by
   cases h:s.testBit j <;> simp [h,Nat.testBit_xor,mask_bit 15 r hr,input_bit 15 _ r hr]
 simp only [cube,cubeBool,List.range_succ,List.range_zero,List.foldr_append,List.foldr_cons,List.foldr_nil,
 Nat.testBit_and,bit,mask_bit 15 r hr]
 simp [seedVars]

theorem validBool (p s h a c t : Bool) :
 (2305880426972133179:Nat).testBit
 (p.toNat+2*s.toNat+4*h.toNat+8*a.toNat+16*c.toNat+32*t.toNat)=
 states.foldr (fun n v=>cubeBool n [p,s,h,a,c,t] || v) false := by
 cases p <;> cases s <;> cases h <;> cases a <;> cases c <;> cases t <;> decide +kernel

theorem validCols_bit (r : Nat) (hr:r<32768) : (validCols).testBit r=valid r := by
 rw [valid,seedIndex,validBool]
 unfold validCols
 generalize states=ss
 induction ss with
 | nil=>simp
 | cons n ns ih=>
  simp only [List.foldr_cons,Nat.testBit_or,cube_bit n r hr,ih]
  simp [seedVars]

 theorem columns_checked (i : Fin 7) :
 validCols &&& poly 15 (comparePolys.getD i.val []) varsCols=
 validCols &&& lowRsCols.getD (i.val+6) 0 := by
  revert i
  decide +kernel

 theorem low_checked (x : Nat) (bound : x<32768) (hv:valid x=true) (i : Fin 7) :
 evalPoly (comparePolys.getD i.val []) (compareVars x)=(lowRs x).getD (i.val+6) false := by
 have h:=congrArg (fun n:Nat=>n.testBit x) (columns_checked i)
 simp only [Nat.testBit_and,validCols_bit x bound,hv,Bool.true_and,
 poly_bit 15 x bound,varsCols_bit x bound] at h
 rw [←get_bit,lowRsCols_bit x bound] at h
 exact h
end ECDSAAdd.Entrant.CertificateBits

end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.CompareDecoder
open DirectDecoder
theorem low_checked (x : Nat) (bound : x<32768) (h : valid x=true) (i : Fin 7) :
 evalPoly (comparePolys.getD i.val []) (compareVars x)=(lowRs x).getD (i.val+6) false :=
 CertificateBits.low_checked x bound h i
#print axioms low_checked
end ECDSAAdd.Entrant.CompareDecoder

end

section
set_option autoImplicit false
/-! Comparator carries supply two previously separate helper products. Full all-record frame proof follows below. -/

-- Proof component: CompareLowSeed
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder

def seedCarry : List Bool → List Bool → Bool → Bool → Bool → Bool → Bool × Bool
 | [],_,_,_,a,c=>(a,c)
 | y::ys,d::ds,prev,sigma,a,c=>
   let raw:=prev ^^ y ^^ sigma ^^ a
   seedCarry ys ds y sigma (carryBit prev (y ^^ sigma) a) (carryBit d raw c)
 | _,[],_,_,a,c=>(a,c)

def prefixState (x : Nat) : Nat :=
 let ys:=(List.range 4).map x.testBit
 let s:=x.testBit 4
 let h:=x.testBit 5
 let sign:=x.testBit 6
 let ac:=seedCarry ys [h,sign && !s,false,false] false s s false
 let cmp:=(cmpSteps ys [true,false,true,true] sign).getD 3 false
 (x.testBit 3).toNat+2*s.toNat+4*h.toNat+8*ac.1.toNat+16*ac.2.toNat+32*cmp.toNat

theorem prefix_seed_checked : ∀x : Fin 128,
 !(x.val.testBit 4 && x.val.testBit 5)=true →
 (2305880426972133179:Nat).testBit (prefixState x.val)=true := by decide +kernel

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareBorrowRun
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph
attribute [local irreducible] run

def borrowBasis : List Wire → List Wire → Wire → Nat → BasisState → BasisState
 | x::xs,c::cs,cin,k,b=>
   borrowBasis xs cs c (k/2)
    (writeBit b c (b c ^^ carryBit (!b x) (decide (k%2=1)) (b cin)))
 | _,_,_,_,b=>b

theorem borrow_run (xs cs : List Wire) (cin : Wire) (k : Nat)
 (hn : (cin::xs++cs).Nodup) (s : State) (m : List Bool) :
 run (borrowPath false xs cs cin k) m s=⟨s.phase,borrowBasis xs cs cin k s.basis⟩ := by
 induction xs generalizing cs cin k s with
 | nil=>simp [borrowPath,borrowBasis,run]
 | cons x xs ih=>
  cases cs with
  | nil=>simp [borrowPath,borrowBasis,run]
  | cons c cs=>
   have cnt:=List.nodup_iff_count.mp hn
   have nd : [x,cin,c].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
   have nd' : (c::xs++cs).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
   have bc:=constantBorrow_counts (decide (k%2=1)) x cin c
   simp only [borrowPath,Bool.false_eq_true,if_false,run_append,bc.2.1,List.take_zero,List.drop_zero]
   rw [constantBorrow_correct _ _ _ _ nd]
   simpa only [borrowBasis] using ih cs c (k/2) nd'
    ⟨s.phase,writeBit s.basis c (s.basis c ^^ carryBit (!s.basis x) (decide (k%2=1)) (s.basis cin))⟩

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareBorrowGraph
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph

theorem borrow_outside (xs cs : List Wire) (cin : Wire) (k : Nat) (b : BasisState)
 (q : Wire) (hq : q∉cs) : borrowBasis xs cs cin k b q=b q := by
 induction xs generalizing cs cin k b with
 | nil=>rfl
 | cons x xs ih=>
  cases cs with
  | nil=>rfl
  | cons c cs=>
   have ne:q≠c:=fun e=>hq (by simp [e])
   have away:q∉cs:=fun h=>hq (by simp [h])
   simp only [borrowBasis]
   rw [ih cs c (k/2) _ away]
   exact Function.update_of_ne ne _ _

def BorrowGraph : List Wire → List Wire → Wire → Nat → BasisState → Prop
 | x::xs,c::cs,cin,k,b=>
   b c=carryBit (!b x) (decide (k%2=1)) (b cin) ∧ BorrowGraph xs cs c (k/2) b
 | _,_,_,_,_=>True

theorem borrow_graph (xs cs : List Wire) (cin : Wire) (k : Nat)
 (hn : (cin::xs++cs).Nodup) (b : BasisState) (zero : ∀q∈cs,b q=false) :
 BorrowGraph xs cs cin k (borrowBasis xs cs cin k b) := by
 induction xs generalizing cs cin k b with
 | nil=>trivial
 | cons x xs ih=>
  cases cs with
  | nil=>trivial
  | cons c cs=>
   have cnt:=List.nodup_iff_count.mp hn
   have nd' : (c::xs++cs).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
   have away : ∀q,q=cin ∨ q=x ∨ q=c → q∉cs := by
    intro q h mem
    have hcnt:=cnt q
    have pos:=List.count_pos_iff.mpr mem
    rcases h with h|h|h <;> subst q <;>
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at hcnt <;> omega
   have xc : x≠c := by
    intro e
    have h:=cnt c
    rw [e] at h
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
    omega
   have ic : cin≠c := by
    intro e
    have h:=cnt c
    rw [e] at h
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
    omega
   let v:=carryBit (!b x) (decide (k%2=1)) (b cin)
   let b1:=writeBit b c (b c ^^ v)
   have clean : ∀q∈cs,b1 q=false := by
    intro q mem
    have ne : q≠c := by intro e;exact away c (by tauto) (e ▸ mem)
    exact (Function.update_of_ne ne _ _).trans (zero q (by simp [mem]))
   have tail:=ih cs c (k/2) nd' b1 clean
   change _ ∧ _
   refine ⟨?_,tail⟩
   change borrowBasis xs cs c (k/2) b1 c =
    carryBit (!(borrowBasis xs cs c (k/2) b1 x)) (decide (k%2=1))
      (borrowBasis xs cs c (k/2) b1 cin)
   rw [borrow_outside _ _ _ _ _ c (away c (by tauto)),
    borrow_outside _ _ _ _ _ x (away x (by tauto)),
    borrow_outside _ _ _ _ _ cin (away cin (by tauto))]
   simp [b1,writeBit,xc,ic,zero c (by simp),v]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareBorrowValues
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph

def borrowValues : List Bool → Bool → Nat → List Bool
 | [],_,_=>[]
 | y::ys,c,k=>
   let v:=carryBit (!y) (decide (k%2=1)) c
   v::borrowValues ys v (k/2)

def literalBits : Nat → Nat → List Bool
 | 0,_=>[]
 | n+1,k=>decide (k%2=1)::literalBits n (k/2)

theorem graph_values (xs cs : List Wire) (cin : Wire) (k : Nat) (b : BasisState)
 (len : cs.length=xs.length) (g : BorrowGraph xs cs cin k b) :
 cs.map b=borrowValues (xs.map b) (b cin) k := by
 induction xs generalizing cs cin k with
 | nil=>have e:cs=[]:=List.eq_nil_of_length_eq_zero (by simpa using len);subst cs;rfl
 | cons x xs ih=>
  cases cs with
  | nil=>simp at len
  | cons c cs=>
   have hlen:cs.length=xs.length:=by simpa using len
   obtain ⟨first,tail⟩:=g
   simp only [List.map_cons,borrowValues]
   rw [←first,ih cs c (k/2) hlen tail]

theorem borrow_ge_step (y bit cin : Bool) :
 (!(carryBit (!y) bit cin))=(if bit then y && !cin else y || !cin) := by
 cases y <;> cases bit <;> cases cin <;> rfl

theorem borrowValues_ge (ys : List Bool) (cin : Bool) (k : Nat) :
 (borrowValues ys cin k).map Bool.not=cmpSteps ys (literalBits ys.length k) (!cin) := by
 induction ys generalizing cin k with
 | nil=>rfl
 | cons y ys ih=>
  simp only [borrowValues,List.map_cons,List.length_cons,literalBits,cmpSteps]
  rw [ih,borrow_ge_step]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: ComparePrefixReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder

theorem seedCarry_reference (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255→b (L.A j)=aExpected L b j) :
 seedCarry [b (L.Y 0),b (L.Y 1),b (L.Y 2),b (L.Y 3)]
 [b L.h,b L.bias,false,false] false (b L.sigma) (b L.sigma) false=
 (aExpected L b 3,bExpected L b 4) := by
 have g1:=g 1 (by decide) (by decide)
 have g2:=g 2 (by decide) (by decide)
 have g3:=g 3 (by decide) (by decide)
 have g4:=g 4 (by decide) (by decide)
 have a0:=adds 0 (by decide)
 have a1:=adds 1 (by decide)
 have a2:=adds 2 (by decide)
 simp [correction,MappedBit.value,rawSources,parity] at g1 g2 g3 g4
 rw [g3,g2,g1,a2,a1,a0] at g4
 rw [g4]
 simp only [seedCarry,aExpected]
 generalize b (L.Y 0)=y0,b (L.Y 1)=y1,b (L.Y 2)=y2,b (L.Y 3)=y3,
  b L.sigma=s,b L.h=h,b L.bias=d
 cases y0 <;> cases y1 <;> cases y2 <;> cases y3 <;> cases s <;> cases h <;> cases d <;> rfl

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareLowMath
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail CodecBitSliceVerify

def comparisonValues (L : DecoderLayout) (b : BasisState) : List Bool :=
 cmpSteps ((List.range 13).map (fun j=>b (L.Y j)))
 [true,false,true,true,true,false,true,false,true,true,true,true,true] (b (L.Y 255))
def comparison (L : DecoderLayout) (b : BasisState) (j : Nat) : Bool :=
 (comparisonValues L b).getD j false

def root (L : DecoderLayout) (b : BasisState) : Nat := packBits
 [b (L.Y 3),b (L.Y 4),b (L.Y 5),b (L.Y 6),b (L.Y 7),b (L.Y 8),b (L.Y 9),
 b (L.Y 10),b (L.Y 11),b (L.Y 12),b L.sigma,b L.h,b (L.A 3),bExpected L b 4,comparison L b 3]
def prefixRoot (L : DecoderLayout) (b : BasisState) : Nat := packBits
 [b (L.Y 0),b (L.Y 1),b (L.Y 2),b (L.Y 3),b L.sigma,b L.h,b (L.Y 255)]

theorem root_bound (L : DecoderLayout) (b : BasisState) : root L b<32768 := by
 have h:=pack_bound [b (L.Y 3),b (L.Y 4),b (L.Y 5),b (L.Y 6),b (L.Y 7),b (L.Y 8),b (L.Y 9),
 b (L.Y 10),b (L.Y 11),b (L.Y 12),b L.sigma,b L.h,b (L.A 3),bExpected L b 4,comparison L b 3]
 norm_num only [List.length_cons,List.length_nil] at h
 exact h

theorem prefix_bound (L : DecoderLayout) (b : BasisState) : prefixRoot L b<128 := by
 have h:=pack_bound [b (L.Y 0),b (L.Y 1),b (L.Y 2),b (L.Y 3),b L.sigma,b L.h,b (L.Y 255)]
 norm_num only [List.length_cons,List.length_nil] at h
 exact h

theorem root_valid (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255→b (L.A j)=aExpected L b j)
 (bias : b L.bias=(b (L.Y 255) && !b L.sigma))
 (hh : (b L.sigma && b L.h)=false) : valid (root L b)=true := by
 have ck:=prefix_seed_checked ⟨prefixRoot L b,prefix_bound L b⟩
 have hc:!((prefixRoot L b).testBit 4 && (prefixRoot L b).testBit 5)=true := by
  simp [prefixRoot,pack_testBit,hh]
 have result:=ck hc
 have eq:prefixState (prefixRoot L b)=seedIndex (root L b) := by
  simp only [prefixState,prefixRoot,seedIndex,root,pack_testBit,List.range_succ,List.map_append,
   List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.getD_cons_zero,List.getD_cons_succ,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,List.range_zero]
  rw [←bias,seedCarry_reference L b g adds,←adds 3 (by decide)]
  rfl
 rw [eq] at result
 exact result

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareLowMath2
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail CodecBitSliceVerify

theorem root_results (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255→b (L.A j)=aExpected L b j) :
 lowRs (root L b)=[false,false,false,false]++(List.range' 4 9).map (fun j=>b (L.R j)) := by
 have e:lowRs (root L b)=lowRs (DirectDecoder.lowRoot L b) := by
  simp only [lowRs,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
   List.nil_append,List.cons_append,List.append_nil]
  simp only [root,DirectDecoder.lowRoot,pack_testBit,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
 rw [e,DirectDecoder.lowRoot_results L b g adds]

def expected (L : DecoderLayout) (b : BasisState) : List Bool :=
 [true]++(List.range' 3 10).map (fun j=>b (L.Y j))++
 [b L.sigma,b L.h,b (L.Y 4) && b L.h]++
 (List.range' 3 10).map (comparison L b)++(List.range' 4 9).map (fun j=>b (L.R j))

theorem root_vars (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255→b (L.A j)=aExpected L b j) :
 compareVars (root L b)=expected L b := by
 unfold compareVars
 rw [root_results L b g adds]
 simp only [expected,List.range_succ,List.range_zero,List.range'_succ,List.map_append,
  List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil]
 simp only [root,pack_testBit,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
 rfl

theorem low_math (L : DecoderLayout) (b : BasisState) (g : BGraph L b)
 (adds : ∀j,j<255→b (L.A j)=aExpected L b j)
 (bias : b L.bias=(b (L.Y 255) && !b L.sigma))
 (hh : (b L.sigma && b L.h)=false) (i : Fin 7) :
 evalPoly (comparePolys.getD i.val []) (expected L b)=b (L.R (i.val+6)) := by
 have ck:=low_checked (root L b) (root_bound L b) (root_valid L b g adds bias hh) i
 rw [root_vars L b g adds,root_results L b g adds] at ck
 rw [ck]
 fin_cases i <;> simp [List.range'_succ]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareDecoderProgram
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

def initialWires (L : DecoderLayout) : List Wire := [L.bias]++
 (List.range 13).map L.Y++[L.sigma,L.h,L.Y 255,L.bias,L.bias,L.bias]++(List.range 13).map L.R

def compareWires (L : DecoderLayout) : List Wire := [L.bias]++
 (List.range' 3 10).map L.Y++[L.sigma,L.h,L.bias]++
 (List.range' 3 10).map L.A++(List.range' 4 9).map L.R

def corrections (L : DecoderLayout) (j : Nat) : List Correction :=
 if j<6 then correctionsFor (initialWires L) (lowPolys.getD j [])
 else correctionsFor (compareWires L) (comparePolys.getD (j-6) [])

def lowErase (L : DecoderLayout) : Program := eraseRange L.R (corrections L) 13
def lowBlock (L : DecoderLayout) : Program := andWrap (L.Y 4) L.h L.bias (lowErase L)
def invertCarry (L : DecoderLayout) : Program := L.carry.map (fun q=>.X q)

def cmpFront (L : DecoderLayout) : Program := [.X (L.Y 255)]++
 borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)++
 [.X (L.Y 255)]++invertCarry L

def cmpBack (L : DecoderLayout) : Program := invertCarry L++
 [.X (L.Y 255),.X L.sigma,.CX L.sigma L.h,
 .measureX L.h [] [.CZ L.sigma (L.carry.getLastD (L.Y 255))]]++
 borrowPath true (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)++
 [.X L.sigma,.X (L.Y 255)]

def cellDecoderNext : Program := frontFast fixedLayout++
 upper fixedLayout++DirectDecoder.highBlock fixedLayout++DirectDecoder.middle fixedLayout++
 cmpFront fixedLayout++lowBlock fixedLayout++cmpBack fixedLayout++
 restoreSource fixedLayout++copySource fixedLayout

theorem counts : toffoliCount cellDecoderNext=257 ∧ measurementCount cellDecoderNext=514 := by decide +kernel

theorem physical : GatePhysical cellDecoderNext :=
 CodecBitSliceVerify.physical_of_check _ (by decide +kernel)

theorem support : wires cellDecoderNext⊆fixedLayout.wires.toFinset :=
 DecoderBiasReuse.supportCheck_sound _ (by decide +kernel)

theorem slots : gateSlots cellDecoderNext≤7594 := by decide +kernel

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareLowErasure
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

def initialPhysical (L : DecoderLayout) (b : BasisState) : List Bool := [true]++
 (List.range 13).map (fun j=>b (L.Y j))++[b L.sigma,b L.h,b (L.Y 255),b L.bias,false,false]++
 (List.range 13).map (fun j=>b (L.R j))
def comparePhysical (L : DecoderLayout) (b : BasisState) : List Bool := [true]++
 (List.range' 3 10).map (fun j=>b (L.Y j))++[b L.sigma,b L.h,b L.bias]++
 (List.range' 3 10).map (fun j=>b (L.A j))++(List.range' 4 9).map (fun j=>b (L.R j))

theorem initial_value (L : DecoderLayout) (b : BasisState) (j : Fin 6) :
 phaseValue (corrections L j.val) b=evalPoly (lowPolys.getD j.val []) (initialPhysical L b) := by
 fin_cases j <;> simp [corrections,correctionsFor,initialWires,initialPhysical,lowPolys,phaseValue,evalPoly,List.range_succ]

theorem compare_value (L : DecoderLayout) (b : BasisState) (j : Fin 7) :
 phaseValue (corrections L (j.val+6)) b=evalPoly (comparePolys.getD j.val []) (comparePhysical L b) := by
 fin_cases j <;> simp [corrections,correctionsFor,compareWires,comparePhysical,comparePolys,phaseValue,evalPoly,List.range'_succ]

theorem initial_physical_eq (L : DecoderLayout) (ref : BasisState) (s : State)
 (src : SourceData L ref s) (rs : Pending L ref 13 s)
 (helper : s.basis L.bias=(ref (L.Y 4) && ref L.h)) (j : Fin 6) :
 evalPoly (lowPolys.getD j.val []) (initialPhysical L s.basis)=
 evalPoly (lowPolys.getD j.val []) (lowExpected L ref) := by
 have ys:(List.range 13).map (fun j=>s.basis (L.Y j))=(List.range 13).map (fun j=>ref (L.Y j)) := by
  apply List.map_congr_left
  intro j hj
  exact src.source j (by have h:=List.mem_range.mp hj;omega)
 have rr:(List.range 13).map (fun j=>s.basis (L.R j))=(List.range 13).map (fun j=>ref (L.R j)) := by
  apply List.map_congr_left
  intro j hj
  exact rs j (List.mem_range.mp hj)
 unfold initialPhysical lowExpected
 rw [ys,rr,src.sigma,src.h,src.source 255 (by decide),helper]
 fin_cases j <;> simp [lowPolys,evalPoly,List.range_succ]

theorem compare_physical_eq (L : DecoderLayout) (ref : BasisState) (s : State)
 (src : SourceData L ref s) (rs : Pending L ref 13 s)
 (helper : s.basis L.bias=(ref (L.Y 4) && ref L.h))
 (cmp : ∀j,3≤j→j<13→s.basis (L.A j)=comparison L ref j) :
 comparePhysical L s.basis=expected L ref := by
 have ys:(List.range' 3 10).map (fun j=>s.basis (L.Y j))=(List.range' 3 10).map (fun j=>ref (L.Y j)) := by
  apply List.map_congr_left
  intro j hj
  have h:=List.mem_range'.mp hj
  exact src.source j (by omega)
 have rr:(List.range' 4 9).map (fun j=>s.basis (L.R j))=(List.range' 4 9).map (fun j=>ref (L.R j)) := by
  apply List.map_congr_left
  intro j hj
  have h:=List.mem_range'.mp hj
  exact rs j (by omega)
 have cc:(List.range' 3 10).map (fun j=>s.basis (L.A j))=(List.range' 3 10).map (comparison L ref) := by
  apply List.map_congr_left
  intro j hj
  rcases List.mem_range'.mp hj with ⟨i,hi,eq⟩
  exact cmp j (by omega) (by omega)
 unfold comparePhysical expected
 rw [ys,rr,cc,src.sigma,src.h,helper]

theorem low_known (L : DecoderLayout) (hw : L.Widths) (ref : BasisState) (r : Reference L ref)
 (s : State) (src : SourceData L ref s) (rs : Pending L ref 13 s)
 (helper : s.basis L.bias=(ref (L.Y 4) && ref L.h))
 (cmp : ∀j,3≤j→j<13→s.basis (L.A j)=comparison L ref j) (j : Fin 13) :
 s.basis (L.R j.val)=phaseValue (corrections L j.val) s.basis := by
 rw [rs j.val j.isLt]
 symm
 by_cases small:j.val<6
 · rw [initial_value L s.basis ⟨j.val,small⟩,initial_physical_eq L ref s src rs helper ⟨j.val,small⟩]
   exact DirectDecoder.initial_math L hw ref r.bias r.scalar r.exclusive ⟨j.val,small⟩
 · have bound:j.val-6<7:=by omega
   have eq:j.val-6+6=j.val:=by omega
   have val:=compare_value L s.basis ⟨j.val-6,bound⟩
   simp only [eq] at val
   rw [val,compare_physical_eq L ref s src rs helper cmp]
   have math:=CompareDecoder.low_math L ref r.graph r.adds r.bias r.exclusive ⟨j.val-6,bound⟩
   simpa only [eq] using math

theorem correction_away : ∀i : Fin 13,fixedLayout.R i.val∉correctionWires (corrections fixedLayout i.val) := by decide +kernel
theorem correction_tri : ∀i j : Fin 13,i.val<j.val→fixedLayout.R j.val∉correctionWires (corrections fixedLayout i.val) := by decide +kernel

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareLowBlock
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

theorem low_correct (ref : BasisState) (r : Reference fixedLayout ref)
 (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 13 s)
 (helper : s.basis fixedLayout.bias=(ref (fixedLayout.Y 4) && ref fixedLayout.h))
 (cmp : ∀j,3≤j→j<13→s.basis (fixedLayout.A j)=comparison fixedLayout ref j) (m : List Bool) :
 ErasedRange fixedLayout.R 13 s (run (lowErase fixedLayout) m s) := by
 apply eraseRange_correct
 · intro i hi j hj eq
   exact result_inj _ fixed_widths fixed_nodup i j (by omega) (by omega) eq
 · intro i hi;exact correction_away ⟨i,hi⟩
 · intro i hi j hij hj;exact correction_tri ⟨i,hi⟩ ⟨j,hj⟩ hij
 · intro i hi;exact low_known _ fixed_widths ref r s src rs helper cmp ⟨i,hi⟩

theorem y_ne_bias : ∀j : Fin 256,fixedLayout.Y j.val≠fixedLayout.bias := by decide +kernel
theorem a_ne_bias : ∀j : Fin 255,fixedLayout.A j.val≠fixedLayout.bias := by decide +kernel

theorem lowBlock_correct (ref : BasisState) (r : Reference fixedLayout ref)
 (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 13 s)
 (cmp : ∀j,3≤j→j<13→s.basis (fixedLayout.A j)=comparison fixedLayout ref j)
 (clean : s.basis fixedLayout.bias=false) (m : List Bool) :
 ErasedRange fixedLayout.R 13 s (run (lowBlock fixedLayout) m s) := by
 let L:=fixedLayout
 let u:=prepared s (L.Y 4) L.h L.bias
 have us : SourceData L ref u := by
  constructor
  · intro j hj
    exact (Function.update_of_ne (y_ne_bias ⟨j,hj⟩) (s.basis (L.Y 4) && s.basis L.h) s.basis).trans (src.source j hj)
  · have ne:L.sigma≠L.bias:=by decide +kernel
    exact (Function.update_of_ne ne (s.basis (L.Y 4) && s.basis L.h) s.basis).trans src.sigma
  · have ne:L.h≠L.bias:=by decide +kernel
    exact (Function.update_of_ne ne (s.basis (L.Y 4) && s.basis L.h) s.basis).trans src.h
 have ur : Pending L ref 13 u := by
  intro j hj
  have ne:L.R j≠L.bias := (flag_ne_r L fixed_widths fixed_nodup L.bias (by tauto) j (by omega)).symm
  exact (Function.update_of_ne ne (s.basis (L.Y 4) && s.basis L.h) s.basis).trans (rs j hj)
 have uc : ∀j,3≤j→j<13→u.basis (L.A j)=comparison L ref j := by
  intro j lo hi
  exact (Function.update_of_ne (a_ne_bias ⟨j,by omega⟩) (s.basis (L.Y 4) && s.basis L.h) s.basis).trans (cmp j lo hi)
 have uh : u.basis L.bias=(ref (L.Y 4) && ref L.h) := by
  change writeBit s.basis L.bias (s.basis (L.Y 4) && s.basis L.h) L.bias=_
  rw [writeBit,Function.update_self,src.source 4 (by decide),src.h]
 apply andWrap_erased
 · exact y_ne_bias ⟨4,by decide⟩
 · decide +kernel
 · intro i hi;exact y_ne_r L fixed_widths fixed_nodup 4 i (by decide) (by omega)
 · intro i hi;exact flag_ne_r L fixed_widths fixed_nodup L.h (by tauto) i (by omega)
 · intro i hi;exact flag_ne_r L fixed_widths fixed_nodup L.bias (by tauto) i (by omega)
 · exact clean
 · exact low_correct ref r u us ur uh uc m

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: ComparePrefixes
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

theorem cmpSteps_take (ys ks : List Bool) (c : Bool) (n : Nat) :
 (cmpSteps ys ks c).take n=cmpSteps (ys.take n) (ks.take n) c := by
 induction n generalizing ys ks c with
 | zero=>rfl
 | succ n ih=>
  cases ys with
  | nil=>rfl
  | cons y ys=>
   cases ks with
   | nil=>rfl
   | cons k ks=>
    simp only [cmpSteps,List.take_succ_cons]
    rw [ih]

theorem literalBits_take (n m k : Nat) (bound : n≤m) :
 (literalBits m k).take n=literalBits n k := by
 induction n generalizing m k with
 | zero=>rfl
 | succ n ih=>
  cases m with
  | zero=>omega
  | succ m=>
   simp only [literalBits,List.take_succ_cons]
   rw [ih m (k/2) (by omega)]

theorem literal13 : literalBits 13 (((ECDSAAdd.p-1)/2)/3)=
 [true,false,true,true,true,false,true,false,true,true,true,true,true] := by decide +kernel

theorem source13 : (fixedLayout.y.take 255).take 13=(List.range 13).map fixedLayout.Y := by decide +kernel

theorem carry13 : fixedLayout.carry.take 13=(List.range 13).map fixedLayout.A := by decide +kernel

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareFrontRun
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge
attribute [local irreducible] run

def cmpBasis (L : DecoderLayout) (b : BasisState) : BasisState :=
 let s:=writeBit b (L.Y 255) (!(b (L.Y 255)))
 let u:=borrowBasis (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3) s
 let v:=writeBit u (L.Y 255) (!(u (L.Y 255)))
 fun q=>if q∈L.carry then !(v q) else v q

theorem front_run (L : DecoderLayout)
 (hn : (L.Y 255::L.y.take 255++L.carry).Nodup) (s : State) (m : List Bool) :
 run (cmpFront L) m s=⟨s.phase,cmpBasis L s.basis⟩ := by
 have nd:L.carry.Nodup:=by
  apply List.nodup_iff_count.mpr
  intro q
  have h:=List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_append] at h
  omega
 have inv:measurementCount (invertCarry L)=0:=(notRegister_counts L.carry).2
 have bor:=borrowPath_zero (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)
 simp only [cmpFront,run_append,run_take,measurementCount_append,bor,
  measurementCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.zero_add,
  List.take_zero,List.drop_zero]
 change run (notRegister L.carry) m
  (run [.X (L.Y 255)] []
   (run (borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)) []
    (run [.X (L.Y 255)] [] s)))=⟨s.phase,cmpBasis L s.basis⟩
 rw [notRegister_correct _ nd]
 simp only [run]
 rw [borrow_run _ _ _ _ hn]
 rfl

end ECDSAAdd.Entrant.CompareDecoder

namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DecoderBiasReuse DecoderCells5
theorem layout_front_nodup (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 (L.Y 255::L.y.take 255++L.carry).Nodup := by
 have full:(L.y++L.carry).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h:=List.nodup_iff_count.mp hn q
  simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega
 have hn:(L.y.take 255++[L.Y 255]++L.carry).Nodup := by
  simpa only [←y_split L hw] using full
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega


end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareFrontBasis
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

theorem cmpBasis_outside (L : DecoderLayout) (b : BasisState)
 (hs : L.Y 255∉L.carry) (q : Wire) (hq : q∉L.carry) : cmpBasis L b q=b q := by
 dsimp only [cmpBasis]
 rw [if_neg hq]
 by_cases eq:q=L.Y 255
 · subst q
   simp only [writeBit,Function.update_self]
   rw [borrow_outside _ _ _ _ _ _ hs]
   simp [Bool.not_not]
 · rw [show (writeBit _ (L.Y 255) _) q=_ from Function.update_of_ne eq _ _]
   rw [borrow_outside _ _ _ _ _ q hq]
   exact Function.update_of_ne eq _ _

theorem cmpBasis_carry (L : DecoderLayout) (b : BasisState)
 (hs : L.Y 255∉L.carry) (q : Wire) (hq : q∈L.carry) :
 cmpBasis L b q=!(borrowBasis (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)
  (writeBit b (L.Y 255) (!(b (L.Y 255)))) q) := by
 have ne:q≠L.Y 255:=by intro eq;exact hs (eq ▸ hq)
 dsimp only [cmpBasis]
 rw [if_pos hq]
 rw [show (writeBit _ (L.Y 255) _) q=_ from Function.update_of_ne ne _ _]

theorem sign_away : fixedLayout.Y 255∉fixedLayout.carry := by decide +kernel
theorem source_away : ∀q∈fixedLayout.y.take 255,q∉fixedLayout.carry ∧ q≠fixedLayout.Y 255 := by decide +kernel

theorem cmpBasis_values (b : BasisState) (clean : ∀q∈fixedLayout.carry,b q=false) :
 fixedLayout.carry.map (cmpBasis fixedLayout b)=
 cmpSteps ((fixedLayout.y.take 255).map b)
 (literalBits 255 (((ECDSAAdd.p-1)/2)/3)) (b (fixedLayout.Y 255)) := by
 let L:=fixedLayout
 let k:=(((ECDSAAdd.p-1)/2)/3)
 let bs:=writeBit b (L.Y 255) (!(b (L.Y 255)))
 let u:=borrowBasis (L.y.take 255) L.carry (L.Y 255) k bs
 have hn:(L.Y 255::L.y.take 255++L.carry).Nodup:=layout_front_nodup L fixed_widths fixed_nodup
 have zero:∀q∈L.carry,bs q=false := by
  intro q hq
  have ne:q≠L.Y 255:=by intro eq;exact sign_away (eq ▸ hq)
  exact (Function.update_of_ne ne _ b).trans (clean q hq)
 have graph:=borrow_graph (L.y.take 255) L.carry (L.Y 255) k hn bs zero
 have lens:L.carry.length=(L.y.take 255).length:=by decide +kernel
 have values:=graph_values (L.y.take 255) L.carry (L.Y 255) k u lens graph
 have mapEq:L.carry.map (cmpBasis L b)=(L.carry.map u).map Bool.not := by
  rw [List.map_map]
  apply List.map_congr_left
  intro q hq
  exact cmpBasis_carry L b sign_away q hq
 have ys:(L.y.take 255).map u=(L.y.take 255).map b := by
  apply List.map_congr_left
  intro q hq
  have away:=source_away q hq
  exact (borrow_outside _ _ _ _ _ q away.1).trans (Function.update_of_ne away.2 _ b)
 have sg:u (L.Y 255)=!(b (L.Y 255)) := by
  change borrowBasis (L.y.take 255) L.carry (L.Y 255) k bs (L.Y 255)=_
  rw [borrow_outside (L.y.take 255) L.carry (L.Y 255) k bs (L.Y 255) sign_away]
  exact Function.update_self _ _ _
 rw [mapEq,values,borrowValues_ge,ys,sg]
 simp only [Bool.not_not]
 rfl

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareFrontPrefix
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

theorem cmpBasis_prefix (b : BasisState) (clean : ∀q∈fixedLayout.carry,b q=false) :
 ((List.range 13).map (fun j=>cmpBasis fixedLayout b (fixedLayout.A j)))=
 comparisonValues fixedLayout b := by
 have all:=congrArg (fun xs:List Bool=>xs.take 13) (cmpBasis_values b clean)
 dsimp only at all
 have len:(fixedLayout.y.take 255).length=255:=by decide +kernel
 rw [←List.map_take,carry13,cmpSteps_take,←List.map_take,source13,literalBits_take 13 255 _ (by decide),literal13] at all
 simpa only [List.map_map,comparisonValues] using all

theorem cmpBasis_comparison (b : BasisState) (clean : ∀q∈fixedLayout.carry,b q=false)
 (j : Fin 13) : cmpBasis fixedLayout b (fixedLayout.A j.val)=comparison fixedLayout b j.val := by
 have eq:=congrArg (fun xs:List Bool=>xs.getD j.val false) (cmpBasis_prefix b clean)
 fin_cases j <;> simpa [List.range_succ,comparison] using eq

theorem comparison_congr (L : DecoderLayout) (a b : BasisState)
 (ys : ∀j,j<256→a (L.Y j)=b (L.Y j)) (i : Nat) : comparison L a i=comparison L b i := by
 have e:(List.range 13).map (fun j=>a (L.Y j))=(List.range 13).map (fun j=>b (L.Y j)) := by
  apply List.map_congr_left
  intro j hj
  exact ys j (by have h:=List.mem_range.mp hj;omega)
 simp only [comparison,comparisonValues,e,ys 255 (by decide)]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareFrontFrame
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge
attribute [local irreducible] cmpBasis comparison

theorem front_nodup : (fixedLayout.Y 255::fixedLayout.y.take 255++fixedLayout.carry).Nodup :=
 layout_front_nodup _ fixed_widths fixed_nodup

theorem front_source (ref : BasisState) (s : State) (src : SourceData fixedLayout ref s) :
 SourceData fixedLayout ref ⟨s.phase,cmpBasis fixedLayout s.basis⟩ := by
 let L:=fixedLayout
 constructor
 · intro j hj
   exact (cmpBasis_outside L s.basis sign_away _
    (carry_source_away L fixed_nodup _ (Or.inl (y_mem L fixed_widths j hj)))).trans (src.source j hj)
 · exact (cmpBasis_outside L s.basis sign_away L.sigma
    (carry_source_away L fixed_nodup L.sigma (by tauto))).trans src.sigma
 · exact (cmpBasis_outside L s.basis sign_away L.h
    (carry_source_away L fixed_nodup L.h (by tauto))).trans src.h

theorem front_pending (ref : BasisState) (s : State) (n : Nat) (bound : n≤256)
 (rs : Pending fixedLayout ref n s) :
 Pending fixedLayout ref n ⟨s.phase,cmpBasis fixedLayout s.basis⟩ := by
 let L:=fixedLayout
 intro j hj
 have free:L.R j∉L.carry := by
  intro hc
  exact source_r_away L fixed_nodup (L.R j) (Or.inr (Or.inl hc)) (r_mem L fixed_widths j (by omega))
 exact (cmpBasis_outside L s.basis sign_away _ free).trans (rs j hj)

theorem front_bias (s : State) : cmpBasis fixedLayout s.basis fixedLayout.bias=s.basis fixedLayout.bias :=
 cmpBasis_outside fixedLayout s.basis sign_away fixedLayout.bias (carry_source_away fixedLayout fixed_nodup fixedLayout.bias (by tauto))

theorem front_cmp (ref : BasisState) (s : State) (src : SourceData fixedLayout ref s)
 (clean : ∀q∈fixedLayout.carry,s.basis q=false) (j : Nat) (_lo : 3≤j) (hi : j<13) :
 cmpBasis fixedLayout s.basis (fixedLayout.A j)=comparison fixedLayout ref j := by
 rw [cmpBasis_comparison s.basis clean ⟨j,hi⟩]
 exact comparison_congr _ _ _ src.source j

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareCommutation
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

theorem run_X_outside (P : Program) (q : Wire) (free : q∉wires P) (s : State) (m : List Bool) :
 run P m (run [.X q] [] s)=run [.X q] [] (run P m s) := by
 change run P m ⟨s.phase,writeBit s.basis q (!(s.basis q))⟩=
  ⟨(run P m s).phase,writeBit (run P m s).basis q (!((run P m s).basis q))⟩
 rw [run_write_outside P q free]
 rw [run_preserves_outside P m s q free]

theorem run_CX_outside (P : Program) (a q : Wire)
 (fa : a∉wires P) (fq : q∉wires P) (s : State) (m : List Bool) :
 run P m (run [.CX a q] [] s)=run [.CX a q] [] (run P m s) := by
 change run P m ⟨s.phase,writeBit s.basis q (s.basis q ^^ s.basis a)⟩=
  ⟨(run P m s).phase,writeBit (run P m s).basis q ((run P m s).basis q ^^ (run P m s).basis a)⟩
 rw [run_write_outside P q fq]
 rw [run_preserves_outside P m s q fq,run_preserves_outside P m s a fa]

theorem run_flagPre_outside (P : Program) (a q : Wire)
 (fa : a∉wires P) (fq : q∉wires P) (s : State) (m : List Bool) :
 run P m (run [.X a,.CX a q] [] s)=run [.X a,.CX a q] [] (run P m s) := by
 change run P m (run [.CX a q] [] (run [.X a] [] s))=
  run [.CX a q] [] (run [.X a] [] (run P m s))
 rw [run_CX_outside P a q fa fq,run_X_outside P a fa]

theorem notRegister_twice (r : List Wire) (nd : r.Nodup) (s : State) (m n : List Bool) :
 run (notRegister r) m (run (notRegister r) n s)=s := by
 rw [notRegister_correct r nd,notRegister_correct r nd]
 apply State.extensionality
 · rfl
 · funext q
   by_cases hq:q∈r <;> simp [hq]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: ComparePair
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

def cmpTail (L : DecoderLayout) : Program :=
 [.measureX L.h [] [.CZ L.sigma (L.carry.getLastD (L.Y 255))]]++
 borrowPath true (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)++[.X L.sigma,.X (L.Y 255)]

theorem pair_shape (L : DecoderLayout) : cmpFront L++cmpBack L=
 [.X (L.Y 255)]++borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)++
 [.X (L.Y 255)]++invertCarry L++invertCarry L++[.X (L.Y 255)]++[.X L.sigma,.CX L.sigma L.h]++cmpTail L := by
 simp [cmpFront,cmpBack,cmpTail,List.append_assoc]

theorem quotient_shape (L : DecoderLayout) : clearQuotient L=
 [.X (L.Y 255)]++[.X L.sigma,.CX L.sigma L.h]++
 borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)++cmpTail L := by
 simp [clearQuotient,eraseSelected,cmpTail,List.append_assoc]

attribute [local irreducible] run cmpTail

theorem pair_run (L : DecoderLayout)
 (nd : L.carry.Nodup)
 (fs : L.sigma∉wires (borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)))
 (fh : L.h∉wires (borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)))
 (s : State) (m : List Bool) : run (cmpFront L++cmpBack L) m s=run (clearQuotient L) m s := by
 have iz : measurementCount (invertCarry L)=0 := (notRegister_counts L.carry).2
 have bz:=borrowPath_zero (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)
 have az : measurementCount [.X (L.Y 255)]=0 :=rfl
 have dz : measurementCount [.X L.sigma,.CX L.sigma L.h]=0 :=rfl
 rw [pair_shape,quotient_shape]
 simp only [run_append,run_take,measurementCount_append,iz,bz,az,dz,Nat.zero_add,List.take_zero,List.drop_zero]
 change run (cmpTail L) m
  (run [.X L.sigma,.CX L.sigma L.h] []
   (run [.X (L.Y 255)] [] (run (notRegister L.carry) [] (run (notRegister L.carry) []
    (run [.X (L.Y 255)] [] (run (borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)) []
     (run [.X (L.Y 255)] [] s)))))))=
  run (cmpTail L) m (run (borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)) []
   (run [.X L.sigma,.CX L.sigma L.h] [] (run [.X (L.Y 255)] [] s)))
 rw [notRegister_twice _ nd]
 have xx (t : State) : run [.X (L.Y 255)] [] (run [.X (L.Y 255)] [] t)=t :=
  notRegister_twice [L.Y 255] (by simp) t [] []
 rw [xx]
 rw [run_flagPre_outside _ L.sigma L.h fs fh]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareMask
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

def maskBasis (qs : List Wire) (b : BasisState) : BasisState :=
 fun q=>if q∈qs then false else b q

theorem erased_eq (target : Nat→Wire) (n : Nat) (s t : State) (er : ErasedRange target n s t) :
 t=⟨s.phase,maskBasis ((List.range n).map target) s.basis⟩ := by
 apply State.extensionality
 · exact er.phase
 · funext q
   by_cases h:q∈(List.range n).map target
   · rcases List.mem_map.mp h with ⟨i,hi,eq⟩
     have b:=er.cleared i (List.mem_range.mp hi)
     rw [eq] at b
     simpa only [maskBasis,if_pos h] using b
   · have same:=er.outside q (by
      intro i hi eq
      exact h (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,eq.symm⟩))
     simpa only [maskBasis,if_neg h] using same

theorem run_mask (P : Program) (qs : List Wire) (free : ∀q∈qs,q∉wires P) (s : State) (m : List Bool) :
 run P m ⟨s.phase,maskBasis qs s.basis⟩=
 ⟨(run P m s).phase,maskBasis qs (run P m s).basis⟩ := by
 let u:State:=⟨s.phase,maskBasis qs s.basis⟩
 have loc:=run_measured_locality P (wires P) (Finset.Subset.refl _) u s m rfl (by
  intro q hq
  have no:q∉qs:=fun mem=>free q mem hq
  change maskBasis qs s.basis q=s.basis q
  simp only [maskBasis,if_neg no])
 apply State.extensionality
 · exact loc.1
 · funext q
   by_cases mem:q∈qs
   · have fq:=free q mem
     rw [run_preserves_outside P m u q fq]
     simp only [u,maskBasis,if_pos mem]
   · by_cases hw:q∈wires P
     · simpa only [maskBasis,if_neg mem] using loc.2 q hw
     · rw [run_preserves_outside P m u q hw]
       simp only [u,maskBasis,if_neg mem,run_preserves_outside P m s q hw]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareSupport
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

def restWires (L : DecoderLayout) : List Wire := [L.sigma,L.h,L.Y 255]++L.y.take 255++L.carry

theorem back_support (L : DecoderLayout) : wires (cmpBack L)⊆(restWires L).toFinset := by
 intro q hq
 simp only [cmpBack,wires_append,Finset.mem_union] at hq
 rcases hq with ((inv|head)|bor)|tail
 · have h:q∈L.carry:=by
    change q∈wires (notRegister L.carry) at inv
    rw [notRegister_wires] at inv
    exact List.mem_toFinset.mp inv
   simp [restWires,h]
 · have last:=List.getLastD_mem_cons (l:=L.carry) (a:=L.Y 255)
   simp only [List.mem_cons] at last
   simp [wires,Instr.wires,correctionWires] at head
   simp only [List.mem_toFinset,restWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
   aesop
 · have mem:=borrowPath_wires true (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3) bor
   simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at mem
   simp only [List.mem_toFinset,restWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
   tauto
 · simp [wires,Instr.wires] at tail
   simp only [List.mem_toFinset,restWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
   aesop

theorem back_away_r (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (q : Wire) (hr : q∈L.r) : q∉wires (cmpBack L) := by
 intro hq
 have mem:=List.mem_toFinset.mp (back_support L hq)
 simp only [restWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mem
 apply source_r_away L hn q _ hr
 rcases mem with ((rfl|rfl|rfl)|hy)|hc
 · tauto
 · tauto
 · exact Or.inl (y_mem L hw 255 (by decide))
 · exact Or.inl (List.mem_of_mem_take hy)
 · exact Or.inr (Or.inl hc)

theorem borrow_flag_free (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (q : Wire) (flag : q=L.sigma ∨ q=L.h) :
 q∉wires (borrowPath false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3)) := by
 intro hq
 have mem:=borrowPath_wires false (L.y.take 255) L.carry (L.Y 255) (((ECDSAAdd.p-1)/2)/3) hq
 simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at mem
 have yf:q∉L.y:=flag_y_away L hn q (by rcases flag with rfl|rfl <;> simp)
 have cf:q∉L.carry:=carry_source_away L hn q (by rcases flag with rfl|rfl <;> tauto)
 rcases mem with eq|hy|hc
 · exact yf (eq ▸ y_mem L hw 255 (by decide))
 · exact yf (List.mem_of_mem_take hy)
 · exact cf hc

theorem carry_nd (L : DecoderLayout) (hn : L.wires.Nodup) : L.carry.Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
 omega

theorem pair_run_fixed (s : State) (m : List Bool) :
 run (cmpFront fixedLayout++cmpBack fixedLayout) m s=run (clearQuotient fixedLayout) m s :=
 pair_run _ (carry_nd _ fixed_nodup)
 (borrow_flag_free _ fixed_widths fixed_nodup _ (by tauto))
 (borrow_flag_free _ fixed_widths fixed_nodup _ (by tauto)) s m

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareSegment
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge
attribute [local irreducible] run cmpBasis comparison

theorem front_measurements (L : DecoderLayout) : measurementCount (cmpFront L)=0 := by
 have inv:measurementCount (invertCarry L)=0:=(notRegister_counts L.carry).2
 simp only [cmpFront,measurementCount_append,borrowPath_zero,inv]
 rfl

theorem low_measurements (L : DecoderLayout) : measurementCount (lowBlock L)=14 := by rfl

def segment (L : DecoderLayout) : Program := cmpFront L++lowBlock L++cmpBack L

theorem segment_correct (ref : BasisState) (r : Reference fixedLayout ref)
 (s : State) (src : SourceData fixedLayout ref s) (rs : Pending fixedLayout ref 13 s)
 (clean : ∀q∈fixedLayout.carry,s.basis q=false) (bias : s.basis fixedLayout.bias=false)
 (quotient : s.basis fixedLayout.h=(!s.basis fixedLayout.sigma &&
  !(decide (regValue (fixedLayout.y.take 255) s.basis <
   ((ECDSAAdd.p-1)/2)/3+(!s.basis (fixedLayout.Y 255)).toNat)))) (m : List Bool) :
 run (segment fixedLayout) m s=
 ⟨s.phase,maskBasis ((List.range 13).map fixedLayout.R) (writeBit s.basis fixedLayout.h false)⟩ := by
 let L:=fixedLayout
 let u:State:=⟨s.phase,cmpBasis L s.basis⟩
 have ub:u.basis L.bias=false:=(front_bias s).trans bias
 have er:=lowBlock_correct ref r u (front_source ref s src) (front_pending ref s 13 (by decide) rs)
  (front_cmp ref s src clean) ub (m.take 14)
 have eqBody:=erased_eq L.R 13 u (run (lowBlock L) (m.take 14) u) er
 have free:∀q∈(List.range 13).map L.R,q∉wires (cmpBack L) := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨i,hi,eq⟩
  apply back_away_r L fixed_widths fixed_nodup q
  rw [←eq]
  exact r_mem L fixed_widths i (by have h:=List.mem_range.mp hi;omega)
 have pair:=pair_run_fixed s (m.drop 14)
 simp only [run_append,front_measurements,List.take_zero,List.drop_zero] at pair
 rw [front_run _ front_nodup] at pair
 have erase:=clearQuotient_correct L fixed_widths fixed_nodup s (m.drop 14) clean quotient
 simp only [segment,run_append,measurementCount_append,front_measurements,low_measurements,
  Nat.zero_add,List.take_zero,List.drop_zero]
 rw [front_run _ front_nodup]
 change run (cmpBack L) (m.drop 14) (run (lowBlock L) (m.take 14) u)=_
 rw [eqBody,run_mask (cmpBack L) ((List.range 13).map L.R) free u (m.drop 14),pair,erase]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: ComparePrefix
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge
attribute [local irreducible] run

def upperStages (L : DecoderLayout) : Program := upper L++(DirectDecoder.highBlock L++DirectDecoder.middle L)

theorem prefix_correct (ref : BasisState) (r : Reference fixedLayout ref)
 (s : State) (f : GraphInput fixedLayout ref s) (m : List Bool) :
 ErasedRange (fun i=>fixedLayout.R (13+i)) 243 s (run (upperStages fixedLayout) m s) := by
 let L:=fixedLayout
 let mh:=m.drop (measurementCount (upper L))
 let mm:=mh.drop (measurementCount (highBlock L))
 let u:=run (upper L) m s
 let v:=run (highBlock L) mh u
 let w:=run (middle L) mm v
 have src : SourceData L ref s:=⟨f.source,f.sigma,f.h⟩
 have rs : Pending L ref 256 s:=f.result
 have eu : ErasedRange (fun i=>L.R (36+i)) 220 s u:=
   upper_correct L fixed_widths fixed_nodup ref r s src rs m
 have su : SourceData L ref u:=range_source L fixed_widths fixed_nodup 36 220 (by decide) ref s u eu src
 have pu : Pending L ref 36 u:=range_pending L fixed_widths fixed_nodup 36 220 (by decide) ref s u eu
   (fun j hj=>rs j (by omega))
 have cu : ∀k,k<255 → u.basis (L.A k)=false := by
   intro k hk
   exact (range_carry L fixed_widths fixed_nodup 36 220 (by decide) s u eu k hk).trans (f.carry k hk)
 have ev : ErasedRange (fun i=>L.R (32+i)) 4 u v:=
   highBlock_correct ref r u su pu (cu 0 (by decide)) mh
 have sv : SourceData L ref v:=range_source L fixed_widths fixed_nodup 32 4 (by decide) ref u v ev su
 have pv : Pending L ref 32 v:=range_pending L fixed_widths fixed_nodup 32 4 (by decide) ref u v ev
   (fun j hj=>pu j (by omega))
 have cv : ∀k,k<255 → v.basis (L.A k)=false := by
   intro k hk
   exact (range_carry L fixed_widths fixed_nodup 32 4 (by decide) u v ev k hk).trans (cu k hk)
 have ew : ErasedRange (fun i=>L.R (13+i)) 19 v w:=
   middle_correct L fixed_widths fixed_nodup ref r v sv pv mm
 have sw : SourceData L ref w:=range_source L fixed_widths fixed_nodup 13 19 (by decide) ref v w ew sv
 have pw : Pending L ref 13 w:=range_pending L fixed_widths fixed_nodup 13 19 (by decide) ref v w ew
   (fun j hj=>pv j (by omega))
 have cw : ∀k,k<255 → w.basis (L.A k)=false := by
   intro k hk
   exact (range_carry L fixed_widths fixed_nodup 13 19 (by decide) v w ew k hk).trans (cv k hk)

 have runeq:run (upperStages L) m s=w := by
  simp only [upperStages,run_append,run_take]
  rfl
 rw [runeq]
 refine ⟨ew.phase.trans (ev.phase.trans eu.phase),?_,?_⟩
 · intro q hq
   apply (ew.outside q (fun i hi=>hq i (by omega))).trans
   apply (ev.outside q (fun i hi=>by
    have h:=hq (19+i) (by omega)
    simpa only [show 13+(19+i)=32+i by omega] using h)).trans
   exact eu.outside q (fun i hi=>by
    have h:=hq (23+i) (by omega)
    simpa only [show 13+(23+i)=36+i by omega] using h)
 · intro j hj
   by_cases low:j<19
   · exact ew.cleared j low
   · rw [range_above L fixed_widths fixed_nodup 13 19 (by decide) v w ew (13+j) (by omega) (by omega)]
     by_cases high:j<23
     · have h:=ev.cleared (j-19) (by omega)
       simpa only [show 32+(j-19)=13+j by omega] using h
     · rw [range_above L fixed_widths fixed_nodup 32 4 (by decide) u v ev (13+j) (by omega) (by omega)]
       have h:=eu.cleared (j-23) (by omega)
       simpa only [show 36+(j-23)=13+j by omega] using h

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareMaskFacts
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge

theorem mask_append (qs rs : List Wire) (b : BasisState) :
 maskBasis qs (maskBasis rs b)=maskBasis (qs++rs) b := by
 funext q
 by_cases hq:q∈qs <;> by_cases hr:q∈rs <;> simp [maskBasis,hq,hr]

theorem mask_write (qs : List Wire) (h : Wire) (free : h∉qs) (b : BasisState) :
 maskBasis qs (writeBit b h false)=writeBit (maskBasis qs b) h false := by
 funext q
 by_cases eq:q=h
 · subst q
   simp [maskBasis,writeBit,free]
 · by_cases mem:q∈qs <;> simp [maskBasis,writeBit,eq,mem]

theorem result_partition : ((List.range 13).map fixedLayout.R)++
 ((List.range 243).map (fun i=>fixedLayout.R (13+i)))=fixedLayout.r := by decide +kernel

theorem low_flag_free : fixedLayout.h∉(List.range 13).map fixedLayout.R := by
 intro mem
 have all:=List.mem_append_left ((List.range 243).map (fun i=>fixedLayout.R (13+i))) mem
 rw [result_partition] at all
 exact source_r_away _ fixed_nodup fixedLayout.h (by tauto) all

theorem masks_combined (b : BasisState) :
 maskBasis ((List.range 13).map fixedLayout.R)
  (writeBit (maskBasis ((List.range 243).map (fun i=>fixedLayout.R (13+i))) b) fixedLayout.h false)=
 writeBit (maskBasis fixedLayout.r b) fixedLayout.h false := by
 rw [mask_write _ _ low_flag_free,mask_append,result_partition]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareClean
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge
attribute [local irreducible] run maskBasis

def Quota (L : DecoderLayout) (b : BasisState) : Prop := b L.h=(!b L.sigma &&
 !(decide (regValue (L.y.take 255) b < ((ECDSAAdd.p-1)/2)/3+(!b (L.Y 255)).toNat)))

theorem quota_of_outside (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (a b : BasisState) (same : ∀q,q∉L.r→b q=a q) (quota : Quota L a) : Quota L b := by
 have values:regValue (L.y.take 255) b=regValue (L.y.take 255) a := by
  apply regValue_congr
  intro q hq
  exact same q (source_r_away L hn q (Or.inl (List.mem_of_mem_take hq)))
 unfold Quota
 rw [same L.h (source_r_away L hn L.h (by tauto)),same L.sigma (source_r_away L hn L.sigma (by tauto)),
  same (L.Y 255) (source_r_away L hn _ (Or.inl (y_mem L hw 255 (by decide)))),values]
 exact quota

def cleanedNext : Program := upperStages fixedLayout++segment fixedLayout

theorem cleanedNext_semantics (ref : BasisState) (r : Reference fixedLayout ref)
 (s : State) (f : GraphInput fixedLayout ref s) (quota : Quota fixedLayout s.basis) (m : List Bool) :
 run cleanedNext m s=⟨s.phase,writeBit (maskBasis fixedLayout.r s.basis) fixedLayout.h false⟩ := by
 let L:=fixedLayout
 let w:=run (upperStages L) m s
 have er:=prefix_correct ref r s f m
 have src:SourceData L ref s:=⟨f.source,f.sigma,f.h⟩
 have sw:SourceData L ref w:=range_source L fixed_widths fixed_nodup 13 243 (by decide) ref s w er src
 have pw:Pending L ref 13 w:=range_pending L fixed_widths fixed_nodup 13 243 (by decide) ref s w er
  (fun j hj=>f.result j (by omega))
 have ci:∀i,i<255→w.basis (L.A i)=false := by
  intro i hi
  exact (range_carry L fixed_widths fixed_nodup 13 243 (by decide) s w er i hi).trans (f.carry i hi)
 have cw:∀q∈L.carry,w.basis q=false := by
  intro q hq
  apply index_zero_mem L.carry w.basis _ q hq
  intro i hi
  exact ci i (by change i<L.carry.length at hi;rw [fixed_widths.2.2] at hi;exact hi)
 have out:∀q,q∉L.r→w.basis q=s.basis q:=range_outside L fixed_widths 13 243 (by decide) s w er
 have bw:w.basis L.bias=false:=
  (out L.bias (source_r_away L fixed_nodup L.bias (by tauto))).trans f.bias
 have qw:Quota L w.basis:=quota_of_outside L fixed_widths fixed_nodup s.basis w.basis out quota
 have seg:=segment_correct ref r w sw pw cw bw qw (m.drop (measurementCount (upperStages L)))
 have eq:run cleanedNext m s=run (segment L) (m.drop (measurementCount (upperStages L))) w := by
  simp only [cleanedNext,run_append,run_take]
  rfl
 rw [eq,seg]
 have weq:=erased_eq (fun i=>L.R (13+i)) 243 s w er
 rw [weq]
 rw [masks_combined]

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareQuotaSource
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Challenge
theorem quota_source (L : DecoderLayout) (hw : L.Widths) (a : BasisState) (s : State)
 (src : SourceData L a s) (quota : Quota L a) : Quota L s.basis := by
 have vals:regValue (L.y.take 255) s.basis=regValue (L.y.take 255) a := by
  apply regValue_congr
  intro q hq
  rcases List.mem_iff_getElem.mp (List.mem_of_mem_take hq) with ⟨i,hi,eq⟩
  have ylen: L.y.length≤256 := by have h:=hw.1;omega
  have get:L.Y i=q:=by rw [DecoderLayout.Y,List.getD_eq_getElem _ _ hi];exact eq
  rw [←get]
  exact src.source i (by omega)
 unfold Quota
 rw [src.h,src.sigma,src.source 255 (by decide),vals]
 exact quota

end ECDSAAdd.Entrant.CompareDecoder

-- Proof component: CompareDecoderFinal
set_option maxRecDepth 30000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder DecoderCells5 DecoderMeasuredTail DecoderBiasReuse Secp256k1 BalancedField Challenge Baselines
attribute [local irreducible] run maskBasis

theorem cleanedNext_correct (f : State)
    (clean : ∀i,i<255 → f.basis (fixedLayout.A i)=false)
    (scalar : regValue fixedLayout.r f.basis=
      ((if f.basis fixedLayout.sigma then regValue (fixedLayout.y.take 255) f.basis
        else 3*regValue (fixedLayout.y.take 255) f.basis)+
        2*(f.basis fixedLayout.bias).toNat+(f.basis fixedLayout.h).toNat*(2^32+977))%2^256)
    (bias : f.basis 784=(f.basis 1041 && !f.basis 2425))
    (quotient : f.basis fixedLayout.h=(!f.basis fixedLayout.sigma &&
      !(decide (regValue (fixedLayout.y.take 255) f.basis <
        ((p-1)/2)/3+(!f.basis (fixedLayout.Y 255)).toNat)))) (m : List Bool) :
    ∃t,CoreResult fixedLayout f t ∧ run cleanedNext m (withoutBias f)=
      ⟨f.phase,writeBit (writeBit t.basis fixedLayout.bias false) fixedLayout.h false⟩ := by
  have exclusive : (f.basis fixedLayout.sigma && f.basis fixedLayout.h)=false := by
    rw [quotient]
    cases f.basis fixedLayout.sigma <;> simp
  let ref:=run (aProgram fixedLayout) [] f
  have good:=reference_after_add f clean scalar bias exclusive
  have src:SourceData fixedLayout f.basis (withoutBias f) := by
    constructor
    · intro j hj
      change writeBit f.basis fixedLayout.bias false (fixedLayout.Y j)=_
      exact Function.update_of_ne (y_ne_bias ⟨j,hj⟩) false f.basis
    · change writeBit f.basis fixedLayout.bias false fixedLayout.sigma=_
      exact Function.update_of_ne (by decide +kernel : fixedLayout.sigma≠fixedLayout.bias) false f.basis
    · change writeBit f.basis fixedLayout.bias false fixedLayout.h=_
      exact Function.update_of_ne (by decide +kernel : fixedLayout.h≠fixedLayout.bias) false f.basis
  have quota:Quota fixedLayout (withoutBias f).basis:=
    quota_source fixedLayout fixed_widths f.basis (withoutBias f) src quotient
  let L:=fixedLayout
  let v:State:=⟨f.phase,maskBasis L.r (withoutBias f).basis⟩
  have fv:FastCoreResult f v := by
    refine ⟨rfl,?_,?_,?_,?_⟩
    · intro q _ hr hb
      change maskBasis L.r (writeBit f.basis L.bias false) q=f.basis q
      rw [maskBasis,if_neg hr]
      exact Function.update_of_ne hb false f.basis
    · intro i hi
      have ar:L.A i∉L.r:=source_r_away L fixed_nodup (L.A i) (Or.inr (Or.inl (a_mem L fixed_widths i hi)))
      change maskBasis L.r (withoutBias f).basis (L.A i)=false
      rw [maskBasis,if_neg ar]
      change writeBit f.basis L.bias false (L.A i)=false
      rw [writeBit,Function.update_of_ne (a_ne_bias ⟨i,hi⟩)]
      exact clean i hi
    · intro i hi
      change maskBasis L.r (withoutBias f).basis (L.R i)=false
      simp only [maskBasis,if_pos (r_mem L fixed_widths i hi)]
    · have free:L.bias∉L.r:=source_r_away L fixed_nodup L.bias (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      change maskBasis L.r (withoutBias f).basis L.bias=false
      rw [maskBasis,if_neg free]
      exact Function.update_self L.bias false f.basis
  obtain ⟨t,old,veq⟩:=restore_old_core f v fv
  have actual:=cleanedNext_semantics ref.basis good.1 (withoutBias f) good.2 quota m
  refine ⟨t,old,?_⟩
  rw [actual]
  change (⟨f.phase,writeBit v.basis L.h false⟩ : State)=_
  rw [veq]

theorem cellDecoderNext_parts : cellDecoderNext=
 frontFast fixedLayout++(cleanedNext++back fixedLayout) := by
 simp only [cellDecoderNext,cleanedNext,upperStages,segment,back,List.append_assoc]

theorem cellDecoderNext_correct (Y : Fp) (sigma : Bool) (s : State) (m : List Bool)
    (ys : regValue fixedLayout.y s.basis=centerWord Y)
    (rs : regValue fixedLayout.r s.basis=centerWord ((if sigma then 1 else 3)*Y))
    (sig : s.basis fixedLayout.sigma=sigma)
    (hc : s.basis fixedLayout.h=false) (bc : s.basis fixedLayout.bias=false)
    (cc : ∀q∈fixedLayout.carry,s.basis q=false) :
    (run (cellDecoderNext) m s).phase=s.phase ∧
    (∀q,q∉fixedLayout.r → (run (cellDecoderNext) m s).basis q=s.basis q) ∧
    regValue fixedLayout.r (run (cellDecoderNext) m s).basis=centerWord Y := by
  have result := run_three_states (frontFast fixedLayout) cleanedNext (back fixedLayout)
    (fun a d=>a=s → d.phase=s.phase ∧
      (∀q,q∉fixedLayout.r → d.basis q=s.basis q) ∧ regValue fixedLayout.r d.basis=centerWord Y) (by
      intro a n u d m1 m2 m3 han hnu hud eq
      subst a
      let f : State := ⟨s.phase,frontBasis fixedLayout s.basis⟩
      have neq : n=withoutBias f := by
        rw [←han,frontFast_view s m1 bc,TerminalGraph.front_run fixedLayout fixed_widths fixed_nodup]
      rw [neq] at hnu
      have scalar := actual_front_scalar fixedLayout fixed_widths fixed_nodup
        s.basis Y sigma ys rs sig hc bc
      have nc : ∀i,i<255 → f.basis (fixedLayout.A i)=false := by
        intro i hi
        exact front_carry_clean fixedLayout fixed_nodup s.basis cc
          (fixedLayout.A i) (a_mem fixedLayout fixed_widths i hi)
      have bb : f.basis 784=(f.basis 1041 && !f.basis 2425) := by
        have facts := actual_front_values fixedLayout fixed_widths fixed_nodup
          s.basis Y sigma ys rs sig hc bc
        change frontBasis fixedLayout s.basis fixedLayout.bias=
          (frontBasis fixedLayout s.basis (fixedLayout.Y 255) &&
            !frontBasis fixedLayout s.basis fixedLayout.sigma)
        rw [facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2]
      have cg := cleanedNext_correct f nc scalar.1
        bb scalar.2 m2
      obtain ⟨t,tf,ut⟩ := cg
      rw [hnu] at ut
      have cleanbasis := cleaned_front_basis fixedLayout fixed_widths fixed_nodup
        s.basis s.phase t tf hc bc cc
      have uz : u=⟨s.phase,zeroR fixedLayout s.basis⟩ := by
        rw [ut,cleanbasis]
      have done := back_correct fixedLayout fixed_widths fixed_nodup s.basis s.phase m3
      rw [uz] at hud
      rw [hud] at done
      exact ⟨done.1,done.2.1,done.2.2.trans ys⟩) s m
  rw [cellDecoderNext_parts]
  exact result rfl

theorem cellDecoderNext_frame (origin : BasisState)
    (clean : ∀q∈work fixedLayout,origin q=false) (X Y : Fp)
    (hend : (X+(if origin fixedLayout.sigma then Y else -Y))/2=Y) :
    Triple (PairFrame fixedLayout.r fixedLayout.y origin (centerWord X) (centerWord Y))
      (cellDecoderNext)
      (PairFrame fixedLayout.r fixedLayout.y origin (centerWord Y) (centerWord Y)) := by
  intro s m input
  have cleanS (q : Wire) (hq:q∈work fixedLayout) : s.basis q=false :=
    (input.2.2 q (work_away fixedLayout fixed_nodup q hq).1
      (work_away fixedLayout fixed_nodup q hq).2).trans (clean q hq)
  have sig : s.basis fixedLayout.sigma=origin fixedLayout.sigma := input.2.2 fixedLayout.sigma
    (source_r_away fixedLayout fixed_nodup _ (by tauto))
    (flag_y_away fixedLayout fixed_nodup _ (by simp))
  have rel := terminal_relation X Y (origin fixedLayout.sigma) hend
  have rword : regValue fixedLayout.r s.basis=
      centerWord ((if origin fixedLayout.sigma then 1 else 3)*Y) := by
    rw [input.1,rel]
  have c := cellDecoderNext_correct Y (origin fixedLayout.sigma) s m input.2.1 rword sig
    (cleanS fixedLayout.h (by simp [work])) (cleanS fixedLayout.bias (by simp [work]))
    (fun q hq=>cleanS q (by simp [work,hq]))
  refine ⟨c.1,c.2.2,?_,?_⟩
  · exact (regValue_congr fixedLayout.y _ _ (fun q hq=>c.2.1 q
      (source_r_away fixedLayout fixed_nodup q (Or.inl hq)))).trans input.2.1
  · intro q qr qy
    exact (c.2.1 q qr).trans (input.2.2 q qr qy)

end ECDSAAdd.Entrant.CompareDecoder

#print axioms ECDSAAdd.Entrant.CompareDecoder.cellDecoderNext_frame
#print axioms ECDSAAdd.Entrant.CompareDecoder.counts

end
