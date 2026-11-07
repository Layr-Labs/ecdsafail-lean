import ECDSAAdd.Submission.Entrant.CompareDecoder.FiniteBase
import Mathlib.Data.Nat.Bitwise
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
