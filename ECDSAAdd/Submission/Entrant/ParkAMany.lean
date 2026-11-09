import ECDSAAdd.Submission.Entrant.ParkAWorkLoan
import ECDSAAdd.Submission.Entrant.ParkAStagedProof

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open ThirdSavedCarryDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def bitsValue:List Bool→Nat
 | []=>0
 | b::bs=>b.toNat+2*bitsValue bs

def chain (n:Nat) (xs ys:List Bool) (cin:Bool):Bool:=
 match n,xs,ys with
 | 0,_,_=>cin
 | n+1,a::as,b::bs=>chain n as bs (carryBit a b cin)
 | _,_,_=>cin

theorem chain_value (n:Nat) (xs ys:List Bool) (cin:Bool)
 (hx:n≤xs.length) (hy:n≤ys.length):
 (chain n xs ys cin).toNat=(bitsValue (xs.take n)+bitsValue (ys.take n)+cin.toNat)/2^n:=by
 induction n generalizing xs ys cin with
 | zero=>simp[chain,bitsValue]
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    rw[chain,ih as bs (carryBit a b cin) (by simp_all) (by simp_all),carry_bit_nat]
    simp only[List.take_succ_cons,bitsValue]
    have hd:(a.toNat+2*bitsValue (as.take n)+(b.toNat+2*bitsValue (bs.take n))+cin.toNat)/2=
     bitsValue (as.take n)+bitsValue (bs.take n)+(a.toNat+b.toNat+cin.toNat)/2:=by omega
    calc
     _=((a.toNat+2*bitsValue (as.take n)+(b.toNat+2*bitsValue (bs.take n))+cin.toNat)/2)/2^n:=by rw[hd]
     _=(a.toNat+2*bitsValue (as.take n)+(b.toNat+2*bitsValue (bs.take n))+cin.toNat)/(2*2^n):=by rw[Nat.div_div_eq_div_mul]
     _=_:=by rw[Nat.pow_succ,Nat.mul_comm (2^n) 2]
#print axioms chain_value
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def lastCarry (n:Nat) (cs:List Wire) (cin:Wire):Wire:=
 match n,cs with
 | 0,_=>cin
 | n+1,c::cs=>lastCarry n cs c
 | _,[]=>cin

theorem prefixState_last (n:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n≤xs.length) (hy:n≤ys.length) (hc:n≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀w∈cs,s.basis w=false):
 (prefixState n xs ys cs cin s).basis (lastCarry n cs cin)=
 chain n (xs.map s.basis) (ys.map s.basis) (s.basis cin):=by
 induction n generalizing xs ys cs cin s with
 | zero=>rfl
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    cases cs with
    | nil=>simp at hc
    | cons c cs=>
     have nd:=prefix_tail_nd a b c cin as bs cs hn
     have away:c∉as++bs++cs:=(List.nodup_cons.mp nd).1
     let s1:State:=⟨s.phase,writeBit s.basis c (s.basis c ^^ carryBit (s.basis a) (s.basis b) (s.basis cin))⟩
     have outside (w:Wire) (hw:w∈as++bs++cs):s1.basis w=s.basis w:=by
      have ne:w≠c:=by intro e;exact away (e ▸ hw)
      simp[s1,writeBit,ne]
     have clean:∀w∈cs,s1.basis w=false:=by
      intro w hw
      exact (outside w (List.mem_append_right _ hw)).trans (hz w (by simp[hw]))
     have xmap:as.map s1.basis=as.map s.basis:=by
      apply List.map_congr_left
      intro w hw
      exact outside w (List.mem_append_left _ (List.mem_append_left _ hw))
     have ymap:bs.map s1.basis=bs.map s.basis:=by
      apply List.map_congr_left
      intro w hw
      exact outside w (List.mem_append_left _ (List.mem_append_right _ hw))
     have cvalue:s1.basis c=carryBit (s.basis a) (s.basis b) (s.basis cin):=by
      have zero:s.basis c=false:=hz c (by simp)
      simp[s1,writeBit,zero]
     have h:=ih as bs cs c s1 (by simp_all) (by simp_all) (by simp_all) nd clean
     rw[xmap,ymap,cvalue]at h
     simpa only[prefixState,lastCarry,chain,List.map_cons]using h

theorem prefix_value (n:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State) (m:List Bool)
 (hx:n≤xs.length) (hy:n≤ys.length) (hc:n≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀w∈cs,s.basis w=false):
 ((run (carryPrefix n xs ys cs cin) m s).basis (lastCarry n cs cin)).toNat=
 (bitsValue ((xs.map s.basis).take n)+bitsValue ((ys.map s.basis).take n)+(s.basis cin).toNat)/2^n:=by
 rw[carryPrefix_run n xs ys cs cin hn s m,prefixState_last n xs ys cs cin s hx hy hc hn hz]
 exact chain_value n _ _ _ (by simpa using hx) (by simpa using hy)
#print axioms prefixState_last
#print axioms prefix_value
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem bitsValue_map (xs:List Wire) (s:BasisState):bitsValue (xs.map s)=regValue xs s:=by
 induction xs with
 | nil=>rfl
 | cons q xs ih=>cases h:s q <;> simp[bitsValue,regValue,ih,h]

theorem lastCarry_index (n:Nat) (cs:List Wire) (cin:Wire) (hc:n+1≤cs.length):
 lastCarry (n+1) cs cin=cs.getD n 0:=by
 induction n generalizing cs cin with
 | zero=>cases cs with
   | nil=>simp at hc
   | cons c cs=>rfl
 | succ n ih=>
  cases cs with
  | nil=>simp at hc
  | cons c cs=>
   change lastCarry (n+1) cs c=cs.getD n 0
   exact ih cs c (by simp_all)

theorem prefix_value_reg (n:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State) (m:List Bool)
 (hx:n+1≤xs.length) (hy:n+1≤ys.length) (hc:n+1≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀w∈cs,s.basis w=false):
 ((run (carryPrefix (n+1) xs ys cs cin) m s).basis (cs.getD n 0)).toNat=
 (regValue (xs.take (n+1)) s.basis+regValue (ys.take (n+1)) s.basis+(s.basis cin).toNat)/2^(n+1):=by
 have h:=prefix_value (n+1) xs ys cs cin s m hx hy hc hn hz
 rw[lastCarry_index n cs cin hc]at h
 simpa only[←List.map_take,bitsValue_map]using h
#print axioms prefix_value_reg
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def subPreN (n:Nat) (xs ys cs:List Wire) (cin:Wire):Program:=notRegister ys++carryPrefix n xs ys cs cin

theorem subPre_value (n:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n+1≤xs.length) (hy:n+1≤ys.length) (hc:n+1≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (s:State)
 (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false):
 ((run (subPreN (n+1) xs ys cs cin) [] s).basis (cs.getD n 0)).toNat=
 (regValue (xs.take (n+1)) s.basis+(2^(n+1)-1-regValue (ys.take (n+1)) s.basis))/2^(n+1):=by
  have nd:=List.nodup_cons.mp hn
  have split:=List.nodup_append'.mp nd.2
  have xy:=List.nodup_append'.mp split.1
  have xAway:∀q∈xs,q∉ys := by
    intro q hq bad
    exact List.disjoint_left.mp xy.2.2 hq bad
  have cAway:∀q∈cs,q∉ys := by
    intro q hq bad
    exact List.disjoint_left.mp split.2.2 (List.mem_append_right _ bad) hq
  have cinAway:cin∉ys := by
    intro bad
    exact nd.1 (List.mem_append_left _ (List.mem_append_right _ bad))
  let t:=run (notRegister ys) [] s
  have nr:=notRegister_correct ys xy.2.1 s []
  have zt:∀q∈cs,t.basis q=false := by
    intro q hq
    change (run (notRegister ys) [] s).basis q=false
    rw [nr]
    simpa [cAway q hq] using hz q hq
  have it:t.basis cin=false := by
    change (run (notRegister ys) [] s).basis cin=false
    rw [nr]
    simpa [cinAway] using hi
  have xv:regValue (xs.take (n+1)) t.basis=regValue (xs.take (n+1)) s.basis := by
    apply regValue_congr
    intro q hq
    change (run (notRegister ys) [] s).basis q=s.basis q
    rw [nr]
    simp [xAway q (List.mem_of_mem_take hq)]
  have yv:regValue (ys.take (n+1)) t.basis=2^(n+1)-1-regValue (ys.take (n+1)) s.basis := by
    have e:regValue (ys.take (n+1)) t.basis=regValue (ys.take (n+1)) (fun q=>!s.basis q) := by
      apply regValue_congr
      intro q hq
      change (run (notRegister ys) [] s).basis q= !s.basis q
      rw [nr]
      simp [List.mem_of_mem_take hq]
    rw [e,regValue_complement]
    have len:(ys.take (n+1)).length=n+1 := by simp [hy]
    rw [len]
  have val:=prefix_value_reg n xs ys cs cin t [] hx hy hc hn zt
  rw[xv,yv,it]at val
  simp only[Bool.toNat_false,Nat.add_zero]at val
  have count:measurementCount (notRegister ys)=0:=(notRegister_counts ys).2
  simpa only[subPreN,run_append,count,List.take_zero,List.drop_zero]using val

#print axioms subPre_value
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def nextMajority (n:Nat) (xs ys cs:List Wire) (cin:Wire):Program:=
 majority (xs.getD n 0) (ys.getD n 0) (lastCarry n cs cin) (cs.getD n 0)

theorem prefix_split (n:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n+1≤xs.length) (hy:n+1≤ys.length) (hc:n+1≤cs.length):
 carryPrefix (n+1) xs ys cs cin=carryPrefix n xs ys cs cin++nextMajority n xs ys cs cin:=by
 induction n generalizing xs ys cs cin with
 | zero=>cases xs <;> cases ys <;> cases cs <;> simp_all[carryPrefix,nextMajority,lastCarry]
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    cases cs with
    | nil=>simp at hc
    | cons c cs=>
     simp only[carryPrefix]
     rw[ih as bs cs c (by simp_all) (by simp_all) (by simp_all)]
     simp[nextMajority,lastCarry,List.append_assoc]

theorem next_nd (n:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n+1≤xs.length) (hy:n+1≤ys.length) (hc:n+1≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup):
 [xs.getD n 0,ys.getD n 0,lastCarry n cs cin,cs.getD n 0].Nodup:=by
 induction n generalizing xs ys cs cin with
 | zero=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    cases cs with
    | nil=>simp at hc
    | cons c cs=>exact prefix_head_nd a b c cin as bs cs hn
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    cases cs with
    | nil=>simp at hc
    | cons c cs=>
     exact ih as bs cs c (by simp_all) (by simp_all) (by simp_all) (prefix_tail_nd a b c cin as bs cs hn)
#print axioms prefix_split
#print axioms next_nd
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem index_not_take (n:Nat) (cs:List Wire) (hc:n<cs.length) (hn:cs.Nodup):cs.getD n 0∉cs.take n:=by
 induction n generalizing cs with
 | zero=>simp
 | succ n ih=>
  cases cs with
  | nil=>simp at hc
  | cons c cs=>
   have nd:=List.nodup_cons.mp hn
   have len:n<cs.length:=by simp_all
   simp only[List.getD_cons_succ,List.take_succ_cons,List.mem_cons,not_or]
   constructor
   · intro e;exact nd.1 (e ▸ DiagSq.getD_in cs n len)
   · exact ih cs len nd.2

theorem next_value (n:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n+1≤xs.length) (hy:n+1≤ys.length) (hc:n+1≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀w∈cs,s.basis w=false):
 let t:=run (carryPrefix n xs ys cs cin) [] s
 (carryBit (t.basis (xs.getD n 0)) (t.basis (ys.getD n 0)) (t.basis (lastCarry n cs cin))).toNat=
 (regValue (xs.take (n+1)) s.basis+regValue (ys.take (n+1)) s.basis+(s.basis cin).toNat)/2^(n+1):=by
 let t:=run (carryPrefix n xs ys cs cin) [] s
 have ndcs:cs.Nodup:=(List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
 have clean:t.basis (cs.getD n 0)=false:=
  (carryPrefix_preserves n xs ys cs cin hn s [] _ (index_not_take n cs (by omega) ndcs)).trans
   (hz _ (DiagSq.getD_in cs n (by omega)))
 have val:=prefix_value_reg n xs ys cs cin s [] hx hy hc hn hz
 rw[prefix_split n xs ys cs cin hx hy hc,run_append,List.take_nil,List.drop_nil]at val
 rw[nextMajority,majority_correct _ _ _ _ (next_nd n xs ys cs cin hx hy hc hn) t [],clean]at val
 simpa only[writeBit,Function.update_self,Bool.false_xor]using val
#print axioms next_value
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem borrow_value (m x a:Nat) (hm:0<m) (hx:x<m) (ha:a<m):
 (x+(m-1-a))/m=(if a<x then 1 else 0):=by
 split_ifs with h
 · apply Nat.div_eq_of_lt_le <;> omega
 · apply Nat.div_eq_of_lt
   omega

theorem carry_same_mod (m X Y A:Nat) (hm:0<m) (sum:X+Y=A):
 (X%m+(m-1-A%m))/m=(X%m+Y%m)/m:=by
 let x:=X%m
 let y:=Y%m
 have hx:x<m:=Nat.mod_lt _ hm
 have hy:y<m:=Nat.mod_lt _ hm
 have ha:A%m<m:=Nat.mod_lt _ hm
 have rem:A%m=(x+y)%m:=by rw[←sum];exact Nat.add_mod _ _ _
 change (x+(m-1-A%m))/m=(x+y)/m
 rw[borrow_value m x (A%m) hm hx ha]
 by_cases small:x+y<m
 · have same:A%m=x+y:=rem.trans (Nat.mod_eq_of_lt small)
   have no:¬A%m<x:=by rw[same];omega
   simp only[no,if_false]
   exact (Nat.div_eq_of_lt small).symm
 · have ge:m≤x+y:=by omega
   have last:x+y-m<m:=by omega
   have same:A%m=x+y-m:=by rw[rem,Nat.mod_eq_sub_mod ge,Nat.mod_eq_of_lt last]
   have yes:A%m<x:=by rw[same];omega
   simp only[yes,if_true]
   symm
   apply Nat.div_eq_of_lt_le <;> omega

theorem w64_return (m H:Nat) (hm:0<m):
 (H%m+(m-1-(1040*H/64)%m))/m=(H%m+(976*H/64)%m)/m:=by
 apply carry_same_mod m H (976*H/64) (1040*H/64) hm
 omega
#print axioms borrow_value
#print axioms carry_same_mod
#print axioms w64_return
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def cacheN (k H:Nat):Bool:=decide ((1040*H/64)%2^k<H%2^k)

theorem cacheN_value (k H:Nat):(cacheN k H).toNat=(if (1040*H/64)%2^k<H%2^k then 1 else 0):=by
 by_cases h:(1040*H/64)%2^k<H%2^k <;> simp[cacheN,h]

theorem sub_known (n:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n+1≤xs.length) (hy:n+1≤ys.length) (hc:n+1≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (H:Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64):
 (run (subPreN (n+1) xs ys cs cin) [] s).basis (cs.getD n 0)=cacheN (n+1) H:=by
 have val:=subPre_value n xs ys cs cin hx hy hc hn s hz hi
 rw[regValue_take_mod xs (n+1) hx s.basis,regValue_take_mod ys (n+1) hy s.basis,source,target]at val
 have hm:0<2^(n+1):=by positivity
 rw[borrow_value _ _ _ hm (Nat.mod_lt _ hm) (Nat.mod_lt _ hm)]at val
 exact bool_nat_injective _ _ (val.trans (cacheN_value (n+1) H).symm)

theorem add_next_known (n:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n+1≤xs.length) (hy:n+1≤ys.length) (hc:n+1≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (H:Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=976*H/64):
 let t:=run (carryPrefix n xs ys cs cin) [] s
 carryBit (t.basis (xs.getD n 0)) (t.basis (ys.getD n 0)) (t.basis (lastCarry n cs cin))=cacheN (n+1) H:=by
 have val:=next_value n xs ys cs cin s hx hy hc hn hz
 rw[regValue_take_mod xs (n+1) hx s.basis,regValue_take_mod ys (n+1) hy s.basis,source,target,hi]at val
 simp only[Bool.toNat_false,Nat.add_zero]at val
 have hm:0<2^(n+1):=by positivity
 rw[←w64_return _ H hm,borrow_value _ _ _ hm (Nat.mod_lt _ hm) (Nat.mod_lt _ hm)]at val
 exact bool_nat_injective _ _ (val.trans (cacheN_value (n+1) H).symm)
#print axioms sub_known
#print axioms add_next_known
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem prefix_compose (n m:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n≤xs.length) (hy:n≤ys.length) (hc:n≤cs.length):
 carryPrefix (n+m) xs ys cs cin=carryPrefix n xs ys cs cin++
 carryPrefix m (xs.drop n) (ys.drop n) (cs.drop n) (lastCarry n cs cin):=by
 induction n generalizing xs ys cs cin with
 | zero=>simp[carryPrefix,lastCarry]
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    cases cs with
    | nil=>simp at hc
    | cons c cs=>
     simp only[Nat.succ_add,carryPrefix,List.drop_succ_cons,lastCarry]
     rw[ih as bs cs c (by simp_all) (by simp_all) (by simp_all)]
     simp[List.append_assoc]

theorem layout_after (n:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n≤xs.length) (hy:n≤ys.length) (hc:n≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup):
 (lastCarry n cs cin::(xs.drop n++ys.drop n++cs.drop n)).Nodup:=by
 induction n generalizing xs ys cs cin with
 | zero=>exact hn
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    cases cs with
    | nil=>simp at hc
    | cons c cs=>
     exact ih as bs cs c (by simp_all) (by simp_all) (by simp_all) (prefix_tail_nd a b c cin as bs cs hn)

theorem prefix_earlier (j total:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hj:j+1≤total) (hx:total≤xs.length) (hy:total≤ys.length) (hc:total≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup):
 (run (carryPrefix total xs ys cs cin) [] s).basis (cs.getD j 0)=
 (run (carryPrefix (j+1) xs ys cs cin) [] s).basis (cs.getD j 0):=by
 have eq:total=(j+1)+(total-(j+1)):=by omega
 have nd:=layout_after (j+1) xs ys cs cin (by omega) (by omega) (by omega) hn
 have outside:cs.getD j 0∉(cs.drop (j+1)).take (total-(j+1)):=by
  intro h
  have ht:cs.getD j 0∈cs.drop (j+1):=List.mem_of_mem_take h
  rw[←lastCarry_index j cs cin (by omega)]at ht
  exact (List.nodup_cons.mp nd).1 (by simp[ht])
 rw[eq,prefix_compose (j+1) (total-(j+1)) xs ys cs cin (by omega) (by omega) (by omega),run_append,List.take_nil,List.drop_nil]
 exact carryPrefix_preserves _ _ _ _ _ nd _ [] _ outside
#print axioms prefix_compose
#print axioms layout_after
#print axioms prefix_earlier
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem sub_earlier (j total:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hj:j+1≤total) (hx:total≤xs.length) (hy:total≤ys.length) (hc:total≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup):
 (run (subPreN total xs ys cs cin) [] s).basis (cs.getD j 0)=
 (run (subPreN (j+1) xs ys cs cin) [] s).basis (cs.getD j 0):=by
 simp only[subPreN,run_append,List.take_nil,List.drop_nil]
 exact prefix_earlier j total xs ys cs cin (run (notRegister ys) [] s) hj hx hy hc hn

theorem all_sub_known (j total:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hj:j+1≤total) (hx:total≤xs.length) (hy:total≤ys.length) (hc:total≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (H:Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64):
 (run (subPreN total xs ys cs cin) [] s).basis (cs.getD j 0)=cacheN (j+1) H:=
 (sub_earlier j total xs ys cs cin s hj hx hy hc hn).trans
  (sub_known j xs ys cs cin s (by omega) (by omega) (by omega) hn hz hi H source target)
#print axioms all_sub_known
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def copyMany (xs hs:List Wire):Program:=
 match xs,hs with
 | x::xs,h::hs=>.CX x h::copyMany xs hs
 | _,_=>[]

def scatterState (hs:List Wire) (vs:List Bool) (s:State):State:=
 match hs,vs with
 | h::hs,v::vs=>scatterState hs vs (setWire s h v)
 | _,_=>s

theorem run_scatter (p:Program) (hs:List Wire) (vs:List Bool) (s:State) (m:List Bool)
 (off:∀h∈hs,h∉wires p):
 run p m (scatterState hs vs s)=scatterState hs vs (run p m s):=by
 induction hs generalizing vs s with
 | nil=>rfl
 | cons h hs ih=>
  cases vs with
  | nil=>rfl
  | cons v vs=>
   simp only[scatterState]
   rw[ih vs (setWire s h v) (fun q hq=>off q (by simp[hq]))]
   have he:run p m (setWire s h v)=setWire (run p m s) h v:=run_update_outside p h v (off h (by simp)) s m
   rw[he]

theorem copyMany_frame (xs hs:List Wire) (s:State) (m:List Bool)
 (nd:hs.Nodup) (fresh:∀h∈hs,h∉xs) (zero:∀h∈hs,s.basis h=false):
 run (copyMany xs hs) m s=scatterState hs (xs.map s.basis) s:=by
 induction xs generalizing hs s with
 | nil=>cases hs <;> rfl
 | cons x xs ih=>
  cases hs with
  | nil=>rfl
  | cons h hs=>
   let s1:=setWire s h (s.basis x)
   have ndt:hs.Nodup:=(List.nodup_cons.mp nd).2
   have ft:∀q∈hs,q∉xs:=by
    intro q hq bad
    exact fresh q (by simp[hq]) (by simp[bad])
   have zt:∀q∈hs,s1.basis q=false:=by
    intro q hq
    have ne:q≠h:=by intro e;exact (List.nodup_cons.mp nd).1 (e ▸ hq)
    simpa only[s1,setWire,writeBit,Function.update_of_ne ne]using zero q (by simp[hq])
   have mp:xs.map s1.basis=xs.map s.basis:=by
    apply List.map_congr_left
    intro q hq
    have ne:q≠h:=by intro e;exact fresh h (by simp) (by simp[e ▸ hq])
    simp only[s1,setWire,writeBit,Function.update_of_ne ne]
   have hz:s.basis h=false:=zero h (by simp)
   have out:=ih hs s1 ndt ft zt
   rw[mp]at out
   simpa only[copyMany,run,hz,Bool.false_xor,List.map_cons,scatterState,s1,setWire]using out

theorem copyMany_counts (xs hs:List Wire):toffoliCount (copyMany xs hs)=0 ∧ measurementCount (copyMany xs hs)=0:=by
 induction xs generalizing hs with
 | nil=>simp[copyMany,toffoliCount,measurementCount]
 | cons x xs ih=>
  cases hs with
  | nil=>simp[copyMany,toffoliCount,measurementCount]
  | cons h hs=>simpa only[copyMany,toffoliCount,measurementCount]using ih hs
#print axioms run_scatter
#print axioms copyMany_frame
#print axioms copyMany_counts
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem copyMany_slots (xs hs:List Wire):
 Challenge.gateSlots (copyMany xs hs)=min xs.length hs.length:=by
 induction xs generalizing hs with
 | nil=>simp[copyMany,Challenge.gateSlots]
 | cons x xs ih=>
  cases hs with
  | nil=>simp[copyMany,Challenge.gateSlots]
  | cons h hs=>simpa [copyMany,Challenge.gateSlots,Challenge.instructionSlots,Nat.succ_min_succ,Nat.add_comm] using congrArg Nat.succ (ih hs)

theorem copyMany_support (xs hs:List Wire):
 wires (copyMany xs hs)⊆xs.toFinset∪hs.toFinset:=by
 induction xs generalizing hs with
 | nil=>simp[copyMany,wires]
 | cons x xs ih=>
  cases hs with
  | nil=>simp[copyMany,wires]
  | cons h hs=>
   intro q hq
   simp only[copyMany,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq
   rcases hq with (rfl|rfl)|hq
   · simp
   · simp
   · have ht:=ih hs hq
     simp only[Finset.mem_union,List.mem_toFinset] at ht ⊢
     rcases ht with ht|ht
     · exact Or.inl (by simp[ht])
     · exact Or.inr (by simp[ht])

theorem copyMany_physical (xs hs:List Wire) (fresh:∀h∈hs,h∉xs):
 ∀i∈copyMany xs hs,Challenge.instructionValid i:=by
 induction xs generalizing hs with
 | nil=>simp[copyMany]
 | cons x xs ih=>
  cases hs with
  | nil=>simp[copyMany]
  | cons h hs=>
   intro i hi
   simp only[copyMany,List.mem_cons]at hi
   rcases hi with rfl|hi
   · exact fun eq=>fresh h (by simp) (by simp[eq])
   · exact ih hs (fun q hq hxs=>fresh q (by simp[hq]) (by simp[hxs])) i hi
#print axioms copyMany_slots
#print axioms copyMany_support
#print axioms copyMany_physical
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def subPostN (n:Nat) (xs ys cs:List Wire) (cin:Wire):Program:=
 addKTSuffix true n xs ys cs cin++notRegister ys

def prefixAfter (n k:Nat) (xs ys cs:List Wire) (cin:Wire):Program:=
 carryPrefix k (xs.drop n) (ys.drop n) (cs.drop n) (lastCarry n cs cin)

theorem subPost_split (n k:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:n+k+2≤ys.length):
 subPostN n xs ys cs cin=prefixAfter n k xs ys cs cin++subPostN (n+k) xs ys cs cin:=by
 have a:=addKT_split true n xs ys cs cin hx hc (by omega)
 have b:=addKT_split true (n+k) xs ys cs cin hx hc hy
 rw[prefix_compose n k xs ys cs cin (by omega) (by omega) (by omega),List.append_assoc]at b
 have eq:carryPrefix n xs ys cs cin++addKTSuffix true n xs ys cs cin=
  carryPrefix n xs ys cs cin++(prefixAfter n k xs ys cs cin++addKTSuffix true (n+k) xs ys cs cin):=a.symm.trans b
 have tail:=List.append_cancel_left eq
 simp only[subPostN,tail,List.append_assoc]

theorem cachedSubTriple_splitN (k:Nat) (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length):
 cachedSubTriple xs ys cs cin q r t=
 (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin)++subPostN (7+k) xs ys cs cin:=by
 have tail:=subPost_split 7 k xs ys cs cin hx hc hy
 change subPost7 xs ys cs cin=_ at tail
 rw[cachedSubTriple,tail]
 simp only[preTriple,insertCopy,List.append_assoc]

def cachedSubMany (k:Nat) (xs ys cs hs:List Wire) (cin q r t:Wire):Program:=
 (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin)++
 copyMany ((cs.drop 7).take k) hs++subPostN (7+k) xs ys cs cin
#print axioms subPost_split
#print axioms cachedSubTriple_splitN
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem insertMany_frame (pre post:Program) (xs hs:List Wire) (s:State) (m:List Bool)
 (nd:hs.Nodup) (fresh:∀h∈hs,h∉xs)
 (offpre:∀h∈hs,h∉wires pre) (offpost:∀h∈hs,h∉wires post)
 (zero:∀h∈hs,s.basis h=false):
 run (pre++copyMany xs hs++post) m s=
 scatterState hs (xs.map (run pre (m.take (measurementCount pre)) s).basis) (run (pre++post) m s):=by
 have z:∀h∈hs,(run pre (m.take (measurementCount pre)) s).basis h=false:=by
  intro h hh
  rw[run_preserves_outside pre _ s h (offpre h hh)]
  exact zero h hh
 rw[List.append_assoc,run_append,run_append,(copyMany_counts xs hs).2,List.take_zero,List.drop_zero]
 rw[copyMany_frame xs hs _ [] nd fresh z,run_scatter post hs _ _ _ offpost]
 rw[run_append]
#print axioms insertMany_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem cachedSubMany_frame (k:Nat) (xs ys cs hs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length)
 (nd:hs.Nodup) (fresh:∀h∈hs,h∉cs)
 (off:∀h∈hs,h∉wires (cachedSubTriple xs ys cs cin q r t))
 (s:State) (m:List Bool) (zero:∀h∈hs,s.basis h=false):
 run (cachedSubMany k xs ys cs hs cin q r t) m s=
 scatterState hs (((cs.drop 7).take k).map
   (run (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin) [] s).basis)
   (run (cachedSubTriple xs ys cs cin q r t) m s):=by
 have split:=cachedSubTriple_splitN k xs ys cs cin q r t hx hc hy
 have op:∀h∈hs,h∉wires (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin):=by
  intro h hh bad
  apply off h hh
  rw[split,wires_append]
  exact Finset.mem_union_left _ bad
 have ot:∀h∈hs,h∉wires (subPostN (7+k) xs ys cs cin):=by
  intro h hh bad
  apply off h hh
  rw[split,wires_append]
  exact Finset.mem_union_right _ bad
 have ft:∀h∈hs,h∉(cs.drop 7).take k:=by
  intro h hh bad
  exact fresh h hh (List.mem_of_mem_drop (List.mem_of_mem_take bad))
 have mp:measurementCount (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin)=0:=by
  simp[preTriple,secondCopy,insertCopy,subPre,sixthMajority,seventhMajority,prefixAfter,majority,
   measurementCount_append,(notRegister_counts ys).2,carryPrefix_measurements,measurementCount]
 have eq:=insertMany_frame (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin)
  (subPostN (7+k) xs ys cs cin) ((cs.drop 7).take k) hs s m nd ft op ot zero
 simpa only[cachedSubMany,mp,List.take_zero,←split,List.append_assoc] using eq
#print axioms cachedSubMany_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem scatter_phase (hs:List Wire) (vs:List Bool) (s:State):
 (scatterState hs vs s).phase=s.phase:=by
 induction hs generalizing vs s with
 | nil=>rfl
 | cons h hs ih=>
  cases vs with
  | nil=>rfl
  | cons v vs=>exact ih vs (setWire s h v)

theorem scatter_outside (hs:List Wire) (vs:List Bool) (s:State) (w:Wire) (off:w∉hs):
 (scatterState hs vs s).basis w=s.basis w:=by
 induction hs generalizing vs s with
 | nil=>rfl
 | cons h hs ih=>
  cases vs with
  | nil=>rfl
  | cons v vs=>
   rw[scatterState,ih vs (setWire s h v) (by simp_all)]
   simp only[setWire,writeBit,Function.update_of_ne (show w≠h by simp_all)]

theorem scatter_update (hs:List Wire) (vs:List Bool) (s:State) (w:Wire) (v:Bool) (off:w∉hs):
 scatterState hs vs (setWire s w v)=setWire (scatterState hs vs s) w v:=by
 induction hs generalizing vs s with
 | nil=>rfl
 | cons h hs ih=>
  cases vs with
  | nil=>rfl
  | cons b vs=>
   simp only[scatterState]
   have ne:w≠h:=by simp_all
   have comm:setWire (setWire s w v) h b=setWire (setWire s h b) w v:=by
    cases s with
    | mk phase basis=>
     simp only[setWire,writeBit]
     congr 1
     exact Function.update_comm ne v b basis
   rw[comm,ih vs (setWire s h b) (by simp_all)]
#print axioms scatter_phase
#print axioms scatter_outside
#print axioms scatter_update
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def moveMany (xs hs:List Wire):Program:=
 match xs,hs with
 | x::xs,h::hs=>move h x++moveMany xs hs
 | _,_=>[]

theorem moveMany_frame (xs hs:List Wire) (s:State) (m:List Bool)
 (len:xs.length=hs.length) (ndx:xs.Nodup) (ndh:hs.Nodup)
 (fresh:∀h∈hs,h∉xs) (zero:∀x∈xs,s.basis x=false):
 run (moveMany xs hs) m s=
 scatterState hs (List.replicate hs.length false) (scatterState xs (hs.map s.basis) s):=by
 induction xs generalizing hs s with
 | nil=>cases hs <;> simp_all[moveMany,scatterState,run]
 | cons x xs ih=>
  cases hs with
  | nil=>simp at len
  | cons h hs=>
   have hx:x∉xs:=(List.nodup_cons.mp ndx).1
   have hh:h∉hs:=(List.nodup_cons.mp ndh).1
   have hx_h:x≠h:=by intro e;exact fresh h (by simp) (by simp[e])
   let s1:=setWire (setWire s x (s.basis h)) h false
   have zt:∀q∈xs,s1.basis q=false:=by
    intro q hq
    have qx:q≠x:=by intro e;exact hx (e ▸ hq)
    have qh:q≠h:=by intro e;exact fresh h (by simp) (by simp[e ▸ hq])
    simpa only[s1,setWire,writeBit,Function.update_of_ne qh,Function.update_of_ne qx]using zero q (by simp[hq])
   have mapEq:hs.map s1.basis=hs.map s.basis:=by
    apply List.map_congr_left
    intro q hq
    have qh:q≠h:=by intro e;exact hh (e ▸ hq)
    have qx:q≠x:=by intro e;exact fresh q (by simp[hq]) (by simp[←e])
    simp only[s1,setWire,writeBit,Function.update_of_ne qh,Function.update_of_ne qx]
   have ft:∀q∈hs,q∉xs:=by
    intro q hq hxs
    exact fresh q (by simp[hq]) (by simp[hxs])
   have result:=ih hs s1 (by simpa using len) (List.nodup_cons.mp ndx).2 (List.nodup_cons.mp ndh).2 ft zt
   rw[mapEq]at result
   rw[moveMany,run_append,show measurementCount (move h x)=0 by rfl,List.take_zero,List.drop_zero,
    move_correct h x hx_h.symm s [] (zero x (by simp))]
   change run (moveMany xs hs) m s1=_
   rw[result]
   simp only[List.length_cons,List.replicate_succ,List.map_cons,scatterState]
   rw[←scatter_update xs (hs.map s.basis) (setWire s x (s.basis h)) h false
    (fun bad=>fresh h (by simp) (by simp[bad]))]
#print axioms moveMany_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem scatter_restore (xs:List Wire) (s u:State) (nd:xs.Nodup)
 (phase:u.phase=s.phase) (outside:∀w,w∉xs→u.basis w=s.basis w):
 scatterState xs (xs.map u.basis) s=u:=by
 induction xs generalizing s with
 | nil=>
  change s=u
  cases s with
  | mk sp sb=>
   cases u with
   | mk up ub=>
    simp only at phase outside
    have hb:ub=sb:=funext (fun w=>outside w (by simp))
    simp_all
 | cons x xs ih=>
  simp only[List.map_cons,scatterState]
  apply ih (setWire s x (u.basis x)) (List.nodup_cons.mp nd).2 phase
  intro w hw
  by_cases eq:w=x
  · subst w;simp[setWire,writeBit]
  · simp only[setWire,writeBit,Function.update_of_ne eq]
    exact outside w (by simp[eq,hw])

theorem moveMany_emulates (xs hs:List Wire) (s u:State) (m:List Bool)
 (len:xs.length=hs.length) (ndx:xs.Nodup) (ndh:hs.Nodup)
 (fresh:∀h∈hs,h∉xs) (zero:∀x∈xs,s.basis x=false)
 (phase:u.phase=s.phase) (outside:∀w,w∉xs→u.basis w=s.basis w)
 (saved:hs.map s.basis=xs.map u.basis):
 run (moveMany xs hs) m s=scatterState hs (List.replicate hs.length false) u:=by
 rw[moveMany_frame xs hs s m len ndx ndh fresh zero,saved,scatter_restore xs s u ndx phase outside]
#print axioms scatter_restore
#print axioms moveMany_emulates
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem prefixState_phase (n:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State):
 (prefixState n xs ys cs cin s).phase=s.phase:=by
 induction n generalizing xs ys cs cin s with
 | zero=>rfl
 | succ n ih=>
  cases xs <;> cases ys <;> cases cs <;> simp only[prefixState]
  exact ih _ _ _ _ _

theorem moveMany_prefix (n:Nat) (xs ys cs hs:List Wire) (cin:Wire) (s:State) (m:List Bool)
 (hc:n≤cs.length) (len:hs.length=n)
 (hn:(cin::(xs++ys++cs)).Nodup) (ndh:hs.Nodup)
 (fresh:∀h∈hs,h∉cs.take n) (zero:∀x∈cs.take n,s.basis x=false)
 (saved:hs.map s.basis=(cs.take n).map (run (carryPrefix n xs ys cs cin) [] s).basis):
 run (moveMany (cs.take n) hs) m s=
 scatterState hs (List.replicate hs.length false) (run (carryPrefix n xs ys cs cin) [] s):=by
 have ndc:cs.Nodup:=by
  exact (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
 have phase:(run (carryPrefix n xs ys cs cin) [] s).phase=s.phase:=by
  rw[carryPrefix_run n xs ys cs cin hn s []]
  exact prefixState_phase n xs ys cs cin s
 exact moveMany_emulates (cs.take n) hs s (run (carryPrefix n xs ys cs cin) [] s) m
  (by simp only[List.length_take];omega) ndc.take ndh fresh zero phase
  (fun w hw=>carryPrefix_preserves n xs ys cs cin hn s [] w hw) saved
#print axioms prefixState_phase
#print axioms moveMany_prefix
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem add_known (n:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n+1≤xs.length) (hy:n+1≤ys.length) (hc:n+1≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (H:Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=976*H/64):
 (run (carryPrefix (n+1) xs ys cs cin) [] s).basis (cs.getD n 0)=cacheN (n+1) H:=by
 have val:=prefix_value_reg n xs ys cs cin s [] hx hy hc hn hz
 rw[regValue_take_mod xs (n+1) hx s.basis,regValue_take_mod ys (n+1) hy s.basis,source,target,hi]at val
 simp only[Bool.toNat_false,Nat.add_zero]at val
 have hm:0<2^(n+1):=by positivity
 rw[←w64_return _ H hm,borrow_value _ _ _ hm (Nat.mod_lt _ hm) (Nat.mod_lt _ hm)]at val
 exact bool_nat_injective _ _ (val.trans (cacheN_value (n+1) H).symm)

theorem all_add_known (j total:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hj:j+1≤total) (hx:total≤xs.length) (hy:total≤ys.length) (hc:total≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (H:Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=976*H/64):
 (run (carryPrefix total xs ys cs cin) [] s).basis (cs.getD j 0)=cacheN (j+1) H:=
 (prefix_earlier j total xs ys cs cin s hj hx hy hc hn).trans
  (add_known j xs ys cs cin s (by omega) (by omega) (by omega) hn hz hi H source target)
#print axioms add_known
#print axioms all_add_known
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def bankValues (n k H:Nat):List Bool:=(List.range k).map (fun i=>cacheN (n+i+1) H)

theorem bankValues_map (n k H:Nat) (cs:List Wire) (f:Wire→Bool)
 (hc:n+k≤cs.length) (known:∀j,j<k→f (cs.getD (n+j) 0)=cacheN (n+j+1) H):
 ((cs.drop n).take k).map f=bankValues n k H:=by
 apply List.ext_getElem
 · simp only[List.length_map,List.length_take,List.length_drop,bankValues,List.length_range]
   omega
 · intro i h1 h2
   have hi:i<k:=by simpa only[bankValues,List.length_map,List.length_range]using h2
   have h:=known i hi
   rw[List.getD_eq_getElem cs 0 (by omega)]at h
   simpa only[List.getElem_map,List.getElem_take,List.getElem_drop,bankValues,List.getElem_range]using h

theorem sub_bankValues (n k H:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n+k≤xs.length) (hy:n+k≤ys.length) (hc:n+k≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64):
 ((cs.drop n).take k).map (run (subPreN (n+k) xs ys cs cin) [] s).basis=bankValues n k H:=by
 apply bankValues_map n k H cs _ hc
 intro j hj
 exact all_sub_known (n+j) (n+k) xs ys cs cin s (by omega) hx hy hc hn hz hi H source target

theorem add_bankValues (n k H:Nat) (xs ys cs:List Wire) (cin:Wire) (s:State)
 (hx:n+k≤xs.length) (hy:n+k≤ys.length) (hc:n+k≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (source:regValue xs s.basis=H) (target:regValue ys s.basis=976*H/64):
 ((cs.drop n).take k).map (run (carryPrefix (n+k) xs ys cs cin) [] s).basis=bankValues n k H:=by
 apply bankValues_map n k H cs _ hc
 intro j hj
 exact all_add_known (n+j) (n+k) xs ys cs cin s (by omega) hx hy hc hn hz hi H source target
#print axioms sub_bankValues
#print axioms add_bankValues

#print axioms bankValues_map
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem subPreN_split7 (k:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:7≤xs.length) (hy:7≤ys.length) (hc:7≤cs.length):
 subPreN (7+k) xs ys cs cin=
 subPre xs ys cs cin++sixthMajority xs ys cs++seventhMajority xs ys cs++prefixAfter 7 k xs ys cs cin:=by
 rw[subPreN,prefix_compose 7 k xs ys cs cin hx hy hc]
 rw[←List.append_assoc]
 change subPre7 xs ys cs cin++prefixAfter 7 k xs ys cs cin=_
 rw[subPre7_split xs ys cs cin hx hy hc,subPre6_split xs ys cs cin (by omega) (by omega) (by omega)]

theorem plainSub_splitN (k:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length):
 subPreN (7+k) xs ys cs cin++subPostN (7+k) xs ys cs cin=CodexNarrowSub.program xs ys cs cin:=by
 rw[CodexNarrowSub.program,addKT_split true (7+k) xs ys cs cin hx hc hy]
 simp only[subPreN,subPostN,List.append_assoc]

theorem preTriple_value (k:Nat) (xs ys cs:List Wire) (cin q r t w:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length)
 (qoff:q∉wires (CodexNarrowSub.program xs ys cs cin))
 (roff:r∉wires (CodexNarrowSub.program xs ys cs cin)) (rq:r≠q)
 (toff:t∉wires (cachedSubDual xs ys cs cin q r))
 (wq:w≠q) (wr:w≠r) (wt:w≠t)
 (s:State) (hq:s.basis q=false) (hr:s.basis r=false) (ht:s.basis t=false):
 (run (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin) [] s).basis w=
 (run (subPreN (7+k) xs ys cs cin) [] s).basis w:=by
 have split:=plainSub_splitN k xs ys cs cin hx hc hy
 rw[subPreN_split7 k xs ys cs cin (by omega) (by omega) (by omega)]at split
 simp only[List.append_assoc]at split
 have qo:=qoff
 have ro:=roff
 rw[←split]at qo ro
 simp only[wires_append,Finset.mem_union,not_or]at qo ro
 have rfirst:r∉wires (cachedSub xs ys cs cin q):=by
  intro h
  have h:=Finset.mem_insert.mp (cachedSub_support xs ys cs cin q hx hc (by omega) h)
  exact h.elim rq roff
 rw[cachedSub_first_split xs ys cs cin q hx hc (by omega),firstCopy_split,wires_append,Finset.mem_union,not_or]at rfirst
 have tail:=subPost_split 7 k xs ys cs cin hx hc hy
 change subPost7 xs ys cs cin=_ at tail
 have tfree:=toff
 rw[cachedSubDual_split7 xs ys cs cin q r hx hc (by omega),tail]at tfree
 simp only[wires_append,Finset.mem_union,not_or]at tfree
 have dq:cs.getD 5 0≠q:=by
  intro e;apply qo.2.1
  simp[sixthMajority,majority,wires,Instr.wires,←e]
 have mp:measurementCount (subPre xs ys cs cin)=0:=by
  simp only[subPre,measurementCount_append,(notRegister_counts ys).2,carryPrefix_measurements,Nat.zero_add]
 have value:=thirdCopy_value (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs) (prefixAfter 7 k xs ys cs cin)
  (cs.getD 4 0) (cs.getD 5 0) (cs.getD 6 0) q r t w
  qo.1 qo.2.1 qo.2.2.1 qo.2.2.2.1 rfirst.1 ro.2.2.1 ro.2.2.2.1 tfree.1 tfree.2.1 mp rfl dq wq wr wt s hq hr ht
 rw[subPreN_split7 k xs ys cs cin (by omega) (by omega) (by omega)]
 simpa only[preTriple,insertCopy,List.append_assoc]using value
#print axioms preTriple_value

#print axioms subPreN_split7
#print axioms plainSub_splitN
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem preTriple_bankValues (k H:Nat) (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (s:State)
 (hz:∀w∈cs,s.basis w=false) (hi:s.basis cin=false)
 (qoff:q∉wires (CodexNarrowSub.program xs ys cs cin))
 (roff:r∉wires (CodexNarrowSub.program xs ys cs cin)) (rq:r≠q)
 (toff:t∉wires (cachedSubDual xs ys cs cin q r))
 (qc:q∉cs) (rc:r∉cs) (tc:t∉cs)
 (hq:s.basis q=false) (hr:s.basis r=false) (ht:s.basis t=false)
 (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64):
 ((cs.drop 7).take k).map (run (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin) [] s).basis=
 bankValues 7 k H:=by
 have eq:((cs.drop 7).take k).map (run (preTriple xs ys cs cin q r t++prefixAfter 7 k xs ys cs cin) [] s).basis=
  ((cs.drop 7).take k).map (run (subPreN (7+k) xs ys cs cin) [] s).basis:=by
  apply List.map_congr_left
  intro w hw
  have mem:w∈cs:=List.mem_of_mem_drop (List.mem_of_mem_take hw)
  exact preTriple_value k xs ys cs cin q r t w hx hc hy qoff roff rq toff
   (fun e=>qc (e ▸ mem)) (fun e=>rc (e ▸ mem)) (fun e=>tc (e ▸ mem)) s hq hr ht
 rw[eq]
 exact sub_bankValues 7 k H xs ys cs cin s (by omega) (by omega) (by omega) hn hz hi source target

theorem cachedSubMany_known_frame (k H:Nat) (xs ys cs hs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (s:State) (m:List Bool)
 (hz:∀w∈cs,s.basis w=false) (hi:s.basis cin=false)
 (qoff:q∉wires (CodexNarrowSub.program xs ys cs cin))
 (roff:r∉wires (CodexNarrowSub.program xs ys cs cin)) (rq:r≠q)
 (toff:t∉wires (cachedSubDual xs ys cs cin q r))
 (qc:q∉cs) (rc:r∉cs) (tc:t∉cs)
 (hq:s.basis q=false) (hr:s.basis r=false) (ht:s.basis t=false)
 (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64)
 (nd:hs.Nodup) (fresh:∀h∈hs,h∉cs)
 (off:∀h∈hs,h∉wires (cachedSubTriple xs ys cs cin q r t))
 (zero:∀h∈hs,s.basis h=false):
 run (cachedSubMany k xs ys cs hs cin q r t) m s=
 scatterState hs (bankValues 7 k H) (run (cachedSubTriple xs ys cs cin q r t) m s):=by
 rw[cachedSubMany_frame k xs ys cs hs cin q r t hx hc hy nd fresh off s m zero,
  preTriple_bankValues k H xs ys cs cin q r t hx hc hy hn s hz hi qoff roff rq toff qc rc tc hq hr ht source target]
#print axioms cachedSubMany_known_frame

#print axioms preTriple_bankValues
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem cachedSubMany_counts (k:Nat) (xs ys cs hs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length):
 toffoliCount (cachedSubMany k xs ys cs hs cin q r t)=toffoliCount (cachedSubTriple xs ys cs cin q r t) ∧
 measurementCount (cachedSubMany k xs ys cs hs cin q r t)=measurementCount (cachedSubTriple xs ys cs cin q r t) ∧
 Challenge.gateSlots (cachedSubMany k xs ys cs hs cin q r t)=
  Challenge.gateSlots (cachedSubTriple xs ys cs cin q r t)+min ((cs.drop 7).take k).length hs.length:=by
 rw[cachedSubTriple_splitN k xs ys cs cin q r t hx hc hy]
 simp only[cachedSubMany,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
  (copyMany_counts ((cs.drop 7).take k) hs).1,(copyMany_counts ((cs.drop 7).take k) hs).2,copyMany_slots]
 omega

theorem cachedSubTriple_carry_live (k:Nat) (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length)
 (w:Wire) (hw:w∈(cs.drop 7).take k):
 w∈wires (cachedSubTriple xs ys cs cin q r t):=by
 have live:=carryPrefix_carry_mem k (xs.drop 7) (ys.drop 7) (cs.drop 7) (lastCarry 7 cs cin)
  (by simp only[List.length_drop];omega) (by simp only[List.length_drop];omega)
  (by simp only[List.length_drop];omega) w hw
 rw[cachedSubTriple_splitN k xs ys cs cin q r t hx hc hy,wires_append,wires_append]
 exact Finset.mem_union_left _ (Finset.mem_union_right _ live)

theorem cachedSubMany_support (k:Nat) (xs ys cs hs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length)
:
 wires (cachedSubMany k xs ys cs hs cin q r t)⊆wires (cachedSubTriple xs ys cs cin q r t)∪hs.toFinset:=by
 have split:=cachedSubTriple_splitN k xs ys cs cin q r t hx hc hy
 intro w hw
 simp only[cachedSubMany,wires_append,Finset.mem_union]at hw
 rcases hw with (hp|hp)|hp
 · exact Finset.mem_union_left _ (by rw[split,wires_append];exact Finset.mem_union_left _ (by simpa only[wires_append,Finset.mem_union] using hp))
 · have h:=copyMany_support ((cs.drop 7).take k) hs hp
   rcases Finset.mem_union.mp h with h|h
   · exact Finset.mem_union_left _ (cachedSubTriple_carry_live k xs ys cs cin q r t hx hc hy w (List.mem_toFinset.mp h))
   · exact Finset.mem_union_right _ h
 · exact Finset.mem_union_left _ (by rw[split,wires_append];exact Finset.mem_union_right _ hp)

theorem cachedSubMany_physical (k:Nat) (xs ys cs hs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length)
 (fresh:∀h∈hs,h∉cs)
 (old:∀i∈cachedSubTriple xs ys cs cin q r t,Challenge.instructionValid i):
 ∀i∈cachedSubMany k xs ys cs hs cin q r t,Challenge.instructionValid i:=by
 have split:=cachedSubTriple_splitN k xs ys cs cin q r t hx hc hy
 intro i hi
 simp only[cachedSubMany,List.mem_append]at hi
 rcases hi with (hi|hi)|hi
 · apply old i
   rw[split]
   exact List.mem_append_left _ (List.mem_append.mpr hi)
 · exact copyMany_physical ((cs.drop 7).take k) hs
    (fun h hh bad=>fresh h hh (List.mem_of_mem_drop (List.mem_of_mem_take bad))) i hi
 · apply old i
   rw[split]
   exact List.mem_append_right _ hi

#print axioms cachedSubMany_counts
#print axioms cachedSubMany_support
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def mappedSuffix : Nat→List Wire→List Wire→List Wire→Wire→Program
 | n+1,a::as,b::bs,c::cs,cin=>mappedSuffix n as bs cs c++
   mappedEraseCarry ⟨some a,false⟩ b cin c++mappedSum ⟨some a,false⟩ b cin
 | _,xs,ys,cs,cin=>mappedAdd (mappedRead xs false) ys cs cin

theorem mappedAdd_split (n:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n+2≤xs.length) (hy:n+2≤ys.length) (hc:n≤cs.length):
 mappedAdd (mappedRead xs false) ys cs cin=carryPrefix n xs ys cs cin++mappedSuffix n xs ys cs cin:=by
 induction n generalizing xs ys cs cin with
 | zero=>rfl
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases as with
   | nil=>simp at hx
   | cons a' as=>
    cases ys with
    | nil=>simp at hy
    | cons b bs=>
     cases bs with
     | nil=>simp at hy
     | cons b' bs=>
      cases cs with
      | nil=>simp at hc
      | cons c cs=>
       have stepEq:=ih (a'::as) (b'::bs) cs c (by simp_all) (by simp_all) (by simp_all)
       simp only[mappedRead,List.map_cons,mappedAdd,mappedMajority,Bool.false_eq_true,ite_false,carryPrefix,mappedSuffix]
       simp only[mappedRead,List.map_cons]at stepEq
       rw[stepEq]
       simp only[List.append_assoc]

theorem mappedAdd_take (n:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n+2≤xs.length) (hy:n+2≤ys.length) (hc:n≤cs.length):
 (mappedAdd (mappedRead xs false) ys cs cin).take (6*n)=carryPrefix n xs ys cs cin:=by
 rw[mappedAdd_split n xs ys cs cin hx hy hc]
 rw[←carryPrefix_length n xs ys cs cin (by omega) (by omega) hc,List.take_left]
#print axioms mappedAdd_take

#print axioms mappedAdd_split
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem lastCarry_compose (n k:Nat) (cs:List Wire) (cin:Wire) (hc:n≤cs.length):
 lastCarry (n+k) cs cin=lastCarry k (cs.drop n) (lastCarry n cs cin):=by
 induction n generalizing cs cin with
 | zero=>simp[lastCarry]
 | succ n ih=>
  cases cs with
  | nil=>simp at hc
  | cons c cs=>
   simp only[Nat.succ_add,lastCarry,List.drop_succ_cons]
   exact ih cs c (by simpa using hc)

theorem prefixAfter_compose (n j k:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n+j≤xs.length) (hy:n+j≤ys.length) (hc:n+j≤cs.length):
 prefixAfter n (j+k) xs ys cs cin=
 prefixAfter n j xs ys cs cin++prefixAfter (n+j) k xs ys cs cin:=by
 rw[prefixAfter,prefix_compose j k (xs.drop n) (ys.drop n) (cs.drop n) (lastCarry n cs cin)
  (by simp only[List.length_drop];omega) (by simp only[List.length_drop];omega) (by simp only[List.length_drop];omega)]
 simp only[prefixAfter,List.drop_drop,lastCarry_compose n j cs cin (by omega)]
#print axioms lastCarry_compose
#print axioms prefixAfter_compose
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem knownSuffix_after4 (src Z ys cs:List Wire) (cin:Wire)
 (hs:7≤src.length) (hy:7≤ys.length) (hc:7≤cs.length):
 ∃tail:Program,knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) cs cin=
 mappedAdd (mappedRead ((src++Z.take 5).drop 4) false) (ys.drop 4) (cs.drop 4) (cs.getD 3 0)++tail:=by
 obtain ⟨a0,a1,a2,a3,a4,a5,a6,as,rfl⟩:=shape7 src hs
 obtain ⟨b0,b1,b2,b3,b4,b5,b6,bs,rfl⟩:=shape7 ys hy
 obtain ⟨c0,c1,c2,c3,c4,c5,c6,cs,rfl⟩:=shape7 cs hc
 simp only[desired,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
  List.cons_append,List.getD_cons_succ,List.getD_cons_zero,mappedRead,List.map_cons,List.map_nil,knownSuffix]
 exact ⟨_,by simp only[List.append_assoc];rfl⟩
theorem knownSuffix_prefix (n:Nat) (src Z ys cs:List Wire) (cin:Wire)
 (hs:7≤src.length) (hxs:n+6≤src.length) (hy:n+7≤ys.length) (hc:n+7≤cs.length):
 ∃tail:Program,knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) cs cin=
 prefixAfter 4 n (src++Z.take 5) ys cs cin++tail:=by
 obtain ⟨tail,eq⟩:=knownSuffix_after4 src Z ys cs cin hs (by omega) (by omega)
 rw[mappedAdd_split n ((src++Z.take 5).drop 4) (ys.drop 4) (cs.drop 4) (cs.getD 3 0)
  (by simp only[List.length_drop,List.length_append];omega)
  (by simp only[List.length_drop];omega) (by simp only[List.length_drop];omega)]at eq
 refine ⟨mappedSuffix n ((src++Z.take 5).drop 4) (ys.drop 4) (cs.drop 4) (cs.getD 3 0)++tail,?_⟩
 simpa only[prefixAfter,lastCarry_index 3 cs cin (by omega),List.append_assoc]using eq
#print axioms knownSuffix_prefix

#print axioms knownSuffix_after4
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop SourceAddFourDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def inversePostN (k:Nat) (src Z ys cs:List Wire) (cin:Wire):Program:=
 (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) cs cin).drop (6*(3+k))

theorem addPost3_splitN (k:Nat) (src Z ys cs:List Wire) (cin:Wire)
 (hs:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length):
 addPost3 src Z ys cs cin=prefixAfter 7 k (src++Z.take 5) ys cs cin++inversePostN k src Z ys cs cin:=by
 obtain ⟨tail,eq⟩:=knownSuffix_prefix (3+k) src Z ys cs cin (by omega) (by omega) (by omega) (by omega)
 have plen:(prefixAfter 4 (3+k) (src++Z.take 5) ys cs cin).length=6*(3+k):=by
  apply carryPrefix_length <;> simp only[List.length_drop,List.length_append] <;> omega
 have tlen:(prefixAfter 4 3 (src++Z.take 5) ys cs cin).length=18:=by
  apply carryPrefix_length <;> simp only[List.length_drop,List.length_append] <;> omega
 have post:inversePostN k src Z ys cs cin=tail:=by
  rw[inversePostN,eq,←plen,List.drop_left]
 rw[prefixAfter_compose 4 3 k (src++Z.take 5) ys cs cin
  (by simp only[List.length_append];omega) (by omega) (by omega),List.append_assoc]at eq
 change (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) cs cin).drop 18=_
 rw[eq,←tlen,List.drop_left,post]
#print axioms addPost3_splitN
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem moveMany_counts (xs hs:List Wire):
 toffoliCount (moveMany xs hs)=0 ∧ measurementCount (moveMany xs hs)=0 ∧
 Challenge.gateSlots (moveMany xs hs)=2*min xs.length hs.length:=by
 induction xs generalizing hs with
 | nil=>simp[moveMany,toffoliCount,measurementCount,Challenge.gateSlots]
 | cons x xs ih=>
  cases hs with
  | nil=>simp[moveMany,toffoliCount,measurementCount,Challenge.gateSlots]
  | cons h hs=>
   have result:=ih hs
   simp only[moveMany,move,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,Nat.succ_min_succ]at result ⊢
   omega

theorem moveMany_support (xs hs:List Wire):wires (moveMany xs hs)⊆xs.toFinset∪hs.toFinset:=by
 induction xs generalizing hs with
 | nil=>simp[moveMany,wires]
 | cons x xs ih=>
  cases hs with
  | nil=>simp[moveMany,wires]
  | cons h hs=>
   intro q hq
   rw[moveMany,wires_append]at hq
   rcases Finset.mem_union.mp hq with hq|hq
   · have head:q=h ∨ q=x:=by simpa[move,wires,Instr.wires,or_comm,or_left_comm,or_assoc]using hq
     rcases head with rfl|rfl <;> simp
   · have ht:=ih hs hq
     simp only[Finset.mem_union,List.mem_toFinset]at ht ⊢
     rcases ht with ht|ht
     · exact Or.inl (by simp[ht])
     · exact Or.inr (by simp[ht])

theorem moveMany_physical (xs hs:List Wire) (fresh:∀h∈hs,h∉xs):
 ∀i∈moveMany xs hs,Challenge.instructionValid i:=by
 induction xs generalizing hs with
 | nil=>simp[moveMany]
 | cons x xs ih=>
  cases hs with
  | nil=>simp[moveMany]
  | cons h hs=>
   intro i hi
   rw[moveMany]at hi
   rcases List.mem_append.mp hi with hi|hi
   · have ne:h≠x:=by intro e;exact fresh h (by simp) (by simp[e])
     simp only[move,List.mem_cons,List.not_mem_nil,or_false]at hi
     rcases hi with rfl|rfl
     · exact ne
     · exact ne.symm
   · exact ih hs (fun q hq bad=>fresh q (by simp[hq]) (by simp[bad])) i hi
#print axioms moveMany_physical

#print axioms moveMany_counts
#print axioms moveMany_support
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop SourceAddFourDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def consumePre3 (src Z ys cs:List Wire) (cin q r t:Wire):Program:=
 ((addPre src Z ys cs cin++move q (cs.getD 4 0))++move r (cs.getD 5 0))++move t (cs.getD 6 0)

def consumedAddMany (k:Nat) (src Z ys cs hs:List Wire) (cin q r t:Wire):Program:=
 consumePre3 src Z ys cs cin q r t++moveMany ((cs.drop 7).take k) hs++inversePostN k src Z ys cs cin

theorem consumedAddTriple_splitN (k:Nat) (src Z ys cs:List Wire) (cin q r t:Wire)
 (hsrc:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length):
 consumedAddTriple src Z ys cs cin q r t=
 consumePre3 src Z ys cs cin q r t++prefixAfter 7 k (src++Z.take 5) ys cs cin++inversePostN k src Z ys cs cin:=by
 rw[consumedAddTriple,addPost3_splitN k src Z ys cs cin hsrc hy hc]
 simp only[consumePre3,List.append_assoc]

theorem consumePre3_M (src Z ys cs:List Wire) (cin q r t:Wire):
 measurementCount (consumePre3 src Z ys cs cin q r t)=0:=by
 have mp:measurementCount (addPre src Z ys cs cin)=0:=(knownPrefix_counts _ _ _ _ _ _).2
 simp only[consumePre3,measurementCount_append,mp,move,measurementCount,Nat.zero_add]

theorem consumedAddMany_frame (k:Nat) (src Z ys cs hs:List Wire) (cin q r t:Wire)
 (hsrc:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length)
 (hn:(cin::((src++Z.take 5)++ys++cs)).Nodup) (ndh:hs.Nodup) (len:hs.length=k)
 (fresh:∀h∈hs,h∉(cs.drop 7).take k)
 (off:∀h∈hs,h∉wires (inversePostN k src Z ys cs cin))
 (s:State) (m:List Bool)
 (zero:∀x∈(cs.drop 7).take k,(run (consumePre3 src Z ys cs cin q r t) [] s).basis x=false)
 (saved:hs.map (run (consumePre3 src Z ys cs cin q r t) [] s).basis=
  ((cs.drop 7).take k).map (run (prefixAfter 7 k (src++Z.take 5) ys cs cin) []
    (run (consumePre3 src Z ys cs cin q r t) [] s)).basis):
 run (consumedAddMany k src Z ys cs hs cin q r t) m s=
 scatterState hs (List.replicate hs.length false) (run (consumedAddTriple src Z ys cs cin q r t) m s):=by
 have nd:=layout_after 7 (src++Z.take 5) ys cs cin
  (by simp only[List.length_append];omega) (by omega) (by omega) hn
 have mv:=moveMany_prefix k ((src++Z.take 5).drop 7) (ys.drop 7) (cs.drop 7) hs (lastCarry 7 cs cin)
  (run (consumePre3 src Z ys cs cin q r t) [] s) []
  (by simp only[List.length_drop];omega) len nd ndh fresh zero saved
 have mm:measurementCount (moveMany ((cs.drop 7).take k) hs)=0:=(moveMany_counts _ _).2.1
 have pm:measurementCount (prefixAfter 7 k (src++Z.take 5) ys cs cin)=0:=carryPrefix_measurements _ _ _ _ _
 simp only[consumedAddMany,consumedAddTriple_splitN k src Z ys cs cin q r t hsrc hy hc,
  List.append_assoc,run_append,consumePre3_M,mm,pm,List.take_zero,List.drop_zero]
 rw[mv,run_scatter _ hs _ _ _ off]
 rfl
#print axioms consumedAddTriple_splitN
#print axioms consumePre3_M
#print axioms consumedAddMany_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem carryPrefix_T (n:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n≤xs.length) (hy:n≤ys.length) (hc:n≤cs.length):
 toffoliCount (carryPrefix n xs ys cs cin)=n:=by
 induction n generalizing xs ys cs cin with
 | zero=>rfl
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    cases cs with
    | nil=>simp at hc
    | cons c cs=>
     rw[carryPrefix,toffoliCount_append,ih as bs cs c (by simp_all) (by simp_all) (by simp_all)]
     simp[majority,toffoliCount,Nat.add_comm]

theorem carryPrefix_slots (n:Nat) (xs ys cs:List Wire) (cin:Wire)
 (hx:n≤xs.length) (hy:n≤ys.length) (hc:n≤cs.length):
 Challenge.gateSlots (carryPrefix n xs ys cs cin)=6*n:=by
 induction n generalizing xs ys cs cin with
 | zero=>rfl
 | succ n ih=>
  cases xs with
  | nil=>simp at hx
  | cons a as=>
   cases ys with
   | nil=>simp at hy
   | cons b bs=>
    cases cs with
    | nil=>simp at hc
    | cons c cs=>
     rw[carryPrefix,Challenge.gateSlots_append,ih as bs cs c (by simp_all) (by simp_all) (by simp_all)]
     simp[majority,Challenge.gateSlots,Challenge.instructionSlots]
     omega

theorem consumedAddMany_counts (k:Nat) (src Z ys cs hs:List Wire) (cin q r t:Wire)
 (hsrc:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length) (len:hs.length=k):
 toffoliCount (consumedAddMany k src Z ys cs hs cin q r t)+k=toffoliCount (consumedAddTriple src Z ys cs cin q r t) ∧
 measurementCount (consumedAddMany k src Z ys cs hs cin q r t)=measurementCount (consumedAddTriple src Z ys cs cin q r t) ∧
 Challenge.gateSlots (consumedAddMany k src Z ys cs hs cin q r t)+4*k=Challenge.gateSlots (consumedAddTriple src Z ys cs cin q r t):=by
 have tx: k≤((src++Z.take 5).drop 7).length:=by simp only[List.length_drop,List.length_append];omega
 have ty: k≤(ys.drop 7).length:=by simp only[List.length_drop];omega
 have tc: k≤(cs.drop 7).length:=by simp only[List.length_drop];omega
 have pt:=carryPrefix_T k ((src++Z.take 5).drop 7) (ys.drop 7) (cs.drop 7) (lastCarry 7 cs cin) tx ty tc
 have ps:=carryPrefix_slots k ((src++Z.take 5).drop 7) (ys.drop 7) (cs.drop 7) (lastCarry 7 cs cin) tx ty tc
 have pm:=carryPrefix_measurements k ((src++Z.take 5).drop 7) (ys.drop 7) (cs.drop 7) (lastCarry 7 cs cin)
 have mc:=moveMany_counts ((cs.drop 7).take k) hs
 have banklen:((cs.drop 7).take k).length=k:=by simp only[List.length_take];omega
 rw[banklen,len,Nat.min_self]at mc
 rw[consumedAddTriple_splitN k src Z ys cs cin q r t hsrc hy hc]
 simp only[consumedAddMany,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,prefixAfter,pt,ps,pm,mc.1,mc.2.1,mc.2.2]
 constructor
 · omega
 · constructor
   · trivial
   · omega
#print axioms consumedAddMany_counts

#print axioms carryPrefix_T
#print axioms carryPrefix_slots
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem carryPrefix_off (n:Nat) (xs ys cs:List Wire) (cin w:Wire)
 (fresh:w∉cin::(xs++ys++cs)):
 w∉wires (carryPrefix n xs ys cs cin):=by
 induction n generalizing xs ys cs cin with
 | zero=>simp[carryPrefix,wires]
 | succ n ih=>
  cases xs with
  | nil=>simp[carryPrefix,wires]
  | cons a as=>
   cases ys with
   | nil=>simp[carryPrefix,wires]
   | cons b bs=>
    cases cs with
    | nil=>simp[carryPrefix,wires]
    | cons c cs=>
     have ft:w∉c::(as++bs++cs):=by simp_all
     have ht:=ih as bs cs c ft
     simp_all[carryPrefix,majority,wires,Instr.wires]
#print axioms carryPrefix_off
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem prefixAfter_overlay_bankValues (n k H:Nat) (xs ys cs old:List Wire) (vs:List Bool) (cin:Wire) (s u:State)
 (hx:n+k≤xs.length) (hy:n+k≤ys.length) (hc:n+k≤cs.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false)
 (source:regValue xs s.basis=H) (target:regValue ys s.basis=976*H/64)
 (eq:u=scatterState old vs (run (carryPrefix n xs ys cs cin) [] s))
 (off:∀w∈old,w∉wires (prefixAfter n k xs ys cs cin))
 (fresh:∀w∈(cs.drop n).take k,w∉old):
 ((cs.drop n).take k).map (run (prefixAfter n k xs ys cs cin) [] u).basis=bankValues n k H:=by
 have whole:run (prefixAfter n k xs ys cs cin) [] (run (carryPrefix n xs ys cs cin) [] s)=
  run (carryPrefix (n+k) xs ys cs cin) [] s:=by
  rw[prefix_compose n k xs ys cs cin (by omega) (by omega) (by omega),run_append,List.take_nil,List.drop_nil]
  rfl
 have mapEq:((cs.drop n).take k).map (run (prefixAfter n k xs ys cs cin) [] u).basis=
  ((cs.drop n).take k).map (run (carryPrefix (n+k) xs ys cs cin) [] s).basis:=by
  apply List.map_congr_left
  intro w hw
  rw[eq,run_scatter _ old vs _ [] off,scatter_outside old vs _ w (fresh w hw),whole]
 rw[mapEq]
 exact add_bankValues n k H xs ys cs cin s hx hy hc hn hz hi source target
#print axioms prefixAfter_overlay_bankValues
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem modify_many_inside (pre old new post:Program) (hs:List Wire) (vs:List Bool)
 (mc:measurementCount new=measurementCount old) (off:∀w∈hs,w∉wires post)
 (s:State) (m:List Bool)
 (changed:run new (m.drop (measurementCount pre)) (run pre m s)=
  scatterState hs vs (run old (m.drop (measurementCount pre)) (run pre m s))):
 run (pre++new++post) m s=scatterState hs vs (run (pre++old++post) m s):=by
 simp only[List.append_assoc,ZeroReadDevelop.run_cat,measurementCount_append,List.drop_drop,mc]
 rw[changed,run_scatter post hs vs _ _ off]
#print axioms modify_many_inside
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def buildMany (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire):Program:=
 buildPre acc Z bank cin src++cachedSubMany k (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) hs cin q r p++buildPost acc Z bank cin src
theorem buildMany_frame (k:Nat) (acc Z bank : List Wire) (cin : Wire) (src hs : List Wire) (q r p : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false) (hr:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (NarrowAcc.build8 acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (rq:r≠q)
    (hp:s.basis p=false) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (buildDual acc Z bank cin src q r))
    (hk:k≤33) (ndhs:hs.Nodup)
    (hu:∀u∈hs,s.basis u=false) (freshU:∀u∈hs,u∉cin::(src++acc++Z++bank))
    (offU:∀u∈hs,u∉wires (buildTriple acc Z bank cin src q r p)) :
    run (buildMany k acc Z bank cin src hs q r p) m s=
      scatterState hs (bankValues 7 k (regValue src s.basis)) (run (buildTriple acc Z bank cin src q r p) m s) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (buildPre acc Z bank cin src) (m.take (measurementCount (buildPre acc Z bank cin src))) s
  have preFrame:=buildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
    (m.take (measurementCount (buildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have len:(acc.take 139).length=139 := by simp [hacc]
  have lens:=Acc.fits_lengths (acc.take 139) Z bank cin 139 f len fit.toFitsLen
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have window:(Acc.ty (acc.take 139) f).length=133 := by simpa [f,Acc.earlyTerm] using lens.2.2
  have xv:regValue (Acc.tx Z 139 f) t.basis=H := by
    have zero:regValue (Z.take (139-f.shift-f.src.length)) t.basis=0 := (regValue_zero _ _).mpr (by
      intro w hw
      exact (same w (Or.inl (by simp [List.mem_of_mem_take hw]))).trans (hz w (List.mem_of_mem_take hw)))
    have srcv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
    change regValue (src++Z.take (139-6-src.length)) t.basis=H
    change regValue (Z.take (139-6-src.length)) t.basis=0 at zero
    rw [regValue_append,srcv,zero,Nat.mul_zero,Nat.add_zero]
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue (Acc.ty (acc.take 139) f) t.basis=1040*H/64 := by
    rw [Acc.ty,regValue_drop_div _ _ (by simp [f,Acc.earlyTerm,len]),pref.1]
    simp [f,Acc.earlyTerm]
  have clean:∀w∈Acc.tc bank 139 f,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=false := (preFrame.2.2 q qacc).trans hq
  have pieces:=off
  rw [build_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=false := (preFrame.2.2 r racc).trans hr
  have piecesR:=offR
  rw [build_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=false:=(preFrame.2.2 p pacc).trans hp
  have piecesP:=offP
  rw[buildDual]at piecesP
  simp only[wires_append,Finset.mem_union,not_or]at piecesP
  have ut (u:Wire) (h:u∈hs):t.basis u=false:=by
    have uacc:u∉acc:=by intro bad;exact freshU u h (by simp[bad])
    exact (preFrame.2.2 u uacc).trans (hu u h)
  have piecesU (u:Wire) (h:u∈hs):u∉wires (buildPre acc Z bank cin src) ∧
    u∉wires (cachedSubTriple (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p) ∧
    u∉wires (buildPost acc Z bank cin src):=by
    have free:=offU u h
    rw[buildTriple]at free
    simpa only[wires_append,Finset.mem_union,not_or,and_assoc,f]using free
  have freshcs (u:Wire) (h:u∈hs):u∉Acc.tc bank 139 f:=by
    intro bad
    exact freshU u h (by simp[List.mem_of_mem_take bad])
  have qc:q∉Acc.tc bank 139 f:=by intro bad;exact fresh (by simp[List.mem_of_mem_take bad])
  have rc:r∉Acc.tc bank 139 f:=by intro bad;exact freshR (by simp[List.mem_of_mem_take bad])
  have pc:p∉Acc.tc bank 139 f:=by intro bad;exact freshP (by simp[List.mem_of_mem_take bad])
  have count:=cachedSubMany_counts k (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) hs cin q r p lens.1 lens.2.1 (by omega)
  have changed:=cachedSubMany_known_frame k H (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) hs cin q r p
   lens.1 lens.2.1 (by omega) nd t (m.drop (measurementCount (buildPre acc Z bank cin src)))
   clean iv pieces.1.2 piecesR.1.2 rq piecesP.1.2 qc rc pc qt rt pt xv yv ndhs freshcs
   (fun u h=>(piecesU u h).2.1) ut
  have result:=modify_many_inside (buildPre acc Z bank cin src)
   (cachedSubTriple (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p)
   (cachedSubMany k (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) hs cin q r p)
   (buildPost acc Z bank cin src) hs (bankValues 7 k H) count.2.1
   (fun u h=>(piecesU u h).2.2) s m (by simpa only[t,run_take]using changed)
  simpa only[buildMany,buildTriple,f,H]using result
#print axioms buildMany_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem take_drop_disjoint (n:Nat) (cs:List Wire) (nd:cs.Nodup):
 ∀w∈cs.drop n,w∉cs.take n:=by
 induction n generalizing cs with
 | zero=>simp
 | succ n ih=>
  cases cs with
  | nil=>simp
  | cons c cs=>
   intro w hw
   have ht:w∈cs.drop n:=by simpa only[List.drop_succ_cons]using hw
   have mem:w∈cs:=List.mem_of_mem_drop ht
   have ne:w≠c:=by intro e;exact (List.nodup_cons.mp nd).1 (e ▸ mem)
   simp only[List.take_succ_cons,List.mem_cons,not_or]
   exact ⟨ne,ih cs (List.nodup_cons.mp nd).2 w ht⟩

theorem prefix_bank_zero (n k:Nat) (xs ys cs old:List Wire) (vs:List Bool) (cin:Wire) (s u:State)
 (hn:(cin::(xs++ys++cs)).Nodup) (hz:∀q∈cs,s.basis q=false)
 (eq:u=scatterState old vs (run (carryPrefix n xs ys cs cin) [] s))
 (fresh:∀w∈(cs.drop n).take k,w∉old):
 ∀w∈(cs.drop n).take k,u.basis w=false:=by
 intro w hw
 have mem:w∈cs.drop n:=List.mem_of_mem_take hw
 have ndc:cs.Nodup:=(List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
 have away:=take_drop_disjoint n cs ndc w mem
 rw[eq,scatter_outside old vs _ w (fresh w hw),carryPrefix_preserves n xs ys cs cin hn s [] w away]
 exact hz w (List.mem_of_mem_drop mem)
#print axioms take_drop_disjoint
#print axioms prefix_bank_zero
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem consumedAddMany_known_frame (k H:Nat) (src Z ys cs hs:List Wire) (cin q r t:Wire)
 (hsrc:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length)
 (hn:(cin::((src++Z.take 5)++ys++cs)).Nodup) (ndh:hs.Nodup) (len:hs.length=k)
 (fresh:∀h∈hs,h∉(cs.drop 7).take k)
 (offpre:∀h∈hs,h∉wires (consumePre3 src Z ys cs cin q r t))
 (offpost:∀h∈hs,h∉wires (inversePostN k src Z ys cs cin))
 (oldoff:∀w∈[q,r,t],w∉wires (prefixAfter 7 k (src++Z.take 5) ys cs cin))
 (oldfresh:∀w∈(cs.drop 7).take k,w∉[q,r,t])
 (s:State) (m:List Bool) (hz:∀w∈cs,s.basis w=false) (hi:s.basis cin=false)
 (source:regValue (src++Z.take 5) s.basis=H) (target:regValue ys s.basis=976*H/64)
 (preEq:run (consumePre3 src Z ys cs cin q r t) [] s=
  scatterState [q,r,t] [false,false,false] (run (carryPrefix 7 (src++Z.take 5) ys cs cin) [] s))
 (saved:hs.map s.basis=bankValues 7 k H):
 run (consumedAddMany k src Z ys cs hs cin q r t) m s=
 scatterState hs (List.replicate hs.length false) (run (consumedAddTriple src Z ys cs cin q r t) m s):=by
 let u:=run (consumePre3 src Z ys cs cin q r t) [] s
 have zero:∀w∈(cs.drop 7).take k,u.basis w=false:=
  prefix_bank_zero 7 k (src++Z.take 5) ys cs [q,r,t] [false,false,false] cin s u hn hz preEq oldfresh
 have values:=prefixAfter_overlay_bankValues 7 k H (src++Z.take 5) ys cs [q,r,t] [false,false,false] cin s u
  (by simp only[List.length_append];omega) (by omega) (by omega) hn hz hi source target preEq oldoff oldfresh
 have su:hs.map u.basis=bankValues 7 k H:=by
  rw[←saved]
  apply List.map_congr_left
  intro w hw
  exact run_preserves_outside (consumePre3 src Z ys cs cin q r t) [] s w (offpre w hw)
 exact consumedAddMany_frame k src Z ys cs hs cin q r t hsrc hy hc hn ndh len fresh offpost s m zero (su.trans values.symm)
#print axioms consumedAddMany_known_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem lastCarry_mem (n:Nat) (cs:List Wire) (cin:Wire):lastCarry n cs cin∈cin::cs:=by
 induction n generalizing cs cin with
 | zero=>simp[lastCarry]
 | succ n ih=>
  cases cs with
  | nil=>simp[lastCarry]
  | cons c cs=>
   exact List.mem_cons_of_mem cin (ih cs c)

theorem prefixAfter_off (n k:Nat) (xs ys cs:List Wire) (cin w:Wire)
 (fresh:w∉cin::(xs++ys++cs)):
 w∉wires (prefixAfter n k xs ys cs cin):=by
 apply carryPrefix_off
 intro bad
 rcases List.mem_cons.mp bad with eq|bad
 · have lc:=lastCarry_mem n cs cin
   rw[←eq]at lc
   rcases List.mem_cons.mp lc with rfl|lc
   · exact fresh (by simp)
   · exact fresh (by simp[lc])
 · simp only[List.mem_append]at bad
   rcases bad with (bad|bad)|bad
   · exact fresh (by simp[List.mem_of_mem_drop bad])
   · exact fresh (by simp[List.mem_of_mem_drop bad])
   · exact fresh (by simp[List.mem_of_mem_drop bad])
#print axioms lastCarry_mem
#print axioms prefixAfter_off
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open FourthASavedCarryDevelop ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def unbuildMany (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire):Program:=
 unbuildPre acc Z bank cin src++consumedAddMany k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p++unbuildPost acc Z bank cin src
theorem unbuildMany_frame (k:Nat) (acc Z bank : List Wire) (cin : Wire) (src hs : List Wire) (q r p : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis)) (savedR:s.basis r=cacheBit6 (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src)) (rq:r≠q)
    (savedP:s.basis p=cacheBit7 (regValue src s.basis)) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (unbuildDual acc Z bank cin src q r)) (pq:p≠q) (pr:p≠r)
    (hk:k≤33) (ndhs:hs.Nodup) (hostlen:hs.length=k)
    (savedU:hs.map s.basis=bankValues 7 k (regValue src s.basis))
    (freshU:∀u∈hs,u∉cin::(src++acc++Z++bank))
    (offU:∀u∈hs,u∉wires (unbuildTriple acc Z bank cin src q r p)) :
    run (unbuildMany k acc Z bank cin src hs q r p) m s=
      scatterState hs (List.replicate hs.length false) (run (unbuildTriple acc Z bank cin src q r p) m s) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (unbuildPre acc Z bank cin src) (m.take (measurementCount (unbuildPre acc Z bank cin src))) s
  have preFrame:=unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
    (m.take (measurementCount (unbuildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have nd0:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd:(cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa only [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd0
  have bankLen:132≤bank.length := by
    have h:=hf6.bankLen
    norm_num [f,Acc.earlyTerm] at h
    omega
  have zlen:5≤Z.length := by
    have h:=hf6.zpad
    norm_num [f,Acc.earlyTerm,hsrc] at h
    omega
  have sv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue ((acc.take 139).drop 6) t.basis=976*H/64 := by
    rw [regValue_drop_div _ 6 (by simp [hacc]),pref.1]
    norm_num
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (same w (Or.inl (by simp [hw]))).trans (hz w hw)
  have clean:∀w∈bank.take 132,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=cacheBit H := (preFrame.2.2 q qacc).trans saved
  have qbank:q∉bank.take 132 := by intro bad;exact fresh (by simp [List.mem_of_mem_take bad])
  have pieces:=off
  rw [unbuild_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [hacc,hsrc]
  have hc:(bank.take 132).length+1=((acc.take 139).drop 6).length := by simp [hacc,Nat.min_eq_left bankLen]
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=cacheBit6 H := (preFrame.2.2 r racc).trans savedR
  have rbank:r∉bank.take 132 := by intro bad;exact freshR (by simp [List.mem_of_mem_take bad])
  have freshQ:q∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132 := by
    intro bad
    simp only [List.mem_append] at bad
    rcases bad with ((h|h)|h)|h
    · exact fresh (by simp [h])
    · exact fresh (by simp [List.mem_of_mem_take h])
    · exact fresh (by simp [List.mem_of_mem_take (List.mem_of_mem_drop h)])
    · exact fresh (by simp [List.mem_of_mem_take h])
  have piecesR:=offR
  rw [unbuild_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=cacheBit7 H:=(preFrame.2.2 p pacc).trans savedP
  have freshP':p∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132:=by
   intro bad
   simp only[List.mem_append]at bad
   rcases bad with ((h|h)|h)|h
   · exact freshP (by simp[h])
   · exact freshP (by simp[List.mem_of_mem_take h])
   · exact freshP (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
   · exact freshP (by simp[List.mem_of_mem_take h])
  have freshR':r∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132:=by
   intro bad
   simp only[List.mem_append]at bad
   rcases bad with ((h|h)|h)|h
   · exact freshR (by simp[h])
   · exact freshR (by simp[List.mem_of_mem_take h])
   · exact freshR (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
   · exact freshR (by simp[List.mem_of_mem_take h])
  have restrictFresh (w:Wire) (free:w∉cin::(src++acc++Z++bank)):
    w∉cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132):=by
    intro bad
    simp only[List.mem_cons,List.mem_append]at bad
    rcases bad with rfl|((h|h)|h)|h
    · exact free (by simp)
    · exact free (by simp[h])
    · exact free (by simp[List.mem_of_mem_take h])
    · exact free (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
    · exact free (by simp[List.mem_of_mem_take h])
  have preEq:run (consumePre3 src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) [] t=
    scatterState [q,r,p] [false,false,false]
      (run (carryPrefix 7 (src++Z.take 5) ((acc.take 139).drop 6) (bank.take 132) cin) [] t):=by
    exact source_prefix_consumed_eq7 src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p
     (by omega) zlen hy hc nd t zt clean iv H sv yv freshQ freshR' rq
     (by intro h;exact freshP' (by simp[h])) pq pr qt rt pt
  have svx:regValue (src++Z.take 5) t.basis=H:=by
    rw[regValue_append,sv,(regValue_zero _ _).mpr (fun w hw=>zt w (List.mem_of_mem_take hw))]
    simp
  have savedUt:hs.map t.basis=bankValues 7 k H:=by
    rw[show bankValues 7 k H=hs.map s.basis from savedU.symm]
    apply List.map_congr_left
    intro u hu
    exact preFrame.2.2 u (fun bad=>freshU u hu (by simp[bad]))
  have windowlen:((acc.take 139).drop 6).length=133:=by simp[hacc]
  have carrylen:(bank.take 132).length=132:=by simp[Nat.min_eq_left bankLen]
  have piecesU (u:Wire) (hu:u∈hs):u∉wires (unbuildPre acc Z bank cin src) ∧
    u∉wires (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) ∧
    u∉wires (unbuildPost acc Z bank cin src):=by
    have free:=offU u hu
    rw[unbuildTriple]at free
    simpa only[wires_append,Finset.mem_union,not_or,and_assoc]using free
  have freepieces (u:Wire) (hu:u∈hs):
    u∉wires (consumePre3 src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) ∧
    u∉wires (prefixAfter 7 k (src++Z.take 5) ((acc.take 139).drop 6) (bank.take 132) cin) ∧
    u∉wires (inversePostN k src Z ((acc.take 139).drop 6) (bank.take 132) cin):=by
    have free:=(piecesU u hu).2.1
    rw[consumedAddTriple_splitN k src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p (by omega) (by omega) (by omega)]at free
    simpa only[wires_append,Finset.mem_union,not_or,and_assoc]using free
  have oldoff:∀w∈[q,r,p],w∉wires (prefixAfter 7 k (src++Z.take 5) ((acc.take 139).drop 6) (bank.take 132) cin):=by
    intro w hw
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hw
    rcases hw with rfl|rfl|rfl
    · exact prefixAfter_off _ _ _ _ _ _ _ (restrictFresh _ fresh)
    · exact prefixAfter_off _ _ _ _ _ _ _ (restrictFresh _ freshR)
    · exact prefixAfter_off _ _ _ _ _ _ _ (restrictFresh _ freshP)
  have oldfresh:∀w∈((bank.take 132).drop 7).take k,w∉[q,r,p]:=by
    intro w hw bad
    have mem:w∈bank:=List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_mem_take hw))
    simp only[List.mem_cons,List.not_mem_nil,or_false]at bad
    rcases bad with rfl|rfl|rfl
    · exact fresh (by simp[mem])
    · exact freshR (by simp[mem])
    · exact freshP (by simp[mem])
  have freebank:∀u∈hs,u∉((bank.take 132).drop 7).take k:=by
    intro u hu bad
    exact freshU u hu (by simp[List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_mem_take bad))])
  have count:=consumedAddMany_counts k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
   (by omega) (by omega) (by omega) hostlen
  have changed:=consumedAddMany_known_frame k H src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
   (by omega) (by omega) (by omega) nd ndhs hostlen freebank
   (fun u hu=>(freepieces u hu).1) (fun u hu=>(freepieces u hu).2.2) oldoff oldfresh
   t (m.drop (measurementCount (unbuildPre acc Z bank cin src))) clean iv svx yv preEq savedUt
  have result:=modify_many_inside (unbuildPre acc Z bank cin src)
   (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p)
   (consumedAddMany k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p) (unbuildPost acc Z bank cin src)
   hs (List.replicate hs.length false) count.2.1 (fun u hu=>(piecesU u hu).2.2) s m
   (by simpa only[t,run_take]using changed)
  simpa only[unbuildMany,unbuildTriple]using result
#print axioms unbuildMany_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem state_eq (s t:State) (hp:s.phase=t.phase) (hb:s.basis=t.basis):s=t:=by
 cases s
 cases t
 cases hp
 cases hb
 rfl

theorem scatter_zero_mem (hs:List Wire) (s:State) (nd:hs.Nodup) (w:Wire) (hw:w∈hs):
 (scatterState hs (List.replicate hs.length false) s).basis w=false:=by
 induction hs generalizing s with
 | nil=>simp at hw
 | cons h hs ih=>
  simp only[List.length_cons,List.replicate_succ,scatterState]
  rcases List.mem_cons.mp hw with rfl|hw
  · rw[scatter_outside hs _ _ _ (List.nodup_cons.mp nd).1]
    simp[setWire,writeBit]
  · exact ih (setWire s h false) (List.nodup_cons.mp nd).2 hw

theorem scatter_clear_overlay (hs:List Wire) (vs:List Bool) (s:State)
 (nd:hs.Nodup) (hz:∀w∈hs,s.basis w=false):
 scatterState hs (List.replicate hs.length false) (scatterState hs vs s)=s:=by
 apply state_eq
 · rw[scatter_phase,scatter_phase]
 · funext w
   by_cases hw:w∈hs
   · rw[scatter_zero_mem hs _ nd w hw,hz w hw]
   · rw[scatter_outside hs _ _ w hw,scatter_outside hs _ s w hw]
#print axioms scatter_zero_mem
#print axioms scatter_clear_overlay
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem cached_pair_many_eq (F newF M I newI:Program) (hs:List Wire) (vs:List Bool)
 (sameM:measurementCount newF=measurementCount F)
 (offF:∀w∈hs,w∉wires F) (offM:∀w∈hs,w∉wires M) (offI:∀w∈hs,w∉wires I)
 (nd:hs.Nodup) (s:State) (tape:List Bool) (zero:∀w∈hs,s.basis w=false)
 (forward:run newF (tape.take (measurementCount F)) s=
  scatterState hs vs (run F (tape.take (measurementCount F)) s))
 (inverse:run newI (tape.drop (measurementCount F+measurementCount M)) (scatterState hs vs (middleState F M s tape))=
  scatterState hs (List.replicate hs.length false)
   (run I (tape.drop (measurementCount F+measurementCount M)) (scatterState hs vs (middleState F M s tape)))):
 run (newF++M++newI) tape s=run (F++M++I) tape s:=by
 let last:=run I (tape.drop (measurementCount F+measurementCount M)) (middleState F M s tape)
 have lastZero:∀w∈hs,last.basis w=false:=by
  intro w hw
  dsimp only[last,middleState]
  rw[run_preserves_outside I _ _ w (offI w hw),run_preserves_outside M _ _ w (offM w hw),
   run_preserves_outside F _ _ w (offF w hw)]
  exact zero w hw
 simp only[run_three,sameM]
 rw[forward,run_scatter M hs vs _ _ offM]
 change run newI (tape.drop (measurementCount F+measurementCount M)) (scatterState hs vs (middleState F M s tape))=last
 rw[inverse,run_scatter I hs vs _ _ offI]
 exact scatter_clear_overlay hs vs last nd lastZero

#print axioms cached_pair_many_eq
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem buildMany_counts (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤33) (hh:hs.length=k):
 toffoliCount (buildMany k acc Z bank cin src hs q r p)=toffoliCount (buildTriple acc Z bank cin src q r p) ∧
 measurementCount (buildMany k acc Z bank cin src hs q r p)=measurementCount (buildTriple acc Z bank cin src q r p) ∧
 Challenge.gateSlots (buildMany k acc Z bank cin src hs q r p)=Challenge.gateSlots (buildTriple acc Z bank cin src q r p)+k:=by
 have len:=sub6_lengths acc Z bank src ha hl hz hb
 have count:=cachedSubMany_counts k (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) hs cin q r p
  (by omega) (by omega) (by omega)
 have banklen:(((Acc.tc bank 139 (Acc.earlyTerm src true 6)).drop 7).take k).length=k:=by
  simp only[List.length_take,List.length_drop,len.2.2]
  omega
 rw[banklen,hh,Nat.min_self]at count
 simp only[buildMany,buildTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

theorem unbuildMany_counts (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hl:src.length=128) (hb:132≤bank.length) (hk:k≤33) (hh:hs.length=k):
 toffoliCount (unbuildMany k acc Z bank cin src hs q r p)+k=toffoliCount (unbuildTriple acc Z bank cin src q r p) ∧
 measurementCount (unbuildMany k acc Z bank cin src hs q r p)=measurementCount (unbuildTriple acc Z bank cin src q r p) ∧
 Challenge.gateSlots (unbuildMany k acc Z bank cin src hs q r p)+4*k=Challenge.gateSlots (unbuildTriple acc Z bank cin src q r p):=by
 have count:=consumedAddMany_counts k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
  (by omega) (by simp only[List.length_drop,List.length_take];omega)
  (by simp only[List.length_take];omega) hh
 simp only[unbuildMany,unbuildTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩
#print axioms buildMany_counts
#print axioms unbuildMany_counts
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem WReady_scatter (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (H:Nat)
 (hs:List Wire) (vs:List Bool) (u:State)
 (fresh:∀h∈hs,h∉cin::(src++acc++Z++bank)) (h:WReady acc Z bank cin src H u):
 WReady acc Z bank cin src H (scatterState hs vs u):=by
 induction hs generalizing vs u with
 | nil=>exact h
 | cons q hs ih=>
  cases vs with
  | nil=>exact h
  | cons v vs=>
   exact ih vs (setWire u q v) (fun w hw=>fresh w (by simp[hw]))
    (WReady.setWire acc Z bank cin src H u q v (fresh q (by simp)) h)

theorem scatter_saved_map (hs:List Wire) (vs:List Bool) (u:State)
 (nd:hs.Nodup) (len:hs.length=vs.length):
 hs.map (scatterState hs vs u).basis=vs:=by
 induction hs generalizing vs u with
 | nil=>cases vs <;> simp_all[scatterState]
 | cons h hs ih=>
  cases vs with
  | nil=>simp at len
  | cons v vs=>
   have hd:(scatterState hs vs (setWire u h v)).basis h=v:=by
    rw[scatter_outside hs vs _ h (List.nodup_cons.mp nd).1]
    simp[setWire,writeBit]
   simpa only[scatterState,List.map_cons,hd]using
    congrArg (List.cons v) (ih vs (setWire u h v) (List.nodup_cons.mp nd).2 (by simpa using len))

#print axioms WReady_scatter
#print axioms scatter_saved_map
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem cached_wloop_many_eq (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle:Program)
 (hacc:acc.length=163) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false) (zeroU:∀u∈hs,s.basis u=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (hk:k≤33) (ndhs:hs.Nodup) (hostlen:hs.length=k)
 (freshU:∀u∈hs,u∉cin::(src++acc++Z++bank))
 (oldNe:∀u∈hs,u≠q ∧ u≠r ∧ u≠p)
 (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (offFU:∀u∈hs,u∉wires (buildTriple acc Z bank cin src q r p)) (offMU:∀u∈hs,u∉wires middle)
 (offIU:∀u∈hs,u∉wires (unbuildTriple acc Z bank cin src q r p))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (buildTriple acc Z bank cin src q r p) middle s m))
 (savedQ:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis q=cacheBit (regValue src s.basis))
 (savedR:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis r=cacheBit6 (regValue src s.basis))
 (savedP:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis p=cacheBit7 (regValue src s.basis)):
 run (buildMany k acc Z bank cin src hs q r p++middle++unbuildMany k acc Z bank cin src hs q r p) m s=
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s:=by
 let H:=regValue src s.basis
 have hf6:=hf _ (NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hsrc]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have tc:=buildMany_counts k acc Z bank cin src hs q r p hacc hsrc zl bl hk hostlen
 let t3:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 let tm:=scatterState hs (bankValues 7 k H) t3
 have ready:WReady acc Z bank cin src H tm:=WReady_scatter acc Z bank cin src H hs (bankValues 7 k H) t3 freshU good
 have qoff:q∉hs:=by intro h;exact (oldNe q h).1 rfl
 have roff:r∉hs:=by intro h;exact (oldNe r h).2.1 rfl
 have poff:p∉hs:=by intro h;exact (oldNe p h).2.2 rfl
 have saved1:tm.basis q=cacheBit (regValue src tm.basis):=by
  rw[ready.2.1]
  exact (scatter_outside hs (bankValues 7 k H) t3 q qoff).trans savedQ
 have saved2:tm.basis r=cacheBit6 (regValue src tm.basis):=by
  rw[ready.2.1]
  exact (scatter_outside hs (bankValues 7 k H) t3 r roff).trans savedR
 have saved3:tm.basis p=cacheBit7 (regValue src tm.basis):=by
  rw[ready.2.1]
  exact (scatter_outside hs (bankValues 7 k H) t3 p poff).trans savedP
 have savedMany:hs.map tm.basis=bankValues 7 k (regValue src tm.basis):=by
  rw[ready.2.1]
  exact scatter_saved_map hs (bankValues 7 k H) t3 ndhs (by simp[bankValues,hostlen])
 have av:regValue acc tm.basis=4294968272*regValue src tm.basis:=by rw[ready.2.1];exact ready.1
 have forward:=buildMany_frame k acc Z bank cin src hs q r p hacc hsrc hf s
  (m.take (measurementCount (buildTriple acc Z bank cin src q r p))) hz hb hi ha zero zeroR fresh offF freshR offFR rq zeroP freshP offFP hk ndhs zeroU freshU offFU
 have inverse:=unbuildMany_frame k acc Z bank cin src hs q r p hacc hsrc hf tm
  (m.drop (measurementCount (buildTriple acc Z bank cin src q r p)+measurementCount middle))
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 av saved1 saved2 fresh offI freshR offIR rq saved3 freshP offIP pq pr hk ndhs hostlen savedMany freshU offIU
 exact cached_pair_many_eq (buildTriple acc Z bank cin src q r p) (buildMany k acc Z bank cin src hs q r p) middle
  (unbuildTriple acc Z bank cin src q r p) (unbuildMany k acc Z bank cin src hs q r p) hs (bankValues 7 k H)
  tc.2.1 offFU offMU offIU ndhs s m zeroU forward inverse
#print axioms cached_wloop_many_eq
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open FourthASavedCarryDevelop InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem compiled_wloop_many_eq (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle newMiddle:Program)
 (hacc:acc.length=163) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (hk:k≤33) (ndhs:hs.Nodup) (hostlen:hs.length=k)
 (zeroU:∀u∈hs,s.basis u=false) (freshU:∀u∈hs,u∉cin::(src++acc++Z++bank))
 (oldNe:∀u∈hs,u≠q ∧ u≠r ∧ u≠p)
 (offFU:∀u∈hs,u∉wires (buildTriple acc Z bank cin src q r p))
 (offIU:∀u∈hs,u∉wires (unbuildTriple acc Z bank cin src q r p))
 (cert:ManyRewrites hs middle newMiddle)
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (NarrowAcc.build8 acc Z bank cin src) middle s m)):
 run (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p) m s=
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s:=by
 have ready:=triple_middle_ready acc Z bank cin src q r p middle hacc hsrc hf s m hz hb hi ha zero zeroR zeroP
  fresh freshR rq freshP pq pr offF offM offI offFR offMR offIR offFP offMP offIP good
 have middleEq:=cert.middle_eq hs middle newMiddle (buildTriple acc Z bank cin src q r p) s m zeroU offFU
 rw[←middleEq]at ready
 have newOff:∀u∈hs,u∉wires newMiddle:=cert.support hs middle newMiddle |>.2
 have eq:=cached_wloop_many_eq k acc Z bank cin src hs q r p newMiddle hacc hsrc hf s m hz hb hi ha zero zeroR zeroP zeroU
  fresh freshR rq freshP pq pr hk ndhs hostlen freshU oldNe offF offI offFR offIR offFP offIP offFU newOff offIU
  ready.1 ready.2.1 ready.2.2.1 ready.2.2.2
 have replaced:=cert.surround_eq hs middle newMiddle (buildTriple acc Z bank cin src q r p) (unbuildTriple acc Z bank cin src q r p) s m zeroU offFU
 exact eq.trans replaced
#print axioms compiled_wloop_many_eq
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem consumedAddTriple_carry_live (k:Nat) (src Z ys cs:List Wire) (cin q r t:Wire)
 (hsrc:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length)
 (w:Wire) (hw:w∈(cs.drop 7).take k):
 w∈wires (consumedAddTriple src Z ys cs cin q r t):=by
 have live:=carryPrefix_carry_mem k ((src++Z.take 5).drop 7) (ys.drop 7) (cs.drop 7) (lastCarry 7 cs cin)
  (by simp only[List.length_drop,List.length_append];omega) (by simp only[List.length_drop];omega)
  (by simp only[List.length_drop];omega) w hw
 rw[consumedAddTriple_splitN k src Z ys cs cin q r t hsrc hy hc,wires_append,wires_append]
 exact Finset.mem_union_left _ (Finset.mem_union_right _ live)

theorem consumedAddMany_support (k:Nat) (src Z ys cs hs:List Wire) (cin q r t:Wire)
 (hsrc:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length):
 wires (consumedAddMany k src Z ys cs hs cin q r t)⊆wires (consumedAddTriple src Z ys cs cin q r t)∪hs.toFinset:=by
 have split:=consumedAddTriple_splitN k src Z ys cs cin q r t hsrc hy hc
 intro w hw
 simp only[consumedAddMany,wires_append,Finset.mem_union]at hw
 rcases hw with (hp|hp)|hp
 · exact Finset.mem_union_left _ (by rw[split,wires_append,wires_append];exact Finset.mem_union_left _ (Finset.mem_union_left _ hp))
 · have h:=moveMany_support ((cs.drop 7).take k) hs hp
   rcases Finset.mem_union.mp h with h|h
   · exact Finset.mem_union_left _ (consumedAddTriple_carry_live k src Z ys cs cin q r t hsrc hy hc w (List.mem_toFinset.mp h))
   · exact Finset.mem_union_right _ h
 · exact Finset.mem_union_left _ (by rw[split,wires_append];exact Finset.mem_union_right _ hp)

theorem consumedAddMany_physical (k:Nat) (src Z ys cs hs:List Wire) (cin q r t:Wire)
 (hsrc:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length)
 (fresh:∀h∈hs,h∉cs)
 (old:∀i∈consumedAddTriple src Z ys cs cin q r t,Challenge.instructionValid i):
 ∀i∈consumedAddMany k src Z ys cs hs cin q r t,Challenge.instructionValid i:=by
 have split:=consumedAddTriple_splitN k src Z ys cs cin q r t hsrc hy hc
 intro i hi
 simp only[consumedAddMany,List.mem_append]at hi
 rcases hi with (hi|hi)|hi
 · apply old i
   rw[split]
   exact List.mem_append_left _ (List.mem_append_left _ hi)
 · exact moveMany_physical ((cs.drop 7).take k) hs
    (fun h hh bad=>fresh h hh (List.mem_of_mem_drop (List.mem_of_mem_take bad))) i hi
 · apply old i
   rw[split]
   exact List.mem_append_right _ hi
#print axioms consumedAddMany_support
#print axioms consumedAddMany_physical
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open FourthASavedCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def aFoldMany (k:Nat) (L:CuccaroStreamedSquareWideLayout) (g:Wire) (hs:List Wire) (middle:Program):Program:=
 buildMany k (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) hs L.core.sumCarry (eV L) (spare L)++middle++
 unbuildMany k (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) hs L.core.sumCarry (eV L) (spare L)
theorem aFoldMany_eq (k:Nat) (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g:Wire) (hs:List Wire) (newMiddle:Program) (hg:g∉L.wires)
    (hk:k≤33) (ndhs:hs.Nodup) (hostlen:hs.length=k)
    (work:∀u∈hs,u∈L.core.work)
    (freshU:∀u∈hs,u∉L.core.cin::(hiReg L++accReg L++accZ L++accBank L))
    (oldNe:∀u∈hs,u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L)
    (cert:ManyRewrites hs (aMiddle L g) newMiddle) (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false) (hV:base (eV L)=false) (hP:base (spare L)=false)
    (O : Nat) (hO:O<SquareReduction.p) (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    run (aFoldMany k L g hs newMiddle) m s=run (aFoldTriple L g) m s := by
  have clean:=L.squareFrame_clean hn base s.basis O hf hc
  have lens:=acc_lengths L hw
  have hz:∀q∈accZ L,s.basis q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact (regValue_zero _ _).mp clean.pad q h
    · exact (regValue_zero _ _).mp clean.work q (List.mem_of_mem_drop h)
  have hb:∀q∈accBank L,s.basis q=false := fun q hq =>
    (regValue_zero _ _).mp clean.pad q (List.mem_of_mem_take hq)
  have ha:regValue (accReg L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp clean.work q (accReg_work L q hq))
  have away:=ParkCarryDevelop.sumCarry_off_regs L hn
  have zero:s.basis L.core.sumCarry=false := (hf.2 _ away.1).trans hsum
  have off:=a_wloop_sumCarry_free L hw hn g hg
  have zeroR:s.basis (eV L)=false :=
    (hf.2 _ (eReg_away L hn _ (eK_mem L hw).2.2.1).1).trans hV
  have freshR:=eV_fresh_domain L hw hn
  have offR:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (eV L)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) freshR
  have zeroP:s.basis (spare L)=false:=
   (hf.2 _ (eReg_away L hn _ (spare_mem_eReg L hw)).1).trans hP
  have offP:=spare_off_dual L hw hn
  have zeroU:∀u∈hs,s.basis u=false:=by
   intro u hu
   exact (regValue_zero _ _).mp clean.work u (work u hu)
  have offU (u:Wire) (hu:u∈hs):u∉wires (buildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)) ∧
   u∉wires (unbuildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)):=
   fresh_off_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    L.core.sumCarry (eV L) (spare L) u lens.1 (hiReg_length L hw) (wTerms_fits L hw hn)
    (freshU u hu) (oldNe u hu).1 (oldNe u hu).2.1 (oldNe u hu).2.2
  have eq:=compiled_wloop_many_eq k (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) hs
   L.core.sumCarry (eV L) (spare L) (aMiddle L g) newMiddle
   lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) s m hz hb clean.cin ha zero zeroR zeroP
   (sumCarry_fresh_domain L hn) freshR (eV_ne_sumCarry L hw hn)
   (spare_fresh_domain L hw hn) (spare_ne_sumCarry L hw hn) (spare_ne_eV L hw hn)
   off.1 off.2.1 off.2.2 offR.1 (eV_off_amiddle L hw hn g hg) offR.2
   offP.1 (spare_off_amiddle L hw hn g hg) offP.2 hk ndhs hostlen zeroU freshU oldNe
   (fun u hu=>(offU u hu).1) (fun u hu=>(offU u hu).2) cert (a_middle_good L hw hn g hg base hc O hO s m hf)
  simpa only[aFoldMany,aFoldTriple]using eq

#print axioms aFoldMany_eq
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem valid_to_physical (i:Instr) (h:Challenge.instructionValid i):RecordedQuantum.PhysicalInstr (.gate i):=by
 cases i <;> simp_all[Challenge.instructionValid,RecordedQuantum.PhysicalInstr,ProperGate]

theorem cachedSubMany_gatePhysical (k:Nat) (xs ys cs hs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:7+k+2≤ys.length)
 (fresh:∀h∈hs,h∉cs) (old:GatePhysical (cachedSubTriple xs ys cs cin q r t)):
 GatePhysical (cachedSubMany k xs ys cs hs cin q r t):=by
 have split:=cachedSubTriple_splitN k xs ys cs cin q r t hx hc hy
 intro i hi
 simp only[cachedSubMany,List.mem_append]at hi
 rcases hi with (hi|hi)|hi
 · apply old i
   rw[split]
   exact List.mem_append_left _ (List.mem_append.mpr hi)
 · apply valid_to_physical
   exact copyMany_physical ((cs.drop 7).take k) hs
    (fun h hh bad=>fresh h hh (List.mem_of_mem_drop (List.mem_of_mem_take bad))) i hi
 · apply old i
   rw[split]
   exact List.mem_append_right _ hi

theorem consumedAddMany_gatePhysical (k:Nat) (src Z ys cs hs:List Wire) (cin q r t:Wire)
 (hsrc:k+9≤src.length) (hy:k+10≤ys.length) (hc:k+10≤cs.length)
 (fresh:∀h∈hs,h∉cs) (old:GatePhysical (consumedAddTriple src Z ys cs cin q r t)):
 GatePhysical (consumedAddMany k src Z ys cs hs cin q r t):=by
 have split:=consumedAddTriple_splitN k src Z ys cs cin q r t hsrc hy hc
 intro i hi
 simp only[consumedAddMany,List.mem_append]at hi
 rcases hi with (hi|hi)|hi
 · apply old i
   rw[split]
   exact List.mem_append_left _ (List.mem_append_left _ hi)
 · apply valid_to_physical
   exact moveMany_physical ((cs.drop 7).take k) hs
    (fun h hh bad=>fresh h hh (List.mem_of_mem_drop (List.mem_of_mem_take bad))) i hi
 · apply old i
   rw[split]
   exact List.mem_append_right _ hi
#print axioms cachedSubMany_gatePhysical
#print axioms consumedAddMany_gatePhysical
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem support_surround (pre old new post:Program) (hs:List Wire)
 (sub:wires new⊆wires old∪hs.toFinset):
 wires (pre++new++post)⊆wires (pre++old++post)∪hs.toFinset:=by
 intro w hw
 simp only[wires_append,Finset.mem_union]at hw ⊢
 rcases hw with (hw|hw)|hw
 · exact Or.inl (Or.inl (Or.inl hw))
 · rcases Finset.mem_union.mp (sub hw) with hw|hw
   · exact Or.inl (Or.inl (Or.inr hw))
   · exact Or.inr hw
 · exact Or.inl (Or.inr hw)

theorem buildMany_support (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤33):
 wires (buildMany k acc Z bank cin src hs q r p)⊆wires (buildTriple acc Z bank cin src q r p)∪hs.toFinset:=by
 have len:=sub6_lengths acc Z bank src ha hl hz hb
 exact support_surround _ _ _ _ hs (cachedSubMany_support k _ _ _ hs cin q r p (by omega) (by omega) (by omega))

theorem unbuildMany_support (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hl:src.length=128) (hb:132≤bank.length) (hk:k≤33):
 wires (unbuildMany k acc Z bank cin src hs q r p)⊆wires (unbuildTriple acc Z bank cin src q r p)∪hs.toFinset:=by
 exact support_surround _ _ _ _ hs (consumedAddMany_support k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
  (by omega) (by simp only[List.length_drop,List.length_take];omega) (by simp only[List.length_take];omega))

theorem buildMany_physical (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤33)
 (fresh:∀u∈hs,u∉bank) (physical:GatePhysical (buildTriple acc Z bank cin src q r p)):
 GatePhysical (buildMany k acc Z bank cin src hs q r p):=by
 have len:=sub6_lengths acc Z bank src ha hl hz hb
 rw[buildTriple,gatePhysical_append,gatePhysical_append]at physical
 have sub:=cachedSubMany_gatePhysical k (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) hs cin q r p
  (by omega) (by omega) (by omega) (fun u hu bad=>fresh u hu (List.mem_of_mem_take bad)) physical.1.2
 rw[buildMany,gatePhysical_append,gatePhysical_append]
 exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

theorem unbuildMany_physical (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hl:src.length=128) (hb:132≤bank.length) (hk:k≤33)
 (fresh:∀u∈hs,u∉bank) (physical:GatePhysical (unbuildTriple acc Z bank cin src q r p)):
 GatePhysical (unbuildMany k acc Z bank cin src hs q r p):=by
 rw[unbuildTriple,gatePhysical_append,gatePhysical_append]at physical
 have sub:=consumedAddMany_gatePhysical k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
  (by omega) (by simp only[List.length_drop,List.length_take];omega) (by simp only[List.length_take];omega)
  (fun u hu bad=>fresh u hu (List.mem_of_mem_take bad)) physical.1.2
 rw[unbuildMany,gatePhysical_append,gatePhysical_append]
 exact ⟨⟨physical.1.1,sub⟩,physical.2⟩
#print axioms buildMany_support
#print axioms unbuildMany_support
#print axioms buildMany_physical
#print axioms unbuildMany_physical
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem compiled_counts (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle newMiddle:Program)
 (ha:acc.length=163) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤33) (hostlen:hs.length=k)
 (cert:ManyRewrites hs middle newMiddle):
 toffoliCount (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p)+k≤
 toffoliCount (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) ∧
 measurementCount (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p)=
 measurementCount (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) ∧
 Challenge.gateSlots (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p)+3*k≤
 Challenge.gateSlots (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p):=by
 have b:=buildMany_counts k acc Z bank cin src hs q r p ha hl hz hb hk hostlen
 have i:=unbuildMany_counts k acc Z bank cin src hs q r p ha hl hb hk hostlen
 have t:=cert.toffoli hs middle newMiddle
 have m:=cert.measurements hs middle newMiddle
 have slots:=cert.slots hs middle newMiddle
 simp only[toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

theorem compiled_support (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle newMiddle:Program)
 (ha:acc.length=163) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤33)
 (cert:ManyRewrites hs middle newMiddle):
 wires (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p)⊆
 wires (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p)∪hs.toFinset:=by
 have b:=buildMany_support k acc Z bank cin src hs q r p ha hl hz hb hk
 have i:=unbuildMany_support k acc Z bank cin src hs q r p ha hl hb hk
 have mid:=(cert.support hs middle newMiddle).1
 intro w hw
 simp only[wires_append,Finset.mem_union]at hw ⊢
 rcases hw with (hw|hw)|hw
 · rcases Finset.mem_union.mp (b hw) with hw|hw
   · exact Or.inl (Or.inl (Or.inl hw))
   · exact Or.inr hw
 · exact Or.inl (Or.inl (Or.inr (mid hw)))
 · rcases Finset.mem_union.mp (i hw) with hw|hw
   · exact Or.inl (Or.inr hw)
   · exact Or.inr hw

theorem compiled_physical (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle newMiddle:Program)
 (ha:acc.length=163) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤33)
 (fresh:∀u∈hs,u∉bank) (cert:ManyRewrites hs middle newMiddle)
 (physical:GatePhysical (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p)):
 GatePhysical (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p):=by
 rw[gatePhysical_append,gatePhysical_append]at physical ⊢
 exact ⟨⟨buildMany_physical k acc Z bank cin src hs q r p ha hl hz hb hk fresh physical.1.1,
 cert.physical hs middle newMiddle physical.1.2⟩,
 unbuildMany_physical k acc Z bank cin src hs q r p ha hl hb hk fresh physical.2⟩
#print axioms compiled_counts
#print axioms compiled_support
#print axioms compiled_physical
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def loans (L:CuccaroStreamedSquareWideLayout):List Wire:=(L.core.work.drop 163).take 33

def BankReady (L:CuccaroStreamedSquareWideLayout) (g:Wire) (hs:List Wire):Prop:=
 hs.length=33 ∧ hs.Nodup ∧ ∀u∈hs,LoanReady L g u
instance (L:CuccaroStreamedSquareWideLayout) (g:Wire) (hs:List Wire):Decidable (BankReady L g hs):=by
 unfold BankReady
 infer_instance

def aFoldSelected (L:CuccaroStreamedSquareWideLayout) (g:Wire):Program:=
 let hs:=loans L
 if hr:BankReady L g hs then
  match compileManyChunked? hs (aMiddle L g) with
  | none=>aFoldTriple L g
  | some cm=>aFoldMany 33 L g hs cm.out
 else aFoldTriple L g

theorem aFoldSelected_eq (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false) (O:Nat) (hO:O<SquareReduction.p)
 (s:State) (m:List Bool) (hf:SquareFrame L.core.out base O s.basis):
 run (aFoldSelected L g) m s=run (aFoldTriple L g) m s:=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:compileManyChunked? (loans L) (aMiddle L g) with
   | none=>rfl
   | some cm=>
    exact aFoldMany_eq 33 L hw hn g (loans L) cm.out hg (by decide) hr.2.1 hr.1
     (fun u hu=>(hr.2.2 u hu).1) (fun u hu=>(hr.2.2 u hu).2.1)
     (fun u hu=>⟨(hr.2.2 u hu).2.2.1,(hr.2.2 u hu).2.2.2.1,(hr.2.2 u hu).2.2.2.2.1⟩)
     cm.proof base hc hsum hV hP O hO s m hf
 · rfl

#print axioms aFoldSelected_eq
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem aFoldMany_resources (k:Nat) (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire) (hs:List Wire) (middle:Program)
 (hk:k≤33) (hostlen:hs.length=k) (cert:ManyRewrites hs (aMiddle L g) middle):
 toffoliCount (aFoldMany k L g hs middle)+k≤toffoliCount (aFoldTriple L g) ∧
 measurementCount (aFoldMany k L g hs middle)=measurementCount (aFoldTriple L g) ∧
 Challenge.gateSlots (aFoldMany k L g hs middle)+3*k≤Challenge.gateSlots (aFoldTriple L g):=by
 have lens:=acc_lengths L hw
 exact compiled_counts k (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) hs L.core.sumCarry (eV L) (spare L)
  (aMiddle L g) middle lens.1 (hiReg_length L hw) (by omega) (by omega) hk hostlen cert

theorem aFoldSelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 toffoliCount (aFoldSelected L g)≤toffoliCount (aFoldTriple L g) ∧
 measurementCount (aFoldSelected L g)=measurementCount (aFoldTriple L g) ∧
 Challenge.gateSlots (aFoldSelected L g)≤Challenge.gateSlots (aFoldTriple L g):=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:compileManyChunked? (loans L) (aMiddle L g) with
   | none=>exact ⟨le_rfl,rfl,le_rfl⟩
   | some cm=>
    dsimp only
    have h:=aFoldMany_resources 33 L hw g (loans L) cm.out (by decide) hr.1 cm.proof
    exact ⟨by omega,h.2.1,by omega⟩
 · exact ⟨le_rfl,rfl,le_rfl⟩
#print axioms aFoldSelected_resources
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem aFoldSelected_frame (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false) (O:Nat) (hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (aFoldSelected L g)
  (SquareFrame L.core.out base (((if base g then OwnDiagAll12Square.cFlipK-4294968272*regValue (hiReg L) base
   else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hs
 rw[aFoldSelected_eq L hw hn g hg base hc hsum hV hP O hO s m hs]
 exact aFoldTriple_frame L hw hn g hg base hc hsum hV hP O hO s m hs

#print axioms aFoldSelected_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open ThirdSavedCarryDevelop Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def aBodySelected (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++aFoldSelected L c)
theorem aBodySelected_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBodySelected L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have vZero:base (eV L)=false := eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
  let P := M^2
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have v3 : AccView L base (aAcc L) := views (.inr (aAcc L)) (by simp [accAMix,aAcc])
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
  have hAeq : Acc.accVal base 0 (aAcc L).spec=4294968272*regValue (hiReg L) base := by
    rw [show (aAcc L).spec=earlyHTerms (L.core.product.drop 128) from rfl,accVal_earlyH]
    congr 1
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb,hP]
  have t3 := aFoldSelected_frame L hw hn c hcw base hc hzero vZero (spare_zero L hw base M hP) O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  let A := Acc.accVal base 0 (aAcc L).spec
  have hA : A<2^163 := Acc.accVal_lt base 163 (aAcc L).spec 0 (by norm_num) v3.specValid
  have hsum := (accA_mixSum L hw base).trans (L.measuredA_sum hw base (M^2) hP hb)
  have n1 : mixNeg (.inl (rot128F L) : MixItem)=false := rfl
  have n2 : mixNeg (.inr (aAcc L) : MixItem)=false := rfl
  have n3 : mixNeg (.inl (negP L) : MixItem)=true := rfl
  have e : accAMix L=[.inl (rot128F L),.inr (aAcc L),.inl (negP L)] := rfl
  rw [e] at hsum
  simp only [mixSignedSum,mixSignedPayload,n1,n2,n3,Bool.false_eq_true,if_false,if_true,mixPayload,add_zero,
    pay1,pay2] at hsum
  change ((((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
    (((A : Nat) : ZMod SquareReduction.p)+-((P : Nat) : ZMod SquareReduction.p)))=
      ((P : Nat) : ZMod SquareReduction.p)*2^128-(P : ZMod SquareReduction.p) at hsum
  have bound : ((if base c then OwnDiagAll12Square.cFlipK-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))).symm
  simp only [measuredOrientationCast,if_true,Bool.false_eq_true,if_false]
  have c0 := measuredReflection_zmod O hO
  have c1 := measuredReflection_zmod O1 hO1
  have c2 := measuredReflection_zmod O2 hO2
  have k1 : (O1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    simp only [O1,ZMod.natCast_mod,Nat.cast_add,c0]
  have k2 : (O2 : ZMod SquareReduction.p)=(((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(O1 : ZMod SquareReduction.p)) := by
    rw [show O2=((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p from rfl,
      ZMod.natCast_mod,Nat.cast_add,c1]
  rw [ZMod.natCast_mod,Nat.cast_add,c2,k2,k1]
  cases hgv : base c
  · have M0 := hg hgv
    have P0 : P=0 := by show M^2=0; rw [M0]; norm_num
    have R0 : (((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)=0 := by rw [P0]; simp
    rw [R0,P0] at hsum
    simp only [Bool.false_eq_true,if_false]
    rw [R0,P0]
    have hM2 : ((M^2 : Nat) : ZMod SquareReduction.p)=0 := by rw [M0]; simp
    rw [hM2]
    simp at hsum ⊢
    linear_combination -hsum
  · simp only [if_true]
    have hAle : A≤OwnDiagAll12Square.cFlipK := by simp only [OwnDiagAll12Square.cFlipK]; omega
    have hoff : ((OwnDiagAll12Square.cFlipK-A : Nat) : ZMod SquareReduction.p)=(OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum

#print axioms aBodySelected_frame
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem aFoldSelected_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 wires (aFoldSelected L g)⊆wires (aFoldTriple L g)∪(loans L).toFinset:=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:compileManyChunked? (loans L) (aMiddle L g) with
   | none=>exact Finset.subset_union_left
   | some cm=>
    have lens:=acc_lengths L hw
    exact compiled_support 33 (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (eV L) (spare L)
     (aMiddle L g) cm.out lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide) cm.proof
 · exact Finset.subset_union_left

theorem aFoldSelected_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire)
 (physical:GatePhysical (aFoldTriple L g)):GatePhysical (aFoldSelected L g):=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:compileManyChunked? (loans L) (aMiddle L g) with
   | none=>exact physical
   | some cm=>
    have lens:=acc_lengths L hw
    have fresh:∀u∈loans L,u∉accBank L:=by
     intro u hu bad
     exact (hr.2.2 u hu).2.1 (by simp[bad])
    exact compiled_physical 33 (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (eV L) (spare L)
     (aMiddle L g) cm.out lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide) fresh cm.proof physical
 · exact physical

theorem aBodySelected_subset (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 wires (aBodySelected L g)⊆wires (aBodyTriple L g):=by
 have oldfold:wires (aFoldTriple L g)⊆wires (aBodyTriple L g):=by
  intro w hw
  simp only[aBodyTriple,wires_append,Finset.mem_union]
  exact Or.inr (Or.inr hw)
 have fold:wires (aFoldSelected L g)⊆wires (aBodyTriple L g):=by
  by_cases hr:BankReady L g (loans L)
  · intro w hwire
    rcases Finset.mem_union.mp (aFoldSelected_support L hw g hwire)with h|h
    · exact oldfold h
    · have member:w∈loans L:=List.mem_toFinset.mp h
      exact (FourthASavedCarryDevelop.hasWire_iff _ _).mp (hr.2.2 w member).2.2.2.2.2
  · simpa only[aFoldSelected,dif_neg hr]using oldfold
 intro w hw
 simp only[aBodySelected,wires_append,Finset.mem_union]at hw
 rcases hw with hw|(hw|hw)
 · simp only[aBodyTriple,wires_append,Finset.mem_union];exact Or.inl hw
 · simp only[aBodyTriple,wires_append,Finset.mem_union];exact Or.inr (Or.inl hw)
 · exact fold hw

theorem aBodySelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 toffoliCount (aBodySelected L g)≤2915 ∧ measurementCount (aBodySelected L g)=3077 ∧
 Challenge.gateSlots (aBodySelected L g)≤Challenge.gateSlots (aBodyTriple L g):=by
 have old:=aBodyTriple_counts L hw g
 have h:=aFoldSelected_resources L hw g
 simp only[aBodySelected,aBodyTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]at old ⊢
 exact ⟨by omega,by omega,by omega⟩

theorem aBodySelected_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire)
 (hn:(g::L.wires).Nodup):GatePhysical (aBodySelected L g):=by
 have old:=aBodyTriple_physical L hw g hn
 simp only[aBodyTriple,gatePhysical_append]at old
 have fold:=aFoldSelected_physical L hw g old.2.2
 simp only[aBodySelected,gatePhysical_append]
 exact ⟨old.1,old.2.1,fold⟩
#print axioms aBodySelected_subset
#print axioms aBodySelected_resources
#print axioms aBodySelected_physical
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ParkCarryDevelop
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def hostedASelected (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire):Program:=aBodySelected (hostLayout L rho) c

theorem hostedASelected_eq (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire)
 (h:rho L.core.sumCarry=L.core.sumCarry):hostedASelected L rho c=aBodySelected L c:=by
 rw[hostedASelected,host_eq L rho h]

theorem hostedASelected_subset (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 wires (hostedASelected L rho c)⊆wires (hostedATriple L rho c):=
 aBodySelected_subset (hostLayout L rho) (host_widths L hw rho) c

theorem hostedASelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 toffoliCount (hostedASelected L rho c)≤toffoliCount (hostedATriple L rho c) ∧
 measurementCount (hostedASelected L rho c)=measurementCount (hostedATriple L rho c) ∧
 Challenge.gateSlots (hostedASelected L rho c)≤Challenge.gateSlots (hostedATriple L rho c):=by
 have h:=aBodySelected_resources (hostLayout L rho) (host_widths L hw rho) c
 have o:=aBodyTriple_counts (hostLayout L rho) (host_widths L hw rho) c
 exact ⟨by simpa only[hostedASelected,hostedATriple,o.1]using h.1,
  by simp only[hostedASelected,hostedATriple,h.2.1,o.2],h.2.2⟩
#print axioms hostedASelected_subset
#print axioms hostedASelected_resources
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop
set_option linter.unusedSimpArgs false

theorem aBodySelected_refined (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 wires (aBodySelected L c)⊆insert (spare L) (wires (InverseCarryDevelop.aBodyDual L c)):=
 (aBodySelected_subset L hw c).trans (aBodyTriple_refined L hw c)

theorem aBodySelected_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) (c:Wire):
 wires (aBodySelected L c)⊆(c::L.wires).toFinset:=
 (aBodySelected_subset L hw c).trans (aBodyTriple_support L hw hn c)
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false
 theorem actual_ready:BankReady Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic
 (loans Baselines.layout.dialogStreamedSquareWide):=by decide +kernel
#print axioms actual_ready
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open InverseCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false
 theorem actual_compiled:
 (compileManyChunked? (loans Baselines.layout.dialogStreamedSquareWide)
  (aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)).isSome=true:=ParkAStagedProof.actual_compiled
#print axioms actual_compiled
end ManyACarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ManyACarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount

theorem gain_of_success (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire)
 (ready:BankReady L g (loans L)) (success:(compileManyChunked? (loans L) (aMiddle L g)).isSome=true):
 toffoliCount (aFoldSelected L g)+33≤toffoliCount (aFoldTriple L g):=by
 unfold aFoldSelected
 dsimp only
 rw[dif_pos ready]
 cases he:compileManyChunked? (loans L) (aMiddle L g) with
 | none=>simp[he]at success
 | some cm=>exact (aFoldMany_resources 33 L hw g (loans L) cm.out (by decide) ready.1 cm.proof).1

theorem actual_fold_gain:
 toffoliCount (aFoldSelected Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)+33≤
 toffoliCount (aFoldTriple Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic):=
 gain_of_success _ (ControlledPointLayout.dialogStreamedSquareWide_widths Baselines.layout Baselines.layout_widths) _ actual_ready actual_compiled

theorem body_gain (L:CuccaroStreamedSquareWideLayout) (g:Wire)
 (h:toffoliCount (aFoldSelected L g)+33≤toffoliCount (aFoldTriple L g)):
 toffoliCount (aBodySelected L g)+33≤toffoliCount (aBodyTriple L g):=by
 simp only[aBodySelected,aBodyTriple,toffoliCount_append]
 omega

theorem bound2882 (a b:Nat) (h:a+33≤b) (hb:b=2915):a≤2882:=by omega

theorem actual_body_T_le:
 toffoliCount (aBodySelected Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)≤2882:=
 bound2882 _ _ (body_gain _ _ actual_fold_gain)
  (aBodyTriple_counts _ (ControlledPointLayout.dialogStreamedSquareWide_widths Baselines.layout Baselines.layout_widths) _).1
#print axioms actual_fold_gain
#print axioms actual_body_T_le
end ManyACarryDevelop

end
