import ECDSAAdd.Submission.Entrant.MainPart04Base
import ECDSAAdd.Submission.Entrant.QTop

/-! Two retained W carries (A branch), from mpjunior92's 88826c53. -/


-- Two retained W carries: CarrySixArithmeticDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def word6 (a0 a1 a2 a3 a4 a5 : Bool) : Nat := 1*a0.toNat + 2*a1.toNat + 4*a2.toNat + 8*a3.toNat + 16*a4.toNat + 32*a5.toNat

def carry6 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) : Bool := carryBit a5 b5 (carryBit a4 b4 (carryBit a3 b3 (carryBit a2 b2 (carryBit a1 b1 (carryBit a0 b0 (false))))))

theorem carry6_value : ∀a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool,
 (carry6 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5).toNat=(word6 a0 a1 a2 a3 a4 a5+word6 b0 b1 b2 b3 b4 b5)/64 := by decide +kernel

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CarryPrefixSixDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem carryPrefix_six (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 c0 c1 c2 c3 c4 c5 cin : Wire) (as bs cs : List Wire)
 (hn:(cin::(([a0,a1,a2,a3,a4,a5]++as)++([b0,b1,b2,b3,b4,b5]++bs)++([c0,c1,c2,c3,c4,c5]++cs))).Nodup) (s : State) (m : List Bool)
 (hz:∀q∈[c0,c1,c2,c3,c4,c5],s.basis q=false) (hi:s.basis cin=false) :
 (run (carryPrefix 6 ([a0,a1,a2,a3,a4,a5]++as) ([b0,b1,b2,b3,b4,b5]++bs) ([c0,c1,c2,c3,c4,c5]++cs) cin) m s).basis c5=carry6 (s.basis a0) (s.basis a1) (s.basis a2) (s.basis a3) (s.basis a4) (s.basis a5) (s.basis b0) (s.basis b1) (s.basis b2) (s.basis b3) (s.basis b4) (s.basis b5) := by
  rw [carryPrefix_run 6 ([a0,a1,a2,a3,a4,a5]++as) ([b0,b1,b2,b3,b4,b5]++bs) ([c0,c1,c2,c3,c4,c5]++cs) cin hn s m]
  have hzc0:s.basis c0=false := hz c0 (by simp)
  have hzc1:s.basis c1=false := hz c1 (by simp)
  have hzc2:s.basis c2=false := hz c2 (by simp)
  have hzc3:s.basis c3=false := hz c3 (by simp)
  have hzc4:s.basis c4=false := hz c4 (by simp)
  have hzc5:s.basis c5=false := hz c5 (by simp)
  have small:[a0,a1,a2,a3,a4,a5,b0,b1,b2,b3,b4,b5,c0,c1,c2,c3,c4,c5,cin].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have h:=List.nodup_iff_count_le_one.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have getNe (i j : Nat) (hi:i<19) (hj:j<19) (hne:i≠j) :
    ([a0,a1,a2,a3,a4,a5,b0,b1,b2,b3,b4,b5,c0,c1,c2,c3,c4,c5,cin][i]'hi)≠([a0,a1,a2,a3,a4,a5,b0,b1,b2,b3,b4,b5,c0,c1,c2,c3,c4,c5,cin][j]'hj) := by
    intro e
    exact hne ((List.Nodup.getElem_inj_iff small).mp e)
  have ne0_12:a0≠c0 := getNe 0 12 (by decide) (by decide) (by decide)
  have ne0_13:a0≠c1 := getNe 0 13 (by decide) (by decide) (by decide)
  have ne0_14:a0≠c2 := getNe 0 14 (by decide) (by decide) (by decide)
  have ne0_15:a0≠c3 := getNe 0 15 (by decide) (by decide) (by decide)
  have ne0_16:a0≠c4 := getNe 0 16 (by decide) (by decide) (by decide)
  have ne0_17:a0≠c5 := getNe 0 17 (by decide) (by decide) (by decide)
  have ne1_12:a1≠c0 := getNe 1 12 (by decide) (by decide) (by decide)
  have ne1_13:a1≠c1 := getNe 1 13 (by decide) (by decide) (by decide)
  have ne1_14:a1≠c2 := getNe 1 14 (by decide) (by decide) (by decide)
  have ne1_15:a1≠c3 := getNe 1 15 (by decide) (by decide) (by decide)
  have ne1_16:a1≠c4 := getNe 1 16 (by decide) (by decide) (by decide)
  have ne1_17:a1≠c5 := getNe 1 17 (by decide) (by decide) (by decide)
  have ne2_12:a2≠c0 := getNe 2 12 (by decide) (by decide) (by decide)
  have ne2_13:a2≠c1 := getNe 2 13 (by decide) (by decide) (by decide)
  have ne2_14:a2≠c2 := getNe 2 14 (by decide) (by decide) (by decide)
  have ne2_15:a2≠c3 := getNe 2 15 (by decide) (by decide) (by decide)
  have ne2_16:a2≠c4 := getNe 2 16 (by decide) (by decide) (by decide)
  have ne2_17:a2≠c5 := getNe 2 17 (by decide) (by decide) (by decide)
  have ne3_12:a3≠c0 := getNe 3 12 (by decide) (by decide) (by decide)
  have ne3_13:a3≠c1 := getNe 3 13 (by decide) (by decide) (by decide)
  have ne3_14:a3≠c2 := getNe 3 14 (by decide) (by decide) (by decide)
  have ne3_15:a3≠c3 := getNe 3 15 (by decide) (by decide) (by decide)
  have ne3_16:a3≠c4 := getNe 3 16 (by decide) (by decide) (by decide)
  have ne3_17:a3≠c5 := getNe 3 17 (by decide) (by decide) (by decide)
  have ne4_12:a4≠c0 := getNe 4 12 (by decide) (by decide) (by decide)
  have ne4_13:a4≠c1 := getNe 4 13 (by decide) (by decide) (by decide)
  have ne4_14:a4≠c2 := getNe 4 14 (by decide) (by decide) (by decide)
  have ne4_15:a4≠c3 := getNe 4 15 (by decide) (by decide) (by decide)
  have ne4_16:a4≠c4 := getNe 4 16 (by decide) (by decide) (by decide)
  have ne4_17:a4≠c5 := getNe 4 17 (by decide) (by decide) (by decide)
  have ne5_12:a5≠c0 := getNe 5 12 (by decide) (by decide) (by decide)
  have ne5_13:a5≠c1 := getNe 5 13 (by decide) (by decide) (by decide)
  have ne5_14:a5≠c2 := getNe 5 14 (by decide) (by decide) (by decide)
  have ne5_15:a5≠c3 := getNe 5 15 (by decide) (by decide) (by decide)
  have ne5_16:a5≠c4 := getNe 5 16 (by decide) (by decide) (by decide)
  have ne5_17:a5≠c5 := getNe 5 17 (by decide) (by decide) (by decide)
  have ne6_12:b0≠c0 := getNe 6 12 (by decide) (by decide) (by decide)
  have ne6_13:b0≠c1 := getNe 6 13 (by decide) (by decide) (by decide)
  have ne6_14:b0≠c2 := getNe 6 14 (by decide) (by decide) (by decide)
  have ne6_15:b0≠c3 := getNe 6 15 (by decide) (by decide) (by decide)
  have ne6_16:b0≠c4 := getNe 6 16 (by decide) (by decide) (by decide)
  have ne6_17:b0≠c5 := getNe 6 17 (by decide) (by decide) (by decide)
  have ne7_12:b1≠c0 := getNe 7 12 (by decide) (by decide) (by decide)
  have ne7_13:b1≠c1 := getNe 7 13 (by decide) (by decide) (by decide)
  have ne7_14:b1≠c2 := getNe 7 14 (by decide) (by decide) (by decide)
  have ne7_15:b1≠c3 := getNe 7 15 (by decide) (by decide) (by decide)
  have ne7_16:b1≠c4 := getNe 7 16 (by decide) (by decide) (by decide)
  have ne7_17:b1≠c5 := getNe 7 17 (by decide) (by decide) (by decide)
  have ne8_12:b2≠c0 := getNe 8 12 (by decide) (by decide) (by decide)
  have ne8_13:b2≠c1 := getNe 8 13 (by decide) (by decide) (by decide)
  have ne8_14:b2≠c2 := getNe 8 14 (by decide) (by decide) (by decide)
  have ne8_15:b2≠c3 := getNe 8 15 (by decide) (by decide) (by decide)
  have ne8_16:b2≠c4 := getNe 8 16 (by decide) (by decide) (by decide)
  have ne8_17:b2≠c5 := getNe 8 17 (by decide) (by decide) (by decide)
  have ne9_12:b3≠c0 := getNe 9 12 (by decide) (by decide) (by decide)
  have ne9_13:b3≠c1 := getNe 9 13 (by decide) (by decide) (by decide)
  have ne9_14:b3≠c2 := getNe 9 14 (by decide) (by decide) (by decide)
  have ne9_15:b3≠c3 := getNe 9 15 (by decide) (by decide) (by decide)
  have ne9_16:b3≠c4 := getNe 9 16 (by decide) (by decide) (by decide)
  have ne9_17:b3≠c5 := getNe 9 17 (by decide) (by decide) (by decide)
  have ne10_12:b4≠c0 := getNe 10 12 (by decide) (by decide) (by decide)
  have ne10_13:b4≠c1 := getNe 10 13 (by decide) (by decide) (by decide)
  have ne10_14:b4≠c2 := getNe 10 14 (by decide) (by decide) (by decide)
  have ne10_15:b4≠c3 := getNe 10 15 (by decide) (by decide) (by decide)
  have ne10_16:b4≠c4 := getNe 10 16 (by decide) (by decide) (by decide)
  have ne10_17:b4≠c5 := getNe 10 17 (by decide) (by decide) (by decide)
  have ne11_12:b5≠c0 := getNe 11 12 (by decide) (by decide) (by decide)
  have ne11_13:b5≠c1 := getNe 11 13 (by decide) (by decide) (by decide)
  have ne11_14:b5≠c2 := getNe 11 14 (by decide) (by decide) (by decide)
  have ne11_15:b5≠c3 := getNe 11 15 (by decide) (by decide) (by decide)
  have ne11_16:b5≠c4 := getNe 11 16 (by decide) (by decide) (by decide)
  have ne11_17:b5≠c5 := getNe 11 17 (by decide) (by decide) (by decide)
  have ne12_13:c0≠c1 := getNe 12 13 (by decide) (by decide) (by decide)
  have ne12_14:c0≠c2 := getNe 12 14 (by decide) (by decide) (by decide)
  have ne12_15:c0≠c3 := getNe 12 15 (by decide) (by decide) (by decide)
  have ne12_16:c0≠c4 := getNe 12 16 (by decide) (by decide) (by decide)
  have ne12_17:c0≠c5 := getNe 12 17 (by decide) (by decide) (by decide)
  have ne13_12:c1≠c0 := getNe 13 12 (by decide) (by decide) (by decide)
  have ne13_14:c1≠c2 := getNe 13 14 (by decide) (by decide) (by decide)
  have ne13_15:c1≠c3 := getNe 13 15 (by decide) (by decide) (by decide)
  have ne13_16:c1≠c4 := getNe 13 16 (by decide) (by decide) (by decide)
  have ne13_17:c1≠c5 := getNe 13 17 (by decide) (by decide) (by decide)
  have ne14_12:c2≠c0 := getNe 14 12 (by decide) (by decide) (by decide)
  have ne14_13:c2≠c1 := getNe 14 13 (by decide) (by decide) (by decide)
  have ne14_15:c2≠c3 := getNe 14 15 (by decide) (by decide) (by decide)
  have ne14_16:c2≠c4 := getNe 14 16 (by decide) (by decide) (by decide)
  have ne14_17:c2≠c5 := getNe 14 17 (by decide) (by decide) (by decide)
  have ne15_12:c3≠c0 := getNe 15 12 (by decide) (by decide) (by decide)
  have ne15_13:c3≠c1 := getNe 15 13 (by decide) (by decide) (by decide)
  have ne15_14:c3≠c2 := getNe 15 14 (by decide) (by decide) (by decide)
  have ne15_16:c3≠c4 := getNe 15 16 (by decide) (by decide) (by decide)
  have ne15_17:c3≠c5 := getNe 15 17 (by decide) (by decide) (by decide)
  have ne16_12:c4≠c0 := getNe 16 12 (by decide) (by decide) (by decide)
  have ne16_13:c4≠c1 := getNe 16 13 (by decide) (by decide) (by decide)
  have ne16_14:c4≠c2 := getNe 16 14 (by decide) (by decide) (by decide)
  have ne16_15:c4≠c3 := getNe 16 15 (by decide) (by decide) (by decide)
  have ne16_17:c4≠c5 := getNe 16 17 (by decide) (by decide) (by decide)
  have ne17_12:c5≠c0 := getNe 17 12 (by decide) (by decide) (by decide)
  have ne17_13:c5≠c1 := getNe 17 13 (by decide) (by decide) (by decide)
  have ne17_14:c5≠c2 := getNe 17 14 (by decide) (by decide) (by decide)
  have ne17_15:c5≠c3 := getNe 17 15 (by decide) (by decide) (by decide)
  have ne17_16:c5≠c4 := getNe 17 16 (by decide) (by decide) (by decide)
  clear hn small getNe hz
  simp_all [prefixState,writeBit,Function.update,carry6]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CarryPrefixSixValueDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem shape6 (xs : List Wire) (h:6≤xs.length) :
    ∃a b c d e f tail,xs=a::b::c::d::e::f::tail := by
  obtain ⟨a,b,c,d,e,tail,rfl⟩:=shape5 xs (by omega)
  cases tail with
  | nil => simp at h
  | cons f tail => exact ⟨a,b,c,d,e,f,tail,rfl⟩

theorem carryPrefix_value6 (xs ys cs : List Wire) (cin : Wire)
    (hx:6≤xs.length) (hy:6≤ys.length) (hc:6≤cs.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State) (m : List Bool)
    (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false) :
    ((run (carryPrefix 6 xs ys cs cin) m s).basis (cs.getD 5 0)).toNat=
      (regValue (xs.take 6) s.basis+regValue (ys.take 6) s.basis)/64 := by
  obtain ⟨a0,a1,a2,a3,a4,a5,as,rfl⟩:=shape6 xs hx
  obtain ⟨b0,b1,b2,b3,b4,b5,bs,rfl⟩:=shape6 ys hy
  obtain ⟨c0,c1,c2,c3,c4,c5,cs,rfl⟩:=shape6 cs hc
  have zeros:∀q∈[c0,c1,c2,c3,c4,c5],s.basis q=false := by
    intro q hq
    apply hz q
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have v:=congrArg Bool.toNat (carryPrefix_six a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 c0 c1 c2 c3 c4 c5 cin as bs cs hn s m zeros hi)
  rw [carry6_value] at v
  simpa [regValue,word6,Bool.toNat,Bool.cond_eq_ite,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using v

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedSubSixValueDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def subPre6 (xs ys cs : List Wire) (cin : Wire) : Program :=
  notRegister ys++carryPrefix 6 xs ys cs cin

theorem subPre6_value6 (xs ys cs : List Wire) (cin : Wire)
    (hx:6≤xs.length) (hy:6≤ys.length) (hc:6≤cs.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State)
    (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false) :
    ((run (subPre6 xs ys cs cin) [] s).basis (cs.getD 5 0)).toNat=
      (regValue (xs.take 6) s.basis+(63-regValue (ys.take 6) s.basis))/64 := by
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
  have xv:regValue (xs.take 6) t.basis=regValue (xs.take 6) s.basis := by
    apply regValue_congr
    intro q hq
    change (run (notRegister ys) [] s).basis q=s.basis q
    rw [nr]
    simp [xAway q (List.mem_of_mem_take hq)]
  have yv:regValue (ys.take 6) t.basis=63-regValue (ys.take 6) s.basis := by
    have e:regValue (ys.take 6) t.basis=regValue (ys.take 6) (fun q=>!s.basis q) := by
      apply regValue_congr
      intro q hq
      change (run (notRegister ys) [] s).basis q= !s.basis q
      rw [nr]
      simp [List.mem_of_mem_take hq]
    rw [e,regValue_complement]
    have len:(ys.take 6).length=6 := by simp [hy]
    rw [len]
    norm_num
  have val:=carryPrefix_value6 xs ys cs cin hx hy hc hn t [] zt it
  rw [xv,yv] at val
  have count:measurementCount (notRegister ys)=0 := (notRegister_counts ys).2
  simpa only [subPre6,run_append,count,List.take_zero,List.drop_zero] using val

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedSubSixSplitDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def sixthMajority (xs ys cs : List Wire) : Program :=
  majority (xs.getD 5 0) (ys.getD 5 0) (cs.getD 4 0) (cs.getD 5 0)

def subPost6 (xs ys cs : List Wire) (cin : Wire) : Program :=
  addKTSuffix true 6 xs ys cs cin++notRegister ys

theorem carryPrefix_split6 (xs ys cs : List Wire) (cin : Wire)
    (hx:6≤xs.length) (hy:6≤ys.length) (hc:6≤cs.length) :
    carryPrefix 6 xs ys cs cin=carryPrefix 5 xs ys cs cin++sixthMajority xs ys cs := by
  obtain ⟨a0,a1,a2,a3,a4,a5,as,rfl⟩:=shape6 xs hx
  obtain ⟨b0,b1,b2,b3,b4,b5,bs,rfl⟩:=shape6 ys hy
  obtain ⟨c0,c1,c2,c3,c4,c5,cs,rfl⟩:=shape6 cs hc
  simp [carryPrefix,sixthMajority,List.append_assoc]

theorem subPre6_split (xs ys cs : List Wire) (cin : Wire)
    (hx:6≤xs.length) (hy:6≤ys.length) (hc:6≤cs.length) :
    subPre6 xs ys cs cin=subPre xs ys cs cin++sixthMajority xs ys cs := by
  simp only [subPre6,subPre,carryPrefix_split6 xs ys cs cin hx hy hc,List.append_assoc]

theorem subPost_split6 (xs ys cs : List Wire) (cin : Wire)
    (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:8≤ys.length) :
    subPost xs ys cs cin=sixthMajority xs ys cs++subPost6 xs ys cs cin := by
  have a:=addKT_split true 5 xs ys cs cin hx hc (by omega)
  have b:=addKT_split true 6 xs ys cs cin hx hc hy
  rw [carryPrefix_split6 xs ys cs cin (by omega) (by omega) (by omega),List.append_assoc] at b
  have eq:carryPrefix 5 xs ys cs cin++addKTSuffix true 5 xs ys cs cin=
      carryPrefix 5 xs ys cs cin++(sixthMajority xs ys cs++addKTSuffix true 6 xs ys cs cin) := a.symm.trans b
  have tail:=List.append_cancel_left eq
  simp only [subPost,subPost6,tail,List.append_assoc]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: SecondCarryInsertDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def secondCopy (pre next post : Program) (c d q r : Wire) : Program :=
  insertCopy (insertCopy pre next c q) post d r

theorem firstCopy_split (pre next post : Program) (c q : Wire) :
    insertCopy pre (next++post) c q=insertCopy pre next c q++post := by
  simp only [insertCopy,List.append_assoc]

theorem secondCopy_correct (pre next post : Program) (c d q r : Wire)
    (hqpre:q∉wires pre) (hqnext:q∉wires next)
    (hrpre:r∉wires (insertCopy pre next c q)) (hrpost:r∉wires post)
    (mp:measurementCount pre=0) (mn:measurementCount next=0) (dq:d≠q)
    (s : State) (m : List Bool) (hq:s.basis q=false) (hr:s.basis r=false) :
    run (secondCopy pre next post c d q r) m s=
      ⟨(run (insertCopy pre (next++post) c q) m s).phase,
        writeBit (run (insertCopy pre (next++post) c q) m s).basis r ((run (pre++next) [] s).basis d)⟩ := by
  have first:=insertCopy_correct pre next c q hqpre hqnext s [] hq
  have count:measurementCount (insertCopy pre next c q)=0 := by
    simp only [insertCopy,measurementCount_append,mp,mn,measurementCount,List.foldl_cons,List.foldl_nil,Nat.zero_add]
  have result:=insertCopy_correct (insertCopy pre next c q) post d r hrpre hrpost s m hr
  rw [count,List.take_zero,first] at result
  simpa only [secondCopy,firstCopy_split,writeBit,Function.update_of_ne dq] using result

theorem secondCopy_counts (pre next post : Program) (c d q r : Wire) :
    toffoliCount (secondCopy pre next post c d q r)=toffoliCount (insertCopy pre (next++post) c q) ∧
    measurementCount (secondCopy pre next post c d q r)=measurementCount (insertCopy pre (next++post) c q) ∧
    Challenge.gateSlots (secondCopy pre next post c d q r)=Challenge.gateSlots (insertCopy pre (next++post) c q)+1 := by
  rw [firstCopy_split]
  exact insertCopy_counts (insertCopy pre next c q) post d r

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedSubDualDevelop2
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def cachedSubDual (xs ys cs : List Wire) (cin q r : Wire) : Program :=
  secondCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (subPost6 xs ys cs cin)
    (cs.getD 4 0) (cs.getD 5 0) q r

theorem cachedSub_first_split (xs ys cs : List Wire) (cin q : Wire)
    (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:8≤ys.length) :
    cachedSub xs ys cs cin q=insertCopy (subPre xs ys cs cin)
      (sixthMajority xs ys cs++subPost6 xs ys cs cin) (cs.getD 4 0) q := by
  simp only [cachedSub,subPost_split6 xs ys cs cin hx hc hy]

theorem cachedSubDual_counts (xs ys cs : List Wire) (cin q r : Wire)
    (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:8≤ys.length) :
    toffoliCount (cachedSubDual xs ys cs cin q r)=toffoliCount (cachedSub xs ys cs cin q) ∧
    measurementCount (cachedSubDual xs ys cs cin q r)=measurementCount (cachedSub xs ys cs cin q) ∧
    Challenge.gateSlots (cachedSubDual xs ys cs cin q r)=Challenge.gateSlots (cachedSub xs ys cs cin q)+1 := by
  rw [cachedSub_first_split xs ys cs cin q hx hc hy]
  exact secondCopy_counts _ _ _ _ _ _ _

theorem cachedSubDual_frame (xs ys cs : List Wire) (cin q r : Wire)
    (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:8≤ys.length)
    (qoff:q∉wires (CodexNarrowSub.program xs ys cs cin))
    (roff:r∉wires (CodexNarrowSub.program xs ys cs cin)) (rq:r≠q)
    (s : State) (m : List Bool) (hq:s.basis q=false) (hr:s.basis r=false) :
    run (cachedSubDual xs ys cs cin q r) m s=
      ⟨(run (cachedSub xs ys cs cin q) m s).phase,
        writeBit (run (cachedSub xs ys cs cin q) m s).basis r
          ((run (subPre6 xs ys cs cin) [] s).basis (cs.getD 5 0))⟩ := by
  have split:subPre xs ys cs cin++(sixthMajority xs ys cs++subPost6 xs ys cs cin)=
      CodexNarrowSub.program xs ys cs cin := by
    rw [←subPost_split6 xs ys cs cin hx hc hy]
    exact sub_split xs ys cs cin hx hc (by omega)
  have qo:=qoff
  rw [←split] at qo
  simp only [wires_append,Finset.mem_union,not_or] at qo
  have rfirst:r∉wires (cachedSub xs ys cs cin q) := by
    intro h
    have h:=Finset.mem_insert.mp (cachedSub_support xs ys cs cin q hx hc (by omega) h)
    exact h.elim rq roff
  rw [cachedSub_first_split xs ys cs cin q hx hc hy,firstCopy_split,wires_append,Finset.mem_union,not_or] at rfirst
  have dq:cs.getD 5 0≠q := by
    intro e
    apply qo.2.1
    simp [sixthMajority,majority,wires,Instr.wires,←e]
  have mp:measurementCount (subPre xs ys cs cin)=0 := by
    simp only [subPre,measurementCount_append,(notRegister_counts ys).2,carryPrefix_measurements,Nat.zero_add]
  have result:=secondCopy_correct (subPre xs ys cs cin) (sixthMajority xs ys cs) (subPost6 xs ys cs cin)
    (cs.getD 4 0) (cs.getD 5 0) q r qo.1 qo.2.1 rfirst.1 rfirst.2 mp rfl dq s m hq hr
  rw [←subPre6_split xs ys cs cin (by omega) (by omega) (by omega)] at result
  simpa only [cachedSubDual,←cachedSub_first_split xs ys cs cin q hx hc hy] using result

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: InverseCarrySixArithmeticDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop

theorem carry_return64 (X A : Nat) (hX:X<64) (hA:A<64) :
    (X+(A+64-X)%64)/64=(if A<X then 1 else 0) := by
  split_ifs <;> omega

theorem carry_return6_w64 (H : Nat) :
    (H%64+(976*H/64)%64)/64 =
      (if (1040*H/64)%64<H%64 then 1 else 0) := by
  have sum:H+976*H/64=1040*H/64 := by omega
  have back:((1040*H/64)%64+64-H%64)%64=(976*H/64)%64 := by omega
  rw [←back]
  exact carry_return64 _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

theorem sub_add_carry64 (X A : Nat) (hX:X<64) (hA:A<64) :
    (X+(63-A))/64=(X+(A+64-X)%64)/64 := by
  rw [carry_return64 X A hX hA]
  split_ifs <;> omega

theorem sub_add_carry6_w64 (H : Nat) :
    (H%64+(63-(1040*H/64)%64))/64=(H%64+(976*H/64)%64)/64 := by
  have sub:(H%64+(63-(1040*H/64)%64))/64=(if (1040*H/64)%64<H%64 then 1 else 0) := by
    split_ifs <;> omega
  exact sub.trans (carry_return6_w64 H).symm

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedSubDualKnownDevelop2
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def cacheBit6 (H : Nat) : Bool := decide ((1040*H/64)%64<H%64)

theorem cacheBit6_value (H : Nat) : (cacheBit6 H).toNat=(if (1040*H/64)%64<H%64 then 1 else 0) := by
  by_cases h:(1040*H/64)%64<H%64 <;> simp [cacheBit6,h]

theorem cachedSubDual_known_frame (xs ys cs : List Wire) (cin q r : Wire)
    (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:8≤ys.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State) (m : List Bool)
    (hz:∀w∈cs,s.basis w=false) (hi:s.basis cin=false)
    (hq:q∉wires (CodexNarrowSub.program xs ys cs cin))
    (hr:r∉wires (CodexNarrowSub.program xs ys cs cin)) (rq:r≠q)
    (hq0:s.basis q=false) (hr0:s.basis r=false)
    (H : Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64) :
    run (cachedSubDual xs ys cs cin q r) m s=
      ⟨(run (cachedSub xs ys cs cin q) m s).phase,
        writeBit (run (cachedSub xs ys cs cin q) m s).basis r (cacheBit6 H)⟩ := by
  have v:=subPre6_value6 xs ys cs cin (by omega) (by omega) (by omega) hn s hz hi
  rw [regValue_take_mod xs 6 (by omega) s.basis,regValue_take_mod ys 6 (by omega) s.basis,
    source,target] at v
  norm_num only [show 2^6=64 by decide] at v
  rw [sub_add_carry6_w64 H,carry_return6_w64 H] at v
  have bit:(run (subPre6 xs ys cs cin) [] s).basis (cs.getD 5 0)=cacheBit6 H :=
    bool_nat_injective _ _ (v.trans (cacheBit6_value H).symm)
  rw [cachedSubDual_frame xs ys cs cin q r hx hc hy hq hr rq s m hq0 hr0,bit]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedWBuildDualDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def buildDual (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire) : Program :=
  buildPre acc Z bank cin src++
    cachedSubDual (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6))
      (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r++buildPost acc Z bank cin src

theorem buildDual_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false) (hr:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (NarrowAcc.build8 acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (rq:r≠q) :
    run (buildDual acc Z bank cin src q r) m s=
      setWire (run (buildCached acc Z bank cin src q) m s) r (cacheBit6 (regValue src s.basis)) := by
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
  have count:=cachedSubDual_counts (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r lens.1 lens.2.1 (by omega)
  have changed:=cachedSubDual_known_frame (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r
    lens.1 lens.2.1 (by omega) nd t
    ((m.drop (measurementCount (buildPre acc Z bank cin src))).take
      (measurementCount (cachedSub (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q)))
    clean iv pieces.1.2 piecesR.1.2 rq qt rt H xv yv
  have result:=modify_inside (buildPre acc Z bank cin src)
    (cachedSub (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q)
    (cachedSubDual (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r)
    (buildPost acc Z bank cin src) r (cacheBit6 H) count.2.1 piecesR.2 s m changed
  simpa only [buildDual,buildCached,f] using result

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedAddDualSplitDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic SourceAddFourDevelop

theorem source_suffix_two_heads (src Z ys carry : List Wire) (cin : Wire)
    (hs:8≤src.length) (hy:ys.length=src.length+5) (hc:6≤carry.length) :
    (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin).take 12=
      majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0)++
      sixthMajority (src++Z.take 5) ys carry := by
  obtain ⟨a0,a1,a2,a3,a4,a5,as,rfl⟩:=shape6 src (by omega)
  cases as with
  | nil => simp only [List.length_cons,List.length_nil] at hs;omega
  | cons a6 as =>
    cases as with
    | nil => simp only [List.length_cons,List.length_nil] at hs;omega
    | cons a7 as =>
      obtain ⟨b0,b1,b2,b3,b4,b5,bs,rfl⟩:=shape6 ys (by simp only [List.length_cons] at hy;omega)
      cases bs with
      | nil => simp only [List.length_cons,List.length_nil] at hy;omega
      | cons b6 bs =>
        cases bs with
        | nil => simp only [List.length_cons,List.length_nil] at hy;omega
        | cons b7 bs =>
          obtain ⟨c0,c1,c2,c3,c4,c5,cs,rfl⟩:=shape6 carry hc
          change _=majority a4 b4 c3 c4++majority a5 b5 c4 c5
          simp [knownSuffix,desired,mappedRead,mappedAdd,mappedMajority,majority,List.append_assoc]

def addPost2 (src Z ys carry : List Wire) (cin : Wire) : Program :=
  (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin).drop 12

theorem addPost_split6 (src Z ys carry : List Wire) (cin : Wire)
    (hs:8≤src.length) (hy:ys.length=src.length+5) (hc:6≤carry.length) :
    addPost src Z ys carry cin=sixthMajority (src++Z.take 5) ys carry++addPost2 src Z ys carry cin := by
  let suffix:=knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin
  have split:=List.take_append_drop 12 suffix
  rw [source_suffix_two_heads src Z ys carry cin hs hy hc] at split
  have split':suffix=majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0)++
      (sixthMajority (src++Z.take 5) ys carry++suffix.drop 12) := by
    simpa only [List.append_assoc] using split.symm
  have eq:=congrArg (List.drop 6) split'
  simpa only [addPost,addPost2,majority,List.append_assoc,List.drop_succ_cons,List.drop_zero,List.nil_append] using eq

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CarrySixthGeometryDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem sixth_not_take5 (carry : List Wire) (hc:6≤carry.length) (hn:carry.Nodup) :
    carry.getD 5 0∉carry.take 5 := by
  obtain ⟨c0,c1,c2,c3,c4,c5,cs,rfl⟩:=shape6 carry hc
  change c5∉[c0,c1,c2,c3,c4]
  intro mem
  have pos:=List.count_pos_iff.mpr mem
  have bound:=List.nodup_iff_count_le_one.mp hn c5
  simp only [List.count_cons,List.count_nil] at pos bound
  simp only [beq_self_eq_true,if_true] at bound
  omega

theorem sixth_majority_nd (xs ys carry : List Wire) (cin : Wire)
    (hx:6≤xs.length) (hy:6≤ys.length) (hc:6≤carry.length)
    (hn:(cin::(xs++ys++carry)).Nodup) :
    [xs.getD 5 0,ys.getD 5 0,carry.getD 4 0,carry.getD 5 0].Nodup := by
  obtain ⟨a0,a1,a2,a3,a4,a5,as,rfl⟩:=shape6 xs hx
  obtain ⟨b0,b1,b2,b3,b4,b5,bs,rfl⟩:=shape6 ys hy
  obtain ⟨c0,c1,c2,c3,c4,c5,cs,rfl⟩:=shape6 carry hc
  change [a5,b5,c4,c5].Nodup
  apply List.nodup_iff_count_le_one.mpr
  intro w
  have h:=List.nodup_iff_count_le_one.mp hn w
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem carryPrefix_split5 (xs ys cs : List Wire) (cin : Wire)
    (hx:5≤xs.length) (hy:5≤ys.length) (hc:5≤cs.length) :
    carryPrefix 5 xs ys cs cin=carryPrefix 4 xs ys cs cin++
      majority (xs.getD 4 0) (ys.getD 4 0) (cs.getD 3 0) (cs.getD 4 0) := by
  obtain ⟨a0,a1,a2,a3,a4,as,rfl⟩:=shape5 xs hx
  obtain ⟨b0,b1,b2,b3,b4,bs,rfl⟩:=shape5 ys hy
  obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 cs hc
  simp [carryPrefix,List.append_assoc]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedAddFirstConsumePrefixDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic SourceAddFourDevelop

theorem source_prefix_consumed_eq5 (src Z ys carry : List Wire) (cin q : Wire)
    (hs:7≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
    (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
    (s : State) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
    (hcin:s.basis cin=false) (H : Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
    (fresh:q∉carry) (saved:s.basis q=cacheBit H) :
    run (addPre src Z ys carry cin++move q (carry.getD 4 0)) [] s=
      setWire (run (carryPrefix 5 (src++Z.take 5) ys carry cin) [] s) q false := by
  have enough:5≤carry.length := by omega
  have xlen:5≤(src++Z.take 5).length := by simp only [List.length_append];omega
  have nd:=fifth_majority_nd (src++Z.take 5) ys carry cin xlen (by omega) enough hn
  have member:carry.getD 4 0∈carry := by
    obtain ⟨c0,c1,c2,c3,c4,cs,rfl⟩:=shape5 carry enough
    simp
  have ne:q≠carry.getD 4 0 := by intro e;exact fresh (e.symm ▸ member)
  have ready:=source_prefix_consume_ready src Z ys carry cin q hs hzl hy hc hn s hz hclean hcin H hsrc hys fresh saved
  have eq4:=source_prefix_eq src Z ys carry cin hs hzl hy hc hn s [] hz hclean hcin H hsrc hys
  have step:=consume_eq_majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0)
    q nd ne (run (addPre src Z ys carry cin) [] s) [] ready.1 ready.2
  have eq5:run (carryPrefix 5 (src++Z.take 5) ys carry cin) [] s=
      run (majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0)) []
        (run (addPre src Z ys carry cin) [] s) := by
    rw [carryPrefix_split5 _ _ _ _ xlen (by omega) enough,run_append]
    simp only [List.take_nil,List.drop_nil]
    rw [show run (addPre src Z ys carry cin) [] s=run (carryPrefix 4 (src++Z.take 5) ys carry cin) [] s from eq4]
  simpa only [run_append,List.take_nil,List.drop_nil,eq5,setWire] using step

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CarryPrefixSixNextDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem carryPrefix_next_value6 (xs ys carry : List Wire) (cin : Wire)
    (hx:6≤xs.length) (hy:6≤ys.length) (hc:6≤carry.length)
    (hn:(cin::(xs++ys++carry)).Nodup) (s : State)
    (hz:∀q∈carry,s.basis q=false) (hi:s.basis cin=false) :
    (carryBit
      ((run (carryPrefix 5 xs ys carry cin) [] s).basis (xs.getD 5 0))
      ((run (carryPrefix 5 xs ys carry cin) [] s).basis (ys.getD 5 0))
      ((run (carryPrefix 5 xs ys carry cin) [] s).basis (carry.getD 4 0))).toNat=
      (regValue (xs.take 6) s.basis+regValue (ys.take 6) s.basis)/64 := by
  obtain ⟨a0,a1,a2,a3,a4,a5,as,rfl⟩:=shape6 xs hx
  obtain ⟨b0,b1,b2,b3,b4,b5,bs,rfl⟩:=shape6 ys hy
  obtain ⟨c0,c1,c2,c3,c4,c5,cs,rfl⟩:=shape6 carry hc
  let xs:=a0::a1::a2::a3::a4::a5::as
  let ys:=b0::b1::b2::b3::b4::b5::bs
  let carry:=c0::c1::c2::c3::c4::c5::cs
  let t:=run (carryPrefix 5 xs ys carry cin) [] s
  have nd4:[a5,b5,c4,c5].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have h:=List.nodup_iff_count_le_one.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ndcs:carry.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
  have off:c5∉carry.take 5 := by
    change c5∉[c0,c1,c2,c3,c4]
    intro mem
    have pos:=List.count_pos_iff.mpr mem
    have bound:=List.nodup_iff_count_le_one.mp ndcs c5
    simp only [carry,List.count_cons,List.count_nil] at pos bound
    simp only [beq_self_eq_true,if_true] at bound
    omega
  have clean:t.basis c5=false :=
    (carryPrefix_preserves 5 xs ys carry cin hn s [] c5 off).trans (hz c5 (by simp))
  have split:carryPrefix 6 xs ys carry cin=carryPrefix 5 xs ys carry cin++majority a5 b5 c4 c5 := by
    simp [xs,ys,carry,carryPrefix,List.append_assoc]
  have run6:run (carryPrefix 6 xs ys carry cin) [] s=run (majority a5 b5 c4 c5) [] t := by
    rw [split,run_append]
    simp only [List.take_nil,List.drop_nil,t]
  have v:=carryPrefix_value6 xs ys carry cin hx hy hc hn s [] hz hi
  rw [run6,majority_correct a5 b5 c4 c5 nd4 t [],clean] at v
  change (carryBit (t.basis a5) (t.basis b5) (t.basis c4)).toNat=_
  have get:carry.getD 5 0=c5 := rfl
  rw [get] at v
  simpa only [writeBit,Function.update_self,Bool.false_xor] using v

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedAddSecondReadyDevelop2
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic SourceAddFourDevelop Arithmetic.CuccaroStreamedSquareWideLayout

theorem source_second_consume_ready (src Z ys carry : List Wire) (cin q r : Wire)
    (hs:8≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
    (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
    (s : State) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
    (hcin:s.basis cin=false) (H : Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
    (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉carry) (rq:r≠q)
    (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H) :
    let t:=run (addPre src Z ys carry cin++move q (carry.getD 4 0)) [] s
    t.basis (carry.getD 5 0)=false ∧
    t.basis r=carryBit (t.basis ((src++Z.take 5).getD 5 0)) (t.basis (ys.getD 5 0)) (t.basis (carry.getD 4 0)) := by
  let xs:=src++Z.take 5
  let u:=run (carryPrefix 5 xs ys carry cin) [] s
  let t:=run (addPre src Z ys carry cin++move q (carry.getD 4 0)) [] s
  have freshC:q∉carry := by intro h;exact fresh (by simp [h])
  have eq:t=setWire u q false := source_prefix_consumed_eq5 src Z ys carry cin q (by omega) hzl hy hc hn s hz hclean hcin H hsrc hys freshC saved
  have xlen:6≤xs.length := by simp only [xs,List.length_append];omega
  have enough:6≤carry.length := by omega
  have member6 (ws : List Wire) (h:6≤ws.length) : ws.getD 5 0∈ws := by
    obtain ⟨a,b,c,d,e,f,as,rfl⟩:=shape6 ws h
    simp
  have member4:carry.getD 4 0∈carry := by
    obtain ⟨a,b,c,d,e,as,rfl⟩:=shape5 carry (by omega)
    simp
  have neX:xs.getD 5 0≠q := by
    intro e
    have member:q∈xs := e ▸ member6 xs xlen
    exact fresh (List.mem_append_left _ (List.mem_append_left _ member))
  have neY:ys.getD 5 0≠q := by
    intro e
    have member:q∈ys := e ▸ member6 ys (by omega)
    exact fresh (List.mem_append_left _ (List.mem_append_right _ member))
  have neC4:carry.getD 4 0≠q := by intro e;exact freshC (e ▸ member4)
  have neC5:carry.getD 5 0≠q := by intro e;exact freshC (e ▸ member6 carry enough)
  have outside (w : Wire) (ne:w≠q) : t.basis w=u.basis w := by
    rw [eq]
    simp only [setWire,writeBit,Function.update_of_ne ne]
  have ndcs:carry.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
  have clean:t.basis (carry.getD 5 0)=false := (outside _ neC5).trans
    ((carryPrefix_preserves 5 xs ys carry cin hn s [] _ (sixth_not_take5 carry enough ndcs)).trans (hclean _ (member6 carry enough)))
  have kept:t.basis r=cacheBit6 H := (outside r rq).trans
    ((carryPrefix_preserves 5 xs ys carry cin hn s [] r (fun h=>rfresh (List.mem_of_mem_take h))).trans savedR)
  have val:=carryPrefix_next_value6 xs ys carry cin xlen (by omega) enough hn s hclean hcin
  have xvalue:regValue xs s.basis=H := by
    have zv:regValue (Z.take 5) s.basis=0 := (regValue_zero _ _).mpr (fun w hw=>hz w (List.mem_of_mem_take hw))
    simp only [xs,regValue_append,zv,hsrc,Nat.mul_zero,Nat.add_zero]
  rw [regValue_take_mod xs 6 xlen s.basis,regValue_take_mod ys 6 (by omega) s.basis,xvalue,hys] at val
  norm_num only [show 2^6=64 by decide] at val
  rw [carry_return6_w64 H] at val
  have known:carryBit (u.basis (xs.getD 5 0)) (u.basis (ys.getD 5 0)) (u.basis (carry.getD 4 0))=cacheBit6 H :=
    bool_nat_injective _ _ (val.trans (cacheBit6_value H).symm)
  refine ⟨clean,?_⟩
  rw [outside _ neX,outside _ neY,outside _ neC4,known]
  exact kept

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: SecondCarryConsumeDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem secondConsume_correct (pre post : Program) (a b cin c q : Wire)
    (hn:[a,b,cin,c].Nodup) (ne:q≠c) (off:q∉wires post)
    (s : State) (m : List Bool)
    (clean:(run pre (m.take (measurementCount pre)) s).basis c=false)
    (ready:let t:=run pre (m.take (measurementCount pre)) s
      t.basis q=carryBit (t.basis a) (t.basis b) (t.basis cin)) :
    run (pre++move q c++post) m s=setWire (run (pre++majority a b cin c++post) m s) q false := by
  apply modify_inside pre (majority a b cin c) (move q c) post q false rfl off s m
  simp only [show measurementCount (majority a b cin c)=0 from rfl,List.take_zero]
  exact consume_eq_majority a b cin c q hn ne _ [] clean ready

theorem secondConsume_counts (pre post : Program) (a b cin c q : Wire) :
    toffoliCount (pre++move q c++post)+1=toffoliCount (pre++majority a b cin c++post) ∧
    measurementCount (pre++move q c++post)=measurementCount (pre++majority a b cin c++post) ∧
    Challenge.gateSlots (pre++move q c++post)+4=Challenge.gateSlots (pre++majority a b cin c++post) := by
  have count:=consume_counts a b cin c q
  simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedAddDualDevelop2
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic SourceAddFourDevelop

def consumedAddDual (src Z ys carry : List Wire) (cin q r : Wire) : Program :=
  (addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0)++addPost2 src Z ys carry cin

theorem consumedAdd_split6 (src Z ys carry : List Wire) (cin q : Wire)
    (hs:8≤src.length) (hy:ys.length=src.length+5) (hc:6≤carry.length) :
    consumedAdd src Z ys carry cin q=(addPre src Z ys carry cin++move q (carry.getD 4 0))++
      sixthMajority (src++Z.take 5) ys carry++addPost2 src Z ys carry cin := by
  simp only [consumedAdd,addPost_split6 src Z ys carry cin hs hy hc,List.append_assoc]

theorem consumedAddDual_counts (src Z ys carry : List Wire) (cin q r : Wire)
    (hs:8≤src.length) (hy:ys.length=src.length+5) (hc:6≤carry.length) :
    toffoliCount (consumedAddDual src Z ys carry cin q r)+1=toffoliCount (consumedAdd src Z ys carry cin q) ∧
    measurementCount (consumedAddDual src Z ys carry cin q r)=measurementCount (consumedAdd src Z ys carry cin q) ∧
    Challenge.gateSlots (consumedAddDual src Z ys carry cin q r)+4=Challenge.gateSlots (consumedAdd src Z ys carry cin q) := by
  rw [consumedAdd_split6 src Z ys carry cin q hs hy hc]
  exact secondConsume_counts _ _ _ _ _ _ _

theorem consumedAddDual_frame (src Z ys carry : List Wire) (cin q r : Wire)
    (hs:8≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
    (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
    (hcin:s.basis cin=false) (H : Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
    (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉carry) (rq:r≠q)
    (roff:r∉wires (SourceAddFourDevelop.program src Z ys carry cin))
    (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H) :
    run (consumedAddDual src Z ys carry cin q r) m s=
      setWire (run (consumedAdd src Z ys carry cin q) m s) r false := by
  have enough:6≤carry.length := by omega
  have xlen:6≤(src++Z.take 5).length := by simp only [List.length_append];omega
  have nd:=sixth_majority_nd (src++Z.take 5) ys carry cin xlen (by omega) enough hn
  have member:carry.getD 5 0∈carry := by
    obtain ⟨c0,c1,c2,c3,c4,c5,cs,rfl⟩:=shape6 carry enough
    simp
  have ne:r≠carry.getD 5 0 := by intro e;exact rfresh (e.symm ▸ member)
  have rf:r∉wires (consumedAdd src Z ys carry cin q) := by
    intro h
    have h:=Finset.mem_insert.mp (consumedAdd_support src Z ys carry cin q (by omega) hy (by omega) h)
    exact h.elim rq roff
  rw [consumedAdd_split6 src Z ys carry cin q hs hy enough] at rf
  simp only [wires_append,Finset.mem_union,not_or] at rf
  have ready:=source_second_consume_ready src Z ys carry cin q r hs hzl hy hc hn s hz hclean hcin H hsrc hys fresh rfresh rq saved savedR
  have preM:measurementCount (addPre src Z ys carry cin++move q (carry.getD 4 0))=0 := by
    have h:= (knownPrefix_counts (src.getD 0 0) (mappedRead (src++Z.take 5) false) (desired src) ys carry cin).2
    change measurementCount (addPre src Z ys carry cin)=0 at h
    simp only [measurementCount_append,h,show measurementCount (move q (carry.getD 4 0))=0 from rfl,Nat.zero_add]
  have result:=secondConsume_correct (addPre src Z ys carry cin++move q (carry.getD 4 0))
    (addPost2 src Z ys carry cin) ((src++Z.take 5).getD 5 0) (ys.getD 5 0) (carry.getD 4 0) (carry.getD 5 0) r
    nd ne rf.2 s m (by simpa only [preM,List.take_zero] using ready.1)
    (by simpa only [preM,List.take_zero] using ready.2)
  have split:=consumedAdd_split6 src Z ys carry cin q hs hy enough
  rw [sixthMajority] at split
  rw [←split] at result
  simpa only [consumedAddDual] using result

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedWUnbuildDualDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def unbuildDual (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire) : Program :=
  unbuildPre acc Z bank cin src++
    consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r++unbuildPost acc Z bank cin src

theorem unbuildDual_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis)) (savedR:s.basis r=cacheBit6 (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src)) (rq:r≠q) :
    run (unbuildDual acc Z bank cin src q r) m s=
      setWire (run (unbuildConsumed acc Z bank cin src q) m s) r false := by
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
  have count:=consumedAddDual_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r
    (by omega) hy (by simp [Nat.min_eq_left bankLen])
  have changed:=consumedAddDual_frame src Z ((acc.take 139).drop 6) (bank.take 132) cin q r
    (by omega) zlen hy hc nd t
    ((m.drop (measurementCount (unbuildPre acc Z bank cin src))).take
      (measurementCount (consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q)))
    zt clean iv H sv yv freshQ rbank rq piecesR.1.2 qt rt
  have result:=modify_inside (unbuildPre acc Z bank cin src)
    (consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q)
    (consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r) (unbuildPost acc Z bank cin src)
    r false count.2.1 piecesR.2 s m changed
  simpa only [unbuildDual,unbuildConsumed] using result

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedWDualCountsDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem buildDual_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    toffoliCount (buildDual acc Z bank cin src q r)=toffoliCount (buildCached acc Z bank cin src q) ∧
    measurementCount (buildDual acc Z bank cin src q r)=measurementCount (buildCached acc Z bank cin src q) ∧
    Challenge.gateSlots (buildDual acc Z bank cin src q r)=Challenge.gateSlots (buildCached acc Z bank cin src q)+1 := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have count:=cachedSubDual_counts (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r
    (by omega) (by omega) (by omega)
  simp only [buildDual,buildCached,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem unbuildDual_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length) :
    toffoliCount (unbuildDual acc Z bank cin src q r)+1=toffoliCount (unbuildConsumed acc Z bank cin src q) ∧
    measurementCount (unbuildDual acc Z bank cin src q r)=measurementCount (unbuildConsumed acc Z bank cin src q) ∧
    Challenge.gateSlots (unbuildDual acc Z bank cin src q r)+4=Challenge.gateSlots (unbuildConsumed acc Z bank cin src q) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:6≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have count:=consumedAddDual_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r (by omega) hy hc
  simp only [unbuildDual,unbuildConsumed,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedWReadyDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

def WReady (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (H : Nat) (u : State) : Prop :=
  regValue acc u.basis=4294968272*H ∧ regValue src u.basis=H ∧
    (∀w∈Z,u.basis w=false) ∧ (∀w∈bank,u.basis w=false) ∧ u.basis cin=false

theorem setWire_basis_outside (s : State) (q w : Wire) (v : Bool) (ne:w≠q) :
    (setWire s q v).basis w=s.basis w := by
  simp only [setWire,writeBit,Function.update_of_ne ne]

theorem WReady.setWire (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (H : Nat) (u : State)
    (q : Wire) (v : Bool) (fresh:q∉cin::(src++acc++Z++bank)) (h:WReady acc Z bank cin src H u) :
    WReady acc Z bank cin src H (setWire u q v) := by
  have qa:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qs:q∉src := by intro bad;exact fresh (by simp [bad])
  have qz:q∉Z := by intro bad;exact fresh (by simp [bad])
  have qb:q∉bank := by intro bad;exact fresh (by simp [bad])
  have qi:cin≠q := by intro e;exact fresh (by simp [←e])
  refine ⟨(setWire_regValue acc u q v qa).trans h.1,(setWire_regValue src u q v qs).trans h.2.1,?_,?_,?_⟩
  · intro w hw
    exact (setWire_basis_outside u q w v (by intro e;exact qz (e ▸ hw))).trans (h.2.2.1 w hw)
  · intro w hw
    exact (setWire_basis_outside u q w v (by intro e;exact qb (e ▸ hw))).trans (h.2.2.2.1 w hw)
  · exact (setWire_basis_outside u q cin v qi).trans h.2.2.2.2

theorem middleState_frame_copy (F newF M : Program) (q : Wire) (v : Bool)
    (sameM:measurementCount newF=measurementCount F) (off:q∉wires M) (s : State) (m : List Bool)
    (forward:∀tape,run newF tape s=setWire (run F tape s) q v) :
    middleState newF M s m=setWire (middleState F M s m) q v := by
  simp only [middleState,sameM]
  rw [forward,run_setWire M q v off]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedWLoopDualDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem cached_wloop_dual_eq (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire) (middle : Program)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
    (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
    (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
    (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (good:WReady acc Z bank cin src (regValue src s.basis)
      (middleState (NarrowAcc.build8 acc Z bank cin src) middle s m)) :
    run (buildDual acc Z bank cin src q r++middle++unbuildDual acc Z bank cin src q r) m s=
      run (NarrowAcc.build8 acc Z bank cin src++middle++SourceAddFourDevelop.unbuild acc Z bank cin src) m s := by
  let H:=regValue src s.basis
  have hf6:=hf _ (NarrowAcc.terms_mem src).2.2.1
  have zl:5≤Z.length := by have h:=hf6.zpad;norm_num [Acc.earlyTerm,hsrc] at h;omega
  have bl:132≤bank.length := by have h:=hf6.bankLen;norm_num [Acc.earlyTerm] at h;omega
  have bc:=buildCached_counts acc Z bank cin src q hacc hsrc zl bl
  have dc:=buildDual_counts acc Z bank cin src q r hacc hsrc zl bl
  have offF1:r∉wires (buildCached acc Z bank cin src q) := by
    intro h
    have h:=Finset.mem_insert.mp (buildCached_support acc Z bank cin src q hacc hsrc zl bl h)
    exact h.elim rq offFR
  have offI1:r∉wires (unbuildConsumed acc Z bank cin src q) := by
    intro h
    have h:=Finset.mem_insert.mp (unbuildConsumed_support acc Z bank cin src q hacc hsrc bl h)
    exact h.elim rq offIR
  let u:=middleState (NarrowAcc.build8 acc Z bank cin src) middle s m
  let t1:=middleState (buildCached acc Z bank cin src q) middle s m
  let t2:=setWire t1 r (cacheBit6 H)
  have eq1:t1=setWire u q (cacheBit H) :=
    middleState_frame_copy _ _ middle q (cacheBit H) bc.2.1 offM s m
      (fun tape=>buildCached_frame acc Z bank cin src q hacc hsrc hf s tape hz hb hi ha zero fresh offF)
  have ready1:WReady acc Z bank cin src H t1 := by
    rw [eq1]
    exact WReady.setWire acc Z bank cin src H u q (cacheBit H) fresh good
  have ready2:WReady acc Z bank cin src H t2 :=
    WReady.setWire acc Z bank cin src H t1 r (cacheBit6 H) freshR ready1
  have saved1:t2.basis q=cacheBit (regValue src t2.basis) := by
    rw [ready2.2.1]
    have atq:t1.basis q=cacheBit H := by
      rw [eq1]
      simp only [setWire,writeBit,Function.update_self]
    exact (setWire_basis_outside t1 r q (cacheBit6 H) (Ne.symm rq)).trans atq
  have saved2:t2.basis r=cacheBit6 (regValue src t2.basis) := by
    rw [ready2.2.1]
    simp only [t2,setWire,writeBit,Function.update_self]
  have av:regValue acc t2.basis=4294968272*regValue src t2.basis := by
    rw [ready2.2.1]
    exact ready2.1
  have forward:=buildDual_frame acc Z bank cin src q r hacc hsrc hf s
    (m.take (measurementCount (buildCached acc Z bank cin src q))) hz hb hi ha zero zeroR fresh offF freshR offFR rq
  have inverse:=unbuildDual_frame acc Z bank cin src q r hacc hsrc hf t2
    (m.drop (measurementCount (buildCached acc Z bank cin src q)+measurementCount middle))
    ready2.2.2.1 ready2.2.2.2.1 ready2.2.2.2.2 av saved1 saved2 fresh offI freshR offIR rq
  have paired:=cached_pair_eq (buildCached acc Z bank cin src q) (buildDual acc Z bank cin src q r) middle
    (unbuildConsumed acc Z bank cin src q) (unbuildDual acc Z bank cin src q r) r (cacheBit6 H)
    dc.2.1 offF1 offMR offI1 s m zeroR forward inverse
  exact paired.trans (cached_wloop_eq acc Z bank cin src q middle hacc hsrc hf s m hz hb hi ha zero fresh offF offM offI good)

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: WLoopDomainFreeDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem wloop_original_off (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (fresh:q∉cin::(src++acc++Z++bank)) :
    q∉wires (NarrowAcc.build8 acc Z bank cin src) ∧
    q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src) := by
  have support:=CodexNarrowTail.build8_support acc Z bank cin src ha (by omega) hf
  rw [CodexNarrowTail.build8_eq] at support
  have inv:=SourceAddFourDevelop.unbuild_resources acc Z bank cin src ha hs
    (fun f h=>(hf f h).toFitsLen)
  exact ⟨fun h=>fresh (List.mem_toFinset.mp (support.1 h)),
    fun h=>fresh (List.mem_toFinset.mp (support.2 (inv.2.2.1 h)))⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: EVLoanGeometryDevelop3
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem eV_mem_product (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) : eV L∈L.core.product :=
  eReg_product L _ (eK_mem L hw).2.2.1

theorem eV_off_aux (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (q : Wire) (hq:q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,L.core.workHigh,
      L.core.cin,L.core.normFlag,L.core.modFlag]) : eV L≠q := by
  intro eq
  have off:=(L.pairAuxAway hn q hq).1
  exact off (eq ▸ eV_mem_product L hw)

theorem eV_fresh_domain (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eV L∉L.core.cin::(hiReg L++accReg L++accZ L++accBank L) := by
  have off:=eV_off_aux L hw hn
  intro h
  simp only [List.mem_cons,List.mem_append] at h
  rcases h with h|(((h|h)|h)|h)
  · exact off _ (by simp) h
  · exact (eReg_away L hn _ (eK_mem L hw).2.2.1).2.2 h
  · exact off _ (by simp [accReg_work L _ h]) rfl
  · rcases accZ_mem L _ h with h|h
    · exact off _ (by simp [h]) rfl
    · exact off _ (by simp [List.mem_of_mem_drop h]) rfl
  · exact off _ (by simp [List.mem_of_mem_take h]) rfl

theorem eV_ne_eU (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) : eV L≠eU L := by
  have plen:(L.core.product.drop 256).length=2 := by simp [hw.core.product]
  have prodND:L.core.product.Nodup := by
    apply List.nodup_iff_count_le_one.mpr;intro q
    have h:=lay_pos L hn q
    omega
  have nd:(L.core.product.drop 256).Nodup := by
    apply List.nodup_iff_count_le_one.mpr;intro q
    have h:=List.nodup_iff_count_le_one.mp prodND q
    have le:=(List.drop_sublist 256 L.core.product).count_le q
    omega
  have hzero (xs : List Wire) : xs.headD 0=xs.getD 0 0 := by cases xs <;> rfl
  simp only [eV,eU,hzero]
  rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]
  intro eq
  have bad:=(List.Nodup.getElem_inj_iff nd).mp eq
  omega

theorem eV_ne_sumCarry (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eV L≠L.core.sumCarry := by
  intro eq
  apply ParkCarryDevelop.sumCarry_away L hn
  have h:=eV_mem_product L hw
  simp [ParkCarryDevelop.restWires,←eq,h]

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: EVLoanMiddleDevelop3
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem eV_off_wmiddle (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eV L∉wires (wFwdK L++(wCoreK L++wInvK L)) := by
  have off:=eV_off_aux L hw hn
  have hi:eV L∉hiReg L := (eReg_away L hn _ (eK_mem L hw).2.2.1).2.2
  have memOff:¬WinArith.Mem (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eV L) := by
    intro h
    rcases h with h|h|h|h|h|h
    · exact off _ (by simp) h
    · exact hi (mU_hi L _ h)
    · exact off _ (by simp [mR_work L _ h]) rfl
    · exact off _ (by simp [mS_pad L _ h]) rfl
    · exact off _ (by simp [mZ_pad L _ h]) rfl
    · exact off _ (by simp [mC_pad L _ h]) rfl
  have fw:eV L∉wires (wFwdK L) := by
    intro h
    have h:=WinArith.tFwdK_mem (mLens L hw) (eU L) _ h
    exact h.elim memOff (eV_ne_eU L hw hn)
  have iv:eV L∉wires (wInvK L) := by
    intro h
    have h:=WinArith.tInvK_mem (mLens L hw) (eU L) _ h
    exact h.elim memOff (eV_ne_eU L hw hn)
  have kwOff:eV L∉wires (kw L) := by
    intro h
    have h:eV L=eU L ∨ eV L=w192 L := by simpa [kw,wires,Instr.wires,or_comm] using h
    rcases h with h|h
    · exact eV_ne_eU L hw hn h
    · have w:=List.mem_of_mem_drop (List.mem_of_mem_drop (w192_tail L hw))
      exact off _ (by simp [w]) h
  have wc:eV L∉wires (wCoreTq L) := by
    intro h
    have old:=(QRel.qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).1 h
    have hh:=List.mem_toFinset.mp (QCore.qprog_support (rotWCore L) SquareReduction.p old)
    have mem:(eV L)∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,L.core.workHigh,
      L.core.cin,L.core.normFlag,L.core.modFlag] ∨ (eV L)∈L.core.out := by
      simp only [rotWCore,rotWork,measuredCore,MeasuredCanonicalModLayout.wires,foldCarry,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh
      have flat : eV L∈L.core.work.drop 128 ∨ eV L∈L.core.work.take 128 ∨ eV L∈L.core.out ∨
          eV L∈L.foldPad ∨ eV L=L.core.productHigh ∨ eV L=L.core.workHigh ∨
          eV L=L.core.outHigh ∨ eV L=L.core.cin ∨ eV L=L.core.modFlag := by
        simpa only [or_assoc] using hh
      rcases flat with h|h|h|h|h|h|h|h|h
      · exact Or.inl (by simp [List.mem_of_mem_drop h])
      · exact Or.inl (by simp [List.mem_of_mem_take h])
      · exact Or.inr h
      · exact Or.inl (by simp [h])
      · exact Or.inl (by simp [h])
      · exact Or.inl (by simp [h])
      · exact Or.inl (by simp [h])
      · exact Or.inl (by simp [h])
      · exact Or.inl (by simp [h])
    rcases mem with mem|mem
    · exact off _ mem rfl
    · exact (eReg_away L hn _ (eK_mem L hw).2.2.1).1 mem
  simp only [wires_append,Finset.mem_union,not_or,wCoreK]
  exact ⟨fw,⟨kwOff,wc,kwOff⟩,iv⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: EVLoanZeroDevelop2
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem eV_zero_of_eReg_lt (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (s : BasisState)
    (h:regValue (eReg L) s<2^129) : s (eV L)=false := by
  have value:=eReg_split L hw s
  cases hu:s (eU L) <;> cases hv:s (eV L) <;> simp only [hu,hv,Bool.false_eq_true,if_false,if_true] at value ⊢ <;> omega

theorem eV_zero_of_bstate (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (base : BasisState)
    (O E W : Nat) (s : BasisState) (hs:BState L base O E W s) (hE:E<2^129) : s (eV L)=false :=
  eV_zero_of_eReg_lt L hw s (by rw [hs.2.1];exact hE)

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedWLoopDualBStateDevelop2
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem cached_wloop_dual_bstate_step (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
    (O E O' : Nat) (middle : Program) (hE:E<2^129)
    (mid:Triple (BState L base O E (4294968272*regValue (hiReg L) base)) middle
      (BState L base O' E (4294968272*regValue (hiReg L) base)))
    (offM:L.core.sumCarry∉wires middle) (offMR:eV L∉wires middle) :
    Triple (BState L base O E 0)
      (buildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)++middle++
      unbuildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L))
      (BState L base O' E 0) := by
  intro s m hs
  have away:=ParkCarryDevelop.sumCarry_off_regs L hn
  have zero:s.basis L.core.sumCarry=false := (hs.2.2.2 _ away.1 away.2.1 away.2.2).trans hsum
  have zeroR:s.basis (eV L)=false := eV_zero_of_bstate L hw base O E 0 s.basis hs hE
  have fresh:=sumCarry_fresh_domain L hn
  have freshR:=eV_fresh_domain L hw hn
  have off:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_fits L hw hn) fresh
  have offR:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (eV L)
    (acc_lengths L hw).1 (hiReg_length L hw) (wTerms_fits L hw hn) freshR
  obtain ⟨hz,hb,hi,_,_⟩:=zero_regs L hn base hc O E 0 s.basis hs
  have source0:regValue (hiReg L) s.basis=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq=>bstate_other L hn base O E 0 s.basis hs q (Or.inl hq))
  have good:WReady (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (regValue (hiReg L) s.basis)
      (middleState (wBuild L) middle s m) := by
    let first:=run (wBuild L) (m.take (measurementCount (wBuild L))) s
    have firstGood:= (wBuild_step L hw hn base hc O E) s (m.take (measurementCount (wBuild L))) hs
    have midGood:=mid first ((m.drop (measurementCount (wBuild L))).take (measurementCount middle)) firstGood.2
    obtain ⟨mz,mb,mi,_,_⟩:=zero_regs L hn base hc O' E _ _ midGood.2
    have source1:=regValue_congr (hiReg L) _ base
      (fun q hq=>bstate_other L hn base O' E _ _ midGood.2 q (Or.inl hq))
    exact ⟨midGood.2.2.2.1.trans (by rw [source0]),source1.trans source0.symm,mz,mb,mi⟩
  rw [cached_wloop_dual_eq _ _ _ _ _ _ _ middle (acc_lengths L hw).1 (hiReg_length L hw)
    (wTerms_fits L hw hn) s m hz hb hi hs.2.2.1 zero zeroR fresh freshR (eV_ne_sumCarry L hw hn)
    off.1 offM off.2 offR.1 offMR offR.2 good]
  have old:Triple (BState L base O E 0) (wBuild L++middle++wUnbuildKnown L) (BState L base O' E 0) :=
    ((wBuild_step L hw hn base hc O E).seq mid).seq (wUnbuildKnown_step L hw hn base hc O' E)
  exact old s m hs

end ECDSAAdd.Entrant.InverseCarryDevelop
end




-- Two retained W carries: CachedDualGateResourcesDevelop2
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem cachedSubDual_support (xs ys cs : List Wire) (cin q r : Wire)
    (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:8≤ys.length) :
    wires (cachedSubDual xs ys cs cin q r)⊆insert r (wires (cachedSub xs ys cs cin q)) := by
  have used:cs.getD 5 0∈wires (sixthMajority xs ys cs) := by
    simp [sixthMajority,majority,wires,Instr.wires]
  have cused:cs.getD 5 0∈wires (insertCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (cs.getD 4 0) q++subPost6 xs ys cs cin) := by
    simp only [insertCopy,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr (Or.inr used))
  have h:=insertCopy_support (insertCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (cs.getD 4 0) q)
    (subPost6 xs ys cs cin) (cs.getD 5 0) r cused
  have split:cachedSub xs ys cs cin q=insertCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (cs.getD 4 0) q++subPost6 xs ys cs cin :=
    (cachedSub_first_split xs ys cs cin q hx hc hy).trans (firstCopy_split _ _ _ _ _)
  rw [←split] at h
  exact h

theorem cachedSubDual_physical (xs ys cs : List Wire) (cin q r : Wire)
    (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:8≤ys.length)
    (off:r∉wires (cachedSub xs ys cs cin q)) (physical:GatePhysical (cachedSub xs ys cs cin q)) :
    GatePhysical (cachedSubDual xs ys cs cin q r) := by
  have split:cachedSub xs ys cs cin q=insertCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (cs.getD 4 0) q++subPost6 xs ys cs cin :=
    (cachedSub_first_split xs ys cs cin q hx hc hy).trans (firstCopy_split _ _ _ _ _)
  have used:cs.getD 5 0∈wires (cachedSub xs ys cs cin q) := by
    rw [split]
    simp [insertCopy,sixthMajority,majority,wires_append,wires,Instr.wires]
  have ne:cs.getD 5 0≠r := by intro e;exact off (e ▸ used)
  rw [split,gatePhysical_append] at physical
  exact insertCopy_physical _ _ _ _ physical.1 physical.2 ne

theorem consumedAddDual_support (src Z ys carry : List Wire) (cin q r : Wire)
    (hs:8≤src.length) (hy:ys.length=src.length+5) (hc:6≤carry.length) :
    wires (consumedAddDual src Z ys carry cin q r)⊆insert r (wires (consumedAdd src Z ys carry cin q)) := by
  intro w hw
  by_cases eq:w=r
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [consumedAddDual,wires_append,Finset.mem_union] at hw
  simp only [consumedAdd_split6 src Z ys carry cin q hs hy hc,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (consume_support ((src++Z.take 5).getD 5 0) (ys.getD 5 0) (carry.getD 4 0) (carry.getD 5 0) r hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem consumedAddDual_physical (src Z ys carry : List Wire) (cin q r : Wire)
    (hs:8≤src.length) (hy:ys.length=src.length+5) (hc:6≤carry.length)
    (off:r∉wires (consumedAdd src Z ys carry cin q)) (physical:GatePhysical (consumedAdd src Z ys carry cin q)) :
    GatePhysical (consumedAddDual src Z ys carry cin q r) := by
  have split:=consumedAdd_split6 src Z ys carry cin q hs hy hc
  have used:carry.getD 5 0∈wires (consumedAdd src Z ys carry cin q) := by
    rw [split]
    simp [sixthMajority,majority,wires_append,wires,Instr.wires]
  have ne:r≠carry.getD 5 0 := by intro e;exact off (e.symm ▸ used)
  rw [split,gatePhysical_append,gatePhysical_append] at physical
  rw [consumedAddDual,gatePhysical_append,gatePhysical_append]
  refine ⟨⟨physical.1.1,?_⟩,physical.2⟩
  simp only [move,GatePhysical,List.mem_cons,List.not_mem_nil,or_false]
  intro i hi
  rcases hi with rfl|rfl
  · exact ne
  · exact Ne.symm ne

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedWDualResourcesDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem buildDual_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    wires (buildDual acc Z bank cin src q r)⊆insert r (wires (buildCached acc Z bank cin src q)) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have sub:=cachedSubDual_support (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r
    (by omega) (by omega) (by omega)
  intro w hw
  by_cases eq:w=r
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [buildDual,wires_append,Finset.mem_union] at hw
  simp only [buildCached,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem unbuildDual_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length) :
    wires (unbuildDual acc Z bank cin src q r)⊆insert r (wires (unbuildConsumed acc Z bank cin src q)) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:6≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have sub:=consumedAddDual_support src Z ((acc.take 139).drop 6) (bank.take 132) cin q r (by omega) hy hc
  intro w hw
  by_cases eq:w=r
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [unbuildDual,wires_append,Finset.mem_union] at hw
  simp only [unbuildConsumed,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem buildDual_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
    (off:r∉wires (buildCached acc Z bank cin src q)) (physical:GatePhysical (buildCached acc Z bank cin src q)) :
    GatePhysical (buildDual acc Z bank cin src q r) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  rw [buildCached,gatePhysical_append,gatePhysical_append] at physical
  have midOff:r∉wires (cachedSub (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q) := by
    intro h;apply off
    simp only [buildCached,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=cachedSubDual_physical _ _ _ cin q r (by omega) (by omega) (by omega) midOff physical.1.2
  simp only [buildDual,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

theorem unbuildDual_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length)
    (off:r∉wires (unbuildConsumed acc Z bank cin src q)) (physical:GatePhysical (unbuildConsumed acc Z bank cin src q)) :
    GatePhysical (unbuildDual acc Z bank cin src q r) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:6≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  rw [unbuildConsumed,gatePhysical_append,gatePhysical_append] at physical
  have midOff:r∉wires (consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q) := by
    intro h;apply off
    simp only [unbuildConsumed,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=consumedAddDual_physical src Z ((acc.take 139).drop 6) (bank.take 132) cin q r (by omega) hy hc midOff physical.1.2
  simp only [unbuildDual,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedWLoopDualResourcesDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic ParkCarryDevelop

theorem cached_wloop_dual_le (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire) (middle : Program)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    ExtraLe r (buildDual acc Z bank cin src q r++middle++unbuildDual acc Z bank cin src q r)
      (buildCached acc Z bank cin src q++middle++unbuildConsumed acc Z bank cin src q) := by
  have b:=buildDual_support acc Z bank cin src q r ha hs hz hb
  have u:=unbuildDual_support acc Z bank cin src q r ha hs hb
  have bc:=buildDual_counts acc Z bank cin src q r ha hs hz hb
  have uc:=unbuildDual_counts acc Z bank cin src q r ha hs hb
  constructor
  · intro w hw
    by_cases eq:w=r
    · exact Finset.mem_insert.mpr (Or.inl eq)
    apply Finset.mem_insert_of_mem
    simp only [wires_append,Finset.mem_union] at hw ⊢
    rcases hw with (hw|hw)|hw
    · have h:=Finset.mem_insert.mp (b hw)
      exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inl h))
    · exact Or.inl (Or.inr hw)
    · have h:=Finset.mem_insert.mp (u hw)
      exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inr h)
  · simp only [Challenge.gateSlots_append]
    omega

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: EVLoanCachedDomainDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem eV_off_cached_build_unbuild (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eV L∉wires (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) ∧
    eV L∉wires (unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) := by
  have lens:=acc_lengths L hw
  have fresh:=eV_fresh_domain L hw hn
  have off:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (eV L)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) fresh
  have b:=buildCached_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    lens.1 (hiReg_length L hw) (by omega) (by omega)
  have u:=unbuildConsumed_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
    lens.1 (hiReg_length L hw) (by omega)
  constructor
  · intro h
    exact (Finset.mem_insert.mp (b h)).elim (eV_ne_sumCarry L hw hn) off.1
  · intro h
    exact (Finset.mem_insert.mp (u h)).elim (eV_ne_sumCarry L hw hn) off.2

end ECDSAAdd.Entrant.InverseCarryDevelop
end




-- Two retained W carries: OldBExtraWireDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem old_bbody_eV_mem (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    eV L∈wires (bBody L c) := by
  have lens:=eSrc_length L hw (b1Src L) (Or.inl rfl)
  have member:eV L∈eReg L := (eK_mem L hw).2.2.1
  have sub:eV L∈wires (eSub L (b1Src L)) := by
    rw [eSub,subInPlace_wires _ _ _ _ lens.1 lens.2]
    simp [member]
  simp only [bBody,wFold,wires_append,Finset.mem_union]
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl sub)))))

end ECDSAAdd.Entrant.InverseCarryDevelop
end




-- Two retained W carries: EVLoanAMiddleDevelop2
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem eV_off_acore (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    eV L∉wires (qprogTq L.measuredCore SquareReduction.p) := by
  intro h
  have old:=(QRel.qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)).1 h
  have hh:=List.mem_toFinset.mp (QCore.qprog_support L.measuredCore SquareReduction.p old)
  simp only [measuredCore,MeasuredCanonicalModLayout.wires,foldCarry,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh
  have flat : eV L∈L.core.work ∨ eV L∈L.core.out ∨ eV L∈L.foldPad ∨
      eV L=L.core.productHigh ∨ eV L=L.core.workHigh ∨ eV L=L.core.outHigh ∨ eV L=L.core.cin ∨ eV L=L.core.modFlag := by
    simpa only [or_assoc] using hh
  have off:=eV_off_aux L hw hn
  rcases flat with h|h|h|h|h|h|h|h
  · exact off _ (by simp [h]) rfl
  · exact (eReg_away L hn _ (eK_mem L hw).2.2.1).1 h
  · exact off _ (by simp [h]) rfl
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h

theorem eV_off_amiddle (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) : eV L∉wires (aMiddle L g) := by
  have ne:eV L≠g := by
    intro e
    apply hg
    have h:=eV_mem_product L hw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,←e,h]
  have away:eV L∉accReg L := (eReg_away L hn _ (eK_mem L hw).2.2.1).2.1
  have masks:eV L∉wires (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK) := by
    intro h
    have mem:=maskedConstant_wires_subset g (accReg L) OwnDiagAll12Square.cFlipK h
    simp only [List.mem_toFinset,List.mem_cons] at mem
    exact mem.elim ne away
  simp only [aMiddle,wires_append,Finset.mem_union,not_or]
  exact ⟨masks,eV_off_acore L hw hn,masks⟩

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedAFoldDualDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

def aFoldDual (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  buildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)++aMiddle L g++
    unbuildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)

theorem aFoldDual_eq (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false) (hV:base (eV L)=false)
    (O : Nat) (hO:O<SquareReduction.p) (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    run (aFoldDual L g) m s=run (aFold8Tq L g) m s := by
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
  have eq:=cached_wloop_dual_eq (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (aMiddle L g)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) s m hz hb clean.cin ha zero zeroR
    (sumCarry_fresh_domain L hn) freshR (eV_ne_sumCarry L hw hn) off.1 off.2.1 off.2.2
    offR.1 (eV_off_amiddle L hw hn g hg) offR.2 (a_middle_good L hw hn g hg base hc O hO s m hf)
  simpa only [aFoldDual,aFold8Tq,aMiddle,List.append_assoc] using eq

theorem aFoldDual_frame (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false) (hV:base (eV L)=false)
    (O : Nat) (hO:O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (aFoldDual L g)
      (SquareFrame L.core.out base (((if base g then OwnDiagAll12Square.cFlipK-4294968272*regValue (hiReg L) base
        else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hs
  rw [aFoldDual_eq L hw hn g hg base hc hsum hV O hO s m hs]
  exact aFold8_frameTq L hw hn g hg base hc O hO s m hs

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: EVLoanProductZeroDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem eV_zero_of_product_lt (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (s : BasisState)
    (bound:regValue L.core.product s<2^256) : s (eV L)=false := by
  have value:regValue (L.core.product.drop 256) s=0 := by
    rw [regValue_drop_div _ 256 (by simp [hw.core.product]),Nat.div_eq_of_lt bound]
  apply (regValue_zero _ _).mp value
  change (L.core.product.drop 256).getD 1 0∈L.core.product.drop 256
  exact DiagSq.getD_in _ _ (by simp [hw.core.product])

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: CachedABodyDualDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

def aBodyDual (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++aFoldDual L c)

theorem aBodyDual_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBodyDual L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
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
  have t3 := aFoldDual_frame L hw hn c hcw base hc hzero vZero O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  -- value
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

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: DualCarryAResourcesDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop

def ExtraLeTwo (q r : Wire) (P Q : Program) : Prop :=
  wires P⊆insert q (insert r (wires Q)) ∧ Challenge.gateSlots P≤Challenge.gateSlots Q

theorem aBodyDual_counts (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    toffoliCount (aBodyDual L c)=2916 ∧ measurementCount (aBodyDual L c)=3077 := by
  have old:=aBodyCached_counts L hw c
  have lens:=acc_lengths L hw
  have wb:=buildDual_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)
    lens.1 (hiReg_length L hw) (by omega) (by omega)
  have wu:=unbuildDual_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)
    lens.1 (hiReg_length L hw) (by omega)
  simp only [aBodyDual,aFoldDual,aBodyCached,aFoldCached,aMiddle,toffoliCount_append,measurementCount_append] at old ⊢
  constructor <;> omega

theorem aBodyDual_le_parent (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    ExtraLe (eV L) (aBodyDual L c) (aBodyCached L c) := by
  have lens:=acc_lengths L hw
  have loop:=cached_wloop_dual_le (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (aMiddle L c)
    lens.1 (hiReg_length L hw) (by omega) (by omega)
  have all:=ExtraLe.app (extraLe_refl (eV L) (measuredFoldQTq L (negP L)))
    (ExtraLe.app (extraLe_refl (eV L) (measuredFoldQTq L (rot128F L))) loop)
  simpa only [aBodyDual,aFoldDual,aBodyCached,aFoldCached] using all

theorem aBodyDual_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    toffoliCount (aBodyDual L c)+130=toffoliCount (aBody L c) ∧
    measurementCount (aBodyDual L c)+3=measurementCount (aBody L c) ∧
    ExtraLeTwo L.core.sumCarry (eV L) (aBodyDual L c) (aBody L c) := by
  have count:=aBodyDual_counts L hw c
  have oldCount:=aBodyCached_counts L hw c
  have old:=aBodyCached_rel L hw c
  have step:=aBodyDual_le_parent L hw c
  refine ⟨by omega,by omega,?_,step.2.trans old.2.2.2⟩
  intro w hw'
  rcases Finset.mem_insert.mp (step.1 hw') with h|h
  · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h))
  · rcases Finset.mem_insert.mp (old.2.2.1 h) with h|h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)

theorem aBodyDual_physical (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire)
    (hn:(c::L.wires).Nodup) : GatePhysical (aBodyDual L c) := by
  have nd:=(List.nodup_cons.mp hn).2
  have lens:=acc_lengths L hw
  have off:=eV_off_cached_build_unbuild L hw nd
  have old:=aBodyCached_physical L hw c hn
  simp only [aBodyCached,aFoldCached,gatePhysical_append] at old
  rcases old with ⟨p1,p2,⟨⟨wb,mid⟩,wu⟩⟩
  have bp:=buildDual_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)
    lens.1 (hiReg_length L hw) (by omega) (by omega) off.1 wb
  have up:=unbuildDual_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)
    lens.1 (hiReg_length L hw) (by omega) off.2 wu
  simp only [aBodyDual,aFoldDual,gatePhysical_append]
  exact ⟨p1,p2,⟨⟨bp,mid⟩,up⟩⟩

theorem aBodyDual_support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) (c : Wire) :
    wires (aBodyDual L c)⊆(c::L.wires).toFinset := by
  intro q hq
  have h:=(aBodyDual_rel L hw c).2.2.1 hq
  rcases Finset.mem_insert.mp h with h|h
  · subst q;simp [Arithmetic.CuccaroStreamedSquareWideLayout.wires,Arithmetic.CuccaroStreamedSquareLayout.wires]
  · rcases Finset.mem_insert.mp h with h|h
    · subst q
      have member:=eV_mem_product L hw
      simp [Arithmetic.CuccaroStreamedSquareWideLayout.wires,Arithmetic.CuccaroStreamedSquareLayout.wires,member]
    · exact ControlLoan1589BFFold.aBody_support L hw hn c h

end ECDSAAdd.Entrant.InverseCarryDevelop
end


-- Two retained W carries: DualBodyPlacementDevelop
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic ControlLoan1589BFFold ParkCarryDevelop

def hostedADual (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
  aBodyDual (hostLayout L rho) c

theorem hostedADual_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
    toffoliCount (hostedADual L rho c)+130=toffoliCount (aBody L c) ∧
    measurementCount (hostedADual L rho c)+3=measurementCount (aBody L c) ∧
    ExtraLeTwo (rho.symm L.core.sumCarry) (eV L) (hostedADual L rho c) (aBody L c) := by
  have h:=aBodyDual_rel (hostLayout L rho) (host_widths L hw rho) c
  simpa only [hostedADual,oldA_host,hostLayout,eV] using h

theorem hostedADual_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire)
    (h:rho L.core.sumCarry=L.core.sumCarry) : hostedADual L rho c=aBodyDual L c := by
  rw [hostedADual,host_eq L rho h]

end ECDSAAdd.Entrant.InverseCarryDevelop
end
