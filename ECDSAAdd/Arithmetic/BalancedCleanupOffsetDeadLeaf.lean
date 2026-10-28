import ECDSAAdd.Arithmetic.BalancedCleanupOffsetHead
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetDeadLeaf
open BalancedCleanupOffset

def bit : MappedBit := {wire:=none,flip:=false}
def oldLeaf : Program := prepareHead bit 16 17 18 19 20 21++
  flipBelow none 21 22++releaseHead bit 16 17 18 19 20 21
def newLeaf : Program := mappedSum bit 17 18++[.X 17]++
  compareChain none [16] [17] [21] 19 22++[.X 17]++mappedSum bit 17 18

def result (s : State) : State := ⟨s.phase,writeBit s.basis 22
  (s.basis 22 ^^ !(carryBit (s.basis 16) (!(sumBit false (s.basis 17) (s.basis 18))) (s.basis 19)))⟩

attribute [local irreducible] run majority eraseCarry mappedMajority mappedEraseCarry mappedSum

private theorem sumM : measurementCount (mappedSum bit 17 18)=0 := by
  simp [mappedSum,bit,measurementCount]
private theorem xM : measurementCount [.X 17]=0 := rfl
private theorem prepareM : measurementCount (prepareHead bit 16 17 18 19 20 21)=0 := by
  simp [prepareHead,bit,mappedMajority,mappedSum,majority,measurementCount_append,measurementCount]
private theorem flipM : measurementCount (flipBelow none 21 22)=0 := by
  simp [flipBelow,measurementCount]
private theorem preM : measurementCount (mappedSum bit 17 18++[.X 17])=0 := by
  simp only [measurementCount_append,sumM,xM,Nat.add_zero]
private theorem compareM : measurementCount (compareChain none [16] [17] [21] 19 22)=1 := by
  simp [compareChain,majority,eraseCarry,flipBelow,measurementCount_append,measurementCount]

private theorem zero_records (P : Program) (h : measurementCount P=0)
    (s : State) (m n : List Bool) : run P m s=run P n s := by
  have a := run_take P m s
  have b := run_take P n s
  rw [h,List.take_zero] at a b
  exact a.symm.trans b

private theorem run_zero_append (P Q : Program) (h : measurementCount P=0)
    (s : State) (m : List Bool) : run (P++Q) m s=run Q m (run P m s) := by
  rw [run_append,h,List.take_zero,List.drop_zero,zero_records P h s [] m]

theorem old_normal (s : State) (m : List Bool) (hc : s.basis 20=false) (hd : s.basis 21=false) :
    run oldLeaf m s=result s := by
  let K := carryBit false (s.basis 17) (s.basis 18)
  let S := sumBit false (s.basis 17) (s.basis 18)
  let D := carryBit (s.basis 16) (!S) (s.basis 19)
  let u := run (prepareHead bit 16 17 18 19 20 21) m s
  have pu := prepareHead_run bit 16 17 18 19 20 21 (by decide) (by simp [bit]) s m hc hd
  change u=⟨s.phase,writeBit (writeBit (writeBit s.basis 20 K) 17 (!S)) 21 D⟩ at pu
  let v := run (flipBelow none 21 22) m u
  have pv := flipBelow_correct none 21 22 (by decide) (by simp) u m
  change v=⟨u.phase,writeBit u.basis 22 (u.basis 22 ^^ !u.basis 21)⟩ at pv
  have clear := releaseHead_run bit 16 17 18 19 20 21 (by decide) (by simp [bit])
    false (s.basis 16) (s.basis 17) (s.basis 18) (s.basis 19) v m
    (by simp [bit,MappedBit.value])
    (by simp [pv,pu,writeBit]) (by simp [pv,pu,writeBit])
    (by simp [pv,pu,writeBit]) (by simp [pv,pu,writeBit,S])
    (by simp [pv,pu,writeBit,K]) (by simp [pv,pu,writeBit,D,S])
  have actual : run oldLeaf m s=run (releaseHead bit 16 17 18 19 20 21) m v := by
    simp only [oldLeaf,List.append_assoc]
    rw [run_zero_append _ _ prepareM,run_zero_append _ _ flipM]
  rw [actual,clear,pv,pu]
  apply State.extensionality
  · rfl
  · funext q
    by_cases e20 : q=20 <;> by_cases e17 : q=17 <;>
      by_cases e21 : q=21 <;> by_cases e22 : q=22 <;>
      simp [result,writeBit,Function.update,e20,e17,e21,e22,hc,hd,K,S,D]

private theorem carry_threshold (a b c : Bool) :
    decide (2 ≤ (if a then 1 else 0)+(if b then 1 else 0)+c.toNat)=carryBit a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem new_normal (s : State) (m : List Bool) (hd : s.basis 21=false) :
    run newLeaf m s=result s := by
  let S := sumBit false (s.basis 17) (s.basis 18)
  let u := run (mappedSum bit 17 18++[.X 17]) m s
  have pu : u=⟨s.phase,writeBit s.basis 17 (!S)⟩ := by
    dsimp only [u]
    rw [run_zero_append _ _ sumM]
    rw [mappedSum_correct bit 17 18 (by decide) (by simp [bit])]
    rw [x_run]
    apply State.extensionality
    · rfl
    · funext q
      by_cases e : q=17 <;> simp [writeBit,Function.update,e,bit,MappedBit.value,S]
  let v := run (compareChain none [16] [17] [21] 19 22) m u
  have comp := compareChain_correct none [16] [17] [21] 19 22 (by decide)
    (by simp) rfl rfl u m (by
      intro q hq
      rcases List.mem_singleton.mp hq with rfl
      simpa [pu,writeBit] using hd)
  change v.phase=u.phase ∧ (∀q,q≠22 → v.basis q=u.basis q) ∧ _ at comp
  have value : v.basis 22=(s.basis 22 ^^ !(carryBit (s.basis 16) (!S) (s.basis 19))) := by
    have raw := comp.2.2
    change v.basis 22=(u.basis 22 ^^ !(decide (2 ≤
      (if u.basis 16 then 1 else 0)+(if u.basis 17 then 1 else 0)+(u.basis 19).toNat))) at raw
    rw [carry_threshold] at raw
    have h22 : u.basis 22=s.basis 22 := by rw [pu]; simp [writeBit]
    have h16 : u.basis 16=s.basis 16 := by rw [pu]; simp [writeBit]
    have h17 : u.basis 17= !S := by rw [pu]; simp [writeBit]
    have h19 : u.basis 19=s.basis 19 := by rw [pu]; simp [writeBit]
    rw [h22,h16,h17,h19] at raw
    exact raw
  have layout : newLeaf=(mappedSum bit 17 18++[.X 17])++
      (compareChain none [16] [17] [21] 19 22++([.X 17]++mappedSum bit 17 18)) := by
    simp only [newLeaf,List.append_assoc]
  have actual : run newLeaf m s=run (mappedSum bit 17 18) (m.drop 1) (run [.X 17] (m.drop 1) v) := by
    rw [layout,run_zero_append _ _ preM,run_append]
    have take := run_take (compareChain none [16] [17] [21] 19 22) m u
    rw [compareM] at take
    rw [compareM,take,run_zero_append _ _ xM]
  rw [actual,x_run,mappedSum_correct bit 17 18 (by decide) (by simp [bit])]
  apply State.extensionality
  · change v.phase=s.phase
    exact comp.1.trans (by rw [pu])
  · funext q
    by_cases eq : q=17
    · subst q
      have read := comp.2.1 17 (by decide)
      have cin := comp.2.1 18 (by decide)
      cases ey : s.basis 17 <;> cases ec : s.basis 18 <;>
        simp [result,writeBit,Function.update,bit,MappedBit.value,read,cin,pu,S,sumBit,ey,ec]
    · by_cases et : q=22
      · subst q
        simp [result,writeBit,Function.update,eq,value,S]
      · have read := comp.2.1 q et
        simp [result,writeBit,Function.update,eq,et,read,pu]

theorem leaf_equiv (s : State) (mOld mNew : List Bool)
    (hc : s.basis 20=false) (hd : s.basis 21=false) :
    run oldLeaf mOld s=run newLeaf mNew s :=
  (old_normal s mOld hc hd).trans (new_normal s mNew hd).symm

theorem prices : toffoliCount oldLeaf=2 ∧ measurementCount oldLeaf=2 ∧
    toffoliCount newLeaf=1 ∧ measurementCount newLeaf=1 := by
  simp [oldLeaf,newLeaf,prepareHead,releaseHead,bit,mappedMajority,mappedSum,
    mappedEraseCarry,majority,eraseCarry,compareChain,flipBelow,
    toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.BalancedCleanupOffsetDeadLeaf
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetDeadLeaf.leaf_equiv
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetDeadLeaf.prices
