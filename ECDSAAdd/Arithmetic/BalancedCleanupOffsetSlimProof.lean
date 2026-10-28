import ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlimChainProof
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetCompareProof
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetConstant
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
open BalancedCleanupOffset BalancedField
attribute [local irreducible] run chain

theorem program_sandwich (L : Layout) : program L=
    front L++chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity++
      (front L).reverse := rfl

theorem chain_compare (bits : List MappedBit) (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hn : (target::cinC::cinB::(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉target::cinC::cinB::(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (m : List Bool) (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false)
    (hi : s.basis cinB=true) :
    run (chain bits xs ys cs ds cinC cinB target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^
        decide (regValue xs s.basis<(mappedValue bits s.basis+regValue ys s.basis+
          (s.basis cinC).toNat)%2^ys.length))⟩ := by
  have h := chain_run bits xs ys cs ds cinC cinB target hn ha hb hx hc hd s m hcc hdd
  have v := decision_value (bits.map (fun b => b.value s.basis)) (xs.map s.basis)
    (ys.map s.basis) (by simpa using hb) (by simpa using hx) (s.basis cinC)
  rw [mapped_value_map,word_value_map,word_value_map,List.length_map] at v
  rw [hi,v] at h
  exact h


private theorem bank_away (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.carry++L.offsetCarry) :
    q∉L.r ∧ q∉L.y ∧ q≠L.lower ∧ q≠L.cout := by
  have nd : (L.r++(L.y++(L.carry++L.offsetCarry))).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (L.allND hn)).2.1
  have r := List.nodup_append'.mp nd
  have y := List.nodup_append'.mp r.2.1
  refine ⟨fun h => List.disjoint_left.mp r.2.2 h (List.mem_append_right _ hq),
    fun h => List.disjoint_left.mp y.2.2 h hq,?_,?_⟩
  · intro e
    exact L.flagAway hn L.lower (by simp) (by simp [←e,List.mem_append.mp hq])
  · intro e
    exact L.flagAway hn L.cout (by simp) (by simp [←e,List.mem_append.mp hq])

/-- Complete exact measured cleanup, restoring every site except the cleared
parity bit, and preserving phase for every measurement record. Both carry
banks must be supplied clean by the caller's actual allocation invariant. -/
theorem xor_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R)
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false)
    (ho : s.basis L.one=false) (hcout : s.basis L.cout=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hd : ∀q∈L.offsetCarry,s.basis q=false)
    : run (program L) m s=⟨s.phase,writeBit s.basis L.parity
      (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|))⟩ := by
  let u := run (front L) m s
  let cell := chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity
  let v := run cell m u
  let n := m.drop (measurementCount cell)
  have prepared := front_value L hw hn R Y B hr hy s m hR hY hS hz hcout
  have flags := L.flagsND hn
  have flagFacts := flags
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flagFacts
  have pR : L.parity∉L.r := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have pY : L.parity∉L.y := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have oR : L.one∉L.r := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have oY : L.one∉L.y := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have pl : L.parity≠L.lower := by tauto
  have pc : L.parity≠L.cout := by tauto
  have ol : L.one≠L.lower := by tauto
  have oc : L.one≠L.cout := by tauto
  have one : u.basis L.one=false := (prepared.2.2.2.2 _ oR oY ol oc).trans ho
  have parity : u.basis L.parity=s.basis L.parity :=
    prepared.2.2.2.2 _ pR pY pl pc
  have cleanC : ∀q∈L.carry,u.basis q=false := by
    intro q hq
    have away := bank_away L hn q (List.mem_append_left _ hq)
    exact (prepared.2.2.2.2 q away.1 away.2.1 away.2.2.1 away.2.2.2).trans (hc q hq)
  have cleanD : ∀q∈L.offsetCarry,u.basis q=false := by
    intro q hq
    have away := bank_away L hn q (List.mem_append_right _ hq)
    exact (prepared.2.2.2.2 q away.1 away.2.1 away.2.2.1 away.2.2.2).trans (hd q hq)
  have widths := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cmp := chain_compare (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout
    L.parity (L.chainND hn) (offsetSources_away L hn)
    (by rw [offsetBits_length,widths.2.1]) (by omega) (by rw [hw.2,widths.2.1])
    (by rw [hw.1.2.2,widths.2.1]) u m cleanD cleanC prepared.2.2.2.1
  have pred : decide (regValue L.y u.basis <
      (mappedValue (offsetBits L) u.basis+regValue L.r u.basis+(u.basis L.one).toNat)%2^L.r.length)=
      decide (q < |2*R-signedY B Y|) := by
    rw [prepared.1,prepared.2.1,offsetBits_value,prepared.2.2.1,one,widths.2.1]
    simp only [Bool.toNat_false,Nat.add_zero]
    exact decide_eq_decide.mpr (chain_predicate B R Y hr hy)
  have clear : v=⟨u.phase,writeBit u.basis L.parity
      (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|))⟩ := by
    change run cell m u=_
    rw [cmp,pred,parity]
  have except := BalancedCleanup.inverse_except (front L) (front_proper L hn) L.parity
    (front_parity_away L hw hn) s v m n (by
      rw [clear]
      exact ⟨rfl,fun q hq => by simp [writeBit,hq,u]⟩)
  have kept := run_preserves_outside (front L).reverse n v L.parity (by
    rw [wires_reverse]
    exact front_parity_away L hw hn)
  have zero : (run (front L).reverse n v).basis L.parity=
      (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|)) := by
    rw [kept,clear]
    simp [writeBit]
  have execute : run (program L) m s=run (front L).reverse n v := by
    have mc := properProgram_measurementCount _ (front_proper L hn)
    have empty : run (front L) (m.take 0) s=run (front L) m s := by
      simpa only [mc] using run_take (front L) m s
    rw [program_sandwich,List.append_assoc,run_append,mc,List.drop_zero,empty,
      run_append,run_take]
  rw [execute]
  apply State.extensionality
  · exact except.1
  · funext q
    by_cases e : q=L.parity
    · subst q
      simpa [writeBit] using zero
    · simpa [writeBit,e] using except.2 q e

/-- Known parity is erased using the same exact XOR oracle. -/
theorem correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R)
    (hY : regValue L.y s.basis=encodeWord 256 Y) (hS : s.basis L.sign=B)
    (hz : s.basis L.lower=false) (ho : s.basis L.one=false) (hcout : s.basis L.cout=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hd : ∀q∈L.offsetCarry,s.basis q=false)
    (hA : s.basis L.parity=decide (q < |2*R-signedY B Y|)) :
    run (program L) m s=⟨s.phase,writeBit s.basis L.parity false⟩ := by
  simpa only [hA,Bool.xor_self] using
    xor_correct L hw hn R Y B hr hy s m hR hY hS hz ho hcout hc hd

end ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim.chain_compare
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim.xor_correct
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlim.correct
