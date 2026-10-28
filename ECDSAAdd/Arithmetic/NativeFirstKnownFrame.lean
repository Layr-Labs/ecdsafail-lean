import ECDSAAdd.Arithmetic.NativeFirstKnownProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.NativeFirstKnown
open NativeFirstDirect
attribute [local irreducible] run hAdd kAdd mappedAdd hReceiver

private theorem contained (w : Nat → Wire) (a n b m : Nat)
    (lo : b≤a) (hi : a+n≤b+m) :
    ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨i,by
    simp only [List.mem_range'_1] at hi' ⊢
    omega,rfl⟩

private theorem one_block (w : Nat → Wire) (a : Nat) : wireBlock w a 1=[w a] := by
  simp [wireBlock,List.range']

/-- This physical witness is produced by the existing clean copy. No bound on
the B value or a ghost original-x register is required. -/
theorem front_known_sum (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool)
    (ha : regValue (wireBlock w 1 256) s.basis=0) :
    mappedValue (desired w) (run (inverseFront w) m s).basis=
      regValue (wireBlock w 4 253) (run (inverseFront w) m s).basis := by
  let P : Program := [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]
  let t := run P m s
  let u := run (lowCopy w) m t
  have pm : measurementCount P=0 := rfl
  have front : run (inverseFront w) m s=u := by
    rw [inverseFront,run_append,run_take,pm,List.drop_zero]
  have flags_keep (i : Nat) (hi : i<1798)
      (sep : i≠0 ∧ i≠770 ∧ i≠1028) : t.basis (w i)=s.basis (w i) := by
    apply run_preserves_outside P m s
    have h0 := index_ne w hn i 0 hi (by omega) sep.1
    have hB := index_ne w hn i 770 hi (by omega) sep.2.1
    have hQ := index_ne w hn i 1028 hi (by omega) sep.2.2
    simp [P,wires,Instr.wires,h0,hB,hQ]
  have cleanT : regValue (wireBlock w 1 256) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [flags_keep i (by omega) (by omega)]
    exact (regValue_zero _ _).mp ha _ (List.mem_map.mpr ⟨i,by simpa only [List.mem_range'_1] using hi,rfl⟩)
  have copy := copyRegister_correct none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) (copy_inputs_nd w hn) (by simp) t m
  have dest0 : regValue (wireBlock w 1 255) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero _ _).mp cleanT q (block_subset w 1 255 256 (by omega) q hq)
  have value : regValue (wireBlock w 1 255) u.basis=regValue (wireBlock w 771 255) t.basis := by
    simpa only [lowCopy,copyValue,dest0,Nat.zero_xor] using copy.2.2
  have outside : ∀q,q∉wireBlock w 1 255 → u.basis q=t.basis q := by
    simpa only [lowCopy] using copy.2.1
  have source : regValue (wireBlock w 771 255) u.basis=regValue (wireBlock w 771 255) t.basis := by
    apply regValue_congr
    intro q hq
    exact outside q (List.disjoint_left.mp
      (block_disjoint w hn 771 255 1 255 (by omega) (by omega) (by omega)) hq)
  have equality := value.trans source.symm
  rw [←wireBlock_append w 1 3 252,←wireBlock_append w 771 3 252,
    regValue_append,regValue_append,wireBlock_length,wireBlock_length] at equality
  have lowA := regValue_lt (wireBlock w 1 3) u.basis
  have lowB := regValue_lt (wireBlock w 771 3) u.basis
  rw [wireBlock_length] at lowA lowB
  have upper : regValue (wireBlock w 4 252) u.basis=regValue (wireBlock w 774 252) u.basis := by
    norm_num only [Nat.reducePow] at equality lowA lowB
    omega
  have top : u.basis (w 256)=false := by
    rw [outside _ (block_not_mem w hn 256 1 255 (by omega) (by omega) (by omega))]
    exact (regValue_zero _ _).mp cleanT _ (List.mem_map.mpr ⟨256,by simp [List.mem_range'_1],rfl⟩)
  have topValue : regValue (wireBlock w 256 1) u.basis=0 := by
    simp [one_block,regValue,top]
  rw [front,desired_value,←wireBlock_append w 4 252 1,regValue_append,topValue,
    Nat.mul_zero,Nat.add_zero]
  exact upper.symm

theorem hReceiver_after_forward (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (u : State) (mF mI : List Bool)
    (hc : ∀q∈wireBlock w 1540 252,u.basis q=false)
    (cin : u.basis (w 1797)=false)
    (known : mappedValue (desired w) u.basis=regValue (wireBlock w 4 253) u.basis) :
    run (hReceiver w) mI (run (hAdd w false) mF u)=u := by
  let v := run (hAdd w false) mF u
  have forward := hAdd_spec w false u mF (h_inputs_nd w hn) (h_sources_fresh w hn false) hc
  have carryAway (q : Wire) (hq : q∈wireBlock w 1540 252) : q∉wireBlock w 4 253 :=
    List.disjoint_right.mp (block_disjoint w hn 4 253 1540 252 (by omega) (by omega) (by omega)) hq
  have vc : ∀q∈wireBlock w 1540 252,v.basis q=false := by
    intro q hq
    exact (forward.2.1 q (carryAway q hq)).trans (hc q hq)
  have cancel := hAdd_cancel w u mF mI (h_inputs_nd w hn)
    (fun i => h_sources_fresh w hn i)
    (block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega)) hc cin
  have inverseSpec := mappedAdd_correct (hBits w true) (wireBlock w 4 253)
    (wireBlock w 1540 252) (w 1797) (h_inputs_nd w hn) (h_sources_fresh w hn true)
    (by simp [hBits_length,wireBlock_length]) (by simp [wireBlock_length]) v mI vc
  have sum : (mappedValue (hBits w true) v.basis+regValue (wireBlock w 4 253) v.basis+
      (v.basis (w 1797)).toNat)%2^253=regValue (wireBlock w 4 253) u.basis := by
    have value := inverseSpec.2.2
    rw [← hAdd] at value
    rw [cancel] at value
    simpa only [wireBlock_length] using value.symm
  have witness : mappedValue (desired w) v.basis=mappedValue (desired w) u.basis := by
    apply mappedValue_congr
    intro q hq
    have fresh := desired_fresh w hn q hq
    exact forward.2.1 q (fun bad => fresh (by simp [bad]))
  have ready : mappedValue (desired w) v.basis=
      (mappedValue (hBits w true) v.basis+regValue (wireBlock w 4 253) v.basis+
        (v.basis (w 1797)).toNat)%2^253 := witness.trans (known.trans sum.symm)
  rw [hReceiver_eq w hn v mI vc ready]
  exact cancel

end ECDSAAdd.Arithmetic.NativeFirstKnown

#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.front_known_sum
#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.hReceiver_after_forward
