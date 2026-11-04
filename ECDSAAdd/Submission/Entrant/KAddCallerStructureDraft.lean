import ECDSAAdd.Submission.Entrant.AdderSpineBridgeDraft
import ECDSAAdd.Arithmetic.PoolLayout
import ECDSAAdd.Arithmetic.SkywalkPool

/-! Private structural decomposition/support/cost module. No real MF caller premise is discharged. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.KAddCallerBridgeResearch
open Arithmetic RecordedQuantum Challenge HighOutputTailStructuredResearch AdderSpineBridgeResearch

-- Keep support/cost proof elaboration from eagerly expanding whole program wire sets.
attribute [local irreducible] ECDSAAdd.wires

/-- This is literally both E1Merge.kAddM and E1Reflected.kAddM. -/
def literalKAdd (w : Nat→Wire) : Program :=
  mappedAdd (mappedRead (wireBlock w 0 258) false) (wireBlock w 770 258)
    (wireBlock w 1540 257) (w 1797)

def P (w : Nat→Wire) : Program :=
  adderPrefix (wireBlock w 0 256) (wireBlock w 770 256) (wireBlock w 1540 256) (w 1797)

def R (w : Nat→Wire) : Program :=
  adderSuffix (wireBlock w 0 256) (wireBlock w 770 256) (wireBlock w 1540 256) (w 1797)

def lowPorts (w : Nat→Wire) : List Wire :=
  spinePorts (wireBlock w 0 256) (wireBlock w 770 256) (wireBlock w 1540 256) (w 1797)

def flagKAdd (w : Nat→Wire) : Program :=
  P w++HighOutputFlagResearch.newFlagAt (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027)++R w

def zeroKAdd (w : Nat→Wire) : Program :=
  P w++newLeafAt false (w 256) (w 1026) (w 1795) (w 257) (w 1027)++R w

private theorem lastCarry_cat (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs ++ ys) cin = lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => exact ih x

/-- Split the final carry by one list append instead of reducing 256 entries. -/
theorem literal_split (w : Nat→Wire) :
    literalKAdd w=P w++oldLeafAt (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)++R w := by
  have hx : wireBlock w 0 258=wireBlock w 0 256++[w 256,w 257] := by
    rw [←wireBlock_append w 0 256 2]
    rfl
  have hy : wireBlock w 770 258=wireBlock w 770 256++[w 1026,w 1027] := by
    rw [←wireBlock_append w 770 256 2]
    rfl
  have hc : wireBlock w 1540 257=wireBlock w 1540 256++[w 1796] := by
    rw [←wireBlock_append w 1540 256 1]
    rfl
  have lastBlock : wireBlock w 1540 256 = wireBlock w 1540 255 ++ [w 1795] := by
    rw [←wireBlock_append w 1540 255 1]
    rfl
  have last : lastCarry (wireBlock w 1540 256) (w 1797)=w 1795 := by
    rw [lastBlock,lastCarry_cat]
    rfl
  rw [literalKAdd,read_add,hx,hy,hc]
  simpa only [P,R,last] using add_split
    (wireBlock w 0 256) (wireBlock w 770 256) (wireBlock w 1540 256)
    (w 1797) (w 256) (w 257) (w 1026) (w 1027) (w 1796)
    (by simp [wireBlock_length]) (by simp [wireBlock_length])

theorem low_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉lowPorts w := by
  intro h
  simp only [lowPorts,spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e:=hinj h
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji
    subst j
    simp only [List.mem_range'_1] at hj
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji
    subst j
    simp only [List.mem_range'_1] at hj
    omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji
    subst j
    simp only [List.mem_range'_1] at hj
    omega

theorem P_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉wires (P w) := by
  intro h
  exact low_avoid w hinj i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section RSupportWireOpaque

theorem R_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉wires (R w) := by
  intro h
  have support := suffix_support (wireBlock w 0 256) (wireBlock w 770 256)
    (wireBlock w 1540 256) (w 1797)
  exact low_avoid w hinj i hi (List.mem_toFinset.mp (support h))
end RSupportWireOpaque

theorem tail_nd (w : Nat→Wire) (hinj : Function.Injective w) :
    [w 1028,w 256,w 1026,w 1795,w 257,w 1027,w 1796].Nodup := by
  exact List.Nodup.map hinj (by decide : [1028,256,1026,1795,257,1027,1796].Nodup)

/-- A post-word value/division fact gives its actual high physical bit.
The original MF supplies postWord, not an unrelated abstract integer bound. -/
theorem top_from_div (w : Nat→Wire) (s : BasisState) (W : Nat) (flag : Bool)
    (postWord : regValue (wireBlock w 770 258) s=W) (hdiv : W/2^257=flag.toNat) :
    s (w 1027)=flag := by
  have h:=regValue_bit (wireBlock w 770 258) 257 0 s (by simp [wireBlock_length])
  have port : (wireBlock w 770 258).getD 257 0=w 1027 := by rfl
  rw [port,postWord,hdiv] at h
  cases hs : s (w 1027) <;> cases flag <;> simp [hs] at h ⊢

theorem flag_counts (w : Nat→Wire) :
    toffoliCount (literalKAdd w)=toffoliCount (flagKAdd w)+1 ∧
    measurementCount (literalKAdd w)=measurementCount (flagKAdd w) ∧
    gateSlots (literalKAdd w)=gateSlots (flagKAdd w)+5 := by
  have o:=HighOutputTailStructuredResearch.counts false (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
  have n:=HighOutputFlagResearch.counts (w 1028) (w 256) (w 1026) (w 1795) (w 257) (w 1027)
  have os:=HighOutputTailStructuredResearch.slots false (w 256) (w 1026) (w 1795) (w 257) (w 1027) (w 1796)
  simp only [literal_split,flagKAdd,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

/-- Bounded alternative rooted in the actual real-caller pool Nodup premise.
The old globally injective research theorem above is retained unchanged. -/
theorem low_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉lowPorts w := by
  have ir : i<1798 := by omega
  intro h
  simp only [lowPorts,spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e := skywalkPool_index_inj w hn i 1797 ir (by decide) h
    omega
  all_goals
    obtain ⟨j,hj,hji⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have jr : j<1798 := by omega
    have e := skywalkPool_index_inj w hn j i jr ir hji
    omega

theorem P_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉wires (P w) := by
  intro h
  exact low_avoid_pool w hn i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section RPoolSupportWireOpaque

theorem R_avoid_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) (i : Nat)
    (hi : i=1796 ∨ i=1028 ∨ i=1027) : w i∉wires (R w) := by
  intro h
  have support := suffix_support (wireBlock w 0 256) (wireBlock w 770 256)
    (wireBlock w 1540 256) (w 1797)
  exact low_avoid_pool w hn i hi (List.mem_toFinset.mp (support h))
end RPoolSupportWireOpaque

theorem tail_nd_pool (w : Nat→Wire) (hn : (skywalkPoolWires w).Nodup) :
    [w 1028,w 256,w 1026,w 1795,w 257,w 1027,w 1796].Nodup := by
  have neq (i j : Nat) (hi : i<1798) (hj : j<1798) (hne : i≠j) : w i≠w j := by
    intro he
    exact hne (skywalkPool_index_inj w hn i j hi hj he)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals exact neq _ _ (by decide) (by decide) (by decide)

end ECDSAAdd.Entrant.KAddCallerBridgeResearch
