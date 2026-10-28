import ECDSAAdd.Framework.CertifiedProgram
import ECDSAAdd.Arithmetic.KnownOutputAdder
import ECDSAAdd.Arithmetic.NativeFirstDirectInverseFinish

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.NativeFirstKnown
open NativeFirstDirect
attribute [local irreducible] KnownOutputAdder.program mappedAdd wires run
  NativeFirstDirect.inverse NativeFirstDirect.forward inverseUnmiddle inverseBack

def desired (w : Nat → Wire) : List MappedBit :=
  mappedRead (wireBlock w 774 252) false++[{wire:=none,flip:=false}]

def hReceiver (w : Nat → Wire) : Program :=
  sealedProgram (KnownOutputAdder.program (hBits w true) (wireBlock w 4 253) (desired w)
    (wireBlock w 1540 252) (w 1797))

/-- Specialized clean-caller inverse; the unrestricted inverse is unchanged. -/
def inverse (w : Nat → Wire) : Program :=
  kAdd w true++inverseUnmiddle w++hReceiver w++inverseBack w

attribute [local irreducible] inverse

theorem desired_length (w : Nat → Wire) : (desired w).length=253 := by
  simp [desired,mappedRead,wireBlock_length]

theorem desired_value (w : Nat → Wire) (s : BasisState) :
    mappedValue (desired w) s=regValue (wireBlock w 774 252) s := by
  simp [desired,mappedValue_append,mappedRead_value,mappedValue,MappedBit.value]

theorem desired_wires (w : Nat → Wire) :
    mappedWires (desired w)=wireBlock w 774 252 := by
  simp only [desired,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    Option.toList_none,List.nil_append,List.append_nil]
  exact mappedRead_wires _ false

theorem desired_fresh (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    ∀q∈mappedWires (desired w),q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252) := by
  intro q hq
  rw [desired_wires] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [List.mem_cons,List.mem_append,not_or]
  exact ⟨index_ne w hn i 1797 (by omega) (by omega) (by omega),
    block_not_mem w hn i 4 253 (by omega) (by omega) (by omega),
    block_not_mem w hn i 1540 252 (by omega) (by omega) (by omega)⟩

theorem hReceiver_counts (w : Nat → Wire) :
    toffoliCount (hReceiver w)=0 ∧ measurementCount (hReceiver w)=252 := by
  have h := KnownOutputAdder.program_counts (hBits w true) (desired w)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
    (by simp [hBits_length,wireBlock_length])
    (by simp [desired_length,wireBlock_length]) (by simp [wireBlock_length])
  simpa only [hReceiver,sealedProgram_eq,wireBlock_length] using h

theorem inverse_counts (w : Nat → Wire) :
    toffoliCount (inverse w)=256 ∧ measurementCount (inverse w)=508 := by
  have k := kAdd_counts w true
  have h := hReceiver_counts w
  have c := lowCopy_counts w
  have r := rotate_counts (wireBlock w 770 258)
  simp [inverse,inverseUnmiddle,inverseBack,toffoliCount_append,measurementCount_append,
    k.1,k.2,h.1,h.2,c.1,c.2,r.2.2.1,r.2.2.2,toffoliCount,measurementCount]

theorem hReceiver_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (hc : ∀q∈wireBlock w 1540 252,s.basis q=false)
    (known : mappedValue (desired w) s.basis=
      (mappedValue (hBits w true) s.basis+regValue (wireBlock w 4 253) s.basis+
        (s.basis (w 1797)).toNat)%2^253) :
    run (hReceiver w) m s=run (hAdd w true) m s := by
  rw [hReceiver,sealedProgram_run]
  apply KnownOutputAdder.program_eq_mappedAdd _ _ _ _ _ (h_inputs_nd w hn)
    (h_sources_fresh w hn true) (desired_fresh w hn)
    (by simp [hBits_length,wireBlock_length])
    (by simp [desired_length,wireBlock_length]) (by simp [wireBlock_length]) s m hc
  exact KnownOutputAdder.ready_of_value _ _ _ _ _
    (by simp [hBits_length,wireBlock_length])
    (by simp [desired_length,wireBlock_length]) (by simpa [wireBlock_length] using known)

attribute [local irreducible] hAdd kAdd lowCopy rotateLeft rotateRight hReceiver

private theorem block_inside (w : Nat → Wire) (a n : Nat)
    (ha : a+n≤257 ∨ (770≤a ∧ a+n≤1028) ∨ (1540≤a ∧ a+n≤1796)) :
    ∀q∈wireBlock w a n,q∈prefixSites w := by
  intro q hq
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have mem (b m : Nat) (hb : b ≤ i ∧ i < b+m) : q∈wireBlock w b m := by
    exact List.mem_map.mpr ⟨i,by simpa only [List.mem_range'_1] using hb,he⟩
  simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases ha with h|h|h
  · exact Or.inl (Or.inl (Or.inl (mem 0 257 (by omega))))
  · exact Or.inl (Or.inl (Or.inr (mem 770 258 (by omega))))
  · exact Or.inl (Or.inr (mem 1540 256 (by omega)))

theorem hReceiver_support (w : Nat → Wire) :
    wires (hReceiver w)⊆(prefixSites w).toFinset := by
  intro q hq
  rw [hReceiver,(sealedProgram_cost _).2.2] at hq
  have h := KnownOutputAdder.program_support (hBits w true) (desired w)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797) hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with (((h|h)|h)|h)|h
  · rw [hBits_wire w true q h]
    simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inl True.intro)
  · rw [desired_wires] at h
    exact block_inside w 774 252 (by omega) q h
  · exact block_inside w 4 253 (by omega) q h
  · exact block_inside w 1540 252 (by omega) q h
  · subst q
    simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr True.intro)

theorem inverse_support (w : Nat → Wire) :
    wires (inverse w)⊆(prefixSites w).toFinset := by
  have old := (prefix_support w).2
  have hK : wires (kAdd w true)⊆wires (NativeFirstDirect.inverse w) := by
    intro q hq
    simp only [NativeFirstDirect.inverse,wires_append,Finset.mem_union]
    tauto
  have hU : wires (inverseUnmiddle w)⊆wires (NativeFirstDirect.inverse w) := by
    intro q hq
    simp only [inverseUnmiddle,wires_append,Finset.mem_union] at hq
    simp only [NativeFirstDirect.inverse,wires_append,Finset.mem_union]
    tauto
  have hB : wires (inverseBack w)⊆wires (NativeFirstDirect.inverse w) := by
    intro q hq
    simp only [inverseBack,wires_append,Finset.mem_union] at hq
    simp only [NativeFirstDirect.inverse,wires_append,Finset.mem_union]
    tauto
  intro q hq
  simp only [inverse,wires_append,Finset.mem_union] at hq
  rcases hq with ((hq|hq)|hq)|hq
  · exact old (hK hq)
  · exact old (hU hq)
  · exact hReceiver_support w hq
  · exact old (hB hq)

end ECDSAAdd.Arithmetic.NativeFirstKnown

#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.hReceiver_counts
#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.inverse_counts
#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.hReceiver_eq
#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.inverse_support
