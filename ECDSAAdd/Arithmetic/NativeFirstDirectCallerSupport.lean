import ECDSAAdd.Arithmetic.NativeFirstDirectCallerProgram

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open MappedCompressed CompressedAllocation
attribute [local irreducible] wires callerKernel callerControlled forward inverse NativeFirstKnown.inverse
  compressedCompactForward compressedCompactReverse selectedFieldSegment

theorem prefix_slots : (prefixSites base).toFinset ⊆ slots.toFinset := by
  intro q hq
  simp only [prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      apply slot_mem
      · unfold live; omega
      · unfold omitted; omega
    | apply slot_mem
      · unfold live; omega
      · unfold omitted; omega

theorem caller_kernel_support (divide : Bool) :
    wires (callerKernel divide) ⊆ slots.toFinset := by
  have hpfx := prefix_support base
  have ints := integer_support 1 511 (by omega)
  simp only [callerKernel,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨hpfx.1.trans prefix_slots,ints.1,clear_support,selectedFieldSegment_support divide,
    clear_support,ints.2,(NativeFirstKnown.inverse_support base).trans prefix_slots⟩

theorem caller_controlled_support (divide : Bool) :
    wires (callerControlled divide) ⊆ slots.toFinset := by
  have z := directZeroDivisor_wires (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411)
  have zero : (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255)).toFinset
      ⊆ slots.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at hq
    rcases hq with rfl|rfl|(h|h)
    all_goals first
      | obtain ⟨i,hi,rfl⟩ := h
        apply slot_mem
        · unfold live; omega
        · unfold omitted; omega
      | apply slot_mem
        · unfold live; omega
        · unfold omitted; omega
  have wrap := z.trans zero
  rw [wires_append,Finset.union_subset_iff] at wrap
  simp only [callerControlled,directZeroControlled,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨wrap.1,caller_kernel_support divide,wrap.2⟩

/-- Includes the existing 521 resident coordinate/control sites. This is a
static union and allocation ceiling, not an exact peak-live measurement. -/
theorem caller_total_site_bound (divide : Bool) :
    (wires (callerControlled divide) ∪ resident.toFinset).card ≤1899 := by
  have h : wires (callerControlled divide) ∪ resident.toFinset ⊆ slots.toFinset :=
    Finset.union_subset (caller_controlled_support divide) resident_support
  have card := Finset.card_le_card h
  have exactCard : slots.toFinset.card=1899 := by
    rw [List.toFinset_card_of_nodup slots_nodup,slots_length]
  exact exactCard ▸ card

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.prefix_slots
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.caller_kernel_support
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.caller_controlled_support
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.caller_total_site_bound
