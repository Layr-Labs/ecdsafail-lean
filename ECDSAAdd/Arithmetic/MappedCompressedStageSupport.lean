import ECDSAAdd.Arithmetic.NativeFirstKnownProgram
import ECDSAAdd.Arithmetic.TerminalMappedReplayResources
import ECDSAAdd.Arithmetic.EntryForwardSelectedFieldSegment
import ECDSAAdd.Arithmetic.MappedCompressedFieldReplay
import ECDSAAdd.Arithmetic.LiteralSkywalkSeedPool
import ECDSAAdd.Arithmetic.SkywalkArithmeticCore
import ECDSAAdd.Arithmetic.DirectZeroControlled
import ECDSAAdd.Arithmetic.NativeFirstDirectProgram
import ECDSAAdd.Arithmetic.NativeFirstDirectSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation Secp256k1
attribute [local irreducible] wires compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
  NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse

private theorem base_integer_mem (q : Nat) (h : q < 515 ∨ (770 ≤ q ∧ q < 1798)) :
    base q∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold omitted; omega

private theorem tick_layout_support (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout base i).wires.toFinset⊆slots.toFinset := by
  have width := compactSkywalkTick_width_bounds i hi
  have view : (compactSkywalkTickLayout base i).wires =
      ([skywalkPoolPreviousId i,1028+i,i+compactSkywalkTickPreWidth i,i,770]++
      List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
      List.range' 771 (compactSkywalkTickPreWidth i-1)++
      List.range' 1540 (compactSkywalkTickPreWidth i-1)).map base := by
    change base (skywalkPoolPreviousId i)::base (1028+i)::
      base (i+compactSkywalkTickPreWidth i)::base i::base 770::
      ((compactSkywalkTickLayout base i).ah++(compactSkywalkTickLayout base i).bh++
      wireBlock base 1540 (compactSkywalkTickPreWidth i-1)) = _
    rw [compactSkywalkTick_ah base i hi,compactSkywalkTick_bh base i hi]
    simp [wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [List.mem_toFinset,view] at hq
  obtain ⟨old,h,rfl⟩ := List.mem_map.mp hq
  apply base_integer_mem
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  by_cases hz : i=0
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; omega

theorem ticks_support (i : Nat) (hi : i < 512) :
    wires (compactSkywalkTick base i)⊆slots.toFinset ∧
    wires (compactSkywalkReverseTick base i)⊆slots.toFinset :=
  ⟨(compactSkywalkTick_support base i hi base_pool_nodup).trans (tick_layout_support i hi),
   (compactSkywalkReverseTick_support base i hi base_pool_nodup).trans (tick_layout_support i hi)⟩

private theorem base_codec_support (start : Nat) (hs : start+3 ≤ 512) :
    wires (compressedHistoryEncode base start)⊆slots.toFinset ∧
    wires (compressedHistoryDecode base start)⊆slots.toFinset := by
  have lift (P : Program) (he : P=compressedHistoryEncode base start ∨
      P=compressedHistoryDecode base start) : wires P⊆slots.toFinset := by
    intro q hq
    obtain ⟨u,rfl⟩ := compressedHistory_gate_mem base base_pool_nodup base_above start hs P he q hq
    have region := compressedHistoryId_region start hs u
    apply base_integer_mem
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

private theorem delayed_codec_support (i : Nat) (hi : i < 512) :
    wires (compressedPackAfter base i)⊆slots.toFinset ∧
    wires (compressedDecodeBefore base i)⊆slots.toFinset := by
  cases h : compressedPackDue i
  · simp [compressedPackAfter,compressedDecodeBefore,h,wires]
  · have due := compressedPackDue_true i h
    have support := base_codec_support (i-3) (by omega)
    simpa only [compressedPackAfter,compressedDecodeBefore,h,if_true] using support

theorem integer_support (i n : Nat) (h : i+n ≤ 512) :
    wires (compressedCompactForward base i n)⊆slots.toFinset ∧
    wires (compressedCompactReverse base i n)⊆slots.toFinset := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,compressedCompactReverse,wires]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := ticks_support i (by omega)
    have codec := delayed_codec_support i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,wires_append,
      Finset.union_subset_iff,and_assoc]
    exact ⟨tick.1,codec.1,rest.1,rest.2,codec.2,tick.2⟩

theorem seed_support :
    wires (literalSkywalkSeed (literalSkywalkPoolSeed base) p)⊆slots.toFinset ∧
    wires (literalSkywalkUnseed (literalSkywalkPoolSeed base) p)⊆slots.toFinset := by
  have support := literalSkywalkSeed_support (literalSkywalkPoolSeed base) 258 p
    (literalSkywalkPoolSeed_widths base)
  have lift : (literalSkywalkPoolSeed base).usedWires.toFinset⊆slots.toFinset := by
    intro q hq
    simp only [List.mem_toFinset,literalSkywalkPoolSeed,LiteralSkywalkSeedLayout.usedWires,
      List.mem_cons,List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at hq
    rcases hq with rfl|rfl|((h|h)|h)
    · exact base_integer_mem 1028 (by omega)
    · exact base_integer_mem 1797 (by omega)
    all_goals obtain ⟨old,ho,rfl⟩ := h; exact base_integer_mem old (by omega)
  exact ⟨support.1.trans lift,support.2.trans lift⟩

theorem clear_support : wires (skywalkArithmeticClear base)⊆slots.toFinset := by
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals apply base_integer_mem; omega

private theorem native_prefix_slots :
    (NativeFirstDirect.prefixSites base).toFinset⊆slots.toFinset := by
  intro q hq
  simp only [NativeFirstDirect.prefixSites,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((h|h)|h)|(rfl|rfl)
  all_goals first
    | obtain ⟨i,hi,rfl⟩ := h
      apply slot_mem
      · unfold live; omega
      · unfold omitted; omega
    | apply slot_mem
      · unfold live; omega
      · unfold omitted; omega

/-- Exact first native prefix and independent inverse; the remaining ticks,
codec schedule, and selected field program retain their existing allocation. -/
def kernel (divide : Bool) : Program :=
  NativeFirstDirect.forward base++compressedCompactForward base 1 511++
  skywalkArithmeticClear base++selectedFieldSegment divide++skywalkArithmeticClear base++
  compressedCompactReverse base 1 511++NativeFirstKnown.inverse base

theorem kernel_support (divide : Bool) : wires (kernel divide)⊆slots.toFinset := by
  have native := NativeFirstDirect.prefix_support base
  have integer := integer_support 1 511 (by omega)
  simp only [kernel,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨native.1.trans native_prefix_slots,integer.1,clear_support,
    selectedFieldSegment_support divide,clear_support,integer.2,(NativeFirstKnown.inverse_support base).trans native_prefix_slots⟩

def controlled (divide : Bool) : Program :=
  directZeroControlled (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (kernel divide)

private theorem zero_sites :
    (base 2411::base 2313::(wireBlock base 770 256++wireBlock base 0 255)).toFinset⊆slots.toFinset := by
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,wireBlock,
    List.mem_map,List.mem_range'_1] at hq
  rcases hq with rfl|rfl|(h|h)
  · exact slot_mem 2411 (by unfold live; omega) (by unfold omitted; omega)
  · exact slot_mem 2313 (by unfold live; omega) (by unfold omitted; omega)
  all_goals obtain ⟨old,ho,rfl⟩ := h; apply base_integer_mem; omega

theorem controlled_support (divide : Bool) : wires (controlled divide)⊆slots.toFinset := by
  have z := (directZeroDivisor_wires (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411)).trans zero_sites
  rw [wires_append,Finset.union_subset_iff] at z
  simp only [controlled,directZeroControlled,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨z.1,kernel_support divide,z.2⟩

/-- All resident field data and nine caller selectors are counted, even when
an instruction does not touch one of the selector sites. -/
def resident : List Wire := wireBlock base 770 256++wireBlock base 2056 256++wireBlock base 2400 9

theorem resident_length : resident.length=521 := by simp [resident,wireBlock]

theorem resident_support : resident.toFinset⊆slots.toFinset := by
  intro q hq
  simp only [resident,List.mem_toFinset,List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at hq
  rcases hq with (h|h)|h
  all_goals
    obtain ⟨old,ho,rfl⟩ := h
    apply slot_mem
    · unfold live; omega
    · unfold omitted; omega

theorem total_site_bound (divide : Bool) :
    (wires (controlled divide)∪resident.toFinset).card ≤ 1899 := by
  have sub : wires (controlled divide)∪resident.toFinset⊆slots.toFinset :=
    Finset.union_subset (controlled_support divide) resident_support
  have card := Finset.card_le_card sub
  have exactCard : slots.toFinset.card=1899 := by
    rw [List.toFinset_card_of_nodup slots_nodup,slots_length]
  exact exactCard ▸ card

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.integer_support
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.controlled_support
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.total_site_bound
