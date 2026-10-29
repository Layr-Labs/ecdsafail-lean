import ECDSAAdd.Submission.Entrant.LaneAvoid
import ECDSAAdd.Submission.Entrant.WKernelRes

/-! `ArithAvoid` for the narrowed arithmetic: its ticks are prefixes of the
original tick layouts, so the same labels are avoided. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.W
open ECDSAAdd.Arithmetic MappedCompressed CompressedAllocation Secp256k1
attribute [local irreducible] wires compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
  NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse

theorem tick_layout_avoid (i : Nat) (hi : i < 512) :
    ∀ q ∈ (compactSkywalkTickLayout base i).wires.toFinset, goodW q := by
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
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  by_cases hz : i=0
  · simp only [skywalkPoolPreviousId,if_pos hz] at h; exact integer_good _ (by omega) (by omega)
  · simp only [skywalkPoolPreviousId,if_neg hz] at h; exact integer_good _ (by omega) (by omega)

theorem ticks_avoid (i : Nat) (hi : i < 512) :
    Avoid (compactSkywalkTick base i) ∧ Avoid (compactSkywalkReverseTick base i) :=
  ⟨fun q hq => tick_layout_avoid i hi q (compactSkywalkTick_support base i hi base_pool_nodup hq),
   fun q hq => tick_layout_avoid i hi q (compactSkywalkReverseTick_support base i hi base_pool_nodup hq)⟩

theorem integer_avoid (i n : Nat) (h : i+n ≤ 512) :
    Avoid (compressedCompactForward base i n) ∧ Avoid (compressedCompactReverse base i n) := by
  induction n generalizing i with
  | zero => simp only [compressedCompactForward,compressedCompactReverse]; exact ⟨avoid_nil, avoid_nil⟩
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have tick := ticks_avoid i (by omega)
    have codec := delayed_codec_avoid i (by omega)
    simp only [compressedCompactForward,compressedCompactReverse,avoid_append]
    exact ⟨⟨⟨tick.1,codec.1⟩,rest.1⟩,⟨⟨rest.2,codec.2⟩,tick.2⟩⟩

theorem kernel_avoid (divide : Bool) : Avoid (kernel divide) := by
  have native := NativeFirstDirect.prefix_support base
  have integer := integer_avoid 1 511 (by omega)
  have known := NativeFirstKnown.inverse_support base
  simp only [kernel,avoid_append]
  exact ⟨⟨⟨⟨⟨⟨fun q hq => prefixSites_avoid q (native.1 hq),integer.1⟩,clear_avoid⟩,
    laneSegment_avoid divide⟩,clear_avoid⟩,integer.2⟩,
    fun q hq => prefixSites_avoid q (known hq)⟩

theorem controlled_avoid (divide : Bool) : Avoid (controlled divide) := by
  have xs : wireBlock base 770 256 = base 770 :: base 771 :: wireBlock base 772 254 := by
    simp [wireBlock, List.range'_succ]
  have cs : wireBlock base 0 255 = base 0 :: wireBlock base 1 254 := by
    simp [wireBlock, List.range'_succ]
  have good : ∀ q ∈ base 770 :: base 771 :: wireBlock base 772 254 ++ base 0 :: wireBlock base 1 254 ++
      [base 2411], goodW q := by
    intro q hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, wireBlock, List.mem_map,
      List.mem_range'_1] at hq
    rcases hq with ((rfl|rfl|⟨i,hi,rfl⟩)|(rfl|⟨i,hi,rfl⟩))|rfl
    all_goals apply base_good; unfold badIdx; omega
  have cmp := zeroCompare_avoid _ _ _ _ _ (base 2313) (base 2411) good
  have mask : Avoid (maskedConstant (base 2411) (wireBlock base 770 256) 1) := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ hq)
    rw [xs] at h
    exact good q (by simp only [List.mem_cons, List.mem_append] at h ⊢; tauto)
  simp only [controlled, directZeroControlled, directZeroDivisorEnter, directZeroDivisorLeave,
    avoid_append, xs, cs]
  rw [xs] at mask
  exact ⟨⟨cmp, mask⟩, kernel_avoid divide, mask, cmp⟩

end ECDSAAdd.Entrant.W
