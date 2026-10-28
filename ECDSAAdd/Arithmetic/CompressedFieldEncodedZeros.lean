import ECDSAAdd.Arithmetic.CompressedFieldGroupedReplay
import ECDSAAdd.Arithmetic.CompressedAllocationSwitch
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedAllocation
attribute [local irreducible] run wires allGroupEncode compressedHistoryEncode

/-- The actual final MX instruction clears codec site3 for every input.
Legality is needed for phase/invertibility, but not for this zero output. -/
private theorem pack_hole_zero (s : State) (m : List Bool) :
    (run TranscriptCodec3.pack m s).basis 3 = false := by
  have layout : TranscriptCodec3.pack = TranscriptCodec3.pack.dropLast++
      [.measureX 3 [] [.CZ 1 0]] := by rfl
  rw [layout,run_append,run_take]
  simp only [run,measureAndCorrect,correct_basis,writeBit,Function.update_self]

private theorem placed_hole_zero (f : Fin 6 → Wire) (hn : Function.Injective f)
    (hl : ∀ j,6 ≤ f j) (s : State) (m : List Bool) :
    (run (TranscriptCodec3.encode f) m s).basis (f 3) = false := by
  let e := TranscriptCodec3.placement f
  have eq := run_rename e e.injective TranscriptCodec3.pack m s
  have atThree := congrArg (fun t : State => t.basis 3) eq
  have site : e 3 = f 3 := TranscriptCodec3.placement_apply f hn hl 3
  change (run (TranscriptCodec3.encode f) m s).basis (e 3) =
    (run TranscriptCodec3.pack m (pullState e s)).basis 3 at atThree
  rw [site] at atThree
  exact atThree.trans (pack_hole_zero (pullState e s) m)

/-- Every hole is cleared by its own actual encoder and kept by every
other encoder. This statement is universal, even before assuming legal tape. -/
theorem allGroupEncode_holes_zero (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (n : Nat) (bound : 3*n ≤ 512) (s : State) (m : List Bool)
    (j : Nat) (hj : j < n) :
    (run (allGroupEncode w n) m s).basis (w (H j)) = false := by
  induction n generalizing m j with
  | zero => omega
  | succ n ih =>
    let before := run (allGroupEncode w n) (m.take (measurementCount (allGroupEncode w n))) s
    rw [allGroupEncode,run_append]
    by_cases current : j=n
    · subst j
      have zero := placed_hole_zero (compressedHistoryMap w (3*n))
        (compressedHistoryMap_injective w hn (3*n) (by omega))
        (compressedHistoryMap_above w (3*n) (by omega) hlo) before
        (m.drop (measurementCount (allGroupEncode w n)))
      simpa only [compressedHistoryEncode,compressedHistoryMap,compressedHistoryId,H,
        Nat.reduceMod,Nat.reduceDiv,Nat.reduceEqDiff,if_false] using zero
    · have older : j < n := by omega
      have old := ih (by omega) (m.take (measurementCount (allGroupEncode w n))) j older
      have dis := compressedHistory_windows_disjoint w hn hlo (3*j) (3*n) (by omega) (by omega) (by omega)
      have site : w (H j) ∈ wires (compressedHistoryEncode w (3*j)) := by
        simpa only [compressedHistoryMap,compressedHistoryId,H,Nat.reduceMod,Nat.reduceDiv,
          Nat.reduceEqDiff,if_false] using compressedHistory_site_mem w hn hlo (3*j) (by omega) 3
      have keep := run_preserves_outside (compressedHistoryEncode w (3*n))
        (m.drop (measurementCount (allGroupEncode w n))) before (w (H j))
        (fun h => Finset.disjoint_left.mp dis site h)
      exact keep.trans old

/-- Existing raw field work cleanliness is transported by the field frame;
encoding never touches the170 work positions. -/
theorem encoded_work_zero (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (base : BasisState) (env : Env w base) (X Y : Fp) (s : State)
    (frame : EncodedFieldFrame w sign base X Y s)
    (j : Nat) (hj : j < 170) : s.basis (w (W j)) = false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have rawEnv := pair_env w sign hn base raw.basis _ _ env rawFrame
  have zero := OffsetCleanupBorrowedCaller.maskBit_zero w raw.basis rawEnv.1 (W j)
    (by unfold W; omega) (by unfold W; omega)
  have pool := skywalkShared_integer_nodup w hn
  have support := compressedPrefix_history_support w pool hlo 512 (by decide)
  have away : w (W j) ∉ wires (allGroupEncode w 170) := by
    rw [←encode_prefix_512]
    intro hq
    have member := List.mem_toFinset.mp (support hq)
    rcases List.mem_append.mp member with member|member
    all_goals
      obtain ⟨k,hk,eq⟩ := List.mem_map.mp member
      simp only [List.mem_range'_1] at hk
      have same := skywalkPool_index_inj w pool k (W j) (by omega) (by unfold W; omega) eq
      unfold W at same
      omega
  rw [encoded]
  exact (run_preserves_outside (allGroupEncode w 170) [] raw (w (W j)) away).trans zero

/-- Derived universal allocation boundary for every encoded field frame.
No extra all-zero bank hypothesis is added to the replay/caller contract. -/
theorem encoded_zero_region (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (base : BasisState) (env : Env w base) (X Y : Fp) (s : State)
    (frame : EncodedFieldFrame w sign base X Y s) :
    ∀ q,zeroRegion q → (pullState w s).basis q = false := by
  intro q hq
  rcases hq with work|hole
  · have j : q = W (q-515) := by unfold workRegion W at *; omega
    have bound : q-515 < 170 := by unfold workRegion at work; omega
    rw [j]
    exact encoded_work_zero w sign hn hlo base env X Y s frame _ bound
  · have j : q = H ((q-1029)/3) := by unfold holeRegion H at *; omega
    have bound : (q-1029)/3 < 170 := by unfold holeRegion at hole; omega
    obtain ⟨raw,_,_,encoded⟩ := frame
    rw [encoded,j]
    exact allGroupEncode_holes_zero w (skywalkShared_integer_nodup w hn) hlo 170 (by decide) raw [] _ bound

/-- Switching placements at an encoded packet boundary is justified by
that invariant itself; phase and every live field coordinate are preserved. -/
theorem run_switch_encoded_boundary (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (base : BasisState) (env : Env w base) (X Y : Fp) (s actual : State)
    (frame : EncodedFieldFrame w sign base X Y s)
    (a j : Nat) (ha : a < 170) (hj : j < 170) (program : Program) (m : List Bool)
    (map : pullState (pi a) actual = pullState w s) :
    pullState (pi j) (run (renameProgram (pi j) program) m actual) =
      run program m (pullState w s) :=
  run_switch_packet_placements a j ha hj actual (pullState w s) program m map
    (encoded_zero_region w sign hn hlo base env X Y s frame)

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.allGroupEncode_holes_zero
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.encoded_work_zero
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.encoded_zero_region
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.run_switch_encoded_boundary
