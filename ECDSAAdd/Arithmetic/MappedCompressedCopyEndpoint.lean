import ECDSAAdd.Arithmetic.MappedCompressedConversionEncoding
import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryFrames
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedAllocation CompressedFieldSupport FieldRename
attribute [local irreducible] run wires copyRegister allGroupEncode

def copyPairAt (w : Nat → Wire) : Program :=
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a

theorem copyPair_natural (f : Nat → Wire) :
    renameProgram f (copyPairAt id)=copyPairAt f := by
  simp only [copyPairAt,copyRegister_natural,skywalkShared_field_z,wireBlock_map,
    Option.map_none,Function.comp_id]
  rfl

private theorem block_fixed (start len : Nat)
    (hs : ∀q,start ≤ q → q < start+len → ¬zeroRegion q) :
    wireBlock allPlaced start len=wireBlock base start len := by
  unfold wireBlock
  apply List.map_congr_left
  intro q hq
  have range := List.mem_range'_1.mp hq
  change pi0 q+16=q+16
  rw [pi0_outside q (hs q range.1 range.2)]

/-- Both full257-bit copy words lie outside every reassigned role. -/
theorem copyPair_placement : renameProgram allPlaced (copyPairAt id)=copyPairAt base := by
  rw [copyPair_natural]
  have z := block_fixed 2056 257
    (by intro q lo hi; unfold zeroRegion workRegion holeRegion; omega)
  have a := block_fixed 770 257
    (by intro q lo hi; unfold zeroRegion workRegion holeRegion; omega)
  simp only [copyPairAt,skywalkShared_field_z]
  change copyRegister none (wireBlock allPlaced 2056 257) (wireBlock allPlaced 770 257)=
    copyRegister none (wireBlock base 2056 257) (wireBlock base 770 257)
  rw [z,a]

theorem copyPair_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState) (X Y : Nat) :
    Triple (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X Y)
      (copyPairAt base)
      (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X (Y^^^X)) := by
  have widths := skywalkShared_field_widths base
  have length : (skywalkSharedField base).z.length=(skywalkSharedField base).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,widths.core.low,widths.core.a]
  have nd := skywalkShared_field_nodup base hn
  have pair : ((skywalkSharedField base).z++(skywalkSharedField base).a).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have full := List.nodup_iff_count.mp nd q
    simp only [ModInPlaceLayout.wires,List.count_append] at full ⊢
    omega
  have dis := (List.nodup_append'.mp pair).2.2
  intro s m input
  obtain ⟨phase,keep,value⟩ := copyRegister_correct none (skywalkSharedField base).z
    (skywalkSharedField base).a length pair (by simp) s m
  refine ⟨phase,PairFrame.update_dst _ _ origin s.basis _ X Y _ dis input keep ?_⟩
  simpa only [copyValue,input.1,input.2.1] using value

/-- Exact retained endpoint operations: populate a clean source, or erase
the equal source after division. Incoming phase and every outsider restore. -/
theorem copyPair_fill (hn : (skywalkSharedWires base).Nodup) (origin : BasisState) (X : Fp) :
    Triple (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val 0)
      (copyPairAt base)
      (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val X.val) := by
  simpa only [Nat.zero_xor] using copyPair_frame hn origin X.val 0

theorem copyPair_clear (hn : (skywalkSharedWires base).Nodup) (origin : BasisState) (X : Fp) :
    Triple (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val X.val)
      (copyPairAt base)
      (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin X.val 0) := by
  simpa only [Nat.xor_self] using copyPair_frame hn origin X.val X.val

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.copyPair_placement
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.copyPair_fill
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.copyPair_clear
