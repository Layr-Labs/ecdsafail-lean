import ECDSAAdd.Arithmetic.MappedCompressedConversionNaturality
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation FieldRename

private def converterSite (q : Nat) : Prop :=
  (770 ≤ q ∧ q ≤ 1027) ∨ (1540 ≤ q ∧ q ≤ 1797) ∨ (2056 ≤ q ∧ q ≤ 2311)

private theorem site_fixed (q : Nat) (h : converterSite q) : allPlaced q=base q := by
  change pi0 q+16=q+16
  rw [pi0_outside q]
  unfold converterSite zeroRegion workRegion holeRegion at *
  omega

private theorem block_fixed (start len : Nat)
    (hs : ∀q,start ≤ q → q < start+len → converterSite q) :
    wireBlock allPlaced start len=wireBlock base start len := by
  unfold wireBlock
  apply List.map_congr_left
  intro q hq
  have bound := List.mem_range'_1.mp hq
  exact site_fixed q (hs q bound.1 bound.2)

theorem target_conversion_placement :
    balancedSharedTargetConvert allPlaced=balancedSharedTargetConvert base := by
  have low := block_fixed 2056 255 (by intro q lo hi; unfold converterSite; omega)
  have carry := block_fixed 1540 255 (by intro q lo hi; unfold converterSite; omega)
  simp only [balancedSharedTargetConvert,low,carry,
    site_fixed 2311 (by unfold converterSite; omega),
    site_fixed 1797 (by unfold converterSite; omega),
    site_fixed 1027 (by unfold converterSite; omega),
    site_fixed 1796 (by unfold converterSite; omega)]

theorem source_conversion_placement :
    balancedSharedSourceConvert allPlaced=balancedSharedSourceConvert base := by
  have low := block_fixed 770 255 (by intro q lo hi; unfold converterSite; omega)
  have carry := block_fixed 1540 255 (by intro q lo hi; unfold converterSite; omega)
  simp only [balancedSharedSourceConvert,low,carry,
    site_fixed 1025 (by unfold converterSite; omega),
    site_fixed 1797 (by unfold converterSite; omega),
    site_fixed 1027 (by unfold converterSite; omega),
    site_fixed 1796 (by unfold converterSite; omega)]

/-- Boundary converters never borrow the omitted work positions or encoded
holes. The actual placement is therefore identical as a complete program. -/
theorem converterPair_placement (canonical : Bool) :
    renameProgram allPlaced (converterPair canonical)=converterPairAt base canonical := by
  rw [converterPair_natural]
  cases canonical <;> simp only [converterPairAt,Bool.false_eq_true,if_false,if_true,
    target_conversion_placement,source_conversion_placement]

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.converterPair_placement
