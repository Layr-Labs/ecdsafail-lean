import ECDSAAdd.Arithmetic.MappedCompressedStageSupport
import ECDSAAdd.Arithmetic.MappedCompressedReplayCounts
import ECDSAAdd.Arithmetic.CompressedCompactRestore

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1
attribute [local irreducible] logicalCell dblInPlace halfInPlace copyRegister
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] compactSkywalkForward compressedCompactForward compressedCompactReverse
attribute [local irreducible] toffoliCount measurementCount

private theorem renameT (f : Wire → Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem renameM (f : Wire → Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem integer512_counts :
    toffoliCount (compressedCompactForward base 0 512)=198142 ∧
    measurementCount (compressedCompactForward base 0 512)=98858 ∧
    toffoliCount (compressedCompactReverse base 0 512)=198312 ∧
    measurementCount (compressedCompactReverse base 0 512)=98688 := by
  have recurrence := compactSkywalkForward_counts base base_pool_nodup 0 512 (by omega)
  have exactCharges := compactSkywalkForward_512_counts base base_pool_nodup
  have ht : compactSkywalkForwardT 0 512=197632 := recurrence.1.symm.trans exactCharges.1
  have hm : compactSkywalkForwardM 0 512=98688 := recurrence.2.symm.trans exactCharges.2
  have packets : compressedPackCount 0 512=170 := by rfl
  have forward := compressedCompactForward_counts base base_pool_nodup 0 512 (by omega)
  have reverse := compressedCompactReverse_counts base base_pool_nodup 0 512 (by omega)
  simpa only [ht,hm,packets,Nat.reduceMul,Nat.reduceAdd] using
    And.intro forward.1 (And.intro forward.2 reverse)

/-- The unchanged delayed codec still emits all 170 packets after tick zero. -/
theorem integer_tail_counts :
    toffoliCount (compressedCompactForward base 1 511)=197628 ∧
    measurementCount (compressedCompactForward base 1 511)=98601 ∧
    toffoliCount (compressedCompactReverse base 1 511)=197798 ∧
    measurementCount (compressedCompactReverse base 1 511)=98431 := by
  have f := compressedCompactForward_counts base base_pool_nodup 1 511 (by omega)
  have r := compressedCompactReverse_counts base base_pool_nodup 1 511 (by omega)
  have t : compactSkywalkForwardT 1 511=197118 := by decide
  have m : compactSkywalkForwardM 1 511=98431 := by decide
  have packs : compressedPackCount 1 511=170 := by decide
  simpa only [t,m,packs,Nat.reduceAdd,Nat.reduceMul] using
    And.intro f.1 (And.intro f.2 r)

theorem kernel_counts (divide : Bool) :
    toffoliCount (kernel divide)=(if divide then 1053240 else 1053750) ∧
    measurementCount (kernel divide)=724028 := by
  have f := NativeFirstDirect.forward_counts base
  have r := NativeFirstKnown.inverse_counts base
  have integer := integer_tail_counts
  have clear := skywalkTerminalClear_counts (base 511) (base 512) (base 770)
  have field := selectedFieldSegment_counts divide
  simp only [kernel,skywalkArithmeticClear,toffoliCount_append,measurementCount_append,
    f.1,f.2,r.1,r.2,integer.1,integer.2.1,integer.2.2.1,integer.2.2.2,
    clear.1,clear.2,field.1,field.2]
  cases divide <;> constructor <;> norm_num

/-- Exact emitted gate and record counts for both candidate stages. The
separate support certificate includes resident ports; caller semantics are
transported separately across the public placement changes. -/
theorem controlled_counts (divide : Bool) :
    toffoliCount (controlled divide)=(if divide then 1053750 else 1054260) ∧
    measurementCount (controlled divide)=724536 := by
  have width : (wireBlock base 0 255).length+1=(wireBlock base 770 256).length := by
    simp [wireBlock]
  have wrapped := directZeroControlled_counts (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (kernel divide) width
  have core := kernel_counts divide
  simp only [controlled] at ⊢
  rw [wrapped.1,wrapped.2,core.1,core.2,wireBlock_length]
  cases divide <;> norm_num

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedReplay_counts
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.integer_tail_counts
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.kernel_counts
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.controlled_counts
