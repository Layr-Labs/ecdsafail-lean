import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
import ECDSAAdd.Arithmetic.NativeFirstKnownProgram
import ECDSAAdd.Arithmetic.MappedCompressedStageCounts

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open Secp256k1 MappedCompressed CompressedAllocation
attribute [local irreducible] toffoliCount measurementCount compactSkywalkTick
  compactSkywalkReverseTick compressedCompactForward compressedCompactReverse
  selectedFieldSegment forward inverse NativeFirstKnown.inverse

/-- The new prefix and independent inverse replace seed and tick zero only.
The 511 remaining ticks and the entire codec/field schedule are unchanged. -/
def callerKernel (divide : Bool) : Program :=
  forward base ++ compressedCompactForward base 1 511 ++ skywalkArithmeticClear base ++
    selectedFieldSegment divide ++ skywalkArithmeticClear base ++
    compressedCompactReverse base 1 511 ++ NativeFirstKnown.inverse base

def callerControlled (divide : Bool) : Program :=
  directZeroControlled (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (callerKernel divide)

private theorem zero_codec (w : Nat → Wire) :
    compressedPackAfter w 0=[] ∧ compressedDecodeBefore w 0=[] := by
  constructor <;> rfl

private theorem forward_step_counts (w : Nat → Wire) (i n : Nat) :
    toffoliCount (compressedCompactForward w i (n+1))=
      toffoliCount (compactSkywalkTick w i)+toffoliCount (compressedPackAfter w i)+
        toffoliCount (compressedCompactForward w (i+1) n) ∧
    measurementCount (compressedCompactForward w i (n+1))=
      measurementCount (compactSkywalkTick w i)+measurementCount (compressedPackAfter w i)+
        measurementCount (compressedCompactForward w (i+1) n) := by
  rw [compressedCompactForward,toffoliCount_append,toffoliCount_append,
    measurementCount_append,measurementCount_append]
  exact ⟨rfl,rfl⟩

private theorem reverse_step_counts (w : Nat → Wire) (i n : Nat) :
    toffoliCount (compressedCompactReverse w i (n+1))=
      toffoliCount (compressedCompactReverse w (i+1) n)+toffoliCount (compressedDecodeBefore w i)+
        toffoliCount (compactSkywalkReverseTick w i) ∧
    measurementCount (compressedCompactReverse w i (n+1))=
      measurementCount (compressedCompactReverse w (i+1) n)+measurementCount (compressedDecodeBefore w i)+
        measurementCount (compactSkywalkReverseTick w i) := by
  rw [compressedCompactReverse,toffoliCount_append,toffoliCount_append,
    measurementCount_append,measurementCount_append]
  exact ⟨rfl,rfl⟩

theorem tail_counts :
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

/-- Counts only. Functional caller acceptance remains a separate obligation. -/
theorem caller_counts (divide : Bool) :
    toffoliCount (callerKernel divide)=(if divide then 1053240 else 1053750) ∧
    measurementCount (callerKernel divide)=724028 ∧
    toffoliCount (callerControlled divide)=(if divide then 1053750 else 1054260) ∧
    measurementCount (callerControlled divide)=724536 := by
  have f := forward_counts base
  have r := NativeFirstKnown.inverse_counts base
  have tails := tail_counts
  have clear := skywalkTerminalClear_counts (base 511) (base 512) (base 770)
  have fields := selectedFieldSegment_counts divide
  have core : toffoliCount (callerKernel divide)=(if divide then 1053240 else 1053750) ∧
      measurementCount (callerKernel divide)=724028 := by
    simp only [callerKernel,skywalkArithmeticClear,toffoliCount_append,measurementCount_append,
      f.1,f.2,r.1,r.2,tails.1,tails.2.1,tails.2.2.1,tails.2.2.2,clear.1,clear.2,
      fields.1,fields.2]
    cases divide <;> constructor <;> norm_num
  have width : (wireBlock base 0 255).length+1=(wireBlock base 770 256).length := by
    simp [wireBlock_length]
  have ctrl := directZeroControlled_counts (wireBlock base 770 256) (wireBlock base 0 255)
    (base 2313) (base 2411) (callerKernel divide) width
  refine ⟨core.1,core.2,?_,?_⟩
  · cases divide <;> simpa only [callerControlled,core.1,wireBlock_length,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using ctrl.1
  · simpa only [callerControlled,core.2,wireBlock_length,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using ctrl.2

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.tail_counts
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.caller_counts
