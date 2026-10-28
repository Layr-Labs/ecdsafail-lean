import ECDSAAdd.Arithmetic.NativeFirstDirectSeedInput
import ECDSAAdd.Arithmetic.SkywalkArithmeticCore

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect

private theorem block_away_shared (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i a n : Nat) (hi : i<2314) (ha : a+n ≤ 2314)
    (sep : i<a ∨ a+n ≤ i) : w i ∉ wireBlock w a n := by
  intro h
  obtain ⟨j,hj,he⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  have eq := skywalkShared_index_inj w hn j i (by omega) hi he
  omega

private theorem clean_bit (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y i : Nat) (bits : BasisState) (hin : SkywalkArithmeticInput w x y bits)
    (hi : i<2314) (hx : i<770 ∨ 1026 ≤ i) (hy : i<2056 ∨ 2312 ≤ i) : bits (w i)=false := by
  apply hin.2.2 (w i)
  · exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  · exact block_away_shared w hn i 770 256 hi (by omega) hx
  · exact block_away_shared w hn i 2056 256 hi (by omega) hy

private theorem clean_word (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y a n : Nat) (bits : BasisState) (hin : SkywalkArithmeticInput w x y bits)
    (ha : a+n ≤ 2314) (hx : a+n ≤ 770 ∨ 1026 ≤ a) (hy : a+n ≤ 2056 ∨ 2312 ≤ a) :
    regValue (wireBlock w a n) bits=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact clean_bit w hn x y i bits hin (by omega) (by omega) (by omega)

/-- Readiness is derived from the full caller's existing workspace contract.
No new restriction is imposed on the divisor, numerator, or control. -/
theorem caller_ready (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (bits : BasisState) (hin : SkywalkArithmeticInput w x y bits) :
    LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x bits ∧ bits (w 258)=false := by
  have bz := clean_word w hn x y 1026 2 bits hin (by omega) (by omega) (by omega)
  have bv : regValue (wireBlock w 770 258) bits=x := by
    rw [←wireBlock_append w 770 256 2,regValue_append,bz,Nat.mul_zero,Nat.add_zero]
    exact hin.1
  refine ⟨?_,clean_bit w hn x y 258 bits hin (by omega) (by omega) (by omega)⟩
  refine ⟨clean_word w hn x y 0 258 bits hin (by omega) (by omega) (by omega),bv,
    clean_word w hn x y 1540 257 bits hin (by omega) (by omega) (by omega),?_,?_,?_⟩
  · exact clean_bit w hn x y 1797 bits hin (by omega) (by omega) (by omega)
  · exact clean_bit w hn x y 1028 bits hin (by omega) (by omega) (by omega)
  · exact clean_bit w hn x y 1797 bits hin (by omega) (by omega) (by omega)

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.caller_ready
