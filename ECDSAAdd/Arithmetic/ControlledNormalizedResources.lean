import ECDSAAdd.Arithmetic.ControlledNormalizedMod
import ECDSAAdd.Arithmetic.CuccaroCnotResources
import ECDSAAdd.Math.SquareReduction

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

theorem cuccaroMod_cnotCounts (L : CuccaroModLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    cnotCount (cuccaroModAdd L p)=22*n+7+2*constantWeight n p ∧
    cnotCount (cuccaroModSub L p)=24*n+11+2*constantWeight n p := by
  have zl := L.z_length n hw
  have sl := L.scratch_length n hw
  have a1 := cuccaroAdd_cnotCount L.a L.z L.cin (hw.a.trans zl.symm)
  have s1 := cuccaroSub_cnotCount L.scratch L.z L.cin (sl.trans zl.symm)
  have a2 := cuccaroAdd_cnotCount L.work L.low L.cin (hw.work.trans hw.low.symm)
  have s2 := cuccaroSub_cnotCount L.a L.scratch L.cin (hw.a.trans sl.symm)
  have a3 := cuccaroAdd_cnotCount L.a L.scratch L.cin (hw.a.trans sl.symm)
  have s3 := cuccaroSub_cnotCount L.a L.z L.cin (hw.a.trans zl.symm)
  have a4 := cuccaroAdd_cnotCount L.scratch L.z L.cin (sl.trans zl.symm)
  have cp := copyRegister_none_cnotCount L.low L.work (hw.low.trans hw.work.symm)
  have nz : n≠0 := by omega
  simp only [hw.a,hw.work,sl,nz,Nat.add_eq_zero_iff,Nat.one_ne_zero,
    and_false,if_false] at a1 s1 a2 s2 a3 s3 a4
  simp only [cuccaroModAdd,cuccaroModSub,cnotCount_append,
    a1,s1,a2,s2,a3,s3,a4,cp,xorConstant_cnotCount,maskedConstant_cnotCount,
    hw.work,hw.low,cnotCount]
  constructor <;> omega

/-- Kernel-computed full 256-bit constant weight; no native_decide or sampled
carry/borrow window is used. -/
theorem secp256k1_prime_weight : constantWeight 256 SquareReduction.p=250 := by
  decide

theorem controlledNormalizedMod_secp256k1_counts (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (hw : L.Widths 256) :
    (toffoliCount (controlledNormalizedModAdd control scratch L
        SquareReduction.c SquareReduction.p)=15857 ∧
      measurementCount (controlledNormalizedModAdd control scratch L
        SquareReduction.c SquareReduction.p)=0) ∧
    (toffoliCount (controlledNormalizedModSub control scratch L
        SquareReduction.c SquareReduction.p)=17909 ∧
      measurementCount (controlledNormalizedModSub control scratch L
        SquareReduction.c SquareReduction.p)=0) := by
  have h := controlledNormalizedMod_counts control scratch L 256
    SquareReduction.c SquareReduction.p hw
  have cx := cuccaroMod_cnotCounts L.modular 256 SquareReduction.p
    (L.modular_widths 256 hw) (by omega)
  simpa only [cx.1,cx.2,secp256k1_prime_weight] using h

end ECDSAAdd.Arithmetic
