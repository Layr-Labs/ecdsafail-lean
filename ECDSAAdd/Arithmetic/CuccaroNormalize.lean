import ECDSAAdd.Arithmetic.CuccaroModProof
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic

structure CuccaroNormalizeLayout where
  src : List Wire
  high : Wire
  work : List Wire
  workHigh : Wire
  cin : Wire
  flag : Wire

namespace CuccaroNormalizeLayout

def a (L : CuccaroNormalizeLayout) : List Wire := L.src++[L.high]
def scratch (L : CuccaroNormalizeLayout) : List Wire := L.work++[L.workHigh]
def wires (L : CuccaroNormalizeLayout) : List Wire := L.a++L.scratch++[L.cin,L.flag]

structure Widths (L : CuccaroNormalizeLayout) (n : Nat) : Prop where
  src : L.src.length=n
  work : L.work.length=n

theorem a_length (L : CuccaroNormalizeLayout) (n : Nat) (hw : L.Widths n) :
    L.a.length=n+1 := by simp [a,hw.src]

theorem scratch_length (L : CuccaroNormalizeLayout) (n : Nat) (hw : L.Widths n) :
    L.scratch.length=n+1 := by simp [scratch,hw.work]

end CuccaroNormalizeLayout

/-- Normalize an `n`-bit value modulo `2^n-c`, retaining the one-bit branch
history in `flag`.  The work word is reused first as `c`, then as `¬c`. -/
def cuccaroNormalize (L : CuccaroNormalizeLayout) (c : Nat) : Program :=
  xorConstant L.scratch c++
  cuccaroAdd L.scratch L.a L.cin++
  xorConstant L.scratch c++
  xorConstant L.work c++
  maskedConstant L.high L.work c++
  cuccaroSub L.work L.src L.cin++
  maskedConstant L.high L.work c++
  xorConstant L.work c++
  [.CX L.high L.flag,.CX L.flag L.high]

def cuccaroNormalizeClear (L : CuccaroNormalizeLayout) (c : Nat) : Program :=
  (cuccaroNormalize L c).reverse

theorem cuccaroNormalize_counts (L : CuccaroNormalizeLayout) (n c : Nat)
    (hw : L.Widths n) :
    (toffoliCount (cuccaroNormalize L c)=4*n-2 ∧
      measurementCount (cuccaroNormalize L c)=0) ∧
    (toffoliCount (cuccaroNormalizeClear L c)=4*n-2 ∧
      measurementCount (cuccaroNormalizeClear L c)=0) := by
  have ha := L.a_length n hw
  have hs := L.scratch_length n hw
  have add := cuccaroAdd_counts L.scratch L.a L.cin (hs.trans ha.symm)
  have sub := cuccaroSub_counts L.work L.src L.cin (hw.work.trans hw.src.symm)
  have fwd : toffoliCount (cuccaroNormalize L c)=4*n-2 ∧
      measurementCount (cuccaroNormalize L c)=0 := by
    simp [cuccaroNormalize,toffoliCount_append,measurementCount_append,
      toffoliCount,measurementCount,add.1,add.2,sub.1,sub.2,
      (xorConstant_counts L.scratch c).1,(xorConstant_counts L.scratch c).2,
      (xorConstant_counts L.work c).1,(xorConstant_counts L.work c).2,
      (maskedConstant_counts L.high L.work c).1,
      (maskedConstant_counts L.high L.work c).2,ha,hw.src]
    omega
  constructor
  · exact fwd
  · rw [cuccaroNormalizeClear,toffoliCount_reverse,measurementCount_reverse]
    exact fwd

end ECDSAAdd.Arithmetic
