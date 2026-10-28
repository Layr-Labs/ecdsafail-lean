import ECDSAAdd.Arithmetic.CuccaroAdder
import ECDSAAdd.Arithmetic.MaskedConstant
import ECDSAAdd.Arithmetic.Copy

namespace ECDSAAdd.Arithmetic

/-- One-work-register modular arithmetic.  The source, target and work words
are widened by one bit; `flag` is used only by subtraction. -/
structure CuccaroModLayout where
  a : List Wire
  low : List Wire
  high : Wire
  work : List Wire
  workHigh : Wire
  cin : Wire
  flag : Wire

namespace CuccaroModLayout

def z (L : CuccaroModLayout) : List Wire := L.low++[L.high]
def scratch (L : CuccaroModLayout) : List Wire := L.work++[L.workHigh]
def allWork (L : CuccaroModLayout) : List Wire := L.scratch++[L.cin,L.flag]
def wires (L : CuccaroModLayout) : List Wire :=
  L.a++L.z++L.allWork

structure Widths (L : CuccaroModLayout) (n : Nat) : Prop where
  a : L.a.length=n+1
  low : L.low.length=n
  work : L.work.length=n

theorem z_length (L : CuccaroModLayout) (n : Nat) (hw : L.Widths n) :
    L.z.length=n+1 := by simp [z,hw.low]

theorem scratch_length (L : CuccaroModLayout) (n : Nat) (hw : L.Widths n) :
    L.scratch.length=n+1 := by simp [scratch,hw.work]

end CuccaroModLayout

/-- Exact modular addition for canonical `a,z<p`, using only one widened work
word.  The final scratch comparison clears the reduction bit. -/
def cuccaroModAdd (L : CuccaroModLayout) (p : Nat) : Program :=
  cuccaroAdd L.a L.z L.cin ++
  xorConstant L.scratch p ++
  cuccaroSub L.scratch L.z L.cin ++
  xorConstant L.scratch p ++
  maskedConstant L.high L.work p ++
  cuccaroAdd L.work L.low L.cin ++
  maskedConstant L.high L.work p ++
  copyRegister none L.low L.work ++
  cuccaroSub L.a L.scratch L.cin ++
  [.CX L.workHigh L.high,.X L.high] ++
  cuccaroAdd L.a L.scratch L.cin ++
  copyRegister none L.low L.work

/-- Exact modular subtraction for canonical `a,z<p`.  The original borrow is
moved to `flag`; after adding `a` back, trial subtraction of `p` computes its
complement and clears the flag before restoring the result. -/
def cuccaroModSub (L : CuccaroModLayout) (p : Nat) : Program :=
  cuccaroSub L.a L.z L.cin ++
  maskedConstant L.high L.work p ++
  cuccaroAdd L.work L.low L.cin ++
  maskedConstant L.high L.work p ++
  [.CX L.high L.flag,.CX L.flag L.high] ++
  cuccaroAdd L.a L.z L.cin ++
  xorConstant L.scratch p ++
  cuccaroSub L.scratch L.z L.cin ++
  [.X L.flag,.CX L.high L.flag] ++
  cuccaroAdd L.scratch L.z L.cin ++
  xorConstant L.scratch p ++
  cuccaroSub L.a L.z L.cin

theorem cuccaroModAdd_counts (L : CuccaroModLayout) (n p : Nat)
    (hw : L.Widths n) :
    toffoliCount (cuccaroModAdd L p)=10*n-2 ∧
      measurementCount (cuccaroModAdd L p)=0 := by
  have hz := L.z_length n hw
  have hs := L.scratch_length n hw
  have a1 := cuccaroAdd_counts L.a L.z L.cin (hw.a.trans hz.symm)
  have s1 := cuccaroSub_counts L.scratch L.z L.cin (hs.trans hz.symm)
  have a2 := cuccaroAdd_counts L.work L.low L.cin (hw.work.trans hw.low.symm)
  have s2 := cuccaroSub_counts L.a L.scratch L.cin (hw.a.trans hs.symm)
  have a3 := cuccaroAdd_counts L.a L.scratch L.cin (hw.a.trans hs.symm)
  have cp := copyRegister_counts none L.low L.work (hw.low.trans hw.work.symm)
  simp [cuccaroModAdd,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    a1.1,a1.2,s1.1,s1.2,a2.1,a2.2,s2.1,s2.2,a3.1,a3.2,cp.1,cp.2,
    (xorConstant_counts L.scratch p).1,(xorConstant_counts L.scratch p).2,
    (maskedConstant_counts L.high L.work p).1,
    (maskedConstant_counts L.high L.work p).2,hw.low]
  omega

theorem cuccaroModSub_counts (L : CuccaroModLayout) (n p : Nat)
    (hw : L.Widths n) :
    toffoliCount (cuccaroModSub L p)=12*n-2 ∧
      measurementCount (cuccaroModSub L p)=0 := by
  have hz := L.z_length n hw
  have hs := L.scratch_length n hw
  have s1 := cuccaroSub_counts L.a L.z L.cin (hw.a.trans hz.symm)
  have a1 := cuccaroAdd_counts L.work L.low L.cin (hw.work.trans hw.low.symm)
  have a2 := cuccaroAdd_counts L.a L.z L.cin (hw.a.trans hz.symm)
  have s2 := cuccaroSub_counts L.scratch L.z L.cin (hs.trans hz.symm)
  have a3 := cuccaroAdd_counts L.scratch L.z L.cin (hs.trans hz.symm)
  simp [cuccaroModSub,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    s1.1,s1.2,a1.1,a1.2,a2.1,a2.2,s2.1,s2.2,a3.1,a3.2,
    (xorConstant_counts L.scratch p).1,(xorConstant_counts L.scratch p).2,
    (maskedConstant_counts L.high L.work p).1,
    (maskedConstant_counts L.high L.work p).2,hw.low]
  omega

end ECDSAAdd.Arithmetic
