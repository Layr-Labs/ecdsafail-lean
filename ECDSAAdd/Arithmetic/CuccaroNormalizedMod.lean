import ECDSAAdd.Arithmetic.CuccaroNormalizeProof

namespace ECDSAAdd.Arithmetic

/-- Shared physical layout for normalize/use/uncompute.  The 256-bit `work`
word is reused by normalization and modular arithmetic. -/
structure CuccaroNormalizedModLayout where
  src : List Wire
  srcHigh : Wire
  out : List Wire
  outHigh : Wire
  work : List Wire
  workHigh : Wire
  cin : Wire
  normFlag : Wire
  modFlag : Wire

namespace CuccaroNormalizedModLayout

def normalize (L : CuccaroNormalizedModLayout) : CuccaroNormalizeLayout :=
  ⟨L.src,L.srcHigh,L.work,L.workHigh,L.cin,L.normFlag⟩

def modular (L : CuccaroNormalizedModLayout) : CuccaroModLayout :=
  ⟨L.src++[L.srcHigh],L.out,L.outHigh,L.work,L.workHigh,L.cin,L.modFlag⟩

def wires (L : CuccaroNormalizedModLayout) : List Wire :=
  L.src++[L.srcHigh]++L.out++[L.outHigh]++L.work++
    [L.workHigh,L.cin,L.normFlag,L.modFlag]

structure Widths (L : CuccaroNormalizedModLayout) (n : Nat) : Prop where
  src : L.src.length=n
  out : L.out.length=n
  work : L.work.length=n

theorem normalize_widths (L : CuccaroNormalizedModLayout) (n : Nat) (hw : L.Widths n) :
    L.normalize.Widths n := ⟨hw.src,hw.work⟩

theorem modular_widths (L : CuccaroNormalizedModLayout) (n : Nat) (hw : L.Widths n) :
    L.modular.Widths n := by
  constructor <;> simp [modular,hw.src,hw.out,hw.work]

end CuccaroNormalizedModLayout

def cuccaroNormalizedModAdd (L : CuccaroNormalizedModLayout) (c p : Nat) : Program :=
  cuccaroNormalize L.normalize c++cuccaroModAdd L.modular p++
    cuccaroNormalizeClear L.normalize c

def cuccaroNormalizedModSub (L : CuccaroNormalizedModLayout) (c p : Nat) : Program :=
  cuccaroNormalize L.normalize c++cuccaroModSub L.modular p++
    cuccaroNormalizeClear L.normalize c

theorem cuccaroNormalizedModAdd_counts (L : CuccaroNormalizedModLayout)
    (n c p : Nat) (hw : L.Widths n) :
    toffoliCount (cuccaroNormalizedModAdd L c p)=18*n-6 ∧
      measurementCount (cuccaroNormalizedModAdd L c p)=0 := by
  have hn := cuccaroNormalize_counts L.normalize n c (L.normalize_widths n hw)
  have hm := cuccaroModAdd_counts L.modular n p (L.modular_widths n hw)
  simp [cuccaroNormalizedModAdd,toffoliCount_append,measurementCount_append,
    hn.1.1,hn.1.2,hn.2.1,hn.2.2,hm.1,hm.2]
  omega

theorem cuccaroNormalizedModSub_counts (L : CuccaroNormalizedModLayout)
    (n c p : Nat) (hw : L.Widths n) :
    toffoliCount (cuccaroNormalizedModSub L c p)=20*n-6 ∧
      measurementCount (cuccaroNormalizedModSub L c p)=0 := by
  have hn := cuccaroNormalize_counts L.normalize n c (L.normalize_widths n hw)
  have hm := cuccaroModSub_counts L.modular n p (L.modular_widths n hw)
  simp [cuccaroNormalizedModSub,toffoliCount_append,measurementCount_append,
    hn.1.1,hn.1.2,hn.2.1,hn.2.2,hm.1,hm.2]
  omega

end ECDSAAdd.Arithmetic
