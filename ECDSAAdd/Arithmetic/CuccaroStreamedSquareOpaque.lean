import ECDSAAdd.Arithmetic.CuccaroStreamedSquareB
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareCFull

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

/-- An executable list append hidden behind an irreducible boundary.  This
prevents Lean's kernel from recursively expanding a million-instruction left
operand when independently checked circuit specifications are sequenced. -/
def checkedSeq (a b : Program) : Program := a++b

theorem checkedSeq_eq (a b : Program) : checkedSeq a b=a++b := by rfl

attribute [irreducible] checkedSeq

theorem checkedSeq_correct {P Q R : BasisState → Prop} {a b : Program}
    (ha : Triple P a Q) (hb : Triple Q b R) :
    Triple P (checkedSeq a b) R := by
  rw [checkedSeq_eq]
  exact ha.seq hb

/-- Kernel-opaque aliases keep the verified branch boundaries intact when the
full streamed circuit is composed.  Their executable values remain the exact
gate programs below. -/
def checkedBranchA (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.branchA

def checkedBranchBPrefix (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.core.square128 L.core.high++L.addRotate128 false

def checkedBranchBSuffix (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.subTimesC (L.core.product.take 256)++L.core.square128Clear L.core.high

def checkedBranchC (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.branchC

theorem checkedBranchA_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedBranchA=L.branchA := by rfl

theorem checkedBranchBPrefix_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedBranchBPrefix=
      L.core.square128 L.core.high++L.addRotate128 false := by rfl

theorem checkedBranchBSuffix_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedBranchBSuffix=
      L.subTimesC (L.core.product.take 256)++
        L.core.square128Clear L.core.high := by rfl

theorem checkedBranchC_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedBranchC=L.branchC := by rfl

attribute [irreducible] checkedBranchA checkedBranchBPrefix checkedBranchBSuffix checkedBranchC

def checkedFirstHalf (L : CuccaroStreamedSquareWideLayout) : Program :=
  checkedSeq L.checkedBranchA L.checkedBranchBPrefix

def checkedSecondHalf (L : CuccaroStreamedSquareWideLayout) : Program :=
  checkedSeq L.checkedBranchBSuffix L.checkedBranchC

theorem checkedFirstHalf_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedFirstHalf=checkedSeq L.checkedBranchA L.checkedBranchBPrefix := by rfl

theorem checkedSecondHalf_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedSecondHalf=checkedSeq L.checkedBranchBSuffix L.checkedBranchC := by rfl

attribute [irreducible] checkedFirstHalf checkedSecondHalf

def checkedProgram (L : CuccaroStreamedSquareWideLayout) : Program :=
  checkedSeq L.checkedFirstHalf L.checkedSecondHalf

theorem checkedProgram_eq (L : CuccaroStreamedSquareWideLayout) :
    L.checkedProgram=checkedSeq L.checkedFirstHalf L.checkedSecondHalf := by rfl

attribute [irreducible] checkedProgram

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
