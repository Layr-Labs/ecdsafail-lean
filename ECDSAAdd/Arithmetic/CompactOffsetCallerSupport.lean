import ECDSAAdd.Arithmetic.CompactOffsetCallerArithmetic
import ECDSAAdd.Arithmetic.OffsetBorrowedSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open Secp256k1 BorrowedSkywalkCompactSupport
attribute [local irreducible] compactSkywalkForward compactSkywalkReverse

/-- Support follows the actual compact forward/reverse instructions. It does
not claim a reduced whole-stage peak: raw transcript storage is unchanged. -/
theorem compactOffsetCallerArithmetic_support (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (b sign eff : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hb : b∈W) (hs : sign∈W) (he : eff∈W) :
    wires (compactOffsetCallerArithmetic divide w b sign eff)⊆W := by
  have np := skywalkShared_integer_nodup w hn
  have ints := integerSegments w np p W hW
  have pool : (skywalkPoolWires w).toFinset⊆W :=
    blockSites w 0 1798 W hW (by intro i _ hi; exact Or.inl (by omega))
  have fw := (compactSkywalkForward_support w np 0 512 (by decide)).trans pool
  have rv := (compactSkywalkReverse_support w np 0 512 (by decide)).trans pool
  have fields := OffsetBorrowedSupport.endpoints w b sign eff W hW hb hs he
  have field : wires (if divide then offsetBorrowedSharedFieldDivision w b sign eff
      else offsetBorrowedInverseSharedFieldMultiplication w b sign eff)⊆W := by
    cases divide
    · exact fields.2
    · exact fields.1
  simp only [compactOffsetCallerArithmetic,wires_append,Finset.union_subset_iff]
  exact ⟨ints.1,fw,ints.2.2.2.2,field,ints.2.2.2.2,rv,ints.2.1⟩
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactOffsetCallerArithmetic_support
