import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportReplay
import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportUnary
import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportInteger
import ECDSAAdd.Arithmetic.DirectSkywalkArithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
open Secp256k1
attribute [local irreducible] wireBlock dblInPlace halfInPlace copyRegister
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] balancedSharedReplayProgram balancedInverseSharedReplayProgram

/-- Both actual production field endpoints use only compact sites and selectors. -/
theorem endpoints (w : Nat → Wire) (b effG effS : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hb : b∈W) (hg : effG∈W) (hs : effS∈W) :
    wires (balancedSharedFieldDivision w b effG effS)⊆W ∧
    wires (balancedInverseSharedFieldMultiplication w b effG effS)⊆W := by
  have hu := unary w W hW
  have hc := copy w W hW
  have hr := replayPrograms w b effG effS W hW hb hg hs
  simp only [balancedSharedFieldDivision,balancedInverseSharedFieldMultiplication,
    wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨hu.1,hr.1⟩,hc⟩,⟨⟨hc,hr.2⟩,hu.2⟩⟩

/-- The emitted seven-stage kernel includes the literal seed and borrowed
unary endpoints; no support premise names the omitted old virtual bank. -/
theorem kernel (divide : Bool) (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (b effG effS : Wire) (W : Finset Wire) (hW : (compactSharedSites w).toFinset⊆W)
    (hb : b∈W) (hg : effG∈W) (hs : effS∈W) :
    wires (directSkywalkArithmetic divide w b effG effS)⊆W := by
  have hi := integerSegments w (skywalkShared_integer_nodup w hn) p W hW
  have hf := endpoints w b effG effS W hW hb hg hs
  have field : wires (if divide then balancedSharedFieldDivision w b effG effS
      else balancedInverseSharedFieldMultiplication w b effG effS)⊆W := by
    cases divide
    · exact hf.2
    · exact hf.1
  simp only [directSkywalkArithmetic,wires_append,Finset.union_subset_iff]
  exact ⟨hi.1,hi.2.2.1,hi.2.2.2.2,field,hi.2.2.2.2,hi.2.2.2.1,hi.2.1⟩
end ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.endpoints
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.kernel
