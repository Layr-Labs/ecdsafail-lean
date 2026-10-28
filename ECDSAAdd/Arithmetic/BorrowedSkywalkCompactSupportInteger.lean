import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportLayout
import ECDSAAdd.Arithmetic.LiteralSkywalkSeedPool
import ECDSAAdd.Arithmetic.SkywalkArithmeticCore
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
attribute [local irreducible] wireBlock literalSkywalkSeed literalSkywalkUnseed
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop

/-- The actual bank-free seed and integer passes all use the first compact block. -/
theorem integerSegments (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (modulus : Nat) (W : Finset Wire) (hW : (compactSharedSites w).toFinset⊆W) :
    wires (literalSkywalkSeed (literalSkywalkPoolSeed w) modulus)⊆W ∧
    wires (literalSkywalkUnseed (literalSkywalkPoolSeed w) modulus)⊆W ∧
    wires (narrowSkywalkRoutedLoop w 0 512)⊆W ∧
    wires (narrowSkywalkRoutedUnloop w 0 512)⊆W ∧
    wires (skywalkArithmeticClear w)⊆W := by
  have pool : (skywalkPoolWires w).toFinset⊆W :=
    blockSites w 0 1798 W hW (by intro i _ hi; exact Or.inl (by omega))
  have seed := literalSkywalkPoolSeed_support w modulus
  have loops := narrowSkywalkRoutedLoop_support w 0 512 hn (by omega)
  have clear : wires (skywalkArithmeticClear w)⊆W := by
    rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    all_goals exact hW (List.mem_toFinset.mpr (index_mem w _ (Or.inl (by omega))))
  exact ⟨seed.1.trans pool,seed.2.trans pool,loops.1.trans pool,loops.2.trans pool,clear⟩
end ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.integerSegments
