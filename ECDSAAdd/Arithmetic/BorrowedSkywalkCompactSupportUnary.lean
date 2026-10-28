import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportLayout
import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryLayout
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
open Secp256k1
attribute [local irreducible] wireBlock dblInPlace halfInPlace

/-- The actual unary recipes omit the ghost mask from their instruction support. -/
theorem unary (w : Nat → Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) :
    wires (dblInPlace (borrowedSkywalkUnary w) p)⊆W ∧
    wires (halfInPlace (borrowedSkywalkUnary w) p)⊆W := by
  have hu := modUnary_wires (borrowedSkywalkUnary w) 256 p
    (borrowedSkywalkUnary_widths w) (by omega)
  have hz : ((borrowedSkywalkUnary w).z).toFinset⊆W := by
    rw [borrowedSkywalkUnary_z_block]
    exact blockSites w 2056 257 W hW (by intro i h₁ h₂; exact Or.inr ⟨h₁,by omega⟩)
  have hconstant := blockSites w 512 257 W hW (by intro i _ h₂; exact Or.inl (by omega))
  have hcarry := blockSites w 1540 256 W hW (by intro i _ h₂; exact Or.inl (by omega))
  have hcin := hW (List.mem_toFinset.mpr (index_mem w 1797 (Or.inl (by omega))))
  have hflag := hW (List.mem_toFinset.mpr (index_mem w 769 (Or.inl (by omega))))
  have used : ((borrowedSkywalkUnary w).z++(borrowedSkywalkUnary w).core.work++
      [(borrowedSkywalkUnary w).flag]).toFinset⊆W := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_append] at hq
    rcases hq with (hq|hq)|hq
    · exact hz (List.mem_toFinset.mpr hq)
    · simp only [ModUnaryLayout.core,ModAddCoreLayout.work,borrowedSkywalkUnary,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
      rcases hq with hq|hq|rfl
      · exact hconstant (List.mem_toFinset.mpr hq)
      · exact hcarry (List.mem_toFinset.mpr hq)
      · exact hcin
    · simp only [borrowedSkywalkUnary,List.mem_singleton] at hq
      subst q
      exact hflag
  have usedCore : ((borrowedSkywalkUnary w).z++(borrowedSkywalkUnary w).core.work).toFinset⊆W := by
    intro q hq
    exact used (List.mem_toFinset.mpr
      (List.mem_append_left _ (List.mem_toFinset.mp hq)))
  exact ⟨by rw [hu.1]; exact usedCore,by rw [hu.2]; exact used⟩
end ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport
#print axioms ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupport.unary
