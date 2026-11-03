import ECDSAAdd.Arithmetic.NativeFirstDirectProgram
import Mathlib.Tactic

/-! Source-only numerical caller facts. These do not assert the MF-to-tail
prefix bridge, any program equivalence, or a full candidate certificate. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.E1CallerValueFactsResearch
open Arithmetic NativeFirstDirect

def Kword (D : Nat) (par : Bool) : Nat := (D/2+kConstant false par)%2^258

/-- Both forward selected callers have this identical numerical K output.
The parity premise excludes D=p-1 in the true branch, where a naive bound
without the actual caller condition would wrap exactly to zero. -/
theorem Kword_high_div (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) :
    Kword D par<2^258 ∧ (Kword D par)/2^257=par.toNat ∧
      (par=true → (Kword D par)/2^256=3) := by
  cases par <;> norm_num [Kword,kConstant,ECDSAAdd.p] at * <;> omega

/-- The exit's literal mapped-adder output is Y/2, not an unbounded MF word. -/
theorem exit_half_bound (Y : Nat) (hY : Y<ECDSAAdd.p) : Y/2<2^255 := by
  norm_num [ECDSAAdd.p] at hY ⊢
  omega

/-- Three final zero output bits justify the optional affine-carry extension.
A whole-adder prefix/cleanup proof is still required to use these facts. -/
theorem exit_top3 (Y : Nat) (hY : Y<ECDSAAdd.p) :
    (Y/2).testBit 255=false ∧ (Y/2).testBit 256=false ∧ (Y/2).testBit 257=false := by
  have h := exit_half_bound Y hY
  refine ⟨Nat.testBit_eq_false_of_lt h,?_,?_⟩
  · apply Nat.testBit_eq_false_of_lt
    norm_num at h ⊢
    omega
  · apply Nat.testBit_eq_false_of_lt
    norm_num at h ⊢
    omega

end ECDSAAdd.Entrant.E1CallerValueFactsResearch
