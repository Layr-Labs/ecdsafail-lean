import ECDSAAdd.Submission.Entrant.E1CallerValueFactsDraft

/-! SOURCE ONLY in this independent import context. Existing39 ValueFacts remains
byte-identical. The new proof bodies are copied from separately qualified v7. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.E1CallerValueFactsResearch
open Arithmetic NativeFirstDirect

/-- SOURCE DRAFT 52: the actual canonical caller fixes the top three-bit word.
The odd branch still needs the real parity premise; par=true,D=p-1 would wrap. -/
theorem Kword_high_div255 (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) :
    (par=false → (Kword D par)/2^255=1 ∨ (Kword D par)/2^255=2) ∧
      (par=true → (Kword D par)/2^255=7) := by
  cases par <;> norm_num [Kword,kConstant,ECDSAAdd.p] at * <;> omega

private theorem testBit_of_quotient_flag52 (N i : Nat) (flag : Bool)
    (h : N/2^i=flag.toNat) : N.testBit i=flag := by
  rw [Nat.testBit_eq_decide_div_mod_eq,h]
  cases flag <;> decide

/-- SOURCE DRAFT 52: only the two affine relations needed by the forward tail.
This states a Nat/Bool value fact, not a physical-port or program equivalence. -/
theorem Kword_top_affine (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool)
    (hp : par=decide (D%2=1)) :
    (Kword D par).testBit 257=par ∧
      ((Kword D par).testBit 256 ^^ (Kword D par).testBit 255)=(!par) := by
  have high := Kword_high_div D hD par hp
  have high257 : (Kword D par)/2^257=par.toNat := high.2.1
  have top3 := Kword_high_div255 D hD par hp
  have div256 : (Kword D par)/2^256=((Kword D par)/2^255)/2 := by
    norm_num [Nat.div_div_eq_div_mul]
  refine ⟨?_,?_⟩
  · exact testBit_of_quotient_flag52 (Kword D par) 257 par high257
  · rcases top3 with ⟨evenTop,oddTop⟩
    cases par with
    | false =>
        rcases evenTop rfl with h | h
        · (simp only [Nat.testBit_eq_decide_div_mod_eq,div256,h]; decide)
        · (simp only [Nat.testBit_eq_decide_div_mod_eq,div256,h]; decide)
    | true =>
        have h := oddTop rfl
        (simp only [Nat.testBit_eq_decide_div_mod_eq,div256,h]; decide)

end ECDSAAdd.Entrant.E1CallerValueFactsResearch
