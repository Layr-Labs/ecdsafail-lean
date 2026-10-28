import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/- Finite shallow-decoder identities only: not circuit-state reachability. -/
namespace ECDSAAdd.Divsteps.SmallDecoders

def bit (x i : Nat) : Bool := decide (x / 2^i % 2 = 1)
def oddValue {n : Nat} (x : Fin n) : Nat := 2 * x.val + 1

def decode2 (f q : Nat) : Bool := true ^^ bit f 1 ^^ bit q 1
def decode3 (f q : Nat) : Bool := true ^^ bit f 2 ^^ bit q 2
def decode4 (f q : Nat) : Bool :=
  true ^^ bit f 1 ^^ bit f 2 ^^ bit f 3 ^^ bit q 1 ^^ bit q 2 ^^ bit q 3 ^^
    ((bit f 1 ^^ bit f 2) && (bit q 1 ^^ bit q 2))

set_option maxRecDepth 4096 in
theorem depth2 : ∀ f q : Fin 2,
    bit (((3 : ZMod 4) * ((oddValue f * oddValue q : Nat) : ZMod 4)⁻¹).val) 1 =
      decode2 (oddValue f) (oddValue q) := by decide

set_option maxRecDepth 4096 in
theorem depth3 : ∀ f q : Fin 4,
    bit (((7 : ZMod 8) * ((oddValue f * oddValue q : Nat) : ZMod 8)⁻¹).val) 2 =
      decode3 (oddValue f) (oddValue q) := by decide

set_option maxRecDepth 4096 in
theorem depth4 : ∀ f q : Fin 8,
    bit (((15 : ZMod 16) * ((oddValue f * oddValue q : Nat) : ZMod 16)⁻¹).val) 3 =
      decode4 (oddValue f) (oddValue q) := by decide

example : (2^256 - 2^32 - 977 : Int) % 16 = 15 := by norm_num
end ECDSAAdd.Divsteps.SmallDecoders
