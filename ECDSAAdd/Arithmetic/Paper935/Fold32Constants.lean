import ECDSAAdd.Arithmetic.Paper935.Fold32Word

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- secp256k1 field modulus, independent of any endpoint layout. -/
def fold32Prime : Nat := 2^256-2^32-977

theorem fold32_literal_one : fold32Literal (Nat.testBit 1)=1 := by decide +kernel
theorem fold32_literal_prime : fold32Literal (Nat.testBit fold32Prime)=fold32Prime := by decide +kernel
theorem fold32_literal_negative_prime :
    fold32Literal (Nat.testBit (2^257-fold32Prime))=2^257-fold32Prime := by decide +kernel

/-- One subtraction and conditional restoration gives exact canonical reduction.
The branch information must be retained by a reversible implementation. -/
theorem fold32_reduce_math (x : Nat) (hx : x<2*fold32Prime) :
    ((x+(2^257-fold32Prime))%2^257+(if x<fold32Prime then fold32Prime else 0))%2^257=
      x%fold32Prime := by
  norm_num [fold32Prime] at *
  split_ifs <;> omega

end ECDSAAdd.Arithmetic.Paper935
