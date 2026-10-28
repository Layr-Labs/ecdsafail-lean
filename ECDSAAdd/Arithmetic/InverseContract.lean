import ECDSAAdd.Framework.Hoare
import ECDSAAdd.Math.BitcoinPrimes

namespace ECDSAAdd.Arithmetic

/-- secp256k1 求逆的接口要求；具体实现及满足证明见 fieldInverse_contract。
输入明确排除零，两个数值寄存器均为 256 位；工作位清零、相位恢复。
资源等式和线路包含关系约束同一个程序。 -/
def inverseContract (x out work : List Wire) (c : Program)
    (toffolis measurements qubits : Nat) : Prop :=
  (x ++ out ++ work).Nodup ∧ x.length = 256 ∧ out.length = 256 ∧
  (∀ X : Nat, 0 < X → X < ECDSAAdd.p →
    {{ x = X, out = (0 : Nat), work = (0 : Nat) }} c
    {{ x = X, out = ((X : Fp)⁻¹).val, work = (0 : Nat) }}) ∧
  toffoliCount c = toffolis ∧ measurementCount c = measurements ∧
  qubitCount c = qubits ∧ wires c ⊆ (x ++ out ++ work).toFinset

end ECDSAAdd.Arithmetic
