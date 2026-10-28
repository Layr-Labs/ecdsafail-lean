import ECDSAAdd.Arithmetic.MontAdapterFrame
import ECDSAAdd.Math.BitcoinPrimes

namespace ECDSAAdd.Arithmetic

/-- secp256k1 模乘：两段Montgomery标准模积、XOR输出与前向清理。 -/
def fieldMul (L : MontLayout) : Program := montMulXor L p

/-- 任意输出 XOR 规格保持；乘数范围由 256 位寄存器自动给出。 -/
theorem fieldMul_spec (L : MontLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (X Y O : Nat) (hX : X<p) :
    {{ L.x=X,L.y=Y,L.out=O,L.work=0 }} fieldMul L
    {{ L.x=X,L.y=Y,L.out=(O ^^^ ((X*Y)%p)),L.work=0 }} := by
  letI : Fact p.Prime := ⟨Secp256k1.p_prime⟩
  intro s m h
  have hy : Y<2^256 := by
    have hb := regValue_lt L.y s.basis
    rw [hw.y] at hb
    exact h.1.1.2 ▸ hb
  exact montMulXor_spec L p X Y O hw hnd (by norm_num [p]) secp256k1_mod_sixteen hX hy s m h

theorem fieldMul_zero_spec (L : MontLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (X Y : Nat) (hX : X<p) :
    {{ L.x=X,L.y=Y,L.out=0,L.work=0 }} fieldMul L
    {{ L.x=X,L.y=Y,L.out=((X*Y)%p),L.work=0 }} := by
  simpa only [Nat.zero_xor] using fieldMul_spec L hnd hw X Y 0 hX

theorem fieldMul_resources (L : MontLayout) (hnd : L.wires.Nodup) (hw : L.Widths) :
    toffoliCount (fieldMul L)=379424 ∧ measurementCount (fieldMul L)=379424 ∧
    qubitCount (fieldMul L)=2596 := by
  have hc := montAdapter_counts L p hw hnd
  have hq := montAdapter_qubits L p hw hnd
  exact ⟨hc.1.1,hc.1.2,hq.1⟩

end ECDSAAdd.Arithmetic
