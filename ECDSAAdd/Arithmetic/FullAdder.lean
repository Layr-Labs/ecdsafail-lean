import ECDSAAdd.Framework.Hoare

namespace ECDSAAdd.Arithmetic
open Instr Correction

def sumBit (a b c : Bool) : Bool := (a ^^ b) ^^ c

def carryBit (a b c : Bool) : Bool := ((a && b) ^^ (a && c)) ^^ (b && c)

/-- 先临时异或输入，用一个 Toffoli 计算 majority，再恢复输入并异或输出和位。 -/
def fullAdder (a b cin out carry : Wire) : Program := prog {
  CX a b; CX a cin; CCX b cin carry;
  CX a carry; CX a cin; CX a b;
  CX a out; CX b out; CX cin out
}

/-- 进位是三项 AND 的异或；测量后立即执行对应的三个 CZ 修正。 -/
def eraseCarry (a b cin carry : Wire) : Program :=
  prog { if meas carry = 1 then [CZ a b, CZ a cin, CZ b cin] else skip }

/-- 任意输出和进位初值均可：在两处 XOR 写入和位与进位，其余状态保持。 -/
theorem fullAdder_correct (a b cin out carry : Wire)
    (hdisjoint : [a, b, cin, out, carry].Nodup)
    (s : State) (m : List Bool) :
    run (fullAdder a b cin out carry) m s =
      ⟨s.phase,
        writeBit (writeBit s.basis carry
          (s.basis carry ^^ carryBit (s.basis a) (s.basis b) (s.basis cin)))
          out (s.basis out ^^ sumBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hdisjoint
  obtain ⟨⟨hab, hac, hao, hak⟩, ⟨hbc, hbo, hbk⟩, ⟨hco, hck⟩, hok⟩ := hdisjoint
  have hcb := Ne.symm hbc
  simp only [fullAdder, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwa : w = a <;> by_cases hwb : w = b <;>
    by_cases hwc : w = cin <;> by_cases hwo : w = out <;>
    by_cases hwk : w = carry <;>
    simp_all [writeBit, Function.update, sumBit, carryBit]
  cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;>
    cases s.basis out <;> cases s.basis carry <;> simp_all

/-- 只要 carry 保存正确的进位，就能对任意测量结果清零它，且恢复原相位。 -/
theorem eraseCarry_correct (a b cin carry : Wire)
    (ha : a ≠ carry) (hb : b ≠ carry) (hc : cin ≠ carry)
    (s : State)
    (hcarry : s.basis carry = carryBit (s.basis a) (s.basis b) (s.basis cin))
    (m : List Bool) :
    run (eraseCarry a b cin carry) m s =
      ⟨s.phase, writeBit s.basis carry false⟩ := by
  simp only [eraseCarry, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, ha, hb, hc,
      hcarry, carryBit]
  cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;> simp

/-- 保持三个输入，在输出与进位线上异或写入和位与进位。 -/
theorem fullAdder_spec (a b cin out carry : Wire)
    (hnd : [a, b, cin, out, carry].Nodup) (A B C O K : Bool) :
    {{ a = A, b = B, cin = C, out = O, carry = K }} fullAdder a b cin out carry
    {{ a = A, b = B, cin = C, out = (O ^^ sumBit A B C),
       carry = (K ^^ carryBit A B C) }} := by
  intro s m hP
  rw [fullAdder_correct a b cin out carry hnd]
  simp only [Holds.holds] at hP ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨hab, hac, hao, hak⟩, ⟨hbc, hbo, hbk⟩, ⟨hco, hck⟩, hok⟩ := hnd
  simp_all [writeBit, Function.update, Ne.symm hok]

/-- 进位已等于 majority 时，清零进位并保持输入与相位。 -/
theorem eraseCarry_spec (a b cin carry : Wire)
    (hnd : [a, b, cin, carry].Nodup) (A B C : Bool) :
    {{ a = A, b = B, cin = C, carry = carryBit A B C }} eraseCarry a b cin carry
    {{ a = A, b = B, cin = C, carry = false }} := by
  intro s m hP
  simp only [Holds.holds] at hP ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨_, _, ha⟩, ⟨_, hb⟩, hc⟩ := hnd
  rw [eraseCarry_correct a b cin carry ha hb hc s (by simp_all) m]
  simp_all [writeBit, Function.update]

/-- 一位全加器只有一个 Toffoli。 -/
theorem fullAdder_toffoliCount (a b cin out carry : Wire) :
    toffoliCount (fullAdder a b cin out carry) = 1 := rfl

theorem fullAdder_measurementCount (a b cin out carry : Wire) :
    measurementCount (fullAdder a b cin out carry) = 0 := rfl

/-- 进位清理使用一次测量和零个 Toffoli。 -/
theorem eraseCarry_resources (a b cin carry : Wire) :
    toffoliCount (eraseCarry a b cin carry) = 0 ∧
    measurementCount (eraseCarry a b cin carry) = 1 := ⟨rfl, rfl⟩

theorem fullAdder_wires (a b cin out carry : Wire) :
    wires (fullAdder a b cin out carry) = {a, b, cin, out, carry} := by
  ext w
  simp [fullAdder, wires, Instr.wires]
  tauto

theorem eraseCarry_wires (a b cin carry : Wire) :
    wires (eraseCarry a b cin carry) = {a, b, cin, carry} := by
  ext w
  simp [eraseCarry, wires, Instr.wires, correctionWires]
  tauto

/-- 五线互异时，一位全加器的静态线路数为 5。 -/
theorem fullAdder_qubitCount (a b cin out carry : Wire)
    (hnd : [a, b, cin, out, carry].Nodup) :
    qubitCount (fullAdder a b cin out carry) = 5 := by
  rw [qubitCount, fullAdder_wires]
  have h := List.toFinset_card_of_nodup hnd
  simpa using h

/-- 四线互异时，进位测量清理的静态线路数为 4。 -/
theorem eraseCarry_qubitCount (a b cin carry : Wire)
    (hnd : [a, b, cin, carry].Nodup) :
    qubitCount (eraseCarry a b cin carry) = 4 := by
  rw [qubitCount, eraseCarry_wires]
  have h := List.toFinset_card_of_nodup hnd
  simpa using h

/-- 和位加上二倍进位，恰好等于三个输入位的自然数之和。 -/
theorem fullAdder_bit_value (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat =
      a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

end ECDSAAdd.Arithmetic
