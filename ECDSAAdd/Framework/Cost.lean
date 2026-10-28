import ECDSAAdd.Framework.Semantics
import Mathlib.Data.Finset.Card

namespace ECDSAAdd

def toffoliCount : Program → Nat
  | [] => 0
  | .CCX _ _ _ :: p => 1 + toffoliCount p
  | _ :: p => toffoliCount p

def correctionWires : List Correction → Finset Wire
  | [] => ∅
  | .Z t :: cs => {t} ∪ correctionWires cs
  | .CZ a b :: cs => {a, b} ∪ correctionWires cs

def Instr.wires : Instr → Finset Wire
  | .X t => {t}
  | .CX c t => {c, t}
  | .CCX a b t => {a, b, t}
  | .measureX t c₀ c₁ => {t} ∪ correctionWires c₀ ∪ correctionWires c₁

/-- 静态线路并集包含两条修正列表，不是每条指令的线路数之和。 -/
def wires : Program → Finset Wire
  | [] => ∅
  | i :: p => i.wires ∪ wires p

/-- 不同物理线路数，不声称最大同时存活数。 -/
def qubitCount (p : Program) : Nat := (wires p).card

@[simp] theorem measurementCount_append (p q : Program) :
    measurementCount (p ++ q) = measurementCount p + measurementCount q := by
  induction p with
  | nil => simp [measurementCount]
  | cons i p ih => cases i <;> simp [measurementCount, ih, Nat.add_assoc]

@[simp] theorem toffoliCount_append (p q : Program) :
    toffoliCount (p ++ q) = toffoliCount p + toffoliCount q := by
  induction p with
  | nil => simp [toffoliCount]
  | cons i p ih => cases i <;> simp [toffoliCount, ih, Nat.add_assoc]

@[simp] theorem wires_append (p q : Program) : wires (p ++ q) = wires p ∪ wires q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih => simp [wires, ih, Finset.union_assoc]

/-- 对所有测量结果，程序不会修改声明线路集合以外的位。 -/
theorem run_preserves_outside (p : Program) (m : List Bool) (s : State) (w : Wire)
    (hw : w ∉ wires p) : (run p m s).basis w = s.basis w := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    have hi : w ∉ i.wires := fun h => hw (Finset.mem_union_left _ h)
    have hp : w ∉ wires p := fun h => hw (Finset.mem_union_right _ h)
    cases i <;> simp only [run] <;> rw [ih _ _ hp] <;>
      simp_all [Instr.wires, measureAndCorrect, writeBit, Function.update]

end ECDSAAdd
