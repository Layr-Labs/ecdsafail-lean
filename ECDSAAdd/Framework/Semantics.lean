import ECDSAAdd.Framework.Syntax

namespace ECDSAAdd

def writeBit (bits : BasisState) (w : Wire) (v : Bool) : BasisState :=
  Function.update bits w v

def correct : List Correction → State → State
  | [], s => s
  | .Z t :: cs, s => correct cs ⟨s.phase ^^ s.basis t, s.basis⟩
  | .CZ a b :: cs, s => correct cs ⟨s.phase ^^ (s.basis a && s.basis b), s.basis⟩

/-- 先用清零前的位更新相位，再清零，最后按测量结果立即修正。 -/
def measureAndCorrect (t : Wire) (c₀ c₁ : List Correction) (m : Bool) (s : State) : State :=
  correct (if m then c₁ else c₀)
    ⟨s.phase ^^ (m && s.basis t), writeBit s.basis t false⟩

/-- 按表头消费测量结果；不足时补 0，多余结果忽略。全称量化仍覆盖所有分支。 -/
def run : Program → List Bool → State → State
  | [], _, s => s
  | .X t :: p, m, s => run p m ⟨s.phase, writeBit s.basis t (!s.basis t)⟩
  | .CX c t :: p, m, s => run p m ⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis c)⟩
  | .CCX a b t :: p, m, s =>
      run p m ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩
  | .measureX t c₀ c₁ :: p, m, s =>
      run p m.tail (measureAndCorrect t c₀ c₁ (m.headD false) s)

/-- 相位修正不改变任何 basis 位。 -/
@[simp] theorem correct_basis (cs : List Correction) (s : State) :
    (correct cs s).basis = s.basis := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [correct, ih]

/-- 执行只读取本程序需要的测量结果。 -/
theorem run_take (p : Program) (m : List Bool) (s : State) :
    run p (m.take (measurementCount p)) s = run p m s := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [measurementCount, run]
    all_goals try exact ih m _
    cases m <;> simp [ih, Nat.add_comm]

/-- 顺序执行两个程序，记录用 take/drop 按第一段的测量次数拆分。 -/
theorem run_append (p q : Program) (m : List Bool) (s : State) :
    run (p ++ q) m s =
      run q (m.drop (measurementCount p)) (run p (m.take (measurementCount p)) s) := by
  rw [run_take]
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [List.cons_append, run, measurementCount]
    all_goals try exact ih m _
    cases m <;> simp [ih, Nat.add_comm]

end ECDSAAdd
