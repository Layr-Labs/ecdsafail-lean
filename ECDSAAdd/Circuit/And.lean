import ECDSAAdd.Framework.Hoare

namespace ECDSAAdd
open Instr Correction

/-- AND 计算后立即测量反计算：结果 1 时做 CZ，结果 0 时不修正。 -/
def andComputeErase (a b anc : Wire) : Program := prog {
  CCX a b anc;
  if meas anc = 1 then CZ a b else skip
}

/-- 辅助位初始为零时，程序恢复整个状态，包括相位和所有外部线路。 -/
theorem andComputeErase_correct (a b anc : Wire)
    (ha : a ≠ anc) (hb : b ≠ anc) (s : State) (hclean : s.basis anc = false)
    (m : List Bool) : run (andComputeErase a b anc) m s = s := by
  have hclear : writeBit s.basis anc false = s.basis := by
    funext w
    by_cases h : w = anc
    · subst w; simp [writeBit, hclean]
    · simp [writeBit, h]
  simp only [andComputeErase, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, hclean, ha, hb] <;>
    change State.mk s.phase (writeBit s.basis anc false) = s <;> rw [hclear]

/-- 三线互异：任意 A、B 的 AND 计算与测量反计算保持数据，辅助位归零。
Triple 的定义还保证初始相位恢复，并覆盖所有测量结果。 -/
theorem andComputeErase_spec (a b anc : Wire) (hnd : [a, b, anc].Nodup) (A B : Bool) :
    {{ a = A, b = B, anc = false }} andComputeErase a b anc
    {{ a = A, b = B, anc = false }} := by
  intro s m hP
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
    List.not_mem_nil, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨_, ha⟩, hb⟩ := hnd
  rw [andComputeErase_correct a b anc ha hb s hP.2 m]
  exact ⟨rfl, hP⟩

/-- 同一程序恰好使用一个 Toffoli。 -/
theorem andComputeErase_toffoliCount (a b anc : Wire) :
    toffoliCount (andComputeErase a b anc) = 1 := rfl

/-- 同一程序恰好测量一次。 -/
theorem andComputeErase_measurementCount (a b anc : Wire) :
    measurementCount (andComputeErase a b anc) = 1 := rfl

theorem andComputeErase_wires (a b anc : Wire) :
    wires (andComputeErase a b anc) = {a, b, anc} := by
  ext w
  simp [andComputeErase, wires, Instr.wires, correctionWires]
  tauto

/-- 三线互异时，静态物理线路数恰好为 3。 -/
theorem andComputeErase_qubitCount (a b anc : Wire) (hnd : [a, b, anc].Nodup) :
    qubitCount (andComputeErase a b anc) = 3 := by
  rw [qubitCount, andComputeErase_wires]
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
    List.not_mem_nil, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨hab, ha⟩, hb⟩ := hnd
  simp [hab, ha, hb]

end ECDSAAdd
