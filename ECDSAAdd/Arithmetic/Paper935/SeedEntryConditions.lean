import ECDSAAdd.Arithmetic.Paper935.Seed

namespace ECDSAAdd.Arithmetic.Paper935

/-- The concrete seed accepts arbitrary x/A data, but requires both the
second host and every remaining auxiliary address to be clean. -/
theorem seedBefore_ready_iff (s : BasisState) :
    seedBefore.Ready s ↔
      (∀ q∈yHost,s q=false) ∧ (∀ q : Wire,768≤q → q<935 → s q=false) := by
  simp only [Arena.Ready,seedBefore,arenaWires,xHost,yHost,aHost,
    Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
  dsimp only [Wire] at *
  constructor
  · intro h
    constructor
    · intro q hq
      exact h q (by omega) (by omega)
    · intro q lo hi
      exact h q hi (by omega)
  · rintro ⟨hy,ha⟩ q hq hn
    by_cases h : q<512
    · exact hy q (by omega)
    · exact ha q (by omega) hq

/-- A zero unsigned y word is equivalent to zero on every y host wire. -/
theorem seedF_zero_iff (s : BasisState) :
    regValue seedF s=0 ↔ ∀ q∈yHost,s q=false := by
  rw [regValue_zero]
  simp only [seedF,yHost,List.mem_range'_1,Finset.mem_Ico]

/-- Callers may state the y cleaning obligation as a register-value equality.
The auxiliary zero obligation remains separate and cannot be dropped. -/
theorem seedBefore_ready_iff_word (s : BasisState) :
    seedBefore.Ready s ↔
      regValue seedF s=0 ∧ (∀ q : Wire,768≤q → q<935 → s q=false) := by
  rw [seedBefore_ready_iff,seedF_zero_iff]

/-- Changing only caller-owned x/A data preserves the seed's zero conditions. -/
theorem seedBefore_ready_of_agree (s t : BasisState) (ready : seedBefore.Ready s)
    (agree : ∀ q∈arenaWires,q∉xHost∪aHost → t q=s q) :
    seedBefore.Ready t := by
  intro q hq hn
  rw [agree q hq hn]
  exact ready q hq hn

end ECDSAAdd.Arithmetic.Paper935
