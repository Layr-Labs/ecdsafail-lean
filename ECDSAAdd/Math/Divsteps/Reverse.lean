import ECDSAAdd.Math.Divsteps.Recovery

namespace ECDSAAdd.Divsteps

/-- Restore one active step from its swap and parity history. These are
integer operations; finite registers must separately satisfy `Bounds`. -/
def zUnstep (swap : Bool) (b : Int) (t : ZState) : ZState :=
  if swap then
    ⟨-t.z, t.f - 2 * t.g, t.f, t.fv / 2 - t.gv, t.fv / 2⟩
  else
    ⟨t.z - 1, t.f, 2 * t.g - b * t.f, t.fv / 2, t.gv - b * (t.fv / 2)⟩

/-- The recorded branch bits suffice for exact restoration, including
negative intermediate values. No step-count or prime assumption is needed. -/
theorem zUnstep_zStep (s : ZState) (hf : s.f % 2 = 1) :
    zUnstep (decide (0 ≤ s.z ∧ s.g % 2 = 1)) (bbit s) (zStep s) = s := by
  rcases s with ⟨z, f, g, fv, gv⟩
  dsimp at hf
  by_cases hs : 0 ≤ z ∧ g % 2 = 1
  · simp [zStep, zUnstep, hs]
    omega

  · simp only [zStep, zUnstep, bbit]
    dsimp
    simp only [hs, ↓reduceIte, decide_false, Bool.false_eq_true]
    rcases (by omega : g % 2 = 0 ∨ g % 2 = 1) with hg | hg
    · simp only [hg, zero_mul, add_zero, sub_zero]
      congr 1 <;> omega
    · simp only [hg, one_mul]
      congr 1 <;> omega

/-- A frozen schedule slot records that it was inactive. This extra bit
makes zero inputs and early termination reversible without a timing guess. -/
def zSlot (s : ZState) : ZState := if s.g = 0 then s else zStep s

def zUnslot (active swap : Bool) (b : Int) (s : ZState) : ZState :=
  if active then zUnstep swap b s else s

theorem zUnslot_zSlot (s : ZState) (hf : s.f % 2 = 1) :
    zUnslot (decide (s.g ≠ 0)) (decide (0 ≤ s.z ∧ s.g % 2 = 1))
      (bbit s) (zSlot s) = s := by
  by_cases hg : s.g = 0
  · simp [zUnslot, zSlot, hg]
  · simpa [zUnslot, zSlot, hg] using zUnstep_zStep s hf

end ECDSAAdd.Divsteps
