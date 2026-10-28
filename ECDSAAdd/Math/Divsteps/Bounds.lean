import ECDSAAdd.Math.Divsteps.Recovery
import Mathlib.Tactic

namespace ECDSAAdd.Divsteps

/-- Conservative signed bounds; these do not assume a sampled trajectory. -/
structure Bounds (pB zB cB : Int) (s : ZState) : Prop where
  f_lo : -pB ≤ s.f
  f_hi : s.f ≤ pB
  g_lo : -pB ≤ s.g
  g_hi : s.g ≤ pB
  z_lo : -zB ≤ s.z
  z_hi : s.z ≤ zB
  fv_lo : -cB ≤ s.fv
  fv_hi : s.fv ≤ cB
  gv_lo : -cB ≤ s.gv
  gv_hi : s.gv ≤ cB

/-- One exact integer step needs no more integer magnitude, one extra
counter unit, and at most twice the coefficient magnitude. -/
theorem zStep_bounds {pB zB cB : Int} {s : ZState}
    (hp : 0 ≤ pB) (_hz : 0 ≤ zB) (_hc : 0 ≤ cB)
    (h : Bounds pB zB cB s) : Bounds pB (zB + 1) (2 * cB) (zStep s) := by
  rcases h with ⟨hfl, hfh, hgl, hgh, hzl, hzh, hvl, hvh, hwl, hwh⟩
  have hg : s.g % 2 = 0 ∨ s.g % 2 = 1 := by omega
  rcases hg with hg | hg
  all_goals
    unfold zStep
    split
    · constructor <;> dsimp <;> omega
    · constructor <;> simp only [hg, zero_mul, one_mul, add_zero] <;> omega

/-- Widening a bound changes no program/state. -/
theorem Bounds.mono {pB zB cB zB' cB' : Int} {s : ZState}
    (h : Bounds pB zB cB s) (hz : zB ≤ zB') (hc : cB ≤ cB') :
    Bounds pB zB' cB' s := by
  rcases h with ⟨hfl, hfh, hgl, hgh, hzl, hzh, hvl, hvh, hwl, hwh⟩
  constructor <;> omega

/-- Every canonical-input frozen walk has deterministic conservative bounds.
No termination certificate, probability assumption or `native_decide` is used. -/
theorem zWalk_bounds (p x : Int) (hp : 0 ≤ p) (hx0 : 0 ≤ x) (hxp : x ≤ p)
    (t : Nat) : Bounds p (t : Int) ((2 : Int)^t) (zWalk p x t) := by
  induction t with
  | zero =>
      constructor <;> simp [zWalk, zSeed] <;> omega
  | succ t ih =>
      rw [zWalk_succ]
      split
      · apply ih.mono
        · simp
        · have hpos : (0 : Int) ≤ 2^t := by positivity
          rw [pow_succ]
          omega
      · simpa [pow_succ, mul_comm] using
          zStep_bounds hp (by omega : (0 : Int) ≤ t) (by positivity) ih

end ECDSAAdd.Divsteps
