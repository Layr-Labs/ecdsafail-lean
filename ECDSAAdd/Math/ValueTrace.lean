import ECDSAAdd.Math.ValueReplay

namespace ECDSAAdd

theorem valueStep_count (i : Nat) (z : ValueState)
    (hk : z.k ≤ i ∧ (z.v ≠ 0 → z.k=i)) :
    (valueStep z).k ≤ i+1 ∧ ((valueStep z).v ≠ 0 → (valueStep z).k=i+1) := by
  let full : KState := ⟨z.u,z.v,0,0,z.k⟩
  have h := kaliski_round_count_step i full hk
  have hv := congrArg ValueState.v (valueStep_projection full)
  have hk' := congrArg ValueState.k (valueStep_projection full)
  change (kaliskiStep full).v=(valueStep z).v at hv
  change (kaliskiStep full).k=(valueStep z).k at hk'
  simpa only [KRoundCount,hv,hk'] using h

theorem valueIter_k_mono (n : Nat) (z : ValueState) : z.k ≤ (valueStep^[n] z).k := by
  have hs (z : ValueState) : z.k ≤ (valueStep z).k := by
    unfold valueStep
    split_ifs <;> simp_all
  induction n generalizing z with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (hs z).trans (ih (valueStep z))

/-- 每个非空后缀的最终计数恢复当前活动位，包括终止后的填充轮。 -/
theorem value_active_final (n i : Nat) (z : ValueState)
    (hk : z.k ≤ i ∧ (z.v ≠ 0 → z.k=i)) :
    (i < (valueStep^[n+1] z).k) ↔ z.v ≠ 0 := by
  by_cases hz : z.v=0
  · have hs : valueStep z=z := by simp [valueStep,hz]
    have hi : valueStep^[n+1] z=z := Function.iterate_fixed hs _
    rw [hi]
    simp [hz,show ¬i<z.k by omega]
  · have hs : (valueStep z).k=z.k+1 := by unfold valueStep; split_ifs <;> simp_all
    have hm := valueIter_k_mono n (valueStep z)
    rw [Function.iterate_succ_apply,hs] at *
    have he := hk.2 hz
    constructor
    · intro _; exact hz
    · intro _; omega

end ECDSAAdd
