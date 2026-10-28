import ECDSAAdd.Math.KaliskiRound

namespace ECDSAAdd

/-- 奇数模数下，更新后的系数奇偶决定交换分支；终止后的恒等轮由活动位排除。 -/
theorem kaliski_swap_from_r (p a : Nat) (z : KState)
    (hinv : KInvariant p a z) (hodd : p%2=1) :
    (kaliskiCode z).1 =
      (decide (z.v≠0) && decide ((kaliskiStep z).r%2=0)) := by
  have he := (kaliski_invariant p a z hinv).2.2.1
  have hm := congrArg (fun n : Nat => n%2) he
  dsimp at hm
  rw [hodd] at hm
  have hr : (kaliskiStep z).s%2=0 → (kaliskiStep z).r%2≠0 := by
    intro hs hr
    simp [Nat.add_mod, Nat.mul_mod, hs, hr] at hm
  unfold kaliskiCode
  split_ifs with hv hu he hc
  · simp [hv]
  · have hs : (kaliskiStep z).s%2=0 := by simp [kaliskiStep,hv,hu]
    simp [hv,hr hs]
  · simp [kaliskiStep,hv,hu,he]
  · have hs : (kaliskiStep z).s%2=0 := by simp [kaliskiStep,hv,hu,he,hc]
    simp [hv,hr hs]
  · simp [kaliskiStep,hv,hu,he,hc]

end ECDSAAdd
