import ECDSAAdd.Math.Kaliski

namespace ECDSAAdd

/-- 完整两位记录：(是否交换 u/v 与 r/s，是否需要减法)。终止后取 00。 -/
def kaliskiCode (z : KState) : Bool × Bool :=
  if z.v = 0 then (false, false)
  else if z.u%2 = 0 then (false, false)
  else if z.v%2 = 0 then (true, false)
  else if z.v < z.u then (false, true)
  else (true, true)

/-- 固定轮号 i 的可达计数关系：尚未终止时 k=i，终止后 k≤i。 -/
def KRoundCount (i : Nat) (z : KState) : Prop := z.k ≤ i ∧ (z.v ≠ 0 → z.k = i)

theorem kaliski_round_count_init (p a : Nat) : KRoundCount 0 (kaliskiInit p a) := by
  simp [KRoundCount, kaliskiInit]

theorem kaliski_round_count_step (i : Nat) (z : KState) (h : KRoundCount i z) :
    KRoundCount (i+1) (kaliskiStep z) := by
  obtain ⟨hk, hv⟩ := h
  unfold kaliskiStep KRoundCount
  split_ifs with hz hu he hc
  · simp [hz]; omega
  all_goals have hki := hv hz
  all_goals dsimp; omega

/-- 正轮结束后由 i<k 判定本轮是否活动，无需再保存第三个记录位。 -/
theorem kaliski_round_active (i : Nat) (z : KState) (h : KRoundCount i z) :
    i < (kaliskiStep z).k ↔ z.v ≠ 0 := by
  obtain ⟨hk, hv⟩ := h
  unfold kaliskiStep
  split_ifs with hz hu he hc
  · simp [hz]; omega
  all_goals have hki := hv hz
  all_goals dsimp; omega

/-- 逆轮用固定 i、更新后的 k 和保存的两位分支，不能重新读取已变化的奇偶位。 -/
def kaliskiUnstep (i : Nat) (code : Bool × Bool) (z : KState) : KState :=
  if i < z.k then
    match code with
    | (false, false) => ⟨2*z.u, z.v, z.r, z.s/2, z.k-1⟩
    | (true, false) => ⟨z.u, 2*z.v, z.r/2, z.s, z.k-1⟩
    | (false, true) => ⟨2*z.u+z.v, z.v, z.r-z.s/2, z.s/2, z.k-1⟩
    | (true, true) => ⟨z.u, 2*z.v+z.u, z.r/2, z.s-z.r/2, z.k-1⟩
  else z

/-- 两位记录加计数足够恢复完整旧状态，包括终止轮与后续恒等轮。 -/
theorem kaliski_unstep_step (i : Nat) (z : KState) (h : KRoundCount i z) :
    kaliskiUnstep i (kaliskiCode z) (kaliskiStep z) = z := by
  have ha := kaliski_round_active i z h
  unfold kaliskiUnstep
  by_cases hv : z.v = 0
  · simp [kaliskiStep, hv, show ¬i < z.k by exact Nat.not_lt.mpr h.1]
  · rw [if_pos (ha.mpr hv)]
    rcases z with ⟨u,v,r,s,k⟩
    simp only [kaliskiCode, kaliskiStep, hv, if_false]
    split_ifs with hu he hc
    all_goals simp only [Nat.add_sub_cancel]
    all_goals congr 1 <;> omega

/-- 两组寄存器同步交换，把四种情形归一成对 u/r 的一次减/加。 -/
def kaliskiSwap (b : Bool) (z : KState) : KState :=
  if b then ⟨z.v,z.u,z.s,z.r,z.k⟩ else z

/-- 记录驱动的统一算术体。活动位单独控制移位与计数，00 不等于“不活动”。 -/
def kaliskiBody (active : Bool) (code : Bool × Bool) (z : KState) : KState :=
  let t := kaliskiSwap code.1 z
  let u := t.u - if code.2 then t.v else 0
  let r := t.r + if code.2 then t.s else 0
  kaliskiSwap code.1 ⟨if active then u/2 else u, t.v, r,
    if active then 2*t.s else t.s, t.k+active.toNat⟩

theorem kaliski_body_step (z : KState) :
    kaliskiBody (decide (z.v≠0)) (kaliskiCode z) z = kaliskiStep z := by
  rcases z with ⟨u,v,r,s,k⟩
  unfold kaliskiCode kaliskiStep
  split_ifs <;> simp_all [kaliskiBody, kaliskiSwap, Bool.toNat, Nat.add_comm]

/-- 正轮活动时，统一体的减法不下溢且结果为偶数；加法与左移均装得进 n+1 位。 -/
theorem kaliski_body_bounds (p a n : Nat) (z : KState) (hi : KInvariant p a z)
    (hv : z.v≠0) (hp : p<2^n) :
    let code := kaliskiCode z
    let t := kaliskiSwap code.1 z
    (if code.2 then t.v else 0) ≤ t.u ∧
    (t.u-(if code.2 then t.v else 0))%2=0 ∧
    t.r+(if code.2 then t.s else 0)<2^(n+1) ∧ 2*t.s<2^(n+1) := by
  obtain ⟨huz, hsz, he, _, _, _⟩ := hi
  have hvz : 0<z.v := by omega
  have hr : z.r<p := by nlinarith
  have hs : z.s≤p := by nlinarith
  have hrs : z.r+z.s≤p := by nlinarith
  unfold kaliskiCode
  simp only [hv, if_false]
  split_ifs with heU heV hlt
  all_goals simp_all [kaliskiSwap, pow_succ] <;> omega

/-- 电路的两个 XOR 记录函数就是数学层的四分支编码。 -/
theorem kaliski_code_bits (z : KState) :
    let A := decide (z.v≠0)
    let U := decide (z.u%2≠0)
    let V := decide (z.v%2≠0)
    let B := decide (z.v<z.u)
    kaliskiCode z = ((A && U) ^^ (A && U && V && B), A && U && V) := by
  unfold kaliskiCode
  split_ifs <;> simp_all

end ECDSAAdd
