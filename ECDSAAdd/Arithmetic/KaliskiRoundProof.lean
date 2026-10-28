import ECDSAAdd.Arithmetic.RoundControls

namespace ECDSAAdd.Arithmetic

theorem round_body_bounds (L : KaliskiRoundLayout) (p a : Nat) (z : KState)
    (hi : KInvariant p a z) (hp : p<2^L.low.length)
    (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) (hr : z.r<2^L.data.width) :
    let A := decide (z.v≠0)
    let code := kaliskiCode z
    let t := kaliskiSwap code.1 z
    t.u<2^L.data.width ∧
    (if code.2 then t.v else 0)≤t.u ∧
    t.r+(if code.2 then t.s else 0)<2^L.data.width ∧
    (A=true → (t.u-(if code.2 then t.v else 0))%2=0) ∧
    (A=true → 2*t.s<2^L.data.width) := by
  have hw : L.data.width=L.low.length+1 := by simp [KaliskiRoundLayout.data,RoundDataLayout.width]
  have hpow : 2^L.low.length≤2^L.data.width := by rw [hw,pow_succ]; omega
  have hut : (kaliskiSwap (kaliskiCode z).1 z).u<2^L.data.width := by
    cases (kaliskiCode z).1 <;> simp [kaliskiSwap] <;> omega
  by_cases hz : z.v=0
  · simpa [kaliskiCode,hz,kaliskiSwap] using (show z.u<2^L.data.width ∧ z.r<2^L.data.width from ⟨hu.trans_le hpow,hr⟩)
  · have h := kaliski_body_bounds p a L.low.length z hi hz hp
    rw [← hw] at h
    exact ⟨hut,h.1,h.2.2.1,fun _ => h.2.1,fun _ => h.2.2.2⟩

theorem step_counter (z : KState) :
    (kaliskiStep z).k=z.k+(decide (z.v≠0)).toNat := by
  unfold kaliskiStep
  split_ifs <;> simp_all [Bool.toNat]

theorem step_done (z : KState) :
    (decide (z.v=0) ^^ (decide (z.v≠0) && decide ((kaliskiStep z).v=0))) =
      decide ((kaliskiStep z).v=0) := by
  by_cases hz : z.v=0
  · simp [kaliskiStep,hz]
  · simp [hz]

/-- 一轮完整正向规格：更新四份数据和计数，保存两位分支，恢复所有工作区。
范围条件来自 I1 的可达状态界；计数更新包含使 v 首次为零的终止轮。 -/
theorem kaliskiRound_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i p a : Nat) (z : KState)
    (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length)
    (hr : z.r<2^L.data.width) :
    Triple (RoundState L z z.k 0 false (decide (z.v=0)) false false) (kaliskiRound L i)
      (RoundState L (kaliskiStep z) 0 (kaliskiStep z).k false (decide ((kaliskiStep z).v=0))
        (kaliskiCode z).1 (kaliskiCode z).2) := by
  let A := decide (z.v≠0)
  let code := kaliskiCode z
  have hA : (!decide (z.v=0))=A := by simp [A]
  have hcount : (kaliskiStep z).k≤512 := (kaliski_round_count_step i z hk).1.trans (by omega)
  have hmod : (z.k+A.toNat)%1024=(kaliskiStep z).k := by
    rw [← step_counter z]
    exact Nat.mod_eq_of_lt (by omega)
  have hactive : decide (i < (kaliskiStep z).k)=A := by
    simp only [A,kaliski_round_active i z hk]
  have h1 := loadActive_state L hnd z z.k 0 false (decide (z.v=0)) false false
  simp only [Bool.false_xor,hA] at h1
  have h2 := recordRound_state L hnd z z.k 0 (decide (z.v=0)) false false
  simp only [Bool.false_xor] at h2
  obtain ⟨hU,hsub,hR,heven,hfit⟩ := round_body_bounds L p a z hinv hp hu hv hr
  have h3 := kaliskiBodyProgram_state L hnd z z.k 0 A (decide (z.v=0)) code.1 code.2 hU hsub hR heven hfit
  change Triple _ _ (RoundState L (kaliskiBody A code z) z.k 0 A (decide (z.v=0)) code.1 code.2) at h3
  rw [kaliski_body_step] at h3
  have h4 := counterInc_state L hnd hw (kaliskiStep z) z.k A (decide (z.v=0)) code.1 code.2
  rw [hmod] at h4
  have h5 := zeroDone_state L hnd (kaliskiStep z) 0 (kaliskiStep z).k A (decide (z.v=0)) code.1 code.2
  rw [step_done] at h5
  have h6 := roundActiveXor_state L hnd hw (kaliskiStep z) (kaliskiStep z).k i hi A
    (decide ((kaliskiStep z).v=0)) code.1 code.2
  rw [hactive,Bool.xor_self] at h6
  exact ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6

/-- 一轮完整逆向规格：由更新后 k 恢复活动性，清除保存的两位记录并恢复旧状态。 -/
theorem kaliskiUnround_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i p a : Nat) (z : KState)
    (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length)
    (hr : z.r<2^L.data.width) :
    Triple (RoundState L (kaliskiStep z) 0 (kaliskiStep z).k false (decide ((kaliskiStep z).v=0))
        (kaliskiCode z).1 (kaliskiCode z).2) (kaliskiUnround L i)
      (RoundState L z z.k 0 false (decide (z.v=0)) false false) := by
  let A := decide (z.v≠0)
  let code := kaliskiCode z
  have hcount : (kaliskiStep z).k≤512 := (kaliski_round_count_step i z hk).1.trans (by omega)
  have hactive : decide (i < (kaliskiStep z).k)=A := by
    simp only [A,kaliski_round_active i z hk]
  have hmod : ((kaliskiStep z).k+1024-A.toNat)%1024=z.k := by
    rw [step_counter]
    have hk0 : z.k<1024 := by have h := hk.1; omega
    change (z.k+A.toNat+1024-A.toNat)%1024=z.k
    rw [show z.k+A.toNat+1024-A.toNat=z.k+1024 by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hk0]
  have hdone : (decide ((kaliskiStep z).v=0) ^^ (A && decide ((kaliskiStep z).v=0))) = decide (z.v=0) := by
    have h := step_done z
    change (decide (z.v=0) ^^ (A && decide ((kaliskiStep z).v=0)))=decide ((kaliskiStep z).v=0) at h
    calc
      _ = ((decide (z.v=0) ^^ (A && decide ((kaliskiStep z).v=0))) ^^
          (A && decide ((kaliskiStep z).v=0))) := congrArg (fun b => b ^^ (A && decide ((kaliskiStep z).v=0))) h.symm
      _ = _ := by simp
  have h1 := roundActiveXor_state L hnd hw (kaliskiStep z) (kaliskiStep z).k i hi false
    (decide ((kaliskiStep z).v=0)) code.1 code.2
  rw [Bool.false_xor,hactive] at h1
  have h2 := zeroDone_state L hnd (kaliskiStep z) 0 (kaliskiStep z).k A (decide ((kaliskiStep z).v=0)) code.1 code.2
  rw [hdone] at h2
  obtain ⟨hU,hsub,hR,heven,_⟩ := round_body_bounds L p a z hinv hp hu hv hr
  have h3 := kaliskiUnbodyProgram_state L hnd z 0 (kaliskiStep z).k A (decide (z.v=0)) code.1 code.2 hU hsub hR heven
  change Triple (RoundState L (kaliskiBody A code z) 0 (kaliskiStep z).k A (decide (z.v=0)) code.1 code.2) _ _ at h3
  rw [kaliski_body_step] at h3
  have h4 := counterDec_state L hnd hw z (kaliskiStep z).k A (decide (z.v=0)) code.1 code.2
  rw [hmod] at h4
  have h5 := recordRound_state L hnd z z.k 0 (decide (z.v=0)) code.1 code.2
  simp only [code,Bool.xor_self] at h5
  have h6 := loadActive_state L hnd z z.k 0 A (decide (z.v=0)) false false
  have hA : (!decide (z.v=0))=A := by simp [A]
  rw [hA,Bool.xor_self] at h6
  exact ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6

end ECDSAAdd.Arithmetic
