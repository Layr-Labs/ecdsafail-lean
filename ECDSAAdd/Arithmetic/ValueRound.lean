import ECDSAAdd.Arithmetic.ValueBody

namespace ECDSAAdd.Arithmetic

/-- 两位记录轮沿用原控制段，只以值走体替换原四字算术体。 -/
def valueRound (L : KaliskiRoundLayout) (i : Nat) : Program :=
  loadActive L ++ recordRound L ++ valueBodyProgram L.data L.active L.swap L.subtract ++
  counterInc L.counter ++ zeroControlled L.active L.done (L.data.zeroBits .v) ++ roundActiveXor L i

def valueUnround (L : KaliskiRoundLayout) (i : Nat) : Program :=
  roundActiveXor L i ++ zeroControlled L.active L.done (L.data.zeroBits .v) ++
  valueUnbodyProgram L.data L.active L.swap L.subtract ++ counterDec L.counter.swapCounter ++
  recordRound L ++ loadActive L

@[simp] theorem valueKStep_fields (z : KState) :
    (valueKStep z).u=(kaliskiStep z).u ∧ (valueKStep z).v=(kaliskiStep z).v ∧
    (valueKStep z).k=(kaliskiStep z).k := by
  exact ⟨congrArg ValueState.u (valueStep_projection z).symm,
    congrArg ValueState.v (valueStep_projection z).symm,
    congrArg ValueState.k (valueStep_projection z).symm⟩

private theorem value_round_count_step (i : Nat) (z : KState) (h : KRoundCount i z) :
    KRoundCount (i+1) (valueKStep z) := by
  simpa only [KRoundCount,(valueKStep_fields z).2.1,(valueKStep_fields z).2.2] using
    kaliski_round_count_step i z h

private theorem value_round_active (i : Nat) (z : KState) (h : KRoundCount i z) :
    i<(valueKStep z).k ↔ z.v ≠ 0 := by
  rw [(valueKStep_fields z).2.2]
  exact kaliski_round_active i z h

private theorem value_step_counter (z : KState) :
    (valueKStep z).k=z.k+(decide (z.v ≠ 0)).toNat := by
  rw [(valueKStep_fields z).2.2]
  exact step_counter z

private theorem value_step_done (z : KState) :
    (decide (z.v=0) ^^ (decide (z.v ≠ 0) && decide ((valueKStep z).v=0))) =
      decide ((valueKStep z).v=0) := by
  rw [(valueKStep_fields z).2.1]
  exact step_done z

/-- 一轮完整正向规格：仅更新 u/v 和计数，保存两位分支，恢复工作区。
r/s 作为任意旁路值保持；计数更新包含使 v 首次为零的终止轮。 -/
theorem valueRound_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i : Nat) (z : KState)
    (hi : i<512) (hk : KRoundCount i z)
    (hu : z.u<2^L.data.width) (hv : z.v<2^L.data.width) :
    Triple (RoundState L z z.k 0 false (decide (z.v=0)) false false) (valueRound L i)
      (RoundState L (valueKStep z) 0 (valueKStep z).k false (decide ((valueKStep z).v=0))
        (kaliskiCode z).1 (kaliskiCode z).2) := by
  let A := decide (z.v≠0)
  let code := kaliskiCode z
  have hA : (!decide (z.v=0))=A := by simp [A]
  have hcount : (valueKStep z).k≤512 := (value_round_count_step i z hk).1.trans (by omega)
  have hmod : (z.k+A.toNat)%1024=(valueKStep z).k := by
    rw [← value_step_counter z]
    exact Nat.mod_eq_of_lt (by omega)
  have hactive : decide (i < (valueKStep z).k)=A := by
    simp only [A,value_round_active i z hk]
  have h1 := loadActive_state L hnd z z.k 0 false (decide (z.v=0)) false false
  simp only [Bool.false_xor,hA] at h1
  have h2 := recordRound_state L hnd z z.k 0 (decide (z.v=0)) false false
  simp only [Bool.false_xor] at h2
  have h3 := valueBodyProgram_state L hnd z z.k 0 (decide (z.v=0)) hu hv
  have h4 := counterInc_state L hnd hw (valueKStep z) z.k A (decide (z.v=0)) code.1 code.2
  rw [hmod] at h4
  have h5 := zeroDone_state L hnd (valueKStep z) 0 (valueKStep z).k A (decide (z.v=0)) code.1 code.2
  rw [value_step_done] at h5
  have h6 := roundActiveXor_state L hnd hw (valueKStep z) (valueKStep z).k i hi A
    (decide ((valueKStep z).v=0)) code.1 code.2
  rw [hactive,Bool.xor_self] at h6
  exact ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6

/-- 一轮完整逆向规格：由更新后 k 恢复活动性，清除保存的两位记录并恢复旧状态。 -/
theorem valueUnround_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i : Nat) (z : KState)
    (hi : i<512) (hk : KRoundCount i z)
    (hu : z.u<2^L.data.width) (hv : z.v<2^L.data.width) :
    Triple (RoundState L (valueKStep z) 0 (valueKStep z).k false (decide ((valueKStep z).v=0))
        (kaliskiCode z).1 (kaliskiCode z).2) (valueUnround L i)
      (RoundState L z z.k 0 false (decide (z.v=0)) false false) := by
  let A := decide (z.v≠0)
  let code := kaliskiCode z
  have hcount : (valueKStep z).k≤512 := (value_round_count_step i z hk).1.trans (by omega)
  have hactive : decide (i < (valueKStep z).k)=A := by
    simp only [A,value_round_active i z hk]
  have hmod : ((valueKStep z).k+1024-A.toNat)%1024=z.k := by
    rw [value_step_counter]
    have hk0 : z.k<1024 := by have h := hk.1; omega
    change (z.k+A.toNat+1024-A.toNat)%1024=z.k
    rw [show z.k+A.toNat+1024-A.toNat=z.k+1024 by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hk0]
  have hdone : (decide ((valueKStep z).v=0) ^^ (A && decide ((valueKStep z).v=0))) = decide (z.v=0) := by
    have h := value_step_done z
    change (decide (z.v=0) ^^ (A && decide ((valueKStep z).v=0)))=decide ((valueKStep z).v=0) at h
    calc
      _ = ((decide (z.v=0) ^^ (A && decide ((valueKStep z).v=0))) ^^
          (A && decide ((valueKStep z).v=0))) := congrArg (fun b => b ^^ (A && decide ((valueKStep z).v=0))) h.symm
      _ = _ := by simp
  have h1 := roundActiveXor_state L hnd hw (valueKStep z) (valueKStep z).k i hi false
    (decide ((valueKStep z).v=0)) code.1 code.2
  rw [Bool.false_xor,hactive] at h1
  have h2 := zeroDone_state L hnd (valueKStep z) 0 (valueKStep z).k A (decide ((valueKStep z).v=0)) code.1 code.2
  rw [hdone] at h2
  have h3 := valueUnbodyProgram_state L hnd z 0 (valueKStep z).k (decide (z.v=0)) hu hv
  have h4 := counterDec_state L hnd hw z (valueKStep z).k A (decide (z.v=0)) code.1 code.2
  rw [hmod] at h4
  have h5 := recordRound_state L hnd z z.k 0 (decide (z.v=0)) code.1 code.2
  simp only [code,Bool.xor_self] at h5
  have h6 := loadActive_state L hnd z z.k 0 A (decide (z.v=0)) false false
  have hA : (!decide (z.v=0))=A := by simp [A]
  rw [hA,Bool.xor_self] at h6
  exact ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6


end ECDSAAdd.Arithmetic
