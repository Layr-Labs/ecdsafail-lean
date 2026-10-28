import ECDSAAdd.Math.KaliskiRound

namespace ECDSAAdd

/-- 值走只保留欧几里得数据与活动计数，不分配整数系数字。 -/
@[ext] structure ValueState where
  u : Nat
  v : Nat
  k : Nat
  deriving DecidableEq

def KState.value (z : KState) : ValueState := ⟨z.u,z.v,z.k⟩
def valueInit (p x : Nat) : ValueState := ⟨p,x,0⟩

def valueStep (z : ValueState) : ValueState :=
  if z.v=0 then z
  else if z.u%2=0 then ⟨z.u/2,z.v,z.k+1⟩
  else if z.v%2=0 then ⟨z.u,z.v/2,z.k+1⟩
  else if z.v<z.u then ⟨(z.u-z.v)/2,z.v,z.k+1⟩
  else ⟨z.u,(z.v-z.u)/2,z.k+1⟩

def valueCode (z : ValueState) : Bool × Bool :=
  if z.v=0 then (false,false)
  else if z.u%2=0 then (false,false)
  else if z.v%2=0 then (true,false)
  else if z.v<z.u then (false,true)
  else (true,true)

@[simp] theorem valueInit_projection (p x : Nat) :
    (kaliskiInit p x).value=valueInit p x := rfl
@[simp] theorem valueStep_projection (z : KState) :
    (kaliskiStep z).value=valueStep z.value := by
  unfold kaliskiStep valueStep KState.value
  split_ifs <;> rfl
@[simp] theorem valueCode_projection (z : KState) :
    valueCode z.value=kaliskiCode z := rfl

/-- 任意轮数逐步继承旧状态机，不以新收敛假设替代原定理。 -/
theorem valueIter_projection (n : Nat) (z : KState) :
    (kaliskiStep^[n] z).value=valueStep^[n] z.value := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply',valueStep_projection,ih]

theorem valueIter_terminal (p x n : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hp : p<2^n) (hx : x<2^n) (hc : p.Coprime x) :
    (valueStep^[2*n] (valueInit p x)).v=0 ∧
    (valueStep^[2*n] (valueInit p x)).u=1 ∧
    (valueStep^[2*n] (valueInit p x)).k≤2*n := by
  have h := kaliski_terminates p x n hp0 hx0 hp hx hc
  rw [← valueInit_projection,← valueIter_projection]
  exact h

/-- 保留两位记录和更新后的计数，逆向恢复旧的u/v。 -/
def valueUnstep (i : Nat) (code : Bool × Bool) (z : ValueState) : ValueState :=
  if i<z.k then
    match code with
    | (false,false) => ⟨2*z.u,z.v,z.k-1⟩
    | (true,false) => ⟨z.u,2*z.v,z.k-1⟩
    | (false,true) => ⟨2*z.u+z.v,z.v,z.k-1⟩
    | (true,true) => ⟨z.u,2*z.v+z.u,z.k-1⟩
  else z
@[simp] theorem valueUnstep_projection (i : Nat) (code : Bool × Bool) (z : KState) :
    (kaliskiUnstep i code z).value=valueUnstep i code z.value := by
  rcases code with ⟨a,b⟩
  cases a <;> cases b <;> unfold kaliskiUnstep valueUnstep KState.value <;>
    split_ifs <;> rfl

theorem value_unstep_step (i : Nat) (z : ValueState)
    (h : z.k ≤ i ∧ (z.v ≠ 0 → z.k = i)) :
    valueUnstep i (valueCode z) (valueStep z)=z := by
  let full : KState := ⟨z.u,z.v,0,0,z.k⟩
  have hf : KRoundCount i full := h
  have he := congrArg KState.value (kaliski_unstep_step i full hf)
  simpa only [valueUnstep_projection,valueStep_projection,← valueCode_projection] using he


/-- Per-round width envelope of the value walk: full width w early on, then 512−i from the product bound, at least 2 bits. -/
def valueWidth (w i : Nat) : Nat := min w (max 2 (512-i))

/-- Value-walk envelope invariant: u, v coprime and u·v·2^i<2^N. Every active round at least halves the product. -/
def ValueEnv (N i : Nat) (z : ValueState) : Prop :=
  Nat.Coprime z.u z.v ∧ z.u*z.v*2^i < 2^N

theorem valueStep_le (z : ValueState) : (valueStep z).u ≤ z.u ∧ (valueStep z).v ≤ z.v := by
  unfold valueStep
  split_ifs <;> (try dsimp) <;> omega

theorem valueStep_env (N i : Nat) (z : ValueState) (h : ValueEnv N i z) :
    ValueEnv N (i+1) (valueStep z) := by
  obtain ⟨hg,hlt⟩ := h
  have hN : 0<2^N := Nat.two_pow_pos N
  unfold valueStep
  split_ifs with h0 hu hv hvu
  · refine ⟨hg,?_⟩
    rw [h0,Nat.mul_zero,Nat.zero_mul]
    exact hN
  · have hd : 2 ∣ z.u := Nat.dvd_of_mod_eq_zero hu
    refine ⟨Nat.Coprime.coprime_div_left hg hd,?_⟩
    have e : z.u/2*z.v*2^(i+1)=(z.u/2*2)*z.v*2^i := by rw [pow_succ]; ring
    rw [Nat.div_mul_cancel hd] at e
    dsimp only
    rw [e]; exact hlt
  · have hd : 2 ∣ z.v := Nat.dvd_of_mod_eq_zero hv
    refine ⟨Nat.Coprime.coprime_div_right hg hd,?_⟩
    have e : z.u*(z.v/2)*2^(i+1)=z.u*(z.v/2*2)*2^i := by rw [pow_succ]; ring
    rw [Nat.div_mul_cancel hd] at e
    dsimp only
    rw [e]; exact hlt
  · have hd : 2 ∣ z.u-z.v := Nat.dvd_of_mod_eq_zero (by omega)
    have hc : Nat.Coprime (z.u-z.v) z.v := (Nat.coprime_sub_self_left hvu.le).mpr hg
    refine ⟨Nat.Coprime.coprime_div_left hc hd,?_⟩
    have e : (z.u-z.v)/2*z.v*2^(i+1)=((z.u-z.v)/2*2)*z.v*2^i := by rw [pow_succ]; ring
    rw [Nat.div_mul_cancel hd] at e
    dsimp only
    rw [e]
    refine lt_of_le_of_lt ?_ hlt
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  · have hle : z.u ≤ z.v := by omega
    have hd : 2 ∣ z.v-z.u := Nat.dvd_of_mod_eq_zero (by omega)
    have hc : Nat.Coprime z.u (z.v-z.u) := ((Nat.coprime_sub_self_left hle).mpr hg.symm).symm
    refine ⟨Nat.Coprime.coprime_div_right hc hd,?_⟩
    have e : z.u*((z.v-z.u)/2)*2^(i+1)=z.u*((z.v-z.u)/2*2)*2^i := by rw [pow_succ]; ring
    rw [Nat.div_mul_cancel hd] at e
    dsimp only
    rw [e]
    refine lt_of_le_of_lt ?_ hlt
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

theorem valueIter_env (N : Nat) (z : ValueState) (h : ValueEnv N 0 z) (j : Nat) :
    ValueEnv N j (valueStep^[j] z) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact valueStep_env N j _ ih

/-- Envelope consequence: at the start of round i<N, u and v are below 2^(N−i); the terminal state u=1, v=0 also fits. -/
theorem valueEnv_width (N i : Nat) (z : ValueState) (h : ValueEnv N i z) (hi : i<N) :
    z.u<2^(N-i) ∧ z.v<2^(N-i) := by
  obtain ⟨hg,hlt⟩ := h
  have hsplit : 2^N=2^(N-i)*2^i := by rw [← pow_add]; congr 1; omega
  have hprod : z.u*z.v<2^(N-i) := by
    rw [hsplit] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt
  have h2 : 2 ≤ 2^(N-i) := by
    calc 2=2^1 := by norm_num
      _ ≤ 2^(N-i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases Nat.eq_zero_or_pos z.v with hv|hv
  · have hu : z.u=1 := by simpa [Nat.Coprime,hv] using hg
    constructor <;> omega
  rcases Nat.eq_zero_or_pos z.u with hu|hu
  · have hv1 : z.v=1 := by simpa [Nat.Coprime,hu] using hg
    constructor <;> omega
  exact ⟨lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hv) hprod,
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hu) hprod⟩

theorem valueIter_le (z : ValueState) (j : Nat) :
    (valueStep^[j] z).u ≤ z.u ∧ (valueStep^[j] z).v ≤ z.v := by
  induction j with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h := valueStep_le (valueStep^[j] z)
    exact ⟨h.1.trans ih.1,h.2.trans ih.2⟩

/-- For coprime p, x with p·x<2^512, u and v fit in `valueWidth w i` bits in each of the first 512 rounds. -/
theorem valueIter_width (p x w j : Nat) (hc : Nat.Coprime p x) (hpx : p*x<2^512)
    (hp : p<2^w) (hx : x<2^w) (hj : j<512) :
    (valueStep^[j] (valueInit p x)).u<2^(valueWidth w j) ∧
    (valueStep^[j] (valueInit p x)).v<2^(valueWidth w j) := by
  have he := valueEnv_width 512 j _ (valueIter_env 512 (valueInit p x)
    ⟨hc,by show p*x*2^0<2^512; rw [pow_zero,Nat.mul_one]; exact hpx⟩ j) hj
  have hl := valueIter_le (valueInit p x) j
  have hmax : 2^(512-j) ≤ 2^(max 2 (512-j)) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  have fit (a : Nat) (ha : a<2^w) (hb : a<2^(512-j)) : a<2^(valueWidth w j) := by
    unfold valueWidth
    rcases le_total w (max 2 (512-j)) with h|h
    · rw [min_eq_left h]; exact ha
    · rw [min_eq_right h]; exact lt_of_lt_of_le hb hmax
  exact ⟨fit _ (lt_of_le_of_lt hl.1 hp) he.1,fit _ (lt_of_le_of_lt hl.2 hx) he.2⟩

end ECDSAAdd
