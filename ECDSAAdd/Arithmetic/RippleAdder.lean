import ECDSAAdd.Arithmetic.FullAdder
import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- 每一位的两根输入线、输出线和进位工作线；列表按小端排列。 -/
structure AddBit where
  x : Wire
  y : Wire
  out : Wire
  carry : Wire

def addWires : List AddBit → List Wire
  | [] => []
  | b :: bs => b.x :: b.y :: b.out :: b.carry :: addWires bs

/-- 正向计算各位，递归返回时按逆序测量清理进位。 -/
def rippleAdder : List AddBit → Wire → Program
  | [], _ => []
  | b :: bs, cin =>
      fullAdder b.x b.y cin b.out b.carry ++ rippleAdder bs b.carry ++
        eraseCarry b.x b.y cin b.carry

theorem mem_addWires {bs : List AddBit} {b : AddBit} (h : b ∈ bs) :
    b.x ∈ addWires bs ∧ b.y ∈ addWires bs ∧
      b.out ∈ addWires bs ∧ b.carry ∈ addWires bs := by
  induction bs with
  | nil => simp at h
  | cons a bs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [addWires]
    · obtain ⟨hx, hy, ho, hc⟩ := ih h
      simp [addWires, hx, hy, ho, hc]

theorem sum_value_step (A B C : Bool) (X Y n : Nat) :
    (sumBit A B C).toNat + 2 * ((X + Y + (carryBit A B C).toNat) % 2^n) =
      ((A.toNat + 2 * X) + (B.toNat + 2 * Y) + C.toNat) % 2^(n+1) := by
  have hv := fullAdder_bit_value A B C
  have hs : (sumBit A B C).toNat < 2 := by cases sumBit A B C <;> decide
  have hn : 0 < 2^n := by positivity
  have hr := Nat.mod_lt (X + Y + (carryBit A B C).toNat) hn
  have he : (A.toNat + 2 * X) + (B.toNat + 2 * Y) + C.toNat =
      (sumBit A B C).toNat + 2 * (X + Y + (carryBit A B C).toNat) := by omega
  rw [he, Nat.pow_succ, Nat.mul_comm (2^n) 2]
  have hsmod : (sumBit A B C).toNat < 2 * 2^n := by omega
  have hsmall : (sumBit A B C).toNat +
      2 * ((X + Y + (carryBit A B C).toNat) % 2^n) < 2 * 2^n := by omega
  conv_rhs => rw [Nat.add_mod, Nat.mul_mod_mul_left,
    Nat.mod_eq_of_lt hsmod, Nat.mod_eq_of_lt hsmall]

/-- 进位工作线初始为零时，向任意输出初值异或写入低 n 位的和，其他线路恢复。 -/
theorem rippleAdder_xor_correct (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) (s : State) (m : List Bool)
    (hclean : ∀ b ∈ bs, s.basis b.carry = false) :
    (run (rippleAdder bs cin) m s).phase = s.phase ∧
    (∀ w, w ∉ bs.map AddBit.out → (run (rippleAdder bs cin) m s).basis w = s.basis w) ∧
    regValue (bs.map AddBit.out) (run (rippleAdder bs cin) m s).basis =
      regValue (bs.map AddBit.out) s.basis ^^^
      ((regValue (bs.map AddBit.x) s.basis + regValue (bs.map AddBit.y) s.basis +
        (s.basis cin).toNat) % 2^bs.length) := by
  induction bs generalizing cin s m with
  | nil => simp [rippleAdder, run, regValue, Nat.mod_one]
  | cons b bs ih =>
    have hn := hnd
    simp only [addWires, List.nodup_cons, List.mem_cons, not_or] at hn
    obtain ⟨⟨hcx, hcy, hco, hck, hcr⟩, ⟨hxy, hxo, hxk, hxr⟩,
      ⟨hyo, hyk, hyr⟩, ⟨hok, hor⟩, hkr, hrest⟩ := hn
    have h5 : [b.x, b.y, cin, b.out, b.carry].Nodup := by
      simp_all [List.nodup_cons, Ne.symm hcx, Ne.symm hcy]
    have hzero := hclean b (by simp)
    let A := s.basis b.x
    let B := s.basis b.y
    let C := s.basis cin
    let s1 : State := ⟨s.phase,
      writeBit (writeBit s.basis b.carry (carryBit A B C)) b.out (s.basis b.out ^^ sumBit A B C)⟩
    have hfirst (record : List Bool) : run (fullAdder b.x b.y cin b.out b.carry) record s = s1 := by
      rw [fullAdder_correct _ _ _ _ _ h5]
      simp [s1, hzero, A, B, C]
    have htail : ∀ w ∈ addWires bs, s1.basis w = s.basis w := by
      intro w hw
      have ho : w ≠ b.out := by intro h; apply hor; simpa [h] using hw
      have hk : w ≠ b.carry := by intro h; apply hkr; simpa [h] using hw
      simp [s1, writeBit, ho, hk]
    have hclean' : ∀ d ∈ bs, s1.basis d.carry = false := by
      intro d hd
      rw [htail _ (mem_addWires hd).2.2.2]
      exact hclean d (by simp [hd])
    let t := run (rippleAdder bs b.carry) m s1
    obtain ⟨hphase, hsame, hsum⟩ := ih b.carry (List.nodup_cons.mpr ⟨hkr, hrest⟩) s1 m hclean'
    have hout_mem : ∀ w ∈ bs.map AddBit.out, w ∈ addWires bs := by
      intro w hw
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
      exact (mem_addWires hd).2.2.1
    have heq : ∀ w, w ∉ addWires bs → t.basis w = s1.basis w := by
      intro w hw
      exact hsame w (fun h => hw (hout_mem w h))
    have htX : t.basis b.x = A := by rw [heq _ hxr]; simp [s1, writeBit, hxo, hxk, A]
    have htY : t.basis b.y = B := by rw [heq _ hyr]; simp [s1, writeBit, hyo, hyk, B]
    have htC : t.basis cin = C := by rw [heq _ hcr]; simp [s1, writeBit, hco, hck, C]
    have htK : t.basis b.carry = carryBit A B C := by
      rw [heq _ hkr]; simp [s1, writeBit, Ne.symm hok]
    have htO : t.basis b.out = (s.basis b.out ^^ sumBit A B C) := by rw [heq _ hor]; simp [s1, writeBit]
    have herase (record : List Bool) : run (eraseCarry b.x b.y cin b.carry) record t =
        ⟨t.phase, writeBit t.basis b.carry false⟩ :=
      eraseCarry_correct _ _ _ _ hxk hyk hck t (by rw [htX, htY, htC, htK]) record
    simp only [rippleAdder, run_append, run_take]
    rw [hfirst]
    simp only [measurementCount_append, fullAdder_measurementCount, zero_add,
      List.drop_zero]
    change (run (eraseCarry b.x b.y cin b.carry) _ t).phase = _ ∧ _
    rw [herase]
    refine ⟨hphase, ?_, ?_⟩
    · intro w hw
      have hw' : w ≠ b.out ∧ w ∉ bs.map AddBit.out := by simpa only [List.map_cons, List.mem_cons, not_or] using hw
      have ht := hsame w hw'.2
      change t.basis w = s1.basis w at ht
      by_cases hk : w = b.carry
      · subst w; simp [writeBit, hzero]
      · simp [writeBit, hk, ht, s1, hw'.1]
    · have hx := regValue_congr (bs.map AddBit.x) s1.basis s.basis (by
        intro w hw
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
        exact htail _ (mem_addWires hd).1)
      have hy := regValue_congr (bs.map AddBit.y) s1.basis s.basis (by
        intro w hw
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
        exact htail _ (mem_addWires hd).2.1)
      have hz := regValue_congr (bs.map AddBit.out) s1.basis s.basis (by
        intro w hw
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
        exact htail _ (mem_addWires hd).2.2.1)
      have ho := regValue_congr (bs.map AddBit.out)
        (writeBit t.basis b.carry false) t.basis (by
          intro w hw
          have h : w ≠ b.carry := by intro he; apply hkr; simpa [he] using hout_mem w hw
          simp [writeBit, h])
      have hc1 : s1.basis b.carry = carryBit A B C := by simp [s1, writeBit, Ne.symm hok]
      change (if (writeBit t.basis b.carry false) b.out then 1 else 0) +
          2 * regValue (bs.map AddBit.out) (writeBit t.basis b.carry false) = _
      rw [ho, hsum, hx, hy, hz, hc1]
      simp only [writeBit, Function.update_of_ne hok, htO, List.map_cons, List.length_cons]
      have hnum := sum_value_step A B C (regValue (bs.map AddBit.x) s.basis)
        (regValue (bs.map AddBit.y) s.basis) bs.length
      have hxor := xor_value_step (s.basis b.out) (sumBit A B C)
        (regValue (bs.map AddBit.out) s.basis)
        ((regValue (bs.map AddBit.x) s.basis + regValue (bs.map AddBit.y) s.basis +
          (carryBit A B C).toNat) % 2^bs.length)
      rw [hnum] at hxor
      simpa only [regValue, List.foldr_cons, Bool.toNat, Bool.cond_eq_ite, A, B, C] using hxor

/-- 零输出的加法是 XOR 接口的特例。 -/
theorem rippleAdder_correct (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) (s : State) (m : List Bool)
    (hclean : ∀ b ∈ bs, s.basis b.out = false ∧ s.basis b.carry = false) :
    (run (rippleAdder bs cin) m s).phase = s.phase ∧
    (∀ w, w ∉ bs.map AddBit.out → (run (rippleAdder bs cin) m s).basis w = s.basis w) ∧
    regValue (bs.map AddBit.out) (run (rippleAdder bs cin) m s).basis =
      (regValue (bs.map AddBit.x) s.basis + regValue (bs.map AddBit.y) s.basis +
        (s.basis cin).toNat) % 2^bs.length := by
  have hz : regValue (bs.map AddBit.out) s.basis = 0 := (regValue_zero _ _).mpr (by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    exact (hclean b hb).1)
  simpa only [hz, Nat.zero_xor] using
    rippleAdder_xor_correct bs cin hnd s m (fun b hb => (hclean b hb).2)


theorem inputs_not_output (bs : List AddBit) (hnd : (addWires bs).Nodup) :
    ∀ b ∈ bs, b.x ∉ bs.map AddBit.out ∧ b.y ∉ bs.map AddBit.out ∧
      b.carry ∉ bs.map AddBit.out := by
  induction bs with
  | nil => simp
  | cons a bs ih =>
    simp only [addWires, List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨hxy, hxo, hxk, hxr⟩, ⟨hyo, hyk, hyr⟩, ⟨hok, hor⟩, hkr, hr⟩ := hnd
    have hn (w : Wire) (h : w ∉ addWires bs) : w ∉ bs.map AddBit.out := by
      intro hw
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
      exact h (mem_addWires hb).2.2.1
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [hn _ hxr, hn _ hyr, hn _ hkr, hxo, hyo, Ne.symm hok]
    · obtain ⟨hx, hy, hk⟩ := ih hr b hb
      obtain ⟨hx', hy', _, hk'⟩ := mem_addWires hb
      have hxo' : b.x ≠ a.out := by intro h; apply hor; simpa [h] using hx'
      have hyo' : b.y ≠ a.out := by intro h; apply hor; simpa [h] using hy'
      have hko' : b.carry ≠ a.out := by intro h; apply hor; simpa [h] using hk'
      simp [hx, hy, hk, hxo', hyo', hko']

/-- n 位 XOR 加法：保持输入和输入进位，向任意输出初值异或低 n 位的和，工作位归零。 -/
theorem rippleAdder_xor_spec (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) (X Y O : Nat) (C : Bool) :
    {{ bs.map AddBit.x = X, bs.map AddBit.y = Y, cin = C,
       bs.map AddBit.out = O, bs.map AddBit.carry = (0 : Nat) }} rippleAdder bs cin
    {{ bs.map AddBit.x = X, bs.map AddBit.y = Y, cin = C,
       bs.map AddBit.out = (O ^^^ ((X + Y + C.toNat) % 2^bs.length)),
       bs.map AddBit.carry = (0 : Nat) }} := by
  intro s m hP
  simp only [Holds.holds] at hP ⊢
  obtain ⟨⟨⟨⟨hx, hy⟩, hc⟩, ho⟩, hk⟩ := hP
  have hclean : ∀ b ∈ bs, s.basis b.carry = false := by
    intro b hb
    exact (regValue_zero _ _).mp hk _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  obtain ⟨hp, hsame, hsum⟩ := rippleAdder_xor_correct bs cin hnd s m hclean
  have hn := inputs_not_output bs (List.nodup_cons.mp hnd).2
  have hr (f : AddBit → Wire) (h : ∀ b ∈ bs, f b ∉ bs.map AddBit.out) :
      regValue (bs.map f) (run (rippleAdder bs cin) m s).basis = regValue (bs.map f) s.basis :=
    regValue_congr _ _ _ (by
      intro w hw
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
      exact hsame _ (h b hb))
  have hx' := hr AddBit.x (fun b hb => (hn b hb).1)
  have hy' := hr AddBit.y (fun b hb => (hn b hb).2.1)
  have hk' := hr AddBit.carry (fun b hb => (hn b hb).2.2)
  have hc' : (run (rippleAdder bs cin) m s).basis cin = s.basis cin := by
    apply hsame
    intro h
    obtain ⟨b, hb, he⟩ := List.mem_map.mp h
    exact (List.nodup_cons.mp hnd).1 (he ▸ (mem_addWires hb).2.2.1)
  exact ⟨hp, ⟨⟨⟨hx'.trans hx, hy'.trans hy⟩, hc'.trans hc⟩,
    by simpa only [hx, hy, hc, ho] using hsum⟩, hk'.trans hk⟩

/-- 输出初始为零时，XOR 写入就是普通加法。 -/
theorem rippleAdder_spec (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) (X Y : Nat) (C : Bool) :
    {{ bs.map AddBit.x = X, bs.map AddBit.y = Y, cin = C,
       bs.map AddBit.out = (0 : Nat), bs.map AddBit.carry = (0 : Nat) }} rippleAdder bs cin
    {{ bs.map AddBit.x = X, bs.map AddBit.y = Y, cin = C,
       bs.map AddBit.out = ((X + Y + C.toNat) % 2^bs.length),
       bs.map AddBit.carry = (0 : Nat) }} := by
  simpa only [Nat.zero_xor] using rippleAdder_xor_spec bs cin hnd X Y 0 C

/-- 加一个高位后，n 位输入的和完整保留在 n+1 位输出中。
高位是输出的一部分；只清理进位工作线，不清理最高输出位。 -/
theorem rippleAdder_wide_spec (bs : List AddBit) (high : AddBit) (cin : Wire)
    (hnd : (cin :: addWires (bs ++ [high])).Nodup) (X Y : Nat) (C : Bool)
    (hX : X < 2^bs.length) (hY : Y < 2^bs.length) :
    {{ (bs ++ [high]).map AddBit.x = X, (bs ++ [high]).map AddBit.y = Y, cin = C,
       (bs ++ [high]).map AddBit.out = (0 : Nat),
       (bs ++ [high]).map AddBit.carry = (0 : Nat) }} rippleAdder (bs ++ [high]) cin
    {{ (bs ++ [high]).map AddBit.x = X, (bs ++ [high]).map AddBit.y = Y, cin = C,
       (bs ++ [high]).map AddBit.out = (X + Y + C.toNat),
       (bs ++ [high]).map AddBit.carry = (0 : Nat) }} := by
  have hbound : X + Y + C.toNat < 2^(bs ++ [high]).length := by
    have hc := C.toNat_le
    simp only [List.length_append, List.length_singleton, Nat.pow_succ]
    omega
  simpa only [Nat.mod_eq_of_lt hbound] using rippleAdder_spec (bs ++ [high]) cin hnd X Y C

/-- 每位一次 Toffoli，进位清理不增加 Toffoli。 -/
theorem rippleAdder_toffoliCount (bs : List AddBit) (cin : Wire) :
    toffoliCount (rippleAdder bs cin) = bs.length := by
  induction bs generalizing cin with
  | nil => rfl
  | cons b bs ih =>
    simp [rippleAdder, toffoliCount_append, fullAdder_toffoliCount,
      eraseCarry, toffoliCount, ih, Nat.add_comm]

/-- 每位一次测量，记录消费数与输入值无关。 -/
theorem rippleAdder_measurementCount (bs : List AddBit) (cin : Wire) :
    measurementCount (rippleAdder bs cin) = bs.length := by
  induction bs generalizing cin with
  | nil => rfl
  | cons b bs ih =>
    simp [rippleAdder, measurementCount_append, fullAdder_measurementCount,
      eraseCarry, measurementCount, ih]

theorem addWires_length (bs : List AddBit) : (addWires bs).length = 4 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [addWires, ih]; omega

/-- 非空进位链恰好访问输入进位线和每位的四根线路。 -/
theorem rippleAdder_wires (b : AddBit) (bs : List AddBit) (cin : Wire) :
    wires (rippleAdder (b :: bs) cin) = (cin :: addWires (b :: bs)).toFinset := by
  induction bs generalizing b cin with
  | nil =>
    ext w
    simp [rippleAdder, wires_append, fullAdder_wires, eraseCarry_wires, addWires]
    tauto
  | cons d ds ih =>
    rw [rippleAdder, wires_append, wires_append, fullAdder_wires, ih, eraseCarry_wires]
    ext w
    simp [addWires]
    tauto

/-- n 位非空加法使用 4n+1 根静态线路；空程序不访问线路。 -/
theorem rippleAdder_qubitCount (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) :
    qubitCount (rippleAdder bs cin) = if bs.isEmpty then 0 else 4 * bs.length + 1 := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    rw [qubitCount, rippleAdder_wires, List.toFinset_card_of_nodup hnd]
    simp [addWires_length]

end ECDSAAdd.Arithmetic
