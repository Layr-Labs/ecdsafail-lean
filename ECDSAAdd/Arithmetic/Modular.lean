import ECDSAAdd.Arithmetic.ModularSteps

namespace ECDSAAdd.Arithmetic

/-- 保留输入的模加 XOR：载入 q，计算和与候选差，选择后按前向 XOR 清理。 -/
def modAdd (L : ModLayout) (q : Nat) : Program :=
  let load := xorConstant (L.reg .modulus) q
  let sum := add (L.adder .x .y .total .carrySum L.cinSum)
  let difference := sub (L.adder .total .modulus .diff .carryDiff L.cinDiff)
  load ++ sum ++ difference ++ selectXor L.selector L.high.diff ++ difference ++ sum ++ load

/-- 保留输入的模减 XOR：借位时选择加回 q 的候选，随后清理全部工作寄存器。 -/
def modSub (L : ModLayout) (q : Nat) : Program :=
  let load := xorConstant (L.reg .modulus) q
  let difference := sub (L.adder .x .y .diff .carryDiff L.cinDiff)
  let correction := add (L.adder .diff .modulus .total .carrySum L.cinSum)
  load ++ difference ++ correction ++ selectXor L.selector L.high.diff ++ correction ++ difference ++ load

def ModValues.clean (X Y O : Nat) : ModField → Nat
  | .x => X | .y => Y | .out => O | _ => 0

theorem ModValues.clean_iff (L : ModLayout) (X Y O : Nat) (st : BasisState) :
    ModValues L (ModValues.clean X Y O) st ↔
      (((regValue L.x st = X ∧ regValue L.y st = Y) ∧ regValue L.out st = O) ∧
        regValue L.work st = 0) := by
  constructor
  · intro hv
    refine ⟨⟨⟨hv.1 .x, hv.1 .y⟩, hv.1 .out⟩, (regValue_zero _ _).mpr ?_⟩
    intro w hw
    simp only [ModLayout.work, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with ((((ht | hm) | hd) | hcs) | hcd) | hci | hci
    · exact (regValue_zero _ _).mp (hv.1 .total) w ht
    · exact (regValue_zero _ _).mp (hv.1 .modulus) w hm
    · exact (regValue_zero _ _).mp (hv.1 .diff) w hd
    · exact (regValue_zero _ _).mp (hv.1 .carrySum) w hcs
    · exact (regValue_zero _ _).mp (hv.1 .carryDiff) w hcd
    · subst w; exact hv.2.1
    · subst w; exact hv.2.2
  · rintro ⟨⟨⟨hx, hy⟩, ho⟩, hw⟩
    have hz := (regValue_zero _ _).mp hw
    refine ⟨?_, hz L.cinSum (by simp [ModLayout.work]), hz L.cinDiff (by simp [ModLayout.work])⟩
    intro f
    cases f
    · exact hx
    · exact hy
    · apply (regValue_zero _ _).mpr; intro w hw; exact hz w (by simp [ModLayout.work, hw])
    · apply (regValue_zero _ _).mpr; intro w hw; exact hz w (by simp [ModLayout.work, hw])
    · apply (regValue_zero _ _).mpr; intro w hw; exact hz w (by simp [ModLayout.work, hw])
    · exact ho
    · apply (regValue_zero _ _).mpr; intro w hw; exact hz w (by simp [ModLayout.work, hw])
    · apply (regValue_zero _ _).mpr; intro w hw; exact hz w (by simp [ModLayout.work, hw])

private theorem modAdd_bounded_values (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (X Y O : Nat) (hXY : X + Y < 2*q) :
    Triple (ModValues L (ModValues.clean X Y O)) (modAdd L q)
      (ModValues L (ModValues.clean X Y (O ^^^ ((X+Y)%q)))) := by
  let S := X+Y
  let D := (S + 2^(L.width+1) - q) % 2^(L.width+1)
  let R := S%q
  have hS : X+Y < 2^(L.width+1) := by rw [Nat.pow_succ]; omega
  have hq' : q < 2^(L.width+1) := by rw [Nat.pow_succ]; omega
  have hchoose : (if 2^L.width ≤ D then S else D) = R :=
    (addReduction S q L.width hq0 hq (by dsimp [S]; omega)).2
  let v0 := ModValues.clean X Y O
  let v1 := Function.update v0 .modulus q
  let v2 := Function.update v1 .total S
  let v3 := Function.update v2 .diff D
  let v4 := Function.update v3 .out (O ^^^ R)
  let v5 := Function.update v4 .diff 0
  let v6 := Function.update v5 .total 0
  let v7 := Function.update v6 .modulus 0
  have h0 : Triple (ModValues L v0) (xorConstant (L.reg .modulus) q) (ModValues L v1) := by
    simpa [v1, v0, ModValues.clean] using constant_modValues L hnd v0 .modulus q hq'
  have h1 : Triple (ModValues L v1) (add (L.adder .x .y .total .carrySum L.cinSum)) (ModValues L v2) := by
    simpa [v2, v1, v0, ModValues.clean, S, Nat.mod_eq_of_lt hS] using
      add_modValues L hnd v1 .x .y .total .carrySum (by decide) L.cinSum (Or.inl rfl)
        (by simp [v1, v0, ModValues.clean])
  have h2 : Triple (ModValues L v2) (sub (L.adder .total .modulus .diff .carryDiff L.cinDiff)) (ModValues L v3) := by
    simpa [v3, v2, v1, v0, ModValues.clean, D] using
      sub_modValues L hnd v2 .total .modulus .diff .carryDiff (by decide) L.cinDiff (Or.inr rfl)
        (by simp [v2, v1, v0, ModValues.clean])
  have h3 : Triple (ModValues L v3) (selectXor L.selector L.high.diff) (ModValues L v4) := by
    simpa [v4, v3, v2, v1, v0, ModValues.clean, hchoose] using select_modValues L hnd v3 (by
      simpa [v3, v2, v1, v0, ModValues.clean, hchoose] using
        (lt_trans (Nat.mod_lt _ hq0) hq : R < 2^L.width))
  have h4 : Triple (ModValues L v4) (sub (L.adder .total .modulus .diff .carryDiff L.cinDiff)) (ModValues L v5) := by
    simpa [v5, v4, v3, v2, v1, v0, ModValues.clean, D] using
      sub_modValues L hnd v4 .total .modulus .diff .carryDiff (by decide) L.cinDiff (Or.inr rfl)
        (by simp [v4, v3, v2, v1, v0, ModValues.clean])
  have h5 : Triple (ModValues L v5) (add (L.adder .x .y .total .carrySum L.cinSum)) (ModValues L v6) := by
    simpa [v6, v5, v4, v3, v2, v1, v0, ModValues.clean, S, Nat.mod_eq_of_lt hS] using
      add_modValues L hnd v5 .x .y .total .carrySum (by decide) L.cinSum (Or.inl rfl)
        (by simp [v5, v4, v3, v2, v1, v0, ModValues.clean])
  have h6 : Triple (ModValues L v6) (xorConstant (L.reg .modulus) q) (ModValues L v7) := by
    simpa [v7, v6, v5, v4, v3, v2, v1, v0, ModValues.clean] using constant_modValues L hnd v6 .modulus q hq'
  have hv7 : v7 = ModValues.clean X Y (O ^^^ R) := by
    funext f; cases f <;> simp [v7, v6, v5, v4, v3, v2, v1, v0, ModValues.clean]
  have h := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))))
  simpa only [modAdd, List.append_assoc, hv7, v0, R, S] using h

/-- 模 q 加法：任意初值输出按位 XOR 更新，输入、相位和全部工作线恢复。
q 是编译期常量，X、Y 是寄存器中的变量；额外高位只属于实现布局。 -/
theorem modAdd_bounded_spec (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (X Y O : Nat) (hXY : X + Y < 2*q) :
    {{ L.x = X, L.y = Y, L.out = O, L.work = 0 }} modAdd L q
    {{ L.x = X, L.y = Y, L.out = (O ^^^ ((X+Y)%q)), L.work = 0 }} :=
  Triple.conseq (fun st h => (ModValues.clean_iff L X Y O st).mpr h)
    (modAdd_bounded_values L hnd q hq0 hq X Y O hXY)
    (fun st h => (ModValues.clean_iff L X Y (O ^^^ ((X+Y)%q)) st).mp h)

theorem modAdd_spec (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (X Y O : Nat) (hX : X < q) (hY : Y < q) :
    {{ L.x = X, L.y = Y, L.out = O, L.work = 0 }} modAdd L q
    {{ L.x = X, L.y = Y, L.out = (O ^^^ ((X+Y)%q)), L.work = 0 }} :=
  modAdd_bounded_spec L hnd q hq0 hq X Y O (by omega)

private theorem modSub_values (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (X Y O : Nat) (hX : X < q) (hY : Y < q) :
    Triple (ModValues L (ModValues.clean X Y O)) (modSub L q)
      (ModValues L (ModValues.clean X Y (O ^^^ ((X+q-Y)%q)))) := by
  let D := (X + 2^(L.width+1) - Y) % 2^(L.width+1)
  let S := (D+q) % 2^(L.width+1)
  let R := (X+q-Y)%q
  have hq' : q < 2^(L.width+1) := by rw [Nat.pow_succ]; omega
  have hchoose : (if 2^L.width ≤ D then S else D) = R :=
    (subReduction X Y q L.width hq0 hq hX hY).2
  let v0 := ModValues.clean X Y O
  let v1 := Function.update v0 .modulus q
  let v2 := Function.update v1 .diff D
  let v3 := Function.update v2 .total S
  let v4 := Function.update v3 .out (O ^^^ R)
  let v5 := Function.update v4 .total 0
  let v6 := Function.update v5 .diff 0
  let v7 := Function.update v6 .modulus 0
  have h0 : Triple (ModValues L v0) (xorConstant (L.reg .modulus) q) (ModValues L v1) := by
    simpa [v1, v0, ModValues.clean] using constant_modValues L hnd v0 .modulus q hq'
  have h1 : Triple (ModValues L v1) (sub (L.adder .x .y .diff .carryDiff L.cinDiff)) (ModValues L v2) := by
    simpa [v2, v1, v0, ModValues.clean, D] using
      sub_modValues L hnd v1 .x .y .diff .carryDiff (by decide) L.cinDiff (Or.inr rfl)
        (by simp [v1, v0, ModValues.clean])
  have h2 : Triple (ModValues L v2) (add (L.adder .diff .modulus .total .carrySum L.cinSum)) (ModValues L v3) := by
    simpa [v3, v2, v1, v0, ModValues.clean, S] using
      add_modValues L hnd v2 .diff .modulus .total .carrySum (by decide) L.cinSum (Or.inl rfl)
        (by simp [v2, v1, v0, ModValues.clean])
  have h3 : Triple (ModValues L v3) (selectXor L.selector L.high.diff) (ModValues L v4) := by
    simpa [v4, v3, v2, v1, v0, ModValues.clean, hchoose] using select_modValues L hnd v3 (by
      simpa [v3, v2, v1, v0, ModValues.clean, hchoose] using
        (lt_trans (Nat.mod_lt _ hq0) hq : R < 2^L.width))
  have h4 : Triple (ModValues L v4) (add (L.adder .diff .modulus .total .carrySum L.cinSum)) (ModValues L v5) := by
    simpa [v5, v4, v3, v2, v1, v0, ModValues.clean, S] using
      add_modValues L hnd v4 .diff .modulus .total .carrySum (by decide) L.cinSum (Or.inl rfl)
        (by simp [v4, v3, v2, v1, v0, ModValues.clean])
  have h5 : Triple (ModValues L v5) (sub (L.adder .x .y .diff .carryDiff L.cinDiff)) (ModValues L v6) := by
    simpa [v6, v5, v4, v3, v2, v1, v0, ModValues.clean, D] using
      sub_modValues L hnd v5 .x .y .diff .carryDiff (by decide) L.cinDiff (Or.inr rfl)
        (by simp [v5, v4, v3, v2, v1, v0, ModValues.clean])
  have h6 : Triple (ModValues L v6) (xorConstant (L.reg .modulus) q) (ModValues L v7) := by
    simpa [v7, v6, v5, v4, v3, v2, v1, v0, ModValues.clean] using constant_modValues L hnd v6 .modulus q hq'
  have hv7 : v7 = ModValues.clean X Y (O ^^^ R) := by
    funext f; cases f <;> simp [v7, v6, v5, v4, v3, v2, v1, v0, ModValues.clean]
  have h := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))))
  simpa only [modSub, List.append_assoc, hv7, v0, R] using h

/-- 模 q 减法：任意初值输出按位 XOR 更新，借位选择线随候选差一起清理。 -/
theorem modSub_spec (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (X Y O : Nat) (hX : X < q) (hY : Y < q) :
    {{ L.x = X, L.y = Y, L.out = O, L.work = 0 }} modSub L q
    {{ L.x = X, L.y = Y, L.out = (O ^^^ ((X+q-Y)%q)), L.work = 0 }} :=
  Triple.conseq (fun st h => (ModValues.clean_iff L X Y O st).mpr h)
    (modSub_values L hnd q hq0 hq X Y O hX hY)
    (fun st h => (ModValues.clean_iff L X Y (O ^^^ ((X+q-Y)%q)) st).mp h)

end ECDSAAdd.Arithmetic
