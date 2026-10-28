import ECDSAAdd.Arithmetic.Layout

/-!
10 位计数原语复用 AdderLayout。常用接口 counterInc_spec / counterDec_spec 从
`{{ x=K, y=0, cin=C, out=0, carry=0 }}` 出发，清空 x 并把结果写入 out。
结果分别为 (K+C) mod 1024 和 (K+1024−C) mod 1024；即使 C=false 也交换角色。
下层 XOR 接口保留来源，用于第二次前向调用清除旧值；不反转测量程序。
-/

namespace ECDSAAdd.Arithmetic

private theorem counter_perm (L : AdderLayout) :
    ((L.cin::L.y) ++ (L.x ++ L.out ++ L.carry)).Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  rcases L with ⟨bs, cin⟩
  induction bs with
  | nil => simp [AdderLayout.y, AdderLayout.x, AdderLayout.out, AdderLayout.carry, AdderLayout.wires, addWires]
  | cons b bs ih =>
    simp [AdderLayout.y, AdderLayout.x, AdderLayout.out, AdderLayout.carry,
      AdderLayout.wires, addWires, List.count_cons] at ih ⊢
    omega

private def counterFlip (L : AdderLayout) : Program := notRegister (L.cin::L.y)

private theorem counterFlip_spec (L : AdderLayout) (hnd : L.wires.Nodup)
    (K Y O : Nat) (C : Bool) :
    {{ L.x=K, L.y=Y, L.cin=C, L.out=O, L.carry=0 }} counterFlip L
    {{ L.x=K, L.y=(2^L.width-1-Y), L.cin=(!C), L.out=O, L.carry=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨⟨⟨⟨hx, hy⟩, hc⟩, ho⟩, hcarry⟩ := h
  have hn := List.nodup_append'.mp ((counter_perm L).nodup_iff.mpr hnd)
  rw [counterFlip, notRegister_correct _ hn.1]
  have keep (r : List Wire) (hr : r ⊆ L.x ++ L.out ++ L.carry) :
      regValue r (fun w => if w ∈ L.cin::L.y then !s.basis w else s.basis w) = regValue r s.basis :=
    regValue_congr _ _ _ (by
      intro w hw
      simp [List.disjoint_right.mp hn.2.2 (hr hw)])
  refine ⟨rfl, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (keep L.x (by intro w hw; simp [hw])).trans hx
  · change regValue L.y (fun w => if w ∈ L.cin::L.y then !s.basis w else s.basis w) = _
    rw [regValue_congr L.y _ (fun w => !s.basis w) (by intro w hw; simp [hw]), regValue_complement, hy]
    simp [AdderLayout.y, AdderLayout.width]
  · simp [hc]
  · exact (keep L.out (by intro w hw; simp [hw])).trans ho
  · exact (keep L.carry (by intro w hw; simp [hw])).trans hcarry

/-- 10 位计数器的 XOR 写出；cin 是活动控制位，y 和 carry 是零工作寄存器。 -/
def counterIncXor (L : AdderLayout) : Program := add L

/-- 用补码加法写出 K−C，恢复用于控制的 cin 和全一辅助寄存器。 -/
def counterDecXor (L : AdderLayout) : Program := counterFlip L ++ add L ++ counterFlip L

theorem counterIncXor_spec (L : AdderLayout) (hnd : L.wires.Nodup) (hw : L.width=10)
    (K O : Nat) (C : Bool) :
    {{ L.x=K, L.y=0, L.cin=C, L.out=O, L.carry=0 }} counterIncXor L
    {{ L.x=K, L.y=0, L.cin=C, L.out=(O ^^^ ((K+C.toNat)%1024)), L.carry=0 }} := by
  simpa only [counterIncXor, hw, Nat.add_zero] using add_spec L hnd K 0 O C

theorem counterDecXor_spec (L : AdderLayout) (hnd : L.wires.Nodup) (hw : L.width=10)
    (K O : Nat) (C : Bool) :
    {{ L.x=K, L.y=0, L.cin=C, L.out=O, L.carry=0 }} counterDecXor L
    {{ L.x=K, L.y=0, L.cin=C, L.out=(O ^^^ ((K+1024-C.toNat)%1024)), L.carry=0 }} := by
  have h1 := counterFlip_spec L hnd K 0 O C
  have h2 := add_spec L hnd K (2^L.width-1) O (!C)
  have h3 := counterFlip_spec L hnd K (2^L.width-1)
    (O ^^^ ((K+(2^L.width-1)+(!C).toNat)%2^L.width)) (!C)
  simp only [Nat.sub_zero] at h1
  simp only [Nat.sub_self, Bool.not_not] at h3
  have h := h1.seq (h2.seq h3)
  have he : K+(2^L.width-1)+(!C).toNat = K+1024-C.toNat := by
    rw [hw]; cases C <;> simp [Bool.toNat]
  rw [he] at h
  simpa only [counterDecXor, List.append_assoc, hw] using h

private theorem counter_wires (L : AdderLayout) (hw : L.width=10) :
    wires (counterIncXor L) = L.wires.toFinset ∧ wires (counterDecXor L) = L.wires.toFinset := by
  have ha : wires (add L) = L.wires.toFinset := by
    cases L with
    | mk bs cin =>
      cases bs with
      | nil => simp [AdderLayout.width] at hw
      | cons b bs => exact rippleAdder_wires b bs cin
  have hs : (L.cin::L.y).toFinset ⊆ L.wires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr ((counter_perm L).mem_iff.mp (List.mem_append_left _ (List.mem_toFinset.mp hw)))
  refine ⟨ha, ?_⟩
  rw [counterDecXor, wires_append, wires_append, counterFlip, notRegister_wires, ha]
  rw [Finset.union_eq_right.mpr hs, Finset.union_eq_left.mpr hs]

theorem counterXor_resources (L : AdderLayout) (hnd : L.wires.Nodup) (hw : L.width=10) :
    toffoliCount (counterIncXor L) = 10 ∧ measurementCount (counterIncXor L) = 10 ∧
    qubitCount (counterIncXor L) = 41 ∧
    toffoliCount (counterDecXor L) = 10 ∧ measurementCount (counterDecXor L) = 10 ∧
    qubitCount (counterDecXor L) = 41 := by
  have ha := add_resources L hnd
  have hf := notRegister_counts (L.cin::L.y)
  have hlen : L.wires.length = 41 := by
    simp only [AdderLayout.wires, List.length_cons, addWires_length]
    change 4*L.width+1=41
    rw [hw]
  have hi : qubitCount (counterIncXor L) = 41 := by
    rw [qubitCount, (counter_wires L hw).1, List.toFinset_card_of_nodup hnd, hlen]
  have hd : qubitCount (counterDecXor L) = 41 := by
    rw [qubitCount, (counter_wires L hw).2, List.toFinset_card_of_nodup hnd, hlen]
  refine ⟨by simpa only [hw] using ha.1, by simpa only [hw] using ha.2.1, hi, ?_, ?_, hd⟩
  · simp only [counterDecXor, toffoliCount_append, counterFlip, hf.1, ha.1, hw]
  · simp only [counterDecXor, measurementCount_append, counterFlip, hf.2, ha.2.1, hw]

def AdderLayout.swapCounter (L : AdderLayout) : AdderLayout :=
  { L with bits := L.bits.map (fun b => { b with x := b.out, out := b.x }) }

theorem AdderLayout.swapCounter_fields (L : AdderLayout) :
    L.swapCounter.x = L.out ∧ L.swapCounter.out = L.x ∧ L.swapCounter.y = L.y ∧
    L.swapCounter.carry = L.carry ∧ L.swapCounter.cin = L.cin ∧ L.swapCounter.width = L.width := by
  simp [AdderLayout.swapCounter, AdderLayout.x, AdderLayout.y, AdderLayout.out,
    AdderLayout.carry, AdderLayout.width, List.map_map, Function.comp_def]

theorem AdderLayout.swapCounter_perm (L : AdderLayout) : L.swapCounter.wires.Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  rcases L with ⟨bs, cin⟩
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp [AdderLayout.swapCounter, AdderLayout.wires, addWires, List.count_cons] at ih ⊢
    omega

/-- 把受控增量后的值移入空计数寄存器，并以前向减法清空旧寄存器。 -/
def counterInc (L : AdderLayout) : Program := counterIncXor L ++ counterDecXor L.swapCounter

/-- 受控减量后同样清空旧计数寄存器，供下轮交换角色复用。 -/
def counterDec (L : AdderLayout) : Program := counterDecXor L ++ counterIncXor L.swapCounter

theorem counterInc_spec (L : AdderLayout) (hnd : L.wires.Nodup) (hw : L.width=10)
    (K : Nat) (C : Bool) :
    {{ L.x=K, L.y=0, L.cin=C, L.out=0, L.carry=0 }} counterInc L
    {{ L.x=0, L.y=0, L.cin=C, L.out=((K+C.toNat)%1024), L.carry=0 }} := by
  intro s m h
  have hx : regValue L.x s.basis = K := h.1.1.1.1
  have hk : K<1024 := by
    have hh := regValue_lt L.x s.basis
    rw [hx] at hh
    simpa only [AdderLayout.x, List.length_map, show L.bits.length=10 from hw] using hh
  have hc : (((K+C.toNat)%1024)+1024-C.toNat)%1024=K := by
    cases C <;> simp [Bool.toNat] <;> omega
  obtain ⟨sx, so, sy, sc, si, sw⟩ := AdderLayout.swapCounter_fields L
  have h1 := counterIncXor_spec L hnd hw K 0 C
  have h2 := counterDecXor_spec L.swapCounter ((AdderLayout.swapCounter_perm L).nodup_iff.mpr hnd)
    (sw.trans hw) ((K+C.toNat)%1024) K C
  simp only [Nat.zero_xor] at h1
  simp only [sx, so, sy, sc, si, hc, Nat.xor_self] at h2
  have h2' :
      {{ L.x=K, L.y=0, L.cin=C, L.out=((K+C.toNat)%1024), L.carry=0 }}
      counterDecXor L.swapCounter
      {{ L.x=0, L.y=0, L.cin=C, L.out=((K+C.toNat)%1024), L.carry=0 }} := Triple.conseq
    (fun st h => ⟨⟨⟨⟨h.1.2, h.1.1.1.2⟩, h.1.1.2⟩, h.1.1.1.1⟩, h.2⟩) h2
    (fun st h => ⟨⟨⟨⟨h.1.2, h.1.1.1.2⟩, h.1.1.2⟩, h.1.1.1.1⟩, h.2⟩)
  exact h1.seq h2' s m h

theorem counterDec_spec (L : AdderLayout) (hnd : L.wires.Nodup) (hw : L.width=10)
    (K : Nat) (C : Bool) :
    {{ L.x=K, L.y=0, L.cin=C, L.out=0, L.carry=0 }} counterDec L
    {{ L.x=0, L.y=0, L.cin=C, L.out=((K+1024-C.toNat)%1024), L.carry=0 }} := by
  intro s m h
  have hx : regValue L.x s.basis = K := h.1.1.1.1
  have hk : K<1024 := by
    have hh := regValue_lt L.x s.basis
    rw [hx] at hh
    simpa only [AdderLayout.x, List.length_map, show L.bits.length=10 from hw] using hh
  have hc : (((K+1024-C.toNat)%1024)+C.toNat)%1024=K := by
    cases C <;> simp [Bool.toNat] <;> omega
  obtain ⟨sx, so, sy, sc, si, sw⟩ := AdderLayout.swapCounter_fields L
  have h1 := counterDecXor_spec L hnd hw K 0 C
  have h2 := counterIncXor_spec L.swapCounter ((AdderLayout.swapCounter_perm L).nodup_iff.mpr hnd)
    (sw.trans hw) ((K+1024-C.toNat)%1024) K C
  simp only [Nat.zero_xor] at h1
  simp only [sx, so, sy, sc, si, hc, Nat.xor_self] at h2
  have h2' :
      {{ L.x=K, L.y=0, L.cin=C, L.out=((K+1024-C.toNat)%1024), L.carry=0 }}
      counterIncXor L.swapCounter
      {{ L.x=0, L.y=0, L.cin=C, L.out=((K+1024-C.toNat)%1024), L.carry=0 }} := Triple.conseq
    (fun st h => ⟨⟨⟨⟨h.1.2, h.1.1.1.2⟩, h.1.1.2⟩, h.1.1.1.1⟩, h.2⟩) h2
    (fun st h => ⟨⟨⟨⟨h.1.2, h.1.1.1.2⟩, h.1.1.2⟩, h.1.1.1.1⟩, h.2⟩)
  exact h1.seq h2' s m h

theorem counter_resources (L : AdderLayout) (hnd : L.wires.Nodup) (hw : L.width=10) :
    toffoliCount (counterInc L) = 20 ∧ measurementCount (counterInc L) = 20 ∧
    qubitCount (counterInc L) = 41 ∧
    toffoliCount (counterDec L) = 20 ∧ measurementCount (counterDec L) = 20 ∧
    qubitCount (counterDec L) = 41 := by
  have h := counterXor_resources L hnd hw
  have hs := counterXor_resources L.swapCounter ((AdderLayout.swapCounter_perm L).nodup_iff.mpr hnd)
    ((AdderLayout.swapCounter_fields L).2.2.2.2.2.trans hw)
  have hwires : L.swapCounter.wires.toFinset = L.wires.toFinset := by
    ext w
    simpa only [List.mem_toFinset] using (AdderLayout.swapCounter_perm L).mem_iff
  have hc := counter_wires L hw
  have hcs := counter_wires L.swapCounter ((AdderLayout.swapCounter_fields L).2.2.2.2.2.trans hw)
  have hi : qubitCount (counterInc L) = 41 := by
    rw [qubitCount, counterInc, wires_append, hc.1, hcs.2, hwires, Finset.union_self]
    simpa only [qubitCount, hc.1] using h.2.2.1
  have hd : qubitCount (counterDec L) = 41 := by
    rw [qubitCount, counterDec, wires_append, hc.2, hcs.1, hwires, Finset.union_self]
    simpa only [qubitCount, hc.1] using h.2.2.1
  exact ⟨by simp only [counterInc, toffoliCount_append, h.1, hs.2.2.2.1],
    by simp only [counterInc, measurementCount_append, h.2.1, hs.2.2.2.2.1], hi,
    by simp only [counterDec, toffoliCount_append, h.2.2.2.1, hs.1],
    by simp only [counterDec, measurementCount_append, h.2.2.2.2.1, hs.2.1], hd⟩

/-- 移动计数器仍只使用同一布局的线路。 -/
theorem counterMove_wires (L : AdderLayout) (hw : L.width=10) :
    wires (counterInc L)=L.wires.toFinset ∧ wires (counterDec L)=L.wires.toFinset := by
  have hc := counter_wires L hw
  have hs := counter_wires L.swapCounter ((AdderLayout.swapCounter_fields L).2.2.2.2.2.trans hw)
  have he : L.swapCounter.wires.toFinset=L.wires.toFinset := by
    ext w
    simpa only [List.mem_toFinset] using (AdderLayout.swapCounter_perm L).mem_iff
  simp only [counterInc,counterDec,wires_append,hc.1,hc.2,hs.1,hs.2,he,Finset.union_self,and_self]

end ECDSAAdd.Arithmetic
