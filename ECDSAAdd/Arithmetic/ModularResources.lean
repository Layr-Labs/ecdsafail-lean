import ECDSAAdd.Arithmetic.Modular

namespace ECDSAAdd.Arithmetic

theorem modAdder_mem (L : ModLayout) (a b t c : ModField) (cin w : Wire) :
    w ∈ wires (add (L.adder a b t c cin)) ↔
      w = cin ∨ w ∈ L.reg a ∨ w ∈ L.reg b ∨ w ∈ L.reg t ∨ w ∈ L.reg c := by
  have hn : (L.adder a b t c cin).bits ≠ [] := by
    simp [ModLayout.adder, ModLayout.bits]
  unfold add
  cases hb : (L.adder a b t c cin).bits with
  | nil => exact False.elim (hn hb)
  | cons bit bs =>
    rw [rippleAdder_wires, ← hb]
    simp [ModLayout.adder, addWires_map, ModLayout.reg, List.mem_flatMap,
      List.mem_map, exists_or, and_or_left, eq_comm]

private theorem sub_mem (L : ModLayout) (a b t c : ModField) (cin w : Wire) :
    w ∈ wires (sub (L.adder a b t c cin)) ↔
      w = cin ∨ w ∈ L.reg a ∨ w ∈ L.reg b ∨ w ∈ L.reg t ∨ w ∈ L.reg c := by
  rw [sub, rippleSubtractor_wires]
  simp [ModLayout.adder, addWires_map, ModLayout.reg, List.mem_flatMap,
    List.mem_map, exists_or, and_or_left, eq_comm]

/-- 实际支持集不含永远不触碰的输出高位。 -/
def ModLayout.activeWires (L : ModLayout) : List Wire :=
  L.cinSum :: L.cinDiff :: (L.low.flatMap ModBit.all ++
    [L.high.x, L.high.y, L.high.total, L.high.modulus, L.high.diff, L.high.carrySum, L.high.carryDiff])

private theorem select_mem (L : ModLayout) (w : Wire) :
    w ∈ wires (selectXor L.selector L.high.diff) ↔
      (L.low ≠ [] ∧ w = L.high.diff) ∨
      w ∈ L.lowReg .diff ∨ w ∈ L.lowReg .total ∨ w ∈ L.lowReg .out := by
  cases hb : L.low with
  | nil => simp [ModLayout.selector, ModLayout.lowReg, hb, selectXor, wires]
  | cons b bs =>
    simp only [ModLayout.selector, hb, List.map_cons, selectXor_wires]
    simp [selectWires_map, ModLayout.lowReg, hb, selectWires,
      ModBit.get, List.mem_flatMap, List.mem_map, exists_or, and_or_left, eq_comm]
    simp only [or_assoc, or_left_comm]

private theorem layout_mem (L : ModLayout) (w : Wire) :
    w ∈ L.activeWires ↔ w = L.cinSum ∨ w = L.cinDiff ∨
      w ∈ L.reg .x ∨ w ∈ L.reg .y ∨ w ∈ L.reg .total ∨ w ∈ L.reg .modulus ∨
      w ∈ L.reg .diff ∨ w ∈ L.lowReg .out ∨ w ∈ L.reg .carrySum ∨ w ∈ L.reg .carryDiff := by
  simp [ModLayout.activeWires, ModLayout.reg, ModLayout.lowReg, ModLayout.bits, ModBit.all, ModBit.get,
    List.mem_flatMap, List.mem_map, exists_or, and_or_left, eq_comm]
  simp only [or_assoc, or_left_comm, or_comm]

private theorem active_nodup (L : ModLayout) (hnd : L.wires.Nodup) : L.activeWires.Nodup := by
  have hs : [L.high.x, L.high.y, L.high.total, L.high.modulus, L.high.diff,
      L.high.carrySum, L.high.carryDiff].Sublist L.high.all := by
    apply List.Sublist.cons₂
    apply List.Sublist.cons₂
    apply List.Sublist.cons₂
    apply List.Sublist.cons₂
    apply List.Sublist.cons₂
    exact List.Sublist.cons _ (List.Sublist.refl _)
  have h := (hs.append_left (L.low.flatMap ModBit.all)).cons₂ L.cinDiff |>.cons₂ L.cinSum
  have hh : L.activeWires.Sublist L.wires := by
    simpa [ModLayout.activeWires, ModLayout.wires, ModLayout.bits] using h
  exact hh.nodup hnd

theorem modAdd_wires (L : ModLayout) (q : Nat) :
    wires (modAdd L q) = L.activeWires.toFinset := by
  ext w
  have hk : w ∈ wires (xorConstant (L.reg .modulus) q) → w ∈ L.reg .modulus :=
    fun h => List.mem_toFinset.mp (xorConstant_wires_subset _ _ h)
  have hd := L.lowReg_subset .diff (a := w)
  have ht := L.lowReg_subset .total (a := w)
  have hf : w = L.high.diff → w ∈ L.reg .diff := by
    rintro rfl; exact L.high_diff_mem
  simp only [modAdd, wires_append, Finset.mem_union, modAdder_mem, sub_mem, select_mem,
    List.mem_toFinset, layout_mem]
  aesop

theorem modSub_wires (L : ModLayout) (q : Nat) :
    wires (modSub L q) = L.activeWires.toFinset := by
  ext w
  have hk : w ∈ wires (xorConstant (L.reg .modulus) q) → w ∈ L.reg .modulus :=
    fun h => List.mem_toFinset.mp (xorConstant_wires_subset _ _ h)
  have hd := L.lowReg_subset .diff (a := w)
  have ht := L.lowReg_subset .total (a := w)
  have hf : w = L.high.diff → w ∈ L.reg .diff := by
    rintro rfl; exact L.high_diff_mem
  simp only [modSub, wires_append, Finset.mem_union, modAdder_mem, sub_mem, select_mem,
    List.mem_toFinset, layout_mem]
  aesop

private theorem layout_length (L : ModLayout) : L.activeWires.length = 8 * L.width + 9 := by
  have h (bs : List ModBit) : (bs.flatMap ModBit.all).length = 8 * bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [ModBit.all, ih]; omega
  simp [ModLayout.activeWires, h, ModLayout.width]


/-- 四次 (n+1) 位算术和 n 位单 Toffoli 选择；输出高位不施门。 -/
theorem modAdd_resources (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat) :
    toffoliCount (modAdd L q) = 5 * L.width + 4 ∧
    measurementCount (modAdd L q) = 4 * (L.width + 1) ∧
    qubitCount (modAdd L q) = 8 * L.width + 9 := by
  have hq : qubitCount (modAdd L q) = 8 * L.width + 9 := by
    rw [qubitCount, modAdd_wires, List.toFinset_card_of_nodup (active_nodup L hnd), layout_length]
  refine ⟨?_, ?_, hq⟩ <;>
    simp [modAdd, toffoliCount_append, measurementCount_append, (xorConstant_counts _ _).1,
      (xorConstant_counts _ _).2, add, sub, rippleAdder_toffoliCount, rippleAdder_measurementCount,
      (rippleSubtractor_counts _ _).1, (rippleSubtractor_counts _ _).2,
      (selectXor_counts _ _).1, (selectXor_counts _ _).2,
      ModLayout.adder, ModLayout.selector, ModLayout.bits, ModLayout.width] <;> omega

theorem modSub_resources (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat) :
    toffoliCount (modSub L q) = 5 * L.width + 4 ∧
    measurementCount (modSub L q) = 4 * (L.width + 1) ∧
    qubitCount (modSub L q) = 8 * L.width + 9 := by
  have hq : qubitCount (modSub L q) = 8 * L.width + 9 := by
    rw [qubitCount, modSub_wires, List.toFinset_card_of_nodup (active_nodup L hnd), layout_length]
  refine ⟨?_, ?_, hq⟩ <;>
    simp [modSub, toffoliCount_append, measurementCount_append, (xorConstant_counts _ _).1,
      (xorConstant_counts _ _).2, add, sub, rippleAdder_toffoliCount, rippleAdder_measurementCount,
      (rippleSubtractor_counts _ _).1, (rippleSubtractor_counts _ _).2,
      (selectXor_counts _ _).1, (selectXor_counts _ _).2,
      ModLayout.adder, ModLayout.selector, ModLayout.bits, ModLayout.width] <;> omega

end ECDSAAdd.Arithmetic
