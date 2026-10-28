import ECDSAAdd.Arithmetic.ModularResources

namespace ECDSAAdd.Arithmetic

def ModBit.swapXOut (b : ModBit) : ModBit := { b with x := b.out, out := b.x }

/-- 交换两个累加器的角色；工作寄存器保持同一份。 -/
def ModLayout.swapXOut (L : ModLayout) : ModLayout :=
  { L with low := L.low.map ModBit.swapXOut, high := L.high.swapXOut }

@[simp] theorem ModLayout.swap_width (L : ModLayout) : L.swapXOut.width = L.width := by
  simp [ModLayout.swapXOut, ModLayout.width]

@[simp] theorem ModLayout.swap_x (L : ModLayout) : L.swapXOut.x = L.out := by
  simp [ModLayout.swapXOut, ModLayout.x, ModLayout.out, ModLayout.reg, ModLayout.bits,
    ModBit.swapXOut, ModBit.get, List.map_map, Function.comp_def]

@[simp] theorem ModLayout.swap_out (L : ModLayout) : L.swapXOut.out = L.x := by
  simp [ModLayout.swapXOut, ModLayout.x, ModLayout.out, ModLayout.reg, ModLayout.bits,
    ModBit.swapXOut, ModBit.get, List.map_map, Function.comp_def]

@[simp] theorem ModLayout.swap_y (L : ModLayout) : L.swapXOut.y = L.y := by
  simp [ModLayout.swapXOut, ModLayout.y, ModLayout.reg, ModLayout.bits,
    ModBit.swapXOut, ModBit.get, List.map_map, Function.comp_def]

@[simp] theorem ModLayout.swap_work (L : ModLayout) : L.swapXOut.work = L.work := by
  simp [ModLayout.swapXOut, ModLayout.work, ModLayout.reg, ModLayout.bits,
    ModBit.swapXOut, ModBit.get, List.map_map, Function.comp_def]

theorem ModLayout.swap_perm (L : ModLayout) : L.swapXOut.wires.Perm L.wires := by
  have hp (b : ModBit) : b.swapXOut.all.Perm b.all := by
    simp only [ModBit.swapXOut, ModBit.all]
    apply List.perm_iff_count.mpr
    intro w
    simp [List.count_cons]
    omega
  have h := (List.Perm.refl L.bits).flatMap (fun b _ => hp b)
  simpa [ModLayout.swapXOut, ModLayout.wires, ModLayout.bits, List.flatMap_map,
      Function.comp_def] using (h.cons L.cinDiff).cons L.cinSum

theorem ModLayout.swap_nodup (L : ModLayout) (hnd : L.wires.Nodup) : L.swapXOut.wires.Nodup :=
  L.swap_perm.nodup_iff.mpr hnd

theorem modular_sum_sub (A B q : Nat) (hA : A < q) (hB : B < q) :
    (((A+B)%q)+q-B)%q = A := by
  by_cases h : A+B < q
  · rw [Nat.mod_eq_of_lt h, show A+B+q-B = A+q by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hA]
  · have hs : (A+B)%q = A+B-q := by
      conv_lhs => rw [show A+B = (A+B-q)+q by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hs, show A+B-q+q-B = A by omega, Nat.mod_eq_of_lt hA]

/-- 将和写入空累加器，再通过模减把旧累加器清零；下一步交换角色复用。 -/
def accumulate (L : ModLayout) (q : Nat) : Program := modAdd L q ++ modSub L.swapXOut q

/-- 撤销一次累加也只调用已证明的前向程序，不反转测量指令。 -/
def unaccumulate (L : ModLayout) (q : Nat) : Program := modSub L.swapXOut q ++ modAdd L q

theorem accumulate_spec (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (A B : Nat) (hA : A < q) (hB : B < q) :
    {{ L.x = A, L.y = B, L.out = 0, L.work = 0 }} accumulate L q
    {{ L.x = 0, L.y = B, L.out = ((A+B)%q), L.work = 0 }} := by
  have h1 := modAdd_spec L hnd q hq0 hq A B 0 hA hB
  have h2 := modSub_spec L.swapXOut (L.swap_nodup hnd) q hq0 (by simpa using hq)
    ((A+B)%q) B A (Nat.mod_lt _ hq0) hB
  simp only [Nat.zero_xor] at h1
  simp only [ModLayout.swap_x, ModLayout.swap_y, ModLayout.swap_out, ModLayout.swap_work,
    modular_sum_sub A B q hA hB, Nat.xor_self] at h2
  apply h1.seq
  exact Triple.conseq (fun st h => ⟨⟨⟨h.1.2, h.1.1.2⟩, h.1.1.1⟩, h.2⟩) h2
    (fun st h => ⟨⟨⟨h.1.2, h.1.1.2⟩, h.1.1.1⟩, h.2⟩)

theorem unaccumulate_spec (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (A B : Nat) (hA : A < q) (hB : B < q) :
    {{ L.x = 0, L.y = B, L.out = ((A+B)%q), L.work = 0 }} unaccumulate L q
    {{ L.x = A, L.y = B, L.out = 0, L.work = 0 }} := by
  have h1 := modSub_spec L.swapXOut (L.swap_nodup hnd) q hq0 (by simpa using hq)
    ((A+B)%q) B 0 (Nat.mod_lt _ hq0) hB
  have h2 := modAdd_spec L hnd q hq0 hq A B ((A+B)%q) hA hB
  simp only [ModLayout.swap_x, ModLayout.swap_y, ModLayout.swap_out, ModLayout.swap_work,
    modular_sum_sub A B q hA hB, Nat.zero_xor] at h1
  simp only [Nat.xor_self] at h2
  apply Triple.seq (c := modSub L.swapXOut q) (d := modAdd L q) _ h2
  exact Triple.conseq (fun st h => ⟨⟨⟨h.1.2, h.1.1.2⟩, h.1.1.1⟩, h.2⟩) h1
    (fun st h => ⟨⟨⟨h.1.2, h.1.1.2⟩, h.1.1.1⟩, h.2⟩)

private theorem both_active_wires (L : ModLayout) :
    L.activeWires.toFinset ∪ L.swapXOut.activeWires.toFinset = L.wires.toFinset := by
  ext w
  simp [ModLayout.activeWires, ModLayout.swapXOut, ModLayout.wires, ModLayout.bits,
    ModBit.swapXOut, ModBit.all, List.mem_flatMap,
    List.flatMap_map, exists_or, and_or_left]
  simp only [or_left_comm, or_self]

theorem accumulate_wires (L : ModLayout) (q : Nat) :
    wires (accumulate L q) = L.wires.toFinset := by
  rw [accumulate, wires_append, modAdd_wires, modSub_wires, both_active_wires]

theorem unaccumulate_wires (L : ModLayout) (q : Nat) :
    wires (unaccumulate L q) = L.wires.toFinset := by
  rw [unaccumulate, wires_append, modSub_wires, modAdd_wires, Finset.union_comm, both_active_wires]

theorem accumulate_resources (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat) :
    toffoliCount (accumulate L q) = 10*L.width+8 ∧
    measurementCount (accumulate L q) = 8*(L.width+1) ∧
    qubitCount (accumulate L q) = 8*(L.width+1)+2 := by
  have ha := modAdd_resources L hnd q
  have hs := modSub_resources L.swapXOut (L.swap_nodup hnd) q
  have hl : L.wires.length = 8*(L.width+1)+2 := by
    have h (bs : List ModBit) : (bs.flatMap ModBit.all).length = 8*bs.length := by
      induction bs with
      | nil => rfl
      | cons b bs ih => simp [ModBit.all, ih]; omega
    simp [ModLayout.wires, h, ModLayout.bits, ModLayout.width, ModBit.all]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [accumulate, toffoliCount_append, ha.1, hs.1, ModLayout.swap_width]; omega
  · simp only [accumulate, measurementCount_append, ha.2.1, hs.2.1, ModLayout.swap_width]; omega
  · rw [qubitCount, accumulate, wires_append, modAdd_wires, modSub_wires,
      both_active_wires, List.toFinset_card_of_nodup hnd, hl]

theorem unaccumulate_resources (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat) :
    toffoliCount (unaccumulate L q) = 10*L.width+8 ∧
    measurementCount (unaccumulate L q) = 8*(L.width+1) ∧
    qubitCount (unaccumulate L q) = 8*(L.width+1)+2 := by
  simpa only [accumulate, unaccumulate, toffoliCount_append, measurementCount_append,
    Nat.add_comm, qubitCount, wires_append, Finset.union_comm] using accumulate_resources L hnd q

end ECDSAAdd.Arithmetic
