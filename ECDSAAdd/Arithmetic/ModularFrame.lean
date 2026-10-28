import ECDSAAdd.Arithmetic.ModularResources

namespace ECDSAAdd.Arithmetic

/-- 按寄存器分组与按位分组包含同一组线路。 -/
theorem ModLayout.interface_perm (L : ModLayout) :
    (L.x ++ L.y ++ L.out ++ L.work).Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  rcases L with ⟨low, high, cinSum, cinDiff⟩
  induction low with
  | nil =>
    simp [ModLayout.x, ModLayout.y, ModLayout.out, ModLayout.work, ModLayout.wires,
      ModLayout.reg, ModLayout.bits, ModBit.get, ModBit.all, List.count_cons]
    omega
  | cons b bs ih =>
    simp [ModLayout.x, ModLayout.y, ModLayout.out, ModLayout.work, ModLayout.wires,
      ModLayout.reg, ModLayout.bits, ModBit.get, ModBit.all, List.count_cons] at ih ⊢
    omega

theorem ModLayout.active_subset (L : ModLayout) : L.activeWires ⊆ L.wires := by
  intro w hw
  simp only [ModLayout.activeWires, ModLayout.wires, ModLayout.bits, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, ModBit.all, List.mem_cons,
    List.mem_append, List.not_mem_nil, or_false] at hw ⊢
  tauto

theorem ModLayout.cover (L : ModLayout) {w : Wire} (hw : w ∈ L.wires) :
    w ∈ L.x ∨ w ∈ L.y ∨ w ∈ L.out ∨ w ∈ L.work := by
  simp only [ModLayout.wires, List.mem_cons] at hw
  rcases hw with rfl | rfl | hw
  · exact Or.inr (Or.inr (Or.inr (by simp [ModLayout.work])))
  · exact Or.inr (Or.inr (Or.inr (by simp [ModLayout.work])))
  · obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp hw
    simp only [ModBit.all, List.mem_cons, List.not_mem_nil, or_false] at hm
    have hr (f : ModField) : b.get f ∈ L.reg f := List.mem_map.mpr ⟨b, hb, rfl⟩
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (hr .x)
    · exact Or.inr (Or.inl (hr .y))
    · exact Or.inr (Or.inr (Or.inr (by simp [ModLayout.work, show b.total ∈ L.reg .total from hr .total])))
    · exact Or.inr (Or.inr (Or.inr (by simp [ModLayout.work, show b.modulus ∈ L.reg .modulus from hr .modulus])))
    · exact Or.inr (Or.inr (Or.inr (by simp [ModLayout.work, show b.diff ∈ L.reg .diff from hr .diff])))
    · exact Or.inr (Or.inr (Or.inl (hr .out)))
    · exact Or.inr (Or.inr (Or.inr (by simp [ModLayout.work, show b.carrySum ∈ L.reg .carrySum from hr .carrySum])))
    · exact Or.inr (Or.inr (Or.inr (by simp [ModLayout.work, show b.carryDiff ∈ L.reg .carryDiff from hr .carryDiff])))


/-- 将寄存器保持提升成逐线保持，供更大的电路在外部寄存器上组合。 -/
theorem ModLayout.preserve_nonoutput (L : ModLayout) (s t : BasisState)
    (hx : regValue L.x t = regValue L.x s) (hy : regValue L.y t = regValue L.y s)
    (hw : regValue L.work t = regValue L.work s)
    (he : ∀ w, w ∉ L.wires → t w = s w) :
    ∀ w, w ∉ L.out → t w = s w := by
  intro w ho
  by_cases h : w ∈ L.wires
  · rcases L.cover h with h | h | h | h
    · exact (regValue_eq_iff L.x t s).mp hx w h
    · exact (regValue_eq_iff L.y t s).mp hy w h
    · exact False.elim (ho h)
    · exact (regValue_eq_iff L.work t s).mp hw w h
  · exact he w h

theorem modAdd_bounded_correct (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (s : State) (m : List Bool)
    (hXY : regValue L.x s.basis + regValue L.y s.basis < 2*q)
    (hwork : regValue L.work s.basis = 0) :
    (run (modAdd L q) m s).phase = s.phase ∧
    (∀ w, w ∉ L.out → (run (modAdd L q) m s).basis w = s.basis w) ∧
    regValue L.out (run (modAdd L q) m s).basis = regValue L.out s.basis ^^^
      ((regValue L.x s.basis + regValue L.y s.basis)%q) := by
  obtain ⟨hp, h⟩ := modAdd_bounded_spec L hnd q hq0 hq _ _ _ hXY s m ⟨⟨⟨rfl, rfl⟩, rfl⟩, hwork⟩
  refine ⟨hp, L.preserve_nonoutput s.basis _ h.1.1.1 h.1.1.2 (h.2.trans hwork.symm) ?_, h.1.2⟩
  intro w hw
  apply run_preserves_outside
  rw [modAdd_wires]
  exact fun h => hw (L.active_subset (List.mem_toFinset.mp h))

theorem modAdd_correct (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (s : State) (m : List Bool)
    (hX : regValue L.x s.basis < q) (hY : regValue L.y s.basis < q)
    (hwork : regValue L.work s.basis = 0) :
    (run (modAdd L q) m s).phase = s.phase ∧
    (∀ w, w ∉ L.out → (run (modAdd L q) m s).basis w = s.basis w) ∧
    regValue L.out (run (modAdd L q) m s).basis = regValue L.out s.basis ^^^
      ((regValue L.x s.basis + regValue L.y s.basis)%q) := by
  obtain ⟨hp, h⟩ := modAdd_spec L hnd q hq0 hq _ _ _ hX hY s m ⟨⟨⟨rfl, rfl⟩, rfl⟩, hwork⟩
  refine ⟨hp, L.preserve_nonoutput s.basis _ h.1.1.1 h.1.1.2 (h.2.trans hwork.symm) ?_, h.1.2⟩
  intro w hw
  apply run_preserves_outside
  rw [modAdd_wires]
  exact fun h => hw (L.active_subset (List.mem_toFinset.mp h))

theorem modSub_correct (L : ModLayout) (hnd : L.wires.Nodup) (q : Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (s : State) (m : List Bool)
    (hX : regValue L.x s.basis < q) (hY : regValue L.y s.basis < q)
    (hwork : regValue L.work s.basis = 0) :
    (run (modSub L q) m s).phase = s.phase ∧
    (∀ w, w ∉ L.out → (run (modSub L q) m s).basis w = s.basis w) ∧
    regValue L.out (run (modSub L q) m s).basis = regValue L.out s.basis ^^^
      ((regValue L.x s.basis + q - regValue L.y s.basis)%q) := by
  obtain ⟨hp, h⟩ := modSub_spec L hnd q hq0 hq _ _ _ hX hY s m ⟨⟨⟨rfl, rfl⟩, rfl⟩, hwork⟩
  refine ⟨hp, L.preserve_nonoutput s.basis _ h.1.1.1 h.1.1.2 (h.2.trans hwork.symm) ?_, h.1.2⟩
  intro w hw
  apply run_preserves_outside
  rw [modSub_wires]
  exact fun h => hw (L.active_subset (List.mem_toFinset.mp h))

theorem ModValues.congr (L : ModLayout) (v : ModField → Nat) (s t : BasisState)
    (he : ∀ w ∈ L.wires, t w = s w) (hv : ModValues L v s) : ModValues L v t := by
  refine ⟨fun f => (regValue_congr _ _ _ ?_).trans (hv.1 f), ?_, ?_⟩
  · intro w hw
    exact he w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (L.reg_mem f hw)))
  · exact (he L.cinSum (by simp [ModLayout.wires])).trans hv.2.1
  · exact (he L.cinDiff (by simp [ModLayout.wires])).trans hv.2.2

theorem modActive_output (L : ModLayout) :
    L.activeWires.toFinset ∪ L.out.toFinset = L.wires.toFinset := by
  ext w
  simp [ModLayout.activeWires, ModLayout.out, ModLayout.reg, ModLayout.wires, ModLayout.bits,
    ModBit.all, ModBit.get, List.mem_flatMap, List.mem_map, exists_or, and_or_left, eq_comm]
  simp [or_left_comm, or_comm]

end ECDSAAdd.Arithmetic
