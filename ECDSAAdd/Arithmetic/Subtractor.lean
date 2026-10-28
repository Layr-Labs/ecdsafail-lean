import ECDSAAdd.Arithmetic.RippleAdder

namespace ECDSAAdd.Arithmetic

/-- X + ¬Y + 1 的低 n 位；前后两次 X 层恢复 Y 与输入进位工作线。 -/
def rippleSubtractor (bs : List AddBit) (cin : Wire) : Program :=
  notRegister (bs.map AddBit.y ++ [cin]) ++ rippleAdder bs cin ++
    notRegister (bs.map AddBit.y ++ [cin])

private theorem y_sublist (bs : List AddBit) : List.Sublist (bs.map AddBit.y) (addWires bs) := by
  induction bs with
  | nil => exact List.Sublist.refl _
  | cons b bs ih => exact (((ih.cons b.carry).cons b.out).cons₂ b.y).cons b.x

private theorem not_y (bs : List AddBit) (hnd : (addWires bs).Nodup) :
    ∀ b ∈ bs, b.x ∉ bs.map AddBit.y ∧ b.out ∉ bs.map AddBit.y ∧
      b.carry ∉ bs.map AddBit.y := by
  induction bs with
  | nil => simp
  | cons a bs ih =>
    simp only [addWires, List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨hxy, hxo, hxk, hxr⟩, ⟨hyo, hyk, hyr⟩, ⟨hok, hor⟩, hkr, hr⟩ := hnd
    have hn (w : Wire) (h : w ∉ addWires bs) : w ∉ bs.map AddBit.y :=
      fun hw => h ((y_sublist bs).subset hw)
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [hn _ hxr, hn _ hor, hn _ hkr, hxy, Ne.symm hyo, Ne.symm hyk]
    · obtain ⟨hx, ho, hk⟩ := ih hr b hb
      obtain ⟨hx', _, ho', hk'⟩ := mem_addWires hb
      have hxy' : b.x ≠ a.y := by intro h; apply hyr; simpa [h] using hx'
      have hoy' : b.out ≠ a.y := by intro h; apply hyr; simpa [h] using ho'
      have hky' : b.carry ≠ a.y := by intro h; apply hyr; simpa [h] using hk'
      simp [hx, ho, hk, hxy', hoy', hky']

/-- 任意输出初值的 XOR 减法，所有非输出线路均恢复。 -/
theorem rippleSubtractor_xor_correct (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) (s : State) (m : List Bool)
    (hc : s.basis cin = false) (hclean0 : ∀ b ∈ bs, s.basis b.carry = false) :
    (run (rippleSubtractor bs cin) m s).phase = s.phase ∧
    (∀ w, w ∉ bs.map AddBit.out → (run (rippleSubtractor bs cin) m s).basis w = s.basis w) ∧
    regValue (bs.map AddBit.out) (run (rippleSubtractor bs cin) m s).basis =
      regValue (bs.map AddBit.out) s.basis ^^^
      ((regValue (bs.map AddBit.x) s.basis + 2^bs.length - regValue (bs.map AddBit.y) s.basis) %
        2^bs.length) := by
  let X := regValue (bs.map AddBit.x) s.basis
  let Y := regValue (bs.map AddBit.y) s.basis
  let O := regValue (bs.map AddBit.out) s.basis
  have hx : regValue (bs.map AddBit.x) s.basis = X := rfl
  have hy : regValue (bs.map AddBit.y) s.basis = Y := rfl
  have ho : regValue (bs.map AddBit.out) s.basis = O := rfl
  have hk : regValue (bs.map AddBit.carry) s.basis = 0 := (regValue_zero _ _).mpr (by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    exact hclean0 b hb)
  obtain ⟨hcw, hn⟩ := List.nodup_cons.mp hnd
  let r := bs.map AddBit.y ++ [cin]
  have hcy : cin ∉ bs.map AddBit.y := fun h => hcw ((y_sublist bs).subset h)
  have hr : r.Nodup := by
    have hd : ∀ b ∈ bs, b.y ≠ cin := by
      intro b hb he
      exact hcy (he ▸ List.mem_map.mpr ⟨b, hb, rfl⟩)
    simpa [r, List.nodup_append] using And.intro ((y_sublist bs).nodup hn) hd
  have hnc (b : AddBit) (hb : b ∈ bs) :
      b.x ≠ cin ∧ b.out ≠ cin ∧ b.carry ≠ cin := by
    obtain ⟨hx', _, ho', hk'⟩ := mem_addWires hb
    exact ⟨fun h => hcw (h ▸ hx'), fun h => hcw (h ▸ ho'), fun h => hcw (h ▸ hk')⟩
  have hnot (b : AddBit) (hb : b ∈ bs) : b.x ∉ r ∧ b.out ∉ r ∧ b.carry ∉ r := by
    obtain ⟨hx', ho', hk'⟩ := not_y bs hn b hb
    obtain ⟨hxc, hoc, hkc⟩ := hnc b hb
    simp [r, hx', ho', hk', hxc, hoc, hkc]
  let s1 : State := ⟨s.phase, fun w => if w ∈ r then !s.basis w else s.basis w⟩
  have hfirst (record : List Bool) : run (notRegister r) record s = s1 :=
    notRegister_correct r hr s record
  have hc1 : s1.basis cin = true := by simp [s1, r, hc]
  have hread (f : AddBit → Wire) (h : ∀ b ∈ bs, f b ∉ r) :
      regValue (bs.map f) s1.basis = regValue (bs.map f) s.basis :=
    regValue_congr _ _ _ (by
      intro w hw
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
      simp [s1, h b hb])
  have hx1 := (hread AddBit.x (fun b hb => (hnot b hb).1)).trans hx
  have ho1 := (hread AddBit.out (fun b hb => (hnot b hb).2.1)).trans ho
  have hk1 := (hread AddBit.carry (fun b hb => (hnot b hb).2.2)).trans hk
  have hy1 : regValue (bs.map AddBit.y) s1.basis = 2^bs.length - 1 - Y := by
    rw [regValue_congr _ _ (fun w => !s.basis w) (by
      intro w hw
      simp [s1, r, hw]), regValue_complement, List.length_map, hy]
  have hclean : ∀ b ∈ bs, s1.basis b.carry = false := by
    intro b hb
    exact (regValue_zero _ _).mp hk1 _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  let t := run (rippleAdder bs cin) m s1
  obtain ⟨hp, hsame, hsum⟩ := rippleAdder_xor_correct bs cin hnd s1 m hclean
  have hrout : ∀ w ∈ r, w ∉ bs.map AddBit.out := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
      exact (inputs_not_output bs hn b hb).2.1
    · have he : w = cin := by simpa using hw
      subst w
      intro hw
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hw
      exact hcw (he ▸ (mem_addWires hb).2.2.1)
  have hfinal : ∀ w, w ∉ bs.map AddBit.out →
      (if w ∈ r then !t.basis w else t.basis w) = s.basis w := by
    intro w hw
    have ht : t.basis w = s1.basis w := hsame w hw
    rw [ht]
    by_cases hwr : w ∈ r <;> simp [s1, hwr]
  simp only [rippleSubtractor, run_append, run_take]
  rw [hfirst]
  simp only [(notRegister_counts (bs.map AddBit.y ++ [cin])).2, zero_add, measurementCount_append, List.drop_zero]
  change (run (notRegister r) _ t).phase = _ ∧ _
  rw [notRegister_correct r hr]
  refine ⟨hp, hfinal, ?_⟩
  have hout := regValue_congr (bs.map AddBit.out)
    (fun w => if w ∈ r then !t.basis w else t.basis w) t.basis (by
      intro w hw
      have hwr : w ∉ r := fun h => hrout w h hw
      simp [hwr])
  have hbound : Y < 2^bs.length := by simpa [hy] using regValue_lt (bs.map AddBit.y) s.basis
  have he : X + (2^bs.length - 1 - Y) + 1 = X + 2^bs.length - Y := by omega
  rw [hout, hsum, ho1, hx1, hy1, hc1, Bool.toNat_true, he]

/-- 任意初值输出的减法规格，输入和工作位保持。 -/
theorem rippleSubtractor_xor_spec (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) (X Y O : Nat) :
    {{ bs.map AddBit.x = X, bs.map AddBit.y = Y, cin = false,
       bs.map AddBit.out = O, bs.map AddBit.carry = (0 : Nat) }} rippleSubtractor bs cin
    {{ bs.map AddBit.x = X, bs.map AddBit.y = Y, cin = false,
       bs.map AddBit.out = (O ^^^ ((X + 2^bs.length - Y) % 2^bs.length)),
       bs.map AddBit.carry = (0 : Nat) }} := by
  intro s m hP
  simp only [Holds.holds] at hP ⊢
  obtain ⟨⟨⟨⟨hx, hy⟩, hc⟩, ho⟩, hk⟩ := hP
  obtain ⟨hp, he, hv⟩ := rippleSubtractor_xor_correct bs cin hnd s m hc (by
    intro b hb
    exact (regValue_zero _ _).mp hk _ (List.mem_map.mpr ⟨b, hb, rfl⟩))
  have hn := inputs_not_output bs (List.nodup_cons.mp hnd).2
  have hreg (f : AddBit → Wire) (h : ∀ b ∈ bs, f b ∉ bs.map AddBit.out) :
      regValue (bs.map f) (run (rippleSubtractor bs cin) m s).basis = regValue (bs.map f) s.basis :=
    regValue_congr _ _ _ (by
      intro w hw
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
      exact he _ (h b hb))
  have hc' : (run (rippleSubtractor bs cin) m s).basis cin = s.basis cin := by
    apply he
    intro h
    obtain ⟨b, hb, hb'⟩ := List.mem_map.mp h
    exact (List.nodup_cons.mp hnd).1 (hb' ▸ (mem_addWires hb).2.2.1)
  exact ⟨hp, ⟨⟨⟨(hreg _ (fun b hb => (hn b hb).1)).trans hx,
      (hreg _ (fun b hb => (hn b hb).2.1)).trans hy⟩, hc'.trans hc⟩,
      by simpa only [hx, hy, ho] using hv⟩, (hreg _ (fun b hb => (hn b hb).2.2)).trans hk⟩

/-- 零输出时，XOR 写入得到模 2^n 的差。 -/
theorem rippleSubtractor_spec (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) (X Y : Nat) :
    {{ bs.map AddBit.x = X, bs.map AddBit.y = Y, cin = false,
       bs.map AddBit.out = (0 : Nat), bs.map AddBit.carry = (0 : Nat) }} rippleSubtractor bs cin
    {{ bs.map AddBit.x = X, bs.map AddBit.y = Y, cin = false,
       bs.map AddBit.out = ((X + 2^bs.length - Y) % 2^bs.length),
       bs.map AddBit.carry = (0 : Nat) }} := by
  simpa only [Nat.zero_xor] using rippleSubtractor_xor_spec bs cin hnd X Y 0

/-- 减法的两层 X 不增加 Toffoli 或测量。 -/
theorem rippleSubtractor_counts (bs : List AddBit) (cin : Wire) :
    toffoliCount (rippleSubtractor bs cin) = bs.length ∧
    measurementCount (rippleSubtractor bs cin) = bs.length := by
  simp [rippleSubtractor, toffoliCount_append, measurementCount_append,
    (notRegister_counts _).1, (notRegister_counts _).2,
    rippleAdder_toffoliCount, rippleAdder_measurementCount]

/-- 减法访问进位工作线和每位的四根线路。 -/
theorem rippleSubtractor_wires (bs : List AddBit) (cin : Wire) :
    wires (rippleSubtractor bs cin) = (cin :: addWires bs).toFinset := by
  cases bs with
  | nil => simp [rippleSubtractor, rippleAdder, wires_append, notRegister_wires, addWires]
  | cons b bs =>
    rw [rippleSubtractor, wires_append, wires_append, notRegister_wires,
      rippleAdder_wires]
    ext w
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_cons]
    have hy : w ∈ (b :: bs).map AddBit.y → w ∈ addWires (b :: bs) := fun hw => (y_sublist _).subset hw
    tauto

/-- n 位减法使用 4n+1 根静态线路，包括恢复为零的输入进位工作线。 -/
theorem rippleSubtractor_qubitCount (bs : List AddBit) (cin : Wire)
    (hnd : (cin :: addWires bs).Nodup) :
    qubitCount (rippleSubtractor bs cin) = 4 * bs.length + 1 := by
  rw [qubitCount, rippleSubtractor_wires, List.toFinset_card_of_nodup hnd]
  simp [addWires_length]

end ECDSAAdd.Arithmetic
