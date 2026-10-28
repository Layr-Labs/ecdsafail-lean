import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- 两个候选值与输出位，均按小端排列。 -/
structure SelectBit where
  no : Wire
  yes : Wire
  out : Wire

def selectWires : List SelectBit → List Wire
  | [] => []
  | b :: bs => b.no :: b.yes :: b.out :: selectWires bs

/-- 输出异或 (if flag then yes else no)。暂时将 yes XOR 到 no，
用一个 Toffoli 选择差值，再还原 no；选择位必须在这三组线路之外。 -/
def selectXor : List SelectBit → Wire → Program
  | [], _ => []
  | b :: bs, flag => prog { Instr.CX b.no b.out;
      Instr.CX b.yes b.no; Instr.CCX flag b.no b.out; Instr.CX b.yes b.no } ++ selectXor bs flag

private theorem mem_selectWires {bs : List SelectBit} {b : SelectBit} (hb : b ∈ bs) :
    b.no ∈ selectWires bs ∧ b.yes ∈ selectWires bs ∧ b.out ∈ selectWires bs := by
  induction bs with
  | nil => simp at hb
  | cons a bs ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [selectWires]
    · obtain ⟨hn, hy, ho⟩ := ih hb
      simp [selectWires, hn, hy, ho]

private theorem selectStep_correct (a b out flag : Wire)
    (ha : a ≠ out) (hb : b ≠ out) (hab : a ≠ b) (hf : flag ≠ out) (hfa : flag ≠ a)
    (s : State) (m : List Bool) :
    run (prog { Instr.CX a out; Instr.CX b a; Instr.CCX flag a out; Instr.CX b a }) m s =
      ⟨s.phase, writeBit s.basis out (s.basis out ^^ (if s.basis flag then s.basis b else s.basis a))⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w = out
  · subst w
    simp only [writeBit, Function.update_self, Function.update_of_ne ha,
      Function.update_of_ne hb, Function.update_of_ne hf, Function.update_of_ne hfa,
      Function.update_of_ne (Ne.symm ha), Function.update_of_ne (Ne.symm hab)]
    cases s.basis flag <;> cases s.basis a <;> cases s.basis b <;> cases s.basis out <;> rfl
  · by_cases hw' : w = a
    · subst w
      simp only [writeBit, Function.update_self, Function.update_of_ne ha,
        Function.update_of_ne hb, Function.update_of_ne (Ne.symm hab)]
      cases s.basis a <;> cases s.basis b <;> rfl
    · simp [writeBit, hw, hw']

/-- 两个输入寄存器和选择位保持，任意输出初值按选择结果 XOR 更新。 -/
theorem selectXor_correct (bs : List SelectBit) (flag : Wire)
    (hnd : (selectWires bs).Nodup) (hflag : flag ∉ selectWires bs)
    (s : State) (m : List Bool) :
    (run (selectXor bs flag) m s).phase = s.phase ∧
    (∀ w, w ∉ bs.map SelectBit.out → (run (selectXor bs flag) m s).basis w = s.basis w) ∧
    regValue (bs.map SelectBit.out) (run (selectXor bs flag) m s).basis =
      regValue (bs.map SelectBit.out) s.basis ^^^
        (if s.basis flag then regValue (bs.map SelectBit.yes) s.basis
         else regValue (bs.map SelectBit.no) s.basis) := by
  induction bs generalizing s with
  | nil => simp [selectXor, run, regValue]
  | cons b bs ih =>
    simp only [selectWires, List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨hny, hno, hnr⟩, ⟨hyo, hyr⟩, hor, hr⟩ := hnd
    have hf : flag ≠ b.no ∧ flag ≠ b.yes ∧ flag ≠ b.out ∧ flag ∉ selectWires bs := by
      simpa only [selectWires, List.mem_cons, not_or] using hflag
    let s1 : State := ⟨s.phase, writeBit s.basis b.out
      (s.basis b.out ^^ (if s.basis flag then s.basis b.yes else s.basis b.no))⟩
    have hs1 (w : Wire) (hw : w ∈ selectWires bs) : s1.basis w = s.basis w := by
      have hn : w ≠ b.out := by intro h; apply hor; simpa [h] using hw
      simp [s1, writeBit, hn]
    let t := run (selectXor bs flag) m s1
    obtain ⟨hp, he, hv⟩ := ih hr hf.2.2.2 s1
    have ho : b.out ∉ bs.map SelectBit.out := by
      intro hw
      obtain ⟨d, hd, heq⟩ := List.mem_map.mp hw
      exact hor (heq ▸ (mem_selectWires hd).2.2)
    have htO : t.basis b.out = s1.basis b.out := he _ ho
    simp only [selectXor, run_append, run_take]
    rw [selectStep_correct _ _ _ _ hno hyo hny hf.2.2.1 hf.1]
    change (run (selectXor bs flag) (m.drop 0) s1).phase = _ ∧ _
    rw [List.drop_zero]
    refine ⟨hp, ?_, ?_⟩
    · intro w hw
      have hw' : w ≠ b.out ∧ w ∉ bs.map SelectBit.out := by
        simpa only [List.map_cons, List.mem_cons, not_or] using hw
      have ht : t.basis w = s1.basis w := he _ hw'.2
      change t.basis w = _
      rw [ht]
      simp [s1, writeBit, hw'.1]
    · have hread (f : SelectBit → Wire) (hf : ∀ d ∈ bs, f d ∈ selectWires bs) :
          regValue (bs.map f) s1.basis = regValue (bs.map f) s.basis :=
        regValue_congr _ _ _ (by
          intro w hw
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hw
          exact hs1 _ (hf d hd))
      have hn' := hread SelectBit.no (fun d hd => (mem_selectWires hd).1)
      have hy' := hread SelectBit.yes (fun d hd => (mem_selectWires hd).2.1)
      have ho' := hread SelectBit.out (fun d hd => (mem_selectWires hd).2.2)
      have hf' : s1.basis flag = s.basis flag := by simp [s1, writeBit, hf.2.2.1]
      change (if t.basis b.out then 1 else 0) + 2 * regValue (bs.map SelectBit.out) t.basis = _
      rw [htO, hv, hn', hy', ho', hf']
      simp only [s1, writeBit, Function.update_self, List.map_cons]
      have hx (choice : Bool) (rest : Nat) := xor_value_step (s.basis b.out) choice
        (regValue (bs.map SelectBit.out) s.basis) rest
      cases h : s.basis flag
      · simpa only [h, Bool.false_eq_true, if_false, regValue, List.foldr_cons,
          Bool.toNat, Bool.cond_eq_ite] using hx (s.basis b.no) (regValue (bs.map SelectBit.no) s.basis)
      · simpa only [h, if_true, regValue, List.foldr_cons,
          Bool.toNat, Bool.cond_eq_ite] using hx (s.basis b.yes) (regValue (bs.map SelectBit.yes) s.basis)

/-- 每位一次 Toffoli，整个选择没有测量。 -/
theorem selectXor_counts (bs : List SelectBit) (flag : Wire) :
    toffoliCount (selectXor bs flag) = bs.length ∧
    measurementCount (selectXor bs flag) = 0 := by
  induction bs with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    simp only [selectXor, toffoliCount_append, measurementCount_append,
      toffoliCount, measurementCount, List.length_cons, ih.1, ih.2]
    exact ⟨by omega, trivial⟩

/-- 非空选择的支持集是输入、输出线路与选择位的并集。 -/
theorem selectXor_wires (b : SelectBit) (bs : List SelectBit) (flag : Wire) :
    wires (selectXor (b :: bs) flag) = insert flag (selectWires (b :: bs)).toFinset := by
  induction bs generalizing b with
  | nil =>
    ext w
    simp [selectXor, wires, Instr.wires, selectWires]
    tauto
  | cons c cs ih =>
    rw [selectXor, wires_append, ih]
    ext w
    simp [wires, Instr.wires, selectWires]
    tauto

end ECDSAAdd.Arithmetic
