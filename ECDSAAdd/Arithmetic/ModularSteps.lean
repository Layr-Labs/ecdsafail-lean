import ECDSAAdd.Arithmetic.ModularLayout
import ECDSAAdd.Arithmetic.Reduction

namespace ECDSAAdd.Arithmetic

/-- 组合证明的内部状态断言：八组寄存器的读值和两根零输入进位线。 -/
def ModValues (L : ModLayout) (v : ModField → Nat) (st : BasisState) : Prop :=
  (∀ f, regValue (L.reg f) st = v f) ∧ st L.cinSum = false ∧ st L.cinDiff = false

theorem ModValues.update (L : ModLayout) (hnd : L.wires.Nodup) (v : ModField → Nat)
    (target : ModField) (z : Nat) (s t : BasisState) (hv : ModValues L v s)
    (he : ∀ w, w ∉ L.reg target → t w = s w) (hz : regValue (L.reg target) t = z) :
    ModValues L (Function.update v target z) t := by
  refine ⟨?_, (he _ (L.cinSum_not_reg hnd target)).trans hv.2.1,
    (he _ (L.cinDiff_not_reg hnd target)).trans hv.2.2⟩
  intro f
  by_cases hf : f = target
  · subst f; simpa using hz
  · rw [Function.update_of_ne hf]
    have hr := regValue_congr (L.reg f) t s (fun w hw => he w
      (List.disjoint_left.mp (L.reg_disjoint hnd f target hf) hw))
    exact hr.trans (hv.1 f)

theorem constant_modValues (L : ModLayout) (hnd : L.wires.Nodup) (v : ModField → Nat)
    (target : ModField) (k : Nat) (hk : k < 2^(L.width+1)) :
    Triple (ModValues L v) (xorConstant (L.reg target) k)
      (ModValues L (Function.update v target (v target ^^^ k))) := by
  intro s m hv
  obtain ⟨hp, he, hz⟩ := xorConstant_correct (L.reg target) (L.reg_nodup hnd target) k
    (by simpa only [ModLayout.reg_length] using hk) s m
  refine ⟨hp, ModValues.update L hnd v target _ s.basis _ hv he ?_⟩
  simpa only [hv.1 target] using hz

theorem add_modValues (L : ModLayout) (hnd : L.wires.Nodup) (v : ModField → Nat)
    (a b target carry : ModField) (hf : [a, b, target, carry].Nodup)
    (cin : Wire) (hcin : cin = L.cinSum ∨ cin = L.cinDiff) (hcarry : v carry = 0) :
    Triple (ModValues L v) (add (L.adder a b target carry cin))
      (ModValues L (Function.update v target (v target ^^^ ((v a + v b) % 2^(L.width+1))))) := by
  intro s m hv
  let A := L.adder a b target carry cin
  have hc : s.basis cin = false := by
    rcases hcin with rfl | rfl
    · exact hv.2.1
    · exact hv.2.2
  have hclean : regValue A.carry s.basis = 0 := by
    simpa only [A, ModLayout.adder_carry, hcarry] using hv.1 carry
  obtain ⟨hp, he, hz⟩ := rippleAdder_xor_correct A.bits A.cin (L.adder_nodup hnd a b target carry hf cin hcin) s m (by
    intro bit hb
    exact (regValue_zero _ _).mp hclean _ (List.mem_map.mpr ⟨bit, hb, rfl⟩))
  change ∀ w, w ∉ A.out → (run (add A) m s).basis w = s.basis w at he
  change regValue A.out (run (add A) m s).basis = regValue A.out s.basis ^^^
    ((regValue A.x s.basis + regValue A.y s.basis + (s.basis cin).toNat) % 2^A.width) at hz
  simp only [A, ModLayout.adder_out] at he
  refine ⟨hp, ModValues.update L hnd v target _ s.basis _ hv he ?_⟩
  simpa only [A, ModLayout.adder_out, ModLayout.adder_x, ModLayout.adder_y,
    ModLayout.adder_width, hv.1 a, hv.1 b, hv.1 target, hc, Bool.toNat_false, Nat.add_zero] using hz

theorem sub_modValues (L : ModLayout) (hnd : L.wires.Nodup) (v : ModField → Nat)
    (a b target carry : ModField) (hf : [a, b, target, carry].Nodup)
    (cin : Wire) (hcin : cin = L.cinSum ∨ cin = L.cinDiff) (hcarry : v carry = 0) :
    Triple (ModValues L v) (sub (L.adder a b target carry cin))
      (ModValues L (Function.update v target
        (v target ^^^ ((v a + 2^(L.width+1) - v b) % 2^(L.width+1))))) := by
  intro s m hv
  let A := L.adder a b target carry cin
  have hc : s.basis cin = false := by
    rcases hcin with rfl | rfl
    · exact hv.2.1
    · exact hv.2.2
  have hclean : regValue A.carry s.basis = 0 := by
    simpa only [A, ModLayout.adder_carry, hcarry] using hv.1 carry
  obtain ⟨hp, he, hz⟩ := rippleSubtractor_xor_correct A.bits A.cin
    (L.adder_nodup hnd a b target carry hf cin hcin) s m hc (by
      intro bit hb
      exact (regValue_zero _ _).mp hclean _ (List.mem_map.mpr ⟨bit, hb, rfl⟩))
  change ∀ w, w ∉ A.out → (run (sub A) m s).basis w = s.basis w at he
  change regValue A.out (run (sub A) m s).basis = regValue A.out s.basis ^^^
    ((regValue A.x s.basis + 2^A.width - regValue A.y s.basis) % 2^A.width) at hz
  simp only [A, ModLayout.adder_out] at he
  refine ⟨hp, ModValues.update L hnd v target _ s.basis _ hv he ?_⟩
  simpa only [A, ModLayout.adder_out, ModLayout.adder_x, ModLayout.adder_y,
    ModLayout.adder_width, hv.1 a, hv.1 b, hv.1 target] using hz

theorem select_modValues (L : ModLayout) (hnd : L.wires.Nodup) (v : ModField → Nat)
    (hbound : (if 2^L.width ≤ v .diff then v .total else v .diff) < 2^L.width) :
    Triple (ModValues L v) (selectXor L.selector L.high.diff)
      (ModValues L (Function.update v .out
        (v .out ^^^ (if 2^L.width ≤ v .diff then v .total else v .diff)))) := by
  intro s m hv
  obtain ⟨hp, he, hz⟩ := selectXor_correct L.selector L.high.diff
    (L.selector_nodup hnd) (L.flag_not_selector hnd) s m
  have hhi : s.basis L.high.diff = true ↔ 2^L.width ≤ v .diff := by
    have h := regValue_highBit (L.low.map ModBit.diff) L.high.diff s.basis
    have hd : regValue (L.low.map ModBit.diff ++ [L.high.diff]) s.basis = v .diff := by
      simpa [ModLayout.reg, ModLayout.bits, ModBit.get] using hv.1 .diff
    simpa only [hd, List.length_map, ModLayout.width] using h
  simp only [ModLayout.selector_out, ModLayout.selector_no, ModLayout.selector_yes] at he hz
  have hlo (f : ModField) : regValue (L.lowReg f) s.basis = v f % 2^L.width := by
    have h := regValue_low (L.lowReg f) (L.high.get f) s.basis
    rw [← L.reg_eq, hv.1 f] at h
    simpa only [ModLayout.lowReg, List.length_map, ModLayout.width] using h
  let R := if 2^L.width ≤ v .diff then v .total else v .diff
  have hchoice : (if s.basis L.high.diff then regValue (L.lowReg .total) s.basis
      else regValue (L.lowReg .diff) s.basis) = R := by
    rw [hlo, hlo]
    have h : (if 2^L.width ≤ v .diff then v .total % 2^L.width else v .diff % 2^L.width) =
        R % 2^L.width := by unfold R; split_ifs <;> rfl
    simp only [hhi, h]
    exact Nat.mod_eq_of_lt hbound
  have hhigh : L.high.out ∉ L.lowReg .out := by
    have hn := L.reg_nodup hnd .out
    rw [L.reg_eq] at hn
    exact fun h => List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 h (by simp [ModBit.get])
  have hfull : regValue (L.reg .out) (run (selectXor L.selector L.high.diff) m s).basis =
      regValue (L.reg .out) s.basis ^^^ R := by
    rw [L.reg_eq, regValue_append, regValue_append, hz, hchoice]
    have hh := he L.high.out hhigh
    simp only [ModBit.get, regValue, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero] at hh ⊢
    rw [hh]
    exact xor_low_add (L.lowReg .out).length _ _ R (regValue_lt _ _) (by
      simpa [ModLayout.lowReg, ModLayout.width] using hbound)
  refine ⟨hp, ModValues.update L hnd v .out _ s.basis _ hv ?_ ?_⟩
  · intro w hw
    exact he w (fun h => hw (L.lowReg_subset .out h))
  · simpa only [hv.1 .out, R] using hfull

end ECDSAAdd.Arithmetic
