import ECDSAAdd.Arithmetic.RippleAdder
import ECDSAAdd.Arithmetic.MaskedConstant
import ECDSAAdd.Arithmetic.Copy

namespace ECDSAAdd.Arithmetic
open Instr

/-- fullAdder 的前六门：carry ^= MAJ(a,b,cin)，三个输入恢复，不写和位。 -/
def majority (a b cin carry : Wire) : Program := prog {
  CX a b; CX a cin; CCX b cin carry; CX a carry; CX a cin; CX a b
}

/-- 原地加法 y ← (x + y + cin) mod 2^n：每位先算进位、递归处理高位，
再用现有 eraseCarry 擦除本位进位（此时 x、y、cin 仍是原值），最后把和位写回 y。
最高位只写和位，不算进位，进位链比位宽少一根。 -/
def addInPlace : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      majority a b cin c ++ addInPlace (a' :: as) (b' :: bs) cs c ++
        eraseCarry a b cin c ++ [CX a b, CX cin b]
  | [a], [b], _, cin => [CX a b, CX cin b]
  | _, _, _, _ => []

/-- 进位异或写入 carry，其余状态保持。 -/
theorem majority_correct (a b cin carry : Wire) (hnd : [a, b, cin, carry].Nodup)
    (s : State) (m : List Bool) :
    run (majority a b cin carry) m s =
      ⟨s.phase, writeBit s.basis carry
        (s.basis carry ^^ carryBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hnd
  obtain ⟨⟨hab, hac, hak⟩, ⟨hbc, hbk⟩, hck⟩ := hnd
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hcb := Ne.symm hbc
  simp only [majority, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwa : w = a <;> by_cases hwb : w = b <;>
    by_cases hwc : w = cin <;> by_cases hwk : w = carry <;>
    simp_all [writeBit, Function.update, carryBit]
  all_goals cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;>
    cases s.basis carry <;> simp_all

/-- 进位链初始为零时：x、cin 保持，y 原地得到低 n 位的和，进位链归零，相位对所有测量记录恢复。 -/
theorem addInPlace_correct (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (s : State) (m : List Bool)
    (hclean : ∀ w ∈ carry, s.basis w = false) :
    (run (addInPlace x y carry cin) m s).phase = s.phase ∧
    (∀ w, w ∉ y → (run (addInPlace x y carry cin) m s).basis w = s.basis w) ∧
    regValue y (run (addInPlace x y carry cin) m s).basis =
      (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^y.length := by
  induction y generalizing x carry cin s m with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    have hcin : cin ∉ a :: as ++ b :: bs ++ carry := (List.nodup_cons.mp hnd).1
    have hrest : ((a :: as) ++ ((b :: bs) ++ carry)).Nodup := by
      simpa only [List.append_assoc] using (List.nodup_cons.mp hnd).2
    obtain ⟨has, hbk, hdisA⟩ := List.nodup_append'.mp hrest
    obtain ⟨hbs, hk, hdisB⟩ := List.nodup_append'.mp hbk
    have hca : cin ≠ a := fun h => hcin (by simp [h])
    have hcb : cin ≠ b := fun h => hcin (by simp [h])
    have hcbs : cin ∉ bs := fun h => hcin (by simp [h])
    have hab : a ≠ b := fun h => List.disjoint_left.mp hdisA List.mem_cons_self (by simp [h])
    have habs : a ∉ bs := fun h => List.disjoint_left.mp hdisA List.mem_cons_self (by simp [h])
    have hbbs : b ∉ bs := (List.nodup_cons.mp hbs).1
    let A := s.basis a
    let B := s.basis b
    let C := s.basis cin
    cases bs with
    | nil =>
      have hx0 : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hx)
      have hc0 : carry = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst hx0 hc0
      simp only [addInPlace, run]
      refine ⟨trivial, ?_, ?_⟩
      · intro w hw
        have hwb : w ≠ b := by simpa using hw
        simp [writeBit, hwb]
      · simp only [regValue, List.foldr_cons, List.foldr_nil, List.length_cons, List.length_nil,
          writeBit, Function.update_self, Function.update_of_ne hcb]
        cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;> simp
    | cons b' bs' =>
      cases as with
      | nil => simp at hx
      | cons a' as' =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
      have hx' : (a' :: as').length = (b' :: bs').length := by simpa using hx
      have hc' : cs.length + 1 = (b' :: bs').length := by simpa using hc
      have hbc : b ≠ c := fun h => List.disjoint_left.mp hdisB List.mem_cons_self (by simp [h])
      have hcbs' : c ∉ b' :: bs' := fun h =>
        List.disjoint_left.mp hdisB (List.mem_cons_of_mem _ h) List.mem_cons_self
      have hccs : c ∉ cs := (List.nodup_cons.mp hk).1
      have hac : a ≠ c := fun h => List.disjoint_left.mp hdisA List.mem_cons_self (by simp [h])
      have hcas : c ∉ a' :: as' := fun h =>
        List.disjoint_left.mp hdisA (List.mem_cons_of_mem _ h) (by simp)
      have hcc : cin ≠ c := fun h => hcin (by simp [h])
      have h4 : [a, b, cin, c].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          not_or, not_false_eq_true, and_true]
        exact ⟨⟨hab, Ne.symm hca, hac⟩, ⟨Ne.symm hcb, hbc⟩, hcc⟩
      have hnd' : (c :: ((a' :: as') ++ (b' :: bs') ++ cs)).Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_, ?_⟩
        · simp only [List.mem_append, not_or]
          exact ⟨⟨hcas, hcbs'⟩, hccs⟩
        · apply List.nodup_append'.mpr
          refine ⟨List.nodup_append'.mpr ⟨(List.nodup_cons.mp has).2, (List.nodup_cons.mp hbs).2, ?_⟩,
            (List.nodup_cons.mp hk).2, ?_⟩
          · exact List.disjoint_left.mpr (fun w hw hw' =>
              List.disjoint_left.mp hdisA (List.mem_cons_of_mem _ hw)
                (List.mem_cons_of_mem _ (List.mem_append_left _ hw')))
          · exact List.disjoint_left.mpr (fun w hw hw' => by
              rcases List.mem_append.mp hw with hw | hw
              · exact List.disjoint_left.mp hdisA (List.mem_cons_of_mem _ hw)
                  (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hw')))
              · exact List.disjoint_left.mp hdisB (List.mem_cons_of_mem _ hw) (List.mem_cons_of_mem _ hw'))
      have hzero : s.basis c = false := hclean c (by simp)
      -- 第一步：进位写入 c
      let s1 : State := ⟨s.phase, writeBit s.basis c (carryBit A B C)⟩
      have hfirst (record : List Bool) : run (majority a b cin c) record s = s1 := by
        rw [majority_correct _ _ _ _ h4]
        simp [s1, hzero, A, B, C]
      have hs1 (w : Wire) (hw : w ≠ c) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
      have hclean' : ∀ d ∈ cs, s1.basis d = false := by
        intro d hd
        rw [hs1 d (fun h => hccs (h ▸ hd))]
        exact hclean d (by simp [hd])
      -- 第二步：高位递归
      obtain ⟨hphase, hsame, hsum⟩ := ih (a' :: as') cs c hnd' hx' hc' s1 m hclean'
      set t := run (addInPlace (a' :: as') (b' :: bs') cs c) m s1 with ht
      have heq (w : Wire) (hw : w ∉ b' :: bs') : t.basis w = s1.basis w := hsame w hw
      have htA : t.basis a = A := by rw [heq a habs, hs1 a hac]
      have htB : t.basis b = B := by rw [heq b hbbs, hs1 b hbc]
      have htC : t.basis cin = C := by rw [heq cin hcbs, hs1 cin hcc]
      have htK : t.basis c = carryBit A B C := by rw [heq c hcbs']; simp [s1, writeBit]
      -- 第三步：擦除本位进位（x、y、cin 仍是原值）
      have herase (record : List Bool) : run (eraseCarry a b cin c) record t =
          ⟨t.phase, writeBit t.basis c false⟩ :=
        eraseCarry_correct _ _ _ _ hac hbc hcc t (by rw [htA, htB, htC, htK]) record
      -- 第四步：写和位
      have hlast (record : List Bool) :
          run [CX a b, CX cin b] record ⟨t.phase, writeBit t.basis c false⟩ =
            ⟨t.phase, writeBit (writeBit t.basis c false) b (sumBit A B C)⟩ := by
        simp only [run]
        apply congrArg (State.mk t.phase)
        funext w
        by_cases hwb : w = b
        · subst hwb
          simp only [writeBit, Function.update_self, Function.update_of_ne hcb,
            Function.update_of_ne hac, Function.update_of_ne hbc, Function.update_of_ne hcc,
            htA, htB, htC, sumBit]
          cases A <;> cases B <;> cases C <;> rfl
        · simp [writeBit, Function.update, hwb]
      -- 组合：按右结合展开，各段记录由 run_take 收回
      have hm0 : measurementCount (majority a b cin c) = 0 := rfl
      simp only [addInPlace, List.append_assoc, run_append, run_take, hm0, List.take_zero,
        List.drop_zero]
      rw [hfirst, ← ht, herase, hlast]
      refine ⟨hphase, ?_, ?_⟩
      · intro w hw
        have hw' : w ≠ b ∧ w ∉ b' :: bs' := by simpa only [List.mem_cons, not_or] using hw
        change (writeBit (writeBit t.basis c false) b (sumBit A B C)) w = s.basis w
        rw [writeBit, Function.update_of_ne hw'.1]
        by_cases hwc : w = c
        · subst hwc; simp [writeBit, hzero]
        · rw [writeBit, Function.update_of_ne hwc, heq w hw'.2, hs1 w hwc]
      · have hbs_t : regValue (b' :: bs') (writeBit (writeBit t.basis c false) b (sumBit A B C)) =
            regValue (b' :: bs') t.basis := by
          apply regValue_congr
          intro w hw
          have hwb : w ≠ b := fun h => hbbs (h ▸ hw)
          have hwc : w ≠ c := fun h => hcbs' (h ▸ hw)
          simp [writeBit, hwb, hwc]
        have hx1 : regValue (a' :: as') s1.basis = regValue (a' :: as') s.basis :=
          regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcas (h ▸ hw)))
        have hy1 : regValue (b' :: bs') s1.basis = regValue (b' :: bs') s.basis :=
          regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcbs' (h ▸ hw)))
        have hc1 : s1.basis c = carryBit A B C := by simp [s1, writeBit]
        change (if (writeBit (writeBit t.basis c false) b (sumBit A B C)) b then 1 else 0) +
            2 * regValue (b' :: bs') (writeBit (writeBit t.basis c false) b (sumBit A B C)) = _
        rw [hbs_t, hsum, hx1, hy1, hc1]
        simp only [writeBit, Function.update_self, List.length_cons]
        have hnum := sum_value_step A B C (regValue (a' :: as') s.basis)
          (regValue (b' :: bs') s.basis) (b' :: bs').length
        simp only [List.length_cons] at hnum
        simpa only [regValue, List.foldr_cons, Bool.toNat, Bool.cond_eq_ite, A, B, C] using hnum


/-- x、cin 保持，y 原地得到低 n 位的和，进位链归零。 -/
theorem addInPlace_spec (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (X Y : Nat) (C : Bool) :
    {{ x = X, y = Y, cin = C, carry = 0 }} addInPlace x y carry cin
    {{ x = X, y = ((X + Y + C.toNat) % 2^y.length), cin = C, carry = 0 }} := by
  intro s m hP
  simp only [Holds.holds] at hP ⊢
  obtain ⟨⟨⟨hxv, hyv⟩, hcv⟩, hkv⟩ := hP
  have hclean : ∀ w ∈ carry, s.basis w = false := fun w hw => (regValue_zero _ _).mp hkv w hw
  obtain ⟨hp, hsame, hsum⟩ := addInPlace_correct x y carry cin hnd hx hc s m hclean
  have hn := List.nodup_cons.mp hnd
  have hn2 := List.nodup_append'.mp (by simpa only [List.append_assoc] using hn.2 : (x ++ (y ++ carry)).Nodup)
  have hyc := List.nodup_append'.mp hn2.2.1
  have hxy : ∀ w ∈ x, w ∉ y := fun w hw hy => List.disjoint_left.mp hn2.2.2 hw (List.mem_append_left _ hy)
  have hky : ∀ w ∈ carry, w ∉ y := fun w hw hy => List.disjoint_left.mp hyc.2.2 hy hw
  have hciny : cin ∉ y := fun h => hn.1 (by simp [h])
  refine ⟨hp, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => hsame w (hxy w hw))).trans hxv
  · rw [hsum, hxv, hyv, hcv]
  · exact (hsame cin hciny).trans hcv
  · exact (regValue_congr _ _ _ (fun w hw => hsame w (hky w hw))).trans hkv

/-- y ← (y − x) mod 2^n：按位取反、加 x、再取反，¬(¬y + x) = y − x；两层 X 门不计资源。 -/
def subInPlace (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addInPlace x y carry cin ++ notRegister y

private theorem flip_y (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (X Y K : Nat) (C : Bool) :
    {{ x = X, y = Y, cin = C, carry = K }} notRegister y
    {{ x = X, y = (2^y.length - 1 - Y), cin = C, carry = K }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hn := List.nodup_cons.mp hnd
  have hn2 := List.nodup_append'.mp (by simpa only [List.append_assoc] using hn.2 : (x ++ (y ++ carry)).Nodup)
  have hyc := List.nodup_append'.mp hn2.2.1
  have hxy : ∀ w ∈ x, w ∉ y := fun w hw hy => List.disjoint_left.mp hn2.2.2 hw (List.mem_append_left _ hy)
  have hky : ∀ w ∈ carry, w ∉ y := fun w hw hy => List.disjoint_left.mp hyc.2.2 hy hw
  have hciny : cin ∉ y := fun hh => hn.1 (by simp [hh])
  rw [notRegister_correct y hyc.1]
  refine ⟨rfl, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => by simp [hxy w hw])).trans h.1.1.1
  · change regValue y (fun w => if w ∈ y then !s.basis w else s.basis w) = _
    rw [regValue_congr y _ (fun w => !s.basis w) (by intro w hw; simp [hw]), regValue_complement, h.1.1.2]
  · simpa [hciny] using h.1.2
  · exact (regValue_congr _ _ _ (fun w hw => by simp [hky w hw])).trans h.2

private theorem complement_sub (X Y N : Nat) (hN : 0 < N) (hX : X < N) (hY : Y < N) :
    N - 1 - ((X + (N - 1 - Y)) % N) = (Y + N - X) % N := by
  by_cases h : X ≤ Y
  · rw [Nat.mod_eq_of_lt (show X + (N - 1 - Y) < N by omega),
      show Y + N - X = (Y - X) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X + (N - 1 - Y) = (X - 1 - Y) + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X - 1 - Y < N by omega), Nat.mod_eq_of_lt (show Y + N - X < N by omega)]
    omega

/-- x 保持，y 原地得到模 2^n 的差，进位链归零。 -/
theorem subInPlace_spec (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (X Y : Nat) :
    {{ x = X, y = Y, cin = false, carry = 0 }} subInPlace x y carry cin
    {{ x = X, y = ((Y + 2^y.length - X) % 2^y.length), cin = false, carry = 0 }} := by
  intro s m h
  have hX : X < 2^y.length := by
    have hh := regValue_lt x s.basis
    rw [show regValue x s.basis = X from h.1.1.1, hx] at hh
    exact hh
  have hY : Y < 2^y.length := by
    have hh := regValue_lt y s.basis
    rwa [show regValue y s.basis = Y from h.1.1.2] at hh
  have h1 := flip_y x y carry cin hnd X Y 0 false
  have h2 := addInPlace_spec x y carry cin hnd hx hc X (2^y.length - 1 - Y) false
  have h3 := flip_y x y carry cin hnd X ((X + (2^y.length - 1 - Y) + false.toNat) % 2^y.length) 0 false
  simp only [Bool.toNat_false, Nat.add_zero] at h2 h3
  rw [complement_sub X Y (2^y.length) (Nat.two_pow_pos _) hX hY] at h3
  have hall := h1.seq (h2.seq h3)
  rw [subInPlace, List.append_assoc]
  exact hall s m h

theorem addInPlace_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    toffoliCount (addInPlace x y carry cin) = y.length - 1 ∧
    measurementCount (addInPlace x y carry cin) = y.length - 1 := by
  induction y generalizing x carry cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    cases bs with
    | nil =>
      have hx0 : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hx)
      subst hx0
      simp [addInPlace, toffoliCount, measurementCount]
    | cons b' bs' =>
      cases as with
      | nil => simp at hx
      | cons a' as' =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
      have := ih (a' :: as') cs c (by simpa using hx) (by simpa using hc)
      simp only [addInPlace, toffoliCount_append, measurementCount_append, this.1, this.2,
        eraseCarry, majority, toffoliCount, measurementCount, List.length_cons]
      omega

theorem subInPlace_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    toffoliCount (subInPlace x y carry cin) = y.length - 1 ∧
    measurementCount (subInPlace x y carry cin) = y.length - 1 := by
  have h := addInPlace_counts x y carry cin hx hc
  simp only [subInPlace, toffoliCount_append, measurementCount_append,
    (notRegister_counts y).1, (notRegister_counts y).2, h.1, h.2, Nat.zero_add, Nat.add_zero, and_self]

/-- 非空寄存器时，程序恰好触及 cin、x、y 与进位链。 -/
theorem addInPlace_wires (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    wires (addInPlace x y carry cin) = (cin :: (x ++ y ++ carry)).toFinset := by
  induction y generalizing x carry cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
    cases bs with
    | nil =>
      have hx0 : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hx)
      have hc0 : carry = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst hx0 hc0
      ext w
      simp [addInPlace, wires, Instr.wires]
    | cons b' bs' =>
      cases as with
      | nil => simp at hx
      | cons a' as' =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
      have := ih (a' :: as') cs c (by simpa using hx) (by simpa using hc)
      have hm : wires (majority a b cin c) = {a, b, cin, c} := by
        ext w; simp [majority, wires, Instr.wires]; tauto
      simp only [addInPlace, wires_append, this, hm, eraseCarry_wires]
      ext w
      simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        List.mem_toFinset, List.mem_cons, List.mem_append, Finset.notMem_empty, or_false]
      tauto

theorem subInPlace_wires (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    wires (subInPlace x y carry cin) = (cin :: (x ++ y ++ carry)).toFinset := by
  rw [subInPlace, wires_append, wires_append, addInPlace_wires x y carry cin hx hc, notRegister_wires]
  ext w
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
  tauto

/-- n 位原地加减：n−1 个 Toffoli、n−1 次测量、3n 根线路。 -/
theorem addInPlace_resources (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) :
    toffoliCount (addInPlace x y carry cin) = y.length - 1 ∧
    measurementCount (addInPlace x y carry cin) = y.length - 1 ∧
    qubitCount (addInPlace x y carry cin) = 3 * y.length ∧
    toffoliCount (subInPlace x y carry cin) = y.length - 1 ∧
    measurementCount (subInPlace x y carry cin) = y.length - 1 ∧
    qubitCount (subInPlace x y carry cin) = 3 * y.length := by
  have ha := addInPlace_counts x y carry cin hx hc
  have hs := subInPlace_counts x y carry cin hx hc
  have hlen : (cin :: (x ++ y ++ carry)).length = 3 * y.length := by
    simp only [List.length_cons, List.length_append, hx]; omega
  refine ⟨ha.1, ha.2, ?_, hs.1, hs.2, ?_⟩
  · rw [qubitCount, addInPlace_wires x y carry cin hx hc, List.toFinset_card_of_nodup hnd, hlen]
  · rw [qubitCount, subInPlace_wires x y carry cin hx hc, List.toFinset_card_of_nodup hnd, hlen]


/-- 受控常数加：T 是零寄存器，受 c 控制装入 K，原地加到 y，再同样受控清 T；不增加 Toffoli。 -/
def maskedAddConst (c : Wire) (T y carry : List Wire) (cin : Wire) (K : Nat) : Program :=
  maskedConstant c T K ++ addInPlace T y carry cin ++ maskedConstant c T K

def maskedSubConst (c : Wire) (T y carry : List Wire) (cin : Wire) (K : Nat) : Program :=
  maskedConstant c T K ++ subInPlace T y carry cin ++ maskedConstant c T K

/-- 受控量子加数：t ← c·src（受控复制），原地加/减到 y，再清 t。 -/
def maskedAddInPlace (c : Wire) (src t y carry : List Wire) (cin : Wire) : Program :=
  copyRegister (some c) src t ++ addInPlace t y carry cin ++ copyRegister (some c) src t

def maskedSubInPlace (c : Wire) (src t y carry : List Wire) (cin : Wire) : Program :=
  copyRegister (some c) src t ++ subInPlace t y carry cin ++ copyRegister (some c) src t

private theorem masked_load (c cin : Wire) (T y carry : List Wire)
    (hnd : (c :: cin :: (T ++ y ++ carry)).Nodup) (K : Nat) (hK : K < 2^T.length)
    (C : Bool) (V Y : Nat) :
    {{ c = C, T = V, y = Y, cin = false, carry = 0 }} maskedConstant c T K
    {{ c = C, T = (V ^^^ (if C then K else 0)), y = Y, cin = false, carry = 0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hc := List.nodup_cons.mp hnd
  have hcin := List.nodup_cons.mp hc.2
  have hn2 := List.nodup_append'.mp (by simpa only [List.append_assoc] using hcin.2 : (T ++ (y ++ carry)).Nodup)
  have hcT : c ∉ T := fun hh => hc.1 (by simp [hh])
  have hcinT : cin ∉ T := fun hh => hcin.1 (by simp [hh])
  have hyT : ∀ w ∈ y, w ∉ T := fun w hw hT => List.disjoint_left.mp hn2.2.2 hT (List.mem_append_left _ hw)
  have hkT : ∀ w ∈ carry, w ∉ T := fun w hw hT => List.disjoint_left.mp hn2.2.2 hT (List.mem_append_right _ hw)
  obtain ⟨hp, he, hv⟩ := maskedConstant_correct c T K hn2.1 hcT hK s m
  refine ⟨hp, ⟨⟨⟨(he c hcT).trans h.1.1.1.1, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hv, h.1.1.1.2, h.1.1.1.1]
  · exact (regValue_congr _ _ _ (fun w hw => he w (hyT w hw))).trans h.1.1.2
  · exact (he cin hcinT).trans h.1.2
  · exact (regValue_congr _ _ _ (fun w hw => he w (hkT w hw))).trans h.2

private theorem masked_add (c cin : Wire) (T y carry : List Wire)
    (hnd : (c :: cin :: (T ++ y ++ carry)).Nodup) (hT : T.length = y.length)
    (hc : carry.length + 1 = y.length) (C : Bool) (V Y : Nat) :
    {{ c = C, T = V, y = Y, cin = false, carry = 0 }} addInPlace T y carry cin
    {{ c = C, T = V, y = ((Y + V) % 2^y.length), cin = false, carry = 0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hn := List.nodup_cons.mp hnd
  obtain ⟨hp, hpost⟩ := addInPlace_spec T y carry cin hn.2 hT hc V Y false s m
    ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩
  simp only [Holds.holds, Bool.toNat_false, Nat.add_zero, Nat.add_comm V Y] at hpost
  have hcw : c ∉ wires (addInPlace T y carry cin) := by
    rw [addInPlace_wires T y carry cin hT hc]
    exact fun hh => hn.1 (List.mem_toFinset.mp hh)
  exact ⟨hp, ⟨⟨⟨(run_preserves_outside _ m s c hcw).trans h.1.1.1.1, hpost.1.1.1⟩, hpost.1.1.2⟩,
    hpost.1.2⟩, hpost.2⟩

private theorem masked_sub (c cin : Wire) (T y carry : List Wire)
    (hnd : (c :: cin :: (T ++ y ++ carry)).Nodup) (hT : T.length = y.length)
    (hc : carry.length + 1 = y.length) (C : Bool) (V Y : Nat) :
    {{ c = C, T = V, y = Y, cin = false, carry = 0 }} subInPlace T y carry cin
    {{ c = C, T = V, y = ((Y + 2^y.length - V) % 2^y.length), cin = false, carry = 0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hn := List.nodup_cons.mp hnd
  obtain ⟨hp, hpost⟩ := subInPlace_spec T y carry cin hn.2 hT hc V Y s m
    ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩
  simp only [Holds.holds] at hpost
  have hcw : c ∉ wires (subInPlace T y carry cin) := by
    rw [subInPlace_wires T y carry cin hT hc]
    exact fun hh => hn.1 (List.mem_toFinset.mp hh)
  exact ⟨hp, ⟨⟨⟨(run_preserves_outside _ m s c hcw).trans h.1.1.1.1, hpost.1.1.1⟩, hpost.1.1.2⟩,
    hpost.1.2⟩, hpost.2⟩

/-- 控制为真时 y 加上常数 K，为假时不变；T 与进位链回零。 -/
theorem maskedAddConst_spec (c cin : Wire) (T y carry : List Wire)
    (hnd : (c :: cin :: (T ++ y ++ carry)).Nodup) (hT : T.length = y.length)
    (hc : carry.length + 1 = y.length) (K : Nat) (hK : K < 2^T.length) (C : Bool) (Y : Nat) :
    {{ c = C, T = 0, y = Y, cin = false, carry = 0 }} maskedAddConst c T y carry cin K
    {{ c = C, T = 0, y = ((Y + (if C then K else 0)) % 2^y.length), cin = false, carry = 0 }} := by
  have h1 := masked_load c cin T y carry hnd K hK C 0 Y
  have h2 := masked_add c cin T y carry hnd hT hc C (if C then K else 0) Y
  have h3 := masked_load c cin T y carry hnd K hK C (if C then K else 0)
    ((Y + (if C then K else 0)) % 2^y.length)
  simp only [Nat.zero_xor, Nat.xor_self] at h1 h3
  simpa only [maskedAddConst, List.append_assoc] using h1.seq (h2.seq h3)

/-- 控制为真时 y 减去常数 K，为假时不变；T 与进位链回零。 -/
theorem maskedSubConst_spec (c cin : Wire) (T y carry : List Wire)
    (hnd : (c :: cin :: (T ++ y ++ carry)).Nodup) (hT : T.length = y.length)
    (hc : carry.length + 1 = y.length) (K : Nat) (hK : K < 2^T.length) (C : Bool) (Y : Nat) :
    {{ c = C, T = 0, y = Y, cin = false, carry = 0 }} maskedSubConst c T y carry cin K
    {{ c = C, T = 0, y = ((Y + 2^y.length - (if C then K else 0)) % 2^y.length), cin = false, carry = 0 }} := by
  have h1 := masked_load c cin T y carry hnd K hK C 0 Y
  have h2 := masked_sub c cin T y carry hnd hT hc C (if C then K else 0) Y
  have h3 := masked_load c cin T y carry hnd K hK C (if C then K else 0)
    ((Y + 2^y.length - (if C then K else 0)) % 2^y.length)
  simp only [Nat.zero_xor, Nat.xor_self] at h1 h3
  simpa only [maskedSubConst, List.append_assoc] using h1.seq (h2.seq h3)

theorem maskedCopyWithFrame_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (hs : src.length = t.length)
    (C : Bool) (S V Y : Nat) :
    {{ c = C, src = S, t = V, y = Y, cin = false, carry = 0 }} copyRegister (some c) src t
    {{ c = C, src = S, t = (V ^^^ (if C then S else 0)), y = Y, cin = false, carry = 0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hcnt := List.nodup_iff_count.mp hnd
  have hst : (src ++ t).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have := hcnt w
    simp only [List.count_cons, List.count_append] at this ⊢; omega
  have hct : c ∉ t := fun hh => by
    have h1 := hcnt c; have h2 := List.count_pos_iff.mpr hh
    simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1; omega
  have hcint : cin ∉ t := fun hh => by
    have h1 := hcnt cin; have h2 := List.count_pos_iff.mpr hh
    simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1; omega
  have hyt : ∀ w ∈ y, w ∉ t := fun w hw hw' => by
    have h1 := hcnt w; have h2 := List.count_pos_iff.mpr hw; have h3 := List.count_pos_iff.mpr hw'
    simp only [List.count_cons, List.count_append] at h1; omega
  have hkt : ∀ w ∈ carry, w ∉ t := fun w hw hw' => by
    have h1 := hcnt w; have h2 := List.count_pos_iff.mpr hw; have h3 := List.count_pos_iff.mpr hw'
    simp only [List.count_cons, List.count_append] at h1; omega
  have hsrct : ∀ w ∈ src, w ∉ t := fun w hw hw' => List.disjoint_left.mp (List.nodup_append'.mp hst).2.2 hw hw'
  obtain ⟨hp, he, hv⟩ := copyRegister_correct (some c) src t hs hst (by simpa using hct) s m
  refine ⟨hp, ⟨⟨⟨⟨(he c hct).trans h.1.1.1.1.1,
    (regValue_congr _ _ _ (fun w hw => he w (hsrct w hw))).trans h.1.1.1.1.2⟩, ?_⟩,
    (regValue_congr _ _ _ (fun w hw => he w (hyt w hw))).trans h.1.1.2⟩,
    (he cin hcint).trans h.1.2⟩,
    (regValue_congr _ _ _ (fun w hw => he w (hkt w hw))).trans h.2⟩
  rw [hv]
  simp only [copyValue, h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2]

theorem addInPlaceWithSource_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (ht : t.length = y.length)
    (hc : carry.length + 1 = y.length) (C : Bool) (S V Y : Nat) :
    {{ c = C, src = S, t = V, y = Y, cin = false, carry = 0 }} addInPlace t y carry cin
    {{ c = C, src = S, t = V, y = ((Y + V) % 2^y.length), cin = false, carry = 0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hcnt := List.nodup_iff_count.mp hnd
  have hnd' : (cin :: (t ++ y ++ carry)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have := hcnt w
    simp only [List.count_cons, List.count_append] at this ⊢; omega
  obtain ⟨hp, hpost⟩ := addInPlace_spec t y carry cin hnd' ht hc V Y false s m
    ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩
  simp only [Holds.holds, Bool.toNat_false, Nat.add_zero, Nat.add_comm V Y] at hpost
  have hout : ∀ w, w = c ∨ w ∈ src → w ∉ wires (addInPlace t y carry cin) := by
    intro w hw
    rw [addInPlace_wires t y carry cin ht hc]
    intro hm
    have hm' := List.mem_toFinset.mp hm
    have h1 := hcnt w
    have h2 := List.count_pos_iff.mpr hm'
    rcases hw with rfl | hw
    · simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    · have h3 := List.count_pos_iff.mpr hw
      simp only [List.count_cons, List.count_append] at h1 h2; omega
  refine ⟨hp, ⟨⟨⟨⟨(run_preserves_outside _ m s c (hout c (Or.inl rfl))).trans h.1.1.1.1.1,
    (regValue_congr _ _ _ (fun w hw => run_preserves_outside _ m s w (hout w (Or.inr hw)))).trans h.1.1.1.1.2⟩,
    hpost.1.1.1⟩, hpost.1.1.2⟩, hpost.1.2⟩, hpost.2⟩

theorem subInPlaceWithSource_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (ht : t.length = y.length)
    (hc : carry.length + 1 = y.length) (C : Bool) (S V Y : Nat) :
    {{ c = C, src = S, t = V, y = Y, cin = false, carry = 0 }} subInPlace t y carry cin
    {{ c = C, src = S, t = V, y = ((Y + 2^y.length - V) % 2^y.length), cin = false, carry = 0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hcnt := List.nodup_iff_count.mp hnd
  have hnd' : (cin :: (t ++ y ++ carry)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have := hcnt w
    simp only [List.count_cons, List.count_append] at this ⊢; omega
  obtain ⟨hp, hpost⟩ := subInPlace_spec t y carry cin hnd' ht hc V Y s m
    ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩
  simp only [Holds.holds] at hpost
  have hout : ∀ w, w = c ∨ w ∈ src → w ∉ wires (subInPlace t y carry cin) := by
    intro w hw
    rw [subInPlace_wires t y carry cin ht hc]
    intro hm
    have hm' := List.mem_toFinset.mp hm
    have h1 := hcnt w
    have h2 := List.count_pos_iff.mpr hm'
    rcases hw with rfl | hw
    · simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    · have h3 := List.count_pos_iff.mpr hw
      simp only [List.count_cons, List.count_append] at h1 h2; omega
  refine ⟨hp, ⟨⟨⟨⟨(run_preserves_outside _ m s c (hout c (Or.inl rfl))).trans h.1.1.1.1.1,
    (regValue_congr _ _ _ (fun w hw => run_preserves_outside _ m s w (hout w (Or.inr hw)))).trans h.1.1.1.1.2⟩,
    hpost.1.1.1⟩, hpost.1.1.2⟩, hpost.1.2⟩, hpost.2⟩

/-- 控制为真时 y 加上寄存器 src 的值，为假时不变；临时字 t 与进位链回零，src 保持。 -/
theorem maskedAddInPlace_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (hs : src.length = t.length)
    (ht : t.length = y.length) (hc : carry.length + 1 = y.length) (C : Bool) (S Y : Nat) :
    {{ c = C, src = S, t = 0, y = Y, cin = false, carry = 0 }} maskedAddInPlace c src t y carry cin
    {{ c = C, src = S, t = 0, y = ((Y + (if C then S else 0)) % 2^y.length), cin = false, carry = 0 }} := by
  have h1 := maskedCopyWithFrame_spec c cin src t y carry hnd hs C S 0 Y
  have h2 := addInPlaceWithSource_spec c cin src t y carry hnd ht hc C S (if C then S else 0) Y
  have h3 := maskedCopyWithFrame_spec c cin src t y carry hnd hs C S (if C then S else 0)
    ((Y + (if C then S else 0)) % 2^y.length)
  simp only [Nat.zero_xor, Nat.xor_self] at h1 h3
  simpa only [maskedAddInPlace, List.append_assoc] using h1.seq (h2.seq h3)

/-- 控制为真时 y 减去寄存器 src 的值，为假时不变。 -/
theorem maskedSubInPlace_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c :: cin :: (src ++ t ++ y ++ carry)).Nodup) (hs : src.length = t.length)
    (ht : t.length = y.length) (hc : carry.length + 1 = y.length) (C : Bool) (S Y : Nat) :
    {{ c = C, src = S, t = 0, y = Y, cin = false, carry = 0 }} maskedSubInPlace c src t y carry cin
    {{ c = C, src = S, t = 0, y = ((Y + 2^y.length - (if C then S else 0)) % 2^y.length), cin = false, carry = 0 }} := by
  have h1 := maskedCopyWithFrame_spec c cin src t y carry hnd hs C S 0 Y
  have h2 := subInPlaceWithSource_spec c cin src t y carry hnd ht hc C S (if C then S else 0) Y
  have h3 := maskedCopyWithFrame_spec c cin src t y carry hnd hs C S (if C then S else 0)
    ((Y + 2^y.length - (if C then S else 0)) % 2^y.length)
  simp only [Nat.zero_xor, Nat.xor_self] at h1 h3
  simpa only [maskedSubInPlace, List.append_assoc] using h1.seq (h2.seq h3)


/-- 两次受控复制与一次原地加减的字面门数。 -/
theorem maskedInPlace_counts (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hs : src.length = t.length) (ht : t.length = y.length)
    (hc : carry.length + 1 = y.length) :
    (toffoliCount (maskedAddInPlace c src t y carry cin) = 3*y.length-1 ∧
      measurementCount (maskedAddInPlace c src t y carry cin) = y.length-1) ∧
    (toffoliCount (maskedSubInPlace c src t y carry cin) = 3*y.length-1 ∧
      measurementCount (maskedSubInPlace c src t y carry cin) = y.length-1) := by
  have cp := copyRegister_counts (some c) src t hs
  have ap := addInPlace_counts t y carry cin ht hc
  have sp := subInPlace_counts t y carry cin ht hc
  simp only [maskedAddInPlace,maskedSubInPlace,toffoliCount_append,measurementCount_append,
    cp.1,cp.2,ap.1,ap.2,sp.1,sp.2,Option.isSome_some,if_true]
  omega

/-- 非空目标保证受控复制确实触及控制位；支持不包含任何额外out寄存器。 -/
theorem maskedInPlace_wires (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hs : src.length = t.length) (ht : t.length = y.length)
    (hc : carry.length + 1 = y.length) :
    wires (maskedAddInPlace c src t y carry cin) = (c::cin::(src++t++y++carry)).toFinset ∧
    wires (maskedSubInPlace c src t y carry cin) = (c::cin::(src++t++y++carry)).toFinset := by
  have hn : src ≠ [] := by intro h; simp [h] at hs; omega
  have cp := copyRegister_wires (some c) src t hs
  simp only [List.isEmpty_iff,hn,if_false,Option.toList_some,List.cons_append,List.nil_append] at cp
  constructor
  · rw [maskedAddInPlace,wires_append,wires_append,cp,addInPlace_wires t y carry cin ht hc]
    ext w
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  · rw [maskedSubInPlace,wires_append,wires_append,cp,subInPlace_wires t y carry cin ht hc]
    ext w
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto

/-- 受控加减只触及控制位、cin、常数字/临时字、目标与进位链。 -/
theorem maskedConst_wires_subset (c : Wire) (T y carry : List Wire) (cin : Wire) (K : Nat)
    (hT : T.length = y.length) (hc : carry.length + 1 = y.length) :
    wires (maskedAddConst c T y carry cin K) ⊆ (c :: cin :: (T ++ y ++ carry)).toFinset ∧
    wires (maskedSubConst c T y carry cin K) ⊆ (c :: cin :: (T ++ y ++ carry)).toFinset := by
  have hm : wires (maskedConstant c T K) ⊆ (c :: cin :: (T ++ y ++ carry)).toFinset := by
    intro w hw
    have := List.mem_toFinset.mp (maskedConstant_wires_subset c T K hw)
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at this ⊢; tauto
  have ha : wires (addInPlace T y carry cin) ⊆ (c :: cin :: (T ++ y ++ carry)).toFinset := by
    rw [addInPlace_wires T y carry cin hT hc]
    intro w hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hw ⊢; tauto
  have hs : wires (subInPlace T y carry cin) ⊆ (c :: cin :: (T ++ y ++ carry)).toFinset := by
    rw [subInPlace_wires T y carry cin hT hc]
    intro w hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hw ⊢; tauto
  constructor
  · simp only [maskedAddConst, wires_append]
    exact Finset.union_subset (Finset.union_subset hm ha) hm
  · simp only [maskedSubConst, wires_append]
    exact Finset.union_subset (Finset.union_subset hm hs) hm

theorem maskedInPlace_wires_subset (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hs : src.length = t.length) (ht : t.length = y.length) (hc : carry.length + 1 = y.length) :
    wires (maskedAddInPlace c src t y carry cin) ⊆ (c :: cin :: (src ++ t ++ y ++ carry)).toFinset ∧
    wires (maskedSubInPlace c src t y carry cin) ⊆ (c :: cin :: (src ++ t ++ y ++ carry)).toFinset := by
  have hcopy : wires (copyRegister (some c) src t) ⊆ (c :: cin :: (src ++ t ++ y ++ carry)).toFinset := by
    rw [copyRegister_wires (some c) src t hs]
    split_ifs
    · exact Finset.empty_subset _
    · intro w hw
      simp only [Option.toList_some, List.mem_toFinset, List.mem_cons, List.mem_append,
        List.cons_append, List.nil_append] at hw ⊢; tauto
  have ha : wires (addInPlace t y carry cin) ⊆ (c :: cin :: (src ++ t ++ y ++ carry)).toFinset := by
    rw [addInPlace_wires t y carry cin ht hc]
    intro w hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hw ⊢; tauto
  have hsu : wires (subInPlace t y carry cin) ⊆ (c :: cin :: (src ++ t ++ y ++ carry)).toFinset := by
    rw [subInPlace_wires t y carry cin ht hc]
    intro w hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hw ⊢; tauto
  constructor
  · simp only [maskedAddInPlace, wires_append]
    exact Finset.union_subset (Finset.union_subset hcopy ha) hcopy
  · simp only [maskedSubInPlace, wires_append]
    exact Finset.union_subset (Finset.union_subset hcopy hsu) hcopy

end ECDSAAdd.Arithmetic
