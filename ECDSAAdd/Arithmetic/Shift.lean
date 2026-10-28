import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- Fredkin 门分解为两次 CX 与一次 CCX；控制与两个目标必须互异。 -/
def cswap (c a b : Wire) : Program := [.CX b a, .CCX c a b, .CX b a]

theorem cswap_correct (c a b : Wire) (hnd : [c,a,b].Nodup) (s : State) (m : List Bool) :
    (run (cswap c a b) m s).phase = s.phase ∧
    (∀ w, w ≠ a → w ≠ b → (run (cswap c a b) m s).basis w = s.basis w) ∧
    (run (cswap c a b) m s).basis a = (if s.basis c then s.basis b else s.basis a) ∧
    (run (cswap c a b) m s).basis b = (if s.basis c then s.basis a else s.basis b) := by
  have hn : c ≠ a ∧ c ≠ b ∧ a ≠ b := by simpa [and_assoc] using hnd
  obtain ⟨hca, hcb, hab⟩ := hn
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro w ha hb
    simp [cswap, run, writeBit, ha, hb]
  all_goals cases hc : s.basis c <;> cases ha : s.basis a <;> cases hb : s.basis b <;>
    simp [cswap, run, writeBit, hca, hab, Ne.symm hab, hc, ha, hb]

theorem cswap_spec (c a b : Wire) (hnd : [c,a,b].Nodup) (C A B : Bool) :
    {{ c=C, a=A, b=B }} cswap c a b
    {{ c=C, a=(if C then B else A), b=(if C then A else B) }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hp, he, ha, hb⟩ := cswap_correct c a b hnd s m
  have hn : c ≠ a ∧ c ≠ b ∧ a ≠ b := by simpa [and_assoc] using hnd
  exact ⟨hp, ⟨(he c hn.1 hn.2.1).trans h.1.1, by simpa only [h.1.1, h.1.2, h.2] using ha⟩,
    by simpa only [h.1.1, h.1.2, h.2] using hb⟩

theorem cswap_twice (c a b : Wire) (hnd : [c,a,b].Nodup) (s : State) (m : List Bool) :
    run (cswap c a b) m (run (cswap c a b) m s) = s := by
  obtain ⟨p1, e1, a1, b1⟩ := cswap_correct c a b hnd s m
  obtain ⟨p2, e2, a2, b2⟩ := cswap_correct c a b hnd (run (cswap c a b) m s) m
  have hn : c ≠ a ∧ c ≠ b ∧ a ≠ b := by simpa [and_assoc] using hnd
  have hc := e1 c hn.1 hn.2.1
  apply congrArg₂ State.mk
  · exact p2.trans p1
  · funext w
    change (run (cswap c a b) m (run (cswap c a b) m s)).basis w = s.basis w
    by_cases ha : w=a
    · subst w; rw [a2, hc, a1, b1]; cases s.basis c <;> rfl
    by_cases hb : w=b
    · subst w; rw [b2, hc, a1, b1]; cases s.basis c <;> rfl
    · exact (e2 w ha hb).trans (e1 w ha hb)

/-- 右移网络实际是循环移位；规格中的偶数前提保证移出的最低位为零。 -/
def shiftRight (c : Wire) : List Wire → Program
  | a::b::bs => cswap c a b ++ shiftRight c (b::bs)
  | _ => []

/-- 左移按相反顺序执行同一组 CSWAP；只重排无测量交换门。 -/
def shiftLeft (c : Wire) : List Wire → Program
  | a::b::bs => shiftLeft c (b::bs) ++ cswap c a b
  | _ => []

theorem shift_counts (c : Wire) (r : List Wire) :
    toffoliCount (shiftRight c r) = r.length-1 ∧ measurementCount (shiftRight c r) = 0 ∧
    toffoliCount (shiftLeft c r) = r.length-1 ∧ measurementCount (shiftLeft c r) = 0 := by
  induction r with
  | nil => simp [shiftRight, shiftLeft, toffoliCount, measurementCount]
  | cons a r ih =>
    cases r with
    | nil => simp [shiftRight, shiftLeft, toffoliCount, measurementCount]
    | cons b bs => simp [shiftRight, shiftLeft, toffoliCount_append, measurementCount_append,
        cswap, toffoliCount, measurementCount, ih]; omega

theorem shift_frame (c : Wire) (r : List Wire) (s : State) (m : List Bool) :
    (run (shiftRight c r) m s).phase = s.phase ∧
    (∀ w, w ∉ r → (run (shiftRight c r) m s).basis w = s.basis w) ∧
    (run (shiftLeft c r) m s).phase = s.phase ∧
    (∀ w, w ∉ r → (run (shiftLeft c r) m s).basis w = s.basis w) := by
  induction r generalizing s with
  | nil => simp [shiftRight, shiftLeft, run]
  | cons a r ih =>
    cases r with
    | nil => simp [shiftRight, shiftLeft, run]
    | cons b bs =>
      have hc : measurementCount (cswap c a b) = 0 := rfl
      simp only [shiftRight, shiftLeft]
      rw [run_append, run_append, run_take, run_take, hc, (shift_counts c (b::bs)).2.2.2, List.drop_zero]
      have hR := ih (run (cswap c a b) m s)
      have hL := ih s
      refine ⟨hR.1, ?_, hL.2.2.1, ?_⟩
      · intro w hw
        have hn : w ≠ a ∧ w ≠ b ∧ w ∉ bs := by simpa only [List.mem_cons, not_or] using hw
        rw [hR.2.1 w (by simp [hn.2.1, hn.2.2])]
        simp [cswap, run, writeBit, hn.1, hn.2.1]
      · intro w hw
        have hn : w ≠ a ∧ w ≠ b ∧ w ∉ bs := by simpa only [List.mem_cons, not_or] using hw
        simpa [cswap, run, writeBit, hn.1, hn.2.1] using hL.2.2.2 w (by simp [hn.2.1, hn.2.2])

/-- 非空寄存器的完整循环右移值公式，包含被移到最高位的原最低位。 -/
theorem shiftRight_value (c a : Wire) (bs : List Wire) (hnd : (c::a::bs).Nodup)
    (s : State) (m : List Bool) :
    regValue (a::bs) (run (shiftRight c (a::bs)) m s).basis =
      if s.basis c then regValue bs s.basis + 2^bs.length*(s.basis a).toNat
      else regValue (a::bs) s.basis := by
  induction bs generalizing a s with
  | nil => cases s.basis c <;> simp [shiftRight, run, regValue, Bool.toNat]
  | cons b bs ih =>
    have hab : a ≠ b := by have h := hnd; simp at h; tauto
    have ha : a ∉ b::bs := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    have htail : (c::b::bs).Nodup := List.nodup_cons.mpr
      ⟨fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ h),
        (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2⟩
    have hgate : [c,a,b].Nodup := by
      have h := hnd
      simp only [List.nodup_cons, List.mem_cons, not_or] at h
      simp [h.1.1, h.1.2.1, hab]
    let s1 := run (cswap c a b) m s
    have hv := ih b htail s1
    obtain ⟨_, he, hA, hB⟩ := cswap_correct c a b hgate s m
    have hca : c ≠ a := by have h := (List.nodup_cons.mp hnd).1; simp only [List.mem_cons, not_or] at h; exact h.1
    have hcb : c ≠ b := by have h := (List.nodup_cons.mp htail).1; simp only [List.mem_cons, not_or] at h; exact h.1
    have hc : s1.basis c = s.basis c := he c hca hcb
    have hbs : regValue bs s1.basis = regValue bs s.basis := regValue_congr _ _ _ (by
      intro w hw
      apply he w
      · intro h; subst w; exact ha (List.mem_cons_of_mem _ hw)
      · intro h; subst w; exact (List.nodup_cons.mp (List.nodup_cons.mp htail).2).1 hw)
    have hkeep := (shift_frame c (b::bs) s1 m).2.1 a ha
    change regValue (a::b::bs) (run (cswap c a b ++ shiftRight c (b::bs)) m s).basis = _
    rw [run_append, run_take]
    change (if (run (shiftRight c (b::bs)) m s1).basis a then 1 else 0) +
      2*regValue (b::bs) (run (shiftRight c (b::bs)) m s1).basis = _
    rw [hkeep, hv, hc, hbs]
    have hbval : regValue (b::bs) s1.basis = (s1.basis b).toNat + 2*regValue bs s.basis := by
      simp only [regValue, List.foldr_cons, Bool.toNat, Bool.cond_eq_ite] at hbs ⊢
      rw [hbs]
    rw [hbval, hA, hB]
    cases hc' : s.basis c <;> cases ha' : s.basis a <;>
      simp [ha', regValue, Bool.toNat, Bool.cond_eq_ite, pow_succ]
    all_goals ring

/-- 左右网络互为逆；交换门无测量，所以不涉及测量程序的逆序执行。 -/
theorem shiftRight_left_cancel (c : Wire) (r : List Wire) (hnd : (c::r).Nodup)
    (s : State) (m : List Bool) : run (shiftRight c r) m (run (shiftLeft c r) m s) = s := by
  induction r generalizing s with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b bs =>
      have ht : (c::b::bs).Nodup := List.nodup_cons.mpr
        ⟨fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ h),
          (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2⟩
      have hg : [c,a,b].Nodup := by
        have h := hnd
        simp only [List.nodup_cons, List.mem_cons, not_or] at h
        simp [h.1.1, h.1.2.1, h.2.1.1]
      change run (cswap c a b ++ shiftRight c (b::bs)) m
        (run (shiftLeft c (b::bs) ++ cswap c a b) m s) = s
      rw [run_append, run_take, run_append, run_take, (shift_counts c (b::bs)).2.2.2,
        show measurementCount (cswap c a b) = 0 from rfl, List.drop_zero]
      rw [cswap_twice c a b hg]
      exact ih ht s

/-- 若活动控制下输入为偶数，循环右移就是精确除以二。 -/
theorem shiftRight_spec (c : Wire) (r : List Wire) (hnd : (c::r).Nodup)
    (C : Bool) (X : Nat) (heven : C = true → X%2 = 0) :
    {{ c=C, r=X }} shiftRight c r {{ c=C, r=(if C then X/2 else X) }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hf := shift_frame c r s m
  refine ⟨hf.1, (hf.2.1 c (List.nodup_cons.mp hnd).1).trans h.1, ?_⟩
  cases r with
  | nil => have hx : X=0 := h.2.symm; subst X; cases C <;> rfl
  | cons a bs =>
    have hv := shiftRight_value c a bs hnd s m
    rw [h.1] at hv
    cases hC : C with
    | false => simpa only [hC, Bool.false_eq_true, if_false, h.2] using hv
    | true =>
      have hx : (s.basis a).toNat + 2*regValue bs s.basis = X := by
        simpa only [regValue, List.foldr_cons, Bool.toNat, Bool.cond_eq_ite] using h.2
      have he := heven hC
      rw [hC] at hv
      cases ha : s.basis a <;> simp [ha, Bool.toNat] at hx hv <;>
        simp only [if_true] <;> omega

/-- 左移要求活动控制下 2X 仍能放入原寄存器，不静默截断最高位。 -/
theorem shiftLeft_spec (c : Wire) (r : List Wire) (hnd : (c::r).Nodup)
    (C : Bool) (X : Nat) (hfit : C = true → 2*X < 2^r.length) :
    {{ c=C, r=X }} shiftLeft c r {{ c=C, r=(if C then 2*X else X) }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hf := shift_frame c r s m
  let t := run (shiftLeft c r) m s
  have hc : t.basis c = C := (hf.2.2.2 c (List.nodup_cons.mp hnd).1).trans h.1
  have hcancel := shiftRight_left_cancel c r hnd s m
  refine ⟨hf.2.2.1, hc, ?_⟩
  cases r with
  | nil => have hx : X=0 := h.2.symm; subst X; cases C <;> rfl
  | cons a bs =>
    have hv := shiftRight_value c a bs hnd t m
    rw [hcancel, hc, h.2] at hv
    cases hC : C with
    | false => simpa only [hC, Bool.false_eq_true, if_false] using hv.symm
    | true =>
      have hb := hfit hC
      rw [hC] at hv
      simp only [List.length_cons, pow_succ] at hb
      change regValue (a::bs) t.basis = _
      change (if t.basis a then 1 else 0) + 2*regValue bs t.basis = _
      cases ha : t.basis a <;> simp [ha, Bool.toNat] at hv ⊢ <;> omega

theorem shift_wires (c : Wire) (r : List Wire) :
    wires (shiftRight c r) = (if r.length<2 then ∅ else (c::r).toFinset) ∧
    wires (shiftLeft c r) = (if r.length<2 then ∅ else (c::r).toFinset) := by
  induction r with
  | nil => simp [shiftRight, shiftLeft, wires]
  | cons a r ih =>
    cases r with
    | nil => simp [shiftRight, shiftLeft, wires]
    | cons b bs =>
      change wires (cswap c a b ++ shiftRight c (b::bs)) = _ ∧
        wires (shiftLeft c (b::bs) ++ cswap c a b) = _
      simp only [wires_append, ih.1, ih.2]
      cases bs with
      | nil => simp [cswap, wires, Instr.wires, Finset.union_comm]
      | cons d ds =>
        simp only [show ¬(b::d::ds).length<2 by simp,
          show ¬(a::b::d::ds).length<2 by simp, if_false]
        constructor <;> ext w <;> simp [cswap, wires, Instr.wires] <;> tauto

theorem shift_resources (c : Wire) (r : List Wire) (hnd : (c::r).Nodup) :
    toffoliCount (shiftRight c r) = r.length-1 ∧ measurementCount (shiftRight c r) = 0 ∧
    qubitCount (shiftRight c r) = (if r.length<2 then 0 else r.length+1) ∧
    toffoliCount (shiftLeft c r) = r.length-1 ∧ measurementCount (shiftLeft c r) = 0 ∧
    qubitCount (shiftLeft c r) = (if r.length<2 then 0 else r.length+1) := by
  have h := shift_counts c r
  refine ⟨h.1, h.2.1, ?_, h.2.2.1, h.2.2.2, ?_⟩
  all_goals rw [qubitCount]
  · rw [(shift_wires c r).1]
    split_ifs
    · rfl
    · rw [List.toFinset_card_of_nodup hnd]; rfl
  · rw [(shift_wires c r).2]
    split_ifs
    · rfl
    · rw [List.toFinset_card_of_nodup hnd]; rfl

theorem cswap_resources (c a b : Wire) (hnd : [c,a,b].Nodup) :
    toffoliCount (cswap c a b) = 1 ∧ measurementCount (cswap c a b) = 0 ∧
    qubitCount (cswap c a b) = 3 := by
  refine ⟨rfl, rfl, ?_⟩
  have hw : wires (cswap c a b) = [c,a,b].toFinset := by
    ext w; simp [cswap, wires, Instr.wires]; tauto
  rw [qubitCount, hw, List.toFinset_card_of_nodup hnd]
  rfl

end ECDSAAdd.Arithmetic
