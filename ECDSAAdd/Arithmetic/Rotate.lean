import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- 无控制物理交换：三个 CX，不消耗 Toffoli 或测量。 -/
def swapBits (a b : Wire) : Program := [.CX b a,.CX a b,.CX b a]

private theorem swapBits_correct (a b : Wire) (hab : a≠b) (s : State) (m : List Bool) :
    (run (swapBits a b) m s).phase=s.phase ∧
    (∀ q, q≠a → q≠b → (run (swapBits a b) m s).basis q=s.basis q) ∧
    (run (swapBits a b) m s).basis a=s.basis b ∧
    (run (swapBits a b) m s).basis b=s.basis a := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro q ha hb; simp [swapBits,run,writeBit,ha,hb]
  all_goals cases ha : s.basis a <;> cases hb : s.basis b <;>
    simp [swapBits,run,writeBit,hab,Ne.symm hab,ha,hb]

private theorem swapBits_twice (a b : Wire) (hab : a≠b) (s : State) (m : List Bool) :
    run (swapBits a b) m (run (swapBits a b) m s)=s := by
  obtain ⟨p1,e1,a1,b1⟩ := swapBits_correct a b hab s m
  obtain ⟨p2,e2,a2,b2⟩ := swapBits_correct a b hab (run (swapBits a b) m s) m
  apply congrArg₂ State.mk
  · exact p2.trans p1
  · funext q
    by_cases ha : q=a
    · subst q; exact a2.trans b1
    by_cases hb : q=b
    · subst q; exact b2.trans a1
    exact (e2 q ha hb).trans (e1 q ha hb)

/-- 小端寄存器右旋：原最低位经相邻交换移动到最高位。 -/
def rotateRight : List Wire → Program
  | a::b::bs => swapBits a b ++ rotateRight (b::bs)
  | _ => []

/-- 左旋按逆序执行无测量的相邻交换；固定物理寄存器不换视图。 -/
def rotateLeft : List Wire → Program
  | a::b::bs => rotateLeft (b::bs) ++ swapBits a b
  | _ => []

theorem rotate_counts (r : List Wire) :
    toffoliCount (rotateRight r)=0 ∧ measurementCount (rotateRight r)=0 ∧
    toffoliCount (rotateLeft r)=0 ∧ measurementCount (rotateLeft r)=0 := by
  induction r with
  | nil => simp [rotateRight,rotateLeft,toffoliCount,measurementCount]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,toffoliCount,measurementCount]
    | cons b bs => simp [rotateRight,rotateLeft,toffoliCount_append,measurementCount_append,
        swapBits,toffoliCount,measurementCount,ih]

theorem rotate_frame (r : List Wire) (s : State) (m : List Bool) :
    (run (rotateRight r) m s).phase=s.phase ∧
    (∀ q, q∉r → (run (rotateRight r) m s).basis q=s.basis q) ∧
    (run (rotateLeft r) m s).phase=s.phase ∧
    (∀ q, q∉r → (run (rotateLeft r) m s).basis q=s.basis q) := by
  induction r generalizing s with
  | nil => simp [rotateRight,rotateLeft,run]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,run]
    | cons b bs =>
      simp only [rotateRight,rotateLeft]
      rw [run_append,run_append,run_take,run_take,
        show measurementCount (swapBits a b)=0 from rfl,(rotate_counts (b::bs)).2.2.2,List.drop_zero]
      have hR := ih (run (swapBits a b) m s)
      have hL := ih s
      refine ⟨hR.1,?_,hL.2.2.1,?_⟩
      · intro q hq
        have hn : q≠a ∧ q≠b ∧ q∉bs := by simpa only [List.mem_cons,not_or] using hq
        rw [hR.2.1 q (by simp [hn.2.1,hn.2.2])]
        simp [swapBits,run,writeBit,hn.1,hn.2.1]
      · intro q hq
        have hn : q≠a ∧ q≠b ∧ q∉bs := by simpa only [List.mem_cons,not_or] using hq
        simpa [swapBits,run,writeBit,hn.1,hn.2.1] using hL.2.2.2 q (by simp [hn.2.1,hn.2.2])

private theorem rotateRight_value (a : Wire) (bs : List Wire) (hnd : (a::bs).Nodup)
    (s : State) (m : List Bool) :
    regValue (a::bs) (run (rotateRight (a::bs)) m s).basis=
      regValue bs s.basis+2^bs.length*(s.basis a).toNat := by
  induction bs generalizing a s with
  | nil => simp [rotateRight,run,regValue,Bool.toNat]
  | cons b bs ih =>
    have ha := (List.nodup_cons.mp hnd).1
    have ht := (List.nodup_cons.mp hnd).2
    have hab : a≠b := fun hh => ha (by simp [hh])
    let s1 := run (swapBits a b) m s
    have hv := ih b ht s1
    obtain ⟨_,he,hA,hB⟩ := swapBits_correct a b hab s m
    have hbs : regValue bs s1.basis=regValue bs s.basis := regValue_congr _ _ _ (by
      intro q hq
      apply he q
      · intro hh; subst q; exact ha (List.mem_cons_of_mem _ hq)
      · intro hh; subst q; exact (List.nodup_cons.mp ht).1 hq)
    have hk := (rotate_frame (b::bs) s1 m).2.1 a ha
    change regValue (a::b::bs) (run (swapBits a b ++ rotateRight (b::bs)) m s).basis=_
    rw [run_append,run_take]
    change (if (run (rotateRight (b::bs)) m s1).basis a then 1 else 0)+
      2*regValue (b::bs) (run (rotateRight (b::bs)) m s1).basis=_
    rw [hk,hv,hbs,hA,hB]
    simp only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,List.length_cons,pow_succ]
    ring

/-- 仅无测量的旋转互逆，不用于反转算术测量门列。 -/
theorem rotateRight_left_cancel (r : List Wire) (hnd : r.Nodup) (s : State) (m : List Bool) :
    run (rotateRight r) m (run (rotateLeft r) m s)=s := by
  induction r generalizing s with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b bs =>
      have ht := (List.nodup_cons.mp hnd).2
      have hab : a≠b := fun hh => (List.nodup_cons.mp hnd).1 (by simp [hh])
      change run (swapBits a b ++ rotateRight (b::bs)) m
        (run (rotateLeft (b::bs) ++ swapBits a b) m s)=s
      rw [run_append,run_take,run_append,run_take,(rotate_counts (b::bs)).2.2.2,
        show measurementCount (swapBits a b)=0 from rfl,List.drop_zero,swapBits_twice a b hab]
      exact ih ht s

/-- 输入为偶数时，右旋恰好除以二，移入最高位为零。 -/
theorem rotateRight_spec (r : List Wire) (hnd : r.Nodup) (X : Nat) (heven : X%2=0) :
    {{ r=X }} rotateRight r {{ r=(X/2) }} := by
  intro s m h
  refine ⟨(rotate_frame r s m).1,?_⟩
  cases r with
  | nil =>
    change 0=X at h
    change 0=X/2
    omega
  | cons a bs =>
    have hv := rotateRight_value a bs hnd s m
    have hx : (s.basis a).toNat+2*regValue bs s.basis=X := by
      simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite] using h
    change regValue (a::bs) _=X/2
    cases ha : s.basis a <;> simp [ha,Bool.toNat] at hx hv <;> omega

/-- 无溢出时，左旋恰好乘二。 -/
theorem rotateLeft_spec (r : List Wire) (hnd : r.Nodup) (X : Nat) (hfit : 2*X<2^r.length) :
    {{ r=X }} rotateLeft r {{ r=(2*X) }} := by
  intro s m h
  let t := run (rotateLeft r) m s
  have hcancel := rotateRight_left_cancel r hnd s m
  refine ⟨(rotate_frame r s m).2.2.1,?_⟩
  cases r with
  | nil =>
    change 0=X at h
    change 0=2*X
    omega
  | cons a bs =>
    have hv := rotateRight_value a bs hnd t m
    rw [hcancel,h] at hv
    simp only [List.length_cons,pow_succ] at hfit
    change regValue (a::bs) t.basis=_
    change (if t.basis a then 1 else 0)+2*regValue bs t.basis=_
    cases ha : t.basis a <;> simp [ha,Bool.toNat] at hv ⊢ <;> omega

theorem rotate_wires (r : List Wire) :
    wires (rotateRight r)=(if r.length<2 then ∅ else r.toFinset) ∧
    wires (rotateLeft r)=(if r.length<2 then ∅ else r.toFinset) := by
  induction r with
  | nil => simp [rotateRight,rotateLeft,wires]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,wires]
    | cons b bs =>
      simp only [rotateRight,rotateLeft,wires_append,ih.1,ih.2]
      cases bs with
      | nil => simp [swapBits,wires,Instr.wires,Finset.union_comm]
      | cons d ds =>
        simp only [show ¬(b::d::ds).length<2 by simp,show ¬(a::b::d::ds).length<2 by simp,if_false]
        constructor <;> ext q <;> simp [swapBits,wires,Instr.wires] <;> tauto

end ECDSAAdd.Arithmetic
