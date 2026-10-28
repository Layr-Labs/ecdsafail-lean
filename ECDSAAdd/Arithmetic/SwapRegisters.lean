import ECDSAAdd.Arithmetic.Copy

namespace ECDSAAdd.Arithmetic

/-- 向量形式 Fredkin 分解；每对位使用两次 CX 和一次 CCX。 -/
def swapRegisters (c : Wire) (a b : List Wire) : Program :=
  copyRegister none b a ++ copyRegister (some c) a b ++ copyRegister none b a

private theorem copy_back (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (c::(a++b)).Nodup) (C : Bool) (A B : Nat) :
    {{ c=C, a=A, b=B }} copyRegister none b a {{ c=C, a=(A ^^^ B), b=B }} := by
  intro s m h
  have hh := List.nodup_cons.mp hnd
  have hc : c ∉ a := fun h => hh.1 (List.mem_append_left _ h)
  have hba : (b++a).Nodup := by simpa only [List.nodup_append_comm] using hh.2
  have hb := (List.nodup_append'.mp hba).2.2
  obtain ⟨hp, he, hv⟩ := copyRegister_correct none b a hlen.symm hba (by simp) s m
  refine ⟨hp, ⟨(he c hc).trans h.1.1, ?_⟩, ?_⟩
  · simpa only [copyValue, show regValue a s.basis=A from h.1.2,
      show regValue b s.basis=B from h.2] using hv
  · exact (regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp hb hw))).trans h.2

/-- 寄存器长度相同且全部互异；控制为真时交换，否则保持两者。 -/
theorem swapRegisters_spec (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (c::(a++b)).Nodup) (C : Bool) (A B : Nat) :
    {{ c=C, a=A, b=B }} swapRegisters c a b
    {{ c=C, a=(if C then B else A), b=(if C then A else B) }} := by
  have h1 := copy_back c a b hlen hnd C A B
  have h2 := maskedCopy_spec c a b hlen hnd C (A ^^^ B) B
  have h3 := copy_back c a b hlen hnd C (A ^^^ B) (B ^^^ (if C then A ^^^ B else 0))
  have h := h1.seq (h2.seq h3)
  have he : B ^^^ (if C then A ^^^ B else 0) = if C then A else B := by
    cases C <;> simp [Nat.xor_left_comm]
  have hf : (A ^^^ B) ^^^ (B ^^^ (if C then A ^^^ B else 0)) = if C then B else A := by
    rw [he]
    cases C <;> simp [Nat.xor_right_comm]
  rw [hf] at h
  simpa only [swapRegisters, List.append_assoc, he] using h

theorem swapRegisters_resources (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (c::(a++b)).Nodup) :
    toffoliCount (swapRegisters c a b) = a.length ∧
    measurementCount (swapRegisters c a b) = 0 ∧
    qubitCount (swapRegisters c a b) = (if a.isEmpty then 0 else 2*a.length+1) := by
  have h1 := copyRegister_counts none b a hlen.symm
  have h2 := copyRegister_counts (some c) a b hlen
  have hwa := copyRegister_wires (some c) a b hlen
  have hwb := copyRegister_wires none b a hlen.symm
  have he : b.isEmpty = a.isEmpty := by
    cases a <;> cases b <;> simp_all
  refine ⟨by simp [swapRegisters, toffoliCount_append, h1.1, h2.1],
    by simp [swapRegisters, measurementCount_append, h1.2, h2.2], ?_⟩
  rw [qubitCount, swapRegisters, wires_append, wires_append, hwa, hwb, he]
  split_ifs
  · simp
  · have hw : (none.toList ++ b ++ a).toFinset ∪ ((some c).toList ++ a ++ b).toFinset ∪
        (none.toList ++ b ++ a).toFinset = (c::(a++b)).toFinset := by
      ext w; simp; tauto
    rw [hw, List.toFinset_card_of_nodup hnd]
    simp [← hlen]; omega

/-- 无控制交换不需要 Toffoli，用于把新值移回固定的寄存器位置。 -/
def exchangeRegisters (a b : List Wire) : Program :=
  copyRegister none b a ++ copyRegister none a b ++ copyRegister none b a

theorem exchangeRegisters_spec (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (a++b).Nodup) (A B : Nat) :
    {{ a=A, b=B }} exchangeRegisters a b {{ a=B, b=A }} := by
  have hba : (b++a).Nodup := by simpa only [List.nodup_append_comm] using hnd
  have h1 : {{ a=A, b=B }} copyRegister none b a {{ a=(A ^^^ B), b=B }} :=
    Triple.conseq (fun st h => h.symm) (copyRegister_spec b a hlen.symm hba B A)
      (fun st h => h.symm)
  have h2 := copyRegister_spec a b hlen hnd (A ^^^ B) B
  have he : B ^^^ (A ^^^ B)=A := by simp [Nat.xor_left_comm]
  rw [he] at h2
  have h3 : {{ a=(A ^^^ B), b=A }} copyRegister none b a {{ a=B, b=A }} := by
    have h := copyRegister_spec b a hlen.symm hba A (A ^^^ B)
    have he : (A ^^^ B) ^^^ A=B := by simp [Nat.xor_right_comm]
    rw [he] at h
    exact Triple.conseq (fun st h => h.symm) h (fun st h => h.symm)
  simpa only [exchangeRegisters, List.append_assoc] using h1.seq (h2.seq h3)

theorem exchangeRegisters_resources (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (a++b).Nodup) :
    toffoliCount (exchangeRegisters a b)=0 ∧ measurementCount (exchangeRegisters a b)=0 ∧
    qubitCount (exchangeRegisters a b)=2*a.length := by
  have h1 := copyRegister_counts none a b hlen
  have h2 := copyRegister_counts none b a hlen.symm
  have wa := copyRegister_wires none a b hlen
  have wb := copyRegister_wires none b a hlen.symm
  have he : b.isEmpty=a.isEmpty := by cases a <;> cases b <;> simp_all
  refine ⟨by simp [exchangeRegisters, toffoliCount_append, h1.1, h2.1],
    by simp [exchangeRegisters, measurementCount_append, h1.2, h2.2], ?_⟩
  rw [qubitCount, exchangeRegisters, wires_append, wires_append, wa, wb, he]
  split_ifs with h
  · have hz : a=[] := List.isEmpty_iff.mp h
    simp [hz]
  · have hw : (none.toList ++ b ++ a).toFinset ∪ (none.toList ++ a ++ b).toFinset ∪
        (none.toList ++ b ++ a).toFinset = (a++b).toFinset := by
      ext w; simp; tauto
    rw [hw, List.toFinset_card_of_nodup hnd]
    simp [← hlen]; omega

theorem swapRegisters_wires (c : Wire) (a b : List Wire) (hlen : a.length=b.length) :
    wires (swapRegisters c a b) ⊆ (c::(a++b)).toFinset := by
  have wa := copyRegister_wires (some c) a b hlen
  have wb := copyRegister_wires none b a hlen.symm
  intro w hw
  simp only [swapRegisters, wires_append, Finset.mem_union] at hw
  have ha : w∈wires (copyRegister (some c) a b) → w∈(c::(a++b)).toFinset := by
    rw [wa]; split_ifs <;> simp_all
  have hb : w∈wires (copyRegister none b a) → w∈(c::(a++b)).toFinset := by
    rw [wb]; split_ifs <;> simp_all [or_comm]
  tauto

theorem exchangeRegisters_wires (a b : List Wire) (hlen : a.length=b.length) :
    wires (exchangeRegisters a b) ⊆ (a++b).toFinset := by
  have wa := copyRegister_wires none a b hlen
  have wb := copyRegister_wires none b a hlen.symm
  intro w hw
  simp only [exchangeRegisters, wires_append, Finset.mem_union] at hw
  have ha : w∈wires (copyRegister none a b) → w∈(a++b).toFinset := by
    rw [wa]; split_ifs <;> simp_all
  have hb : w∈wires (copyRegister none b a) → w∈(a++b).toFinset := by
    rw [wb]; split_ifs <;> simp_all [or_comm]
  tauto

/-- 两个目标寄存器以外逐线保持，包括控制线。 -/
theorem swapRegisters_correct (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hnd : (c::(a++b)).Nodup) (s : State) (m : List Bool) :
    (run (swapRegisters c a b) m s).phase=s.phase ∧
    (∀ w, w∉a → w∉b → (run (swapRegisters c a b) m s).basis w=s.basis w) ∧
    regValue a (run (swapRegisters c a b) m s).basis =
      (if s.basis c then regValue b s.basis else regValue a s.basis) ∧
    regValue b (run (swapRegisters c a b) m s).basis =
      (if s.basis c then regValue a s.basis else regValue b s.basis) := by
  obtain ⟨hp,hv⟩ := swapRegisters_spec c a b hlen hnd (s.basis c)
    (regValue a s.basis) (regValue b s.basis) s m ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨hp,?_,hv.1.2,hv.2⟩
  intro w ha hb
  by_cases hc : w=c
  · subst w; exact hv.1.1
  · apply run_preserves_outside
    intro hm
    have ht := swapRegisters_wires c a b hlen hm
    simp [ha,hb,hc] at ht

end ECDSAAdd.Arithmetic
