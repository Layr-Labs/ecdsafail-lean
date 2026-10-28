import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Arithmetic.Reduction

namespace ECDSAAdd.Arithmetic

/-- 规范值的未用高位为零。 -/
theorem regValue_take_drop_of_lt (r : List Wire) (n N : Nat) (s : BasisState)
    (hr : n≤r.length) (hv : regValue r s=N) (hb : N<2^n) :
    regValue (r.take n) s=N ∧ regValue (r.drop n) s=0 := by
  have hh := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hr, hv] at hh
  have hn : 0<2^n := by positivity
  have ht := regValue_lt (r.take n) s
  rw [List.length_take, Nat.min_eq_left hr] at ht
  have hz : regValue (r.drop n) s=0 := by
    by_contra h
    have : 1≤regValue (r.drop n) s := by omega
    nlinarith
  exact ⟨by simpa [hz] using hh.symm,hz⟩

/-- 只交换规范数的低位，高位保持零；适用于两个带 padding 的寄存器。 -/
theorem swapLow_correct (c : Wire) (a b : List Wire) (n A B : Nat)
    (ha : n≤a.length) (hb : n≤b.length) (hnd : (c::a++b).Nodup)
    (hA : A<2^n) (hB : B<2^n) (s : State) (m : List Bool)
    (hva : regValue a s.basis=A) (hvb : regValue b s.basis=B) :
    (run (swapRegisters c (a.take n) (b.take n)) m s).phase=s.phase ∧
    (∀ q, q∉a.take n → q∉b.take n →
      (run (swapRegisters c (a.take n) (b.take n)) m s).basis q=s.basis q) ∧
    regValue a (run (swapRegisters c (a.take n) (b.take n)) m s).basis=
      (if s.basis c then B else A) ∧
    regValue b (run (swapRegisters c (a.take n) (b.take n)) m s).basis=
      (if s.basis c then A else B) := by
  have hr := (List.nodup_cons.mp hnd).2
  have hn : (c::a.take n++b.take n).Nodup :=
    (((List.take_sublist n a).append (List.take_sublist n b)).cons₂ c).nodup hnd
  have hl : (a.take n).length=(b.take n).length := by
    simp [List.length_take,Nat.min_eq_left ha,Nat.min_eq_left hb]
  obtain ⟨hpa,hza⟩ := regValue_take_drop_of_lt a n A s.basis ha hva hA
  obtain ⟨hpb,hzb⟩ := regValue_take_drop_of_lt b n B s.basis hb hvb hB
  obtain ⟨hf,he,hx,hy⟩ := swapRegisters_correct c (a.take n) (b.take n) hl hn s m
  have tail (r : List Wire) (hz : regValue (r.drop n) s.basis=0)
      (hda : List.Disjoint (a.take n) (r.drop n))
      (hdb : List.Disjoint (b.take n) (r.drop n)) :
      regValue r (run (swapRegisters c (a.take n) (b.take n)) m s).basis =
      regValue (r.take n) (run (swapRegisters c (a.take n) (b.take n)) m s).basis := by
    have ht : regValue (r.drop n) (run (swapRegisters c (a.take n) (b.take n)) m s).basis=0 := by
      apply Eq.trans (regValue_congr _ _ _ ?_) hz
      intro q hq
      exact he q (fun h => List.disjoint_left.mp hda h hq)
        (fun h => List.disjoint_left.mp hdb h hq)
    have hh := regValue_append (r.take n) (r.drop n)
      (run (swapRegisters c (a.take n) (b.take n)) m s).basis
    simpa [ht] using hh
  have cross : List.Disjoint a b := by
    intro q hqa hqb
    exact (List.nodup_append.mp hr).2.2 q hqa q hqb rfl
  have hab : List.Disjoint (a.take n) (b.drop n) := by
    intro q hqa hqb
    exact cross ((List.take_sublist n a).subset hqa) ((List.drop_sublist n b).subset hqb)
  have hba : List.Disjoint (b.take n) (a.drop n) := by
    intro q hqb hqa
    exact cross ((List.drop_sublist n a).subset hqa) ((List.take_sublist n b).subset hqb)
  refine ⟨hf,he,?_,?_⟩
  · rw [tail a hza (List.disjoint_take_drop (List.nodup_append.mp hr).1 (Nat.le_refl n)) hba,hx,hpa,hpb]
  · rw [tail b hzb hab (List.disjoint_take_drop (List.nodup_append.mp hr).2.1 (Nat.le_refl n)),hy,hpa,hpb]

end ECDSAAdd.Arithmetic
