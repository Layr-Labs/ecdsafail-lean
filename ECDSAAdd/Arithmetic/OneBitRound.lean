import ECDSAAdd.Arithmetic.RoundSpec
import ECDSAAdd.Arithmetic.EraseSwap
import ECDSAAdd.Math.KaliskiOneBit

namespace ECDSAAdd.Arithmetic

/-- 按更新后的 r 最低位异或交换分支，不改变活动位或数据。 -/
def recoverSwap (L : KaliskiRoundLayout) : Program :=
  [.CX L.active L.swap, .CCX L.active L.r.head! L.swap]

/-- 一位历史正轮，交换条件只在本轮内存活。 -/
def oneBitRound (L : KaliskiRoundLayout) (i : Nat) : Program :=
  loadActive L ++ recordRound L ++ kaliskiBodyProgram L.data L.active L.swap L.subtract ++
  eraseSwap L ++ counterInc L.counter ++ zeroControlled L.active L.done (L.data.zeroBits .v) ++
  roundActiveXor L i

/-- 恢复交换条件后调用既有逆算术，最后清除减法历史。 -/
def oneBitUnround (L : KaliskiRoundLayout) (i : Nat) : Program :=
  roundActiveXor L i ++ recoverSwap L ++ zeroControlled L.active L.done (L.data.zeroBits .v) ++
  kaliskiUnbodyProgram L.data L.active L.swap L.subtract ++ counterDec L.counter.swapCounter ++
  recordRound L ++ loadActive L

private theorem swap_update (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N : Nat) (A D S T S' : Bool) (s t : BasisState)
    (h : RoundState L z K N A D S T s) (hs : t L.swap=S')
    (he : ∀ w, w≠L.swap → t w=s w) : RoundState L z K N A D S' T t := by
  have hds := L.control_not_data hnd L.swap (by simp [KaliskiRoundLayout.controls])
  have hcs := L.control_not_counter hnd L.swap (by simp)
  have hdr (w : Wire) (hw : w∈L.data.wires) : t w=s w :=
    he w (fun hh => hds (hh ▸ hw))
  have hr (r : List Wire) (hm : r⊆L.counter.wires) : regValue r t=regValue r s := by
    apply regValue_congr
    intro w hw
    exact he w (fun hh => hcs (hh ▸ hm hw))
  refine ⟨⟨fun f => (regValue_congr _ _ _ (fun w hw => hdr w (L.data.reg_mem f hw))).trans (h.1.1 f),
    (hdr L.data.cin List.mem_cons_self).trans h.1.2⟩,
    (hr L.k L.counter.reg_subset.1).trans h.2.k,
    (hr L.kNext L.counter.reg_subset.2.2.1).trans h.2.next,
    (hr L.counter.y L.counter.reg_subset.2.1).trans h.2.y,
    (hr L.counter.carry L.counter.reg_subset.2.2.2).trans h.2.carry,?_,?_,hs,?_,?_,?_,?_⟩
  all_goals
    have hc := (List.nodup_append'.mp (L.controls_data_nodup hnd)).1
    have rev := List.nodup_reverse.mpr hc
    simp only [KaliskiRoundLayout.controls,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,not_false_eq_true,and_true,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at hc rev
  all_goals first
    | exact (he _ (by tauto)).trans h.2.active
    | exact (he _ (by tauto)).trans h.2.done
    | exact (he _ (by tauto)).trans h.2.subtract
    | exact (he _ (by tauto)).trans h.2.odd
    | exact (he _ (by tauto)).trans h.2.both
    | exact (he _ (by tauto)).trans h.2.cin

/-- 两门恢复器只更新 swap，覆盖任意记录位初值。 -/
theorem recoverSwap_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N : Nat) (A D S T : Bool) :
    Triple (RoundState L z K N A D S T) (recoverSwap L)
      (RoundState L z K N A D (S ^^ (A && decide (z.r%2=0))) T) := by
  have has : L.active≠L.swap := by
    have h := (List.nodup_append'.mp (L.controls_data_nodup hnd)).1
    simp only [KaliskiRoundLayout.controls,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,not_false_eq_true,and_true] at h
    tauto
  have hrs : L.r.head!≠L.swap := fun he =>
    L.control_not_data hnd L.swap (by simp [KaliskiRoundLayout.controls])
      (he ▸ L.data.reg_mem .r (L.head_mem .r))
  intro s m h
  have hr : s.basis L.r.head! = decide (z.r%2≠0) := by
    have hn : L.r≠[] := by
      intro he
      have hh := L.data_reg_length .r
      change L.r.length = _ at hh
      rw [he] at hh
      simp at hh
    have hv : regValue L.r s.basis=z.r := h.1.1 .r
    simpa only [hv] using regValue_headBit L.r hn s.basis
  refine ⟨rfl,swap_update L hnd z K N A D S T _ _ _ h ?_ ?_⟩
  · simp only [recoverSwap,run,writeBit,Function.update_self,
      Function.update_of_ne has,Function.update_of_ne hrs,h.2.active,h.2.swap,hr]
    by_cases he : z.r%2=0 <;> simp [he]
  · intro w hw
    simp [recoverSwap,run,writeBit,hw]

/-- 清理前提由更新后r的奇偶性给出；其余轮状态逐项保持。 -/
theorem eraseSwap_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N : Nat) (A D T : Bool) :
    Triple (RoundState L z K N A D (A && decide (z.r%2=0)) T) (eraseSwap L)
      (RoundState L z K N A D false T) := by
  intro s m h
  have hr : s.basis L.r.head! = decide (z.r%2≠0) := by
    have hn : L.r≠[] := by
      intro he
      have hh := L.data_reg_length .r
      change L.r.length = _ at hh
      rw [he] at hh
      simp at hh
    have hv : regValue L.r s.basis=z.r := h.1.1 .r
    simpa only [hv] using regValue_headBit L.r hn s.basis
  have ht : s.basis L.swap=(s.basis L.active && !s.basis L.r.head!) := by
    rw [h.2.swap,h.2.active,hr]
    by_cases he : z.r%2=0 <;> simp [he]
  rw [eraseSwap_correct L hnd s m ht]
  refine ⟨rfl,swap_update L hnd z K N A D _ T false _ _ h ?_ ?_⟩
  · simp [writeBit]
  · intro w hw; simp [writeBit,hw]

end ECDSAAdd.Arithmetic
