import ECDSAAdd.Arithmetic.RecordRound

namespace ECDSAAdd.Arithmetic

/-- 数据布局外的计数器与控制位；四个工作项始终为零。 -/
structure RoundAuxValues (L : KaliskiRoundLayout) (K N : Nat) (A D S T : Bool)
    (st : BasisState) : Prop where
  k : regValue L.k st=K
  next : regValue L.kNext st=N
  y : regValue L.counter.y st=0
  carry : regValue L.counter.carry st=0
  active : st L.active=A
  done : st L.done=D
  swap : st L.swap=S
  subtract : st L.subtract=T
  odd : st L.oddWork=false
  both : st L.bothWork=false
  cin : st L.compareCin=false

/-- 完整单轮断言，区分计数器的两份物理银行与记录位。 -/
def RoundState (L : KaliskiRoundLayout) (z : KState) (K N : Nat) (A D S T : Bool)
    (st : BasisState) : Prop := RoundValues L.data (roundDataValues z) st ∧ RoundAuxValues L K N A D S T st

namespace KaliskiRoundLayout

theorem counter_not_data (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (w : Wire) (hw : w∈L.counter.wires) : w∉L.data.wires := by
  have h := List.nodup_append'.mp hnd
  intro hd
  exact List.disjoint_left.mp h.2.2 (List.mem_append_right _ hd) hw

theorem controls_counter_nodup (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) :
    ([L.done,L.swap,L.subtract,L.oddWork,L.bothWork,L.compareCin]++L.counter.wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  simp only [wires,List.count_append] at h ⊢
  omega

theorem control_not_counter (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (c : Wire)
    (hc : c∈[L.done,L.swap,L.subtract,L.oddWork,L.bothWork,L.compareCin]) : c∉L.counter.wires :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.controls_counter_nodup hnd)).2.2 hc

end KaliskiRoundLayout

namespace RoundAuxValues

theorem congr (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (K N : Nat) (A D S T : Bool)
    (s t : BasisState) (h : RoundAuxValues L K N A D S T s)
    (he : ∀ w, w∉L.data.wires → t w=s w) : RoundAuxValues L K N A D S T t := by
  have hc (c : Wire) (hm : c∈L.controls) := he c (L.control_not_data hnd c hm)
  have hr (r : List Wire) (hm : r⊆L.counter.wires) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw => he w (L.counter_not_data hnd w (hm hw)))
  refine ⟨(hr L.k L.counter.reg_subset.1).trans h.k,
    (hr L.kNext L.counter.reg_subset.2.2.1).trans h.next,
    (hr L.counter.y L.counter.reg_subset.2.1).trans h.y,
    (hr L.counter.carry L.counter.reg_subset.2.2.2).trans h.carry,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact (hc _ (by simp [KaliskiRoundLayout.controls])).trans h.active
    | exact (hc _ (by simp [KaliskiRoundLayout.controls])).trans h.done
    | exact (hc _ (by simp [KaliskiRoundLayout.controls])).trans h.swap
    | exact (hc _ (by simp [KaliskiRoundLayout.controls])).trans h.subtract
    | exact (hc _ (by simp [KaliskiRoundLayout.controls])).trans h.odd
    | exact (hc _ (by simp [KaliskiRoundLayout.controls])).trans h.both
    | exact (hc _ (by simp [KaliskiRoundLayout.controls])).trans h.cin

theorem record (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (z : KState)
    (K N : Nat) (A D S T : Bool) (st : BasisState) (h : RoundAuxValues L K N A D S T st) :
    RoundAuxValues L K N A D (S ^^ (kaliskiCode z).1) (T ^^ (kaliskiCode z).2) (recordState L z st) := by
  have hs := L.control_not_counter hnd L.swap (by simp)
  have ht := L.control_not_counter hnd L.subtract (by simp)
  have hr (r : List Wire) (hm : r⊆L.counter.wires) :
      regValue r (recordState L z st)=regValue r st := by
    apply regValue_congr
    intro w hw
    have hws : w≠L.swap := fun he => hs (he ▸ hm hw)
    have hwt : w≠L.subtract := fun he => ht (he ▸ hm hw)
    simp [recordState,writeBit,hws,hwt]
  have hc := (List.nodup_append'.mp (L.controls_data_nodup hnd)).1
  have rev := List.nodup_reverse.mpr hc
  simp only [KaliskiRoundLayout.controls,List.nodup_cons,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at hc rev
  refine ⟨(hr L.k L.counter.reg_subset.1).trans h.k,
    (hr L.kNext L.counter.reg_subset.2.2.1).trans h.next,
    (hr L.counter.y L.counter.reg_subset.2.1).trans h.y,
    (hr L.counter.carry L.counter.reg_subset.2.2.2).trans h.carry,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp_all [recordState,writeBit,h.active,h.done,h.swap,h.subtract,h.odd,h.both,h.cin]

end RoundAuxValues

/-- 记录前后的完整单轮状态，允许任意旧记录以支持逆轮清理。 -/
theorem recordRound_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (z : KState)
    (K N : Nat) (D S T : Bool) :
    Triple (RoundState L z K N (decide (z.v≠0)) D S T) (recordRound L)
      (RoundState L z K N (decide (z.v≠0)) D (S ^^ (kaliskiCode z).1) (T ^^ (kaliskiCode z).2)) := by
  intro s m h
  obtain ⟨hp,hv⟩ := recordRound_frame L hnd z s.basis h.2.active h.2.odd h.2.both s m ⟨h.1,fun _ _ => rfl⟩
  exact ⟨hp,hv.1,RoundAuxValues.congr L hnd _ _ _ _ _ _ _ _
    (h.2.record L hnd z K N _ D S T s.basis) hv.2⟩

theorem kaliskiBodyProgram_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N : Nat) (A D S T : Bool)
    (hU : (kaliskiSwap (S) z).u<2^L.data.width)
    (hsub : (if T then (kaliskiSwap (S) z).v else 0)≤(kaliskiSwap (S) z).u)
    (hR : (kaliskiSwap (S) z).r+(if T then (kaliskiSwap (S) z).s else 0)<2^L.data.width)
    (heven : A=true → ((kaliskiSwap (S) z).u-
      (if T then (kaliskiSwap (S) z).v else 0))%2=0)
    (hfit : A=true → 2*(kaliskiSwap (S) z).s<2^L.data.width) :
    Triple (RoundState L (z) K N A D S T) (kaliskiBodyProgram L.data L.active L.swap L.subtract)
      (RoundState L (kaliskiBody A (S,T) z) K N A D S T) := by
  have hc : ([L.active,L.swap,L.subtract]++L.data.wires).Nodup := by
    have hh := L.controls_data_nodup hnd
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hh w
    simp only [KaliskiRoundLayout.controls,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hw : 0<L.data.width := by simp [KaliskiRoundLayout.data,RoundDataLayout.width]
  intro s m h
  have hb := kaliskiBodyProgram_frame L.data L.active L.swap L.subtract hc hw z s.basis
  simp only [h.2.active,h.2.swap,h.2.subtract] at hb
  obtain ⟨hp,hv⟩ := hb hU hsub hR heven hfit s m ⟨h.1,fun _ _ => rfl⟩
  exact ⟨hp,hv.1,RoundAuxValues.congr L hnd K N A D S T _ _ h.2 hv.2⟩

theorem kaliskiUnbodyProgram_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N : Nat) (A D S T : Bool)
    (hU : (kaliskiSwap (S) z).u<2^L.data.width)
    (hsub : (if T then (kaliskiSwap (S) z).v else 0)≤(kaliskiSwap (S) z).u)
    (hR : (kaliskiSwap (S) z).r+(if T then (kaliskiSwap (S) z).s else 0)<2^L.data.width)
    (heven : A=true → ((kaliskiSwap (S) z).u-
      (if T then (kaliskiSwap (S) z).v else 0))%2=0) :
    Triple (RoundState L (kaliskiBody A (S,T) z) K N A D S T) (kaliskiUnbodyProgram L.data L.active L.swap L.subtract)
      (RoundState L (z) K N A D S T) := by
  have hc : ([L.active,L.swap,L.subtract]++L.data.wires).Nodup := by
    have hh := L.controls_data_nodup hnd
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp hh w
    simp only [KaliskiRoundLayout.controls,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hw : 0<L.data.width := by simp [KaliskiRoundLayout.data,RoundDataLayout.width]
  intro s m h
  have hb := kaliskiUnbodyProgram_frame L.data L.active L.swap L.subtract hc hw z s.basis
  simp only [h.2.active,h.2.swap,h.2.subtract] at hb
  obtain ⟨hp,hv⟩ := hb hU hsub hR heven s m ⟨h.1,fun _ _ => rfl⟩
  exact ⟨hp,hv.1,RoundAuxValues.congr L hnd K N A D S T _ _ h.2 hv.2⟩

private theorem counter_update (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N K' N' : Nat) (A D S T : Bool) (s t : BasisState)
    (h : RoundState L z K N A D S T s)
    (hk : regValue L.k t=K') (hn : regValue L.kNext t=N')
    (hy : regValue L.counter.y t=0) (hcarry : regValue L.counter.carry t=0)
    (ha : t L.active=A) (he : ∀ w, w∉L.counter.wires → t w=s w) :
    RoundState L z K' N' A D S T t := by
  have hc (c : Wire) (hm : c∈[L.done,L.swap,L.subtract,L.oddWork,L.bothWork,L.compareCin]) :=
    he c (L.control_not_counter hnd c hm)
  have hd (w : Wire) (hw : w∈L.data.wires) : t w=s w :=
    he w (fun hh => L.counter_not_data hnd w hh hw)
  refine ⟨⟨fun f => (regValue_congr _ _ _ (fun w hw => hd w (L.data.reg_mem f hw))).trans (h.1.1 f),
    (hd L.data.cin List.mem_cons_self).trans h.1.2⟩,hk,hn,hy,hcarry,ha,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact (hc _ (by simp)).trans h.2.done
    | exact (hc _ (by simp)).trans h.2.swap
    | exact (hc _ (by simp)).trans h.2.subtract
    | exact (hc _ (by simp)).trans h.2.odd
    | exact (hc _ (by simp)).trans h.2.both
    | exact (hc _ (by simp)).trans h.2.cin

theorem counterInc_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (hw : L.counter.width=10)
    (z : KState) (K : Nat) (A D S T : Bool) :
    Triple (RoundState L z K 0 A D S T) (counterInc L.counter)
      (RoundState L z 0 ((K+A.toNat)%1024) A D S T) := by
  intro s m h
  obtain ⟨hp,hv⟩ := counterInc_spec L.counter (L.counter_nodup hnd) hw K A s m
    ⟨⟨⟨⟨h.2.k,h.2.y⟩,h.2.active⟩,h.2.next⟩,h.2.carry⟩
  have he (w : Wire) (hh : w∉L.counter.wires) := run_preserves_outside (counterInc L.counter) m s w
    (by rw [(counterMove_wires L.counter hw).1]; exact fun hm => hh (List.mem_toFinset.mp hm))
  exact ⟨hp,counter_update L hnd z K 0 _ _ A D S T _ _ h hv.1.1.1.1 hv.1.2
    hv.1.1.1.2 hv.2 hv.1.1.2 he⟩

theorem counterDec_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) (hw : L.counter.width=10)
    (z : KState) (K : Nat) (A D S T : Bool) :
    Triple (RoundState L z 0 K A D S T) (counterDec L.counter.swapCounter)
      (RoundState L z ((K+1024-A.toNat)%1024) 0 A D S T) := by
  intro s m h
  have hc := L.counter.swapCounter_fields
  have hs := counterDec_spec L.counter.swapCounter (L.counter.swapCounter_perm.nodup_iff.mpr (L.counter_nodup hnd))
    (hc.2.2.2.2.2.trans hw) K A
  simp only [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1] at hs
  obtain ⟨hp,hv⟩ := hs s m ⟨⟨⟨⟨h.2.next,h.2.y⟩,h.2.active⟩,h.2.k⟩,h.2.carry⟩
  have he (w : Wire) (hh : w∉L.counter.wires) := run_preserves_outside (counterDec L.counter.swapCounter) m s w
    (by rw [(counterMove_wires L.counter.swapCounter (hc.2.2.2.2.2.trans hw)).2]
        exact fun hm => hh (L.counter.swapCounter_perm.mem_iff.mp (List.mem_toFinset.mp hm)))
  exact ⟨hp,counter_update L hnd z 0 K _ _ A D S T _ _ h hv.1.2 hv.1.1.1.1
    hv.1.1.1.2 hv.2 hv.1.1.2 he⟩

end ECDSAAdd.Arithmetic
