import ECDSAAdd.Arithmetic.RoundState
import ECDSAAdd.Arithmetic.BorrowFrame

namespace ECDSAAdd.Arithmetic

private theorem counter_regs_not_active (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) :
    L.active∉L.k++L.kNext++L.counter.y++L.counter.carry := by
  have hp : (L.active::(L.k++L.kNext++L.counter.y++L.counter.carry)).Perm L.counter.wires := by
    apply List.perm_iff_count.mpr
    intro w
    have h := L.counter.interface_perm.count_eq w
    simp only [List.count_append,List.count_cons,KaliskiRoundLayout.k,KaliskiRoundLayout.kNext,
      KaliskiRoundLayout.counter] at h ⊢
    omega
  exact (List.nodup_cons.mp (hp.nodup_iff.mpr (L.counter_nodup hnd))).1

private theorem flags_update (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N : Nat) (A D S T A' D' : Bool) (s t : BasisState)
    (h : RoundState L z K N A D S T s) (ha : t L.active=A') (hd : t L.done=D')
    (he : ∀ w, w≠L.active → w≠L.done → t w=s w) : RoundState L z K N A' D' S T t := by
  have hda := L.control_not_data hnd L.active (by simp [KaliskiRoundLayout.controls])
  have hdd := L.control_not_data hnd L.done (by simp [KaliskiRoundLayout.controls])
  have hdr (w : Wire) (hw : w∈L.data.wires) : t w=s w :=
    he w (fun hh => hda (hh ▸ hw)) (fun hh => hdd (hh ▸ hw))
  have hc := (List.nodup_append'.mp (L.controls_data_nodup hnd)).1
  have hn := counter_regs_not_active L hnd
  have hdc := L.control_not_counter hnd L.done (by simp)
  have hr (r : List Wire) (hm : r⊆L.k++L.kNext++L.counter.y++L.counter.carry)
      (hc : r⊆L.counter.wires) : regValue r t=regValue r s := by
    apply regValue_congr
    intro w hw
    exact he w (fun hh => hn (hh ▸ hm hw)) (fun hh => hdc (hh ▸ hc hw))
  refine ⟨⟨fun f => (regValue_congr _ _ _ (fun w hw => hdr w (L.data.reg_mem f hw))).trans (h.1.1 f),
    (hdr L.data.cin List.mem_cons_self).trans h.1.2⟩,
    (hr L.k (by intro w hw; simp [hw]) L.counter.reg_subset.1).trans h.2.k,
    (hr L.kNext (by intro w hw; simp [hw]) L.counter.reg_subset.2.2.1).trans h.2.next,
    (hr L.counter.y (by intro w hw; simp [hw]) L.counter.reg_subset.2.1).trans h.2.y,
    (hr L.counter.carry (by intro w hw; simp [hw]) L.counter.reg_subset.2.2.2).trans h.2.carry,
    ha,hd,?_,?_,?_,?_,?_⟩
  all_goals
    have rev := List.nodup_reverse.mpr hc
    simp only [KaliskiRoundLayout.controls,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,not_false_eq_true,and_true,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at hc rev
  all_goals first
    | exact (he _ (by tauto) (by tauto)).trans h.2.swap
    | exact (he _ (by tauto) (by tauto)).trans h.2.subtract
    | exact (he _ (by tauto) (by tauto)).trans h.2.odd
    | exact (he _ (by tauto) (by tauto)).trans h.2.both
    | exact (he _ (by tauto) (by tauto)).trans h.2.cin

theorem loadActive_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N : Nat) (A D S T : Bool) :
    Triple (RoundState L z K N A D S T) (loadActive L)
      (RoundState L z K N (A ^^ !D) D S T) := by
  have had : L.done≠L.active := by
    have h := (List.nodup_append'.mp (L.controls_data_nodup hnd)).1
    simp only [KaliskiRoundLayout.controls,List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true] at h
    exact Ne.symm h.1.1
  intro s m h
  refine ⟨rfl,flags_update L hnd z K N A D S T _ _ _ _ h ?_ ?_ ?_⟩
  · simp only [loadActive,run,writeBit,Function.update_self,Function.update_of_ne had,h.2.active,h.2.done]
    cases A <;> cases D <;> rfl
  · simpa [loadActive,run,writeBit,had] using h.2.done
  · intro w hw _
    simp [loadActive,run,writeBit,hw]

theorem KaliskiRoundLayout.zero_nodup (L : KaliskiRoundLayout) (hnd : L.wires.Nodup) :
    (L.active::L.done::(L.data.zeroBits .v).flatMap ZeroBit.wires).Nodup := by
  have he (bs : List RoundBit) (w : Wire) :
      ((bs.map (fun b => (⟨b.v,b.zero⟩ : ZeroBit))).flatMap ZeroBit.wires).count w =
      (bs.map RoundBit.v).count w+(bs.map RoundBit.zero).count w := by
    induction bs with
    | nil => simp
    | cons b bs ih => simp [ZeroBit.wires,List.count_cons,ih]; omega
  apply List.nodup_iff_count.mpr
  intro w
  have hc := List.nodup_iff_count.mp (L.controls_data_nodup hnd) w
  have hp := L.data.pair_count .v .zero (by decide) w
  simp only [List.count_cons,RoundDataLayout.zeroBits,RoundBit.get,he]
  change (L.data.bits.map RoundBit.v).count w+(L.data.bits.map RoundBit.zero).count w≤L.data.wires.count w at hp
  simp only [KaliskiRoundLayout.controls,List.count_append,List.count_cons,List.count_nil] at hc
  omega

theorem zeroDone_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (z : KState) (K N : Nat) (A D S T : Bool) :
    Triple (RoundState L z K N A D S T) (zeroControlled L.active L.done (L.data.zeroBits .v))
      (RoundState L z K N A (D ^^ (A && decide (z.v=0))) S T) := by
  intro s m h
  have hi : (L.data.zeroBits .v).map ZeroBit.input=L.v := by
    simp [RoundDataLayout.zeroBits,RoundDataLayout.reg,KaliskiRoundLayout.v,RoundDataLayout.v,
      List.map_map,Function.comp_def,RoundBit.get]
  have hw : (L.data.zeroBits .v).map ZeroBit.work=L.data.reg .zero := by
    simp [RoundDataLayout.zeroBits,RoundDataLayout.reg,List.map_map,Function.comp_def,RoundBit.get]
  have hv : regValue L.v s.basis=z.v := h.1.1 .v
  have hz : regValue (L.data.reg .zero) s.basis=0 := h.1.1 .zero
  have hs := zeroControlled_spec L.active L.done (L.data.zeroBits .v) (L.zero_nodup hnd) A D z.v
  rw [hi,hw] at hs
  obtain ⟨hp,hv⟩ := hs s m ⟨⟨⟨h.2.active,h.2.done⟩,hv⟩,hz⟩
  have hz' : ∀ b∈L.data.zeroBits .v, s.basis b.work=false := by
    intro b hb
    apply (regValue_zero _ _).mp hz
    rw [← hw]
    exact List.mem_map.mpr ⟨b,hb,rfl⟩
  have he := zeroControlled_correct L.active L.done (L.data.zeroBits .v) (L.zero_nodup hnd) s m hz'
  refine ⟨hp,flags_update L hnd z K N A D S T _ _ _ _ h hv.1.1.1 hv.1.1.2 ?_⟩
  intro w _ hd
  rw [he]
  simp [writeBit,hd]

theorem roundActiveXor_state (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (z : KState) (K i : Nat) (hi : i<512) (A D S T : Bool) :
    Triple (RoundState L z 0 K A D S T) (roundActiveXor L i)
      (RoundState L z 0 K (A ^^ decide (i < K)) D S T) := by
  intro s m h
  have hc := L.comparator_fields
  have hs := counterActiveXor_spec L.comparator L.active
    (L.comparator_nodup hnd) (hc.2.2.2.2.2.trans hw) K i A hi
  have hf := counterActiveXor_frame L.comparator L.active
    (L.comparator_nodup hnd) (hc.2.2.2.2.2.trans hw) i K hi A s m
  simp only [hc.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1] at hs hf
  obtain ⟨hp,hv⟩ := hs s m ⟨⟨⟨⟨h.2.active,h.2.next⟩,h.2.y⟩,h.2.cin⟩,h.2.carry⟩
  have he := hf h.2.active h.2.next h.2.y h.2.cin h.2.carry
  have hda : L.done≠L.active := by
    have hh := (List.nodup_append'.mp (L.controls_data_nodup hnd)).1
    simp only [KaliskiRoundLayout.controls,List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true] at hh
    exact Ne.symm hh.1.1
  exact ⟨hp,flags_update L hnd z 0 K A D S T _ _ _ _ h hv.1.1.1.1
    ((he L.done hda).trans h.2.done) (fun w ha _ => he w ha)⟩

end ECDSAAdd.Arithmetic
