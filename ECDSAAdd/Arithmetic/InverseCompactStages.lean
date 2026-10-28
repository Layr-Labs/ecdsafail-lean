import ECDSAAdd.Arithmetic.InverseCompactState

namespace ECDSAAdd.Arithmetic

/-- r以外的每条线保持时，中段边界只更新r的值。 -/
theorem CompactReady.update_r (L : InverseLoopLayout) (hn : L.wires.Nodup)
    (K R V : Nat) (cs : List (Bool×Bool)) (s t : BasisState) (h : CompactReady L K R cs s)
    (he : ∀ w,w∉L.middle.r → t w=s w) (hv : regValue L.middle.r t=V) : CompactReady L K V cs t := by
  have hnd := L.compact_parts_nodup hn
  rw [List.append_assoc] at hnd
  have hd := (List.nodup_append'.mp hnd).2.2
  refine ⟨hv,?_,?_,CompactFrozen.congr L hn K cs s t h.2.2.2 (fun w hw _ => he w hw)⟩
  · exact (regValue_congr _ _ _ (fun w hw => he w
      (fun hr => List.disjoint_left.mp hd hr (List.mem_append_left _ hw)))).trans h.2.1
  · exact (regValue_congr _ _ _ (fun w hw => he w
      (fun hr => List.disjoint_left.mp hd hr (List.mem_append_right _ hw)))).trans h.2.2.1

theorem compactNeg_values (L : InverseLoopLayout) (hn : L.wires.Nodup)
    (hm : L.arithmetic.width=256) (hl : L.first.low.length=256)
    (q R K : Nat) (hq : q<2^256) (ho : q%2=1) (hR : 0<R) (hb : R<2*q) (hev : R%2=0)
    (cs : List (Bool×Bool)) :
    Triple (CompactReady L K R cs) (negativeEven L.compactNeg q) (CompactReady L K (-(R:ZMod q)).val cs) ∧
    Triple (CompactReady L K (-(R:ZMod q)).val cs) (restoreNegativeEven L.compactNeg q) (CompactReady L K R cs) := by
  have work (s : BasisState) (V : Nat) (h : CompactReady L K V cs s) : regValue L.compactNeg.work s=0 := by
    apply (regValue_zero _ _).mpr
    intro w hw
    have hp := (L.compactNeg_partition hm hl).mem_iff.mp
      (show w∈L.compactNeg.wires from by simp [ModInPlaceLayout.wires,hw])
    have ha : w∉L.middle.r := by
      intro hr
      have hd := List.nodup_iff_count.mp (L.compactNeg_nodup hn hm hl) w
      have h1 := List.count_pos_iff.mpr hw
      have h2 := List.count_pos_iff.mpr hr
      simp only [ModInPlaceLayout.wires,List.count_append] at hd
      change L.middle.r.count w+L.compactNeg.z.count w+L.compactNeg.work.count w≤1 at hd
      omega
    rcases List.mem_append.mp hp with hp|hp
    · exact False.elim (ha hp)
    · exact (regValue_zero _ _).mp h.2.2.1 w (List.mem_of_mem_take hp)
  constructor
  · intro s m h
    obtain ⟨hp,hv,he⟩ := (negativeEven_correct L.compactNeg 256 q R (L.compactNeg_widths hm hl)
      (L.compactNeg_nodup hn hm hl) hq ho hR hb hev s m (work _ _ h)).1 h.1
    exact ⟨hp,CompactReady.update_r L hn K R _ cs _ _ h he hv⟩
  · intro s m h
    obtain ⟨hp,hv,he⟩ := (negativeEven_correct L.compactNeg 256 q R (L.compactNeg_widths hm hl)
      (L.compactNeg_nodup hn hm hl) hq ho hR hb hev s m (work _ _ h)).2 h.1
    exact ⟨hp,CompactReady.update_r L hn K _ R cs _ _ h he hv⟩

/-- 中段r为逆元；原r的负值及Montgomery商/借位显式保存在518位历史中。 -/
def CompactPrepared (L : InverseLoopLayout) (q K N : Nat) (cs : List (Bool×Bool)) (s : BasisState) : Prop :=
  L.compactScaling.Prepared q K N s ∧ regValue L.compactBorrow s=0 ∧ CompactFrozen L K cs s

theorem compactScale_values (L : InverseLoopLayout) (hn : L.wires.Nodup)
    (hm : L.arithmetic.width=256) (hl : L.first.low.length=256) (hk : L.first.counter.width=10)
    (q K N : Nat) (hq : q%16=15) (hb : q<2^256) (hN : N<q) (cs : List (Bool×Bool)) :
    Triple (CompactReady L K N cs) (L.compactScaling.prepare q) (CompactPrepared L q K N cs) ∧
    Triple (CompactPrepared L q K N cs) (L.compactScaling.restore q) (CompactReady L K N cs) := by
  have hr : L.middle.r.length=257 := by
    change (L.middle.data.reg .r).length=257
    rw [InverseLoopLayout.middle,loopEnd_data,L.first.data_reg_length,hl]
  have hw := L.compactScaling_widths hr hm hl hk
  have hd := L.compactScaling_nodup hn hm hl
  have borrow (s t : BasisState) (hz : regValue L.compactBorrow s=0)
      (he : ∀ w,w∉L.middle.r → w∉L.scaleLive → t w=s w) : regValue L.compactBorrow t=0 := by
    have hnd := List.nodup_iff_count.mp (L.compact_parts_nodup hn)
    apply (regValue_congr _ _ _ ?_).trans hz
    intro w hw
    have h1 := List.count_pos_iff.mpr hw
    have h := hnd w
    simp only [List.count_append] at h
    apply he w
    · intro hh; have := List.count_pos_iff.mpr hh; omega
    · intro hh; have := List.count_pos_iff.mpr hh; omega
  constructor
  · intro s m h
    have hpre : ((regValue L.compactScaling.a s.basis=N ∧ regValue L.compactScaling.k s.basis=K) ∧
        regValue L.compactScaling.live s.basis=0) ∧ regValue L.compactScaling.work s.basis=0 := by
      refine ⟨⟨⟨h.1,h.2.2.2.1.2.1⟩,?_⟩,?_⟩
      · simpa only [L.compactScaling_live hl] using h.2.1
      · rw [L.compactScaling_work hm hl]
        exact (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp h.2.2.1 w (List.mem_of_mem_take hw))
    obtain ⟨hp,hv⟩ := L.compactScaling.prepare_spec hw hd q hq hb N K hN s m hpre
    have he := L.compactScaling.prepare_frame hw hd q hq hb N K hN s m hpre
    rw [L.compactScaling_live hl] at he
    exact ⟨hp,hv,borrow _ _ h.2.2.1 he,CompactFrozen.congr L hn K cs _ _ h.2.2.2 he⟩
  · intro s m h
    obtain ⟨hp,hv⟩ := L.compactScaling.restore_spec hw hd q hq hb N K hN s m h.1
    have he := L.compactScaling.restore_frame hw hd q hq hb N K hN s m h.1
    rw [L.compactScaling_live hl] at he
    refine ⟨hp,hv.1.1.1,?_,borrow _ _ h.2.1 he,CompactFrozen.congr L hn K cs _ _ h.2.2 he⟩
    simpa only [L.compactScaling_live hl] using hv.1.2

end ECDSAAdd.Arithmetic
