import ECDSAAdd.Arithmetic.ReplayCell

namespace ECDSAAdd.Arithmetic

/-- 回放格的两个规范载荷、三控制位与零工作区。 -/
def ReplayValues (active swap sub : Wire) (L : ModInPlaceLayout)
    (C W S : Bool) (X Y : Nat) (s : BasisState) : Prop :=
  s active=C ∧ s swap=W ∧ s sub=S ∧
  regValue L.z s=X ∧ regValue L.a s=Y ∧ regValue L.work s=0

namespace ReplayValues

theorem control_nodup (active swap sub : Wire) (L : ModInPlaceLayout)
    (h : (active::swap::sub::L.wires).Nodup) (c : Wire)
    (hc : c∈[active,swap,sub]) : (c::L.wires).Nodup := by
  have hh := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp h).2).2).2
  refine List.nodup_cons.mpr ⟨?_,hh⟩
  intro hm
  have ht := List.nodup_iff_count.mp h c
  have hx := List.count_pos_iff.mpr hm
  simp only [List.count_cons] at ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl <;> simp_all

theorem unary_nodup (c : Wire) (L : ModInPlaceLayout) (h : (c::L.wires).Nodup) :
    (c::L.unary.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have hh := List.nodup_iff_count.mp h q
  simp only [ModInPlaceLayout.wires,ModInPlaceLayout.unary,ModUnaryLayout.wires,
    ModUnaryLayout.work,ModUnaryLayout.core,ModUnaryLayout.z,ModInPlaceLayout.z,
    ModInPlaceLayout.work,ModAddCoreLayout.z,ModAddCoreLayout.work,
    List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

/-- 三个控制位均在两个载荷寄存器之外。 -/
theorem control_outside (active swap sub : Wire) (L : ModInPlaceLayout)
    (h : (active::swap::sub::L.wires).Nodup) (c : Wire)
    (hc : c∈[active,swap,sub]) : c∉L.z ∧ c∉L.a := by
  have hn := (List.nodup_cons.mp (control_nodup active swap sub L h c hc)).1
  exact ⟨fun hm => hn (by simp [ModInPlaceLayout.wires,hm]),
    fun hm => hn (by simp [ModInPlaceLayout.wires,hm])⟩

theorem swap_step (active swap sub : Wire) (L : ModInPlaceLayout)
    (n X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hX : X<2^n) (hY : Y<2^n) :
    Triple (ReplayValues active swap sub L C W S X Y)
      (swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length))
      (ReplayValues active swap sub L C W S (if W then Y else X) (if W then X else Y)) := by
  intro s m h
  have hs := control_nodup active swap sub L hnd swap (by simp)
  have hn : (swap::L.z++L.a).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have ht := List.nodup_iff_count.mp hs q
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at ht ⊢
    omega
  have hz : n≤L.z.length := by simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low]
  obtain ⟨hf,he,hx,hy⟩ := swapLow_correct swap L.z L.a n X Y hz
    (by rw [hw.core.a]; omega) hn hX hY s m h.2.2.2.1 h.2.2.2.2.1
  rw [← hw.core.low] at hf he hx hy
  have keep (q : Wire) (hqz : q∉L.z) (hqa : q∉L.a) :=
    he q (fun hm => hqz ((List.take_sublist _ _).subset hm))
      (fun hm => hqa ((List.take_sublist _ _).subset hm))
  have ctrl (q : Wire) (hq : q∈[active,swap,sub]) :=
    keep q (control_outside active swap sub L hnd q hq).1
      (control_outside active swap sub L hnd q hq).2
  refine ⟨hf,?_,?_,?_,?_,?_,?_⟩
  · exact (ctrl active (by simp)).trans h.1
  · exact (ctrl swap (by simp)).trans h.2.1
  · exact (ctrl sub (by simp)).trans h.2.2.1
  · simpa [h.2.1] using hx
  · simpa [h.2.1] using hy
  · apply Eq.trans (regValue_congr _ _ _ ?_) h.2.2.2.2.2
    intro q hq
    have ht := List.nodup_iff_count.mp hs q
    have hc := List.count_pos_iff.mpr hq
    simp only [ModInPlaceLayout.wires,List.count_append,List.count_cons] at ht
    apply keep q
    · intro hm; have := List.count_pos_iff.mpr hm; omega
    · intro hm; have := List.count_pos_iff.mpr hm; omega


theorem subtract_step (active swap sub : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hp : 0<p) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) :
    Triple (ReplayValues active swap sub L C W S X Y) (controlledModSub sub L p)
      (ReplayValues active swap sub L C W S (if S then (X+p-Y)%p else X) Y) := by
  intro s m h
  have hs := control_nodup active swap sub L hnd sub (by simp)
  obtain ⟨hf,hv⟩ := controlledModSub_spec sub L n p Y X S hw hs hp hpn (by omega) hX
    s m ⟨⟨⟨h.2.2.1,h.2.2.2.2.1⟩,h.2.2.2.1⟩,h.2.2.2.2.2⟩
  simp only [Holds.holds] at hv
  have keep (q : Wire) (hq : q∉L.z) :=
    controlledModSub_frame sub L n p Y X S hw hs hp hpn (by omega) hX
      s m h.2.2.1 h.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.2 q hq
  exact ⟨hf,(keep active (control_outside active swap sub L hnd active (by simp)).1).trans h.1,
    (keep swap (control_outside active swap sub L hnd swap (by simp)).1).trans h.2.1,
    hv.1.1.1,hv.1.2,hv.1.1.2,hv.2⟩


theorem add_step (active swap sub : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hp : 0<p) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) :
    Triple (ReplayValues active swap sub L C W S X Y) (controlledModAdd sub L p)
      (ReplayValues active swap sub L C W S (if S then (X+Y)%p else X) Y) := by
  intro s m h
  have hs := control_nodup active swap sub L hnd sub (by simp)
  obtain ⟨hf,hv⟩ := controlledModAdd_spec sub L n p Y X S hw hs hp hpn (by omega) hX
    s m ⟨⟨⟨h.2.2.1,h.2.2.2.2.1⟩,h.2.2.2.1⟩,h.2.2.2.2.2⟩
  simp only [Holds.holds] at hv
  have keep (q : Wire) (hq : q∉L.z) :=
    controlledModAdd_frame sub L n p Y X S hw hs hp hpn (by omega) hX
      s m h.2.2.1 h.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.2 q hq
  exact ⟨hf,(keep active (control_outside active swap sub L hnd active (by simp)).1).trans h.1,
    (keep swap (control_outside active swap sub L hnd swap (by simp)).1).trans h.2.1,
    hv.1.1.1,hv.1.2,hv.1.1.2,hv.2⟩


theorem half_step (active swap sub : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) :
    Triple (ReplayValues active swap sub L C W S X Y) (controlledHalf active L.unary p)
      (ReplayValues active swap sub L C W S (if C then halveMod p X else X) Y) := by
  intro s m h
  have hn := unary_nodup active L (control_nodup active swap sub L hnd active (by simp))
  obtain ⟨hf,hv⟩ := controlledHalf_spec active L.unary n p X C (L.unary_widths n hw) hn hp hpn hX
    s m ⟨⟨h.1,h.2.2.2.1⟩,h.2.2.2.2.2⟩
  simp only [Holds.holds] at hv
  have keep (q : Wire) (hq : q∉L.z) :=
    controlledHalf_frame active L.unary n p X C (L.unary_widths n hw) hn hp hpn hX
      s m h.1 h.2.2.2.1 h.2.2.2.2.2 q hq
  refine ⟨hf,hv.1.1,
    (keep swap (control_outside active swap sub L hnd swap (by simp)).1).trans h.2.1,
    (keep sub (control_outside active swap sub L hnd sub (by simp)).1).trans h.2.2.1,
    hv.1.2,?_,hv.2⟩
  apply Eq.trans (regValue_congr _ _ _ ?_) h.2.2.2.2.1
  intro q hq
  apply keep q
  intro hz
  have ht := List.nodup_iff_count.mp (control_nodup active swap sub L hnd active (by simp)) q
  have ha := List.count_pos_iff.mpr hq
  have hb := List.count_pos_iff.mpr hz
  simp only [ModInPlaceLayout.wires,List.count_append,List.count_cons] at ht
  omega


theorem double_step (active swap sub : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) :
    Triple (ReplayValues active swap sub L C W S X Y) (controlledDouble active L.unary p)
      (ReplayValues active swap sub L C W S (if C then (2*X)%p else X) Y) := by
  intro s m h
  have hn := unary_nodup active L (control_nodup active swap sub L hnd active (by simp))
  obtain ⟨hf,hv⟩ := controlledDouble_spec active L.unary n p X C (L.unary_widths n hw) hn hp hpn hX
    s m ⟨⟨h.1,h.2.2.2.1⟩,h.2.2.2.2.2⟩
  simp only [Holds.holds] at hv
  have keep (q : Wire) (hq : q∉L.z) :=
    controlledDouble_frame active L.unary n p X C (L.unary_widths n hw) hn hp hpn hX
      s m h.1 h.2.2.2.1 h.2.2.2.2.2 q hq
  refine ⟨hf,hv.1.1,
    (keep swap (control_outside active swap sub L hnd swap (by simp)).1).trans h.2.1,
    (keep sub (control_outside active swap sub L hnd sub (by simp)).1).trans h.2.2.1,
    hv.1.2,?_,hv.2⟩
  apply Eq.trans (regValue_congr _ _ _ ?_) h.2.2.2.2.1
  intro q hq
  apply keep q
  intro hz
  have ht := List.nodup_iff_count.mp (control_nodup active swap sub L hnd active (by simp)) q
  have ha := List.count_pos_iff.mpr hq
  have hb := List.count_pos_iff.mpr hz
  simp only [ModInPlaceLayout.wires,List.count_append,List.count_cons] at ht
  omega

end ReplayValues
end ECDSAAdd.Arithmetic
