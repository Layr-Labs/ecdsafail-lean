import ECDSAAdd.Arithmetic.ReplayCellProof

namespace ECDSAAdd.Arithmetic

private theorem swap_exact (c : Wire) (a b : List Wire) (hlen : a.length=b.length)
    (hne : a.isEmpty=false) : wires (swapRegisters c a b)=(c::a++b).toFinset := by
  have he : b.isEmpty=false := by
    cases a <;> cases b <;> simp_all
  simp only [swapRegisters,wires_append,copyRegister_wires _ _ _ hlen,
    copyRegister_wires _ _ _ hlen.symm,hne,he,Bool.false_eq_true,if_false]
  ext q; simp; tauto

/-- 正回放触及完整共享布局；反回放不触及源高位及 flag。 -/
theorem replayCell_wires (active swap sub : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    wires (replayCell active swap sub L p)=(active::swap::sub::L.wires).toFinset ∧
    wires (replayUncell active swap sub L p)=
      (active::swap::sub::L.a.take n++L.z++L.toModAddCoreLayout.work++L.mask).toFinset := by
  have hz : L.z.length=n+1 := by simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low]
  have hl : (L.z.take L.low.length).length=n := by simp [hw.core.low,hz]
  have hr : (L.a.take L.low.length).length=n := by simp [hw.core.low,hw.core.a]
  have he : (L.z.take L.low.length).isEmpty=false := by
    cases h : L.z.take L.low.length <;> simp_all
  have hs := swap_exact swap (L.z.take L.low.length) (L.a.take L.low.length) (hl.trans hr.symm) he
  have hu := controlledUnary_wires active L.unary n p (L.unary_widths n hw) hn
  constructor
  all_goals
    first
    | rw [replayCell, wires_append, wires_append, wires_append, hs,
        controlledModSub_wires sub L n p hw hn, hu.2]
    | rw [replayUncell, wires_append, wires_append, wires_append, hs,
        controlledModAdd_wires sub L n p hw hn, hu.1]
    ext q
  all_goals
    simp only [hw.core.low]
    have hza : q∈L.z.take n → q∈L.z := fun h => (List.take_sublist _ _).subset h
    have haa : q∈L.a.take n → q∈L.a := fun h => (List.take_sublist _ _).subset h
    simp only [ModInPlaceLayout.z,ModAddCoreLayout.z,List.mem_append,List.mem_singleton] at hza
    simp only [Finset.mem_union,List.mem_toFinset,ModInPlaceLayout.wires,ModInPlaceLayout.work,
      ModInPlaceLayout.unary,ModInPlaceLayout.maskedCore,ModUnaryLayout.z,ModUnaryLayout.core,
      ModInPlaceLayout.z,ModAddCoreLayout.wires,ModAddCoreLayout.z,ModAddCoreLayout.work,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    clear hs hu hl hr he hz hw hn
    aesop

theorem replayCell_qubits (active swap sub : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hnd : (active::swap::sub::L.wires).Nodup) (hn : 0<n) :
    qubitCount (replayCell active swap sub L p)=5*n+9 ∧
    qubitCount (replayUncell active swap sub L p)=5*n+7 := by
  have hr : (active::swap::sub::L.a.take n++L.z++L.toModAddCoreLayout.work++L.mask).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hh := List.nodup_iff_count.mp hnd q
    have ht := (List.take_sublist n L.a).count_le q
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,List.count_append,List.count_cons,
      List.count_nil] at hh ⊢
    omega
  constructor
  · rw [qubitCount,(replayCell_wires active swap sub L n p hw hn).1,List.toFinset_card_of_nodup hnd]
    simp [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.z,
      ModAddCoreLayout.work,ModAddCoreLayout.z,hw.core.a,hw.core.low,hw.core.constant,hw.core.carry,hw.mask]
    omega
  · rw [qubitCount,(replayCell_wires active swap sub L n p hw hn).2,List.toFinset_card_of_nodup hr]
    simp [ModInPlaceLayout.z,ModAddCoreLayout.work,ModAddCoreLayout.z,
      hw.core.a,hw.core.low,hw.core.constant,hw.core.carry,hw.mask]
    omega

/-- 从全记录规格与支持推出载荷之外逐线保持。 -/
private theorem cell_frame_of_spec (active swap sub : Wire) (L : ModInPlaceLayout)
    (C W S : Bool) (X Y U V : Nat) (circuit : Program)
    (hspec : Triple (ReplayValues active swap sub L C W S X Y) circuit
      (ReplayValues active swap sub L C W S U V))
    (hsupport : wires circuit ⊆ (active::swap::sub::L.wires).toFinset)
    (s : State) (m : List Bool) (h : ReplayValues active swap sub L C W S X Y s.basis)
    (q : Wire) (hz : q∉L.z) (ha : q∉L.a) : (run circuit m s).basis q=s.basis q := by
  obtain ⟨_,hv⟩ := hspec s m h
  by_cases h1 : q=active
  · subst q; exact hv.1.trans h.1.symm
  by_cases h2 : q=swap
  · subst q; exact hv.2.1.trans h.2.1.symm
  by_cases h3 : q=sub
  · subst q; exact hv.2.2.1.trans h.2.2.1.symm
  by_cases hw : q∈L.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.2.2.2.2.trans h.2.2.2.2.2.symm) q hw
  apply run_preserves_outside
  intro hm
  have hh := hsupport hm
  simp [ModInPlaceLayout.wires,h1,h2,h3,hz,ha,hw] at hh

theorem replayCell_frame (active swap sub : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) (s : State) (m : List Bool)
    (h : ReplayValues active swap sub L C W S X Y s.basis)
    (q : Wire) (hz : q∉L.z) (ha : q∉L.a) :
    (run (replayCell active swap sub L p) m s).basis q=s.basis q := by
  have hn : 0<n := by
    by_contra hh
    have he : n=0 := by omega
    rw [he] at hpn
    norm_num at hpn
    omega
  exact cell_frame_of_spec active swap sub L C W S X Y _ _ _
    (replayCell_spec active swap sub L n p X Y C W S hw hnd hp hpn hX hY)
    (by rw [(replayCell_wires active swap sub L n p hw hn).1]) s m h q hz ha

theorem replayUncell_frame (active swap sub : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C W S : Bool) (hw : L.Widths n)
    (hnd : (active::swap::sub::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) (s : State) (m : List Bool)
    (h : ReplayValues active swap sub L C W S X Y s.basis)
    (q : Wire) (hz : q∉L.z) (ha : q∉L.a) :
    (run (replayUncell active swap sub L p) m s).basis q=s.basis q := by
  have hn : 0<n := by
    by_contra hh
    have he : n=0 := by omega
    rw [he] at hpn
    norm_num at hpn
    omega
  apply cell_frame_of_spec active swap sub L C W S X Y _ _ _
    (replayUncell_spec active swap sub L n p X Y C W S hw hnd hp hpn hX hY) ?_ s m h q hz ha
  rw [(replayCell_wires active swap sub L n p hw hn).2]
  intro q hq
  have ht : q∈L.a.take n → q∈L.a := fun hm => (List.take_sublist _ _).subset hm
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,ModInPlaceLayout.wires,
    ModInPlaceLayout.work] at hq ⊢
  tauto

end ECDSAAdd.Arithmetic
