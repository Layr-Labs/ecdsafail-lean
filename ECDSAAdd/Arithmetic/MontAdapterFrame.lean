import ECDSAAdd.Arithmetic.MontAdapterResources

namespace ECDSAAdd.Arithmetic

private theorem montFrame_values (M : MontLayout) (extra : List Wire) (P : Program) (s : State) (m : List Bool)
    (hs : wires P⊆(extra++M.wires).toFinset)
    (he : ∀q∈extra, (run P m s).basis q=s.basis q)
    (hx : regValue M.x (run P m s).basis=regValue M.x s.basis)
    (hy : regValue M.y (run P m s).basis=regValue M.y s.basis)
    (hc : regValue M.work (run P m s).basis=regValue M.work s.basis)
    (q : Wire) (hq : q∉M.out) : (run P m s).basis q=s.basis q := by
  by_cases hqe : q∈extra
  · exact he q hqe
  by_cases hqx : q∈M.x
  · exact (regValue_eq_iff _ _ _).mp hx q hqx
  by_cases hqy : q∈M.y
  · exact (regValue_eq_iff _ _ _).mp hy q hqy
  by_cases hqc : q∈M.work
  · exact (regValue_eq_iff _ _ _).mp hc q hqc
  apply run_preserves_outside
  intro h
  have hh := hs h
  simp [MontLayout.wires,hqe,hqx,hqy,hqc,hq] at hh


theorem montMulXor_frame (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (s : State) (m : List Bool)
    (hx : regValue M.x s.basis=X) (hy : regValue M.y s.basis=Y)
    (ho : regValue M.out s.basis=O) (hc : regValue M.work s.basis=0)
    (q : Wire) (hq : q∉M.out) : (run (montMulXor M p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := montMulXor_spec M p X Y O hw hnd hp hp16 hX hY s m ⟨⟨⟨hx,hy⟩,ho⟩,hc⟩
  have hs : wires (montMulXor M p)⊆([]++M.wires).toFinset := by
    rw [(montAdapter_wires M p hw).1]
    intro w hw'
    exact List.mem_toFinset.mpr ((((List.take_sublist 256 M.x).append (List.Sublist.refl M.y)).append
      (List.Sublist.refl M.out) |>.append (List.Sublist.refl M.work)).subset (List.mem_toFinset.mp hw'))
  exact montFrame_values M [] _ s m hs (by simp)
    (h.1.1.1.trans hx.symm) (h.1.1.2.trans hy.symm) (h.2.trans hc.symm) q hq

theorem montMulAdd_frame (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (hO : O<p) (s : State) (m : List Bool)
    (hx : regValue M.x s.basis=X) (hy : regValue M.y s.basis=Y)
    (ho : regValue M.out s.basis=O) (hc : regValue M.work s.basis=0)
    (q : Wire) (hq : q∉M.out) : (run (montMulAdd M p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := montMulAdd_spec M p X Y O hw hnd hp hp16 hX hY hO s m ⟨⟨⟨hx,hy⟩,ho⟩,hc⟩
  have hs : wires (montMulAdd M p)⊆([]++M.wires).toFinset := by
    rw [(montAdapter_wires M p hw).2.1]
    intro w hw'
    exact List.mem_toFinset.mpr ((((List.take_sublist 256 M.x).append (List.Sublist.refl M.y)).append
      (List.Sublist.refl M.out) |>.append (List.Sublist.refl M.work)).subset (List.mem_toFinset.mp hw'))
  exact montFrame_values M [] _ s m hs (by simp)
    (h.1.1.1.trans hx.symm) (h.1.1.2.trans hy.symm) (h.2.trans hc.symm) q hq

theorem montMulSub_frame (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (hO : O<p) (s : State) (m : List Bool)
    (hx : regValue M.x s.basis=X) (hy : regValue M.y s.basis=Y)
    (ho : regValue M.out s.basis=O) (hc : regValue M.work s.basis=0)
    (q : Wire) (hq : q∉M.out) : (run (montMulSub M p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := montMulSub_spec M p X Y O hw hnd hp hp16 hX hY hO s m ⟨⟨⟨hx,hy⟩,ho⟩,hc⟩
  have hs : wires (montMulSub M p)⊆([]++M.wires).toFinset := by
    rw [(montAdapter_wires M p hw).2.2]
    intro w hw'
    exact List.mem_toFinset.mpr ((((List.take_sublist 256 M.x).append (List.Sublist.refl M.y)).append
      (List.Sublist.refl M.out) |>.append (List.Sublist.refl M.work)).subset (List.mem_toFinset.mp hw'))
  exact montFrame_values M [] _ s m hs (by simp)
    (h.1.1.1.trans hx.symm) (h.1.1.2.trans hy.symm) (h.2.trans hc.symm) q hq

theorem montMulControlledAdd_frame (c : Wire) (B : Bool) (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : (c::M.wires).Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (hO : O<p) (s : State) (m : List Bool)
    (hb : s.basis c=B) (hx : regValue M.x s.basis=X) (hy : regValue M.y s.basis=Y)
    (ho : regValue M.out s.basis=O) (hc : regValue M.work s.basis=0)
    (q : Wire) (hq : q∉M.out) : (run (montMulControlledAdd c M p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := montMulControlledAdd_spec c B M p X Y O hw hnd hp hp16 hX hY hO s m ⟨⟨⟨⟨hb,hx⟩,hy⟩,ho⟩,hc⟩
  have hs : wires (montMulControlledAdd c M p)⊆([c]++M.wires).toFinset := by
    rw [(montControlledAdapter_wires c M p hw).1]
    intro w hw'
    have hsub : (c::(M.x.take 256++M.y++M.out++M.work)).Sublist (c::M.wires) :=
      ((((List.take_sublist 256 M.x).append (List.Sublist.refl M.y)).append
        (List.Sublist.refl M.out)).append (List.Sublist.refl M.work)).cons_cons c
    apply List.mem_toFinset.mpr
    exact hsub.subset (by simpa only [List.cons_append] using List.mem_toFinset.mp hw')
  exact montFrame_values M [c] _ s m hs (by
      intro w hw'
      have hew : w=c := List.mem_singleton.mp hw'
      subst w
      exact h.1.1.1.1.trans hb.symm)
    (h.1.1.1.2.trans hx.symm) (h.1.1.2.trans hy.symm) (h.2.trans hc.symm) q hq

theorem montMulControlledSub_frame (c : Wire) (B : Bool) (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : (c::M.wires).Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (hO : O<p) (s : State) (m : List Bool)
    (hb : s.basis c=B) (hx : regValue M.x s.basis=X) (hy : regValue M.y s.basis=Y)
    (ho : regValue M.out s.basis=O) (hc : regValue M.work s.basis=0)
    (q : Wire) (hq : q∉M.out) : (run (montMulControlledSub c M p) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := montMulControlledSub_spec c B M p X Y O hw hnd hp hp16 hX hY hO s m ⟨⟨⟨⟨hb,hx⟩,hy⟩,ho⟩,hc⟩
  have hs : wires (montMulControlledSub c M p)⊆([c]++M.wires).toFinset := by
    rw [(montControlledAdapter_wires c M p hw).2]
    intro w hw'
    have hsub : (c::(M.x.take 256++M.y++M.out++M.work)).Sublist (c::M.wires) :=
      ((((List.take_sublist 256 M.x).append (List.Sublist.refl M.y)).append
        (List.Sublist.refl M.out)).append (List.Sublist.refl M.work)).cons_cons c
    apply List.mem_toFinset.mpr
    exact hsub.subset (by simpa only [List.cons_append] using List.mem_toFinset.mp hw')
  exact montFrame_values M [c] _ s m hs (by
      intro w hw'
      have hew : w=c := List.mem_singleton.mp hw'
      subst w
      exact h.1.1.1.1.trans hb.symm)
    (h.1.1.1.2.trans hx.symm) (h.1.1.2.trans hy.symm) (h.2.trans hc.symm) q hq

end ECDSAAdd.Arithmetic
