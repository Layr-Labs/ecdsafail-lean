import ECDSAAdd.Arithmetic.MontAdapterSpec

namespace ECDSAAdd.Arithmetic

theorem montAdapter_counts (M : MontLayout) (p : Nat) (hw : M.Widths) (hnd : M.wires.Nodup) :
    (toffoliCount (montMulXor M p)=379424 ∧ measurementCount (montMulXor M p)=379424) ∧
    (toffoliCount (montMulAdd M p)=380447 ∧ measurementCount (montMulAdd M p)=380447) ∧
    (toffoliCount (montMulSub M p)=380959 ∧ measurementCount (montMulSub M p)=380959) := by
  have h := montPQ_counts M p hw
  have hc := copyRegister_counts none M.product M.out (by simp [MontLayout.product,hw.z,hw.out])
  have ha := modAddInPlace_resources M.addView 256 p (M.add_widths hw) (M.add_nodup hw hnd) (by omega)
  have hs := modSubInPlace_resources M.addView 256 p (M.add_widths hw) (M.add_nodup hw hnd) (by omega)
  simp only [montMulXor,montMulAdd,montMulSub,toffoliCount_append,measurementCount_append,
    h.1.1,h.1.2,h.2.1,h.2.2,hc.1,hc.2,ha.1,ha.2.1,hs.1,hs.2.1,
    Option.isSome_none,Bool.false_eq_true,if_false]
  norm_num

theorem montControlledAdapter_counts (c : Wire) (M : MontLayout) (p : Nat)
    (hw : M.Widths) (hnd : (c::M.wires).Nodup) :
    (toffoliCount (montMulControlledAdd c M p)=380959 ∧ measurementCount (montMulControlledAdd c M p)=380447) ∧
    (toffoliCount (montMulControlledSub c M p)=381471 ∧ measurementCount (montMulControlledSub c M p)=380959) := by
  have h := montPQ_counts M p hw
  have hn := MontLayout.controlled_add_nodup c M hw hnd
  have ha := controlledModAdd_resources c M.addView 256 p (M.add_widths hw) hn (by omega)
  have hs := controlledModSub_resources c M.addView 256 p (M.add_widths hw) hn (by omega)
  simp only [montMulControlledAdd,montMulControlledSub,toffoliCount_append,measurementCount_append,
    h.1.1,h.1.2,h.2.1,h.2.2,ha.1,ha.2.1,hs.1,hs.2.1]
  norm_num

private theorem middle_union (S T O : Finset Wire) (hlo : O⊆T) (hup : T⊆S∪O) : S∪T∪S=S∪O := by
  ext w
  have hl := @hlo w
  have hu := @hup w
  simp only [Finset.mem_union] at hu ⊢
  tauto

/-- 三个中段都完整触及输出；其余线路均来自P/Q已有工作区。 -/
theorem montAdapter_wires (M : MontLayout) (p : Nat) (hw : M.Widths) :
    wires (montMulXor M p)=(M.x.take 256++M.y++M.out++M.work).toFinset ∧
    wires (montMulAdd M p)=(M.x.take 256++M.y++M.out++M.work).toFinset ∧
    wires (montMulSub M p)=(M.x.take 256++M.y++M.out++M.work).toFinset := by
  let S := (M.x.take 256++M.y++M.work).toFinset
  have hpq := montPQ_wires M p hw
  have hcore : M.addView.toModAddCoreLayout.work⊆M.work := by
    intro w h
    have hm : w∈M.addView.work := by simp [ModInPlaceLayout.work,h]
    have hs := M.add_work_subset hw hm
    simp [MontLayout.work,hs]
  have hprod : M.product⊆M.work := by
    intro w h
    have hz : w∈M.z := List.mem_of_mem_take h
    simp [MontLayout.work,MontLayout.activeZ,hz]
  have hshape : M.addView.toModAddCoreLayout.wires=M.product++M.out++M.addView.toModAddCoreLayout.work := by
    change M.product++M.addView.z++_=_
    rw [(M.add_ports hw).2]
  have ha := modAddCore_wires M.addView.toModAddCoreLayout 256 p (M.add_widths hw).core (by omega)
  have hs := modSubInPlace_wires M.addView 256 p (M.add_widths hw) (by omega)
  rw [hshape] at ha hs
  have hc := copyRegister_wires none M.product M.out (by simp [MontLayout.product,hw.z,hw.out])
  have hn : M.product≠[] := by intro he; have hl := congrArg List.length he; simp [MontLayout.product,hw.z] at hl
  simp only [List.isEmpty_iff,hn,if_false,Option.toList_none,List.nil_append] at hc
  have hcopy : S∪wires (copyRegister none M.product M.out)∪S=S∪M.out.toFinset := by
    rw [hc]
    apply middle_union
    · intro w h; simp only [List.mem_toFinset,List.mem_append] at h ⊢; exact Or.inr h
    · intro w h
      simp only [S,List.mem_toFinset,List.mem_append,Finset.mem_union] at h ⊢
      rcases h with h|h
      · exact Or.inl (Or.inr (hprod h))
      · exact Or.inr h
  have hmod : S∪(M.product++M.out++M.addView.toModAddCoreLayout.work).toFinset∪S=S∪M.out.toFinset := by
    apply middle_union
    · intro w h; simp only [List.mem_toFinset,List.mem_append] at h ⊢; exact Or.inl (Or.inr h)
    · intro w h
      simp only [S,List.mem_toFinset,List.mem_append,Finset.mem_union] at h ⊢
      rcases h with (h|h)|h
      · exact Or.inl (Or.inr (hprod h))
      · exact Or.inr h
      · exact Or.inl (Or.inr (hcore h))
  have hout : S∪M.out.toFinset=(M.x.take 256++M.y++M.out++M.work).toFinset := by
    simp only [S,List.toFinset_append]
    ac_rfl
  simpa only [montMulXor,montMulAdd,montMulSub,modAddInPlace,wires_append,hpq.1,hpq.2,ha,hs]
    using ⟨hcopy.trans hout,hmod.trans hout,hmod.trans hout⟩



theorem montControlledAdapter_wires (c : Wire) (M : MontLayout) (p : Nat) (hw : M.Widths) :
    wires (montMulControlledAdd c M p)=(c::M.x.take 256++M.y++M.out++M.work).toFinset ∧
    wires (montMulControlledSub c M p)=(c::M.x.take 256++M.y++M.out++M.work).toFinset := by
  let S := (M.x.take 256++M.y++M.work).toFinset
  have hshared : M.shared⊆M.work := by intro w h; simp [MontLayout.work,h]
  have hmask : M.addView.mask⊆M.work := by
    intro w h
    apply hshared
    have hh : w∈M.addView.work := by simp [ModInPlaceLayout.work,h]
    exact M.add_work_subset hw hh
  have hcore : M.addView.toModAddCoreLayout.work⊆M.work := by
    intro w h
    apply hshared
    exact M.add_work_subset hw (by simp [ModInPlaceLayout.work,h])
  have hprod : M.product⊆M.work := by
    intro w h
    have hz : w∈M.z := List.mem_of_mem_take h
    simp [MontLayout.work,MontLayout.activeZ,hz]
  have hcombine (r : List Wire) (hr : r⊆M.work) :
      S∪(c::r++M.addView.mask++M.out++M.addView.toModAddCoreLayout.work).toFinset∪S=
      (c::M.x.take 256++M.y++M.out++M.work).toFinset := by
    ext w
    have h1 := @hr w
    have h2 := @hmask w
    have h3 := @hcore w
    simp only [S,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  have hv : M.addView.maskedCore.wires=M.addView.mask++M.out++M.addView.toModAddCoreLayout.work := by
    change M.addView.mask++M.addView.z++_=_
    rw [(M.add_ports hw).2]
    rfl
  have ha := controlledModAdd_wires c M.addView 256 p (M.add_widths hw) (by omega)
  have hs := controlledModSub_wires c M.addView 256 p (M.add_widths hw) (by omega)
  rw [hv] at ha hs
  have hpq := montPQ_wires M p hw
  simp only [montMulControlledAdd,montMulControlledSub,wires_append,hpq.1,hpq.2,ha,hs]
  simpa only [S,List.cons_append,List.append_assoc,(M.add_ports hw).1] using
    And.intro (hcombine (M.product.take 256) (fun _ h => hprod (List.mem_of_mem_take h))) (hcombine M.product hprod)

theorem montAdapter_qubits (M : MontLayout) (p : Nat) (hw : M.Widths) (hnd : M.wires.Nodup) :
    qubitCount (montMulXor M p)=2596 ∧ qubitCount (montMulAdd M p)=2596 ∧ qubitCount (montMulSub M p)=2596 := by
  have hn : (M.x.take 256++M.y++M.out++M.work).Nodup :=
    (((List.take_sublist 256 M.x).append (List.Sublist.refl M.y)).append (List.Sublist.refl M.out)).append
      (List.Sublist.refl M.work) |>.nodup hnd
  have hcard : (M.x.take 256++M.y++M.out++M.work).toFinset.card=2596 := by
    rw [List.toFinset_card_of_nodup hn]
    simp [hw.x,hw.y,hw.out,M.work_length hw]
  have hs := montAdapter_wires M p hw
  simp only [qubitCount,hs.1,hs.2.1,hs.2.2,hcard,and_self]

theorem montControlledAdapter_qubits (c : Wire) (M : MontLayout) (p : Nat)
    (hw : M.Widths) (hnd : (c::M.wires).Nodup) :
    qubitCount (montMulControlledAdd c M p)=2597 ∧ qubitCount (montMulControlledSub c M p)=2597 := by
  have hn : (c::(M.x.take 256++M.y++M.out++M.work)).Nodup := by
    apply List.Sublist.nodup _ hnd
    exact ((((List.take_sublist 256 M.x).append (List.Sublist.refl M.y)).append
      (List.Sublist.refl M.out)).append (List.Sublist.refl M.work)).cons_cons c
  have hcard : (c::M.x.take 256++M.y++M.out++M.work).toFinset.card=2597 := by
    simp only [List.cons_append]
    rw [List.toFinset_card_of_nodup hn]
    simp [hw.x,hw.y,hw.out,M.work_length hw]
  have hs := montControlledAdapter_wires c M p hw
  simp only [qubitCount,hs.1,hs.2,hcard,and_self]

end ECDSAAdd.Arithmetic
