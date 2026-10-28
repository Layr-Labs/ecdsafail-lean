import ECDSAAdd.Arithmetic.Paper935.ProbeCompilerReady

namespace ECDSAAdd.Arithmetic.Paper935

/-- Support of the real gates includes all shared work and block flags. -/
theorem compileProbe_support (one target : Wire) (inputs work : List Wire) (width : Nat)
    (bs : List BlockedZero.Block) (h : compileProbe one target inputs work width=some bs) :
    wires (BlockedZero.program one target bs)⊆(one::target::(inputs++work)).toFinset := by
  have hc := compileProbe_contract one target inputs work width bs h
  have hw := compileProbe_work one target inputs work width bs h
  apply (BlockedZero.support one target bs).trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
  rcases hq with rfl|rfl|hq
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · apply Or.inr ∘ Or.inr
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    simp only [BlockedZero.Block.ports,List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact List.mem_append_right _ (hw.1 b hb)
    · obtain ⟨x,hx,hq⟩ := List.mem_flatMap.mp hq
      simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl
      · apply List.mem_append_left
        rw [← hc.2]
        exact List.mem_flatMap.mpr ⟨b,hb,List.mem_map.mpr ⟨x,hx,rfl⟩⟩
      · exact List.mem_append_right _ (hw.2 b hb x hx)

theorem compileBorrowedProbe_support (A D : Arena) (one target : Wire)
    (inputs work : List Wire) (width : Nat) (bs : List BlockedZero.Block)
    (h : compileBorrowedProbe A one target inputs width=some (D,work,bs))
    (owned : (one::target::inputs).toFinset⊆A.live) :
    D.live.card=A.live.card+(width+(inputs.toChunks width).length) ∧
    wires (BlockedZero.program one target bs)⊆D.live := by
  have pair := compileBorrowedProbe_contract A D one target inputs work width bs h
  have hc := A.borrowMany_contract D _ work pair.1
  have hv := (A.reserve_success work.toFinset).mp ⟨D,hc.2.2⟩
  have live : D.live=A.live∪work.toFinset := by
    have he := hc.2.2
    simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
    cases he
    rfl
  constructor
  · rw [live,Finset.card_union_of_disjoint hv.2,List.toFinset_card_of_nodup hc.2.1,hc.1]
  · apply (compileProbe_support one target inputs work width bs pair.2).trans
    rw [live]
    intro q hq
    have split : q∈(one::target::inputs) ∨ q∈work := by
      simpa only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] using hq
    exact split.elim (fun h => Finset.mem_union_left _ (owned (List.mem_toFinset.mpr h)))
      (fun h => Finset.mem_union_right _ (List.mem_toFinset.mpr h))

end ECDSAAdd.Arithmetic.Paper935
