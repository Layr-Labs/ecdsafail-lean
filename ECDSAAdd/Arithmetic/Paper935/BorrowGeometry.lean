import ECDSAAdd.Arithmetic.Paper935.HistoryCompilerTotal

namespace ECDSAAdd.Arithmetic.Paper935

theorem Arena.borrowMany_live (A B : Arena) (n : Nat) (work : List Wire)
    (h : A.borrowMany n=some (B,work)) :
    B.live=A.live∪work.toFinset ∧ B.live.card=A.live.card+n := by
  have hc := A.borrowMany_contract B n work h
  have hv := (A.reserve_success work.toFinset).mp ⟨B,hc.2.2⟩
  have live : B.live=A.live∪work.toFinset := by
    have he := hc.2.2
    simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
    cases he
    rfl
  refine ⟨live,?_⟩
  rw [live,Finset.card_union_of_disjoint hv.2,List.toFinset_card_of_nodup hc.2.1,hc.1]

theorem Arena.borrowMany_append (A B : Arena) (n : Nat) (work xs : List Wire)
    (h : A.borrowMany n=some (B,work)) (distinct : xs.Nodup) (owned : xs.toFinset⊆A.live) :
    (xs++work).Nodup ∧ (xs++work).toFinset⊆B.live := by
  have hc := A.borrowMany_contract B n work h
  have hv := (A.reserve_success work.toFinset).mp ⟨B,hc.2.2⟩
  have live := (A.borrowMany_live B n work h).1
  constructor
  · apply List.nodup_append'.mpr
    exact ⟨distinct,hc.2.1,List.disjoint_left.mpr (fun q hx hw =>
      Finset.disjoint_left.mp hv.2 (owned (List.mem_toFinset.mpr hx)) (List.mem_toFinset.mpr hw))⟩
  · rw [live,List.toFinset_append]
    exact Finset.union_subset_union owned (Finset.Subset.refl _)

end ECDSAAdd.Arithmetic.Paper935
