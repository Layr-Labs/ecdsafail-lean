import ECDSAAdd.Arithmetic.Paper935.BankCompilerTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- Exact allocation balance includes the wires actually returned by shrinking,
so later scratch budgets can use the released space. -/
theorem planRowResize_card (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) :
    B.live.card+r.payload.length=A.live.card+width := by
  unfold planRowResize at h
  split at h
  next valid =>
    split at h
    next grow =>
      obtain ⟨⟨D,qs⟩,borrow,he⟩ := Option.bind_eq_some_iff.mp h
      cases he
      have card := (A.borrowMany_live B _ qs borrow).2
      omega
    next shrink =>
      cases h
      have subset : (r.payload.drop width).toFinset⊆A.live := by
        intro q hq
        exact valid.2 (List.mem_toFinset.mpr (List.mem_cons_of_mem _
          (List.mem_of_mem_drop (List.mem_toFinset.mp hq))))
      have nodup : (r.payload.drop width).Nodup :=
        List.Pairwise.sublist (List.drop_sublist width r.payload) (List.nodup_cons.mp valid.1).2
      have dropCard : (r.payload.drop width).toFinset.card=r.payload.length-width := by
        rw [List.toFinset_card_of_nodup nodup,List.length_drop]
      have bounded := Finset.card_le_card subset
      rw [dropCard] at bounded
      change (A.live\(r.payload.drop width).toFinset).card+r.payload.length=A.live.card+width
      rw [Finset.card_sdiff_of_subset subset,dropCard]
      omega
  next invalid => simp at h

/-- Exact final live count of the actual ordered bank planner. -/
theorem planWindowRows_card (requests : List (WindowRow × Nat)) (A C : Arena)
    (outs : List WindowRow) (p : Program) (h : planWindowRows A requests=some (C,outs,p)) :
    C.live.card+(requests.map (fun r => r.1.payload.length)).sum=
      A.live.card+(requests.map Prod.snd).sum := by
  induction requests generalizing A C outs p with
  | nil => cases h; simp
  | cons request rest ih =>
    rcases request with ⟨row,width⟩
    rw [planWindowRows] at h
    split at h
    next inputCheck =>
      obtain ⟨⟨B,out,pf⟩,first,h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨D,tail,q⟩,remaining,h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      next outputCheck =>
        cases h
        have firstCard := planRowResize_card A B row out width pf first
        have remainingCard := ih B C tail q remaining
        simp only [List.map_cons,List.sum_cons]
        omega
      next invalid => simp at h
    next invalid => simp at h

end ECDSAAdd.Arithmetic.Paper935
