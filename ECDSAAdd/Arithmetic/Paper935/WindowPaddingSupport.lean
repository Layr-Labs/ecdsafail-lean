import ECDSAAdd.Arithmetic.Paper935.WindowBank

namespace ECDSAAdd.Arithmetic.Paper935

/-- A retained old wire outside the resized row cannot be a padding input or
target. This is a support statement, stronger than a basis-value frame. -/
theorem planRowResize_support_away (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) (q : Wire)
    (hq : q∈A.live) (away : q∉r.wires) : q∉wires p := by
  unfold planRowResize at h
  split at h
  next valid =>
    split at h
    next grow =>
      cases hb : A.borrowMany (width-r.payload.length) with
      | none => simp [hb] at h
      | some result =>
        rcases result with ⟨C,qs⟩
        simp only [hb] at h
        rcases h with ⟨rfl,rfl,rfl⟩
        have hc := A.borrowMany_contract C _ qs hb
        have hv := (A.reserve_success qs.toFinset).mp ⟨C,hc.2.2⟩
        intro member
        rcases Finset.mem_insert.mp (growRow_support r.sign qs member) with he|he
        · exact away (by simp [WindowRow.wires,he])
        · exact Finset.disjoint_left.mp hv.2 hq he
    next shrink =>
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      rw [shrinkRow_eq]
      intro member
      rcases Finset.mem_insert.mp (growRow_support r.sign (r.payload.drop width).reverse member) with he|he
      · exact away (by simp [WindowRow.wires,he])
      · apply away
        exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_reverse.mp (List.mem_toFinset.mp he)))
  next invalid => simp at h

theorem planWindowRows_support_away (requests : List (WindowRow × Nat))
    (A C : Arena) (outs : List WindowRow) (p : Program)
    (h : planWindowRows A requests=some (C,outs,p)) (q : Wire)
    (hq : q∈A.live) (away : q∉(requests.map Prod.fst).flatMap WindowRow.wires) : q∉wires p := by
  induction requests generalizing A C outs p with
  | nil =>
    simp only [planWindowRows,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    simp [wires]
  | cons request rest ih =>
    rcases request with ⟨row,width⟩
    have sep : q∉row.wires ∧ q∉(rest.map Prod.fst).flatMap WindowRow.wires := by
      simpa only [List.map_cons,List.flatMap_cons,List.mem_append,not_or] using away
    simp only [planWindowRows] at h
    split at h
    next hv =>
      cases hf : planRowResize A row width with
      | none => simp [hf] at h
      | some first =>
        rcases first with ⟨B,out,pf⟩
        simp only [hf] at h
        dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd] at h
        cases ht : planWindowRows B rest with
        | none => simp [ht] at h
        | some tail =>
          rcases tail with ⟨D,ot,pt⟩
          simp only [ht] at h
          split at h
          next hv' =>
            cases h
            have owned := (planRowResize_locality A B row out width pf hf
              ⟨false,fun _ => false⟩ [] q hq sep.1).1
            have first := planRowResize_support_away A B row out width pf hf q hq sep.1
            have last := ih B C ot pt ht owned sep.2
            simpa only [wires_append,Finset.mem_union,not_or] using And.intro first last
          next hv' => simp at h
    next hv => simp at h

theorem WindowBank.padding_support_away (b out : WindowBank) (w : RowWindow)
    (A C : Arena) (p : Program) (h : b.Planned out w A C p)
    (q : Wire) (hq : q∈A.live) (away : q∉b.rows.flatMap WindowRow.wires) : q∉wires p := by
  apply planWindowRows_support_away (b.requests w) A C out.rows p h q hq
  simpa only [WindowBank.requests,WindowBank.rows,List.map_cons,List.map_nil] using away

end ECDSAAdd.Arithmetic.Paper935
