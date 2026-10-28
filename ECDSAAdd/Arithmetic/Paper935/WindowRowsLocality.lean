import ECDSAAdd.Arithmetic.Paper935.PublicSlotStaticRun

namespace ECDSAAdd.Arithmetic.Paper935

/-- The actual sequential row planner preserves every pre-owned external bit,
for arbitrary states and measurement tapes. -/
theorem planWindowRows_external (requests : List (WindowRow × Nat))
    (A C : Arena) (outs : List WindowRow) (p : Program)
    (h : planWindowRows A requests=some (C,outs,p)) (s : State) (m : List Bool)
    (q : Wire) (owned : q∈A.live) (away : q∉(requests.map Prod.fst).flatMap WindowRow.wires) :
    q∈C.live ∧ q∉outs.flatMap WindowRow.wires ∧ (run p m s).basis q=s.basis q := by
  induction requests generalizing A C outs p s m with
  | nil =>
    simp only [planWindowRows,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    exact ⟨owned,by simp,rfl⟩
  | cons request rest ih =>
    rcases request with ⟨row,width⟩
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
            have noRow : q∉row.wires := by
              intro hq
              apply away
              simp [hq]
            have noRest : q∉(rest.map Prod.fst).flatMap WindowRow.wires := by
              intro hq
              apply away
              simp [hq]
            have first := planRowResize_locality A B row out width pf hf s m q owned noRow
            have tail := ih B C ot pt ht (run pf m s) (m.drop (measurementCount pf)) first.1 noRest
            have noOut : q∉out.wires := fun hq =>
              noRow (planRowResize_old_sites A B row out width pf hf q hq owned)
            refine ⟨tail.1,?_,?_⟩
            · simpa only [List.flatMap_cons,List.mem_append,not_or] using ⟨noOut,tail.2.1⟩
            · rw [run_append,run_take]
              exact tail.2.2.trans first.2
          next hv' => simp at h
    next hv => simp at h

theorem planWindowRows_locality (requests : List (WindowRow × Nat))
    (A C : Arena) (outs : List WindowRow) (p : Program)
    (h : planWindowRows A requests=some (C,outs,p)) (s : State) (m : List Bool)
    (q : Wire) (owned : q∈A.live) (away : q∉(requests.map Prod.fst).flatMap WindowRow.wires) :
    q∈C.live ∧ (run p m s).basis q=s.basis q := by
  have result := planWindowRows_external requests A C outs p h s m q owned away
  exact ⟨result.1,result.2.2⟩

/-- Bank packing preserves the same external-bit contract as the actual row planner. -/
theorem compileBankResize_external (A C : Arena) (b out : WindowBank) (width : RowWindow) (p : Program)
    (h : compileBankResize A b width=some (C,out,p)) (s : State) (m : List Bool)
    (q : Wire) (owned : q∈A.live) (away : q∉b.rows.flatMap WindowRow.wires) :
    q∈C.live ∧ q∉out.rows.flatMap WindowRow.wires ∧ (run p m s).basis q=s.basis q := by
  have planned := compileBankResize_contract A C b out width p h
  exact planWindowRows_external (b.requests width) A C out.rows p planned s m q owned
    (by simpa only [WindowBank.requests,WindowBank.rows,List.map_cons,List.map_nil] using away)

end ECDSAAdd.Arithmetic.Paper935
