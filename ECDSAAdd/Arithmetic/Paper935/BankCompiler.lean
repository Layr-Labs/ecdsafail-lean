import ECDSAAdd.Arithmetic.Paper935.WindowBank

namespace ECDSAAdd.Arithmetic.Paper935

def bankOfRows : List WindowRow → Option WindowBank
  | [f,g,fv,gv] => some ⟨f,g,fv,gv⟩
  | _ => none

theorem bankOfRows_contract (rows : List WindowRow) (b : WindowBank)
    (h : bankOfRows rows=some b) : b.rows=rows := by
  cases rows with
  | nil => simp [bankOfRows] at h
  | cons f rest =>
    cases rest with
    | nil => simp [bankOfRows] at h
    | cons g rest =>
      cases rest with
      | nil => simp [bankOfRows] at h
      | cons fv rest =>
        cases rest with
        | nil => simp [bankOfRows] at h
        | cons gv rest =>
          cases rest with
          | nil => cases h; rfl
          | cons x xs => simp [bankOfRows] at h

def compileBankResize (A : Arena) (b : WindowBank) (w : RowWindow) :
    Option (Arena × WindowBank × Program) := do
  let (C,rows,p) ← planWindowRows A (b.requests w)
  let out ← bankOfRows rows
  pure (C,out,p)

theorem compileBankResize_contract (A C : Arena) (b out : WindowBank) (w : RowWindow)
    (p : Program) (h : compileBankResize A b w=some (C,out,p)) : b.Planned out w A C p := by
  unfold compileBankResize at h
  cases hp : planWindowRows A (b.requests w) with
  | none => simp [hp] at h
  | some result =>
    rcases result with ⟨D,rows,q⟩
    simp only [hp] at h
    dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd] at h
    cases hb : bankOfRows rows with
    | none => simp [hb] at h
    | some bank =>
      simp only [hb] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      unfold WindowBank.Planned
      rw [bankOfRows_contract rows out hb]
      exact hp

/-- Packing the four planner outputs adds no quantum operation. -/
theorem compileBankResize_resources (A C : Arena) (b out : WindowBank) (w : RowWindow)
    (p : Program) (h : compileBankResize A b w=some (C,out,p)) :
    ProperProgram p ∧ toffoliCount p=0 ∧ measurementCount p=0 ∧ wires p⊆arenaWires :=
  b.resize_resources out w A C p (compileBankResize_contract A C b out w p h)

theorem planWindowRows_length (requests : List (WindowRow × Nat))
    (A C : Arena) (outs : List WindowRow) (p : Program)
    (h : planWindowRows A requests=some (C,outs,p)) : outs.length=requests.length := by
  induction requests generalizing A C outs p with
  | nil =>
    simp only [planWindowRows,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    rfl
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
            simp only [List.length_cons,ih B C ot pt ht]
          next hv' => simp at h
    next hv => simp at h

theorem bankOfRows_exists (rows : List WindowRow) (h : rows.length=4) :
    ∃ b,bankOfRows rows=some b := by
  cases rows with
  | nil => simp at h
  | cons f rest =>
    cases rest with
    | nil => simp at h
    | cons g rest =>
      cases rest with
      | nil => simp at h
      | cons fv rest =>
        cases rest with
        | nil => simp at h
        | cons gv rest =>
          cases rest with
          | nil => exact ⟨⟨f,g,fv,gv⟩,rfl⟩
          | cons x xs => simp at h

/-- Four-row packing cannot introduce a failure after successful planning. -/
theorem compileBankResize_exists (A C : Arena) (b : WindowBank) (w : RowWindow)
    (rows : List WindowRow) (p : Program)
    (h : planWindowRows A (b.requests w)=some (C,rows,p)) :
    ∃ out,compileBankResize A b w=some (C,out,p) := by
  have len := planWindowRows_length (b.requests w) A C rows p h
  obtain ⟨out,ho⟩ := bankOfRows_exists rows (by simpa [WindowBank.requests] using len)
  refine ⟨out,?_⟩
  simp only [compileBankResize,h]
  dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd]
  rw [ho]
  rfl

end ECDSAAdd.Arithmetic.Paper935
