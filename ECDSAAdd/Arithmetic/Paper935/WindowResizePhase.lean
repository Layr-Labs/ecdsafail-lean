import ECDSAAdd.Arithmetic.Paper935.WindowBank

namespace ECDSAAdd.Arithmetic.Paper935

theorem planRowResize_phase (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) (s : State) (m : List Bool) :
    (run p m s).phase=s.phase := by
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
        cases h
        exact (growRow_frame r.sign qs s m).1
    next shrink => cases h; exact (shrinkRow_frame r.sign _ s m).1
  next invalid => simp at h

theorem planWindowRows_phase (requests : List (WindowRow × Nat))
    (A C : Arena) (outs : List WindowRow) (p : Program)
    (h : planWindowRows A requests=some (C,outs,p)) (s : State) (m : List Bool) :
    (run p m s).phase=s.phase := by
  induction requests generalizing A C outs p s m with
  | nil =>
    simp only [planWindowRows,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩; rfl
  | cons request rest ih =>
    rcases request with ⟨row,width⟩
    simp only [planWindowRows] at h
    split at h
    next valid =>
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
          next valid' =>
            cases h
            rw [run_append,run_take]
            exact (ih B C ot pt ht _ _).trans (planRowResize_phase A B row out width pf hf s m)
          next valid' => simp at h
    next valid => simp at h

theorem WindowBank.resize_phase (b out : WindowBank) (w : RowWindow)
    (A C : Arena) (p : Program) (h : b.Planned out w A C p) (s : State) (m : List Bool) :
    (run p m s).phase=s.phase := planWindowRows_phase (b.requests w) A C out.rows p h s m

end ECDSAAdd.Arithmetic.Paper935
