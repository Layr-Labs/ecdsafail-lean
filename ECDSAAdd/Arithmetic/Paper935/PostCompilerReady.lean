import ECDSAAdd.Arithmetic.Paper935.PostCompiler

namespace ECDSAAdd.Arithmetic.Paper935

private theorem zip_work (xs ws : List Wire) (b : ZeroBit)
    (h : b∈List.zipWith ZeroBit.mk xs ws) : b.work∈ws := by
  induction xs generalizing ws with
  | nil => simp at h
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      simp only [List.zipWith_cons_cons,List.mem_cons] at h
      rcases h with rfl|h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ws h)

theorem compilePost_scratch (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compilePost armed one zf frozen fire active inputs record work width offset=some P) :
    ∀ q∈P.scratch,q=zf ∨ q=fire ∨ q∈work := by
  have hc := compilePost_contract armed one zf frozen fire active inputs record work width offset P h
  unfold compilePost at h
  dsimp only at h
  split at h
  next valid =>
    cases h
    intro q hq
    simp only [WindowPostLayout.scratch,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|rfl|((hq|hq)|hq)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · apply Or.inr ∘ Or.inr
      cases work with
      | nil => exact (hc.2.2.2 rfl).elim
      | cons x xs => exact List.mem_cons_self
    · apply Or.inr ∘ Or.inr
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
      obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hb
      exact List.mem_of_mem_take (List.of_mem_zip hp).1
    · apply Or.inr ∘ Or.inr
      obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
      exact List.mem_of_mem_drop (BlockedZero.chunks_work _ _ b hb x hx)
    · apply Or.inr ∘ Or.inr
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
      exact List.mem_of_mem_drop (zip_work record (work.drop 1) b hb)
  next invalid => simp at h

theorem compilePost_identity (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compilePost armed one zf frozen fire active inputs record work width offset=some P) :
    P.armed=armed ∧ P.one=one ∧ P.zf=zf ∧ P.frozen=frozen ∧ P.fire=fire ∧ P.active=active ∧ P.offset=offset := by
  unfold compilePost at h
  dsimp only at h
  split at h
  next valid => cases h; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  next invalid => simp at h

/-- The two retained control bits have explicit zero requirements; all
additional work comes clean from the allocator, including shared probe work. -/
theorem compileBorrowedPost_ready (A D : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compileBorrowedPost A armed one zf frozen fire active inputs record width offset=some (D,work,P))
    (s : BasisState) (ready : A.Ready s) (hone : s one=true) (hzf : s zf=false) (hfire : s fire=false)
    (activity : s active= !s frozen) (oldOffset : armed=true → regValue record s<offset)
    (activeOffset : s frozen=false → regValue record s=0) : P.Ready s := by
  have pair := compileBorrowedPost_contract A D armed one zf frozen fire active inputs record work width offset P h
  have hc := compilePost_contract armed one zf frozen fire active inputs record work width offset P pair.2
  have ids := compilePost_identity armed one zf frozen fire active inputs record work width offset P pair.2
  have borrow := A.borrowMany_contract D _ work pair.1
  have clean := (A.reserve_ready D work.toFinset s ready borrow.2.2).2
  constructor
  · rw [ids.2.1]; exact hone
  · intro q hq
    rcases compilePost_scratch armed one zf frozen fire active inputs record work width offset P pair.2 q hq with rfl|rfl|hw
    · exact hzf
    · exact hfire
    · exact clean q (List.mem_toFinset.mpr hw)
  · rw [ids.2.2.2.2.2.1,ids.2.2.2.1]; exact activity
  · rw [ids.1,hc.2.2.1,ids.2.2.2.2.2.2]; exact oldOffset
  · rw [ids.2.2.2.1,hc.2.2.1]; exact activeOffset

end ECDSAAdd.Arithmetic.Paper935
