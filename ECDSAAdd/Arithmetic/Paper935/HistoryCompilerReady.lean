import ECDSAAdd.Arithmetic.Paper935.HistoryCompiler

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

theorem compileHistory_identity (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire) (H : HistoryLayout)
    (h : compileHistory one zz pos sign output port frozen counter coeffBits record work=some H) :
    H.one=one ∧ H.zz=zz ∧ H.pos=pos ∧ H.sign=sign ∧ H.output=output ∧ H.port=port := by
  unfold compileHistory at h
  dsimp only at h
  split at h
  next valid => cases h; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  next invalid => simp at h

theorem compileHistory_work (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire) (H : HistoryLayout)
    (h : compileHistory one zz pos sign output port frozen counter coeffBits record work=some H) :
    (∀ b∈H.zb,b.work∈work) ∧ (∀ b∈H.frozen::H.positive::H.low,b.work∈work) := by
  have hc := compileHistory_contract one zz pos sign output port frozen counter coeffBits record work H h
  unfold compileHistory at h
  dsimp only at h
  split at h
  next valid =>
    cases h
    constructor
    · exact fun b hb => zip_work counter work b hb
    · intro b hb
      simp only [historyCandidate,List.mem_cons] at hb
      rcases hb with rfl|rfl|hb
      · cases work with
        | nil => simp at hc
        | cons w ws => exact List.mem_cons_self
      · cases work with
        | nil => simp at hc
        | cons w ws =>
          cases ws with
          | nil => simp at hc
          | cons v vs => exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_of_mem_drop (zip_work coeffBits (work.drop 2) b hb)
  next invalid => simp at h

/-- Initial detector work is derived from the allocator, not supplied as an
execution oracle. Only the three reused persistent controls require zero input. -/
theorem compileGrowingHistory_ready (A B D : Arena) (record work : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H))
    (hn : record.Nodup) (ho : record.toFinset⊆A.live) (s : BasisState) (ready : A.Ready s)
    (hone : s one=true) (hzz : s zz=false) (hpos : s pos=false) (hout : s output=false) :
    D.Ready s ∧ s H.one=true ∧ s H.zz=false ∧ s H.pos=false ∧ s H.output=false ∧
    (∀ b∈H.zb,s b.work=false) ∧ (∀ b∈H.frozen::H.positive::H.low,s b.work=false) := by
  have hc := compileGrowingHistory_contract A B D record work capacity one zz pos sign output port frozen counter coeffBits H h
  have grow := planHistoryGrow_correct A B record H.record capacity hc.1 hn ho s ready
  have borrow := B.borrowMany_contract D _ work hc.2.1
  have clean := B.reserve_ready D work.toFinset s grow.2.2.2.1 borrow.2.2
  have ids := compileHistory_identity one zz pos sign output port frozen counter coeffBits H.record work H hc.2.2
  have scratch := compileHistory_work one zz pos sign output port frozen counter coeffBits H.record work H hc.2.2
  refine ⟨clean.1,?_,?_,?_,?_,?_,?_⟩
  · rw [ids.1]; exact hone
  · rw [ids.2.1]; exact hzz
  · rw [ids.2.2.1]; exact hpos
  · rw [ids.2.2.2.2.1]; exact hout
  · exact fun b hb => clean.2 b.work (List.mem_toFinset.mpr (scratch.1 b hb))
  · exact fun b hb => clean.2 b.work (List.mem_toFinset.mpr (scratch.2 b hb))

end ECDSAAdd.Arithmetic.Paper935
