import ECDSAAdd.Arithmetic.Paper935.RowAllocation

namespace ECDSAAdd.Arithmetic.Paper935

/-- Extend the unsigned history register only to the current public capacity.
New high bits are already zero by the free-arena invariant; no reset gate is
inserted and no fixed maximum history bank is reserved ahead of time. -/
def planHistoryGrow (A : Arena) (record : List Wire) (width : Nat) :
    Option (Arena × List Wire) := do
  let (B,extra) ← A.borrowMany (width-record.length)
  pure (B,record++extra)

theorem planHistoryGrow_exists (A : Arena) (record : List Wire) (width : Nat)
    (hcap : A.live.card+(width-record.length)≤935) :
    ∃ B out,planHistoryGrow A record width=some (B,out) := by
  obtain ⟨B,extra,h⟩ := (A.borrowMany_capacity _).mpr hcap
  exact ⟨B,record++extra,by simp [planHistoryGrow,h]⟩

theorem planHistoryGrow_correct (A B : Arena) (record out : List Wire) (width : Nat)
    (h : planHistoryGrow A record width=some (B,out))
    (hn : record.Nodup) (ho : record.toFinset⊆A.live)
    (s : BasisState) (hr : A.Ready s) :
    out.length=max width record.length ∧ out.Nodup ∧ out.toFinset⊆B.live ∧
    B.Ready s ∧ regValue out s=regValue record s ∧
    B.live.card=A.live.card+(width-record.length) := by
  unfold planHistoryGrow at h
  cases hb : A.borrowMany (width-record.length) with
  | none => simp [hb] at h
  | some result =>
    rcases result with ⟨C,extra⟩
    simp only [hb] at h
    rcases h with ⟨rfl,rfl⟩
    have hc := A.borrowMany_contract C _ extra hb
    have hv := (A.reserve_success extra.toFinset).mp ⟨C,hc.2.2⟩
    have ready := A.reserve_ready C extra.toFinset s hr hc.2.2
    have live : C.live=A.live∪extra.toFinset := by
      have he := hc.2.2
      simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
      cases he
      rfl
    refine ⟨?_,?_,?_,ready.1,?_,?_⟩
    · simp only [List.length_append,hc.1]; omega
    · apply List.nodup_append.mpr
      refine ⟨hn,hc.2.1,?_⟩
      intro a ha b hb he
      subst b
      exact Finset.disjoint_left.mp hv.2 (ho (List.mem_toFinset.mpr ha)) (List.mem_toFinset.mpr hb)
    · rw [live,List.toFinset_append]
      exact Finset.union_subset_union ho (Finset.Subset.refl _)
    · have hz : regValue extra s=0 := (regValue_zero extra s).mpr
        (fun q hq => ready.2 q (List.mem_toFinset.mpr hq))
      simp only [regValue_append,hz,Nat.mul_zero,Nat.add_zero]
    · rw [live,Finset.card_union_of_disjoint hv.2,List.toFinset_card_of_nodup hc.2.1,hc.1]

/-- The matching reverse boundary may release the appended high bits once
history pop has restored them to zero. It restores the original allocation. -/
theorem historyGrowth_release (A B : Arena) (extra : List Wire) (n : Nat)
    (h : A.borrowMany n=some (B,extra)) (s : BasisState)
    (hz : ∀ q∈extra,s q=false) : B.release extra.toFinset s=some A := by
  have hc := A.borrowMany_contract B n extra h
  have hv := (A.reserve_success extra.toFinset).mp ⟨B,hc.2.2⟩
  have he := hc.2.2
  simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
  cases he
  have own : extra.toFinset⊆A.live∪extra.toFinset := Finset.subset_union_right
  have clean : ∀ q∈extra.toFinset,s q=false := fun q hq => hz q (List.mem_toFinset.mp hq)
  have ok : extra.toFinset⊆A.live∪extra.toFinset ∧ (∀ q∈extra.toFinset,s q=false) := ⟨own,clean⟩
  have live : (A.live∪extra.toFinset)\extra.toFinset=A.live := by
    ext q
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨h|h,hn⟩
      · exact h
      · exact (hn h).elim
    · intro h
      exact ⟨Or.inl h,fun he => Finset.disjoint_left.mp hv.2 h he⟩
  cases A
  simp_all [Arena.release]

end ECDSAAdd.Arithmetic.Paper935
