import ECDSAAdd.Arithmetic.Paper935.BorrowedHistoryTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- Every quantum address of the measured history program belongs to its
explicit controls, detector views, branch port or physical record. -/
theorem HistoryLayout.support (H : HistoryLayout) :
    recordedWires H.program ⊆
      ([H.one,H.zz,H.pos,H.sign,H.output,H.port]++H.zb.flatMap ZeroBit.wires++
        (H.frozen::H.positive::H.low).flatMap ZeroBit.wires++H.record).toFinset := by
  rw [HistoryLayout.program,storePushForget_support,storePush_support,storeFlag_support,
    counterPositive_support]
  have push := (history_support H.output H.port H.record).1
  intro q hq
  simp only [Finset.mem_union] at hq
  rcases hq with (((hq|hq)|hq)|hq)|hq
  · simpa only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] using
      (show q∈[H.one,H.zz,H.pos,H.sign,H.output,H.port]++H.zb.flatMap ZeroBit.wires++
        (H.frozen::H.positive::H.low).flatMap ZeroBit.wires++H.record by
        simp only [List.mem_toFinset,List.mem_cons] at hq
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        tauto)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · simp only [List.mem_toFinset,List.mem_cons] at hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · have hp := push hq
    simp only [List.mem_toFinset,List.mem_cons] at hp
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · simp only [Finset.mem_singleton] at hq
    subst q
    simp

/-- The successful compiler introduces no quantum addresses beyond the supplied
physical inputs and the allocated detector pool. -/
theorem compileHistory_support (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire) (H : HistoryLayout)
    (h : compileHistory one zz pos sign output port frozen counter coeffBits record work=some H) :
    recordedWires H.program ⊆
      ([one,zz,pos,sign,output,port,frozen]++counter++coeffBits++record++work).toFinset := by
  have ids := compileHistory_identity one zz pos sign output port frozen counter coeffBits record work H h
  have hc := compileHistory_contract one zz pos sign output port frozen counter coeffBits record work H h
  have hw := compileHistory_work one zz pos sign output port frozen counter coeffBits record work H h
  intro q hq
  have hp := H.support hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
  rcases hp with (((hp|hp)|hp)|hp)
  · rw [ids.1,ids.2.1,ids.2.2.1,ids.2.2.2.1,ids.2.2.2.2.1,ids.2.2.2.2.2] at hp
    clear h hc hw ids hq
    tauto
  · obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hp
    have hi : b.input∈counter := hc.2.1 ▸ List.mem_map_of_mem hb
    have hw := hw.1 b hb
    simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
    clear h hc ids hb hp
    rcases hq with rfl|rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inr hi)))
    · exact Or.inr hw
  · obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hp
    have hw := hw.2 b hb
    have hi : b.input=frozen ∨ b.input=pos ∨ b.input∈coeffBits := by
      simp only [List.mem_cons] at hb
      rcases hb with rfl|rfl|hb
      · exact Or.inl hc.2.2.2.2.2
      · exact Or.inr (Or.inl (hc.1.2.2.2.1.trans ids.2.2.1))
      · exact Or.inr (Or.inr (hc.2.2.1 ▸ List.mem_map_of_mem hb))
    simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
    clear h hc ids hb hp
    rcases hq with rfl|rfl
    · rcases hi with hi|hi|hi
      · simp only [hi,eq_self,or_true,true_or]
      · simp only [hi,eq_self,or_true,true_or]
      · exact Or.inl (Or.inl (Or.inr hi))
    · exact Or.inr hw
  · rw [hc.2.2.2.2.1] at hp
    clear h hc hw ids hq
    tauto

/-- Actual emitted history instructions stay inside the allocator's detector
stage, provided its persistent inputs were owned before growing the record. -/
theorem compileGrowingHistory_support (A B D : Arena) (record work : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H))
    (owned : ([one,zz,pos,sign,output,port,frozen]++counter++coeffBits++record).toFinset⊆A.live) :
    recordedWires H.program⊆D.live := by
  have hc := compileGrowingHistory_contract A B D record work capacity one zz pos sign output port frozen counter coeffBits H h
  have grow := hc.1
  unfold planHistoryGrow at grow
  obtain ⟨⟨B',extra⟩,hb,he⟩ := Option.bind_eq_some_iff.mp grow
  have eqs : B'=B ∧ record++extra=H.record := by simpa using he
  have recordEq := eqs.2
  have bankEq := eqs.1
  subst B'
  have first := (A.borrowMany_live B _ extra hb).1
  have second := (B.borrowMany_live D _ work hc.2.1).1
  apply Finset.Subset.trans (compileHistory_support one zz pos sign output port frozen counter coeffBits (record++extra) work H (by simpa only [recordEq] using hc.2.2))
  rw [second,first]
  simpa only [List.toFinset_append,Finset.union_assoc] using
    Finset.union_subset_union (Finset.union_subset_union owned (Finset.Subset.refl extra.toFinset))
      (Finset.Subset.refl work.toFinset)

end ECDSAAdd.Arithmetic.Paper935
