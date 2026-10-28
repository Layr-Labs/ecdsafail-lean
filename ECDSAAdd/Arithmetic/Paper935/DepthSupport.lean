import ECDSAAdd.Arithmetic.Paper935.DepthCompiler

namespace ECDSAAdd.Arithmetic.Paper935

def DepthLayout.sites (L : DepthLayout) : List Wire :=
  [L.one,L.zz,L.pos,L.sign,L.flag,L.address,L.tmp,L.output]++L.zb.flatMap ZeroBit.wires++
    (L.frozen::L.positive::L.low).flatMap ZeroBit.wires++L.fdata++L.qbits++L.scratch

theorem DepthLayout.program_support (L : DepthLayout) (p : Int) :
    wires (L.program p)⊆L.sites.toFinset := by
  have root (q : Wire) (h : q∈[L.one,L.zz,L.pos,L.sign,L.flag,L.address,L.tmp,L.output]) : q∈L.sites.toFinset := by
    simp only [sites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
  have zw (q : Wire) (h : q∈L.zb.flatMap ZeroBit.wires) : q∈L.sites.toFinset := by
    simp only [sites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
  have fw (q : Wire) (h : q∈(L.frozen::L.positive::L.low).flatMap ZeroBit.wires) : q∈L.sites.toFinset := by
    simp only [sites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  have data (q : Wire) (h : q∈(L.fdata++L.qbits)++L.scratch) : q∈L.sites.toFinset := by
    simp only [sites,List.mem_toFinset,List.mem_append]
    simp only [List.mem_append] at h
    rcases h with (h|h)|h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  intro q hq
  rw [program,classLookup_support,historyClassFlag_support,counterPositive_support] at hq
  rcases Finset.mem_union.mp hq with hq|hq
  · simp only [Finset.mem_union,List.mem_toFinset,Finset.mem_insert,Finset.mem_singleton,
      List.mem_cons] at hq
    rcases hq with ((rfl|rfl|h)|rfl|rfl|rfl)|(rfl|rfl|h)
    · exact root _ (by simp)
    · exact root _ (by simp)
    · exact zw _ h
    · exact root _ (by simp)
    · exact root _ (by simp)
    · exact root _ (by simp)
    · exact root _ (by simp)
    · exact root _ (by simp)
    · exact fw _ h
  · have hl := lookupBranch_support L.flag L.address L.tmp L.output (L.fdata++L.qbits) L.scratch
      (residueBranchTable p L.low.length) hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl|rfl|h|rfl
    · exact root _ (by simp)
    · exact root _ (by simp)
    · exact root _ (by simp)
    · exact data _ (by simpa only [List.mem_append] using h)
    · exact root _ (by simp)

theorem compileDepth_sites (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) (L : DepthLayout) (h : compileDepth one frozen output z f v work depth=some L) :
    L.sites.toFinset⊆(one::frozen::output::(z++f++v++work)).toFinset := by
  have c := compileDepth_contract one frozen output z f v work depth L h
  have ids := compileDepth_identity one frozen output z f v work depth L h
  have cw := compileDepth_clean_subset one frozen output z f v work depth L h
  have clean (q : Wire) (hq : q∈L.cleanWires) : q∈work :=
    List.mem_toFinset.mp (cw (List.mem_toFinset.mpr hq))
  have inF (q : Wire) (hq : q∈L.address::L.fdata) : q∈f := by
    rw [←c.2.2.2.1]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)
  have inV (q : Wire) (hq : q∈L.low.map ZeroBit.input) : q∈v := by
    rw [←c.2.2.2.2.1]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)
  have inQ (q : Wire) (hq : q∈L.qbits) : q∈v := by
    rw [←c.2.2.2.2.1,c.1.hcoeffview]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hq))
  have inZ (q : Wire) (hq : q∈L.zb.map ZeroBit.input) : q∈z := by rw [←c.2.2.1]; exact hq
  have zwork (bit : ZeroBit) (hb : bit∈L.zb) : bit.work∈work := by
    apply clean
    simp only [DepthLayout.cleanWires,List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨bit,hb,rfl⟩)))
  have fwork (bit : ZeroBit) (hb : bit∈L.frozen::L.positive::L.low) : bit.work∈work := by
    apply clean
    simp only [DepthLayout.cleanWires,List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨bit,hb,rfl⟩))
  have root (q : Wire) (hq : q∈[L.zz,L.pos,L.flag,L.tmp]) : q∈work :=
    clean q (by simp only [DepthLayout.cleanWires,List.mem_append]; exact Or.inl (Or.inl (Or.inl hq)))
  intro q hq
  simp only [DepthLayout.sites,List.mem_toFinset,List.mem_append] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  rcases hq with ((((hq|hq)|hq)|hq)|hq)|hq
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp [ids.1]
    · have hw := root L.zz (by simp); tauto
    · have hw := root L.pos (by simp); tauto
    · have hz := inZ L.sign c.1.hsg; tauto
    · have hw := root L.flag (by simp); tauto
    · have hf := inF L.address (by simp); tauto
    · have hw := root L.tmp (by simp); tauto
    · simp [ids.2.2]
  · obtain ⟨bit,hb,hq⟩ := List.mem_flatMap.mp hq
    simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · have hz := inZ bit.input (List.mem_map.mpr ⟨bit,hb,rfl⟩); tauto
    · have hw := zwork bit hb; tauto
  · obtain ⟨bit,hb,hq⟩ := List.mem_flatMap.mp hq
    simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · simp only [List.mem_cons] at hb
      rcases hb with rfl|rfl|hb
      · simp [ids.2.1]
      · have hw := root L.pos (by simp); rw [c.1.hpos]; tauto
      · have hv := inV bit.input (List.mem_map.mpr ⟨bit,hb,rfl⟩); tauto
    · have hw := fwork bit hb; tauto
  · have hf := inF q (List.mem_cons_of_mem _ hq); tauto
  · have hv := inQ q hq; tauto
  · have hw := clean q (by simp [DepthLayout.cleanWires,hq]); tauto

theorem compileDepth_program_support (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) (L : DepthLayout) (h : compileDepth one frozen output z f v work depth=some L) (p : Int) :
    wires (L.program p)⊆(one::frozen::output::(z++f++v++work)).toFinset :=
  (L.program_support p).trans (compileDepth_sites one frozen output z f v work depth L h)

end ECDSAAdd.Arithmetic.Paper935
