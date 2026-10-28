import ECDSAAdd.Arithmetic.Paper935.BorrowedPostRun
import ECDSAAdd.Arithmetic.Paper935.WindowSlotPhysical

namespace ECDSAAdd.Arithmetic.Paper935

theorem WindowPostLayout.ports_partition (P : WindowPostLayout) :
    P.ports.toFinset ⊆ (P.one::P.frozen::P.active::
      (P.recordWires++BlockedZero.inputs P.blocks++P.scratch)).toFinset := by
  intro q hq
  have scratch (hs : q∈P.scratch) : q∈(P.one::P.frozen::P.active::
      (P.recordWires++BlockedZero.inputs P.blocks++P.scratch)).toFinset := by simp [hs]
  have input (hs : q∈BlockedZero.inputs P.blocks) : q∈(P.one::P.frozen::P.active::
      (P.recordWires++BlockedZero.inputs P.blocks++P.scratch)).toFinset := by simp [hs]
  have record (hs : q∈P.recordWires) : q∈(P.one::P.frozen::P.active::
      (P.recordWires++BlockedZero.inputs P.blocks++P.scratch)).toFinset := by simp [hs]
  simp only [ports,List.mem_toFinset,List.mem_cons,List.mem_append] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|((hq|hq)|hq)
  · simp
  · exact scratch (by simp [WindowPostLayout.scratch])
  · simp
  · exact scratch (by simp [WindowPostLayout.scratch])
  · simp
  · exact scratch (by simp [WindowPostLayout.scratch])
  · exact record hq
  · obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    simp only [BlockedZero.Block.ports,List.mem_cons] at hq
    rcases hq with rfl|hq
    · exact scratch (by simp [WindowPostLayout.scratch,List.mem_map_of_mem hb])
    · obtain ⟨x,hx,hq⟩ := List.mem_flatMap.mp hq
      simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl
      · exact input (List.mem_flatMap.mpr ⟨b,hb,List.mem_map.mpr ⟨x,hx,rfl⟩⟩)
      · apply scratch
        simp only [WindowPostLayout.scratch,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨b,hb,List.mem_map.mpr ⟨x,hx,rfl⟩⟩)))))
  · obtain ⟨x,hx,hq⟩ := List.mem_flatMap.mp hq
    simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · exact record (List.mem_map.mpr ⟨x,hx,rfl⟩)
    · exact scratch (by simp [WindowPostLayout.scratch,List.mem_map_of_mem hx])

theorem compilePost_ports (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compilePost armed one zf frozen fire active inputs record work width offset=some P) :
    P.ports.toFinset⊆(one::zf::frozen::fire::active::(inputs++record++work)).toFinset := by
  have hc := compilePost_contract armed one zf frozen fire active inputs record work width offset P h
  have ids := compilePost_identity armed one zf frozen fire active inputs record work width offset P h
  apply P.ports_partition.trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
  rw [ids.2.1,ids.2.2.2.1,ids.2.2.2.2.2.1,hc.2.2.1,hc.2.1] at hq
  rcases hq with hq|hq|hq|((hq|hq)|hq)
  · exact Or.inl hq
  · exact Or.inr (Or.inr (Or.inl hq))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hq))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hq))))))
  · rcases compilePost_scratch armed one zf frozen fire active inputs record work width offset P h q hq with hq|hq|hq
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq)))))

theorem compileBorrowedPost_support (A D : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compileBorrowedPost A armed one zf frozen fire active inputs record width offset=some (D,work,P))
    (owned : (one::zf::frozen::fire::active::(inputs++record)).toFinset⊆A.live) :
    D.live.card=A.live.card+postPoolSize inputs record width ∧
    wires P.program⊆D.live ∧ wires P.inverse⊆D.live := by
  have pair := compileBorrowedPost_contract A D armed one zf frozen fire active inputs record work width offset P h
  have hc := A.borrowMany_contract D _ work pair.1
  have hv := (A.reserve_success work.toFinset).mp ⟨D,hc.2.2⟩
  have live : D.live=A.live∪work.toFinset := by
    have he := hc.2.2
    simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
    cases he
    rfl
  have ports : P.ports.toFinset⊆D.live := by
    apply (compilePost_ports armed one zf frozen fire active inputs record work width offset P pair.2).trans
    rw [live]
    intro q hq
    have split : q∈(one::zf::frozen::fire::active::(inputs++record)) ∨ q∈work := by
      simpa only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] using hq
    exact split.elim (fun h => Finset.mem_union_left _ (owned (List.mem_toFinset.mpr h)))
      (fun h => Finset.mem_union_right _ (List.mem_toFinset.mpr h))
  refine ⟨?_,P.support.1.trans ports,P.support.2.trans ports⟩
  rw [live,Finset.card_union_of_disjoint hv.2,List.toFinset_card_of_nodup hc.2.1,hc.1]

theorem compilePost_physical (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compilePost armed one zf frozen fire active inputs record work width offset=some P) :
    GatePhysical P.program ∧ GatePhysical P.inverse :=
  P.physical (compilePost_contract armed one zf frozen fire active inputs record work width offset P h).1

end ECDSAAdd.Arithmetic.Paper935
