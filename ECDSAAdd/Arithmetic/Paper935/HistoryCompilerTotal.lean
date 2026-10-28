import ECDSAAdd.Arithmetic.Paper935.ZeroViews
import ECDSAAdd.Arithmetic.Paper935.HistoryPhysical

namespace ECDSAAdd.Arithmetic.Paper935

/-- A single ordinary separation condition on physical input and work lists
suffices for the checked history compiler. The sign is a view of the counter,
not an additional independently allocated wire. -/
theorem historyCandidate_valid (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire)
    (hn : ([one,zz,pos,output,port,frozen]++counter++coeffBits++record++work).Nodup)
    (sg : sign∈counter) (hc : counter.length≤work.length) (hl : coeffBits.length+2≤work.length) :
    (historyCandidate one zz pos sign output port frozen counter coeffBits record work).Valid := by
  cases work with
  | nil => simp at hl
  | cons w0 rest =>
    cases rest with
    | nil => simp at hl
    | cons w1 ws =>
      have counterDistinct : (counter++(w0::w1::ws)).Nodup := by
        simp_all [List.nodup_append',List.disjoint_append_right]
      have lowDistinct : (coeffBits++ws).Nodup := by
        simp_all [List.nodup_append',List.disjoint_append_right]
      have hz : (output::pos::one::zz::(List.zipWith ZeroBit.mk counter (w0::w1::ws)).flatMap ZeroBit.wires).Nodup := by
        apply zeroViews_prefixed_distinct [output,pos,one,zz] counter (w0::w1::ws)
        simp_all [List.nodup_append',List.disjoint_append_right,eq_comm]
      have hf : (one::output::frozen::w0::pos::w1::(List.zipWith ZeroBit.mk coeffBits ws).flatMap ZeroBit.wires).Nodup := by
        apply zeroViews_prefixed_distinct [one,output,frozen,w0,pos,w1] coeffBits ws
        simp_all [List.nodup_append',List.disjoint_append_right,eq_comm]
      have hpush : (output::port::record).Nodup := by
        clear hz hf
        simp_all [List.nodup_append',List.disjoint_append_right]
      have sep : List.Disjoint (output::port::record)
          ([one,zz,pos,frozen]++counter++coeffBits++(w0::w1::ws)) := by
        clear hz hf
        simp_all [List.nodup_append',List.disjoint_append_right,List.disjoint_comm,eq_comm]
      have zviews := zeroViews_distinct counter (w0::w1::ws) counterDistinct
      have lviews := zeroViews_distinct coeffBits ws lowDistinct
      have zinputs := zeroViews_inputs counter (w0::w1::ws) hc
      have linputs := zeroViews_inputs coeffBits ws (by simpa using hl)
      have readsSubset (q : Wire)
          (hq : q∈one::zz::pos::sign::((List.zipWith ZeroBit.mk counter (w0::w1::ws)).flatMap ZeroBit.wires++
            frozen::w0::pos::w1::(List.zipWith ZeroBit.mk coeffBits ws).flatMap ZeroBit.wires)) :
          q∈[one,zz,pos,frozen]++counter++coeffBits++(w0::w1::ws) := by
        simp only [List.mem_cons,List.mem_append] at hq
        rcases hq with rfl|rfl|rfl|rfl|(hq|rfl|rfl|rfl|rfl|hq)
        all_goals try { simp [sg] }
        · have hm := zviews.2 q hq
          simp only [List.mem_append,List.mem_cons] at hm
          rcases hm with hm|rfl|rfl|hm <;> simp [*]
        · have hm := lviews.2 q hq
          simp only [List.mem_append] at hm
          rcases hm with hm|hm <;> simp [*]
      have posAway : pos∉w1::(List.zipWith ZeroBit.mk coeffBits ws).flatMap ZeroBit.wires :=
        (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp
          (List.nodup_cons.mp (List.nodup_cons.mp hf).2).2).2).2).1
      simp only [historyCandidate,HistoryLayout.Valid,List.getD_cons_zero,List.getD_cons_succ,
        List.drop_succ_cons,List.drop_zero,List.flatMap_cons,ZeroBit.wires,List.cons_append,List.nil_append]
      refine ⟨hz,hf,?_,trivial,?_,?_,?_,?_,?_,?_⟩
      · rw [zinputs]; exact sg
      · intro he; subst frozen; simp at hf
      · intro b hb he
        have mem : b.input∈(List.zipWith ZeroBit.mk coeffBits ws).flatMap ZeroBit.wires :=
          List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩
        exact posAway (List.mem_cons_of_mem _ (he ▸ mem))
      · intro b hb he
        rcases List.mem_cons.mp hb with rfl|hb
        · dsimp only at he; subst w0; simp at hf
        · rcases List.mem_cons.mp hb with rfl|hb
          · dsimp only at he; exact posAway (by simp [he])
          · have mem : b.work∈(List.zipWith ZeroBit.mk coeffBits ws).flatMap ZeroBit.wires :=
              List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩
            exact posAway (List.mem_cons_of_mem _ (he ▸ mem))
      · exact hpush
      · intro hm
        exact List.disjoint_left.mp sep List.mem_cons_self (readsSubset output hm)
      · apply List.disjoint_left.mpr
        intro q hq hm
        exact List.disjoint_left.mp sep (List.mem_cons_of_mem _ hq) (readsSubset q hm)


theorem compileHistory_exists (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire)
    (hn : ([one,zz,pos,output,port,frozen]++counter++coeffBits++record++work).Nodup)
    (sg : sign∈counter) (hc : counter.length≤work.length) (hl : coeffBits.length+2≤work.length) :
    ∃ H,compileHistory one zz pos sign output port frozen counter coeffBits record work=some H := by
  have valid := historyCandidate_valid one zz pos sign output port frozen counter coeffBits record work hn sg hc hl
  have zview := zeroViews_inputs counter work hc
  have lview := zeroViews_inputs coeffBits (work.drop 2) (by simp only [List.length_drop]; omega)
  refine ⟨historyCandidate one zz pos sign output port frozen counter coeffBits record work,?_⟩
  unfold compileHistory
  dsimp only
  apply if_pos
  exact ⟨valid,zview,lview,by omega⟩

end ECDSAAdd.Arithmetic.Paper935
