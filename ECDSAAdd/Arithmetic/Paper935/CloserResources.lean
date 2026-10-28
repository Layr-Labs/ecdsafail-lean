import ECDSAAdd.Arithmetic.Paper935.CloserBank

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

private theorem fan_support (c : Wire) (r : List Wire) (a d : Nat) :
    wires (closerFan c r a d)⊆(c::r).toFinset := by
  rw [closerFan,wires_append]
  refine Finset.union_subset (maskedConstant_wires_subset _ _ _) ?_
  exact (xorConstant_wires_subset _ _).trans (by intro q h; simpa using List.mem_cons_of_mem c (List.mem_toFinset.mp h))

theorem closerProgram_counts (b : WindowBank) (p : Nat) :
    toffoliCount (closerProgram b p)=0 ∧ measurementCount (closerProgram b p)=0 := by
  simp only [closerProgram,closerPair,toffoliCount_append,measurementCount_append,
    (rowWindow_cost _ _).2.2.1,(rowWindow_cost _ _).2.2.2,
    (closerFan_counts _ _ _ _).1,(closerFan_counts _ _ _ _).2,
    toffoliCount,measurementCount,Nat.add_zero]
  trivial

theorem closerProgram_support (b : WindowBank) (p : Nat) :
    wires (closerProgram b p)⊆(b.rows.flatMap WindowRow.wires).toFinset := by
  have row (r : WindowRow) (member : r∈b.rows) :
      (r.sign::r.payload).toFinset⊆(b.rows.flatMap WindowRow.wires).toFinset := by
    intro q hq
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨r,member,?_⟩
    simp only [WindowRow.wires,List.mem_append,List.mem_toFinset,List.mem_cons,List.not_mem_nil] at hq ⊢
    tauto
  have g := growRow_support b.g.sign b.g.payload.reverse
  have g' : wires (shrinkRow b.g.sign b.g.payload)⊆(b.g.sign::b.g.payload).toFinset := by
    simpa only [shrinkRow_eq,List.toFinset_reverse,List.toFinset_cons] using g
  have f := (fan_support b.f.sign b.f.payload 1 (2^b.f.payload.length-1)).trans (row b.f (by simp [WindowBank.rows]))
  have gv := (fan_support b.gv.sign b.gv.payload p (2^b.gv.payload.length-p)).trans (row b.gv (by simp [WindowBank.rows]))
  rw [closerProgram,closerPair,wires_append,wires_append,wires_append]
  refine Finset.union_subset (g'.trans (row b.g (by simp [WindowBank.rows])))
    (Finset.union_subset (Finset.union_subset f gv) ?_)
  intro q hq
  simp only [wires,Instr.wires,Finset.union_empty,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact row b.f (by simp [WindowBank.rows]) (by simp)
  · exact row b.gv (by simp [WindowBank.rows]) (by simp)

theorem closerProgram_arena (b : WindowBank) (p : Nat) (A : Arena) (owned : rowsOwned A b.rows) :
    wires (closerProgram b p)⊆arenaWires :=
  (closerProgram_support b p).trans (owned.2.trans A.bounded)

end ECDSAAdd.Arithmetic.Paper935
