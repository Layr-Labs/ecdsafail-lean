import ECDSAAdd.Arithmetic.Paper935.CloserBank

namespace ECDSAAdd.Arithmetic.Paper935

private theorem payload_mem (b : WindowBank) (q : Wire) (h : q∈closerPayloads b) :
    q∈b.rows.flatMap WindowRow.wires := by
  simp only [closerPayloads,List.mem_append] at h
  simp only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,WindowRow.wires,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto

/-- Actual permission-checked release after the physical closer. -/
theorem closerProgram_release (b : WindowBank) (p : Nat) (A : Arena)
    (owned : rowsOwned A b.rows) (fwidth : 1<2^b.f.payload.length)
    (positive : 0<p) (pwidth : p<2^b.gv.payload.length) (s : State) (m : List Bool)
    (ready : A.Ready s.basis) (gzero : b.g.value s.basis=0)
    (funit : (b.f.value s.basis).natAbs=1)
    (gvValue : b.gv.value s.basis=b.f.value s.basis*p) :
    let out := run (closerProgram b p) m s
    A.release (closerPayloads b).toFinset out.basis=some (A.retireSet (closerPayloads b).toFinset) ∧
    (A.retireSet (closerPayloads b).toFinset).Ready out.basis := by
  have clear := closerProgram_clear b p owned.1 fwidth positive pwidth s m gzero funit gvValue
  dsimp only at clear ⊢
  generalize execution : run (closerProgram b p) m s=out at clear ⊢
  have subset : (closerPayloads b).toFinset⊆A.live := by
    intro q hq
    exact owned.2 (List.mem_toFinset.mpr (payload_mem b q (List.mem_toFinset.mp hq)))
  have release : A.release (closerPayloads b).toFinset out.basis=
      some (A.retireSet (closerPayloads b).toFinset) := by
    have zero : ∀ q∈(closerPayloads b).toFinset,out.basis q=false := by
      simpa only [List.mem_toFinset] using clear.2.1
    rw [Arena.release,if_pos ⟨subset,zero⟩]
    rfl
  refine ⟨release,Arena.release_ready _ _ _ _ ?_ release⟩
  intro q hq hn
  have away : q∉b.gv.sign::closerPayloads b := by
    intro h
    apply hn
    apply owned.2
    apply List.mem_toFinset.mpr
    rcases List.mem_cons.mp h with eq | mem
    · subst q
      simp [WindowBank.rows,WindowRow.wires]
    · exact payload_mem b q mem
  exact (clear.2.2.2 q away).trans (ready q hq hn)

theorem closerPayloads_card (b : WindowBank)
    (geometry : (b.rows.flatMap WindowRow.wires).Nodup) :
    (closerPayloads b).toFinset.card=b.f.payload.length+b.g.payload.length+b.gv.payload.length := by
  have nd : (closerPayloads b).Nodup := by
    rw [List.nodup_iff_count_le_one] at geometry ⊢
    intro q
    have h := geometry q
    simp only [closerPayloads,WindowBank.rows,List.flatMap_cons,List.flatMap_nil,
      WindowRow.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  rw [List.toFinset_card_of_nodup nd]
  simp only [closerPayloads,List.length_append]

/-- Ownership after the actual release, expressed independently of a particular
compiler so the numeric specialization uses the compiler's own exit bank. -/
theorem closer_retired_card (b : WindowBank) (A : Arena) (owned : rowsOwned A b.rows) :
    (A.retireSet (closerPayloads b).toFinset).live.card=
      A.live.card-(b.f.payload.length+b.g.payload.length+b.gv.payload.length) := by
  have subset : (closerPayloads b).toFinset⊆A.live := by
    intro q hq
    exact owned.2 (List.mem_toFinset.mpr (payload_mem b q (List.mem_toFinset.mp hq)))
  rw [Arena.retireSet,Finset.card_sdiff_of_subset subset,closerPayloads_card b owned.1]

end ECDSAAdd.Arithmetic.Paper935
