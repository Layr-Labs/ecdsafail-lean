import ECDSAAdd.Arithmetic.Paper935.ProbeCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Every flag and zero-test work bit comes from the allocated pool. -/
theorem compileProbe_work (one target : Wire) (inputs work : List Wire) (width : Nat)
    (bs : List BlockedZero.Block) (h : compileProbe one target inputs work width=some bs) :
    (∀ b∈bs,b.flag∈work) ∧ (∀ b∈bs,∀ x∈b.bits,x.work∈work) := by
  unfold compileProbe at h
  dsimp only at h
  split at h
  next valid =>
    cases h
    constructor
    · intro b hb
      obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hb
      exact List.mem_of_mem_take (List.of_mem_zip hp).1
    · intro b hb x hx
      exact List.mem_of_mem_drop (BlockedZero.chunks_work _ _ b hb x hx)
  next invalid => simp at h

/-- The emitted measurement-containing zero probe implements the exact test
of the complete input list, with no missing row bits or cleanliness oracle. -/
theorem compileBorrowedProbe_run (A D : Arena) (one target : Wire)
    (inputs work : List Wire) (width : Nat) (bs : List BlockedZero.Block)
    (h : compileBorrowedProbe A one target inputs width=some (D,work,bs))
    (s : State) (m : List Bool) (ready : A.Ready s.basis) :
    run (BlockedZero.program one target bs) m s=
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ (s.basis one && decide (regValue inputs s.basis=0)))⟩ := by
  have pair := compileBorrowedProbe_contract A D one target inputs work width bs h
  have hc := compileProbe_contract one target inputs work width bs pair.2
  have hw := compileProbe_work one target inputs work width bs pair.2
  have borrow := A.borrowMany_contract D _ work pair.1
  have clean := (A.reserve_ready D work.toFinset s.basis ready borrow.2.2).2
  have hz : BlockedZero.clean bs s.basis := by
    intro b hb
    exact ⟨clean _ (List.mem_toFinset.mpr (hw.1 b hb)),
      fun x hx => clean _ (List.mem_toFinset.mpr (hw.2 b hb x hx))⟩
  rw [BlockedZero.run_eq one target bs hc.1 s m hz,BlockedZero.test_eq_zero,hc.2]

theorem compileBorrowedProbe_release (A D : Arena) (one target : Wire)
    (inputs work : List Wire) (width : Nat) (bs : List BlockedZero.Block)
    (h : compileBorrowedProbe A one target inputs width=some (D,work,bs))
    (owned : target∈A.live) (s : State) (m : List Bool) (ready : A.Ready s.basis) :
    D.release work.toFinset (run (BlockedZero.program one target bs) m s).basis=some A ∧
    A.Ready (run (BlockedZero.program one target bs) m s).basis := by
  have pair := compileBorrowedProbe_contract A D one target inputs work width bs h
  have hc := A.borrowMany_contract D _ work pair.1
  have hv := (A.reserve_success work.toFinset).mp ⟨D,hc.2.2⟩
  have clean := (A.reserve_ready D work.toFinset s.basis ready hc.2.2).2
  have run_eq := compileBorrowedProbe_run A D one target inputs work width bs h s m ready
  have frame (q : Wire) (away : q≠target) :
      (run (BlockedZero.program one target bs) m s).basis q=s.basis q := by
    rw [run_eq]
    exact Function.update_of_ne away _ _
  constructor
  · apply historyGrowth_release A D work _ pair.1
    intro q hq
    have away : q≠target := fun he => Finset.disjoint_left.mp hv.2 (he ▸ owned) (List.mem_toFinset.mpr hq)
    exact (frame q away).trans (clean q (List.mem_toFinset.mpr hq))
  · intro q hq hn
    rw [frame q (fun he => hn (he ▸ owned))]
    exact ready q hq hn

end ECDSAAdd.Arithmetic.Paper935
