import ECDSAAdd.Arithmetic.Paper935.DepthListCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- The entire five-depth decoder is supported by one live eleven-bit pool. -/
theorem compileBorrowedDepths_support (A D : Arena) (one frozen output : Wire)
    (z f v work : List Wire) (layouts : List DepthLayout)
    (h : compileBorrowedDepths A one frozen output z f v=some (D,work,layouts))
    (owned : (one::frozen::output::(z++f++v)).toFinset⊆A.live) (p : Int) :
    D.live.card=A.live.card+11 ∧ wires (finiteDepthProgram layouts p)⊆D.live := by
  have pair := compileBorrowedDepths_contract A D one frozen output z f v work layouts h
  have contract := compileDepthList_contract one frozen output z f v work _ layouts pair.2
  have nonempty : layouts≠[] := by intro he; simp [he] at contract
  obtain ⟨L,hL⟩ := List.exists_mem_of_ne_nil layouts nonempty
  obtain ⟨d,_,hc⟩ := compileBorrowedDepths_member A D one frozen output z f v work layouts h L hL
  refine ⟨(compileBorrowedDepth_support A D one frozen output z f v work d L hc owned p).1,?_⟩
  have each : ∀ L∈layouts,wires (L.program p)⊆D.live := by
    intro K hk
    obtain ⟨e,_,he⟩ := compileBorrowedDepths_member A D one frozen output z f v work layouts h K hk
    exact (compileBorrowedDepth_support A D one frozen output z f v work e K he owned p).2
  clear contract nonempty hL hc h pair
  induction layouts with
  | nil => simp [finiteDepthProgram,wires]
  | cons K ks ih =>
    change wires (K.program p ++ finiteDepthProgram ks p)⊆D.live
    rw [wires_append]
    exact Finset.union_subset (each K (by simp)) (ih (by intro L hl; exact each L (by simp [hl])))

/-- Readiness and exact execution for every stage follow from the real
pre-borrow clean arena and the physical row/counter values. -/
theorem compileBorrowedDepths_run (A D : Arena) (one frozen output : Wire)
    (b : WindowBank) (z work : List Wire) (layouts : List DepthLayout)
    (h : compileBorrowedDepths A one frozen output z b.f.wires b.fv.wires=some (D,work,layouts))
    (p : Int) (st : ECDSAAdd.Divsteps.ZState) (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (s : State) (m : List Bool) (ready : A.Ready s.basis) (hone : s.basis one=true)
    (rows : s.basis frozen=false → b.Encodes s.basis (ECDSAAdd.Divsteps.zStep st))
    (counter : s.basis frozen=false → signedRegValue z s.basis=(ECDSAAdd.Divsteps.zStep st).z) :
    run (finiteDepthProgram layouts p) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^ finiteDepthMask st (s.basis frozen) layouts)⟩ := by
  have each (L : DepthLayout) (hl : L∈layouts) :=
    compileBorrowedDepths_member A D one frozen output z b.f.wires b.fv.wires work layouts h L hl
  apply finiteDepthProgram_available layouts p st hi hp output (s.basis frozen) s m
  · intro L hl
    obtain ⟨d,_,hc⟩ := each L hl
    exact compileBorrowedDepth_available A D one frozen output b z work d L hc st s ready hone rows counter
  · intro L hl
    obtain ⟨d,_,hc⟩ := each L hl
    have hh := (compileBorrowedDepth_contract A D one frozen output z b.f.wires b.fv.wires work d L hc).2
    exact (compileDepth_identity one frozen output z b.f.wires b.fv.wires work d L hh).2.2
  · intro L hl
    obtain ⟨d,_,hc⟩ := each L hl
    have hh := (compileBorrowedDepth_contract A D one frozen output z b.f.wires b.fv.wires work d L hc).2
    rw [(compileDepth_identity one frozen output z b.f.wires b.fv.wires work d L hh).2.1]

/-- The single shared pool is returned only after all five actual programs
have executed and restored it; the original allocation is recovered. -/
theorem compileBorrowedDepths_release (A D : Arena) (one frozen output : Wire)
    (b : WindowBank) (z work : List Wire) (layouts : List DepthLayout)
    (h : compileBorrowedDepths A one frozen output z b.f.wires b.fv.wires=some (D,work,layouts))
    (owned : output∈A.live)
    (p : Int) (st : ECDSAAdd.Divsteps.ZState) (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (s : State) (m : List Bool) (ready : A.Ready s.basis) (hone : s.basis one=true)
    (rows : s.basis frozen=false → b.Encodes s.basis (ECDSAAdd.Divsteps.zStep st))
    (counter : s.basis frozen=false → signedRegValue z s.basis=(ECDSAAdd.Divsteps.zStep st).z) :
    D.release work.toFinset (run (finiteDepthProgram layouts p) m s).basis=some A ∧
    A.Ready (run (finiteDepthProgram layouts p) m s).basis := by
  have pair := compileBorrowedDepths_contract A D one frozen output z b.f.wires b.fv.wires work layouts h
  have hc := A.borrowMany_contract D 11 work pair.1
  have hv := (A.reserve_success work.toFinset).mp ⟨D,hc.2.2⟩
  have clean := (A.reserve_ready D work.toFinset s.basis ready hc.2.2).2
  have run_eq := compileBorrowedDepths_run A D one frozen output b z work layouts h p st hi hp s m ready hone rows counter
  have frame (q : Wire) (away : q≠output) :
      (run (finiteDepthProgram layouts p) m s).basis q=s.basis q := by
    rw [run_eq]
    exact Function.update_of_ne away _ _
  constructor
  · apply historyGrowth_release A D work 11 pair.1
    intro q hq
    have away : q≠output := fun he => Finset.disjoint_left.mp hv.2 (he ▸ owned) (List.mem_toFinset.mpr hq)
    exact (frame q away).trans (clean q (List.mem_toFinset.mpr hq))
  · intro q hq hn
    rw [frame q (fun he => hn (he ▸ owned))]
    exact ready q hq hn

end ECDSAAdd.Arithmetic.Paper935
