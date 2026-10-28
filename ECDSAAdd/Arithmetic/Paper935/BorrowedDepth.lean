import ECDSAAdd.Arithmetic.Paper935.DepthSupport
import ECDSAAdd.Arithmetic.Paper935.HistoryAllocation

namespace ECDSAAdd.Arithmetic.Paper935

def compileBorrowedDepth (A : Arena) (one frozen output : Wire) (z f v : List Wire)
    (depth : Nat) : Option (Arena × List Wire × DepthLayout) := do
  let (D,work) ← A.borrowMany 11
  let L ← compileDepth one frozen output z f v work depth
  pure (D,work,L)

theorem compileBorrowedDepth_contract (A D : Arena) (one frozen output : Wire)
    (z f v work : List Wire) (depth : Nat) (L : DepthLayout)
    (h : compileBorrowedDepth A one frozen output z f v depth=some (D,work,L)) :
    A.borrowMany 11=some (D,work) ∧ compileDepth one frozen output z f v work depth=some L := by
  unfold compileBorrowedDepth at h
  cases hb : A.borrowMany 11 with
  | none => simp [hb] at h
  | some result =>
    rcases result with ⟨B,ws⟩
    simp only [hb] at h
    dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd] at h
    cases hc : compileDepth one frozen output z f v ws depth with
    | none => simp [hc] at h
    | some K =>
      simp only [hc] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      exact ⟨rfl,hc⟩

/-- The shared pool is actually live during execution, not merely a set of
free addresses omitted from the allocation ledger. -/
theorem compileBorrowedDepth_support (A D : Arena) (one frozen output : Wire)
    (z f v work : List Wire) (depth : Nat) (L : DepthLayout)
    (h : compileBorrowedDepth A one frozen output z f v depth=some (D,work,L))
    (owned : (one::frozen::output::(z++f++v)).toFinset⊆A.live) (p : Int) :
    D.live.card=A.live.card+11 ∧ wires (L.program p)⊆D.live := by
  have pair := compileBorrowedDepth_contract A D one frozen output z f v work depth L h
  have hc := A.borrowMany_contract D 11 work pair.1
  have hv := (A.reserve_success work.toFinset).mp ⟨D,hc.2.2⟩
  have live : D.live=A.live∪work.toFinset := by
    have he := hc.2.2
    simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
    cases he
    rfl
  constructor
  · rw [live,Finset.card_union_of_disjoint hv.2,List.toFinset_card_of_nodup hc.2.1,hc.1]
  · apply (compileDepth_program_support one frozen output z f v work depth L pair.2 p).trans
    rw [live]
    intro q hq
    have split : q∈(one::frozen::output::(z++f++v)) ∨ q∈work := by
      simpa only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] using hq
    exact split.elim (fun h => Finset.mem_union_left _ (owned (List.mem_toFinset.mpr h)))
      (fun h => Finset.mem_union_right _ (List.mem_toFinset.mpr h))

/-- Actual depth execution returns the eleven borrowed bits clean. The
original live allocation and its free-zero invariant are both restored. -/
theorem compileBorrowedDepth_release (A D : Arena) (one frozen output : Wire)
    (z f v work : List Wire) (depth : Nat) (L : DepthLayout)
    (h : compileBorrowedDepth A one frozen output z f v depth=some (D,work,L))
    (owned : output∈A.live) (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (p : Int) (st : ECDSAAdd.Divsteps.ZState) (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (available : L.Available st s) :
    D.release work.toFinset (run (L.program p) m s).basis=some A ∧
    A.Ready (run (L.program p) m s).basis := by
  have pair := compileBorrowedDepth_contract A D one frozen output z f v work depth L h
  have hc := A.borrowMany_contract D 11 work pair.1
  have hv := (A.reserve_success work.toFinset).mp ⟨D,hc.2.2⟩
  have clean := (A.reserve_ready D work.toFinset s.basis ready hc.2.2).2
  have ids := compileDepth_identity one frozen output z f v work depth L pair.2
  have run_eq := DepthLayout.Available.run L p st hi hp s m available
  have frame (q : Wire) (away : q≠output) : (run (L.program p) m s).basis q=s.basis q := by
    rw [run_eq,ids.2.2]
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
