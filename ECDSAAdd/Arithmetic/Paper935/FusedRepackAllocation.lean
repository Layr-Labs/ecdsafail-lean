import ECDSAAdd.Arithmetic.Paper935.FusedBoundaryLayout

namespace ECDSAAdd.Arithmetic.Paper935

/-- Static ownership check for a public relocation journal. The check never
reads quantum data; physical readiness is proved for the emitted swaps. -/
def Arena.checkRepack (A : Arena) : List (Wire × Wire) → Option Arena
  | [] => some A
  | (old,fresh)::ms =>
    if old∈A.live then do
      let B ← A.reserve {fresh}
      (B.retireSet {old}).checkRepack ms
    else none

private theorem reserve_live (A B : Arena) (qs : Finset Wire)
    (h : A.reserve qs=some B) : B.live=A.live∪qs := by
  have hv := (A.reserve_success qs).mp ⟨B,h⟩
  simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at h
  cases h
  rfl

/-- Every accepted move has distinct endpoints and stays inside the arena. -/
theorem Arena.checkRepack_valid (A C : Arena) (ms : List (Wire × Wire))
    (checked : A.checkRepack ms=some C) :
    ∀p∈ms,p.1≠p.2 ∧ p.1∈arenaWires ∧ p.2∈arenaWires := by
  induction ms generalizing A with
  | nil => simp
  | cons p ps ih =>
    simp only [checkRepack] at checked
    split at checked
    next old =>
      cases hr : A.reserve {p.2} with
      | none => simp [hr] at checked
      | some B =>
        simp only [hr] at checked
        have hv := (A.reserve_success {p.2}).mp ⟨B,hr⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl|hq
        · refine ⟨?_,A.bounded old,hv.1 (by simp)⟩
          intro eq
          exact Finset.disjoint_left.mp hv.2 old (by simp [eq])
        · exact ih _ checked q hq
    next old => simp at checked

/-- All clean destinations and all returned old sites are discharged from
allocator readiness and the actual three-CX swaps in the interpreter. -/
theorem Arena.checkRepack_ready (A C : Arena) (ms : List (Wire × Wire))
    (checked : A.checkRepack ms=some C) (s : State) (m : List Bool)
    (ready : A.Ready s.basis) : C.Ready (run (repack ms) m s).basis := by
  induction ms generalizing A s m with
  | nil => simp only [checkRepack,Option.some.injEq] at checked; subst C; exact ready
  | cons p ps ih =>
    simp only [checkRepack] at checked
    split at checked
    next old =>
      cases hr : A.reserve {p.2} with
      | none => simp [hr] at checked
      | some B =>
        simp only [hr] at checked
        obtain ⟨D,release,clean,_,_⟩ := rehome_allocated A B p.1 p.2 s [] old ready hr
        have eq : D=B.retireSet {p.1} := by
          unfold Arena.release at release
          split at release
          next h => cases release; rfl
          next h => simp at release
        subst D
        simp only [repack,run_append,(rehome_cost p.1 p.2).2,List.take_zero,List.drop_zero]
        exact ih _ checked _ m clean
    next old => simp at checked

private theorem move_live (A B : Arena) (old fresh : Wire) (ho : old∈A.live)
    (h : A.reserve {fresh}=some B) :
    (B.retireSet {old}).live=A.live.image (Equiv.swap old fresh) := by
  have hv := (A.reserve_success {fresh}).mp ⟨B,h⟩
  have hf : fresh∉A.live := fun hh => Finset.disjoint_left.mp hv.2 hh (by simp)
  apply Finset.coe_injective
  simpa [Arena.retireSet,reserve_live A B {fresh} h,Finset.coe_sdiff,
    Finset.coe_image,Finset.coe_union,Finset.coe_singleton,Set.union_singleton] using
    (Equiv.image_swap_of_mem_of_notMem (s:=(↑A.live : Set Wire)) ho hf).symm

theorem Arena.checkRepack_live (A C : Arena) (ms : List (Wire × Wire))
    (checked : A.checkRepack ms=some C) :
    C.live=A.live.image (repackEquiv ms) := by
  induction ms generalizing A with
  | nil => simp only [checkRepack,Option.some.injEq] at checked; subst C; simp [repackEquiv]
  | cons p ps ih =>
    simp only [checkRepack] at checked
    split at checked
    next old =>
      cases hr : A.reserve {p.2} with
      | none => simp [hr] at checked
      | some B =>
        simp only [hr] at checked
        rw [ih _ checked,move_live A B p.1 p.2 old hr,Finset.image_image]
        rfl
    next old => simp at checked

/-- Ownership moves with the same wire permutation as the physical data. -/
theorem Arena.checkRepack_owned (A C : Arena) (ms : List (Wire × Wire))
    (checked : A.checkRepack ms=some C) (xs : List Wire)
    (owned : xs.toFinset⊆A.live) : (repackView ms xs).toFinset⊆C.live := by
  rw [repackView_eq_map,checkRepack_live A C ms checked]
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  exact Finset.mem_image_of_mem _ (owned (List.mem_toFinset.mpr ha))

end ECDSAAdd.Arithmetic.Paper935
