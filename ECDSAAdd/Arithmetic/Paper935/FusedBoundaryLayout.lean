import ECDSAAdd.Arithmetic.Paper935.CloserWalk
import ECDSAAdd.Arithmetic.Paper935.Repack

namespace ECDSAAdd.Arithmetic.Paper935

/-- The relocation journal acts on every view, including the sign, pool and
borrowed word. It is not an assertion that a particular journal was compiled. -/
def repackEquiv : List (Wire × Wire) → Equiv Wire Wire
  | [] => Equiv.refl _
  | (a,b)::ms => (Equiv.swap a b).trans (repackEquiv ms)

theorem repackView_eq_map (ms : List (Wire × Wire)) (xs : List Wire) :
    repackView ms xs=xs.map (repackEquiv ms) := by
  induction ms generalizing xs with
  | nil => simp [repackView,repackEquiv]
  | cons p ps ih => simp [repackView,repackEquiv,ih,List.map_map,Function.comp_def]

theorem repackView_length (ms : List (Wire × Wire)) (xs : List Wire) :
    (repackView ms xs).length=xs.length := by rw [repackView_eq_map,List.length_map]

theorem repack_basis (ms : List (Wire × Wire)) (valid : ∀p∈ms,p.1≠p.2)
    (s : State) (m : List Bool) :
    ∀q,(run (repack ms) m s).basis (repackEquiv ms q)=s.basis q := by
  induction ms generalizing s with
  | nil => intro q; rfl
  | cons p ps ih =>
    have ht : ∀r∈ps,r.1≠r.2 := fun r hr => valid r (by simp [hr])
    intro q
    simp only [repack,run_append,(rehome_cost p.1 p.2).2,List.take_zero,List.drop_zero]
    exact (ih ht _ (Equiv.swap p.1 p.2 q)).trans
      ((rehome_run p.1 p.2 (valid p (by simp)) s []).2 q)

/-- Zero words survive a journal when their views move with the data. -/
theorem repack_zero (ms : List (Wire × Wire)) (valid : ∀p∈ms,p.1≠p.2)
    (xs : List Wire) (s : State) (m : List Bool) (zero : ∀q∈xs,s.basis q=false) :
    ∀q∈repackView ms xs,(run (repack ms) m s).basis q=false := by
  rw [repackView_eq_map]
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  exact (repack_basis ms valid s m a).trans (zero a ha)

/-- Actual compiled endpoint row, after any explicit relocation journal. -/
def fusedEndpointRow (slots : List HistoricalSlot) (ms : List (Wire × Wire)) : List Wire :=
  repackView ms (walkExitBank walkSeedBank slots).fv.payload

theorem fusedEndpointRow_length (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (ms : List (Wire × Wire)) :
    (fusedEndpointRow slots ms).length=280 := by
  rw [fusedEndpointRow,repackView_length]
  exact (compileAuthorWalk_exit_widths slots compiled).2.2.1

theorem fusedEndpointRow_distinct (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (ms : List (Wire × Wire)) :
    (repackEquiv ms (walkExitBank walkSeedBank slots).fv.sign :: fusedEndpointRow slots ms).Nodup := by
  have nd := (compileAuthorWalk_exit_owned slots compiled).1
  have row : ((walkExitBank walkSeedBank slots).fv.sign ::
      (walkExitBank walkSeedBank slots).fv.payload).Nodup := by
    rw [List.nodup_iff_count_le_one] at nd ⊢
    intro q
    have h := nd q
    simp only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,WindowRow.wires,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  simpa only [fusedEndpointRow,repackView_eq_map,List.map_cons] using
    row.map (repackEquiv ms).injective

/-- Appending a pool selected by the allocator gives an injective finite
lift placement. No gate-alias condition is separately assumed. -/
theorem fusedLiftPlacement_injective (A B : Arena) (row pool : List Wire) (sign : Wire)
    (distinct : (sign::row).Nodup) (owned : (sign::row).toFinset⊆A.live)
    (allocated : A.borrowMany 24=some (B,pool)) :
    Function.Injective (sign::row++pool).get := by
  have hc := A.borrowMany_contract B 24 pool allocated
  have hv := (A.reserve_success pool.toFinset).mp ⟨B,hc.2.2⟩
  apply List.Nodup.injective_get
  change ((sign::row)++pool).Nodup
  apply List.nodup_append.mpr
  refine ⟨distinct,hc.2.1,?_⟩
  intro a ha b hb eq
  subst b
  exact Finset.disjoint_left.mp hv.2 (owned (List.mem_toFinset.mpr ha))
    (List.mem_toFinset.mpr hb)

/-- Pool zeroes follow from actual reservation and arena readiness, rather
than being asserted as an extra quantum precondition. -/
theorem fusedPool_zero (A B : Arena) (pool : List Wire) (s : BasisState)
    (ready : A.Ready s) (allocated : A.borrowMany 24=some (B,pool)) :
    pool.length=24 ∧ (∀q∈pool,s q=false) ∧ B.Ready s := by
  have hc := A.borrowMany_contract B 24 pool allocated
  have hr := A.reserve_ready B pool.toFinset s ready hc.2.2
  exact ⟨hc.1,fun q hq => hr.2 q (List.mem_toFinset.mpr hq),hr.1⟩

/-- The compiled closer has enough free capacity for the plateau pool.
This alone does not allocate a second 256-bit host or prove a whole peak. -/
theorem fusedClosedPool_exists (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    ∃B pool,(authorClosedArena slots).borrowMany 24=some (B,pool) := by
  apply (Arena.borrowMany_capacity _ _).mpr
  rw [compileAuthorWalk_closed_card slots compiled]
  decide

/-- Fold reference order: high24, low256, borrowed word256, pool root. -/
def fusedFoldPlacement (row word pool : List Wire) : List Wire :=
  row.drop 256 ++ row.take 256 ++ word ++ pool.take 1

theorem fusedFoldPlacement_length (row word pool : List Wire)
    (hr : row.length=280) (hw : word.length=256) (hp : pool.length=24) :
    (fusedFoldPlacement row word pool).length=537 := by
  simp [fusedFoldPlacement,List.length_append,List.length_drop,List.length_take,hr,hw,hp]

/-- The borrowed output word is already owned, whereas the pool is newly
reserved. These different lifetime roles still give one alias-free map. -/
theorem fusedFoldPlacement_injective (A B : Arena) (row word pool : List Wire)
    (distinct : (row++word).Nodup) (owned : (row++word).toFinset⊆A.live)
    (allocated : A.borrowMany 24=some (B,pool)) :
    Function.Injective (fusedFoldPlacement row word pool).get := by
  have hc := A.borrowMany_contract B 24 pool allocated
  have hv := (A.reserve_success pool.toFinset).mp ⟨B,hc.2.2⟩
  have nd : ((row++word)++pool).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨distinct,hc.2.1,?_⟩
    intro a ha b hb eq
    subst b
    exact Finset.disjoint_left.mp hv.2 (owned (List.mem_toFinset.mpr ha))
      (List.mem_toFinset.mpr hb)
  apply List.Nodup.injective_get
  rw [List.nodup_iff_count_le_one] at nd ⊢
  intro q
  have h := nd q
  have parts := congrArg (List.count q) (List.take_append_drop 256 row)
  have small := congrArg (List.count q) (List.take_append_drop 1 pool)
  simp only [fusedFoldPlacement,List.count_append] at h parts small ⊢
  omega

end ECDSAAdd.Arithmetic.Paper935
