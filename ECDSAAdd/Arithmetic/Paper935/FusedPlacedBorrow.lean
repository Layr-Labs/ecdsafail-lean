import ECDSAAdd.Arithmetic.Paper935.FusedPlacementViews
import ECDSAAdd.Arithmetic.Paper935.FusedBoundaryZero

namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] fusedMagnitudeLift fusedRowFoldSource

private theorem placement_mem (ports : List Wire) (i : Nat) (hi : i<ports.length) :
    fusedPlacementMap ports i∈ports := by
  rw [fusedPlacementMap,List.getD_eq_getElem ports 0 hi]
  exact List.getElem_mem hi

/-- Actual measurement supplies the zero word, and the disjoint lift leaves
it zero. No assertion that measurement has cleared phase is made. -/
theorem placedMagnitude_demolished_word (sign : Wire) (row pool word : List Wire)
    (hr : row.length=280) (hp : pool.length=24)
    (disjoint : List.Disjoint word (sign::row++pool))
    (s : State) (m n : List Bool) (inverse : Bool) :
    ∀q∈word,(run (placedMagnitude (fusedPlacementMap (sign::row++pool)) inverse) n
      (run (fusedDemolish word) m s)).basis q=false := by
  intro q hq
  have outside : q∉(Finset.range 305).image (fusedPlacementMap (sign::row++pool)) := by
    intro inside
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp inside
    have bound : i<(sign::row++pool).length := by
      simpa only [List.length_cons,List.length_append,hr,hp] using Finset.mem_range.mp hi
    exact disjoint hq (eq ▸ placement_mem _ i bound)
  exact (placedMagnitude_outside _ inverse _ n q outside).trans
    (fusedDemolish_zero word s m q hq)

private theorem lift_pool_port (sign : Wire) (row pool : List Wire)
    (hr : row.length=280) (hp : pool.length=24) (i : Nat) (hi : i<24) :
    fusedPlacementMap (sign::row++pool) (281+i)=pool[i]'(by omega) := by
  change ((sign::row)++pool).getD (281+i) 0=_
  rw [List.getD_append_right _ _ _ _ (by simp [hr])]
  simp only [List.length_cons,hr,Nat.add_sub_cancel_left]
  exact List.getD_eq_getElem pool 0 (by omega)

/-- Every physical pool site is restored after the actual lift. -/
theorem placedMagnitude_pool_restored (A B : Arena) (sign : Wire) (row pool : List Wire)
    (hr : row.length=280) (distinct : (sign::row).Nodup)
    (owned : (sign::row).toFinset⊆A.live) (allocated : A.borrowMany 24=some (B,pool))
    (s : State) (m : List Bool) (ready : A.Ready s.basis) :
    ∀q∈pool,(run (placedMagnitude (fusedPlacementMap (sign::row++pool)) false) m s).basis q=false := by
  have clean := fusedLiftPlacement_pool_zero A B row pool sign hr s.basis ready allocated
  have hp := (A.borrowMany_contract B 24 pool allocated).1
  let f := fusedPlacementMap (sign::row++pool)
  have sem := run_rename_pool f (Finset.range 305)
    (fusedLiftPlacementMap_injective A B row pool sign hr distinct owned allocated)
    (fusedMagnitudeLift false) (fusedMagnitudeLift_support false) m
    (pullState f s) s rfl (fun _ _ => rfl)
  have tidy := fusedMagnitudeLift_cleanup (pullState f s) m clean
  intro q hq
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hq
  have hi' : i<24 := by omega
  have atPort := (sem.2 (281+i) (by simp only [Finset.mem_range]; omega)).trans (tidy.1 i hi')
  simpa only [f,lift_pool_port sign row pool hr hp i hi',eq] using atPort

/-- A successful reservation is actually returned after lift cleanup. The
final live set and readiness are those of the pre-borrow arena. -/
theorem placedMagnitude_release_pool (A B : Arena) (sign : Wire) (row pool : List Wire)
    (hr : row.length=280) (distinct : (sign::row).Nodup)
    (owned : (sign::row).toFinset⊆A.live) (allocated : A.borrowMany 24=some (B,pool))
    (s : State) (m : List Bool) (ready : A.Ready s.basis) :
    let out := run (placedMagnitude (fusedPlacementMap (sign::row++pool)) false) m s
    ∃ C, B.release pool.toFinset out.basis=some C ∧ C.live=A.live ∧ C.Ready out.basis := by
  have hc := A.borrowMany_contract B 24 pool allocated
  have live : B.live=A.live∪pool.toFinset := by
    have h := hc.2.2
    unfold Arena.reserve at h
    split at h
    next valid => cases h; rfl
    next invalid => simp at h
  have poolOwned : pool.toFinset⊆B.live := by rw [live]; exact Finset.subset_union_right
  have support : wires (placedMagnitude (fusedPlacementMap (sign::row++pool)) false)⊆B.live := by
    rw [placedMagnitude,renameProgram_support]
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    have bound := Finset.mem_range.mp (fusedMagnitudeLift_support false ha)
    have port := placement_mem (sign::row++pool) a (by
      simpa only [List.length_cons,List.length_append,hr,hc.1] using bound)
    change _∈(sign::row)++pool at port
    rcases List.mem_append.mp port with head|tail
    · rw [live]
      exact Finset.mem_union_left _ (owned (List.mem_toFinset.mpr head))
    · exact poolOwned (List.mem_toFinset.mpr tail)
  have before := (fusedPool_zero A B pool s.basis ready allocated).2.2
  have after : B.Ready (run (placedMagnitude (fusedPlacementMap (sign::row++pool)) false) m s).basis := by
    intro q hq hn
    rw [run_preserves_outside _ m s q (fun h => hn (support h))]
    exact before q hq hn
  have clean := placedMagnitude_pool_restored A B sign row pool hr distinct owned allocated s m ready
  obtain ⟨C,release⟩ := (B.release_success pool.toFinset _).mpr
    ⟨poolOwned,fun q h => clean q (List.mem_toFinset.mp h)⟩
  refine ⟨C,release,?_,B.release_ready C _ _ after release⟩
  have outLive : C.live=B.live\pool.toFinset := by
    unfold Arena.release at release
    split at release
    next valid => cases release; rfl
    next invalid => simp at release
  rw [outLive,live]
  have dis := ((A.reserve_success pool.toFinset).mp ⟨B,hc.2.2⟩).2
  ext q
  simp only [Finset.mem_sdiff,Finset.mem_union]
  constructor
  · intro h; rcases h.1 with ha|hp
    · exact ha
    · exact False.elim (h.2 hp)
  · intro h
    exact ⟨Or.inl h,fun hp => Finset.disjoint_left.mp dis h hp⟩

private theorem fold_carry_port (row word pool : List Wire)
    (hr : row.length=280) (hw : word.length=256) (hp : pool.length=24) :
    fusedPlacementMap (fusedFoldPlacement row word pool) 536=pool[0]'(by omega) := by
  have size : (row.drop 256++row.take 256++word).length=536 := by simp [hr,hw]
  change ((row.drop 256++row.take 256++word)++pool.take 1).getD 536 0=_
  rw [List.getD_append_right _ _ _ _ (by omega),size]
  simp only [Nat.sub_self]
  rw [List.getD_eq_getElem _ _ (by simp [hp])]
  exact List.getElem_take

/-- The subsequent fold's carry is the already cleaned pool root P[0]. -/
theorem placedMagnitude_fold_carry_zero (A B : Arena) (sign : Wire) (row word pool : List Wire)
    (hr : row.length=280) (hw : word.length=256) (distinct : (sign::row).Nodup)
    (owned : (sign::row).toFinset⊆A.live) (allocated : A.borrowMany 24=some (B,pool))
    (s : State) (m : List Bool) (ready : A.Ready s.basis) :
    (run (placedMagnitude (fusedPlacementMap (sign::row++pool)) false) m s).basis
      (fusedPlacementMap (fusedFoldPlacement row word pool) 536)=false := by
  have hp := (A.borrowMany_contract B 24 pool allocated).1
  rw [fold_carry_port row word pool hr hw hp]
  exact placedMagnitude_pool_restored A B sign row pool hr distinct owned allocated s m ready
    _ (List.getElem_mem (by omega))

end ECDSAAdd.Arithmetic.Paper935
