import ECDSAAdd.Arithmetic.Paper935.FusedPlacedExecution

namespace ECDSAAdd.Arithmetic.Paper935

private theorem placement_slice (pre xs post : List Wire) :
    (List.range' pre.length xs.length).map (fusedPlacementMap (pre++xs++post))=xs := by
  apply List.ext_getElem (by simp)
  intro i hi hx
  simp only [List.getElem_map,List.getElem_range',Nat.one_mul,fusedPlacementMap]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_append]; omega)]
  rw [List.getElem_append_left (by simp only [List.length_append]; omega)]
  rw [List.getElem_append_right (by omega)]
  simp

theorem fusedLiftPlacement_payload (sign : Wire) (row pool : List Wire)
    (len : row.length=280) :
    magnitudePayload.map (fusedPlacementMap (sign::row++pool))=row := by
  simpa only [List.length_singleton,len,magnitudePayload,List.singleton_append] using
    placement_slice [sign] row pool

theorem fusedFoldPlacement_payload (row word pool : List Wire)
    (len : row.length=280) :
    (fusedFoldLow++fusedFoldHigh).map
      (fusedPlacementMap (fusedFoldPlacement row word pool))=row := by
  have low := placement_slice (row.drop 256) (row.take 256) (word++pool.take 1)
  have high := placement_slice [] (row.drop 256) (row.take 256++word++pool.take 1)
  have dropLen : (row.drop 256).length=24 := by simp [len]
  have takeLen : (row.take 256).length=256 := by simp [len]
  have rangeLow : List.range' 24 256=(List.range 256).map (24+·) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp
  simp only [dropLen,takeLen,rangeLow,List.append_assoc] at low
  have zeroRange : List.range' 0 24=List.range 24 := by decide
  simp only [List.length_nil,dropLen,List.nil_append,zeroRange,
    List.append_assoc] at high
  rw [List.map_append]
  change _ ++ _ = _
  have low' : fusedFoldLow.map (fusedPlacementMap (fusedFoldPlacement row word pool))=
      row.take 256 := by simpa only [fusedFoldPlacement,fusedFoldLow,List.append_assoc] using low
  have high' : fusedFoldHigh.map (fusedPlacementMap (fusedFoldPlacement row word pool))=
      row.drop 256 := by simpa only [fusedFoldPlacement,fusedFoldHigh,List.append_assoc] using high
  rw [low',high',List.take_append_drop]

theorem fusedLiftPlacement_pool_zero (A B : Arena) (row pool : List Wire) (sign : Wire)
    (len : row.length=280) (s : BasisState) (ready : A.Ready s)
    (allocated : A.borrowMany 24=some (B,pool)) :
    ∀i<24,s (fusedPlacementMap (sign::row++pool) (281+i))=false := by
  have hc := fusedPool_zero A B pool s ready allocated
  intro i hi
  dsimp only [Wire] at i hi
  have offset : (sign::row).length≤281+i := by simp [len]
  change s (((sign::row)++pool).getD (281+i) 0)=false
  rw [List.getD_append_right _ _ _ _ offset]
  simp only [List.length_cons,len,Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem pool 0 (by omega)]
  exact hc.2.1 _ (List.getElem_mem _)

/-- The actual lifted physical row is exactly the fold's low-then-high input;
this discharges the fold encoding premise rather than assuming it again. -/
theorem placedLift_fold_encoding (A B : Arena) (row word pool : List Wire) (sign : Wire)
    (len : row.length=280) (distinct : (sign::row).Nodup)
    (owned : (sign::row).toFinset⊆A.live)
    (allocated : A.borrowMany 24=some (B,pool)) (call : FusedCall)
    (s : State) (m : List Bool)
    (ready : A.Ready s.basis)
    (encoding : MagnitudeEncodes call.coefficient
      (fun q => s.basis (fusedPlacementMap (sign::row++pool) q)))
    (good : call.LiftGood) :
    regValue ((fusedFoldLow++fusedFoldHigh).map
      (fusedPlacementMap (fusedFoldPlacement row word pool)))
      (run (placedMagnitude (fusedPlacementMap (sign::row++pool)) false) m s).basis =
      call.coefficient.natAbs := by
  have value := (placedMagnitude_of_good _
    (fusedLiftPlacementMap_injective A B row pool sign len distinct owned allocated)
    call s m (fusedLiftPlacement_pool_zero A B row pool sign len s.basis ready allocated)
    encoding good).1
  rw [fusedFoldPlacement_payload row word pool len]
  simpa only [fusedLiftPlacement_payload sign row pool len] using value

end ECDSAAdd.Arithmetic.Paper935
