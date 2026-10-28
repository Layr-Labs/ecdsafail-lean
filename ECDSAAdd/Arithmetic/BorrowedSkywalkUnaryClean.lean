import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryLayout

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private def borrowedWorkIds : List Nat :=
  List.range' 512 257++List.range' 1540 256++[1797]++List.range' 1798 257++[769]
private def oldAvailableWorkIds : List Nat :=
  List.range' 1540 257++List.range' 1798 256++[1797]++List.range' 512 257++
    [2313]++[769,1027,2054,2055]

private theorem borrowedWorkIds_available : borrowedWorkIds⊆oldAvailableWorkIds := by
  intro j hj
  simp only [borrowedWorkIds,oldAvailableWorkIds,List.mem_append,List.mem_cons,
    List.not_mem_nil,List.mem_range'_1,or_false] at hj ⊢
  omega

/-- Every declared work site, including the untouched ghost mask, is already
clean under the original field-work and explicitly unused-site interface. -/
theorem borrowedSkywalkUnary_work_subset (w : Nat → Wire) :
    (borrowedSkywalkUnary w).work ⊆ (skywalkSharedField w).work++skywalkSharedUnused w := by
  have hb : (borrowedSkywalkUnary w).work=borrowedWorkIds.map w := by
    simp [ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work,
      borrowedSkywalkUnary,borrowedWorkIds,wireBlock,List.map_append,List.append_assoc]
  have ho : (skywalkSharedField w).work++skywalkSharedUnused w=oldAvailableWorkIds.map w := by
    simp [ModInPlaceLayout.work,ModAddCoreLayout.work,skywalkSharedField,
      skywalkSharedUnused,oldAvailableWorkIds,wireBlock,List.map_append,List.append_assoc]
  rw [hb,ho]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨j,borrowedWorkIds_available hj,rfl⟩

theorem borrowedSkywalkUnary_clean_base (w : Nat → Wire) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) :
    regValue (borrowedSkywalkUnary w).work base=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  have h := borrowedSkywalkUnary_work_subset w hq
  rcases List.mem_append.mp h with h|h
  · exact (regValue_zero _ _).mp hw q h
  · exact (regValue_zero _ _).mp hu q h

/-- The original 257-bit pair frame transports all borrowed clean work. -/
theorem borrowedSkywalkUnary_clean_frame (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (base st : BasisState) (X Y : Nat)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (hf : PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X Y st) :
    regValue (borrowedSkywalkUnary w).work st=0 := by
  have hb := (regValue_zero _ _).mp (borrowedSkywalkUnary_clean_base w base hw hu)
  apply (regValue_zero _ _).mpr
  intro q hq
  have ha := borrowedSkywalkUnary_workAway w hn q hq
  exact (hf.2.2 q ha.1 ha.2).trans (hb q hq)

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_work_subset
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_clean_frame
