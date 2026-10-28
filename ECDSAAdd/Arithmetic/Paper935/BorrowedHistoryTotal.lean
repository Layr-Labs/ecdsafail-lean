import ECDSAAdd.Arithmetic.Paper935.BorrowGeometry

namespace ECDSAAdd.Arithmetic.Paper935

/-- Successful growing-history compilation follows from ordinary physical
ownership, separation and available capacity. No interpreter premise occurs. -/
theorem compileGrowingHistory_exists (A : Arena) (record : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire)
    (distinct : ([one,zz,pos,output,port,frozen]++counter++coeffBits++record).Nodup)
    (owned : ([one,zz,pos,output,port,frozen]++counter++coeffBits++record).toFinset⊆A.live)
    (signView : sign∈counter)
    (budget : A.live.card+(capacity-record.length)+max counter.length (coeffBits.length+2)≤935) :
    ∃ B D work H,compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H) := by
  obtain ⟨B,extra,grow⟩ := (A.borrowMany_capacity (capacity-record.length)).mpr (by omega)
  have growLayout := A.borrowMany_append B _ extra _ grow distinct owned
  have growCard := (A.borrowMany_live B _ extra grow).2
  obtain ⟨D,work,borrow⟩ := (B.borrowMany_capacity (max counter.length (coeffBits.length+2))).mpr (by omega)
  have workLayout := B.borrowMany_append D _ work _ borrow growLayout.1 growLayout.2
  have workLength := (B.borrowMany_contract D _ work borrow).1
  have allDistinct : ([one,zz,pos,output,port,frozen]++counter++coeffBits++(record++extra)++work).Nodup := by
    simpa only [List.append_assoc] using workLayout.1
  obtain ⟨H,compiled⟩ := compileHistory_exists one zz pos sign output port frozen counter coeffBits (record++extra) work
    allDistinct signView (by rw [workLength]; exact Nat.le_max_left _ _) (by rw [workLength]; exact Nat.le_max_right _ _)
  refine ⟨B,D,work,H,?_⟩
  simp [compileGrowingHistory,planHistoryGrow,grow,borrow,compiled]

end ECDSAAdd.Arithmetic.Paper935
