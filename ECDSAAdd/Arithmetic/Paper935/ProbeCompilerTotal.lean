import ECDSAAdd.Arithmetic.Paper935.ProbeChunks

namespace ECDSAAdd.Arithmetic.Paper935

/-- Positive public chunk width and enough separated work suffice for the
actual zero-probe compiler; all chunks and scratch views are checked. -/
theorem compileProbe_exists (one target : Wire) (inputs work : List Wire) (width : Nat)
    (positive : 0<width) (distinct : ([one,target]++inputs++work).Nodup)
    (space : width+(inputs.toChunks width).length≤work.length) :
    ∃ bs,compileProbe one target inputs work width=some bs := by
  let cs := inputs.toChunks width
  let flags := work.take cs.length
  let scratch := work.drop cs.length
  let xs := flags.zip cs
  have flagLength : flags.length=cs.length := by
    dsimp only [flags,cs]
    simp only [List.length_take]
    omega
  have first : xs.map Prod.fst=flags := List.map_fst_zip (by omega)
  have second : xs.map Prod.snd=cs := List.map_snd_zip (by omega)
  have inputsEq : xs.flatMap Prod.snd=inputs := by
    rw [List.flatMap_def,second]
    exact probeChunks_flatten inputs width
  have splitWork : flags++scratch=work := List.take_append_drop cs.length work
  have geometry : ([one,target]++xs.map Prod.fst++xs.flatMap Prod.snd++scratch).Nodup := by
    rw [first,inputsEq]
    rw [←splitWork] at distinct
    clear first second inputsEq flagLength space splitWork
    simp_all only [List.nodup_append',List.disjoint_append_left,List.disjoint_append_right,List.disjoint_comm,and_true]
  have fits : BlockedZero.Fits xs scratch := by
    intro p hp
    have hc : p.2∈cs := (List.of_mem_zip hp).2
    have len := probeChunks_lengths inputs width positive p.2 hc
    dsimp only [scratch,cs]
    simp only [List.length_drop]
    omega
  have valid := chunks_valid_of_distinct one target xs scratch geometry
  refine ⟨BlockedZero.chunks xs scratch,?_⟩
  change (if BlockedZero.Valid one target (BlockedZero.chunks xs scratch) ∧
    xs.flatMap Prod.snd=inputs ∧ BlockedZero.Fits xs scratch then some (BlockedZero.chunks xs scratch) else none)=_
  rw [if_pos ⟨valid,inputsEq,fits⟩]

/-- The allocator supplies separated scratch for the exact emitted zero probe. -/
theorem compileBorrowedProbe_exists (A : Arena) (one target : Wire) (inputs : List Wire) (width : Nat)
    (positive : 0<width) (distinct : ([one,target]++inputs).Nodup)
    (owned : ([one,target]++inputs).toFinset⊆A.live)
    (budget : A.live.card+(width+(inputs.toChunks width).length)≤935) :
    ∃ D work bs,compileBorrowedProbe A one target inputs width=some (D,work,bs) := by
  obtain ⟨D,work,borrow⟩ := (A.borrowMany_capacity (width+(inputs.toChunks width).length)).mpr budget
  have geometry := A.borrowMany_append D _ work _ borrow distinct owned
  have length := (A.borrowMany_contract D _ work borrow).1
  obtain ⟨bs,compiled⟩ := compileProbe_exists one target inputs work width positive geometry.1 (by rw [length])
  exact ⟨D,work,bs,by simp [compileBorrowedProbe,borrow,compiled]⟩

end ECDSAAdd.Arithmetic.Paper935
