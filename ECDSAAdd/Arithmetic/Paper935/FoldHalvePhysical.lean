import ECDSAAdd.Arithmetic.Paper935.FoldSeam

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic RecordedQuantum

theorem fold256_physical (subtract : Bool) : GatePhysical (fold256Program subtract) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have h := fold16Program_physical subtract j hj
  cases j <;> simp_all [renameInstr,PhysicalInstr,ProperGate,fold256Place_injective.eq_iff]

private theorem rotate_physical (r : List Wire) (hn : r.Nodup) : GatePhysical (rotateRight r) := by
  induction r with
  | nil => simp [rotateRight,GatePhysical]
  | cons a rest ih =>
    cases rest with
    | nil => simp [rotateRight,GatePhysical]
    | cons b bs =>
      have tailND := (List.nodup_cons.mp hn).2
      have apart : a≠b := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
      rw [rotateRight,gatePhysical_append]
      refine ⟨?_,ih tailND⟩
      simp [GatePhysical,swapBits,PhysicalInstr,ProperGate,apart,Ne.symm apart]

theorem foldParity_physical : GatePhysical foldParityProgram := by
  have copy : GatePhysical [.CX 1 0] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨copy,fold256_physical true⟩,copy⟩

theorem foldHalve_physical : GatePhysical foldHalveProgram :=
  (gatePhysical_append _ _).mpr ⟨foldParity_physical,rotate_physical _ List.nodup_range'⟩

theorem foldSeam_physical (n : Nat) : GatePhysical (foldSeamProgram n) := by
  induction n with
  | zero => simp [foldSeamProgram,GatePhysical]
  | succ n ih => exact (gatePhysical_append _ _).mpr ⟨foldHalve_physical,ih⟩

theorem fold256_support (subtract : Bool) : wires (fold256Program subtract)⊆Finset.range 273 := by
  intro q hq
  rw [fold256Program,renameProgram_support] at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  have bound := Finset.mem_range.mp (fold16Program_support subtract ha)
  apply Finset.mem_range.mpr
  simp only [fold256Place]
  dsimp only [Wire] at *
  split_ifs <;> omega

theorem foldParity_support : wires foldParityProgram⊆Finset.range 273 := by
  have copy : wires [.CX 1 0]⊆Finset.range 273 := by
    intro q h
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at h
    apply Finset.mem_range.mpr
    dsimp only [Wire] at *
    omega
  rw [foldParityProgram,wires_append,wires_append]
  exact Finset.union_subset (Finset.union_subset copy (fold256_support true)) copy

theorem foldHalve_support : wires foldHalveProgram⊆Finset.range 273 := by
  have rotation : wires (rotateRight fold256Word)⊆Finset.range 273 := by
    rw [(rotate_wires fold256Word).1]
    simp only [fold256Word,List.length_range',show ¬256<2 by decide,if_false]
    intro q h
    simp only [List.mem_toFinset,List.mem_range'] at h
    apply Finset.mem_range.mpr
    dsimp only [Wire] at *
    omega
  rw [foldHalveProgram,wires_append]
  exact Finset.union_subset foldParity_support rotation

theorem foldSeam_support (n : Nat) : wires (foldSeamProgram n)⊆Finset.range 273 := by
  induction n with
  | zero => simp [foldSeamProgram,wires]
  | succ n ih =>
    rw [foldSeamProgram,wires_append]
    exact Finset.union_subset foldHalve_support ih

end ECDSAAdd.Arithmetic.Paper935
