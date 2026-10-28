import ECDSAAdd.Arithmetic.Paper935.FoldRider
import ECDSAAdd.Arithmetic.Paper935.FoldHalvePhysical

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic RecordedQuantum

private theorem shift_physical (c : Wire) (r : List Wire) (hn : (c::r).Nodup) :
    GatePhysical (shiftRight c r) := by
  induction r with
  | nil => simp [shiftRight,GatePhysical]
  | cons a rest ih =>
    cases rest with
    | nil => simp [shiftRight,GatePhysical]
    | cons b bs =>
      have ca := (List.nodup_cons.mp hn).1
      have dataND := (List.nodup_cons.mp hn).2
      have tailND := (List.nodup_cons.mp dataND).2
      have caa : c≠a := fun h => ca (by simp [h])
      have cab : c≠b := fun h => ca (by simp [h])
      have ab : a≠b := fun h => (List.nodup_cons.mp dataND).1 (by simp [h])
      have nextND : (c::b::bs).Nodup :=
        List.nodup_cons.mpr ⟨fun h => ca (List.mem_cons_of_mem a h),tailND⟩
      rw [shiftRight,gatePhysical_append]
      refine ⟨?_,ih nextND⟩
      simp [GatePhysical,cswap,PhysicalInstr,ProperGate,cab,ab,Ne.symm ab]

theorem foldRiderParity_physical : GatePhysical foldRiderParityProgram := by
  have mint : GatePhysical [.CCX 273 1 0] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  have kill : GatePhysical [.measureX 0 [] [.CZ 273 1]] := by simp [GatePhysical,PhysicalInstr]
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr ⟨mint,fold256_physical true⟩,kill⟩

theorem foldRider_physical : GatePhysical foldRiderProgram := by
  have nd : (273::fold256Word).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_range'⟩
    simp only [fold256Word,List.mem_range']
    omega
  exact (gatePhysical_append _ _).mpr ⟨foldRiderParity_physical,shift_physical _ _ nd⟩

theorem foldRiderParity_support : wires foldRiderParityProgram⊆Finset.range 274 := by
  have mint : wires [.CCX 273 1 0]⊆Finset.range 274 := by decide
  have kill : wires [.measureX 0 [] [.CZ 273 1]]⊆Finset.range 274 := by decide
  have fold := (fold256_support true).trans (Finset.range_mono (by decide : 273≤274))
  rw [foldRiderParityProgram,wires_append,wires_append]
  exact Finset.union_subset (Finset.union_subset mint fold) kill

theorem foldRider_support : wires foldRiderProgram⊆Finset.range 274 := by
  have rotation : wires (shiftRight 273 fold256Word)⊆Finset.range 274 := by
    rw [(shift_wires 273 fold256Word).1]
    simp only [fold256Word,List.length_range',show ¬256<2 by decide,if_false]
    intro q h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_range'] at h
    apply Finset.mem_range.mpr
    dsimp only [Wire] at *
    omega
  rw [foldRiderProgram,wires_append]
  exact Finset.union_subset foldRiderParity_support rotation

end ECDSAAdd.Arithmetic.Paper935
