import ECDSAAdd.Arithmetic.Paper935.FusedMagnitudeProgram

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic RecordedQuantum

/-- All ordinary gates remain nonaliased after relocating the lift pool.
This property is independent of coefficient success conditions. -/
theorem magnitudeWindow_physical (b : Bool) : GatePhysical (magnitudeWindow b) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have h := lift24Program_physical b j hj
  have injective := magnitudeWindowMap_injective
  cases j <;> simp_all [renameInstr,PhysicalInstr,ProperGate,injective.eq_iff]

theorem fusedMagnitudeLift_physical (inverse : Bool) : GatePhysical (fusedMagnitudeLift inverse) := by
  have fan : GatePhysical (signComplement 0 magnitudePayload) := by
    intro i hi
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
    change (0 : Wire)≠q
    simp only [magnitudePayload,List.mem_range'] at hq
    dsimp only [Wire] at *
    omega
  have rev : GatePhysical (signComplement 0 magnitudePayload).reverse := by
    intro i hi
    exact fan i (List.mem_reverse.mp hi)
  cases inverse <;> simp only [fusedMagnitudeLift,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨fan,magnitudeWindow_physical false⟩
  · exact ⟨magnitudeWindow_physical true,rev⟩

end ECDSAAdd.Arithmetic.Paper935
