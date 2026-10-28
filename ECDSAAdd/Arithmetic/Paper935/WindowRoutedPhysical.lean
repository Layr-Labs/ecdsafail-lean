import ECDSAAdd.Arithmetic.Paper935.WindowRouted
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps ECDSAAdd.RecordedQuantum

private theorem proper_physical (p : Program) (h : ProperProgram p) : GatePhysical p :=
  (physical_embed p).mp (physical_of_proper p h)

private theorem branch_physical (q c u k : Wire) (a b : List Wire)
    (hn : (q::c::u::k::(a++b)).Nodup) :
    GatePhysical (branchRow q c u k a b) ∧ GatePhysical (branchRowInverse q c u k a b) := by
  have core := branchCore_proper c u k a b (List.nodup_cons.mp hn).2
  have hqu : q≠u := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hcu : c≠u := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
  have first : GatePhysical [.CCX q c u] := by simp [GatePhysical,PhysicalInstr,ProperGate,hqu,hcu]
  have last : GatePhysical (eraseAnd q c u) := by simp [GatePhysical,eraseAnd,PhysicalInstr]
  constructor
  · simpa only [branchRow,branchCore,gatePhysical_append,and_assoc] using
      And.intro first (And.intro (proper_physical _ core) last)
  · exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr
      ⟨first,proper_physical _ (properProgram_reverse _ core)⟩,last⟩

/-- Static ordinary-gate legality of both actual measured routed streams. -/
theorem RoutedBankLayout.physical (L : RoutedBankLayout) (hv : L.Valid) :
    GatePhysical L.program ∧ GatePhysical L.inverse := by
  have a := branch_physical L.q L.parity L.u L.k _ _ hv.addFG
  have b := branch_physical L.q L.parity L.u L.k _ _ hv.addV
  have r := routeRows_proper _ _ _ _ _ hv.route
  have hg : L.gsign≠L.glow := by
    intro h; exact (List.nodup_cons.mp hv.half).1 (by simp [←h])
  have f := finishRows_proper _ _ _ _ _ _ hv.double hg
  simp only [program,inverse,routedStage,routedStageInverse,rowStage,rowStageInverse,
    branchPair,branchPairInverse,gatePhysical_append]
  exact ⟨⟨proper_physical _ r,⟨⟨a.1,b.1⟩,proper_physical _ f⟩⟩,
    ⟨⟨proper_physical _ (properProgram_reverse _ f),⟨b.2,a.2⟩⟩,
      proper_physical _ (properProgram_reverse _ r)⟩⟩

/-- Fresh inverse measurements use precisely the same physical addresses. -/
theorem RoutedBankLayout.inverse_wires (L : RoutedBankLayout) :
    wires L.inverse=wires L.program := by
  simp only [inverse,program,routedStageInverse,routedStage,rowStageInverse,rowStage,
    branchPairInverse,branchPair,branchRowInverse,branchRow,branchCore,
    wires_append,wires_reverse]
  ac_rfl

/-- All routed addresses lie in the caller's physical arena. -/
theorem RoutedBankLayout.support (L : RoutedBankLayout) (hv : L.Valid)
    (h1 : (L.q::L.parity::L.u::L.k::(L.f.wires++(L.glow::(L.gmid++[L.gsign])))).toFinset⊆arenaWires)
    (h2 : (L.q::L.parity::L.u::L.k::((L.vlow::(L.vmid++[L.vsign]))++L.gv.wires)).toFinset⊆arenaWires)
    (h3 : (L.active::L.vlow::(L.vmid++[L.vsign])).toFinset⊆arenaWires) :
    wires L.program⊆arenaWires ∧ wires L.inverse⊆arenaWires := by
  have h := routedStage_in_arena _ _ _ _ _ _ _ _ _ _ _ _ _ hv.fgLength hv.vLength h1 h2 h3
  exact ⟨h,by rw [L.inverse_wires]; exact h⟩

end ECDSAAdd.Arithmetic.Paper935
