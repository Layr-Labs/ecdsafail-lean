import ECDSAAdd.Submission.Entrant.Rehost.Base
/-!
# S2 rehost: the S1 program is the flat list of fourteen pieces

The placements are compositions of renames; the three generic lemmas below turn every placed piece into
the nested renames that `hostedWrapper` produces, so that the final comparison is syntactic (no program
is evaluated).
-/
namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1 MappedCompressed
open StairConcreteAssembly

theorem renameProgram_append (f : Wire → Wire) (a b : Program) :
    renameProgram f (a ++ b) = renameProgram f a ++ renameProgram f b := by
  simp only [renameProgram, List.map_append]

theorem fG_eq (P : Program) :
    renameProgram fG P = renameProgram (Wrapper5.U L0)
      (renameProgram (Equiv.swap L0.doubleSelect L0.control) (renameProgram (FlagTop.rho L0) P)) := by
  rw [renameProgram_comp, renameProgram_comp]
  rfl

theorem fK_eq (P : Program) : renameProgram fK P = renameProgram fG (renameProgram (wireFn2 L0) P) := by
  rw [renameProgram_comp]
  rfl

theorem fP_eq (P : Program) :
    renameProgram fP P = renameProgram fK (renameProgram Rolling1588Lifetime.phaseHost P) := by
  rw [renameProgram_comp]
  rfl

theorem hostedWrapper_flat {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    hostedWrapper (.some hc) cx cy = flat (.some hc) cx cy := by
  simp only [flat, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, fU, fP_eq, fK_eq, fG_eq,
    hostedWrapper, hostedFinite, hostedMiddle, hostedBorrowGeneric, hostedGenericBlock,
    hostedGeneric, hostedSecondStage, hostedExitRest, StairHostsSchedule.lastXN,
    ParityXExitInverse23Kernel.x1N, ParityXExitInverse23Kernel.x1N0, ParityXExit.programN,
    renameProgram_append, List.append_assoc]

theorem concreteProgram_flat {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    concreteProgram (.some hc) = flat (.some hc) cx cy := hostedWrapper_flat hc

end ECDSAAdd.Entrant.Rehost
