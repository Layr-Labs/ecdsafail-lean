import ECDSAAdd.Framework.Cost

namespace ECDSAAdd

/-- Kernel-opaque executable packaging, with its original code certified in
the result type. No proof proposition or evaluator result is assumed. -/
opaque certifiedProgram (P : Program) : {Q : Program // Q=P} := ⟨P,rfl⟩

def sealedProgram (P : Program) : Program := (certifiedProgram P).val

theorem sealedProgram_eq (P : Program) : sealedProgram P=P :=
  (certifiedProgram P).property

theorem sealedProgram_run (P : Program) (m : List Bool) (s : State) :
    run (sealedProgram P) m s=run P m s :=
  congrArg (fun Q : Program => run Q m s) (sealedProgram_eq P)

theorem sealedProgram_cost (P : Program) :
    toffoliCount (sealedProgram P)=toffoliCount P ∧
    measurementCount (sealedProgram P)=measurementCount P ∧
    wires (sealedProgram P)=wires P := by
  rw [sealedProgram_eq]
  exact ⟨rfl,rfl,rfl⟩

end ECDSAAdd
#print axioms ECDSAAdd.sealedProgram_eq
#print axioms ECDSAAdd.sealedProgram_run
#print axioms ECDSAAdd.sealedProgram_cost
