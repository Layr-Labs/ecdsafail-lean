import ECDSAAdd.Arithmetic.MontProgramPhysical
import ECDSAAdd.Arithmetic.InverseQuotientSupport

namespace ECDSAAdd.Arithmetic.InverseQuotientCore
open Secp256k1
attribute [local irreducible] montMulControlledAdd montMulControlledSub swapRegisters

theorem physical (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257) :
    GatePhysical (program c M den) := by
  have nd₁ : (c :: M.wires).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have nd₃ : (c :: (denView M den).wires).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    change List.count q (c :: den ++ M.y ++ M.out ++ M.work) ≤ 1
    simp only [MontLayout.wires,List.count_cons,List.count_append] at h ⊢; omega
  have nd₂ : (c :: M.y.take 256 ++ M.out.take 256).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have hy := (List.take_sublist 256 M.y).count_le q
    have ho := (List.take_sublist 256 M.out).count_le q
    simp only [MontLayout.wires,List.count_cons,List.count_append] at h ⊢; omega
  have hw₃ : (denView M den).Widths := ⟨hd,hw.y,hw.out,hw.first,hw.z,hw.hZ⟩
  simp only [program,gatePhysical_append]
  exact ⟨⟨(montControlled_physical c M p hw nd₁).1,swapRegisters_physical _ _ _ nd₂⟩,
    (montControlled_physical c (denView M den) p hw₃ nd₃).2⟩

end ECDSAAdd.Arithmetic.InverseQuotientCore

namespace ECDSAAdd.Arithmetic.InverseQuotientRecorded
open RecordedQuantum
attribute [local irreducible] InverseQuotientCore.program

theorem physical (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den : List Wire)
    (hp : PhysicalProgram inv) (hn : (c :: den ++ M.wires).Nodup)
    (hw : M.Widths) (hd : den.length = 257) : PhysicalProgram (program inv c M den) := by
  simp only [program,physical_then]
  exact ⟨⟨hp,(physical_embed _).mpr (InverseQuotientCore.physical c M den hn hw hd)⟩,hp⟩

/-- The actual recorded quotient program has a coherent circuit semantics;
ordinary-gate physical validity is proved for the whole quotient core. Only
the supplied inverse endpoint retains its own physical/record obligations. -/
theorem realize (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den : List Wire)
    (hp : PhysicalProgram inv) (hf : RecordedWellFormedAt 0 inv)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257)
    (n : Nat) (hi : recordedWires inv ⊆ Finset.range n)
    (hb : (c :: den ++ M.wires).toFinset ⊆ Finset.range n) :
    ∃ l, ∃ circuit : Circuit n 0 l, circuit.program = program inv c M den := by
  apply RecordedQuantum.realize n 0 _ (physical inv c M den hp hn hw hd)
    (wellFormed inv c M den hf)
  rw [support]
  exact Finset.union_subset hi ((InverseQuotientCore.support c M den hw hd).trans hb)

end ECDSAAdd.Arithmetic.InverseQuotientRecorded
