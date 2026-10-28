import ECDSAAdd.Arithmetic.InverseProductRecorded
import ECDSAAdd.Arithmetic.InverseQuotientPhysical
namespace ECDSAAdd.Arithmetic.InverseProductRecorded
open RecordedQuantum
attribute [local irreducible] InverseQuotientCore.program

theorem physical (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den : List Wire)
    (hp : PhysicalProgram inv) (hn : (c :: den ++ M.wires).Nodup)
    (hw : M.Widths) (hd : den.length = 257) : PhysicalProgram (program inv c M den) := by
  have nd : (c :: M.x ++ (InverseQuotientCore.denView M den).wires).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    change List.count q (c :: M.x ++ (den ++ M.y ++ M.out ++ M.work)) ≤ 1
    simp only [MontLayout.wires,List.count_cons,List.count_append] at h ⊢; omega
  have hw' : (InverseQuotientCore.denView M den).Widths := ⟨hd,hw.y,hw.out,hw.first,hw.z,hw.hZ⟩
  simp only [program,physical_then]
  exact ⟨⟨hp,(physical_embed _).mpr
    (InverseQuotientCore.physical c (InverseQuotientCore.denView M den) M.x nd hw' hw.x)⟩,hp⟩

theorem realize (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den : List Wire)
    (hp : PhysicalProgram inv) (hf : RecordedWellFormedAt 0 inv)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257)
    (n : Nat) (hi : recordedWires inv ⊆ Finset.range n)
    (hb : (c :: den ++ M.wires).toFinset ⊆ Finset.range n) :
    ∃ l, ∃ circuit : Circuit n 0 l, circuit.program = program inv c M den := by
  apply RecordedQuantum.realize n 0 _ (physical inv c M den hp hn hw hd)
    (wellFormed inv c M den hf)
  rw [support]
  apply Finset.union_subset hi
  have hw' : (InverseQuotientCore.denView M den).Widths := ⟨hd,hw.y,hw.out,hw.first,hw.z,hw.hZ⟩
  apply (InverseQuotientCore.support _ _ _ hw' hw.x).trans
  intro q hq
  apply hb
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,MontLayout.wires,
    InverseQuotientCore.denView] at hq ⊢
  tauto

end ECDSAAdd.Arithmetic.InverseProductRecorded
