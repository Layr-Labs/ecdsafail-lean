import ECDSAAdd.Arithmetic.PointFixedPhysical

namespace ECDSAAdd.Arithmetic.ConditionalPointDialog
open RecordedQuantum Secp256k1 ControlledPointLayout

theorem generic_physical (backend : ConditionalPointArithmeticBackend)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp)
    (hp : ∀ multiply, PhysicalProgram (backend.program L multiply)) :
    PhysicalProgram (generic backend L cx cy) := by
  simp only [generic,physical_then,physical_embed]
  exact ⟨⟨⟨⟨⟨⟨pointDialogConstantAdd_physical L hw hn _ (Or.inl rfl) _,
    pointDialogConstantAdd_physical L hw hn _ (Or.inr rfl) _⟩,hp false⟩,
    CompressedPointSquare.computableProgram_physical L hw hn⟩,
    pointDialogConstantAdd_physical L hw hn _ (Or.inl rfl) _⟩,hp true⟩,
    pointRecoveryStage_physical L hw hn cx cy⟩

theorem finite_physical (backend : ConditionalPointArithmeticBackend)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp)
    (hp : ∀ multiply, PhysicalProgram (backend.program L multiply)) :
    PhysicalProgram (finite backend L C cx cy) := by
  have flags := pointDialogFlags_physical L hn cy C
  have sep := dialogFlag_separation (L:=L) hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at sep
  simp only [finite,physical_then,physical_embed]
  repeat constructor
  all_goals first
    | exact flags.1
    | exact flags.2.1
    | exact flags.2.2
    | exact generic_physical backend L hw hn cx cy hp
    | exact pointDialogCorners_physical L hn C
    | apply dialogEqual_physical L hw hn
  all_goals simp_all [inPlaceFlags,ne_comm]

theorem program_physical (backend : ConditionalPointArithmeticBackend)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    (hp : ∀ multiply, PhysicalProgram (backend.program L multiply)) :
    PhysicalProgram (program backend L C) := by
  cases C with
  | zero => simp [program,PhysicalProgram]
  | some hc => exact finite_physical backend L hw hn _ _ _ hp

/-- The whole actual point-add program has coherent semantics; only its two
replaceable arithmetic calls retain physical-validity obligations. -/
theorem realize (backend : ConditionalPointArithmeticBackend)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    (hp : ∀ multiply, PhysicalProgram (backend.program L multiply))
    (n : Nat) (hb : L.dialogUsedWires.toFinset ⊆ Finset.range n) :
    ∃ l, ∃ c : Circuit n 0 l, c.program = program backend L C := by
  apply RecordedQuantum.realize n 0 _ (program_physical backend L hw hn C hp)
    (program_wellFormed backend L hw hn C)
  exact (program_wires backend L hw hn C).trans hb

end ECDSAAdd.Arithmetic.ConditionalPointDialog
