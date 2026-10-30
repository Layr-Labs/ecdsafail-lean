import ECDSAAdd.Submission.Entrant.FrontierCurrent
import ECDSAAdd.Submission.Entrant.DiagSquare

/-! Division-callback adapter for accepted 4c326f52, source
6293b28c3138b1381e8a06389bca7bd4dc4d8661. The current square,
exit multiplier, wrapper geometry and certificate contract are retained. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntryGeneric
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite

def genericE (L : ControlledPointLayout) (D : Fp → Program) (cx cy : Fp) : Program :=
  All12Generic.generic L D (OwnDiagAll12PlacedQ6.program L) (OwnExitFuseQ6.arithExit L) cx cy

def genE (L : ControlledPointLayout) (D : Fp → Program) (cx cy : Fp) : Program :=
  All12Generic.gen L D (OwnDiagAll12PlacedQ6.program L) (OwnExitFuseQ6.arithExit L) cx cy

theorem genE_counts_diff (L : ControlledPointLayout) (D : Fp → Program)
    (hD : ∀ k, toffoliCount (D k) + 251 = toffoliCount (OwnEndpointEntryQ6.fusedDivisionF L k) ∧
      measurementCount (D k) + 509 = measurementCount (OwnEndpointEntryQ6.fusedDivisionF L k))
    (cx cy : Fp) :
    toffoliCount (genE L D cx cy) + 251 = toffoliCount (OwnDiagEndpointActual.genE L cx cy) ∧
    measurementCount (genE L D cx cy) + 509 = measurementCount (OwnDiagEndpointActual.genE L cx cy) := by
  have h := hD (-cy)
  simp only [genE, OwnDiagEndpointActual.genE, All12Generic.gen, All12Generic.mid,
    All12Generic.generic, toffoliCount_append, measurementCount_append,
    renameProgram_counts]
  constructor <;> omega

theorem genericE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (hD : ∀ k, wires (D k) ⊆ (OB5Support.sites L).toFinset)
    (cx cy : Fp) : wires (genericE L D cx cy) ⊆ (OB5Support.sites L).toFinset :=
  All12Generic.generic_sites L hw _ _ _ hD
    (OwnDiagAll12PlacedQ6.support L hw hn) (OwnExitFuseQ6.arithExit_support L hw) cx cy

theorem genE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (hD : ∀ k, wires (D k) ⊆ (OB5Support.sites L).toFinset)
    (cx cy : Fp) : wires (genE L D cx cy) ⊆ (OB5Support.genericSites L).toFinset := by
  rw [genE, All12Generic.gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (genericE_sites L hw hn D hD cx cy)

theorem genE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (hD : ∀ k, GatePhysical (D k)) (cx cy : Fp) :
    GatePhysical (genE L D cx cy) :=
  All12Generic.gen_physical L hw hn _ _ _ hD
    (OwnDiagAll12PlacedQ6.physical L hw hn) (OwnExitFuseQ6.arithExit_physical L hw hn) cx cy

theorem genE_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (D : Fp → Program)
    (hD : ∀ k, gateSlots (D k) ≤ 20525006) (cx cy : Fp) :
    gateSlots (genE L D cx cy) ≤ 49200000 :=
  All12Generic.gen_slots_le L hw _ _ _ hD (OwnDiagAll12PlacedQ6.slots L hw)
    (OwnExitFuseQ6.arithExit_slots_le L) cx cy

theorem genericE_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program)
    (hD : ∀ k ∈ ([1800,766,765,767,770,1285] : List Nat),
      ∀ c, L.core.poolWire k ∉ wires (D c))
    (exitFree : base 1541 ∉ wires OwnExitFuseQ5.hostMulS)
    (k : Nat) (hk : k ∈ ([1800,766,765,767,770,1285] : List Nat)) (cx cy : Fp) :
    L.core.poolWire k ∉ wires (genericE L D cx cy) := by
  have bounds : 515 ≤ k ∧ k < 2613 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  exact All12Generic.generic_free L hw hn _ _ _ k bounds (hD k hk)
    (OwnDiagAll12PlacedQ6.square_free L hw hn k hk)
    (Q6FusionOmissions.exit_avoids L hw hn exitFree k hk) cx cy

theorem genE_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (exitFree : base 1541 ∉ wires OwnExitFuseQ5.hostMulS)
    (hD : ∀ (X Y k : Fp) (G : Bool) (origin : BasisState), X ≠ 0 →
      Triple (PointDialogValues L X Y G origin) (D k)
        (PointDialogValues L X ((Y + (if G then k else 0)) / X) G origin))
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (genE L D cx cy) :=
  All12Generic.genFFused_ok L hw hn _ _ _
    (OwnExitFuseQ6.arithExit_correct exitFree L hw hn) hD (OwnDiagEndpointActual.square_step L hw hn) hc

theorem genE_qubits1593 (D : Fp → Program)
    (hD : ∀ k, wires (D k) ⊆ (OB5Support.sites layout).toFinset)
    (hFree : ∀ k ∈ ([1800,766,765,767,770,1285] : List Nat),
      ∀ c, layout.core.poolWire k ∉ wires (D c)) (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (genE layout D cx cy)) ≤ 1593 := by
  rw [genE, All12Generic.gen_shape]
  apply GenericQ6Geometry.edges_wrapG_qubits _
    (genericE_sites layout layout_widths layout_nodup D hD cx cy)
  · intro k hk
    exact genericE_free layout layout_widths layout_nodup D hFree
      OwnQ6Actual.exit_selected_free k (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) cx cy
  · exact genericE_free layout layout_widths layout_nodup D hFree
      OwnQ6Actual.exit_selected_free 1285 (by simp) cx cy
end ECDSAAdd.Entrant.FrontierEntryGeneric

namespace ECDSAAdd.Entrant.FrontierEntryCertificate
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite

def program (D : Fp → Program) (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (FrontierEntryGeneric.genE layout D cx cy)

def entry (D : Fp → Program) : Challenge.Entry := fun C => normalizeProgram (program D C)
def bounds : Challenge.Bounds := ⟨2154395,1500105,1593,50000004⟩

theorem program_correct (D : Fp → Program)
    (hCorrect : ∀ (X Y k : Fp) (G : Bool) (origin : BasisState), X ≠ 0 →
      Triple (PointDialogValues layout X Y G origin) (D k)
        (PointDialogValues layout X ((Y + (if G then k else 0)) / X) G origin))
    (hSupport : ∀ k, wires (D k) ⊆ (OB5Support.sites layout).toFinset)
    (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program D C) (encodes b (if b then R + C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program, run, ←WeierstrassCurve.Affine.Point.zero_def, add_zero, ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have hG := FrontierEntryGeneric.genE_sites layout layout_widths layout_nodup D hSupport cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (FrontierEntryGeneric.genE_ok layout layout_widths layout_nodup D
          OwnQ6Actual.exit_selected_free hCorrect hc) hG)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ hG).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (D : Fp → Program)
    (hCounts : ∀ k, toffoliCount (D k) + 251 = toffoliCount (OwnEndpointEntryQ6.fusedDivisionF layout k) ∧
      measurementCount (D k) + 509 = measurementCount (OwnEndpointEntryQ6.fusedDivisionF layout k))
    (C : Point) : toffoliCount (program D C) ≤ 2154395 := by
  cases C with
  | zero => simp [program, toffoliCount]
  | @some cx cy hc =>
    have h := (Edges.wrapper_counts layout layout_widths (FrontierEntryGeneric.genE layout D cx cy) hc).1
    have g := (SelGeneric5.program_counts layout layout_widths cx cy).1
    have gf := (genF_counts layout layout_widths cx cy).1
    have gd := (genFFused_counts_diff layout layout_widths cx cy).1
    have ge := (OwnExitProducer.genE_counts_diff layout layout_widths cx cy).1
    have gq := (OwnQ6Producer.genE_counts_eq layout cx cy).1
    have ga := (OwnDiagEndpointActual.genE_counts_diff layout layout_widths cx cy).1
    have fresh := (FrontierEntryGeneric.genE_counts_diff layout D hCounts cx cy).1
    change toffoliCount (Edges.wrapper layout (.some hc) cy
      (FrontierEntryGeneric.genE layout D cx cy)) ≤ 2154395
    omega

theorem program_measurements (D : Fp → Program)
    (hCounts : ∀ k, toffoliCount (D k) + 251 = toffoliCount (OwnEndpointEntryQ6.fusedDivisionF layout k) ∧
      measurementCount (D k) + 509 = measurementCount (OwnEndpointEntryQ6.fusedDivisionF layout k))
    (C : Point) : measurementCount (program D C) ≤ 1500105 := by
  cases C with
  | zero => simp [program, measurementCount]
  | @some cx cy hc =>
    have h := (Edges.wrapper_counts layout layout_widths (FrontierEntryGeneric.genE layout D cx cy) hc).2
    have g := (SelGeneric5.program_counts layout layout_widths cx cy).2
    have gf := (genF_counts layout layout_widths cx cy).2
    have gd := (genFFused_counts_diff layout layout_widths cx cy).2
    have ge := (OwnExitProducer.genE_counts_diff layout layout_widths cx cy).2
    have gq := (OwnQ6Producer.genE_counts_eq layout cx cy).2
    have ga := (OwnDiagEndpointActual.genE_counts_diff layout layout_widths cx cy).2
    have fresh := (FrontierEntryGeneric.genE_counts_diff layout D hCounts cx cy).2
    change measurementCount (Edges.wrapper layout (.some hc) cy
      (FrontierEntryGeneric.genE layout D cx cy)) ≤ 1500105
    omega

theorem program_qubits (D : Fp → Program)
    (hSupport : ∀ k, wires (D k) ⊆ (OB5Support.sites layout).toFinset)
    (hFree : ∀ k ∈ ([1800,766,765,767,770,1285] : List Nat),
      ∀ c, layout.core.poolWire k ∉ wires (D c))
    (C : Point) : qubits (program D C) ≤ 1593 := by
  cases C with
  | zero => change qubits [] ≤ 1593; rw [qubits_empty]; decide
  | @some cx cy hc => exact FrontierEntryGeneric.genE_qubits1593 D hSupport hFree (.some hc) cx cy

theorem program_physical (D : Fp → Program) (hPhysical : ∀ k, GatePhysical (D k))
    (C : Point) : GatePhysical (program D C) := by
  cases C with
  | zero => simp [program, GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FrontierEntryGeneric.genE_physical layout layout_widths layout_nodup D hPhysical cx cy)

theorem program_gateSlots (D : Fp → Program)
    (hSlots : ∀ k, gateSlots (D k) ≤ 20525006)
    (C : Point) : gateSlots (program D C) ≤ 50000004 := by
  cases C with
  | zero => simp [program, gateSlots]
  | @some cx cy hc =>
    have h := Edges.wrapper_slots layout layout_widths (.some hc) cy
      (FrontierEntryGeneric.genE layout D cx cy)
    have g := FrontierEntryGeneric.genE_gateSlots_le layout layout_widths D hSlots cx cy
    change gateSlots (Edges.wrapper layout (.some hc) cy
      (FrontierEntryGeneric.genE layout D cx cy)) ≤ _
    omega

theorem certificate (D : Fp → Program)
    (hCorrect : ∀ (X Y k : Fp) (G : Bool) (origin : BasisState), X ≠ 0 →
      Triple (PointDialogValues layout X Y G origin) (D k)
        (PointDialogValues layout X ((Y + (if G then k else 0)) / X) G origin))
    (hSupport : ∀ k, wires (D k) ⊆ (OB5Support.sites layout).toFinset)
    (hCounts : ∀ k, toffoliCount (D k) + 251 = toffoliCount (OwnEndpointEntryQ6.fusedDivisionF layout k) ∧
      measurementCount (D k) + 509 = measurementCount (OwnEndpointEntryQ6.fusedDivisionF layout k))
    (hPhysical : ∀ k, GatePhysical (D k))
    (hFree : ∀ k ∈ ([1800,766,765,767,770,1285] : List Nat),
      ∀ c, layout.core.poolWire k ∉ wires (D c))
    (hSlots : ∀ k, gateSlots (D k) ≤ 20525006) :
    Challenge.Certificate (entry D) bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct D hCorrect hSupport C b R)
  physical C := normalize_physical _ (program_physical D hPhysical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli D hCounts C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program D C)) ≤ 1500105
    rw [normalize_measurements]; exact program_measurements D hCounts C
  qubits_le C := by
    change qubits (normalizeProgram (program D C)) ≤ 1593
    rw [normalize_qubits]; exact program_qubits D hSupport hFree C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program D C)) ≤ 50000004
    rw [normalize_slots]; exact program_gateSlots D hSlots C
end ECDSAAdd.Entrant.FrontierEntryCertificate
