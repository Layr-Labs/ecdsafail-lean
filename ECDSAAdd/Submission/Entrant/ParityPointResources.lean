import ECDSAAdd.Submission.Entrant.OneFlag

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Q1591Resources
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FiniteHostStack FiniteHostFusion
  FiniteHostFive GenericQ5Geometry ExitFusionResearch
attribute [local irreducible] wires run toffoliCount measurementCount fastConstAdd fastConstNeg

def genericOmissions : List Nat := [1800,766,765,767,770,1285,1286,769]

theorem qubits_ten (P : Program)
    (sub : ioWires ∪ wires P ⊆ (WrapperOB5.sites layout).toFinset)
    (free : ∀ k ∈ ([1400,1800,766,765,767,1540,770,1285,1286] : List Nat),
      layout.core.poolWire k ∉ wires P)
    (extra : layout.core.poolWire 769 ∉ wires P) : qubits P ≤ 1591 := by
  let q := layout.core.poolWire 769
  let witness : Program := [.X q] ++ P
  have qm : q ∈ (WrapperOB5.sites layout).toFinset := by
    apply List.mem_toFinset.mpr
    simp only [q,WrapperOB5.sites,List.mem_append,List.mem_singleton,
      wireBlock,List.mem_map,List.mem_range'_1]
    exact Or.inl (Or.inl (Or.inr ⟨769,by omega,rfl⟩))
  have ww : wires witness = insert q (wires P) := by
    unfold witness
    rw [wires_append]
    simp only [wires,Instr.wires,Finset.union_empty,Finset.singleton_union]
  have ws : ioWires ∪ wires witness ⊆ (WrapperOB5.sites layout).toFinset := by
    rw [ww]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact sub (Finset.mem_union.mpr (Or.inl hx))
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact qm
      · exact sub (Finset.mem_union.mpr (Or.inr hx))
  have wf : ∀ k ∈ ([1400,1800,766,765,767,1540,770,1285,1286] : List Nat),
      layout.core.poolWire k ∉ wires witness := by
    intro k hk
    rw [ww]
    intro h
    rcases Finset.mem_insert.mp h with he | hp
    · have kb : k < 2613 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        omega
      have kn : k ≠ 769 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        omega
      exact kn (pool_inj layout layout_widths layout_nodup k 769 kb (by omega) he)
    · exact free k hk hp
  have bound := Q7Inventory.qubits_nine witness ws
    (fun k hk => wf k (List.mem_append_left [1286] hk)) (wf 1286 (by simp))
  have fresh : q ∉ ioWires ∪ wires P := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact FiniteHostStack.io_avoids_pool 769 (by omega) h
    · exact extra h
  have sets : ioWires ∪ wires witness = insert q (ioWires ∪ wires P) := by
    rw [ww,Finset.union_insert]
  change (ioWires ∪ wires witness).card ≤ 1592 at bound
  rw [sets,Finset.card_insert_of_notMem fresh] at bound
  change (ioWires ∪ wires P).card ≤ 1591
  omega

theorem edges_wrapG_qubits (G : Program)
    (hG : wires G ⊆ (OB5Support.sites layout).toFinset)
    (hFree : ∀ k ∈ genericOmissions,layout.core.poolWire k ∉ wires G)
    (C : Point) (cy : Fp) :
    qubits (Edges.wrapper layout C cy (wrapG layout G)) ≤ 1591 := by
  have supported := Edges.wrapper_support layout layout_widths layout_nodup C cy _
    (wrapG_sites layout layout_widths layout_nodup G hG)
  have sub := Finset.union_subset FiniteHostStack.io_support_original supported
  have edge (k : Nat) (hk : 515≤k ∧ k<2613)
      (old : layout.core.poolWire k ∉ wires (WrapperOB5.program layout C cy (wrapG layout G))) :
      layout.core.poolWire k ∉ wires (Edges.wrapper layout C cy (wrapG layout G)) := by
    intro h
    rcases Finset.mem_union.mp (Edges.wrapper_wires layout C cy _ h) with h | h
    · exact old h
    · exact Edges.small_away layout layout_widths layout_nodup k hk
        (Edges.extra_small layout layout_widths layout_nodup C h)
  have omitted (k : Nat) (hk : k ∈ genericOmissions) :
      layout.core.poolWire k ∉ wires (Edges.wrapper layout C cy (wrapG layout G)) := by
    have bounds : 515≤k ∧ k<2613 ∧ k≠684 ∧ k≠717 ∧ k≠1400 ∧ k≠1540 := by
      simp only [genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
      omega
    apply edge k ⟨bounds.1,bounds.2.1⟩
    exact finWrapper_avoid layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩
      bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.2 _
      (wrapG_avoid_of_generic layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩
        bounds.2.2.2.2.1 G (hFree k hk)) C cy
  apply qubits_ten _ sub
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply edge 1400 (by omega)
      exact finWrapper_avoid layout layout_widths layout_nodup 1400 (by omega)
        (by omega) (by omega) (by omega) (wrapG layout G)
        (spare_not_wrapG layout layout_widths layout_nodup G hG) C cy
    · exact omitted 1800 (by simp [genericOmissions])
    · exact omitted 766 (by simp [genericOmissions])
    · exact omitted 765 (by simp [genericOmissions])
    · exact omitted 767 (by simp [genericOmissions])
    · apply edge 1540 (by omega)
      exact finWrapper_avoid1540 layout layout_widths layout_nodup _ (wrapG_noDouble G hG) C cy
    · exact omitted 770 (by simp [genericOmissions])
    · exact omitted 1285 (by simp [genericOmissions])
    · exact omitted 1286 (by simp [genericOmissions])
  · exact omitted 769 (by simp [genericOmissions])

theorem generic_counts_eq (L : ControlledPointLayout) (D : Fp → Program) (S P : Program)
    (dc : ∀ k,toffoliCount (D k)=toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF L k) ∧
      measurementCount (D k)=measurementCount (OwnOneFlagEntryQ7.fusedDivisionF L k))
    (sc : toffoliCount S=toffoliCount (OwnDiagAll12PlacedQ7.program L) ∧
      measurementCount S=measurementCount (OwnDiagAll12PlacedQ7.program L))
    (pc : toffoliCount P=toffoliCount (OwnOneFlagExitQ7.arithExit L) ∧
      measurementCount P=measurementCount (OwnOneFlagExitQ7.arithExit L)) (cx cy : Fp) :
    toffoliCount (All12Generic.generic L D S P cx cy)=toffoliCount (OwnOneFlagActual.generic L cx cy) ∧
    measurementCount (All12Generic.generic L D S P cx cy)=measurementCount (OwnOneFlagActual.generic L cx cy) := by
  have d := dc (-cy)
  simp only [OwnOneFlagActual.generic,OneFlagProducer.generic,All12Generic.generic,
    toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem gen_counts_eq (L : ControlledPointLayout) (D : Fp → Program) (S P : Program)
    (dc : ∀ k,toffoliCount (D k)=toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF L k) ∧
      measurementCount (D k)=measurementCount (OwnOneFlagEntryQ7.fusedDivisionF L k))
    (sc : toffoliCount S=toffoliCount (OwnDiagAll12PlacedQ7.program L) ∧
      measurementCount S=measurementCount (OwnDiagAll12PlacedQ7.program L))
    (pc : toffoliCount P=toffoliCount (OwnOneFlagExitQ7.arithExit L) ∧
      measurementCount P=measurementCount (OwnOneFlagExitQ7.arithExit L)) (cx cy : Fp) :
    toffoliCount (All12Generic.gen L D S P cx cy)=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
    measurementCount (All12Generic.gen L D S P cx cy)=measurementCount (OwnOneFlagActual.gen L cx cy) := by
  have h := generic_counts_eq L D S P dc sc pc cx cy
  simp only [OwnOneFlagActual.generic,OneFlagProducer.generic] at h
  simp only [OwnOneFlagActual.gen,OneFlagProducer.gen,All12Generic.gen,All12Generic.mid,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (S P : Program)
    (ds : ∀ k,wires (D k) ⊆ (OB5Support.sites L).toFinset)
    (ss : wires S ⊆ (OB5Support.sites L).toFinset)
    (ps : wires P ⊆ (OB5Support.sites L).toFinset) (cx cy : Fp) :
    wires (All12Generic.gen L D S P cx cy) ⊆ (OB5Support.genericSites L).toFinset := by
  rw [All12Generic.gen_shape]
  exact wrapG_sites L hw hn _ (All12Generic.generic_sites L hw D S P ds ss ps cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (S P : Program)
    (dp : ∀ k,GatePhysical (D k)) (sp : GatePhysical S) (pp : GatePhysical P) (cx cy : Fp) :
    GatePhysical (All12Generic.gen L D S P cx cy) :=
  All12Generic.gen_physical L hw hn D S P dp sp pp cx cy

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp → Program) (S P : Program)
    (df : ∀ c k,k ∈ genericOmissions → L.core.poolWire k ∉ wires (D c))
    (sf : ∀ k,k ∈ genericOmissions → L.core.poolWire k ∉ wires S)
    (pf : ∀ k,k ∈ genericOmissions → L.core.poolWire k ∉ wires P)
    (k : Nat) (hk : k ∈ genericOmissions) (cx cy : Fp) :
    L.core.poolWire k ∉ wires (All12Generic.generic L D S P cx cy) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  exact All12Generic.generic_free L hw hn D S P k bounds
    (fun c => df c k hk) (sf k hk) (pf k hk) cx cy

theorem gen_qubits (D : Fp → Program) (S P : Program)
    (ds : ∀ k,wires (D k) ⊆ (OB5Support.sites layout).toFinset)
    (ss : wires S ⊆ (OB5Support.sites layout).toFinset)
    (ps : wires P ⊆ (OB5Support.sites layout).toFinset)
    (df : ∀ c k,k ∈ genericOmissions → layout.core.poolWire k ∉ wires (D c))
    (sf : ∀ k,k ∈ genericOmissions → layout.core.poolWire k ∉ wires S)
    (pf : ∀ k,k ∈ genericOmissions → layout.core.poolWire k ∉ wires P)
    (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (All12Generic.gen layout D S P cx cy)) ≤ 1591 := by
  rw [All12Generic.gen_shape]
  exact edges_wrapG_qubits _
    (All12Generic.generic_sites layout layout_widths D S P ds ss ps cx cy)
    (fun k hk => generic_free layout layout_widths layout_nodup D S P df sf pf k hk cx cy) C cy

theorem gen_slots (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp → Program) (S P : Program)
    (ds : ∀ k,gateSlots (D k) ≤ 20527454)
    (ss : gateSlots S ≤ 8000000) (ps : gateSlots P ≤ 20502454) (cx cy : Fp) :
    gateSlots (All12Generic.gen L D S P cx cy) ≤ 49204896 := by
  have add (k : Fp) : gateSlots (fastConstAdd L L.point.x k) ≤ 15368 := by
    simpa only [fastConstAdd] using FastConst.fastAdd_gateSlots_le
      (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have neg : gateSlots (fastConstNeg L cx) ≤ 17928 := by
    simpa only [fastConstNeg] using FastConst.fastNeg_gateSlots_le
      (g:=L.core.generic) 256 p cx.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a := add (-cx)
  have b := add (3*cx-(2^163-1 : Nat))
  have d := ds (-cy)
  have e := exitY_slots L hw cy
  have z := zrep_gateSlots_le L hw
  have c := clrF_gateSlots_le L hw
  simp only [All12Generic.gen,All12Generic.mid,All12Generic.generic,gateSlots_append,rename_gateSlots]
  omega

theorem gen_slots_eq (L : ControlledPointLayout) (D : Fp → Program) (S P : Program)
    (ds : ∀ k,gateSlots (D k)=gateSlots (OwnOneFlagEntryQ7.fusedDivisionF L k)+2448)
    (ss : gateSlots S=gateSlots (OwnDiagAll12PlacedQ7.program L))
    (ps : gateSlots P=gateSlots (OwnOneFlagExitQ7.arithExit L)+2448) (cx cy : Fp) :
    gateSlots (All12Generic.gen L D S P cx cy)=
      gateSlots (OwnOneFlagActual.gen L cx cy)+4896 := by
  have d := ds (-cy)
  simp only [OwnOneFlagActual.gen,OneFlagProducer.gen,All12Generic.gen,
    All12Generic.mid,All12Generic.generic,gateSlots_append,rename_gateSlots]
  omega

theorem wrapper_slots (L : ControlledPointLayout) (hw : L.Widths)
    (G : Program) (gs : gateSlots G ≤ 49204896) (C : Point) (cy : Fp) :
    gateSlots (Edges.wrapper L C cy G) ≤ 50004900 := by
  have h := Edges.wrapper_slots L hw C cy G
  omega

end ECDSAAdd.Entrant.Q1591Resources
