import ECDSAAdd.Arithmetic.MappedCompressedPointTransfer
import ECDSAAdd.Arithmetic.MappedCompressedPointImages
import ECDSAAdd.Arithmetic.MappedCompressedStageCounts
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 ControlledPointLayout DirectSkywalk
attribute [local irreducible] run controlled toffoliCount measurementCount
  mixedTranscriptUnitTrace SkywalkTrace.next Nat.iterate

/-- Concrete physical binding of the finite arithmetic support. -/
theorem pointPlacement (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    PointArithmeticPlacement L (pointWireFn L) := by
  have ports := pointWireFn_coordinates L hw
  have scalars := pointWireFn_scalar_dialog L hw
  exact ⟨pointWireFn_injective_slots L hw hn,ports.1,ports.2,pointWireFn_control L,
    pointWireFn_sharedWork L hw,scalars.1,scalars.2.1,scalars.2.2⟩

private theorem logical_shared_nodup : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

private theorem logical_scalar_outside (i : Nat) (hi : 2314 ≤ i) :
    base i ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hj
  have same := base_injective eq
  omega

private theorem logical_selectors_outside :
    ∀ q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base := by
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact logical_scalar_outside _ (by omega)

/-- Fixed logical template layout; only pure labels are checked here.
The actual recorded tape, not its numerical contents, supplies the layout. -/
private theorem logical_mixed_layout :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base) := by
  have scalar : [base 2400,base 2409,base 2410].Nodup := by simp [base]
  have disjoint : [base 2400,base 2409,base 2410].Disjoint (skywalkSharedWires base) :=
    List.disjoint_left.mpr (fun q hq => logical_selectors_outside q hq)
  have hall := List.nodup_append'.mpr ⟨scalar,logical_shared_nodup,disjoint⟩
  have unused : skywalkSharedUnused base⊆skywalkSharedWires base := by
    intro q hq
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals exact arith_mem base 0 2314 _ (by omega) (by omega)
  apply mixedTranscriptTape_layout
  intro r hr
  have pair := (List.nodup_cons.mp (skywalkShared_tape_layout base logical_shared_nodup
    (base 2400) (logical_selectors_outside _ (by simp)) r hr)).2
  have sub : (r.2::r.1::(skywalkSharedField base).wires)⊆skywalkSharedWires base := by
    intro q hq
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).2
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).1
    · exact retained_field_subset_shared base hq
  constructor
  · exact logical_shared_nodup
  · apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hall q
    have hp := List.nodup_iff_count.mp pair q
    have hle : (r.2::r.1::(skywalkSharedField base).wires).count q≤
        (skywalkSharedWires base).count q := by
      by_cases hm : q∈r.2::r.1::(skywalkSharedField base).wires
      · have positive := List.count_pos_iff.mpr (sub hm); omega
      · rw [List.count_eq_zero.mpr hm]; omega
    simp only [List.count_append,List.count_cons,List.count_nil] at hh hp hle ⊢
    omega
  · exact fun h => logical_selectors_outside _ (by simp) (fusedSharedSites_subset base h)
  · exact fun h => logical_selectors_outside _ (by simp) (unused h)
  · exact fun h => logical_selectors_outside _ (by simp) (unused h)

/-- Computable concrete point arithmetic: finite placement of the complete
zero-repair and compressed512-round arithmetic caller. -/
def pointCompressedArithmetic (L : ControlledPointLayout) (multiply : Bool) : Program :=
  renameProgram (pointWireFn L) (controlled (!multiply))

/-- Original guarded point-arithmetic contract, unchanged on all canonical
X,Y values, incoming phases, inactive zero divisors and full record streams. -/
theorem pointCompressedArithmetic_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (pointCompressedArithmetic L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (pointCompressedArithmetic L multiply) m s).basis=V ∧
    ∀ q,q∉L.point.y → (run (pointCompressedArithmetic L multiply) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  have result := pointTransfer_spec L (pointWireFn L) (pointPlacement L hw hn) (!multiply)
    logical_shared_nodup base_above logical_selectors_outside logical_mixed_layout
    X (Y:Fp) B hX hX0 s m hb hx (hy.trans yValue.symm) hc
  cases B <;> cases multiply <;>
    simpa only [pointCompressedArithmetic,directSkywalkResult,skywalkArithmeticResult,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,yValue] using result

theorem pointCompressedArithmetic_support (L : ControlledPointLayout) (hw : L.Widths)
    (multiply : Bool) : wires (pointCompressedArithmetic L multiply)⊆
      (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).toFinset := by
  intro q hq
  rw [pointCompressedArithmetic,renameProgram_support] at hq
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  exact pointWireFn_slots_image L hw (Finset.mem_image.mpr
    ⟨old,controlled_support (!multiply) used,rfl⟩)

/-- Relabeling preserves the exact emitted prices of both arithmetic stages. -/
theorem pointCompressedArithmetic_counts (L : ControlledPointLayout) :
    toffoliCount (pointCompressedArithmetic L false)=1053750 ∧
    measurementCount (pointCompressedArithmetic L false)=724536 ∧
    toffoliCount (pointCompressedArithmetic L true)=1054260 ∧
    measurementCount (pointCompressedArithmetic L true)=724536 := by
  have div := controlled_counts true
  have mul := controlled_counts false
  have rd := renameProgram_counts (pointWireFn L) (controlled true)
  have rm := renameProgram_counts (pointWireFn L) (controlled false)
  simp only [pointCompressedArithmetic,Bool.not_false,Bool.not_true]
  rw [rd.1,rd.2,rm.1,rm.2,div.1,div.2,mul.1,mul.2]
  norm_num

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointPlacement
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointCompressedArithmetic_correct
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointCompressedArithmetic_support
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointCompressedArithmetic_counts
