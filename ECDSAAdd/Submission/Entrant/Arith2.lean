import ECDSAAdd.Submission.Entrant.LaneAvoid

/-! The Skywalk arithmetic with two logical labels exchanged.

Label `769` is never touched by the arithmetic (`controlled_avoid`); its pool
site is, however, needed by the square stage.  Exchanging labels `769` and
`1797` before placement makes the arithmetic use that already-needed site for
label `1797`, and leaves the site previously behind `1797` idle.  The placement
facts used by the correctness transfer are unchanged by the exchange. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation Secp256k1 ControlledPointLayout DirectSkywalk
open MappedCompressed.LaneA (laneControlled laneControlled_support laneControlled_counts
  laneControlled_physical laneTransfer_spec)
attribute [local irreducible] run controlled laneControlled toffoliCount measurementCount
  mixedTranscriptUnitTrace SkywalkTrace.next Nat.iterate

/-- Exchange of the wires `base 769` and `base 1797`. -/
def swap2 (q : Wire) : Wire :=
  if q = base 769 then base 1797 else if q = base 1797 then base 769 else q

def wireFn2 (L : ControlledPointLayout) (q : Wire) : Wire := pointWireFn L (swap2 q)

def arith2 (L : ControlledPointLayout) (multiply : Bool) : Program :=
  renameProgram (wireFn2 L) (laneControlled (!multiply))

theorem swap2_involutive (q : Wire) : swap2 (swap2 q) = q := by
  have hb : base 769 ≠ base 1797 := by decide
  unfold swap2
  by_cases h1 : q = base 769
  · subst h1; simp [hb, hb.symm]
  · by_cases h2 : q = base 1797
    · subst h2; simp [hb, hb.symm]
    · simp [h1, h2]

theorem m769 : base 769 ∈ slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem m1797 : base 1797 ∈ slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem swap2_slots (q : Wire) (h : q ∈ slots.toFinset) : swap2 q ∈ slots.toFinset := by
  have a := m769
  have b := m1797
  unfold swap2; split_ifs <;> assumption

theorem swap2_fix (q : Wire) (h1 : q ≠ base 769) (h2 : q ≠ base 1797) : swap2 q = q := by
  simp [swap2, h1, h2]

private theorem logical_shared_nodup2 : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

private theorem logical_scalar_outside2 (i : Nat) (hi : 2314 ≤ i) :
    base i ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hj
  have same := base_injective eq
  omega

private theorem logical_selectors_outside2 :
    ∀ q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base := by
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact logical_scalar_outside2 _ (by omega)

private theorem logical_mixed_layout2 :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base) := by
  have scalar : [base 2400,base 2409,base 2410].Nodup := by simp [base]
  have disjoint : [base 2400,base 2409,base 2410].Disjoint (skywalkSharedWires base) :=
    List.disjoint_left.mpr (fun q hq => logical_selectors_outside2 q hq)
  have hall := List.nodup_append'.mpr ⟨scalar,logical_shared_nodup2,disjoint⟩
  have unused : skywalkSharedUnused base⊆skywalkSharedWires base := by
    intro q hq
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals exact arith_mem base 0 2314 _ (by omega) (by omega)
  apply mixedTranscriptTape_layout
  intro r hr
  have pair := (List.nodup_cons.mp (skywalkShared_tape_layout base logical_shared_nodup2
    (base 2400) (logical_selectors_outside2 _ (by simp)) r hr)).2
  have sub : (r.2::r.1::(skywalkSharedField base).wires)⊆skywalkSharedWires base := by
    intro q hq
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).2
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).1
    · exact retained_field_subset_shared base hq
  constructor
  · exact logical_shared_nodup2
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
  · exact fun h => logical_selectors_outside2 _ (by simp) (fusedSharedSites_subset base h)
  · exact fun h => logical_selectors_outside2 _ (by simp) (unused h)
  · exact fun h => logical_selectors_outside2 _ (by simp) (unused h)

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem placement2 : PointArithmeticPlacement L (wireFn2 L) := by
  have base' := pointPlacement L hw hn
  rcases base' with ⟨inj, dmap, nmap, cmap, swork, sg, ss, sz⟩
  have blockfix (a n : Nat) (h : 1797 < a ∨ a + n ≤ 769 ∨ (769 < a ∧ a + n ≤ 1797)) :
      (wireBlock base a n).map (wireFn2 L) = (wireBlock base a n).map (pointWireFn L) := by
    apply List.map_congr_left
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [wireFn2]
    rw [swap2_fix (base i) (fun h => by have h' : i + 16 = 769 + 16 := h; omega)
      (fun h => by have h' : i + 16 = 1797 + 16 := h; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb e
    have := inj _ (swap2_slots a ha) _ (swap2_slots b hb) e
    rw [← swap2_involutive a, this, swap2_involutive]
  · rw [blockfix 770 256 (by omega)]; exact dmap
  · rw [blockfix 2056 256 (by omega)]; exact nmap
  · simp only [wireFn2]; rw [swap2_fix (base 2400) (by decide) (by decide)]; exact cmap
  · intro q hq hs hx hy
    simp only [wireFn2]
    by_cases h1 : q = base 769
    · subst h1
      rw [show swap2 (base 769) = base 1797 by simp [swap2]]
      apply swork
      · exact List.mem_map.mpr ⟨1797, by simp [List.mem_range'_1], rfl⟩
      · exact m1797
      · intro h; obtain ⟨i, hi, he⟩ := List.mem_map.mp h; simp only [List.mem_range'_1] at hi
        have he' : i + 16 = _ := he; simp only [base] at he'; omega
      · intro h; obtain ⟨i, hi, he⟩ := List.mem_map.mp h; simp only [List.mem_range'_1] at hi
        have he' : i + 16 = _ := he; simp only [base] at he'; omega
    · by_cases h2 : q = base 1797
      · subst h2
        rw [show swap2 (base 1797) = base 769 by simp only [swap2, base]; simp]
        apply swork
        · exact List.mem_map.mpr ⟨769, by simp [List.mem_range'_1], rfl⟩
        · exact m769
        · intro h; obtain ⟨i, hi, he⟩ := List.mem_map.mp h; simp only [List.mem_range'_1] at hi
          have he' : i + 16 = _ := he; simp only [base] at he'; omega
        · intro h; obtain ⟨i, hi, he⟩ := List.mem_map.mp h; simp only [List.mem_range'_1] at hi
          have he' : i + 16 = _ := he; simp only [base] at he'; omega
      · rw [swap2_fix _ h1 h2]; exact swork q hq hs hx hy
  · simp only [wireFn2]; rw [swap2_fix (base 2409) (by decide) (by decide)]; exact sg
  · simp only [wireFn2]; rw [swap2_fix (base 2410) (by decide) (by decide)]; exact ss
  · simp only [wireFn2]; rw [swap2_fix (base 2411) (by decide) (by decide)]; exact sz

theorem arith2_correct (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (arith2 L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (arith2 L multiply) m s).basis=V ∧
    ∀ q,q∉L.point.y → (run (arith2 L multiply) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  have result := laneTransfer_spec L (wireFn2 L) (placement2 L hw hn) (!multiply)
    logical_shared_nodup2 base_above logical_selectors_outside2 logical_mixed_layout2
    X (Y:Fp) B hX hX0 s m hb hx (hy.trans yValue.symm) hc
  cases B <;> cases multiply <;>
    simpa only [arith2,directSkywalkResult,skywalkArithmeticResult,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,yValue] using result

end

theorem arith2_counts (L : ControlledPointLayout) :
    toffoliCount (arith2 L false)=1051199 ∧ measurementCount (arith2 L false)=721985 ∧
    toffoliCount (arith2 L true)=1051709 ∧ measurementCount (arith2 L true)=721985 := by
  have h1 := laneControlled_counts true
  have h2 := laneControlled_counts false
  have r1 := renameProgram_counts (wireFn2 L) (laneControlled true)
  have r2 := renameProgram_counts (wireFn2 L) (laneControlled false)
  simp only [if_true, Bool.false_eq_true, if_false] at h1 h2
  simp only [arith2, Bool.not_false, Bool.not_true]
  omega

theorem arith2_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (multiply : Bool) : GatePhysical (arith2 L multiply) := by
  apply gatePhysical_rename_support (wireFn2 L) (laneControlled (!multiply))
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (laneControlled_support (!multiply) ha) b
      (laneControlled_support (!multiply) hb) eq
  · exact laneControlled_physical _

/-- Every arithmetic gate is the placement of a label in the inventory other
than the avoided labels; label `1797` now lands on the site of label `769`. -/
theorem arith2_wire (L : ControlledPointLayout) (multiply : Bool) (q : Wire)
    (hq : q ∈ wires (arith2 L multiply)) :
    ∃ old ∈ slots.toFinset, goodW old ∧ q = pointWireFn L (swap2 old) := by
  rw [arith2, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨old, laneControlled_support (!multiply) used, laneControlled_avoid (!multiply) old used, rfl⟩

/-- The omitted zero high-bit copy leaves physical pool site 1800 unused. -/
theorem arith2_pool1800_unused (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) : L.core.poolWire 1800∉wires (arith2 L multiply) := by
  intro hq
  rw [arith2,renameProgram_support] at hq
  obtain ⟨old,used,e⟩ := Finset.mem_image.mp hq
  have hs := laneControlled_support (!multiply) used
  have slot : base 2312∈slots.toFinset := by
    apply slot_mem <;> simp [live,CompressedAllocation.omitted]
  have image : pointWireFn L (base 2312)=L.core.poolWire 1800 := by
    rw [pointWireFn_base]
    simp [pointIndexWire,skywalkDirectMap,skywalkPointWire]
  have same := pointWireFn_injective_slots L hw hn _ (swap2_slots old hs) _ slot (e.trans image.symm)
  have fix : swap2 (base 2312)=base 2312 := swap2_fix _ (by decide) (by decide)
  have original : old=base 2312 := by
    rw [←swap2_involutive old,same,fix]
  exact laneControlled_nohigh (!multiply) old used original

def backend2 : PointArithmeticBackend where
  program := arith2
  correct := arith2_correct
  support L hw hn multiply := by
    intro q hq
    obtain ⟨old, hs, _, rfl⟩ := arith2_wire L multiply q hq
    have := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, swap2_slots old hs, rfl⟩)
    exact List.mem_toFinset.mpr (PointArithmeticBackend.shared_subset L hw (List.mem_toFinset.mp this))

end ECDSAAdd.Entrant
