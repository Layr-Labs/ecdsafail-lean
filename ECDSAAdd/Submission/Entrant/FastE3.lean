import ECDSAAdd.Submission.Entrant.FastGeneric3
import ECDSAAdd.Submission.Entrant.FlagMerge

/-! Support and boundary contract of `fastGeneric3` in the `sitesE` inventory. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog
attribute [local irreducible] wires controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram MappedCompressed.LaneA.laneKernel

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem arith3E (multiply : Bool) :
    wires (arith3 L multiply) ⊆ (sitesE L).toFinset := by
  intro q hq
  obtain ⟨old, hslot, hgood, rfl⟩ := arith3_wire L multiply q hq
  have hs2 := swap2_slots old hslot
  have inv := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, hs2, rfl⟩)
  have avoid (k : Nat) (hk : base k ∈ slots.toFinset) (hb : pointWireFn L (base k) = pointWireFn L (swap2 old)) :
      old = swap2 (base k) := by
    have := pointWireFn_injective_slots L hw hn _ hs2 (base k) hk hb.symm
    rw [← this, swap2_involutive]
  have mem (k : Nat) (hk : k ∈ indices) : base k ∈ slots.toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hidx (k : Nat) (h : k = 2313 ∨ k = 2406 ∨ k = 2408 ∨ k = 769 ∨ k = 2403) : k ∈ indices := by
    simp only [indices, List.mem_append, List.mem_range'_1]; omega
  apply List.mem_toFinset.mpr
  apply E_of_sites L _ (List.mem_toFinset.mp inv)
  · intro e
    have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
      simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 2313 (mem _ (hidx 2313 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 1797) = L.core.poolWire 1541 := by
      simp only [pointWireFn_base, pointIndexWire, show (1797:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 1797 m1797 (himg.trans e.symm)
    rw [show swap2 (base 1797) = base 769 by simp only [swap2, base]; simp] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2406) = L.core.equalX := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.1
    have := avoid 2406 (mem _ (hidx 2406 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2408) = L.core.double := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.2.1
    have := avoid 2408 (mem _ (hidx 2408 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2403) = L.infinitySelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.1
    have := avoid 2403 (mem _ (hidx 2403 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])

theorem farithE (multiply : Bool) :
    wires (farith L multiply) ⊆ (sitesE L).toFinset := by
  have pf : wires (pfix L) ⊆ (sitesE L).toFinset := by
    intro q hq
    simp only [pfix, wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hq
    apply List.mem_toFinset.mpr
    have hf : L.point.finite ∈ sitesE L := point_E L _ (by simp [PointAddLayout.pointWires])
    have hx : x0 L ∈ sitesE L := x_E L _ (x0_mem L hw)
    rcases hq with rfl | (rfl | rfl) | rfl <;> assumption
  simp only [farith, wires_append, Finset.union_subset_iff]
  exact ⟨pf, arith3E L hw hn multiply, pf⟩

theorem fastGeneric3E (cx cy : Fp) : wires (fastGeneric3 L cx cy) ⊆ (sitesE L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (fastConstAdd L r k) ⊆ (sitesE L).toFinset :=
    (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩).trans
      (fastConstE L hw r hr)
  have cn : wires (fastConstNeg L cx) ⊆ (sitesE L).toFinset :=
    (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstE L hw L.point.x (Or.inl rfl))
  have cr := ca L.point.x (Or.inl rfl) (3*cx)
  simp only [fastGeneric3, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _, ca _ (Or.inr rfl) _⟩, farithE L hw hn false⟩, fastSquareE L hw hn⟩,
    cr⟩, farithE L hw hn true⟩, cn⟩, ca _ (Or.inr rfl) _⟩

theorem arith3G (multiply : Bool) :
    wires (arith3 L multiply) ⊆ (sitesG L).toFinset := by
  intro q hq
  obtain ⟨old, hslot, hgood, rfl⟩ := arith3_wire L multiply q hq
  have hs2 := swap2_slots old hslot
  have inv := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, hs2, rfl⟩)
  have avoid (k : Nat) (hk : base k ∈ slots.toFinset) (hb : pointWireFn L (base k) = pointWireFn L (swap2 old)) :
      old = swap2 (base k) := by
    have := pointWireFn_injective_slots L hw hn _ hs2 (base k) hk hb.symm
    rw [← this, swap2_involutive]
  have mem (k : Nat) (hk : k ∈ indices) : base k ∈ slots.toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hidx (k : Nat) (h : k = 2313 ∨ k = 2403 ∨ k = 2405 ∨ k = 2406 ∨ k = 2407 ∨ k = 2408 ∨ k = 769) : k ∈ indices := by
    simp only [indices, List.mem_append, List.mem_range'_1]; omega
  apply List.mem_toFinset.mpr
  apply G_of_sites L _ (List.mem_toFinset.mp inv)
  · intro e
    have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
      simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 2313 (mem _ (hidx 2313 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 1797) = L.core.poolWire 1541 := by
      simp only [pointWireFn_base, pointIndexWire, show (1797:Nat) < 2314 by omega, if_true]
      simp [skywalkDirectMap, skywalkPointWire]
    have := avoid 1797 m1797 (himg.trans e.symm)
    rw [show swap2 (base 1797) = base 769 by simp only [swap2, base]; simp] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2406) = L.core.equalX := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.1
    have := avoid 2406 (mem _ (hidx 2406 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2408) = L.core.double := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.2.1
    have := avoid 2408 (mem _ (hidx 2408 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2403) = L.infinitySelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.1
    have := avoid 2403 (mem _ (hidx 2403 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2405) = L.genericSelect := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.1
    have := avoid 2405 (mem _ (hidx 2405 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])
  · intro e
    have himg : pointWireFn L (base 2407) = L.core.equalNegY := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.1
    have := avoid 2407 (mem _ (hidx 2407 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])

theorem farithG (multiply : Bool) :
    wires (farith L multiply) ⊆ (sitesG L).toFinset := by
  have pf : wires (pfix L) ⊆ (sitesG L).toFinset := by
    intro q hq
    simp only [pfix, wires, Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, or_false] at hq
    apply List.mem_toFinset.mpr
    have hf : L.point.finite ∈ sitesG L := point_G L _ (by simp [PointAddLayout.pointWires])
    have hx : x0 L ∈ sitesG L := x_G L _ (x0_mem L hw)
    rcases hq with rfl | (rfl | rfl) | rfl <;> assumption
  simp only [farith, wires_append, Finset.union_subset_iff]
  exact ⟨pf, arith3G L hw hn multiply, pf⟩

theorem fastGeneric3G (cx cy : Fp) : wires (fastGeneric3 L cx cy) ⊆ (sitesG L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (fastConstAdd L r k) ⊆ (sitesG L).toFinset :=
    (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩).trans
      (fastConstG L hw r hr)
  have cn : wires (fastConstNeg L cx) ⊆ (sitesG L).toFinset :=
    (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstG L hw L.point.x (Or.inl rfl))
  have cr := ca L.point.x (Or.inl rfl) (3*cx)
  simp only [fastGeneric3, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _, ca _ (Or.inr rfl) _⟩, farithG L hw hn false⟩, fastSquareG L hw hn⟩,
    cr⟩, farithG L hw hn true⟩, cn⟩, ca _ (Or.inr rfl) _⟩

theorem fastGeneric3_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (fastGeneric3 L cx cy) :=
  fun R b f hg => fast3_boundary_generic L hw hn R b f hc hg

end

end ECDSAAdd.Entrant
