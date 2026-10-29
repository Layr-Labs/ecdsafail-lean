import ECDSAAdd.Submission.Entrant.FastE3
import ECDSAAdd.Submission.Entrant.LaneAvoidZ

/-! Pool site 1804 is never touched.

Site 1804 is the image of logical label `2411`, the flag of the compare-based
zero repair.  The arithmetic of `fastGeneric3` runs the bare lane kernel, which
avoids label `2411` (`laneKernel_avoid` with `2411` added to the avoided labels),
and no other block touches the site.  The whole finite-addend program therefore
lives in the site inventory with site 1804 removed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Z
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

/-- The certified pool inventory without sites 1541, 1801 and 1804. -/
def sharedPoolF (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515 ++ wireBlock L.core.poolWire 684 857 ++
    [L.core.poolWire 1800] ++ wireBlock L.core.poolWire 1802 2

def sitesN (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsN L ++ sharedPoolF L

def sitesG (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsG L ++ sharedPoolF L

theorem sitesN_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesN L).length = 1892 := by
  simp [sitesN, flagsN, sharedPoolF, PointAddLayout.pointWires, wireBlock_length,
    show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]

theorem sharedPool_F (L : ControlledPointLayout) (q : Wire) (hq : q ∈ CompressedPointSquare.sharedPool L)
    (hne : q ≠ L.core.poolWire 1801) (hne' : q ≠ L.core.poolWire 1541)
    (hne'' : q ≠ L.core.poolWire 1804) : q ∈ sharedPoolF L := by
  simp only [CompressedPointSquare.sharedPool, sharedPoolF, List.mem_append] at hq ⊢
  rcases hq with (h1 | h1) | h1
  · exact Or.inl (Or.inl (Or.inl h1))
  · simp only [wireBlock, List.mem_map, List.mem_range'_1] at h1 ⊢
    obtain ⟨i, hi, rfl⟩ := h1
    have : i ≠ 1541 := fun e => hne' (by rw [e])
    exact Or.inl (Or.inl (Or.inr ⟨i, by omega, rfl⟩))
  · have h' : q ∈ [L.core.poolWire 1800, L.core.poolWire 1801, L.core.poolWire 1802,
        L.core.poolWire 1803, L.core.poolWire 1804] := by
      simpa [wireBlock, List.range'_succ] using h1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl (Or.inr (by simp [h']))
    · exact absurd h' hne
    · exact Or.inr (by simp [wireBlock, List.range'_succ, h'])
    · exact Or.inr (by simp [wireBlock, List.range'_succ, h'])
    · exact absurd h' hne''

theorem sharedPool_sub (L : ControlledPointLayout) (q : Wire) (hq : q ∈ sharedPoolF L) :
    q ∈ Entrant.sharedPoolF L := by
  simp only [sharedPoolF, Entrant.sharedPoolF, List.mem_append, wireBlock, List.mem_map,
    List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
  rcases hq with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · obtain ⟨i, hi, rfl⟩ := h
    exact Or.inr ⟨i, by omega, rfl⟩

theorem sharedPool_Q_sub (L : ControlledPointLayout) (hw : L.Widths) (q : Wire) (hq : q ∈ sharedPoolF L) :
    q ∈ L.dialogPool :=
  Entrant.sharedPool_Q_sub L hw q (sharedPool_sub L q hq)

attribute [local irreducible] wires MappedCompressed.LaneA.laneKernel in
/-- Every gate wire of the bare kernel avoids the zero-flag label as well. -/
theorem arith3_wireZ (L : ControlledPointLayout) (multiply : Bool) (q : Wire)
    (hq : q ∈ wires (arith3 L multiply)) :
    ∃ old ∈ slots.toFinset, goodW old ∧ q = pointWireFn L (swap2 old) := by
  rw [arith3, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨old, MappedCompressed.LaneA.laneKernel_support (!multiply) used,
    laneKernel_avoid (!multiply) old used, rfl⟩

section Support
attribute [local irreducible] wires shortEqual pairEqual controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

theorem point_G (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesG L := by
  simp [sitesG, hq]
theorem control_G : L.control ∈ sitesG L := by simp [sitesG]
theorem flag_G (t : Wire) (ht : t ∈ flagsG L) : t ∈ sitesG L := by simp [sitesG, ht]
theorem x_G (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesG L :=
  point_G L q (by simp [PointAddLayout.pointWires, hq])
theorem y_G (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesG L :=
  point_G L q (by simp [PointAddLayout.pointWires, hq])
theorem generic_G : L.core.generic ∈ sitesG L := flag_G L _ (by simp [flagsG])
theorem poolQ_G (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ sitesG L := by
  simp only [sitesG, List.mem_append]; exact Or.inr hq

theorem point_N (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesN L := by
  simp [sitesN, hq]
theorem control_N : L.control ∈ sitesN L := by simp [sitesN]
theorem flag_N (t : Wire) (ht : t ∈ flagsN L) : t ∈ sitesN L := by simp [sitesN, ht]
theorem x_N (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesN L :=
  point_N L q (by simp [PointAddLayout.pointWires, hq])
theorem y_N (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesN L :=
  point_N L q (by simp [PointAddLayout.pointWires, hq])
theorem poolQ_N (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ sitesN L := by
  simp only [sitesN, List.mem_append]; exact Or.inr hq

include hw

theorem pool_lowG (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesG L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_G
  simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

theorem pool_lowN (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesN L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_N
  simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

omit hw in
theorem G_of_sites (q : Wire) (hq : q ∈ CompressedPointSquare.residents L ++ CompressedPointSquare.sharedPool L)
    (h1 : q ≠ L.core.poolWire 1801) (h1' : q ≠ L.core.poolWire 1541)
    (h2 : q ≠ L.core.equalX) (h3 : q ≠ L.core.double) (h4 : q ≠ L.infinitySelect)
    (h5 : q ≠ L.genericSelect) (h6 : q ≠ L.core.poolWire 1804) :
    q ∈ sitesG L := by
  rcases List.mem_append.mp hq with hr | hp
  · simp only [CompressedPointSquare.residents, inPlaceFlags, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (hp | hc) | hf
    · exact point_G L q hp
    · rw [hc]; exact control_G L
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h4
      · exact flag_G L _ (by simp [flagsG])
      · exact absurd rfl h5
      · exact flag_G L _ (by simp [flagsG])
      · exact absurd rfl h2
      · exact flag_G L _ (by simp [flagsG])
      · exact absurd rfl h3
  · exact poolQ_G L q (sharedPool_F L q hp h1 h1' h6)

theorem fastConstG (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).toFinset ⊆ (sitesG L).toFinset := by
  intro q hq
  have pool := L.recoveryConstant_pool hw r
  have hq' := List.mem_toFinset.mp hq
  have inpool (h : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ h
  apply List.mem_toFinset.mpr
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at hq'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at hq'
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  rcases hq' with h | (((h | h) | h) | h | h | h)
  · rw [h]; exact generic_G L
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inl (Or.inl h)))
  · rcases hr with rfl | rfl
    · exact x_G L _ h
    · exact y_G L _ h
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inl (Or.inr h)))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inl h)))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inl h))))
  · exact pool_lowG L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inr h))))

include hn

theorem arith3G (multiply : Bool) :
    wires (arith3 L multiply) ⊆ (sitesG L).toFinset := by
  intro q hq
  obtain ⟨old, hslot, hgood, rfl⟩ := arith3_wireZ L multiply q hq
  have hs2 := swap2_slots old hslot
  have inv := pointWireFn_slots_image L hw (Finset.mem_image.mpr ⟨swap2 old, hs2, rfl⟩)
  have avoid (k : Nat) (hk : base k ∈ slots.toFinset) (hb : pointWireFn L (base k) = pointWireFn L (swap2 old)) :
      old = swap2 (base k) := by
    have := pointWireFn_injective_slots L hw hn _ hs2 (base k) hk hb.symm
    rw [← this, swap2_involutive]
  have mem (k : Nat) (hk : k ∈ indices) : base k ∈ slots.toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hidx (k : Nat) (h : k = 2313 ∨ k = 2403 ∨ k = 2405 ∨ k = 2406 ∨ k = 2408 ∨ k = 769 ∨ k = 2411) : k ∈ indices := by
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
    have himg : pointWireFn L (base 2411) = L.core.poolWire 1804 := by
      rw [pointWireFn_base]; exact (pointIndexWire_metadata L).2.2.2.2.2.2.2.2.2.2.2
    have := avoid 2411 (mem _ (hidx 2411 (by omega))) (himg.trans e.symm)
    rw [swap2_fix _ (by decide) (by decide)] at this
    subst this; exact hgood (by simp [base])

attribute [local irreducible] fastCandidate in
theorem fastSquareG : wires (fastSquare L) ⊆ (sitesG L).toFinset := by
  rw [fastSquare_eq L hw hn]
  intro q hq
  rw [fastSquareN, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have supp := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at supp
  apply List.mem_toFinset.mpr
  rcases supp with h | h | h | h
  · rw [h, CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      inPlaceFlags])]
    exact generic_G L
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact y_G L _ h
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact x_G L _ h
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)]
    apply poolQ_G
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have ha := CompressedPointSquare.prefix_allowed i bound
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, by omega, rfl⟩))

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
  have cr : wires (fastConstRefl L (3*cx-1)) ⊆ (sitesG L).toFinset :=
    (FastConst.fastRefl_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstG L hw L.point.x (Or.inl rfl))
  simp only [fastGeneric3, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _, ca _ (Or.inr rfl) _⟩, farithG L hw hn false⟩, fastSquareG L hw hn⟩,
    cr⟩, farithG L hw hn true⟩, cn⟩, ca _ (Or.inr rfl) _⟩

/-- The relabelled block lives in `sitesN`. -/
theorem renamedG (Gen : Program) (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (renameProgram (tauM L) Gen) ⊆ (sitesN L).toFinset := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have h := List.mem_toFinset.mp (hG used)
  apply List.mem_toFinset.mpr
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  by_cases hg : old = L.core.generic
  · rw [hg, show tauM L L.core.generic = L.genericSelect by simp [tauM]]
    exact flag_N L _ (by simp [flagsN])
  · have hs : old ≠ L.genericSelect := by
      intro e
      subst e
      simp only [sitesG, flagsG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.genericSelect
      have cG : 0 < List.count L.genericSelect L.inPlaceFlags :=
        List.count_pos_iff.mpr (by simp [inPlaceFlags])
      rcases h with ((hp | hc) | hf) | hp
      · have := List.count_pos_iff.mpr hp
        simp only [dialogUsedWires, List.count_append] at used
        omega
      · exact absurd hc.symm (by tauto)
      · rcases hf with e | e | e
        · exact absurd e.symm (by tauto)
        · exact hg e
        · exact absurd e (by tauto)
      · have := List.count_pos_iff.mpr (sharedPool_Q_sub L hw _ hp)
        simp only [dialogUsedWires, List.count_append] at used
        omega
    rw [show tauM L old = old by simp [tauM, hg, hs]]
    simp only [sitesG, flagsG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [sitesN, flagsN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

omit hn in
/-- Wires of the output stage, before relabelling. -/
theorem outStage_wires (C : Point) (q : Wire) (hq : q ∈ wires (outStage L C)) :
    q ∈ PointAddLayout.pointWires L.point ∨ q = L.control ∨ q = L.core.generic ∨ q ∈ flagsN L ∨
      q ∈ L.dialogPool.take 256 := by
  simp only [outStage, wires_append, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · rw [zeroFlag_wires] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl (by simp [PointAddLayout.pointWires])
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · simp only [corners2, wires_append, Finset.mem_union] at h
    have m (c : Wire) (P : Point) (hm : q ∈ wires (maskedPointConstant c L.point P)) :
        q = c ∨ q ∈ PointAddLayout.pointWires L.point := by
      have := List.mem_toFinset.mp (maskedPointConstant_support c L.point P hm)
      simpa using this
    rcases h with ((((h | h) | h) | h) | h) | h
    · rcases m _ _ h with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inl e
    all_goals first
      | (rcases m _ _ h with e | e
         · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [flagsN, e]))))
         · exact Or.inl e)
  · have hh := pairEqual_wires L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C) h
    have hy := yLow_mem L hw
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at hh
    rcases hh with rfl | rfl | rfl | rfl | h' | h'
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (by simp [PointAddLayout.pointWires, hy])
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [flagsN]))))
    · exact Or.inl (by simp [PointAddLayout.pointWires, h'])
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

theorem outStageN (C : Point) :
    wires (renameProgram (sigP L) (outStage L C)) ⊆ (sitesN L).toFinset := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  apply List.mem_toFinset.mpr
  have aw := park_away L hw hn
  have pk : parkWire L ∉ L.dialogPool.take 256 := by
    rw [pool_block L hw 256 (by omega)]
    intro h
    obtain ⟨i, hi, e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hi
    have := pool_inj L hw hn i 514 (by omega) (by omega) e
    omega
  have parkN : parkWire L ∈ sitesN L := by
    apply poolQ_N
    simp [parkWire, sharedPoolF, wireBlock, List.mem_map, List.mem_range'_1]
    exact Or.inl ⟨514, by omega, rfl⟩
  rcases outStage_wires L hw C old used with h | h | h | h | h
  · have hg : old ≠ L.core.generic := by
      intro e; subst e
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
      have a := List.count_pos_iff.mpr h
      have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
      simp only [dialogUsedWires, List.count_append] at used
      omega
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => aw.1 (e ▸ h)
      simp [sigP, hg, hk]]
    exact point_N L _ h
  · subst h
    have sep := dialogFlag_separation L hn
    have cg : L.control ≠ L.core.generic := by
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep; tauto
    rw [show sigP L L.control = L.control by
      have hk : L.control ≠ parkWire L := fun e => aw.2.1 e.symm
      simp [sigP, cg, hk]]
    exact control_N L
  · subst h; simpa [sigP] using parkN
  · have hfl : old ∈ L.inPlaceFlags := by
      simp only [flagsN, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [inPlaceFlags]
    have hg : old ≠ L.core.generic := by
      intro e; subst e
      have sep := dialogFlag_separation L hn
      simp only [flagsN, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
      rcases h with e | e | e
      · exact absurd e.symm (by tauto)
      · exact absurd e.symm (by tauto)
      · exact absurd e (by tauto)
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => aw.2.2 (e ▸ hfl)
      simp [sigP, hg, hk]]
    exact flag_N L _ h
  · have hg : old ≠ L.core.generic := by
      intro e; subst e
      have used := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
      have a := List.count_pos_iff.mpr (List.mem_of_mem_take h)
      have c : 0 < List.count L.core.generic L.inPlaceFlags := List.count_pos_iff.mpr (by simp [inPlaceFlags])
      simp only [dialogUsedWires, List.count_append] at used
      omega
    rw [show sigP L old = old by
      have hk : old ≠ parkWire L := fun e => pk (e ▸ h)
      simp [sigP, hg, hk]]
    exact pool_lowN L hw 256 (by omega) _ h

omit hn in
theorem pairN (t₁ t₂ : Wire) (h1 : t₁ ∈ flagsN L) (h2 : t₂ ∈ flagsN L) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (sitesN L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | rfl | rfl | h | h
  · exact control_N L
  · exact y_N L _ hy
  · exact flag_N L _ h1
  · exact flag_N L _ h2
  · exact x_N L _ h
  · exact pool_lowN L hw 256 (by omega) q h

omit hn in
theorem gatedN (en : Bool) (t : Wire) (ht : t ∈ flagsN L) (P : Point) :
    wires (gatedShort L en t P) ⊆ (sitesN L).toFinset := by
  cases en
  · simp [gatedShort, wires]
  · intro q hq
    simp only [gatedShort, if_true] at hq
    have h := shortEqual_wires_subset L hw L.control t P (pointCode P) hq
    rw [equalConstant_wires] at h
    have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp [PointAddLayout.pointWires, L.dialogPool_length hw,
        show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]))
    simp only [List.mem_toFinset, List.mem_cons] at h
    apply List.mem_toFinset.mpr
    rcases h with rfl | rfl | h
    · exact control_N L
    · exact flag_N L _ ht
    · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h' | h'
      · exact point_N L _ h'
      · exact pool_lowN L hw 513 (by omega) _ h'

omit hw hn in
theorem zeroFlagN (t : Wire) (ht : t ∈ flagsN L) :
    wires (zeroFlag L.point.finite L.control t) ⊆ (sitesN L).toFinset := by
  rw [zeroFlag_wires]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl
  · exact point_N L _ (by simp [PointAddLayout.pointWires])
  · exact control_N L
  · exact flag_N L _ ht

omit hw hn in
theorem chainEraseN (t : Wire) (ht : t ∈ flagsN L) :
    wires (chainErase L.control L.point.finite t) ⊆ (sitesN L).toFinset := by
  intro q hq
  have hw' : wires (chainErase L.control L.point.finite t) = {L.control, L.point.finite, t} := by
    ext q
    simp only [chainErase, wires, Instr.wires, correctionWires, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  rw [hw'] at hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact List.mem_toFinset.mpr (control_N L)
  · exact List.mem_toFinset.mpr (point_N L L.point.finite (by simp [PointAddLayout.pointWires]))
  · exact List.mem_toFinset.mpr (flag_N L _ ht)

omit hw hn in
theorem genFlagN_support : wires (genFlagN L) ⊆ (sitesN L).toFinset := by
  intro q hq
  simp [genFlagN, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl | rfl | rfl
  all_goals simp [sitesN, flagsN, PointAddLayout.pointWires]

theorem finiteProgramN_support (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (sitesG L).toFinset) :
    wires (finiteProgramN L C cy Gen) ⊆ (sitesN L).toFinset := by
  have fS : flagsN L = [L.doubleSelect, L.genericSelect, L.core.equalNegY] := rfl
  simp only [finiteProgramN, wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨pairN L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _,
    gatedN L hw _ _ (by simp [fS]) _⟩, genFlagN_support L⟩, renamedG L hw hn Gen hG⟩, genFlagN_support L⟩,
    outStageN L hw hn C⟩, gatedN L hw _ _ (by simp [fS]) _⟩, chainEraseN L _ (by simp [fS])⟩


end Support

end ECDSAAdd.Entrant.Z
