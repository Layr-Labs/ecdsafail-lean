import ECDSAAdd.Submission.Entrant.ArithAvoid

/-! Pool site 1801 is never touched.

The published Skywalk support certificate charges the five pool sites
1800–1804 to the arithmetic.  Site 1801 is the image of logical label 2313,
which the arithmetic avoids (`controlled_avoid`).  Every other block works on
resident sites, on a short pool prefix, or (the square) on relabelled sites
below 945.  So the whole finite-addend program lives in the certified site
inventory with site 1801 removed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout
attribute [local irreducible] wires controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection

/-- The certified pool inventory without site 1801. -/
def sharedPoolQ (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515 ++ wireBlock L.core.poolWire 684 858 ++
    [L.core.poolWire 1800] ++ wireBlock L.core.poolWire 1802 3

def sitesQ (L : ControlledPointLayout) : List Wire :=
  CompressedPointSquare.residents L ++ sharedPoolQ L

theorem sitesQ_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesQ L).length = 1898 := by
  simp only [sitesQ, sharedPoolQ, List.length_append, wireBlock_length, List.length_cons,
    List.length_nil, CompressedPointSquare.residents_length L hw]

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hn in
theorem pool_block (n : Nat) (hn' : n ≤ 2613) : L.dialogPool.take n = wireBlock L.core.poolWire 0 n := by
  simp only [dialogPool, List.take_take, Nat.min_eq_left hn']
  exact (L.core.pool_prefix hw n (by omega)).symm

theorem pool_inj (i j : Nat) (hi : i < 2613) (hj : j < 2613)
    (h : L.core.poolWire i = L.core.poolWire j) : i = j := by
  have nd : (wireBlock L.core.poolWire 0 2613).Nodup := by
    rw [← pool_block L hw 2613 (le_refl _)]
    exact (List.take_sublist _ _).nodup (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.1
  have := List.inj_on_of_nodup_map nd (x := i) (y := j)
    (by simp [List.mem_range'_1]; omega) (by simp [List.mem_range'_1]; omega) h
  exact this

omit hn in
theorem p1801_pool : L.core.poolWire 1801 ∈ L.dialogPool := by
  have : L.core.poolWire 1801 ∈ L.dialogPool.take 2613 := by
    rw [pool_block L hw 2613 (le_refl _)]
    exact List.mem_map.mpr ⟨1801, by simp [List.mem_range'_1], rfl⟩
  exact List.mem_of_mem_take this

theorem p1801_not_resident : L.core.poolWire 1801 ∉ CompressedPointSquare.residents L := by
  intro h
  have dis := (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.2
  exact dis _ (by simpa [dialogUsedWires, CompressedPointSquare.residents] using h) _
    (p1801_pool L hw) rfl

theorem p1801_not_take (k : Nat) (hk : k ≤ 1801) : L.core.poolWire 1801 ∉ L.dialogPool.take k := by
  rw [pool_block L hw k (by omega)]
  intro h
  obtain ⟨i, hi, he⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hi
  have := pool_inj L hw hn i 1801 (by omega) (by omega) he
  omega

/-- Any block confined to residents and a short pool prefix avoids site 1801. -/
theorem p1801_of_subset (P : Program) (k : Nat) (hk : k ≤ 1801)
    (h : wires P ⊆ (CompressedPointSquare.residents L ++ L.dialogPool.take k).toFinset) :
    L.core.poolWire 1801 ∉ wires P := by
  intro hp
  have := List.mem_toFinset.mp (h hp)
  rcases List.mem_append.mp this with h1 | h1
  · exact p1801_not_resident L hw hn h1
  · exact p1801_not_take L hw hn k hk h1

theorem p1801_arith (multiply : Bool) :
    L.core.poolWire 1801 ∉ wires (pointCompressedArithmetic L multiply) := by
  intro hq
  rw [pointCompressedArithmetic, renameProgram_support] at hq
  obtain ⟨old, used, he⟩ := Finset.mem_image.mp hq
  have hslot := controlled_support (!multiply) used
  have hgood := controlled_avoid (!multiply) old used
  have hbase : base 2313 ∈ slots.toFinset := by
    apply slot_mem
    · unfold live; omega
    · unfold CompressedAllocation.omitted; omega
  have himg : pointWireFn L (base 2313) = L.core.poolWire 1801 := by
    simp only [pointWireFn_base, pointIndexWire, show (2313:Nat) < 2314 by omega, if_true]
    simp [skywalkDirectMap, skywalkPointWire]
  have := pointWireFn_injective_slots L hw hn old hslot (base 2313) hbase (he.trans himg.symm)
  subst this
  exact hgood (by simp [base])

theorem p1801_square : L.core.poolWire 1801 ∉ wires (CompressedPointSquare.computableProgram L) := by
  rw [CompressedPointSquare.computableProgram_eq L hw hn]
  intro hq
  rw [CompressedPointSquare.program, renameProgram_support] at hq
  obtain ⟨old, used, he⟩ := Finset.mem_image.mp hq
  have supp := pointMeasuredSquareCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at supp
  have res : old ∈ CompressedPointSquare.residents L ∨ old ∈ L.dialogPool.take 776 := by
    simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  rcases res with res | mem
  · rw [CompressedPointSquare.resident_fixed L hw hn old res] at he
    subst he
    exact p1801_not_resident L hw hn res
  · rw [pool_block L hw 776 (by omega)] at mem
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)] at he
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have := pool_inj L hw hn _ 1801 (by omega) (by omega) he
    omega

theorem p1801_constAdd (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (k : Fp) :
    L.core.poolWire 1801 ∉ wires (pointDialogConstantAdd L r k) := by
  apply p1801_of_subset L hw hn _ 515 (by omega)
  intro q hq
  have h := List.mem_toFinset.mp (pointRecoveryConstantAdd_support L hw r k hq)
  apply List.mem_toFinset.mpr
  simp only [List.mem_cons, List.mem_append] at h
  simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl <;> tauto

theorem p1801_recovery (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (pointRecoveryStage L cx cy) := by
  apply p1801_of_subset L hw hn _ 515 (by omega)
  intro q hq
  have h := List.mem_toFinset.mp (pointRecoveryStage_support L hw cx cy hq)
  apply List.mem_toFinset.mpr
  simp only [recoveryStageSites, List.mem_append] at h
  simp only [CompressedPointSquare.residents, List.mem_append]
  tauto

theorem p1801_generic (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (pointCompressedDialogGeneric L cx cy) := by
  have a1 := p1801_constAdd L hw hn L.point.x (Or.inl rfl) (-cx)
  have a2 := p1801_constAdd L hw hn L.point.y (Or.inr rfl) (-cy)
  have a3 := p1801_constAdd L hw hn L.point.x (Or.inl rfl) (3*cx)
  have d := p1801_arith L hw hn false
  have m := p1801_arith L hw hn true
  have s := p1801_square L hw hn
  have r := p1801_recovery L hw hn cx cy
  simp only [pointCompressedDialogGeneric, wires_append, Finset.mem_union, not_or]
  exact ⟨⟨⟨⟨⟨⟨a1, a2⟩, d⟩, s⟩, a3⟩, m⟩, r⟩

omit hw hn in
/-- A site of the original inventory other than pool site 1801 is in `sitesQ`. -/
theorem sitesQ_of_sites (q : Wire) (hq : q ∈ CompressedPointDialog.sites L)
    (hne : q ≠ L.core.poolWire 1801) : q ∈ sitesQ L := by
  simp only [CompressedPointDialog.sites, sitesQ, CompressedPointSquare.sharedPool, sharedPoolQ,
    List.mem_append] at hq ⊢
  rcases hq with h | ((h | h) | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · have h' : q ∈ [L.core.poolWire 1800, L.core.poolWire 1801, L.core.poolWire 1802,
        L.core.poolWire 1803, L.core.poolWire 1804] := by
      simpa [wireBlock, List.range'_succ] using h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inr (Or.inl (Or.inr (by simp [h'])))
    · exact absurd h' hne
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))
    · exact Or.inr (Or.inr (by simp [wireBlock, List.range'_succ, h']))

end

end ECDSAAdd.Entrant
