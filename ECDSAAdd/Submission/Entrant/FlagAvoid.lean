import ECDSAAdd.Submission.Entrant.FastE
import ECDSAAdd.Submission.Entrant.FiniteArith

/-! The generic block does not use the corner selector `genericSelect`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog
attribute [local irreducible] wires arith2 farith fastSquare fastCandidate

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

private theorem genericSelect_away :
    L.genericSelect∉L.core.generic::(PointAddLayout.pointWires L.point++L.dialogPool) := by
  intro h
  have count := List.count_pos_iff.mpr h
  have full := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.genericSelect
  simp only [dialogUsedWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil,
    beq_self_eq_true,if_true] at full count
  omega

private theorem genericSelect_point : L.genericSelect∉PointAddLayout.pointWires L.point :=
  fun h => genericSelect_away L hw hn (by simp [h])

private theorem genericSelect_pool : L.genericSelect∉L.dialogPool :=
  fun h => genericSelect_away L hw hn (by simp [h])

private theorem genericSelect_generic : L.genericSelect≠L.core.generic :=
  fun h => genericSelect_away L hw hn (by simp [h])

private theorem const_no_selector (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    L.genericSelect∉(L.core.generic::(L.recoveryConstant r).wires).toFinset := by
  intro h
  have pool := L.recoveryConstant_pool hw r
  have inpool (q : Wire) (hq : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool := List.mem_of_mem_take (pool ▸ hq)
  have h' := List.mem_toFinset.mp h
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at h'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at h'
  rcases h' with h | (((h | h) | h) | h | h | h)
  · exact genericSelect_generic L hw hn h
  · exact genericSelect_pool L hw hn (inpool _ (by simp [h]))
  · apply genericSelect_point L hw hn
    rcases hr with rfl|rfl <;> simp [PointAddLayout.pointWires,h]
  all_goals exact genericSelect_pool L hw hn (inpool _ (by simp [h]))

private theorem arith_no_selector (multiply : Bool) :
    L.genericSelect∉wires (arith2 L multiply) := by
  intro hq
  obtain ⟨old,hs,hgood,e⟩ := arith2_wire L multiply L.genericSelect hq
  have slot : base 2405∈slots.toFinset := by
    apply slot_mem <;> simp [live,CompressedAllocation.omitted]
  have image : pointWireFn L (base 2405)=L.genericSelect := by
    rw [pointWireFn_base]
    exact (pointIndexWire_metadata L).2.2.2.2.2.1
  have same := pointWireFn_injective_slots L hw hn _ (swap2_slots old hs) _ slot
    (e.symm.trans image.symm)
  have original : old=base 2405 := by
    rw [←swap2_involutive old,same,swap2_fix _ (by decide) (by decide)]
  subst original
  exact hgood (by simp [base])

private theorem farith_no_selector (multiply : Bool) :
    L.genericSelect∉wires (farith L multiply) := by
  have point := genericSelect_point L hw hn
  have fin : L.genericSelect≠L.point.finite := fun h => point (by simp [PointAddLayout.pointWires,h])
  have x : L.genericSelect≠x0 L := fun h => point (by
    rw [h]; simp only [PointAddLayout.pointWires,List.mem_cons,List.mem_append]
    exact Or.inl (Or.inr (x0_mem L hw)))
  have pf : L.genericSelect∉wires (pfix L) := by
    simp [pfix,wires,Instr.wires,fin,x]
  have core : L.genericSelect∉wires (arith3 L multiply) :=
    fun h => arith_no_selector L hw hn multiply (arith3_support L multiply h)
  simpa only [farith,wires_append,Finset.mem_union,not_or] using And.intro pf (And.intro core pf)

private theorem candidate_no_selector : L.genericSelect∉wires (fastCandidate L) := by
  intro h
  have hs := List.mem_toFinset.mp (fastCandidate_support L hw hn h)
  simp only [List.mem_cons,List.mem_append,or_assoc] at hs
  rcases hs with h|h|h|h
  · exact genericSelect_generic L hw hn h
  · exact genericSelect_point L hw hn (by simp [PointAddLayout.pointWires,h])
  · exact genericSelect_point L hw hn (by simp [PointAddLayout.pointWires,h])
  · exact genericSelect_pool L hw hn (List.mem_of_mem_take h)

private theorem square_no_selector : L.genericSelect∉wires (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  intro h
  rw [fastSquareN,renameProgram_support] at h
  obtain ⟨old,used,e⟩ := Finset.mem_image.mp h
  have fixed := CompressedPointSquare.resident_fixed L hw hn L.genericSelect
    (by simp [CompressedPointSquare.residents,inPlaceFlags])
  have same := (CompressedPointSquare.poolPermutation L.core.poolWire
    (CompressedPointSquare.layout_bounded_injective L hw hn)).injective (e.trans fixed.symm)
  subst same
  exact candidate_no_selector L hw hn used

/-- Actual generic-block support excludes the selector used by the corners. -/
theorem fastGeneric2_no_genericSelect (cx cy : Fp) :
    L.genericSelect∉wires (fastGeneric2 L cx cy) := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      L.genericSelect∉wires (fastConstAdd L r k) :=
    fun h => const_no_selector L hw hn r hr ((FastConst.fastAdd_support _ _
      ⟨256,L.recoveryConstant_widths hw r (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩) h)
  have cn : L.genericSelect∉wires (fastConstNeg L cx) :=
    fun h => const_no_selector L hw hn L.point.x (Or.inl rfl) ((FastConst.fastNeg_support _ _
      ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩) h)
  have cr : L.genericSelect∉wires (fastConstRefl L (3*cx-1)) :=
    fun h => const_no_selector L hw hn L.point.x (Or.inl rfl) ((FastConst.fastRefl_support _ _
      ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩) h)
  simp only [fastGeneric2,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _,ca _ (Or.inr rfl) _⟩,
    farith_no_selector L hw hn false⟩,square_no_selector L hw hn⟩,cr⟩,
    farith_no_selector L hw hn true⟩,cn⟩,ca _ (Or.inr rfl) _⟩

end
end ECDSAAdd.Entrant
