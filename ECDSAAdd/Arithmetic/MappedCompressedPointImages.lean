import ECDSAAdd.Arithmetic.MappedCompressedPointPlacement
import ECDSAAdd.Arithmetic.CompressedPointSquarePool
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open ControlledPointLayout DirectSkywalk

theorem point_pool_mem_dialog (L : ControlledPointLayout) (hw : L.Widths)
    (i : Nat) (hi : i < 2613) : L.core.poolWire i ∈ L.dialogPool := by
  change L.core.poolWire i ∈ L.core.pool.take 2613
  rw [←L.core.pool_prefix hw 2613 (by omega)]
  exact arith_mem L.core.poolWire 0 2613 i (by omega) hi

/-- Every original shared noncoordinate label is bound to existing clean
dialog work, independently of the contents of either public coordinate. -/
theorem pointIndexWire_work_mem (L : ControlledPointLayout) (hw : L.Widths)
    (i : Nat) (hi : i < 2314) (hx : i < 770 ∨ 1026 ≤ i)
    (hy : i < 2056 ∨ 2312 ≤ i) : pointIndexWire L i ∈ L.dialogPool := by
  rw [pointIndexWire_shared L i hi]
  unfold skywalkDirectMap skywalkPointWire
  have nx : ¬(770 ≤ i ∧ i < 1026) := by omega
  have ny : ¬(2056 ≤ i ∧ i < 2312) := by omega
  simp only [if_neg nx,if_neg ny]
  apply point_pool_mem_dialog L hw
  split_ifs <;> omega

theorem pointWireFn_sharedWork (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈skywalkSharedWires base,q∈slots.toFinset →
      q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 →
      pointWireFn L q∈L.dialogPool := by
  intro q hq _ hx hy
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have outsideX : i < 770 ∨ 1026 ≤ i := by
    by_contra bad
    exact hx (arith_mem base 770 256 i (by omega) (by omega))
  have outsideY : i < 2056 ∨ 2312 ≤ i := by
    by_contra bad
    exact hy (arith_mem base 2056 256 i (by omega) (by omega))
  rw [pointWireFn_base]
  exact pointIndexWire_work_mem L hw i hi.2 outsideX outsideY

theorem pointWireFn_control (L : ControlledPointLayout) : pointWireFn L (base 2400)=L.core.generic := by
  simp [pointWireFn_base,pointIndexWire,pointMeta]

theorem pointWireFn_scalar_dialog (L : ControlledPointLayout) (hw : L.Widths) :
    pointWireFn L (base 2409)∈L.dialogPool ∧ pointWireFn L (base 2410)∈L.dialogPool ∧
      pointWireFn L (base 2411)∈L.dialogPool := by
  have a := point_pool_mem_dialog L hw 1802 (by omega)
  have b := point_pool_mem_dialog L hw 1803 (by omega)
  have c := point_pool_mem_dialog L hw 1804 (by omega)
  simpa [pointWireFn_base,pointIndexWire,pointMeta,skywalkDirectSelectorG,
    skywalkDirectSelectorS,skywalkDirectZero] using And.intro a (And.intro b c)

private theorem getD_member (xs : List Wire) (i : Nat) (d : Wire) (hi : i < xs.length) :
    xs.getD i d∈xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => exact List.mem_cons_of_mem a (ih i (by simpa using hi))

private theorem pool_mem_shared (L : ControlledPointLayout) (i : Nat)
    (hi : i < 515 ∨ (684 ≤ i ∧ i < 1542) ∨ (1800 ≤ i ∧ i < 1805)) :
    L.core.poolWire i∈CompressedPointSquare.sharedPool L := by
  rcases hi with low|middle|high
  · exact List.mem_append_left _ (List.mem_append_left _
      (arith_mem L.core.poolWire 0 515 i (by omega) low))
  · exact List.mem_append_left _ (List.mem_append_right _
      (arith_mem L.core.poolWire 684 858 i middle.1 middle.2))
  · exact List.mem_append_right _ (arith_mem L.core.poolWire 1800 5 i high.1 high.2)

theorem pointIndexWire_inventory (L : ControlledPointLayout) (hw : L.Widths)
    (i : Nat) (hi : i∈indices) :
    pointIndexWire L i∈CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L := by
  have range : i < 515 ∨ (684 ≤ i ∧ i < 1798) ∨ (2056 ≤ i ∧ i < 2314) ∨
      (2400 ≤ i ∧ i < 2412) := by
    simp only [indices,List.mem_append,List.mem_range'_1] at hi
    omega
  by_cases shared : i < 2314
  · rw [pointIndexWire_shared L i shared]
    unfold skywalkDirectMap skywalkPointWire
    split_ifs with x y a b
    · apply List.mem_append_left
      have member := getD_member L.point.x (i-770) 0 (by change i-770 < L.core.input.x.length; rw [hw.inputX]; omega)
      simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
      tauto
    · apply List.mem_append_left
      have member := getD_member L.point.y (i-2056) 0 (by change i-2056 < L.core.input.y.length; rw [hw.inputY]; omega)
      simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
      tauto
    all_goals
      apply List.mem_append_right
      apply pool_mem_shared L
      omega
  · have metadata : 2400 ≤ i ∧ i < 2412 := by omega
    by_cases resident : i < 2409
    · interval_cases i <;>
        simp [pointIndexWire,pointMeta,CompressedPointSquare.residents,PointAddLayout.pointWires,inPlaceFlags]
    · have last : i=2409 ∨ i=2410 ∨ i=2411 := by omega
      rcases last with rfl|rfl|rfl
      · apply List.mem_append_right
        simpa [pointIndexWire,pointMeta,skywalkDirectSelectorG] using
          pool_mem_shared L 1802 (Or.inr (Or.inr ⟨by omega,by omega⟩))
      · apply List.mem_append_right
        simpa [pointIndexWire,pointMeta,skywalkDirectSelectorS] using
          pool_mem_shared L 1803 (Or.inr (Or.inr ⟨by omega,by omega⟩))
      · apply List.mem_append_right
        simpa [pointIndexWire,pointMeta,skywalkDirectZero] using
          pool_mem_shared L 1804 (Or.inr (Or.inr ⟨by omega,by omega⟩))

/-- Arithmetic image shares exactly the existing compressed square's
physical work inventory;515..683 never return to this support certificate. -/
theorem pointWireFn_slots_image (L : ControlledPointLayout) (hw : L.Widths) :
    slots.toFinset.image (pointWireFn L)⊆
      (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).toFinset := by
  intro q hq
  obtain ⟨old,member,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  apply List.mem_toFinset.mpr
  have same : pointWireFn L (i+16)=pointIndexWire L i := by
    simp only [pointWireFn,Nat.add_sub_cancel]
  rw [same]
  exact pointIndexWire_inventory L hw i hi

theorem pointInventory_length (L : ControlledPointLayout) (hw : L.Widths) :
    (CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L).length=1899 := by
  simp [CompressedPointSquare.residents,CompressedPointSquare.sharedPool_length,
    PointAddLayout.pointWires,inPlaceFlags,point,hw.inputX,hw.inputY]

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointWireFn_sharedWork
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointWireFn_scalar_dialog
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointWireFn_slots_image
