import ECDSAAdd.Arithmetic.Paper935.FoldBlockSave

namespace ECDSAAdd.Arithmetic.Paper935

/-- A 257-bit reference plan with a thirty-two-wire shared pool. The last
block fills the pool remaining after nine persistent keepers. -/
def fold32Sizes : List Nat := [22,30,29,28,27,26,25,24,23,23]
def fold32Starts : List Nat := [0,22,52,81,109,136,162,187,211,234]

/-- Earlier keepers occupy the lowest pool addresses. -/
def fold32ForwardPool (j : Nat) : List Nat := List.range' j (fold32Sizes[j]?.getD 0)

/-- During erasure the current keeper remains live too, so the same pool is
borrowed beginning immediately after it. Only nonfinal blocks are erased. -/
def fold32ErasePool (j : Nat) : List Nat := List.range' (j+1) (fold32Sizes[j]?.getD 0)

theorem fold32_sizes : fold32Sizes.sum=257 ∧ fold32Sizes.length=10 := by decide

theorem fold32_partition (j : Nat) (hj : j<10) :
    fold32Starts[j]?.getD 0=(fold32Sizes.take j).sum ∧
    fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0≤257 := by
  interval_cases j <;> decide +kernel

theorem fold32_forward_capacity (j : Nat) (hj : j<10) :
    2≤fold32Sizes[j]?.getD 0 ∧ j+fold32Sizes[j]?.getD 0≤32 := by
  interval_cases j <;> decide +kernel

theorem fold32_erase_capacity (j : Nat) (hj : j<9) :
    j+1+fold32Sizes[j]?.getD 0≤32 := by
  interval_cases j <;> decide +kernel

/-- Forward scratch excludes all previously saved keepers and fits thirty-two
addresses; its first address is the new keeper's destination after the sweep. -/
theorem fold32_forward_pool (j q : Nat) (hj : j<10) (hq : q∈fold32ForwardPool j) :
    j≤q ∧ q<32 := by
  have cap := (fold32_forward_capacity j hj).2
  simp only [fold32ForwardPool,List.mem_range'] at hq
  omega

/-- Comparator scratch excludes the current keeper as well as earlier ones. -/
theorem fold32_erase_pool (j q : Nat) (hj : j<9) (hq : q∈fold32ErasePool j) :
    j<q ∧ q<32 := by
  have cap := fold32_erase_capacity j hj
  simp only [fold32ErasePool,List.mem_range'] at hq
  omega

/-- In a nonfinal block the terminal carry and destination keeper are distinct. -/
theorem fold32_keeper_slot (j : Nat) (hj : j<9) :
    j∈fold32ForwardPool j ∧ j+fold32Sizes[j]?.getD 0-1∈fold32ForwardPool j ∧
    j≠j+fold32Sizes[j]?.getD 0-1 := by
  have lower := (fold32_forward_capacity j (by omega)).1
  simp only [fold32ForwardPool,List.mem_range']
  refine ⟨⟨0,by omega,by simp⟩,⟨fold32Sizes[j]?.getD 0-1,by omega,?_⟩,by omega⟩
  simp only [Nat.one_mul]
  omega

/-- Reference addresses: control 0, window bits 1..257, shared pool 258..289. -/
def fold32Cells (bits : Nat → Bool) (j : Nat) (erase : Bool) : List FoldCell :=
  (List.range (fold32Sizes[j]?.getD 0)).map fun i =>
    ⟨(if fold32Starts[j]?.getD 0+i=0 then true else bits (fold32Starts[j]?.getD 0+i)),
      1+fold32Starts[j]?.getD 0+i,258+j+(if erase then 1 else 0)+i⟩

def fold32Input (j : Nat) : Option Wire := if j=0 then none else some (258+j-1)
def fold32Top (j : Nat) : Wire := 258+j+fold32Sizes[j]?.getD 0-1

def fold32Forward (bits : Nat → Bool) (j : Nat) : Program :=
  if j<9 then foldBlockSave 0 (fold32Top j) (258+j) (fold32Cells bits j false) (fold32Input j)
  else foldBlock 0 (fold32Cells bits j false) (fold32Input j) true false

def fold32Erase (bits : Nat → Bool) (j : Nat) : Program :=
  foldKeeperErase 0 (258+j) (fold32Cells bits j true) (fold32Input j)

/-- The actual ten forward blocks followed by reverse-order keeper erasure.
All nine saved keepers live inside the same thirty-two-wire pool. -/
def fold32Program (bits : Nat → Bool) : Program :=
  (List.range 10).flatMap (fold32Forward bits) ++
    (List.range 9).reverse.flatMap (fold32Erase bits)

private theorem cells_wires (bits : Nat → Bool) (j : Nat) (erase : Bool) :
    (fold32Cells bits j erase).flatMap FoldCell.wires =
      (fold32Cells (fun _ => false) j erase).flatMap FoldCell.wires := by
  simp [fold32Cells,List.flatMap_map,FoldCell.wires]

theorem fold32_cells_geometry (bits : Nat → Bool) (j : Nat) (hj : j<10) :
    (0::(fold32Input j).toList++(fold32Cells bits j false).flatMap FoldCell.wires).Nodup := by
  rw [cells_wires bits]
  interval_cases j <;> decide +kernel

theorem fold32_erase_geometry (bits : Nat → Bool) (j : Nat) (hj : j<9) :
    ([0,258+j]++(fold32Input j).toList++(fold32Cells bits j true).flatMap FoldCell.wires).Nodup := by
  rw [cells_wires bits]
  interval_cases j <;> decide +kernel

/-- The literal is odd, so the first bit creates a terminal carry chain;
later blocks receive a saved carry regardless of the quantum control value. -/
theorem fold32_cells_top (bits : Nat → Bool) (j : Nat) (hj : j<10) :
    foldBlockTop (fold32Cells bits j false) (fold32Input j)=some (fold32Top j) := by
  interval_cases j <;> norm_num [fold32Top,fold32Cells,fold32Sizes,fold32Starts,fold32Input,foldBlockTop,FoldCell.next,List.range_succ]

theorem fold32_top_distinct (j : Nat) (hj : j<9) : fold32Top j≠258+j := by
  interval_cases j <;> decide +kernel

theorem fold32_forward_physical (bits : Nat → Bool) (j : Nat) (hj : j<10) :
    GatePhysical (fold32Forward bits j) := by
  by_cases h : j<9
  · rw [fold32Forward,if_pos h,foldBlockSave,gatePhysical_append]
    exact ⟨foldBlock_physical 0 _ _ true true (fold32_cells_geometry bits j hj),
      swapBits_physical _ _ (fold32_top_distinct j h)⟩
  · rw [fold32Forward,if_neg h]
    exact foldBlock_physical 0 _ _ true false (fold32_cells_geometry bits j hj)

theorem fold32_erase_physical (bits : Nat → Bool) (j : Nat) (hj : j<9) :
    GatePhysical (fold32Erase bits j) :=
  foldKeeperErase_physical 0 _ _ _ (fold32_erase_geometry bits j hj)

theorem fold32Program_physical (bits : Nat → Bool) : GatePhysical (fold32Program bits) := by
  rw [fold32Program,gatePhysical_append]
  constructor
  · intro instr hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact fold32_forward_physical bits j (List.mem_range.mp hj) instr hi
  · intro instr hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact fold32_erase_physical bits j (List.mem_range.mp (List.mem_reverse.mp hj)) instr hi

theorem fold32_forward_support (bits : Nat → Bool) (j : Nat) (hj : j<10) :
    wires (fold32Forward bits j) ⊆ Finset.range 290 := by
  have cells : (0::(fold32Input j).toList++(fold32Cells bits j false).flatMap FoldCell.wires).toFinset ⊆
      Finset.range 290 := by
    rw [cells_wires bits]
    interval_cases j <;> decide +kernel
  by_cases h : j<9
  · rw [fold32Forward,if_pos h,foldBlockSave,wires_append,Finset.union_subset_iff]
    refine ⟨Finset.Subset.trans (foldBlock_support 0 _ _ true true) cells,?_⟩
    rw [rehome_support]
    interval_cases j <;> decide +kernel
  · rw [fold32Forward,if_neg h]
    exact Finset.Subset.trans (foldBlock_support 0 _ _ true false) cells

theorem fold32_erase_support (bits : Nat → Bool) (j : Nat) (hj : j<9) :
    wires (fold32Erase bits j) ⊆ Finset.range 290 := by
  apply Finset.Subset.trans (foldKeeperErase_support 0 _ _ _)
  rw [cells_wires bits]
  interval_cases j <;> decide +kernel

private theorem flatMap_support (indices : List Nat) (f : Nat → Program) (support : Finset Wire)
    (h : ∀ j∈indices,wires (f j)⊆support) : wires (indices.flatMap f)⊆support := by
  induction indices with
  | nil => simp [wires]
  | cons j rest ih =>
    rw [List.flatMap_cons,wires_append,Finset.union_subset_iff]
    exact ⟨h j (by simp),ih (by intro k hk; exact h k (by simp [hk]))⟩

/-- Complete emitted fold uses one control, 257 data bits, and exactly the
same pool of thirty-two available addresses throughout both sweeps. -/
theorem fold32Program_support (bits : Nat → Bool) : wires (fold32Program bits)⊆Finset.range 290 := by
  rw [fold32Program,wires_append,Finset.union_subset_iff]
  constructor
  · apply flatMap_support
    intro j hj
    exact fold32_forward_support bits j (List.mem_range.mp hj)
  · apply flatMap_support
    intro j hj
    exact fold32_erase_support bits j (List.mem_range.mp (List.mem_reverse.mp hj))

end ECDSAAdd.Arithmetic.Paper935
