import ECDSAAdd.Arithmetic.Paper935.FoldBlockSave

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- engine.py:3296 and luo_core.py kb_fold_const, source 64b5a13a.
The 58-bit plus/minus-one lift uses the author's 24-wire pool plan [14,22,22]. -/
def lift24Literal (subtract : Bool) : Nat :=
  if subtract then 2^58-1 else 1

def lift24Sizes : List Nat := [14,22,22]
def lift24Starts : List Nat := [0,14,36]

theorem lift24_partition (j : Nat) (hj : j<3) :
    lift24Starts[j]?.getD 0=(lift24Sizes.take j).sum ∧
    lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0≤58 := by
  interval_cases j <;> decide

theorem lift24_forward_capacity (j : Nat) (hj : j<3) :
    2≤lift24Sizes[j]?.getD 0 ∧ j+lift24Sizes[j]?.getD 0≤24 := by
  interval_cases j <;> decide

theorem lift24_erase_capacity (j : Nat) (hj : j<2) :
    j+1+lift24Sizes[j]?.getD 0≤24 := by
  interval_cases j <;> decide

/-- Reference addresses: control 0, window bits 1..58, pool 59..82. -/
def lift24Cells (subtract : Bool) (j : Nat) (erase : Bool) : List FoldCell :=
  (List.range (lift24Sizes[j]?.getD 0)).map fun i =>
    ⟨(lift24Literal subtract).testBit (lift24Starts[j]?.getD 0+i),
      1+lift24Starts[j]?.getD 0+i,59+j+(if erase then 1 else 0)+i⟩

def lift24Input (j : Nat) : Option Wire := if j=0 then none else some (59+j-1)
def lift24Top (j : Nat) : Wire := 59+j+lift24Sizes[j]?.getD 0-1

def lift24Forward (subtract : Bool) (j : Nat) : Program :=
  if j<2 then foldBlockSave 0 (lift24Top j) (59+j) (lift24Cells subtract j false) (lift24Input j)
  else foldBlock 0 (lift24Cells subtract j false) (lift24Input j) true false

def lift24Erase (subtract : Bool) (j : Nat) : Program :=
  foldKeeperErase 0 (59+j) (lift24Cells subtract j true) (lift24Input j)

/-- The actual three forward blocks followed by reverse-order keeper erasure.
Both saved keepers live inside the same 24-wire pool. -/
def lift24Program (subtract : Bool) : Program :=
  (List.range 3).flatMap (lift24Forward subtract) ++
    (List.range 2).reverse.flatMap (lift24Erase subtract)

theorem lift24_cells_geometry (subtract : Bool) (j : Nat) (hj : j<3) :
    (0::(lift24Input j).toList++(lift24Cells subtract j false).flatMap FoldCell.wires).Nodup := by
  cases subtract <;> interval_cases j <;> decide

theorem lift24_erase_geometry (subtract : Bool) (j : Nat) (hj : j<2) :
    ([0,59+j]++(lift24Input j).toList++(lift24Cells subtract j true).flatMap FoldCell.wires).Nodup := by
  cases subtract <;> interval_cases j <;> decide

/-- Both author literals already have a nonzero bit in the first block, so
both keeper lines exist, regardless of the quantum control value. -/
theorem lift24_cells_top (subtract : Bool) (j : Nat) (hj : j<3) :
    foldBlockTop (lift24Cells subtract j false) (lift24Input j)=some (lift24Top j) := by
  cases subtract <;> interval_cases j <;> decide

theorem lift24_top_distinct (j : Nat) (hj : j<2) : lift24Top j≠59+j := by
  interval_cases j <;> decide

theorem lift24_forward_physical (subtract : Bool) (j : Nat) (hj : j<3) :
    GatePhysical (lift24Forward subtract j) := by
  by_cases h : j<2
  · rw [lift24Forward,if_pos h,foldBlockSave,gatePhysical_append]
    exact ⟨foldBlock_physical 0 _ _ true true (lift24_cells_geometry subtract j hj),
      swapBits_physical _ _ (lift24_top_distinct j h)⟩
  · rw [lift24Forward,if_neg h]
    exact foldBlock_physical 0 _ _ true false (lift24_cells_geometry subtract j hj)

theorem lift24_erase_physical (subtract : Bool) (j : Nat) (hj : j<2) :
    GatePhysical (lift24Erase subtract j) :=
  foldKeeperErase_physical 0 _ _ _ (lift24_erase_geometry subtract j hj)

theorem lift24Program_physical (subtract : Bool) : GatePhysical (lift24Program subtract) := by
  rw [lift24Program,gatePhysical_append]
  constructor
  · intro instr hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact lift24_forward_physical subtract j (List.mem_range.mp hj) instr hi
  · intro instr hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact lift24_erase_physical subtract j (List.mem_range.mp (List.mem_reverse.mp hj)) instr hi

theorem lift24_forward_support (subtract : Bool) (j : Nat) (hj : j<3) :
    wires (lift24Forward subtract j) ⊆ Finset.range 83 := by
  have cells : (0::(lift24Input j).toList++(lift24Cells subtract j false).flatMap FoldCell.wires).toFinset ⊆
      Finset.range 83 := by cases subtract <;> interval_cases j <;> decide
  by_cases h : j<2
  · rw [lift24Forward,if_pos h,foldBlockSave,wires_append,Finset.union_subset_iff]
    refine ⟨Finset.Subset.trans (foldBlock_support 0 _ _ true true) cells,?_⟩
    rw [rehome_support]
    interval_cases j <;> decide
  · rw [lift24Forward,if_neg h]
    exact Finset.Subset.trans (foldBlock_support 0 _ _ true false) cells

theorem lift24_erase_support (subtract : Bool) (j : Nat) (hj : j<2) :
    wires (lift24Erase subtract j) ⊆ Finset.range 83 := by
  apply Finset.Subset.trans (foldKeeperErase_support 0 _ _ _)
  cases subtract <;> interval_cases j <;> decide

private theorem flatMap_support (indices : List Nat) (f : Nat → Program) (support : Finset Wire)
    (h : ∀ j∈indices,wires (f j)⊆support) : wires (indices.flatMap f)⊆support := by
  induction indices with
  | nil => simp [wires]
  | cons j rest ih =>
    rw [List.flatMap_cons,wires_append,Finset.union_subset_iff]
    exact ⟨h j (by simp),ih (by intro k hk; exact h k (by simp [hk]))⟩

/-- Complete emitted fold uses one control, 58 data bits, and exactly the
same pool of 24 available addresses throughout both sweeps. -/
theorem lift24Program_support (subtract : Bool) : wires (lift24Program subtract)⊆Finset.range 83 := by
  rw [lift24Program,wires_append,Finset.union_subset_iff]
  constructor
  · apply flatMap_support
    intro j hj
    exact lift24_forward_support subtract j (List.mem_range.mp hj)
  · apply flatMap_support
    intro j hj
    exact lift24_erase_support subtract j (List.mem_range.mp (List.mem_reverse.mp hj))

end ECDSAAdd.Arithmetic.Paper935
