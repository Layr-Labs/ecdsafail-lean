import ECDSAAdd.Arithmetic.Paper935.FoldBlockSave

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- engine.py:3174 and luo_core.py kb_fold_const, source 64b5a13a.
The 58-bit plus/minus-(2^32+976) sign correction uses the author's 24-wire pool plan [14,22,22]. -/
def sign24Literal (subtract : Bool) : Nat :=
  if subtract then 2^58-(2^32+976) else 2^32+976

def sign24Sizes : List Nat := [14,22,22]
def sign24Starts : List Nat := [0,14,36]

theorem sign24_partition (j : Nat) (hj : j<3) :
    sign24Starts[j]?.getD 0=(sign24Sizes.take j).sum ∧
    sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0≤58 := by
  interval_cases j <;> decide

theorem sign24_forward_capacity (j : Nat) (hj : j<3) :
    2≤sign24Sizes[j]?.getD 0 ∧ j+sign24Sizes[j]?.getD 0≤24 := by
  interval_cases j <;> decide

theorem sign24_erase_capacity (j : Nat) (hj : j<2) :
    j+1+sign24Sizes[j]?.getD 0≤24 := by
  interval_cases j <;> decide

/-- Reference addresses: control 0, window bits 1..58, pool 59..82. -/
def sign24Cells (subtract : Bool) (j : Nat) (erase : Bool) : List FoldCell :=
  (List.range (sign24Sizes[j]?.getD 0)).map fun i =>
    ⟨(sign24Literal subtract).testBit (sign24Starts[j]?.getD 0+i),
      1+sign24Starts[j]?.getD 0+i,59+j+(if erase then 1 else 0)+i⟩

def sign24Input (j : Nat) : Option Wire := if j=0 then none else some (59+j-1)
def sign24Top (j : Nat) : Wire := 59+j+sign24Sizes[j]?.getD 0-1

def sign24Forward (subtract : Bool) (j : Nat) : Program :=
  if j<2 then foldBlockSave 0 (sign24Top j) (59+j) (sign24Cells subtract j false) (sign24Input j)
  else foldBlock 0 (sign24Cells subtract j false) (sign24Input j) true false

def sign24Erase (subtract : Bool) (j : Nat) : Program :=
  foldKeeperErase 0 (59+j) (sign24Cells subtract j true) (sign24Input j)

/-- The actual three forward blocks followed by reverse-order keeper erasure.
Both saved keepers live inside the same 24-wire pool. -/
def sign24Program (subtract : Bool) : Program :=
  (List.range 3).flatMap (sign24Forward subtract) ++
    (List.range 2).reverse.flatMap (sign24Erase subtract)

theorem sign24_cells_geometry (subtract : Bool) (j : Nat) (hj : j<3) :
    (0::(sign24Input j).toList++(sign24Cells subtract j false).flatMap FoldCell.wires).Nodup := by
  cases subtract <;> interval_cases j <;> decide

theorem sign24_erase_geometry (subtract : Bool) (j : Nat) (hj : j<2) :
    ([0,59+j]++(sign24Input j).toList++(sign24Cells subtract j true).flatMap FoldCell.wires).Nodup := by
  cases subtract <;> interval_cases j <;> decide

/-- Both author literals already have a nonzero bit in the first block, so
both keeper lines exist, regardless of the quantum control value. -/
theorem sign24_cells_top (subtract : Bool) (j : Nat) (hj : j<3) :
    foldBlockTop (sign24Cells subtract j false) (sign24Input j)=some (sign24Top j) := by
  cases subtract <;> interval_cases j <;> decide

theorem sign24_top_distinct (j : Nat) (hj : j<2) : sign24Top j≠59+j := by
  interval_cases j <;> decide

theorem sign24_forward_physical (subtract : Bool) (j : Nat) (hj : j<3) :
    GatePhysical (sign24Forward subtract j) := by
  by_cases h : j<2
  · rw [sign24Forward,if_pos h,foldBlockSave,gatePhysical_append]
    exact ⟨foldBlock_physical 0 _ _ true true (sign24_cells_geometry subtract j hj),
      swapBits_physical _ _ (sign24_top_distinct j h)⟩
  · rw [sign24Forward,if_neg h]
    exact foldBlock_physical 0 _ _ true false (sign24_cells_geometry subtract j hj)

theorem sign24_erase_physical (subtract : Bool) (j : Nat) (hj : j<2) :
    GatePhysical (sign24Erase subtract j) :=
  foldKeeperErase_physical 0 _ _ _ (sign24_erase_geometry subtract j hj)

theorem sign24Program_physical (subtract : Bool) : GatePhysical (sign24Program subtract) := by
  rw [sign24Program,gatePhysical_append]
  constructor
  · intro instr hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact sign24_forward_physical subtract j (List.mem_range.mp hj) instr hi
  · intro instr hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact sign24_erase_physical subtract j (List.mem_range.mp (List.mem_reverse.mp hj)) instr hi

theorem sign24_forward_support (subtract : Bool) (j : Nat) (hj : j<3) :
    wires (sign24Forward subtract j) ⊆ Finset.range 83 := by
  have cells : (0::(sign24Input j).toList++(sign24Cells subtract j false).flatMap FoldCell.wires).toFinset ⊆
      Finset.range 83 := by cases subtract <;> interval_cases j <;> decide
  by_cases h : j<2
  · rw [sign24Forward,if_pos h,foldBlockSave,wires_append,Finset.union_subset_iff]
    refine ⟨Finset.Subset.trans (foldBlock_support 0 _ _ true true) cells,?_⟩
    rw [rehome_support]
    interval_cases j <;> decide
  · rw [sign24Forward,if_neg h]
    exact Finset.Subset.trans (foldBlock_support 0 _ _ true false) cells

theorem sign24_erase_support (subtract : Bool) (j : Nat) (hj : j<2) :
    wires (sign24Erase subtract j) ⊆ Finset.range 83 := by
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
theorem sign24Program_support (subtract : Bool) : wires (sign24Program subtract)⊆Finset.range 83 := by
  rw [sign24Program,wires_append,Finset.union_subset_iff]
  constructor
  · apply flatMap_support
    intro j hj
    exact sign24_forward_support subtract j (List.mem_range.mp hj)
  · apply flatMap_support
    intro j hj
    exact sign24_erase_support subtract j (List.mem_range.mp (List.mem_reverse.mp hj))

end ECDSAAdd.Arithmetic.Paper935
