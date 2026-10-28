import ECDSAAdd.Arithmetic.Paper935.FoldBlockSave

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The secp256k1 fold uses c-1=2^32+976. Subtraction is addition of its
negative modulo the 58-bit truncation window. -/
def fold16Literal (subtract : Bool) : Nat :=
  if subtract then 2^58-(2^32+976) else 2^32+976

/-- Reference addresses: control 0, window bits 1..58, shared pool 59..74. -/
def fold16Cells (subtract : Bool) (j : Nat) (erase : Bool) : List FoldCell :=
  (List.range (fold16Sizes[j]?.getD 0)).map fun i =>
    ⟨(fold16Literal subtract).testBit (fold16Starts[j]?.getD 0+i),
      1+fold16Starts[j]?.getD 0+i,59+j+(if erase then 1 else 0)+i⟩

def fold16Input (j : Nat) : Option Wire := if j=0 then none else some (59+j-1)
def fold16Top (j : Nat) : Wire := 59+j+fold16Sizes[j]?.getD 0-1

def fold16Forward (subtract : Bool) (j : Nat) : Program :=
  if j<4 then foldBlockSave 0 (fold16Top j) (59+j) (fold16Cells subtract j false) (fold16Input j)
  else foldBlock 0 (fold16Cells subtract j false) (fold16Input j) true false

def fold16Erase (subtract : Bool) (j : Nat) : Program :=
  foldKeeperErase 0 (59+j) (fold16Cells subtract j true) (fold16Input j)

/-- The actual five forward blocks followed by reverse-order keeper erasure.
All four saved keepers live inside the same sixteen-wire pool. -/
def fold16Program (subtract : Bool) : Program :=
  (List.range 5).flatMap (fold16Forward subtract) ++
    (List.range 4).reverse.flatMap (fold16Erase subtract)

theorem fold16_cells_geometry (subtract : Bool) (j : Nat) (hj : j<5) :
    (0::(fold16Input j).toList++(fold16Cells subtract j false).flatMap FoldCell.wires).Nodup := by
  cases subtract <;> interval_cases j <;> decide

theorem fold16_erase_geometry (subtract : Bool) (j : Nat) (hj : j<4) :
    ([0,59+j]++(fold16Input j).toList++(fold16Cells subtract j true).flatMap FoldCell.wires).Nodup := by
  cases subtract <;> interval_cases j <;> decide

/-- Both author literals already have a nonzero bit in the first block, so
all four keeper lines exist, regardless of the quantum control value. -/
theorem fold16_cells_top (subtract : Bool) (j : Nat) (hj : j<5) :
    foldBlockTop (fold16Cells subtract j false) (fold16Input j)=some (fold16Top j) := by
  cases subtract <;> interval_cases j <;> decide

theorem fold16_top_distinct (j : Nat) (hj : j<4) : fold16Top j≠59+j := by
  interval_cases j <;> decide

theorem fold16_forward_physical (subtract : Bool) (j : Nat) (hj : j<5) :
    GatePhysical (fold16Forward subtract j) := by
  by_cases h : j<4
  · rw [fold16Forward,if_pos h,foldBlockSave,gatePhysical_append]
    exact ⟨foldBlock_physical 0 _ _ true true (fold16_cells_geometry subtract j hj),
      swapBits_physical _ _ (fold16_top_distinct j h)⟩
  · rw [fold16Forward,if_neg h]
    exact foldBlock_physical 0 _ _ true false (fold16_cells_geometry subtract j hj)

theorem fold16_erase_physical (subtract : Bool) (j : Nat) (hj : j<4) :
    GatePhysical (fold16Erase subtract j) :=
  foldKeeperErase_physical 0 _ _ _ (fold16_erase_geometry subtract j hj)

theorem fold16Program_physical (subtract : Bool) : GatePhysical (fold16Program subtract) := by
  rw [fold16Program,gatePhysical_append]
  constructor
  · intro instr hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact fold16_forward_physical subtract j (List.mem_range.mp hj) instr hi
  · intro instr hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact fold16_erase_physical subtract j (List.mem_range.mp (List.mem_reverse.mp hj)) instr hi

theorem fold16_forward_support (subtract : Bool) (j : Nat) (hj : j<5) :
    wires (fold16Forward subtract j) ⊆ Finset.range 75 := by
  have cells : (0::(fold16Input j).toList++(fold16Cells subtract j false).flatMap FoldCell.wires).toFinset ⊆
      Finset.range 75 := by cases subtract <;> interval_cases j <;> decide
  by_cases h : j<4
  · rw [fold16Forward,if_pos h,foldBlockSave,wires_append,Finset.union_subset_iff]
    refine ⟨Finset.Subset.trans (foldBlock_support 0 _ _ true true) cells,?_⟩
    rw [rehome_support]
    interval_cases j <;> decide
  · rw [fold16Forward,if_neg h]
    exact Finset.Subset.trans (foldBlock_support 0 _ _ true false) cells

theorem fold16_erase_support (subtract : Bool) (j : Nat) (hj : j<4) :
    wires (fold16Erase subtract j) ⊆ Finset.range 75 := by
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
same pool of sixteen available addresses throughout both sweeps. -/
theorem fold16Program_support (subtract : Bool) : wires (fold16Program subtract)⊆Finset.range 75 := by
  rw [fold16Program,wires_append,Finset.union_subset_iff]
  constructor
  · apply flatMap_support
    intro j hj
    exact fold16_forward_support subtract j (List.mem_range.mp hj)
  · apply flatMap_support
    intro j hj
    exact fold16_erase_support subtract j (List.mem_range.mp (List.mem_reverse.mp hj))

end ECDSAAdd.Arithmetic.Paper935
