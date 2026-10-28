import ECDSAAdd.Arithmetic.Paper935.FoldKeeperErase

namespace ECDSAAdd.Arithmetic.Paper935

/-- The author's `_plan(58,16)` after shrinking the early blocks. The last
block fills the pool remaining after four persistent keepers. -/
def fold16Sizes : List Nat := [7,14,13,12,12]
def fold16Starts : List Nat := [0,7,21,34,46]

/-- Earlier keepers occupy the lowest pool addresses. -/
def fold16ForwardPool (j : Nat) : List Nat := List.range' j (fold16Sizes[j]?.getD 0)

/-- During erasure the current keeper remains live too, so the same pool is
borrowed beginning immediately after it. Only nonfinal blocks are erased. -/
def fold16ErasePool (j : Nat) : List Nat := List.range' (j+1) (fold16Sizes[j]?.getD 0)

theorem fold16_sizes : fold16Sizes.sum=58 ∧ fold16Sizes.length=5 := by decide

theorem fold16_partition (j : Nat) (hj : j<5) :
    fold16Starts[j]?.getD 0=(fold16Sizes.take j).sum ∧
    fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0≤58 := by
  interval_cases j <;> decide

theorem fold16_forward_capacity (j : Nat) (hj : j<5) :
    2≤fold16Sizes[j]?.getD 0 ∧ j+fold16Sizes[j]?.getD 0≤16 := by
  interval_cases j <;> decide

theorem fold16_erase_capacity (j : Nat) (hj : j<4) :
    j+1+fold16Sizes[j]?.getD 0≤16 := by
  interval_cases j <;> decide

/-- Forward scratch excludes all previously saved keepers and fits sixteen
addresses; its first address is the new keeper's destination after the sweep. -/
theorem fold16_forward_pool (j q : Nat) (hj : j<5) (hq : q∈fold16ForwardPool j) :
    j≤q ∧ q<16 := by
  have cap := (fold16_forward_capacity j hj).2
  simp only [fold16ForwardPool,List.mem_range'] at hq
  omega

/-- Comparator scratch excludes the current keeper as well as earlier ones. -/
theorem fold16_erase_pool (j q : Nat) (hj : j<4) (hq : q∈fold16ErasePool j) :
    j<q ∧ q<16 := by
  have cap := fold16_erase_capacity j hj
  simp only [fold16ErasePool,List.mem_range'] at hq
  omega

/-- In a nonfinal block the terminal carry and destination keeper are distinct. -/
theorem fold16_keeper_slot (j : Nat) (hj : j<4) :
    j∈fold16ForwardPool j ∧ j+fold16Sizes[j]?.getD 0-1∈fold16ForwardPool j ∧
    j≠j+fold16Sizes[j]?.getD 0-1 := by
  have lower := (fold16_forward_capacity j (by omega)).1
  simp only [fold16ForwardPool,List.mem_range']
  refine ⟨⟨0,by omega,by simp⟩,⟨fold16Sizes[j]?.getD 0-1,by omega,?_⟩,by omega⟩
  simp only [Nat.one_mul]
  omega

end ECDSAAdd.Arithmetic.Paper935
