import ECDSAAdd.Arithmetic.CompressedPlacementTransport
import ECDSAAdd.Arithmetic.MappedCompressedFieldReplay

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
attribute [local irreducible] logicalCell compressedHistoryEncode compressedHistoryDecode run

/-- The reference packet retains full-sized clean logical workspace. -/
def baseGroup (divide : Bool) (j : Nat) : Program :=
  compressedHistoryDecode base (3*j) ++
  (if divide then renameProgram base (logicalCell divide (3*j)) ++
      renameProgram base (logicalCell divide (3*j+1)) ++
      renameProgram base (logicalCell divide (3*j+2))
   else renameProgram base (logicalCell divide (3*j+2)) ++
      renameProgram base (logicalCell divide (3*j+1)) ++
      renameProgram base (logicalCell divide (3*j))) ++
  compressedHistoryEncode base (3*j)

theorem shifted_cell (j : Nat) (p : Program) :
    renameProgram (shifted (CompressedAllocation.pi j)) (renameProgram base p)=
      renameProgram (placed j) p := by
  rw [renameProgram_comp]
  have eq : shifted (CompressedAllocation.pi j) ∘ base=placed j := by
    funext q
    exact shifted_base _ _
  rw [eq]

/-- Exact emitted-program equality, including every correction operand. -/
theorem mappedGroup_eq_rename (divide : Bool) (j : Nat) (hj : j < 170) :
    mappedGroup divide j=renameProgram (shifted (CompressedAllocation.pi j)) (baseGroup divide j) := by
  have codec := shifted_current_codec j hj
  have append (f : Wire → Wire) (p q : Program) :
      renameProgram f (p++q)=renameProgram f p++renameProgram f q := by
    simp only [renameProgram,List.map_append]
  cases divide <;>
    simp only [mappedGroup,baseGroup,Bool.false_eq_true,if_false,if_true,
      append,codec.1,codec.2,shifted_cell]

/-- Every measurement record yields the same complete logical State under
the injective placement. This is a packet theorem, not a whole-caller claim. -/
theorem mappedGroup_run (divide : Bool) (j : Nat) (hj : j < 170)
    (s : State) (m : List Bool) :
    pullState (shifted (CompressedAllocation.pi j)) (run (mappedGroup divide j) m s)=
      run (baseGroup divide j) m (pullState (shifted (CompressedAllocation.pi j)) s) := by
  rw [mappedGroup_eq_rename divide j hj]
  exact run_rename _ (shifted _).injective _ m s

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedGroup_eq_rename
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedGroup_run
