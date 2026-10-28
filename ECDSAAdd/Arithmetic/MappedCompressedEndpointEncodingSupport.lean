import ECDSAAdd.Arithmetic.MappedCompressedUnaryNaturality
import ECDSAAdd.Arithmetic.MappedCompressedCopyEndpoint
import ECDSAAdd.Arithmetic.CompressedFieldFullEncoding

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode dblInPlace halfInPlace copyRegister

private def endpointRegion (q : Nat) : Prop :=
  (512 ≤ q ∧ q ≤ 1027) ∨ (1540 ≤ q ∧ q ≤ 1797) ∨ (2056 ≤ q ∧ q ≤ 2312)

private def unaryIds : List Nat := List.range' 2056 256++[2312]++
  List.range' 512 257++List.range' 1540 256++[1797,769]
private def copyIds : List Nat := List.range' 2056 257++List.range' 770 257

private theorem unary_region (q : Nat) (h : q∈unaryIds) : endpointRegion q := by
  simp only [unaryIds,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
    or_false,or_assoc] at h
  rcases h with h|rfl|h|h|rfl|rfl
  · exact Or.inr (Or.inr (by omega))
  · norm_num [endpointRegion]
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · norm_num [endpointRegion]
  · norm_num [endpointRegion]

private theorem copy_region (q : Nat) (h : q∈copyIds) : endpointRegion q := by
  simp only [copyIds,List.mem_append,List.mem_range'_1] at h
  rcases h with h|h
  · exact Or.inr (Or.inr (by omega))
  · exact Or.inl (by omega)

private theorem endpoint_unary_history_support (divide : Bool) :
    wires (if divide then dblInPlace (borrowedSkywalkUnary base) p
      else halfInPlace (borrowedSkywalkUnary base) p)⊆(unaryIds.map base).toFinset := by
  have counts := modUnary_wires (borrowedSkywalkUnary base) 256 p
    (borrowedSkywalkUnary_widths base) (by omega)
  have view : ((borrowedSkywalkUnary base).z++(borrowedSkywalkUnary base).core.work++
      [(borrowedSkywalkUnary base).flag])=unaryIds.map base := by
    change (wireBlock base 2056 256++[base 2312])++
      (wireBlock base 512 257++wireBlock base 1540 256++[base 1797])++[base 769]=_
    simp [unaryIds,wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [←view]
  cases divide
  · simp only [Bool.false_eq_true,if_false] at hq
    rw [counts.2] at hq
    exact hq
  · simp only [if_true] at hq
    rw [counts.1] at hq
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hq))

private theorem endpoint_copy_history_support : wires (copyPairAt base)⊆(copyIds.map base).toFinset := by
  have support := copyRegister_wires_subset none (skywalkSharedField base).z (skywalkSharedField base).a
  have view : (none : Option Wire).toList++(skywalkSharedField base).z++
      (skywalkSharedField base).a=copyIds.map base := by
    rw [skywalkShared_field_z]
    change []++wireBlock base 2056 257++wireBlock base 770 257=_
    simp [copyIds,wireBlock,List.map_append]
  intro q hq
  change q∈wires (copyRegister none (skywalkSharedField base).z (skywalkSharedField base).a) at hq
  have h := support hq
  rw [view] at h
  exact h

/-- Actual instruction support, including encoder and endpoint corrections.
Every endpoint site is outside both complete512-bit history rails. -/
private theorem encoder_away (P : Program) (ids : List Nat)
    (support : wires P⊆(ids.map base).toFinset)
    (outside : ∀q∈ids,endpointRegion q) :
    Disjoint (wires (allGroupEncode base 170)) (wires P) := by
  have hist := compressedPrefix_history_support base base_pool_nodup base_above 512 (by decide)
  rw [encode_prefix_512] at hist
  apply Finset.disjoint_left.mpr
  intro q he hp
  have history := List.mem_toFinset.mp (hist he)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (support hp))
  have region := outside j hj
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,equal⟩ := List.mem_map.mp history
    have same := base_injective equal
    subst i
    simp only [List.mem_range'_1] at hi
    rcases region with region|region|region <;> omega

theorem encoder_unary_disjoint (divide : Bool) :
    Disjoint (wires (allGroupEncode base 170))
      (wires (if divide then dblInPlace (borrowedSkywalkUnary base) p
        else halfInPlace (borrowedSkywalkUnary base) p)) :=
  encoder_away _ unaryIds (endpoint_unary_history_support divide) unary_region

theorem encoder_copy_disjoint :
    Disjoint (wires (allGroupEncode base 170)) (wires (copyPairAt base)) :=
  encoder_away _ copyIds endpoint_copy_history_support copy_region

/-- Complete State equality holds for arbitrary independent measurement
record lists and arbitrary incoming phase. -/
theorem encoder_unary_commute (divide : Bool) (s : State) (m n : List Bool) :
    run (if divide then dblInPlace (borrowedSkywalkUnary base) p
      else halfInPlace (borrowedSkywalkUnary base) p) n (run (allGroupEncode base 170) m s)=
    run (allGroupEncode base 170) m
      (run (if divide then dblInPlace (borrowedSkywalkUnary base) p
        else halfInPlace (borrowedSkywalkUnary base) p) n s) :=
  (run_disjoint_commute _ _ (encoder_unary_disjoint divide) m n s).symm

theorem encoder_copy_commute (s : State) (m n : List Bool) :
    run (copyPairAt base) n (run (allGroupEncode base 170) m s)=
      run (allGroupEncode base 170) m (run (copyPairAt base) n s) :=
  (run_disjoint_commute _ _ encoder_copy_disjoint m n s).symm

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoder_unary_disjoint
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoder_copy_disjoint
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoder_unary_commute
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoder_copy_commute
