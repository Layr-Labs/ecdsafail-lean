import ECDSAAdd.Arithmetic.DirectSkywalkFieldSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BalancedSharedFieldSupport
open Secp256k1
attribute [local irreducible] wireBlock dblInPlace halfInPlace copyRegister
theorem unary (w : Nat → Wire) (W : Finset Wire) (hW : (skywalkSharedWires w).toFinset⊆W) :
    wires (dblInPlace (skywalkSharedField w).unary p)⊆W ∧
    wires (halfInPlace (skywalkSharedField w).unary p)⊆W := by
  have hw := skywalkShared_field_widths w
  have hu := modUnary_wires (skywalkSharedField w).unary 256 p
    ((skywalkSharedField w).unary_widths 256 hw) (by omega)
  constructor
  · rw [hu.1]
    intro q hq
    apply hW
    apply List.mem_toFinset.mpr
    apply retained_field_subset_shared w
    simp only [List.mem_toFinset,List.mem_append,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.unary,ModUnaryLayout.z,
      ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,
      ModInPlaceLayout.z] at hq ⊢
    tauto
  · rw [hu.2]
    intro q hq
    apply hW
    apply List.mem_toFinset.mpr
    apply retained_field_subset_shared w
    simp only [List.mem_toFinset,List.mem_append,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.unary,ModUnaryLayout.z,
      ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,
      ModInPlaceLayout.z] at hq ⊢
    tauto

theorem copy (w : Nat → Wire) (W : Finset Wire) (hW : (skywalkSharedWires w).toFinset⊆W) :
    wires (copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a)⊆W := by
  have hw := skywalkShared_field_widths w
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  rw [copyRegister_wires none (skywalkSharedField w).z (skywalkSharedField w).a hlen]
  split
  · exact Finset.empty_subset _
  · intro q hq
    apply hW
    apply List.mem_toFinset.mpr
    apply retained_field_subset_shared w
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hz|ha
    · simp [ModInPlaceLayout.wires,hz]
    · simp [ModInPlaceLayout.wires,ha]

end ECDSAAdd.Arithmetic.BalancedSharedFieldSupport
#print axioms ECDSAAdd.Arithmetic.BalancedSharedFieldSupport.unary
#print axioms ECDSAAdd.Arithmetic.BalancedSharedFieldSupport.copy
