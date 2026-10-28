import ECDSAAdd.Arithmetic.MappedCompressedConversionPlacement
import ECDSAAdd.Arithmetic.MappedCompressedBaseReplay
import ECDSAAdd.Arithmetic.CompressedFieldFullEncoding
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedFieldSupport
attribute [local irreducible] run wires converterPairAt allGroupEncode

private def conversionIds : List Nat := [1797,1027,1796,2311,1025]++
  List.range' 2056 255++List.range' 770 255++List.range' 1540 255

private theorem declared_conversion_support (target : Bool) :
    (if target then balancedSharedTargetConvert base else balancedSharedSourceConvert base).wires.toFinset ⊆
      (conversionIds.map base).toFinset := by
  intro q hq
  cases target <;>
    simp only [Bool.false_eq_true,if_false,if_true,balancedSharedTargetConvert,balancedSharedSourceConvert,
      BalancedConvert.Layout.wires,conversionIds,wireBlock,List.map_append,List.map_cons,List.map_nil,
      List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢ <;> tauto

private theorem conversion_support (canonical : Bool) :
    wires (converterPairAt base canonical) ⊆ (conversionIds.map base).toFinset := by
  have t := BalancedConvert.support (balancedSharedTargetConvert base)
  have u := BalancedConvert.support (balancedSharedSourceConvert base)
  have dt := declared_conversion_support true
  have ds := declared_conversion_support false
  cases canonical <;> simp only [converterPairAt,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff]
  · exact ⟨t.1.trans dt,u.1.trans ds⟩
  · exact ⟨t.2.trans dt,u.2.trans ds⟩

/-- The full history encoder and actual converters have disjoint support,
including every outcome-dependent correction site. -/
theorem encoder_conversion_disjoint (canonical : Bool) :
    Disjoint (wires (allGroupEncode base 170)) (wires (converterPairAt base canonical)) := by
  have hist := compressedPrefix_history_support base base_pool_nodup base_above 512 (by decide)
  rw [encode_prefix_512] at hist
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have history := List.mem_toFinset.mp (hist hq)
  have converted := List.mem_toFinset.mp (conversion_support canonical hc)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp converted
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp history
    have same := base_injective eq
    subst i
    simp only [List.mem_range'_1] at hi
    simp only [conversionIds,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    omega

/-- Conversion transports the entire encoded caller State, with arbitrary
independent encoder and conversion records and arbitrary incoming phase. -/
theorem encoder_conversion_commute (canonical : Bool) (s : State) (m n : List Bool) :
    run (converterPairAt base canonical) n (run (allGroupEncode base 170) m s)=
      run (allGroupEncode base 170) m (run (converterPairAt base canonical) n s) :=
  (run_disjoint_commute _ _ (encoder_conversion_disjoint canonical) m n s).symm

theorem mapped_converter_encoding (canonical : Bool) (s : State) (m n : List Bool) :
    run (renameProgram allPlaced (converterPair canonical)) n (run (allGroupEncode base 170) m s)=
      run (allGroupEncode base 170) m (run (converterPairAt base canonical) n s) := by
  rw [converterPair_placement]
  exact encoder_conversion_commute canonical s m n

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoder_conversion_disjoint
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mapped_converter_encoding
