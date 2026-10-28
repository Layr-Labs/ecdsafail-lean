import ECDSAAdd.Arithmetic.SelectedCellPhysical
import ECDSAAdd.Arithmetic.CompactWalkPhysical
import ECDSAAdd.Arithmetic.BalancedConvertPhysical
import ECDSAAdd.Arithmetic.PenultimateMappedProgram
namespace ECDSAAdd.Arithmetic
open RecordedQuantum MappedCompressed

theorem logicalCell_physical (divide : Bool) (i : Nat) (hi : i<512) :
    GatePhysical (logicalCell divide i) := by
  have h := fixedSelectedCells_physical i hi
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2
  cases divide <;> simp only [logicalCell,Bool.false_eq_true,if_false,if_true]
  · exact h.2
  · exact h.1

theorem mappedGroup_physical (divide : Bool) (j : Nat) (hj : j<170) :
    GatePhysical (mappedGroup divide j) := by
  have codec := transcriptCodec_physical (compressedHistoryMap (placed j) (3*j))
  have a := gatePhysical_rename _ (placed_injective j) _ (logicalCell_physical divide (3*j) (by omega))
  have b := gatePhysical_rename _ (placed_injective j) _ (logicalCell_physical divide (3*j+1) (by omega))
  have c := gatePhysical_rename _ (placed_injective j) _ (logicalCell_physical divide (3*j+2) (by omega))
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨codec.2,⟨⟨c,b⟩,a⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨a,b⟩,c⟩⟩,codec.1⟩

theorem mappedGroups_physical (divide : Bool) (j n : Nat) (hj : j+n≤170) :
    GatePhysical (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp [mappedGroups,GatePhysical]
  | succ n ih =>
    have head := mappedGroup_physical divide j (by omega)
    have tail := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem fixedConverters_physical (canonical : Bool) : GatePhysical (converterPair canonical) := by
  have hn : (skywalkSharedWires id).Nodup := by
    simpa only [skywalkSharedWires,wireBlock,List.map_id] using (List.nodup_range' (s:=0) (n:=2314))
  have ht := balancedSharedTargetConvert_nodup id hn
  have hs := balancedSharedSourceConvert_nodup id hn
  have t := balancedConverters_physical _ ht
  have s := balancedConverters_physical _ hs
  cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨t.1,s.1⟩
  · exact ⟨t.2,s.2⟩

theorem firstMappedGroup_physical (divide : Bool) : GatePhysical (EntryMappedFieldSegmentTrim.firstGroup divide) := by
  have zero : GatePhysical EntryMappedFieldSegmentTrim.logicalZero :=
    transcriptWindow_physical _ _ _ _ _ (by decide) (by decide) fixedFieldSwap_physical
  have z := gatePhysical_rename _ (placed_injective 0) _ zero
  have a := gatePhysical_rename _ (placed_injective 0) _ (logicalCell_physical divide 1 (by decide))
  have b := gatePhysical_rename _ (placed_injective 0) _ (logicalCell_physical divide 2 (by decide))
  have codec := transcriptCodec_physical (compressedHistoryMap (placed 0) 0)
  cases divide <;> simp only [EntryMappedFieldSegmentTrim.firstGroup,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨codec.2,⟨⟨b,a⟩,z⟩⟩,codec.1⟩
  · exact ⟨⟨codec.2,⟨⟨z,a⟩,b⟩⟩,codec.1⟩

theorem penultimateCell_physical (divide : Bool) : GatePhysical (PenultimateSwapIdentity.cell divide) := by
  have x : GatePhysical [.X 2409] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  cases divide <;> simp only [PenultimateSwapIdentity.cell,Bool.false_eq_true,if_false,if_true]
  · apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    simpa only [gatePhysical_append] using And.intro (And.intro x fixedInverseField_physical) x
  · apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    simpa only [gatePhysical_append] using And.intro (And.intro x fixedForwardField_physical) x

theorem penultimateReplay_physical (divide : Bool) : GatePhysical (PenultimateMapped.replay divide) := by
  have first := firstMappedGroup_physical divide
  have groups := mappedGroups_physical divide 1 169 (by decide)
  have last := gatePhysical_rename _ allPlaced_injective _ (penultimateCell_physical divide)
  cases divide <;> simp only [PenultimateMapped.replay,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨last,groups⟩,first⟩
  · exact ⟨⟨first,groups⟩,last⟩

theorem fixedCopy_physical : GatePhysical
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a) := by
  apply physicalGateCheck_correct
  decide +kernel

theorem selectedFieldSegment_physical (divide : Bool) : GatePhysical (PenultimateMapped.fieldSegment divide) := by
  have cp := gatePhysical_rename _ allPlaced_injective _ fixedCopy_physical
  have cent := gatePhysical_rename _ allPlaced_injective _ (fixedConverters_physical false)
  have canon := gatePhysical_rename _ allPlaced_injective _ (fixedConverters_physical true)
  have replay := penultimateReplay_physical divide
  have empty : GatePhysical [] := by simp [GatePhysical]
  cases divide <;> simp only [PenultimateMapped.fieldSegment,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨⟨⟨cp,cent⟩,replay⟩,canon⟩,empty⟩
  · exact ⟨⟨⟨⟨empty,cent⟩,replay⟩,canon⟩,cp⟩
end ECDSAAdd.Arithmetic
