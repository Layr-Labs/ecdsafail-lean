import ECDSAAdd.Arithmetic.FieldRenameKernels
import ECDSAAdd.Arithmetic.MappedCompressedFieldReplay
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] OffsetBorrowedField.program OffsetBorrowedInverse.program
  swapRegisters transcriptSelectWindow

theorem shared_r_map (f w : Wire → Wire) (sign : Wire) :
    (balancedSharedPorts (f ∘ w) (f sign)).r=(balancedSharedPorts w sign).r.map f := by
  have h := congrArg (fun L : BalancedCircuit.Layout => L.r) (sharedPorts_map f w sign)
  simpa only [mapCircuit,r_map] using h.symm

theorem shared_y_map (f w : Wire → Wire) (sign : Wire) :
    (balancedSharedPorts (f ∘ w) (f sign)).y=(balancedSharedPorts w sign).y.map f := by
  have h := congrArg (fun L : BalancedCircuit.Layout => L.y) (sharedPorts_map f w sign)
  simpa only [mapCircuit,y_map] using h.symm

theorem forward_body_natural (f w : Wire → Wire) (sign effS : Wire) :
    renameProgram f (OffsetBorrowedCanonical.body w sign effS)=
      OffsetBorrowedCanonical.body (f ∘ w) (f sign) (f effS) := by
  simp only [OffsetBorrowedCanonical.body,rename_append,forward_program_natural,
    swapRegisters_natural,shared_r_map,shared_y_map]
  rfl

theorem inverse_double_natural (f w : Wire → Wire) (sign : Wire) :
    renameProgram f (OffsetBorrowedInverseCanonical.double w sign)=
      OffsetBorrowedInverseCanonical.double (f ∘ w) (f sign) := by
  simp only [OffsetBorrowedInverseCanonical.double,rename_append,inverse_program_natural]
  rfl

theorem inverse_body_natural (f w : Wire → Wire) (sign effS : Wire) :
    renameProgram f (OffsetBorrowedInverseCanonical.body w sign effS)=
      OffsetBorrowedInverseCanonical.body (f ∘ w) (f sign) (f effS) := by
  simp only [OffsetBorrowedInverseCanonical.body,rename_append,swapRegisters_natural,
    shared_r_map,shared_y_map,inverse_double_natural]

theorem forward_cell_natural (f w : Wire → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    renameProgram f (OffsetBorrowedCanonical.cell w b g swap sign effS ig is)=
      OffsetBorrowedCanonical.cell (f ∘ w) (f b) (f g) (f swap) (f sign) (f effS) ig is := by
  simp only [OffsetBorrowedCanonical.cell,selectWindow_natural,forward_body_natural]

theorem inverse_cell_natural (f w : Wire → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    renameProgram f (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is)=
      OffsetBorrowedInverseCanonical.cell (f ∘ w) (f b) (f g) (f swap) (f sign) (f effS) ig is := by
  simp only [OffsetBorrowedInverseCanonical.cell,selectWindow_natural,inverse_body_natural]

/-- Structural relabeling of the actual512-round unit-trace emission.
No primitive or measured arithmetic circuit is expanded at this layer. -/
theorem logical_cell_natural (f : Wire → Wire) (divide : Bool) (i : Nat) :
    renameProgram f (MappedCompressed.logicalCell divide i)=
      (if divide then OffsetBorrowedCanonical.cell f (f 2400) (f i) (f (1028+i))
          (f 2409) (f 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2
       else OffsetBorrowedInverseCanonical.cell f (f 2400) (f i) (f (1028+i))
          (f 2409) (f 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2) := by
  cases divide <;> simp only [MappedCompressed.logicalCell,Bool.false_eq_true,if_false,if_true,
    forward_cell_natural,inverse_cell_natural,Function.comp_id]

end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.forward_cell_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.inverse_cell_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.logical_cell_natural
