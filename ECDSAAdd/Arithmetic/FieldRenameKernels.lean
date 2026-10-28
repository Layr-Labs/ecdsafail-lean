import ECDSAAdd.Arithmetic.FieldRenameOffsetZero
import ECDSAAdd.Arithmetic.FieldRenameMeasuredOffset
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] addInPlace subInPlace mappedAdd mappedSub
  rotateRight rotateLeft signComplement BalancedCircuit.foldBits
  BalancedCircuit.rawSource BalancedCircuit.rawTarget BalancedCircuit.foldTarget

theorem seedViews_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow ≠ []) :
    renameProgram f (BalancedCircuit.seedViews L)=BalancedCircuit.seedViews (mapCircuit f L) := by
  simp only [BalancedCircuit.seedViews,mapCircuit,mapCleanup,first_source_map f L.ylow hy,
    renameProgram,List.map_cons,List.map_nil,renameInstr]

theorem rawAdd_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedCircuit.rawAdd L)=BalancedCircuit.rawAdd (mapCircuit f L) := by
  simp only [BalancedCircuit.rawAdd,rename_append,signComplement_natural,addInPlace_natural,
    rawSource_map,rawTarget_map]
  rfl

theorem prepareFold_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedCircuit.prepareFold L)=BalancedCircuit.prepareFold (mapCircuit f L) := by
  simp only [BalancedCircuit.prepareFold,mapCircuit,mapCleanup,renameProgram,
    List.map_cons,List.map_nil,renameInstr]

theorem fold_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedCircuit.fold L)=BalancedCircuit.fold (mapCircuit f L) := by
  simp only [BalancedCircuit.fold,rename_append,mappedAdd_natural,foldBits_map,foldTarget_map,
    List.map_append,List.map_cons,List.map_nil]
  rfl

theorem releaseSelectors_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedCircuit.releaseSelectors L)=
      BalancedCircuit.releaseSelectors (mapCircuit f L) := by
  simp only [BalancedCircuit.releaseSelectors,mapCircuit,mapCleanup,renameProgram,
    List.map_cons,List.map_nil,renameInstr,renameCorrection]

theorem coreProgram_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow ≠ []) :
    renameProgram f (BalancedCircuit.coreProgram L)=BalancedCircuit.coreProgram (mapCircuit f L) := by
  simp only [BalancedCircuit.coreProgram,rename_append,seedViews_natural f L hy,
    rawAdd_natural,prepareFold_natural,fold_natural,rotateRight_natural,rawTarget_map,
    releaseSelectors_natural]

theorem recoverSelectors_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedInverse.recoverSelectors L)=
      BalancedInverse.recoverSelectors (mapCircuit f L) := by
  simp only [BalancedInverse.recoverSelectors,mapCircuit,mapCleanup,renameProgram,
    List.map_cons,List.map_nil,renameInstr]

theorem undoFold_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedInverse.undoFold L)=BalancedInverse.undoFold (mapCircuit f L) := by
  simp only [BalancedInverse.undoFold,rename_append,mappedSub_natural,foldBits_map,foldTarget_map,
    List.map_append,List.map_cons,List.map_nil]
  rfl

theorem undoPreparation_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedInverse.undoPreparation L)=
      BalancedInverse.undoPreparation (mapCircuit f L) := by
  simp only [BalancedInverse.undoPreparation,mapCircuit,mapCleanup,renameProgram,
    List.map_cons,List.map_nil,renameInstr,renameCorrection]

theorem rawSubtract_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BalancedInverse.rawSubtract L)=BalancedInverse.rawSubtract (mapCircuit f L) := by
  simp only [BalancedInverse.rawSubtract,rename_append,signComplement_natural,subInPlace_natural,
    rawSource_map,rawTarget_map]
  rfl

theorem inverse_tail_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hy : L.ylow ≠ []) :
    renameProgram f (OffsetBorrowedInverse.tail L)=OffsetBorrowedInverse.tail (mapCircuit f L) := by
  simp only [OffsetBorrowedInverse.tail,rename_append,rename_reverse,recoverSelectors_natural,
    rotateLeft_natural,rawTarget_map,undoFold_natural,undoPreparation_natural,rawSubtract_natural,
    seedViews_natural f L hy]

private theorem shared_ylow_nonempty (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).ylow ≠ [] := by
  intro h
  have len := (balancedSharedPorts_widths w sign).2.1
  rw [h] at len
  contradiction

theorem forward_program_natural (f w : Wire → Wire) (sign : Wire) :
    renameProgram f (OffsetBorrowedField.program w sign)=
      OffsetBorrowedField.program (f ∘ w) (f sign) := by
  simp only [OffsetBorrowedField.program,rename_append,
    coreProgram_natural f _ (shared_ylow_nonempty w sign),sharedPorts_map,
    measured_zero_offset_program_natural f _ (OffsetCleanupBorrowedCaller.widths w sign),callerLayout_map]
  rfl

theorem inverse_program_natural (f w : Wire → Wire) (sign : Wire) :
    renameProgram f (OffsetBorrowedInverse.program w sign)=
      OffsetBorrowedInverse.program (f ∘ w) (f sign) := by
  simp only [OffsetBorrowedInverse.program,OffsetBorrowedInverse.recoverParity,rename_append,
    zero_offset_program_natural f _ (OffsetCleanupBorrowedCaller.widths w sign),callerLayout_map,
    inverse_tail_natural f _ (shared_ylow_nonempty w sign),sharedPorts_map]
  rfl

end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.coreProgram_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.inverse_tail_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.forward_program_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.inverse_program_natural
