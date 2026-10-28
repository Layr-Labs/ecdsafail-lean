import ECDSAAdd.Arithmetic.FieldRenameRegisters
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry majority eraseCarry

theorem offset_chain_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (cinC cinB target : Wire) :
    renameProgram f (BalancedCleanupOffset.chain bits xs ys cs ds cinC cinB target) =
      BalancedCleanupOffset.chain (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f cinC) (f cinB) (f target) := by
  induction bits generalizing xs ys cs ds cinC cinB with
  | nil =>
    cases xs <;> cases ys <;> cases cs <;> cases ds <;>
      simp only [BalancedCleanupOffset.chain,List.map_nil,List.map_cons,renameProgram,List.map_nil]
    exact flipBelow_natural f none cinB target
  | cons b bits ih =>
    cases xs with
    | nil => simp [BalancedCleanupOffset.chain,renameProgram]
    | cons a xs =>
      cases ys with
      | nil => simp [BalancedCleanupOffset.chain,renameProgram]
      | cons y ys =>
        cases cs with
        | nil => simp [BalancedCleanupOffset.chain,renameProgram]
        | cons c cs =>
          cases ds with
          | nil => simp [BalancedCleanupOffset.chain,renameProgram]
          | cons d ds =>
            simp only [BalancedCleanupOffset.chain,List.map_cons,rename_append,
              mappedMajority_natural,mappedSum_natural,majority_natural,eraseCarry_natural,
              mappedEraseCarry_natural,ih]
            rfl

theorem prepareSign_natural (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    renameProgram f (BalancedCleanup.prepareSign L)=BalancedCleanup.prepareSign (mapCleanup f L) := by
  simp only [BalancedCleanup.prepareSign,rename_append,signComplement_natural]
  simp only [mapCleanup,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.map_cons,List.map_append]
  rfl

theorem offset_view_natural (f : Wire → Wire) (L : BalancedCleanupOffset.Layout) :
    renameProgram f (BalancedCleanupOffset.view L)=BalancedCleanupOffset.view (mapOffset f L) := by
  simp only [BalancedCleanupOffset.view,rename_append,rotateLeft_natural,signComplement_natural]
  simp only [mapOffset,mapCircuit,mapCleanup,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.map_cons,List.map_append]
  rfl

theorem offset_program_natural (f : Wire → Wire) (L : BalancedCleanupOffset.Layout) :
    renameProgram f (BalancedCleanupOffset.program L)=BalancedCleanupOffset.program (mapOffset f L) := by
  simp only [BalancedCleanupOffset.program,rename_append,rename_reverse,prepareSign_natural,
    offset_view_natural,offset_chain_natural,offsetBits_map]
  simp only [mapOffset,mapCircuit,mapCleanup,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.map_cons,List.map_append]
  rfl

end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.offset_chain_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.offset_program_natural
