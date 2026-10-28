import ECDSAAdd.Arithmetic.MappedCompressedCanonicalFrame
import ECDSAAdd.Arithmetic.MappedCompressedEndpointEncodingSupport
import ECDSAAdd.Arithmetic.MappedCompressedCleanTransport
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires allGroupEncode dblInPlace halfInPlace copyRegister

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

private theorem encoded_endpoint (P : Program)
    (dis : Disjoint (wires (allGroupEncode base 170)) (wires P))
    (origin : BasisState) (X Y A B : Fp)
    (correct : Triple (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
        origin X.val Y.val) P
      (PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin A.val B.val))
    (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    (run P m s).phase=s.phase ∧ EncodedCanonicalFrame origin A B (run P m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have result := correct raw m frame
  have read : ∀q∈wires P,s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment P s raw m read).1
  rw [result.1,Bool.xor_self] at increment
  have actualPhase := xor_neutral _ _ increment
  have actual : run P m s=run (allGroupEncode base 170) [] (run P m raw) := by
    rw [encoded]
    exact (run_disjoint_commute _ _ dis [] m raw).symm
  exact ⟨actualPhase,run P m raw,result.1.trans (phase.trans actualPhase.symm),result.2,actual⟩

/-- Actual base unary emission preserves the entire encoded canonical
frame for all field inputs and independent measurement records. -/
theorem encoded_unary_step (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    let P := if divide then dblInPlace (borrowedSkywalkUnary base) p
      else halfInPlace (borrowedSkywalkUnary base) p
    (run P m s).phase=s.phase ∧
      EncodedCanonicalFrame origin (if divide then 2*X else X/2) Y (run P m s) := by
  cases divide
  · exact encoded_endpoint _ (encoder_unary_disjoint false) origin X Y (X/2) Y
      (borrowedSkywalkUnary_half_frame base hn origin hw hu X Y) s m input
  · exact encoded_endpoint _ (encoder_unary_disjoint true) origin X Y (2*X) Y
      (borrowedSkywalkUnary_double_frame base hn origin hw hu X Y) s m input

private theorem placed_endpoint_state_eq (P : Program) (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀q,zeroRegion q → (run P m s).basis (base q)=false) :
    run (renameProgram (shifted pi0) P) m s=run P m s := by
  have input := shifted_zero_boundary pi0 pi0_outside s hin
  have output := shifted_zero_boundary pi0 pi0_outside (run P m s) hout
  have same := run_rename (shifted pi0) (shifted pi0).injective P m s
  rw [input] at same
  apply pullState_perm_injective (shifted pi0)
  exact same.trans output.symm

theorem mapped_unary_state_eq (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    run (renameProgram allPlaced (if divide then dblInPlace (borrowedSkywalkUnary id) p
        else halfInPlace (borrowedSkywalkUnary id) p)) m s=
      run (if divide then dblInPlace (borrowedSkywalkUnary base) p
        else halfInPlace (borrowedSkywalkUnary base) p) m s := by
  let P := if divide then dblInPlace (borrowedSkywalkUnary base) p
    else halfInPlace (borrowedSkywalkUnary base) p
  have reference := encoded_unary_step divide hn origin hw hu X Y s m input
  have cleanIn := encoded_canonical_zero_region hn hlo origin hw hu X Y s input
  have cleanOut := encoded_canonical_zero_region hn hlo origin hw hu _ Y (run P m s) reference.2
  have same := placed_endpoint_state_eq P s m cleanIn cleanOut
  cases divide
  · simp only [Bool.false_eq_true,if_false]
    rw [allPlaced_half_natural]
    exact same
  · simp only [if_true]
    rw [allPlaced_dbl_natural]
    exact same

/-- Physical low-width unary endpoint, with both placement boundaries
derived from the encoded frame instead of a new clean-bank premise. -/
theorem mapped_unary_step (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : CompressedHistoryAbove base) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    let P := renameProgram allPlaced (if divide then dblInPlace (borrowedSkywalkUnary id) p
      else halfInPlace (borrowedSkywalkUnary id) p)
    (run P m s).phase=s.phase ∧
      EncodedCanonicalFrame origin (if divide then 2*X else X/2) Y (run P m s) := by
  have same := mapped_unary_state_eq divide hn hlo origin hw hu X Y s m input
  dsimp only
  rw [same]
  exact encoded_unary_step divide hn origin hw hu X Y s m input

/-- Populate the original full source port, preserving all encoded history. -/
theorem encoded_copy_fill (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (X : Fp) (s : State) (m : List Bool)
    (input : EncodedCanonicalFrame origin X 0 s) :
    (run (copyPairAt base) m s).phase=s.phase ∧
      EncodedCanonicalFrame origin X X (run (copyPairAt base) m s) := by
  apply encoded_endpoint _ encoder_copy_disjoint origin X 0 X X _ s m input
  simpa only [ZMod.val_zero] using copyPair_fill hn origin X

/-- The equal retained source port is cleared by the actual XOR copy. -/
theorem encoded_copy_clear (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (X : Fp) (s : State) (m : List Bool)
    (input : EncodedCanonicalFrame origin X X s) :
    (run (copyPairAt base) m s).phase=s.phase ∧
      EncodedCanonicalFrame origin X 0 (run (copyPairAt base) m s) := by
  apply encoded_endpoint _ encoder_copy_disjoint origin X X X 0 _ s m input
  simpa only [ZMod.val_zero] using copyPair_clear hn origin X

theorem mapped_copy_fill (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (X : Fp) (s : State) (m : List Bool)
    (input : EncodedCanonicalFrame origin X 0 s) :
    (run (renameProgram allPlaced (copyPairAt id)) m s).phase=s.phase ∧
      EncodedCanonicalFrame origin X X (run (renameProgram allPlaced (copyPairAt id)) m s) := by
  rw [copyPair_placement]
  exact encoded_copy_fill hn origin X s m input

theorem mapped_copy_clear (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (X : Fp) (s : State) (m : List Bool)
    (input : EncodedCanonicalFrame origin X X s) :
    (run (renameProgram allPlaced (copyPairAt id)) m s).phase=s.phase ∧
      EncodedCanonicalFrame origin X 0 (run (renameProgram allPlaced (copyPairAt id)) m s) := by
  rw [copyPair_placement]
  exact encoded_copy_clear hn origin X s m input

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.encoded_unary_step
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mapped_unary_state_eq
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mapped_unary_step
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mapped_copy_fill
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mapped_copy_clear
