import ECDSAAdd.Arithmetic.MappedCompressedPacketCorrect
import ECDSAAdd.Arithmetic.MappedCompressedCleanTransport
import ECDSAAdd.Arithmetic.MappedCompressedBaseReplay
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run directionalReplay OffsetBorrowedCanonical.cell
  OffsetBorrowedInverseCanonical.cell logicalCell

def tailLetters : List MixedTranscriptLetter :=
  [(mixedTranscriptTape base).getD 510 ((0,0),(false,false)),
   (mixedTranscriptTape base).getD 511 ((0,0),(false,false))]

/-- The actual two raw residual cells, in ascending forward order and
independently measured descending inverse order. -/
def tailProgram (divide : Bool) : Program :=
  if divide then renameProgram allPlaced (logicalCell divide 510)++
      renameProgram allPlaced (logicalCell divide 511)
  else renameProgram allPlaced (logicalCell divide 511)++
      renameProgram allPlaced (logicalCell divide 510)

theorem tailLetters_indexed : IndexedLetters base 510 tailLetters := by
  rw [tailLetters,mixedTape_base_getD 510 (by decide),mixedTape_base_getD 511 (by decide)]
  simp [IndexedLetters]

/-- Keep the tape indices symbolic while the kernel checks the replay identity. -/
private theorem two_cells_eq_replay (divide : Bool) (i j : Nat)
    (hi : i < 512) (hj : j < 512) :
    (if divide then renameProgram base (logicalCell divide i) ++
        renameProgram base (logicalCell divide j)
      else renameProgram base (logicalCell divide j) ++
        renameProgram base (logicalCell divide i)) =
    directionalReplay (!divide) base (base 2400) (base 2409) (base 2410)
      [(mixedTranscriptTape base).getD i ((0,0),(false,false)),
       (mixedTranscriptTape base).getD j ((0,0),(false,false))] := by
  have a := mixedTape_base_getD i hi
  have b := mixedTape_base_getD j hj
  cases divide <;> simp only [a,b,base_cell_eq,directionalReplay,
    OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
    List.append_nil,List.nil_append]

theorem baseTail_eq_replay (divide : Bool) :
    baseTail divide=directionalReplay (!divide) base (base 2400) (base 2409) (base 2410) tailLetters := by
  exact two_cells_eq_replay divide 510 511 (by decide) (by decide)

private theorem shifted_all_cell (divide : Bool) (i : Nat) :
    renameProgram (shifted pi0) (renameProgram base (logicalCell divide i))=
      renameProgram allPlaced (logicalCell divide i) := by
  rw [renameProgram_comp]
  have eq : shifted pi0 ∘ base=allPlaced := by
    funext q
    exact shifted_base pi0 q
  rw [eq]

theorem tailProgram_eq_rename (divide : Bool) :
    tailProgram divide=renameProgram (shifted pi0) (baseTail divide) := by
  cases divide <;> simp only [tailProgram,baseTail,Bool.false_eq_true,if_false,if_true,
    FieldRename.rename_append,shifted_all_cell]

theorem tailProgram_run (divide : Bool) (s : State) (m : List Bool) :
    pullState (shifted pi0) (run (tailProgram divide) m s)=
      run (baseTail divide) m (pullState (shifted pi0) s) := by
  rw [tailProgram_eq_rename]
  exact run_rename _ (shifted pi0).injective _ m s

/-- Complete-State transport follows from the same derived clean boundary
as the packet placement, while all170 earlier groups remain encoded. -/
theorem tailProgram_state_eq (divide : Bool) (s : State) (m : List Bool)
    (hin : ∀q,zeroRegion q → s.basis (base q)=false)
    (hout : ∀q,zeroRegion q → (run (baseTail divide) m s).basis (base q)=false) :
    run (tailProgram divide) m s=run (baseTail divide) m s := by
  have input := shifted_zero_boundary pi0 pi0_outside s hin
  have output := shifted_zero_boundary pi0 pi0_outside (run (baseTail divide) m s) hout
  apply pullState_perm_injective (shifted pi0)
  rw [tailProgram_run,input,output]

/-- Both last raw letters implement their exact original field update for
every independent measurement record, retaining the complete encoded frame. -/
theorem tailProgram_encoded_step (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) tailLetters)
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (tailProgram divide) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)).2 out := by
  have reference := encoded_tail_replay (!divide) base (base 2400) (base 2409) (base 2410)
    hn hlo ho hp 510 tailLetters (by omega) (by simp [tailLetters]) tailLetters_indexed
    hf origin hg0 hs0 env legal X Y s m input
  rw [←baseTail_eq_replay divide] at reference
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env _ _
    (run (baseTail divide) m s) reference.2
  have same := tailProgram_state_eq divide s m cleanIn cleanOut
  change (run (tailProgram divide) m s).phase=s.phase ∧ _
  rw [same]
  exact reference

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.baseTail_eq_replay
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.tailProgram_state_eq
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.tailProgram_encoded_step
