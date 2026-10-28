import ECDSAAdd.Arithmetic.TerminalMappedReplayCore
import ECDSAAdd.Arithmetic.TerminalMappedReplayTrim
import ECDSAAdd.Arithmetic.MappedCompressedReplayFrame
import ECDSAAdd.Arithmetic.MappedCompressedEncodedFrameLayout

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run logicalCell mappedGroups baseGroups measurementCount
  mixedTranscriptTape mixedTranscriptUnitTrace packetLetters tapeLetter

def baseTrimReplay (divide : Bool) : Program :=
  if divide then baseGroups divide 0 170++renameProgram base (logicalCell divide 510)
  else renameProgram base (logicalCell divide 510)++baseGroups divide 0 170

private theorem reference_packet (divide : Bool) (j : Nat) (hj : j<170)
    (tail : List MixedTranscriptLetter) :
    referenceGroups divide (3*j) (packetLetters j++tail)=
      if divide then baseGroup divide j++referenceGroups divide (3*j+3) tail
      else referenceGroups divide (3*j+3) tail++baseGroup divide j := by
  rw [baseGroup_eq_reference divide j hj]
  cases divide <;> simp only [packetLetters,referenceGroups,Bool.false_eq_true,if_false,if_true,
    List.cons_append,List.nil_append,codecGroupForward,codecGroupBackward,
    List.append_nil,List.append_assoc]

private theorem baseTrim_reference (divide : Bool) (j n : Nat) (h : j+n=170) :
    (if divide then baseGroups divide j n++renameProgram base (logicalCell divide 510)
     else renameProgram base (logicalCell divide 510)++baseGroups divide j n)=
      referenceGroups divide (3*j) (indexedLetters (3*j) (3*n+1)) := by
  induction n generalizing j with
  | zero =>
    have hj : j=170 := by omega
    subst j
    have cell := referenceCell_letter divide 510 (by decide)
    have letters : indexedLetters 510 1=[tapeLetter 510] := by rfl
    cases divide <;> simp only [baseGroups,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,
      List.nil_append,List.append_nil,Bool.false_eq_true,if_false,if_true,letters,
      referenceGroups,codecGroupForward,codecGroupBackward,cell]
  | succ n ih =>
    have rest := ih (j+1) (by omega)
    have packet : indexedLetters (3*j) 3=packetLetters j := by
      simp [indexedLetters,packetLetters,tapeLetter,List.range_succ_eq_map]
    have split : indexedLetters (3*j) (3*(n+1)+1)=
        packetLetters j++indexedLetters (3*(j+1)) (3*n+1) := by
      rw [show 3*(n+1)+1=3+(3*n+1) by omega,indexedLetters_append,packet]
      rw [show 3*j+3=3*(j+1) by omega]
    rw [split,reference_packet divide j (by omega),show 3*j+3=3*(j+1) by omega]
    cases divide <;> simp only [baseGroups,Bool.false_eq_true,if_false,if_true] at rest ⊢
    all_goals rw [←rest]; simp only [List.append_assoc]

theorem baseTrimReplay_reference (divide : Bool) :
    baseTrimReplay divide=referenceGroups divide 0 trimLetters := by
  simpa only [baseTrimReplay,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,Nat.reduceAdd,trimLetters]
    using baseTrim_reference divide 0 170 (by decide)

private theorem indexed_prefix (w : Nat → Wire) (ls tail : List MixedTranscriptLetter)
    (i : Nat) (h : IndexedLetters w i (ls++tail)) : IndexedLetters w i ls := by
  induction ls generalizing i with
  | nil => trivial
  | cons l ls ih => exact ⟨h.1,ih (i+1) h.2⟩

theorem trimLetters_indexed : IndexedLetters base 0 trimLetters := by
  have h := mixedTape_indexed base
  rw [←trimLetters_last] at h
  exact indexed_prefix base trimLetters [tapeLetter 511] 0 h

theorem trimLetters_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) trimLetters := by
  intro l hl
  apply hf
  rw [←trimLetters_last]
  exact List.mem_append_left _ hl

/-- Raw residual510 has its original scalar and complete encoded frame under
all independent records. The allocation switch follows derived zero regions. -/
theorem trimCell_step (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (renameProgram allPlaced (logicalCell divide 510)) m s=
      run (renameProgram base (logicalCell divide 510)) m s ∧
    (run (renameProgram allPlaced (logicalCell divide 510)) m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (X,Y)).2
      (run (renameProgram allPlaced (logicalCell divide 510)) m s) := by
  have aligned : IndexedLetters base 510 [tapeLetter 510] := by
    simp only [tapeLetter,mixedTape_base_getD 510 (by decide),IndexedLetters]
    exact ⟨trivial,trivial⟩
  have layout : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) [tapeLetter 510] := by
    intro l hl
    have eq : l=tapeLetter 510 := by simpa using hl
    subst l
    simpa only [tapeLetter] using mixedTape_getD_layout base _ _ _ hf 510 (by decide)
  have ref := encoded_tail_replay (!divide) base _ _ _ hn hlo ho hp 510 [tapeLetter 510]
    (by omega) (by simp) aligned layout origin hg0 hs0 env legal X Y s m input
  have selectedProgram : directionalReplay (!divide) base (base 2400) (base 2409) (base 2410) [tapeLetter 510]=
      renameProgram base (logicalCell divide 510) := by
    rw [←referenceCell_letter divide 510 (by decide)]
    cases divide <;> simp only [directionalReplay,referenceCell,OffsetBorrowedCanonical.replay,
      OffsetBorrowedInverseCanonical.replay,Bool.not_true,Bool.not_false,Bool.false_eq_true,
      if_false,if_true,List.append_nil,List.nil_append]
  rw [selectedProgram] at ref
  have hin := encoded_zero_region base _ hn hlo origin env X Y s input
  have hout := encoded_zero_region base _ hn hlo origin env _ _ _ ref.2
  have pin := shifted_zero_boundary pi0 pi0_outside s hin
  have pout := shifted_zero_boundary pi0 pi0_outside _ hout
  have rename : renameProgram allPlaced (logicalCell divide 510)=
      renameProgram (shifted pi0) (renameProgram base (logicalCell divide 510)) := by
    rw [renameProgram_comp]
    congr 1
  have eq : run (renameProgram allPlaced (logicalCell divide 510)) m s=
      run (renameProgram base (logicalCell divide 510)) m s := by
    apply pullState_perm_injective (shifted pi0)
    rw [rename,run_rename _ (shifted pi0).injective,pin,pout]
  exact ⟨eq,by rw [eq]; exact ref⟩

theorem trimReplay_reference (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (trimReplay divide) m s=run (baseTrimReplay divide) m s := by
  cases divide
  · let first := renameProgram allPlaced (logicalCell false 510)
    let t := run first (m.take (measurementCount first)) s
    have tail := trimCell_step false hn hlo ho hp hf origin hg0 hs0 env legal X Y
      s (m.take (measurementCount first)) input
    generalize hQ : directionalPayload (!false)
      (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (X,Y)=Q at tail
    have groups := mappedGroups_frame false 0 170 (by decide) hn hlo ho hp (packet_layouts _ _ _ hf)
      origin hg0 hs0 env legal Q.1 Q.2 t (m.drop (measurementCount first)) tail.2.2
    have counts : measurementCount (renameProgram base (logicalCell false 510))=measurementCount first :=
      (renameProgram_counts base _).2.trans (renameProgram_counts allPlaced _).2.symm
    simpa only [trimReplay,baseTrimReplay,Bool.false_eq_true,if_false] using
      run_append_agreement first _ (mappedGroups false 0 170) (baseGroups false 0 170)
        s m counts tail.1 groups.1
  · let first := mappedGroups true 0 170
    let t := run first (m.take (measurementCount first)) s
    have groups := mappedGroups_frame true 0 170 (by decide) hn hlo ho hp (packet_layouts _ _ _ hf)
      origin hg0 hs0 env legal X Y s (m.take (measurementCount first)) input
    generalize hQ : groupsPayload true origin 0 170 (X,Y)=Q at groups
    have tail := trimCell_step true hn hlo ho hp hf origin hg0 hs0 env legal Q.1 Q.2
      t (m.drop (measurementCount first)) groups.2.2
    have counts : measurementCount (baseGroups true 0 170)=measurementCount first :=
      (baseGroups_counts true 0 170).2.trans (mappedGroups_counts true 0 170).2.symm
    simpa only [trimReplay,baseTrimReplay,if_true] using
      run_append_agreement first (baseGroups true 0 170) _ _ s m counts groups.1 tail.1

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimCell_step
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimReplay_reference
