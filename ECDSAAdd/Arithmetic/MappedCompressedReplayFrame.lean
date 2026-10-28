import ECDSAAdd.Arithmetic.MappedCompressedGroupsFrame
import ECDSAAdd.Arithmetic.MappedCompressedTailFrame
import ECDSAAdd.Arithmetic.MappedCompressedReplayIdentity
import ECDSAAdd.Framework.RunAppendAgreement
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport CompressedAllocation
attribute [local irreducible] run mappedGroups baseGroups tailProgram baseTail measurementCount
  mixedTranscriptTape mixedTranscriptUnitTrace packetLetters tailLetters

theorem mappedReplay_join (divide : Bool) : mappedReplay divide=
    (if divide then mappedGroups divide 0 170++tailProgram divide
     else tailProgram divide++mappedGroups divide 0 170) := by
  cases divide <;> simp only [mappedReplay,tailProgram,Bool.false_eq_true,if_false,if_true,List.append_assoc]

private theorem tail_complete (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) tailLetters)
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (tailProgram divide) m s=run (baseTail divide) m s ∧
    (run (tailProgram divide) m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)).2
      (run (tailProgram divide) m s) := by
  have out := tailProgram_encoded_step divide hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input
  have zeroIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have zeroOut := encoded_zero_region base (base 2409) hn hlo origin env _ _
    (run (tailProgram divide) m s) out.2
  have pin := shifted_zero_boundary pi0 pi0_outside s zeroIn
  have pout := shifted_zero_boundary pi0 pi0_outside (run (tailProgram divide) m s) zeroOut
  have eq := tailProgram_run divide s m
  rw [pin,pout] at eq
  exact ⟨eq,out⟩

/-- Every actual mapped cell, including the residual raw pair, agrees as a
complete State with the original exact full encoded reference replay. -/
theorem mappedReplay_reference (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : ∀k,k < 170 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters k))
    (ht : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) tailLetters)
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (mappedReplay divide) m s=run
      (if divide then compressedFieldForwardGroups base (base 2400) (base 2409) (base 2410)
       else compressedFieldBackwardGroups base (base 2400) (base 2409) (base 2410)) m s := by
  cases divide
  · let first := tailProgram false
    let t := run first (m.take (measurementCount first)) s
    have tail := tail_complete false hn hlo ho hp ht origin hg0 hs0 env legal X Y
      s (m.take (measurementCount first)) input
    simp only [Bool.not_false] at tail
    generalize hQ : directionalPayload true (mixedTranscriptControls origin (base 2400) tailLetters) (X,Y)=Q at tail
    have groups := mappedGroups_frame false 0 170 (by decide) hn hlo ho hp hf origin hg0 hs0 env legal
      Q.1 Q.2 t (m.drop (measurementCount first)) tail.2.2
    have countEq : measurementCount (baseTail false)=measurementCount first := by
      change measurementCount (baseTail false)=measurementCount (tailProgram false)
      rw [tailProgram_eq_rename]
      exact (renameProgram_counts (shifted pi0) (baseTail false)).2.symm
    rw [mappedReplay_join]
    simp only [Bool.false_eq_true,if_false]
    rw [←base_backward_replay_identity]
    exact run_append_agreement first (baseTail false) (mappedGroups false 0 170)
      (baseGroups false 0 170) s m countEq tail.1 groups.1
  · let first := mappedGroups true 0 170
    let t := run first (m.take (measurementCount first)) s
    have groups := mappedGroups_frame true 0 170 (by decide) hn hlo ho hp hf origin hg0 hs0 env legal
      X Y s (m.take (measurementCount first)) input
    generalize hQ : groupsPayload true origin 0 170 (X,Y)=Q at groups
    have tail := tail_complete true hn hlo ho hp ht origin hg0 hs0 env legal Q.1 Q.2
      t (m.drop (measurementCount first)) groups.2.2
    have countEq : measurementCount (baseGroups true 0 170)=measurementCount first :=
      (baseGroups_counts true 0 170).2.trans (mappedGroups_counts true 0 170).2.symm
    rw [mappedReplay_join]
    simp only [if_true]
    rw [←base_forward_replay_identity]
    exact run_append_agreement first (baseGroups true 0 170) (tailProgram true)
      (baseTail true) s m countEq groups.1 tail.1

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedReplay_reference
