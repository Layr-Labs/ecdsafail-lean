import ECDSAAdd.Arithmetic.CompressedFieldGroupedReplay
import ECDSAAdd.Arithmetic.TerminalMappedReplayPayload
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Arithmetic.CompressedFieldSupport
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run
private theorem short_programs (w : Nat → Wire) (b sign eff : Wire) (i : Nat)
    (ls : List MixedTranscriptLetter) (h : ls.length ≤ 2) :
    codecGroupForward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) i ls =
      directionalReplay false w b sign eff ls ∧
    codecGroupBackward w (fun l : MixedTranscriptLetter =>
      OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) i ls =
      directionalReplay true w b sign eff ls := by
  cases ls with
  | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
      OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
  | cons a ls =>
    cases ls with
    | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
        OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
    | cons c ls =>
      cases ls with
      | nil => simp [codecGroupForward,codecGroupBackward,directionalReplay,
          OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay]
      | cons d tail => simp at h; omega
private theorem split_programs {α : Type} (w : Nat → Wire) (cell : α → Program)
    (i : Nat) (a c d : α) (tail : List α) :
    codecGroupForward w cell i (a::c::d::tail) =
      codecGroupForward w cell i [a,c,d]++codecGroupForward w cell (i+3) tail ∧
    codecGroupBackward w cell i (a::c::d::tail) =
      codecGroupBackward w cell (i+3) tail++codecGroupBackward w cell i [a,c,d] := by
  simp only [codecGroupForward,codecGroupBackward,List.append_nil,List.nil_append,List.append_assoc]
  constructor <;> trivial
/-- Existing packet proof, with its universally framed raw tail instantiated
at one residual letter instead of two. No arithmetic primitive is changed. -/
theorem trim_grouped_encoded_replays (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (ho : ∀ q ∈ [b,sign,eff],q ∉ skywalkSharedWires w)
    (hp : ∀ q ∈ [b,sign,eff],q ∉ skywalkPoolWires w)
    (base : BasisState) (hg0 : base sign = false) (he0 : base eff = false)
    (env : Env w base) (legal : RawGroupLegal w 170 base)
    (n j : Nat) (remaining : j+n=170) (ls : List MixedTranscriptLetter)
    (length : ls.length=3*n+1) (aligned : IndexedLetters w (3*j) ls)
    (hf : MixedTranscriptReplayLayout w b sign eff ls) :
    (∀ (X Y : Fp) (s : State) (m : List Bool), EncodedFieldFrame w sign base X Y s →
      let out := run (codecGroupForward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) ls) m s
      out.phase=s.phase ∧ EncodedFieldFrame w sign base
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2 out) ∧
    (∀ (X Y : Fp) (s : State) (m : List Bool), EncodedFieldFrame w sign base X Y s →
      let out := run (codecGroupBackward w (fun l : MixedTranscriptLetter =>
        OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) ls) m s
      out.phase=s.phase ∧ EncodedFieldFrame w sign base
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).1
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).2 out) := by
  induction n generalizing j ls with
  | zero =>
    have ji : j=170 := by omega
    have len : ls.length=1 := by simpa using length
    have programs := short_programs w b sign eff (3*j) ls (by omega)
    constructor
    · intro X Y s m input
      rw [programs.1]
      simpa only [directionalPayload,Bool.false_eq_true,if_false] using
        encoded_tail_replay false w b sign eff hn hlo ho hp (3*j) ls (by omega)
          (by omega) aligned hf base hg0 he0 env legal X Y s m input
    · intro X Y s m input
      rw [programs.2]
      simpa only [directionalPayload,if_true] using
        encoded_tail_replay true w b sign eff hn hlo ho hp (3*j) ls (by omega)
          (by omega) aligned hf base hg0 he0 env legal X Y s m input
  | succ n ih =>
    cases ls with
    | nil => simp at length
    | cons a rest =>
      cases rest with
      | nil => simp at length
      | cons c rest =>
        cases rest with
        | nil => simp at length
        | cons d tail =>
          have jj : j < 170 := by omega
          have next : IndexedLetters w (3*(j+1)) tail := by
            simpa only [Nat.mul_add,Nat.mul_one] using indexed_three_tail w (3*j) a c d tail aligned
          have lenTail : tail.length=3*n+1 := by simp only [List.length_cons] at length; omega
          have hfTail : MixedTranscriptReplayLayout w b sign eff tail := fun q hq => hf q (by simp [hq])
          have hfPacket : MixedTranscriptReplayLayout w b sign eff [a,c,d] := by
            intro q hq
            exact hf q (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using
              (show q=a ∨ q=c ∨ q=d ∨ q∈tail from by simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto))
          have controls := indexed_packet_controls w j jj (skywalkShared_integer_nodup w hn) hlo a c d tail aligned
          have support := packet_active_support w b sign eff (3*j) [a,c,d] controls
          have tailSpec := ih (j+1) (by omega) tail lenTail next hfTail
          have fwSplit := (split_programs w (fun l : MixedTranscriptLetter =>
            OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) a c d tail).1
          have rvSplit := (split_programs w (fun l : MixedTranscriptLetter =>
            OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) a c d tail).2
          constructor
          · intro X Y s m input
            let packet := codecGroupForward w (fun l : MixedTranscriptLetter =>
              OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j) [a,c,d]
            let t := run packet (m.take (measurementCount packet)) s
            let Q := skywalkPayloadReplay (mixedTranscriptControls base b [a,c,d]) (X,Y)
            have first := encoded_forward_packet_step w b sign eff hn hlo j jj a c d hfPacket ho hp
              base hg0 he0 env legal X Y (by simpa only [rawForwardPacket] using support.1)
              s (m.take (measurementCount packet)) input
            have rest := tailSpec.1 Q.1 Q.2 t (m.drop (measurementCount packet)) first.2
            rw [fwSplit,run_append]
            change (run _ _ t).phase=s.phase ∧ _
            refine ⟨rest.1.trans first.1,?_⟩
            simpa only [mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,Q] using rest.2
          · intro X Y s m input
            let later := codecGroupBackward w (fun l : MixedTranscriptLetter =>
              OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2) (3*j+3) tail
            let t := run later (m.take (measurementCount later)) s
            let Q := skywalkPayloadReplayInverse (mixedTranscriptControls base b tail) (X,Y)
            have rest := tailSpec.2 X Y s (m.take (measurementCount later)) input
            have first := encoded_backward_packet_step w b sign eff hn hlo j jj a c d hfPacket ho hp
              base hg0 he0 env legal Q.1 Q.2 (by simpa only [rawBackwardPacket] using support.2)
              t (m.drop (measurementCount later)) rest.2
            rw [rvSplit,run_append]
            change (run _ _ t).phase=s.phase ∧ _
            refine ⟨first.1.trans rest.1,?_⟩
            simpa only [mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q] using first.2

end ECDSAAdd.Arithmetic.CompressedFieldSupport
#print axioms ECDSAAdd.Arithmetic.CompressedFieldSupport.trim_grouped_encoded_replays
