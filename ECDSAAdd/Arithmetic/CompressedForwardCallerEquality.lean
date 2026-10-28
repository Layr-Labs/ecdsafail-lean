import ECDSAAdd.Arithmetic.CompressedTerminalEncodingBridge
import ECDSAAdd.Arithmetic.CompactSkywalkForwardFrame
import ECDSAAdd.Arithmetic.CompactSkywalkStageTerminal
import ECDSAAdd.Arithmetic.CompressedCompactFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open CompressedFieldSupport
attribute [local irreducible] run wires compactSkywalkForward compressedCompactForward allGroupEncode
attribute [local irreducible] SkywalkTrace.next Nat.iterate SkywalkIntegerStage

/-- Support of the actual full encoder stays inside the original integer
pool, including every measurement-correction site. -/
theorem allGroupEncode_pool_support (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hlo : CompressedHistoryAbove w) :
    wires (allGroupEncode w 170)⊆(skywalkPoolWires w).toFinset := by
  have history := compressedPrefix_history_support w hn hlo 512 (by decide)
  rw [encode_prefix_512] at history
  intro q hq
  have member := List.mem_toFinset.mp (history hq)
  simp only [List.mem_append,wireBlock] at member
  rcases member with member|member
  all_goals
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1] at hi ⊢
    exact ⟨i,by omega,rfl⟩

/-- The actual compressed forward emitter is exactly full encoding of the
actual compact terminal State. The original seed domain, full512 rounds,
incoming phase, and arbitrary independent record lists are retained. -/
theorem compressedCompactForward_caller_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (s : State) (mNew mRaw : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    run (compressedCompactForward w 0 512) mNew s=
      run (allGroupEncode w 170) [] (run (compactSkywalkForward w 0 512) mRaw s) := by
  have pool := skywalkShared_integer_nodup w hn
  have compressed := compressedCompactForward_512_spec w pool hlo x p hp0 hx0 hpo hp hx hc s mNew hin
  have compact := compactSkywalkForward_512 w pool x p hp0 hx0 hpo hp hx hc s mRaw hin
  generalize eCompressed : run (compressedCompactForward w 0 512) mNew s=compressedState at compressed ⊢
  generalize eCompact : run (compactSkywalkForward w 0 512) mRaw s=compactState at compact ⊢
  obtain ⟨ghost,ghostStage,legal,ghostPhase,encoded⟩ :=
    compressed_terminal_encoded_state w pool hlo x p hp0 hpo compressedState compressed.2
  have ghostTerminal := (compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc
    ghost.basis ghostStage).2
  have compactTerminal := (compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc
    compactState.basis compact.2).2
  have phase : ghost.phase=compactState.phase :=
    ghostPhase.trans (compressed.1.trans compact.1.symm)
  have bits : ∀q∈(skywalkPoolWires w).toFinset,ghost.basis q=compactState.basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w (SkywalkRails.encode false false (x:Int) (p:Int))
      512 (by decide) ghost.basis compactState.basis ghostTerminal compactTerminal q
      (List.mem_toFinset.mp hq)
  have support := allGroupEncode_pool_support w pool hlo
  have agreement := pool_run_agrees (allGroupEncode w 170) (skywalkPoolWires w).toFinset
    support [] ghost compactState phase bits
  generalize eEncoded : run (allGroupEncode w 170) [] compactState=encodedState at agreement ⊢
  apply State.extensionality compressedState encodedState
  · rw [encoded]
    exact agreement.1
  · funext q
    by_cases hq : q∈skywalkPoolWires w
    · rw [encoded]
      exact agreement.2 q (List.mem_toFinset.mpr hq)
    · have forwardFrame := compressedCompactForward_frame w pool hlo 0 512 (by decide) s mNew q hq
      have compactFrame := compactSkywalkForward_frame w pool 0 512 (by decide) s mRaw q hq
      have encoderFrame := run_preserves_outside (allGroupEncode w 170) [] compactState q
        (fun h => hq (List.mem_toFinset.mp (support h)))
      rw [eCompressed] at forwardFrame
      rw [eCompact] at compactFrame
      rw [eEncoded] at encoderFrame
      exact forwardFrame.trans (encoderFrame.trans compactFrame).symm

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.allGroupEncode_pool_support
#print axioms ECDSAAdd.Arithmetic.compressedCompactForward_caller_eq
