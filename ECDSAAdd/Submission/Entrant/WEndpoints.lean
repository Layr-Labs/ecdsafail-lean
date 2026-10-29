import ECDSAAdd.Submission.Entrant.WCompressedCompactRestore
import ECDSAAdd.Arithmetic.CompressedForwardCallerEquality
import ECDSAAdd.Arithmetic.CompressedCompactRestore

/-! The tighter schedule agrees with the original one at stages 0, 1 and 512.
Hence the first tick, the stage-1 and stage-512 invariants, and the complete
terminal State of the compressed forward pass are literally the original
ones; every block outside the integer passes is reused unchanged. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.W
open ECDSAAdd.Arithmetic CompressedFieldSupport
attribute [local irreducible] run wires Arithmetic.compactSkywalkForward compressedCompactForward
  Arithmetic.compressedCompactForward allGroupEncode SkywalkTrace.next Nat.iterate SkywalkIntegerStage

theorem compactSkywalkTick_zero_eq (w : Nat → Wire) :
    compactSkywalkTick w 0=Arithmetic.compactSkywalkTick w 0 := by
  have h1 : compactSkywalkTickPreWidth 0=Arithmetic.compactSkywalkTickPreWidth 0 :=
    narrowSkywalkRouteWidth_endpoints.1
  have h2 : compactSkywalkTickPostWidth 0=Arithmetic.compactSkywalkTickPostWidth 0 :=
    narrowSkywalkRouteWidth_endpoints.2.2.2
  unfold compactSkywalkTick Arithmetic.compactSkywalkTick compactSkywalkTickCleanup
    Arithmetic.compactSkywalkTickCleanup compactSkywalkTickARelease
    Arithmetic.compactSkywalkTickARelease compactSkywalkTickBRelease
    Arithmetic.compactSkywalkTickBRelease compactSkywalkTickLayout Arithmetic.compactSkywalkTickLayout
  rw [h1,h2]

theorem signPool_eq (w : Nat → Wire) (i : Nat)
    (h : narrowSkywalkRouteWidth i=Arithmetic.narrowSkywalkRouteWidth i) :
    compactSkywalkSignPoolA w i=Arithmetic.compactSkywalkSignPoolA w i ∧
    compactSkywalkSignPoolB w i=Arithmetic.compactSkywalkSignPoolB w i := by
  unfold compactSkywalkSignPoolA Arithmetic.compactSkywalkSignPoolA compactSkywalkSignPoolB
    Arithmetic.compactSkywalkSignPoolB
  rw [h]
  exact ⟨rfl,rfl⟩

theorem compactSkywalkStage_eq (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (h : narrowSkywalkRouteWidth i=Arithmetic.narrowSkywalkRouteWidth i) (s : BasisState) :
    CompactSkywalkStage w r i s ↔ Arithmetic.CompactSkywalkStage w r i s := by
  have e := signPool_eq w i h
  unfold CompactSkywalkStage Arithmetic.CompactSkywalkStage compactSkywalkStageVirtual
    Arithmetic.compactSkywalkStageVirtual
  rw [e.1,e.2]

theorem compressedCompactStage_eq (w : Nat → Wire) (x p i : Nat)
    (h : narrowSkywalkRouteWidth i=Arithmetic.narrowSkywalkRouteWidth i) (bits : BasisState) :
    CompressedCompactStage w x p i bits ↔ Arithmetic.CompressedCompactStage w x p i bits := by
  unfold CompressedCompactStage Arithmetic.CompressedCompactStage
  simp only [compactSkywalkStage_eq w _ i h]

theorem compactSkywalkStage_one (w : Nat → Wire) (r : SkywalkRails.State) (s : BasisState) :
    CompactSkywalkStage w r 1 s ↔ Arithmetic.CompactSkywalkStage w r 1 s :=
  compactSkywalkStage_eq w r 1 narrowSkywalkRouteWidth_endpoints.2.1 s

theorem compressedCompactStage_512 (w : Nat → Wire) (x p : Nat) (bits : BasisState) :
    CompressedCompactStage w x p 512 bits ↔ Arithmetic.CompressedCompactStage w x p 512 bits :=
  compressedCompactStage_eq w x p 512 narrowSkywalkRouteWidth_endpoints.2.2.1 bits

/-- The narrowed compressed forward pass ends in exactly the original terminal
State, for the original seed domain and arbitrary independent record lists. -/
theorem compressedCompactForward_old_eq (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (hlo : CompressedHistoryAbove w)
    (x p : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p)
    (s : State) (mNew mOld : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 0 s.basis) :
    run (compressedCompactForward w 0 512) mNew s=
      run (Arithmetic.compressedCompactForward w 0 512) mOld s := by
  have pool := skywalkShared_integer_nodup w hn
  have old := Arithmetic.compressedCompactForward_caller_eq w hn hlo x p hp0 hx0 hpo hp hx hc
    s mOld [] hin
  rw [old]
  have compressed := compressedCompactForward_512_spec w pool hlo x p hp0 hx0 hpo hp hx hc s mNew hin
  have compact := Arithmetic.compactSkywalkForward_512 w pool x p hp0 hx0 hpo hp hx hc s [] hin
  generalize eCompressed : run (compressedCompactForward w 0 512) mNew s=compressedState at compressed ⊢
  generalize eCompact : run (Arithmetic.compactSkywalkForward w 0 512) [] s=compactState at compact ⊢
  obtain ⟨ghost,ghostStage,_,ghostPhase,encoded⟩ :=
    compressed_terminal_encoded_state w pool hlo x p hp0 hpo compressedState
      ((compressedCompactStage_512 w x p _).mp compressed.2)
  have ghostTerminal := (Arithmetic.compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc
    ghost.basis ghostStage).2
  have compactTerminal := (Arithmetic.compactSkywalkStage_terminal w pool x p hp0 hx0 hpo hp hx hc
    compactState.basis compact.2).2
  have phase : ghost.phase=compactState.phase :=
    ghostPhase.trans (compressed.1.trans compact.1.symm)
  have bits : ∀q∈(skywalkPoolWires w).toFinset,ghost.basis q=compactState.basis q := by
    intro q hq
    exact skywalkIntegerStage_agrees w (SkywalkRails.encode false false (x:Int) (p:Int))
      512 (by decide) ghost.basis compactState.basis ghostTerminal compactTerminal q
      (List.mem_toFinset.mp hq)
  have support := Arithmetic.allGroupEncode_pool_support w pool hlo
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
      have compactFrame := Arithmetic.compactSkywalkForward_frame w pool 0 512 (by decide) s [] q hq
      have encoderFrame := run_preserves_outside (allGroupEncode w 170) [] compactState q
        (fun h => hq (List.mem_toFinset.mp (support h)))
      rw [eCompressed] at forwardFrame
      rw [eCompact] at compactFrame
      rw [eEncoded] at encoderFrame
      exact forwardFrame.trans (encoderFrame.trans compactFrame).symm

end ECDSAAdd.Entrant.W
