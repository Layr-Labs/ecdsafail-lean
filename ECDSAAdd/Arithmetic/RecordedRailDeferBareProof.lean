import ECDSAAdd.Arithmetic.RecordedRailDeferProgram

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

/-- Absolute cursor indexing is preserved even for short or empty tapes. -/
theorem drop_head_getD (m : List Bool) (k : Nat) : (m.drop k).headD false=m.getD k false := by
  induction k generalizing m with
  | zero => cases m <;> rfl
  | succ k ih =>
    cases m with
    | nil => simp
    | cons b bs => simpa only [List.drop_succ_cons,List.getD_cons_succ] using ih bs

/-- Actual bare MX produces phase debt from its own old carry and fresh outcome. -/
theorem bare_state (q : Wire) (m : List Bool) (cursor : Nat) (s : State) :
    runWithTape (bareMX q) m cursor s=
      ⟨s.phase ^^ (m.getD cursor false && s.basis q),writeBit s.basis q false⟩ := by
  simp [bareMX,runWithTape,run,measureAndCorrect,ECDSAAdd.correct,drop_head_getD]

/-- The next chunk preserves its incoming boundary, and the following bare MX
then clears exactly that boundary and records its original Boolean phase debt. -/
theorem advance_state (a b bank : List Wire) (incoming cout : Wire)
    (bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : RecordedRailVented.Ready a b (some incoming) bank cout bits) :
    let v := runWithTape (RecordedRailVented.vented a b (some incoming) bank cout) m cursor ⟨phase,bits⟩
    runWithTape (advance a b bank incoming cout) m cursor ⟨phase,bits⟩=
      ⟨phase ^^ (m.getD (cursor+a.length-1) false && bits incoming),writeBit v.basis incoming false⟩ := by
  let v := runWithTape (RecordedRailVented.vented a b (some incoming) bank cout) m cursor ⟨phase,bits⟩
  have h := RecordedRailVented.correct a b (some incoming) bank cout bits phase m cursor ready
  have hp : v.phase=phase := h.1
  have hin : v.basis incoming=bits incoming := h.2.2.2.2.2.1
  have counts := RecordedRailVented.counts a b bank
    (RecordedRailVented.aligned_shape a b bank ready.1) (some incoming) cout
  dsimp only
  rw [advance,runWithTape_append,counts.2]
  change runWithTape (bareMX incoming) m (cursor+(a.length-1)) v=_
  rw [bare_state,hp,hin]
  have positive : 0<a.length := ready.1.1
  have ordinal : cursor+(a.length-1)=cursor+a.length-1 := by omega
  rw [ordinal]

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.drop_head_getD
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.bare_state
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.advance_state
