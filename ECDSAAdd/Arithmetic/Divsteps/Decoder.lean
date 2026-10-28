import ECDSAAdd.Framework.Cost
import Mathlib.Tactic
import ECDSAAdd.Math.Divsteps.Recovery

namespace ECDSAAdd.Arithmetic.Divsteps

/-- A flag-controlled two-bit decoder. At ladder depth two the inputs
are the updated `gv[1]` and `fv[3]`; reachability supplies that identity.
The circuit itself works for every basis state and every measurement record. -/
def decode2 (flag a b output : Wire) : Program :=
  [.CCX flag a output, .CCX flag b output]

/-- Exact action, including arbitrary incoming output and phase. -/
theorem decode2_run (flag a b output : Wire)
    (hf : flag ≠ output) (_ha : a ≠ output) (hb : b ≠ output)
    (s : State) (m : List Bool) :
    run (decode2 flag a b output) m s =
      ⟨s.phase, writeBit s.basis output
        (s.basis output ^^ (s.basis flag && (s.basis a ^^ s.basis b)))⟩ := by
  cases hflag : s.basis flag <;> cases hleft : s.basis a <;> cases hright : s.basis b <;>
    cases hout : s.basis output <;>
    simp [decode2, run, writeBit, Function.update, hf, hb, hflag, hleft, hright, hout]

/-- At a reachable depth-two negative-counter step, this circuit erases
its recorded branch bit. The physical input bits explicitly encode the
corresponding coefficient bits; the surrounding register layout must supply
these hypotheses. Every other physical bit and the phase are preserved. -/
theorem decode2_erase (flag a b output : Wire)
    (hf : flag ≠ output) (ha : a ≠ output) (hb : b ≠ output)
    (p : Int) (mathState : ECDSAAdd.Divsteps.ZState)
    (hinv : ECDSAAdd.Divsteps.Inv p mathState) (hp : p % 2 = 1)
    (hz : mathState.z < 0)
    (hdepth : padicValInt 2 (ECDSAAdd.Divsteps.zStep mathState).fv = 2)
    (s : State) (m : List Bool) (hflag : s.basis flag = true)
    (hleft : s.basis a = decide (ECDSAAdd.Divsteps.bitk
      (ECDSAAdd.Divsteps.zStep mathState).gv 1 = 1))
    (hright : s.basis b = decide (ECDSAAdd.Divsteps.bitk
      (ECDSAAdd.Divsteps.zStep mathState).fv 3 = 1))
    (hout : s.basis output = decide (ECDSAAdd.Divsteps.bbit mathState = 1)) :
    run (decode2 flag a b output) m s = ⟨s.phase, writeBit s.basis output false⟩ := by
  have hl : ECDSAAdd.Divsteps.bitk (ECDSAAdd.Divsteps.zStep mathState).gv 1 = 0 ∨
      ECDSAAdd.Divsteps.bitk (ECDSAAdd.Divsteps.zStep mathState).gv 1 = 1 := by
    unfold ECDSAAdd.Divsteps.bitk
    norm_num
    omega
  have hr : ECDSAAdd.Divsteps.bitk (ECDSAAdd.Divsteps.zStep mathState).fv 3 = 0 ∨
      ECDSAAdd.Divsteps.bitk (ECDSAAdd.Divsteps.zStep mathState).fv 3 = 1 := by
    unfold ECDSAAdd.Divsteps.bitk
    norm_num
    omega
  have law := ECDSAAdd.Divsteps.j2_law hinv hp hz hdepth
  rw [decode2_run flag a b output hf ha hb s m, hflag, hleft, hright, hout, law]
  rcases hl with hl | hl <;> rcases hr with hr | hr <;> simp [hl, hr]

/-- Two Toffolis, no measurements; this is a unitary decoder, not a
cost claim for the surrounding walk or controlled point adder. -/
theorem decode2_counts (flag a b output : Wire) :
    toffoliCount (decode2 flag a b output) = 2 ∧
    measurementCount (decode2 flag a b output) = 0 := by
  simp [decode2, toffoliCount, measurementCount]

theorem decode2_wires (flag a b output : Wire) :
    wires (decode2 flag a b output) = {flag, a, b, output} := by
  ext w
  simp [decode2, wires, Instr.wires]
  tauto

end ECDSAAdd.Arithmetic.Divsteps
