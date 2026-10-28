import ECDSAAdd.Arithmetic.Divsteps.Decoder

namespace ECDSAAdd.Divsteps

/-- At every active reachable step, the low coefficient bit alone identifies
whether the step swapped. No excursion-depth restriction is needed. -/
theorem swap_bit_law (p : Int) (s : ZState) (h : Inv p s) (hp : p % 2 = 1) :
    decide (0 ≤ s.z ∧ s.g % 2 = 1) = decide (bitk (zStep s).fv 1 = 1) := by
  rw [decide_eq_decide, (sigma_class h hp).1]
  have heven := (h.zStep hp).fveven
  simp only [Int.ModEq, bitk]
  norm_num
  omega

end ECDSAAdd.Divsteps

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Controlled reconstruction of the swap choice from updated fv[1]. -/
def decodeSwap (active low output : Wire) : Program := [.CCX active low output]

theorem decodeSwap_run (active low output : Wire) (s : State) (m : List Bool) :
    run (decodeSwap active low output) m s =
      ⟨s.phase, writeBit s.basis output
        (s.basis output ^^ (s.basis active && s.basis low))⟩ := rfl

theorem decodeSwap_erase (active low output : Wire)
    (_ha : active ≠ output) (_hl : low ≠ output) (_hal : active ≠ low)
    (p : Int) (t : ECDSAAdd.Divsteps.ZState)
    (h : ECDSAAdd.Divsteps.Inv p t) (hp : p % 2 = 1)
    (s : State) (m : List Bool) (henable : s.basis active = true)
    (hbit : s.basis low = decide (ECDSAAdd.Divsteps.bitk
      (ECDSAAdd.Divsteps.zStep t).fv 1 = 1))
    (hout : s.basis output = decide (0 ≤ t.z ∧ t.g % 2 = 1)) :
    run (decodeSwap active low output) m s =
      ⟨s.phase, writeBit s.basis output false⟩ := by
  rw [decodeSwap_run, henable, hbit, hout, ECDSAAdd.Divsteps.swap_bit_law p t h hp]
  simp

theorem decodeSwap_resources (active low output : Wire) :
    toffoliCount (decodeSwap active low output) = 1 ∧
    measurementCount (decodeSwap active low output) = 0 ∧
    wires (decodeSwap active low output) = {active, low, output} := by
  simp [decodeSwap, toffoliCount, measurementCount, wires, Instr.wires]

end ECDSAAdd.Arithmetic.Divsteps
