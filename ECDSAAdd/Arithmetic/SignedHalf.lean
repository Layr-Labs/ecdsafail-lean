import ECDSAAdd.Arithmetic.Registers
import ECDSAAdd.Arithmetic.Reduction

namespace ECDSAAdd.Arithmetic

/-- Once the even low bit is zero, its wire becomes the new sign extension
bit. The new little-endian view is the old high tail followed by that wire. -/
def skywalkHalfView (low : Wire) (tail : List Wire) : List Wire := tail ++ [low]

def skywalkSignedHalf (sign low : Wire) : Program := [.CX sign low]

theorem skywalkSignedHalf_correct (sign low : Wire) (_hsl : sign ≠ low)
    (s : State) (m : List Bool) (he : s.basis low = false) :
    run (skywalkSignedHalf sign low) m s =
      ⟨s.phase, writeBit s.basis low (s.basis sign)⟩ := by
  simp [skywalkSignedHalf, run, he]

theorem skywalkSignedHalf_value (sign low : Wire) (tail : List Wire)
    (hsl : sign ≠ low) (hlo : low ∉ tail)
    (s : State) (m : List Bool) (he : s.basis low = false) :
    regValue (skywalkHalfView low tail) (run (skywalkSignedHalf sign low) m s).basis =
      regValue tail s.basis + 2 ^ tail.length * (s.basis sign).toNat := by
  rw [skywalkSignedHalf_correct sign low hsl s m he]
  have ht : regValue tail (writeBit s.basis low (s.basis sign)) = regValue tail s.basis := by
    apply regValue_congr
    intro q hq
    have hn : q ≠ low := fun h => hlo (h ▸ hq)
    simp [writeBit, hn]
  change regValue (tail ++ [low]) (writeBit s.basis low (s.basis sign)) = _
  rw [regValue_append, ht]
  cases s.basis sign <;> simp [regValue, writeBit, Bool.toNat]

theorem skywalkSignedHalf_frame (sign low : Wire) (s : State) (m : List Bool) :
    (run (skywalkSignedHalf sign low) m s).phase = s.phase ∧
    (∀ q, q ≠ low → (run (skywalkSignedHalf sign low) m s).basis q = s.basis q) := by
  constructor
  · rfl
  · intro q hq
    simp [skywalkSignedHalf, run, writeBit, hq]

/-- Clearing the sign extension is the same CX before restoring the old view.
This is a genuine gate inverse, valid for every initial basis state. -/
theorem skywalkSignedHalf_twice (sign low : Wire) (hsl : sign ≠ low)
    (s : State) (m : List Bool) :
    run (skywalkSignedHalf sign low) m (run (skywalkSignedHalf sign low) m s) = s := by
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = low
  · subst q
    cases hs : s.basis sign <;> cases hl : s.basis low <;>
      simp [skywalkSignedHalf, run, writeBit, hsl, hs, hl]
  · simp [skywalkSignedHalf, run, writeBit, hq]

theorem skywalkSignedHalf_counts (sign low : Wire) :
    toffoliCount (skywalkSignedHalf sign low) = 0 ∧
    measurementCount (skywalkSignedHalf sign low) = 0 := by
  simp [skywalkSignedHalf, toffoliCount, measurementCount]

theorem skywalkSignedHalf_wires (sign low : Wire) :
    wires (skywalkSignedHalf sign low) = [sign, low].toFinset := by
  ext q
  simp [skywalkSignedHalf, wires, Instr.wires]

/-- Explicit sign-bit interpretation; connecting the actual most significant
bit to the canonical signed-word decoder is a separate layout obligation. -/
def signedHalfDecode (n : Nat) (sign : Bool) (raw : Nat) : Int :=
  (raw : Int) - if sign then (2 : Int) ^ n else 0

theorem signedHalfDecode_half (n X : Nat) (S : Bool) :
    signedHalfDecode (n + 1) S (X + 2 ^ n * S.toNat) =
      signedHalfDecode (n + 1) S (2 * X) / 2 := by
  cases S
  · simp [signedHalfDecode, Bool.toNat]
  · simp [signedHalfDecode, pow_succ]
    omega

end ECDSAAdd.Arithmetic
