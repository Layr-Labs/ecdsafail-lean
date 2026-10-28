import ECDSAAdd.Arithmetic.MaskedConstant
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The affine Clifford fan for two known words selected by a live sign.
Independent-target CX gates are grouped before the X gates. -/
def closerFan (sign : Wire) (payload : List Wire) (positive negative : Nat) : Program :=
  maskedConstant sign payload (positive ^^^ negative)++xorConstant payload positive

private theorem xor_proper (r : List Wire) (k : Nat) : ProperProgram (xorConstant r k) := by
  induction r generalizing k with
  | nil => simp [xorConstant,ProperProgram]
  | cons q r ih =>
    by_cases h : k%2=1
    · simp only [xorConstant,h,if_true,properProgram_append]
      exact ⟨by simp [ProperProgram,ProperGate],ih (k/2)⟩
    · simpa [xorConstant,h] using ih (k/2)

private theorem masked_proper (c : Wire) (r : List Wire) (k : Nat) (hc : c∉r) :
    ProperProgram (maskedConstant c r k) := by
  induction r generalizing k with
  | nil => simp [maskedConstant,ProperProgram]
  | cons q r ih =>
    have cq : c≠q := fun e => hc (by simp [e])
    have cr : c∉r := fun h => hc (by simp [h])
    by_cases h : k%2=1
    · simp only [maskedConstant,h,if_true,properProgram_append]
      exact ⟨by simpa [ProperProgram,ProperGate] using cq,ih (k/2) cr⟩
    · simpa [maskedConstant,h] using ih (k/2) cr

theorem closerFan_proper (sign : Wire) (payload : List Wire) (positive negative : Nat)
    (away : sign∉payload) : ProperProgram (closerFan sign payload positive negative) :=
  (properProgram_append _ _).mpr ⟨masked_proper _ _ _ away,xor_proper _ _⟩

theorem closerFan_counts (sign : Wire) (payload : List Wire) (positive negative : Nat) :
    toffoliCount (closerFan sign payload positive negative)=0 ∧
    measurementCount (closerFan sign payload positive negative)=0 := by
  simp only [closerFan,toffoliCount_append,measurementCount_append,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2,
    (xorConstant_counts _ _).1,(xorConstant_counts _ _).2,Nat.add_zero]
  trivial

/-- Both affine branches erase the actual payload, while preserving every
other bit and the phase. The sign remains available for the caller. -/
theorem closerFan_clear (sign : Wire) (payload : List Wire) (positive negative : Nat)
    (distinct : payload.Nodup) (away : sign∉payload)
    (hp : positive<2^payload.length) (hn : negative<2^payload.length)
    (s : State) (m : List Bool)
    (encoded : regValue payload s.basis=if s.basis sign then negative else positive) :
    let out := run (closerFan sign payload positive negative) m s
    out.phase=s.phase ∧ (∀ q∈payload,out.basis q=false) ∧
      ∀ q∉payload,out.basis q=s.basis q := by
  have first := maskedConstant_correct sign payload (positive ^^^ negative) distinct away
    (Nat.xor_lt_two_pow hp hn) s m
  let t := run (maskedConstant sign payload (positive ^^^ negative)) m s
  have second := xorConstant_correct payload distinct positive hp t m
  dsimp only
  rw [closerFan,run_append,run_take,(maskedConstant_counts _ _ _).2,List.drop_zero]
  refine ⟨second.1.trans first.1,?_,fun q hq => (second.2.1 q hq).trans (first.2.1 q hq)⟩
  apply (regValue_zero payload _).mp
  rw [second.2.2,first.2.2,encoded]
  cases s.basis sign <;> simp [Nat.xor_left_comm]

theorem closerFan_roundtrip (sign : Wire) (payload : List Wire) (positive negative : Nat)
    (away : sign∉payload) (s : State) (m n : List Bool) :
    run (closerFan sign payload positive negative).reverse n
      (run (closerFan sign payload positive negative) m s)=s :=
  run_reverse_proper _ (closerFan_proper sign payload positive negative away) s m n

end ECDSAAdd.Arithmetic.Paper935
