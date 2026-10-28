import ECDSAAdd.Arithmetic.RecordedPointArithmeticBackend
import ECDSAAdd.Framework.RecordedHoare

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- Closed recorded replacement arithmetic. Deferred phase debt must be paid
before returning; records are local and relocated by `recordedThen` at use. -/
structure ConditionalPointArithmeticBackend where
  program : ControlledPointLayout → Bool → RecordedProgram
  /-- Success condition on mathematical operands, independent of the tape. -/
  safe : Bool → Fp → Fp → Bool → Prop
  correct : ∀ (L : ControlledPointLayout), L.Widths → L.wires.Nodup →
    ∀ (multiply : Bool) (X Y : Nat) (B : Bool), X<p → (B=true → X≠0) → Y<p →
    safe multiply (X : Fp) (Y : Fp) B →
    ∀ (s : State) (m : List Bool), s.basis L.core.generic=B →
    regValue L.point.x s.basis=X → regValue L.point.y s.basis=Y →
    regValue L.dialogPool s.basis=0 →
    (runWithTape (program L multiply) m 0 s).phase=s.phase ∧
    regValue L.point.y (runWithTape (program L multiply) m 0 s).basis=
      (if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y) ∧
    ∀ q,q∉L.point.y → (runWithTape (program L multiply) m 0 s).basis q=s.basis q
  support : ∀ (L : ControlledPointLayout), L.Widths → L.wires.Nodup →
    ∀ multiply, recordedWires (program L multiply) ⊆ L.dialogUsedWires.toFinset

  wellFormed : ∀ (L : ControlledPointLayout), L.Widths → L.wires.Nodup →
    ∀ multiply, RecordedWellFormedAt 0 (program L multiply)

namespace ConditionalPointArithmeticBackend

/-- Existing exact providers are a special case, with no exceptional operands. -/
def ofExact (backend : RecordedPointArithmeticBackend) : ConditionalPointArithmeticBackend where
  program := backend.program
  safe := fun _ _ _ _ => True
  correct L hw hn multiply X Y B hx hx0 hy _ :=
    backend.correct L hw hn multiply X Y B hx hx0 hy
  support := backend.support
  wellFormed := backend.wellFormed

end ConditionalPointArithmeticBackend
end ECDSAAdd.Arithmetic
