import ECDSAAdd.Arithmetic.PointArithmeticBackend
import ECDSAAdd.Framework.RecordedHoare

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- Closed recorded replacement arithmetic. Deferred phase debt must be paid
before returning; records are local and relocated by `recordedThen` at use. -/
structure RecordedPointArithmeticBackend where
  program : ControlledPointLayout → Bool → RecordedProgram
  correct : ∀ (L : ControlledPointLayout), L.Widths → L.wires.Nodup →
    ∀ (multiply : Bool) (X Y : Nat) (B : Bool), X<p → (B=true → X≠0) → Y<p →
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

namespace RecordedPointArithmeticBackend

/-- Existing ordinary providers lift without changing their emitted gates,
measurement counts or quantum support. -/
def embed (backend : PointArithmeticBackend) : RecordedPointArithmeticBackend where
  program L multiply := embedRecorded (backend.program L multiply)
  correct L hw hn multiply X Y B hx hx0 hy s m hb hX hY hz := by
    simpa only [runWithTape_embedRecorded,List.drop_zero] using
      backend.correct L hw hn multiply X Y B hx hx0 hy s m hb hX hY hz
  support L hw hn multiply := by
    simpa only [embedRecorded_wires] using backend.support L hw hn multiply
  wellFormed L _ _ multiply := embedRecorded_wellFormed _ 0

end RecordedPointArithmeticBackend
end ECDSAAdd.Arithmetic
