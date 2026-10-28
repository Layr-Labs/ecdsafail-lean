import ECDSAAdd.Arithmetic.InverseBothBackend
import ECDSAAdd.Arithmetic.InverseProductPhysical

namespace ECDSAAdd.Arithmetic.PointInverseEndpoint
open RecordedQuantum ControlledPointLayout

theorem both_physical (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (hp : PhysicalProgram (ep.program L))
    (multiply : Bool) : PhysicalProgram (ep.bothBackend.program L multiply) := by
  cases multiply with
  | false =>
      exact InverseQuotientRecorded.physical _ _ _ _ hp
        (L.quotient_nodup hw hn) (L.quotient_widths hw).1 (L.quotient_widths hw).2
  | true =>
      exact InverseProductRecorded.physical _ _ _ _ hp
        (L.quotient_nodup hw hn) (L.quotient_widths hw).1 (L.quotient_widths hw).2

/-- Either actual point arithmetic call has a coherent implementation once
its inverse endpoint does. Fixed point-add stages are not covered here. -/
theorem both_realize (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (hp : PhysicalProgram (ep.program L))
    (n : Nat) (hb : L.dialogUsedWires.toFinset ⊆ Finset.range n) (multiply : Bool) :
    ∃ l, ∃ c : Circuit n 0 l, c.program = ep.bothBackend.program L multiply := by
  apply RecordedQuantum.realize n 0 _ (ep.both_physical L hw hn hp multiply)
    (ep.bothBackend.wellFormed L hw hn multiply)
  exact (ep.bothBackend.support L hw hn multiply).trans hb

end ECDSAAdd.Arithmetic.PointInverseEndpoint
