import ECDSAAdd.Arithmetic.PointMeasuredSquareCandidate

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Exact controlled streamed square subtraction with clean branch boundaries. -/
def pointDialogSquare (L : ControlledPointLayout) : Program := pointMeasuredSquareCandidate L

theorem pointDialogSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (pointDialogSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointDialogSquare L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (pointDialogSquare L) m s).basis q=s.basis q :=
  pointMeasuredSquareCandidate_correct L hw hn X Y B hX s m hb hx hy hc

end ECDSAAdd.Arithmetic
