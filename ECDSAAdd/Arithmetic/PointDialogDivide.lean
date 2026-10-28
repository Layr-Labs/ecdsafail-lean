import ECDSAAdd.Arithmetic.OffsetBorrowedControlledPort

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Exact Skywalk replacement with the original guarded divisor contract. -/
theorem pointDialog_arithmetic_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (pointOffsetBorrowedArithmetic L multiply) m s).phase=s.phase ∧
      regValue L.point.y (run (pointOffsetBorrowedArithmetic L multiply) m s).basis=V ∧
      ∀ q∉L.point.y,(run (pointOffsetBorrowedArithmetic L multiply) m s).basis q=s.basis q :=
  pointOffsetBorrowedArithmetic_correct L hw hn multiply X Y B hX hX0 hY s m hb hx hy hc

end ECDSAAdd.Arithmetic
