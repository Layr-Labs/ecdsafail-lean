import ECDSAAdd.Arithmetic.PointRecoveryOperations

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def pointDialogConstantAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  pointRecoveryConstantAdd L r k

/-- Narrow exact canonical constant addition; phase and every non-target
site, including source/control/shared scratch, return for all records. -/
theorem pointDialogConstantAdd_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (Z : Nat) (B : Bool) (hZ : Z<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hz : regValue r s.basis=Z)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointDialogConstantAdd L r k) m s).phase=s.phase ∧
      regValue r (run (pointDialogConstantAdd L r k) m s).basis=(Z+(if B then k.val else 0))%p ∧
      ∀ q∉r,(run (pointDialogConstantAdd L r k) m s).basis q=s.basis q :=
  pointRecoveryConstantAdd_correct L hw hnd r hr k Z B hZ s m hb hz hc

end ECDSAAdd.Arithmetic
