import ECDSAAdd.Arithmetic.Paper935.FusedFailureEvents
import ECDSAAdd.Arithmetic.Paper935.ScalingSeed
import ECDSAAdd.Arithmetic.InverseBothFailure

namespace ECDSAAdd.Arithmetic.Paper935
open Secp256k1 PointInverseEndpoint
noncomputable section
local instance fusedPointDecidable : DecidableEq Point := Classical.decEq _

/-- circuit.py:128, :181, :190. These are row_mul sites, not the four
closed-XOR inverse adapter calls. The last site reverses the preceding scan. -/
inductive FusedCallSite
  | quotientApply | productRecompute | productErase
  deriving DecidableEq, Fintype

/-- engine.py:3254 and :3174. Parked coefficient and sign come from the
mathematical divstep trajectory on the original denominator. -/
def fusedCallFromWalk (d : Fp) (operand : Nat) : FusedCall :=
  let rows := (pinWalk 498 p (d.val : Int) 533).rows
  ⟨true,rows.fv,operand,xor (decide (rows.f<0)) (decide (rows.fv<0))⟩

/-- circuit.py:172–181. Walk-C scales its product operand before row_mul.
Reverse the existing reverse-order rider list to obtain forward stage order. -/
def fusedProductOperand (d a : Fp) : Nat :=
  ECDSAAdd.Arithmetic.Divsteps.halveActive p
    (authorRiderActivities p (d.val : Int)).reverse (d*a).val

/-- circuit.py:111–190. Original point labels determine both denominator
and the current mathematical operand. Disabled/nonordinary labels have no
modeled fused call; implementing that guard remains a physical obligation. -/
def fusedPointCall (C : Point) (site : FusedCallSite) (x : Bool × Point) : Option FusedCall :=
  match C with
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
    let X := ((coordinates x.2).getD (0,0)).1
    let Y := ((coordinates x.2).getD (0,0)).2
    if dialogOrdinary x.1 x.2 (.some hc) then
      match site with
      | .quotientApply => some (fusedCallFromWalk (X-cx) (Y-cy).val)
      | .productRecompute | .productErase =>
        let d := cx-genericX X Y cx cy
        some (fusedCallFromWalk d (fusedProductOperand d (genericSlope X Y cx cy)))
    else none

/-- circuit.py:128, :181, :190, in source order. The repeated s6 value
checks the same mathematical trajectory and does not create independence. -/
def fusedPointCalls (C : Point) (x : Bool × Point) : List FusedCall :=
  [FusedCallSite.quotientApply,.productRecompute,.productErase].filterMap
    (fun site => fusedPointCall C site x)

theorem fusedPointCall_erase (C : Point) (x : Bool × Point) :
    fusedPointCall C .productErase x=fusedPointCall C .productRecompute x := by
  cases C <;> rfl

theorem fusedPointCall_infinity (site : FusedCallSite) (x : Bool × Point) :
    fusedPointCall .zero site x=none := rfl

theorem fusedProductOperand_iterate (d a : Fp) :
    fusedProductOperand d a=(halveMod p)^[(authorRiderActivities p (d.val : Int)).count true] (d*a).val := by
  rw [fusedProductOperand,ECDSAAdd.Arithmetic.Divsteps.halveActive_eq,List.count_reverse]

/-- Events for the fused route live on the original control/point labels.
This does not bind any actual point-add program to those labels. -/
def fusedPointFailures [Fintype (Bool × Point)] (C : Point) : FusedFailures (Bool × Point) := by
  classical
  exact fusedFailures (fusedPointCalls C)

end
end ECDSAAdd.Arithmetic.Paper935
