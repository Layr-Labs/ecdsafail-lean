import ECDSAAdd.Arithmetic.BalancedFieldCircuitProof
import ECDSAAdd.Arithmetic.BalancedInverseComposeProof
import ECDSAAdd.Framework.GateInverse
import Mathlib.Tactic

set_option maxHeartbeats 100000
namespace ECDSAAdd.Entrant.DiagonalParity5
open Arithmetic BalancedCircuit BalancedField

theorem magnitude_sign (Y : Int) :
    (magnitude Y).toNat+(negative Y).toNat=Y.natAbs := by
  have cast := Int.natCast_natAbs Y
  by_cases neg : Y<0
  · have mag : magnitude Y= -Y-1 := by simp [magnitude,negative,neg]
    have nonneg := Int.toNat_of_nonneg (show 0≤ -Y-1 by omega)
    rw [abs_of_neg neg] at cast
    rw [mag]
    simp only [negative,neg,decide_true,Bool.toNat_true]
    omega
  · have mag : magnitude Y=Y := by simp [magnitude,negative,neg]
    have nonneg := Int.toNat_of_nonneg (show 0≤Y by omega)
    rw [abs_of_nonneg (by omega)] at cast
    rw [mag]
    simp only [negative,neg,decide_false,Bool.toNat_false,Nat.add_zero]
    omega

end ECDSAAdd.Entrant.DiagonalParity5

namespace ECDSAAdd.Entrant.EntryHalf5
open Arithmetic BalancedCircuit BalancedField

theorem target_nodup (L : Layout) (hn : L.wires.Nodup) : L.r.Nodup := by
  exact (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp (allND L hn)).2.1).1).1

theorem eraseAnd (a b t : Wire) (ha : a≠t) (hb : b≠t)
    (s : State) (m : List Bool) (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  cases hr : m.head?.getD false <;>
    simp [run,measureAndCorrect,correct,writeBit,ha,hb,ht,hr]

end ECDSAAdd.Entrant.EntryHalf5
