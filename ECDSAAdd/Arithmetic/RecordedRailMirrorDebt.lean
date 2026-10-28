import ECDSAAdd.Math.RecordedCarryWordMirror
import ECDSAAdd.Arithmetic.RecordedRailRippleResources

namespace ECDSAAdd.Arithmetic.RecordedRailRipple
open ECDSAAdd.Math.RecordedCarryWordMirror

/-- The actual ripple's saved-record debt is the weighted word of ordinary
binary prefix carries. Shape fixes the number of retained carry positions. -/
theorem phaseDebt_word (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) (bits : BasisState) (m : List Bool) (cin : Bool) :
    phaseDebt a b cin slots bits m=
      debt slots m (carryBits (a.map bits) (b.map bits) cin) := by
  induction shape generalizing cin with
  | one a b => rfl
  | two a0 a1 b0 b1 => rfl
  | step a0 a1 a2 b0 b1 b2 c as bs cs d ds shape ih =>
    cases d <;>
      simp only [phaseDebt,recordDebt,debt,List.map_cons,carryBits,
        Bool.false_xor,ih]

/-- The input phase obligation consumed by the mirror is exactly the original
forward debt. The map equalities are register facts to be supplied by the
forward gate proof, rather than an assumed phase cancellation. -/
theorem mirror_phaseDebt (a b work : List Wire) (slots : List (Option Nat))
    (shape : Shape a b work slots) (original mirror : BasisState)
    (m : List Bool) (cin : Bool)
    (source : a.map mirror=a.map original)
    (target : b.map mirror=(sumBits (a.map original) (b.map original) cin).map (!·)) :
    phaseDebt a b cin slots mirror m=phaseDebt a b cin slots original m := by
  rw [phaseDebt_word a b work slots shape mirror m cin,
    phaseDebt_word a b work slots shape original m cin,source,target,mirror_carries]

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.phaseDebt_word
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.mirror_phaseDebt
