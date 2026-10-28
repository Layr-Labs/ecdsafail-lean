import ECDSAAdd.Arithmetic.MeasuredStreamedBranches

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def measuredCompleteResult (enabled : Bool) (A B O : Nat) : Nat :=
  SquareReduction.p-1-measuredCMiddleResult ((if enabled then A+B else 0)^2)
    (measuredBResult ((if enabled then B else 0)^2) (measuredAResult ((if enabled then A else 0)^2) O))

theorem measuredCompleteResult_lt (enabled : Bool) (A B O : Nat) :
    measuredCompleteResult enabled A B O<SquareReduction.p := by
  have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  dsimp [measuredCompleteResult]
  omega

theorem measuredCompleteResult_exact (enabled : Bool) (A B O : Nat) :
    measuredCompleteResult enabled A B O=
      subModValue (if enabled then (A+2^128*B)^2 else 0) O := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := measuredAResult PA O
  let OB := measuredBResult PB OA
  let OC := measuredCMiddleResult PC OB
  have ea := measuredAResult_cast PA O
  have eb := measuredBResult_cast PB OA
  have ec := measuredCMiddleResult_cast PC OB
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have ocBound : OC<SquareReduction.p := (measured_results_lt PC OB).2.2
  have cast : (measuredCompleteResult enabled A B O : ZMod SquareReduction.p)=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    change ((SquareReduction.p-1-OC : Nat) : ZMod SquareReduction.p)=_
    rw [measuredReflection_zmod OC ocBound,subModValue_cast]
    linear_combination ea+eb+ec+identity
  have targetBound : subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt (measuredCompleteResult_lt enabled A B O),ZMod.val_natCast_of_lt targetBound] using value

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
