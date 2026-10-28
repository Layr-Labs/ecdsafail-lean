import ECDSAAdd.Baselines.NormalizedEntries

namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1 MappedCompressed

/-- Cache a bounded prefix, retaining the original function outside it. -/
def cachedWireFn (f : Nat → Nat) (n : Nat) : Nat → Nat :=
  let table := Array.ofFn (fun i : Fin n => f i)
  fun i => if h : i < n then table[i]'(by simpa [table] using h) else f i

theorem cachedWireFn_eq (f : Nat → Nat) (n : Nat) : cachedWireFn f n = f := by
  funext i
  simp [cachedWireFn]

def cachedArithmetic (L : ControlledPointLayout) (multiply : Bool) : Program :=
  renameProgram (cachedWireFn (pointWireFn L) 2430) (controlled (!multiply))

theorem cachedArithmetic_eq (L : ControlledPointLayout) (multiply : Bool) :
    cachedArithmetic L multiply = pointCompressedArithmetic L multiply := by
  rw [cachedArithmetic, cachedWireFn_eq]
  rfl

def cachedGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  cachedArithmetic L false ++
  CompressedPointSquare.computableProgram L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++
  cachedArithmetic L true ++
  pointRecoveryStage L cx cy

def cachedFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)) ++
  pointDialogGenericFlag L ++ cachedGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)) ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy


theorem cachedGeneric_eq (L : ControlledPointLayout) (cx cy : Fp) :
    cachedGeneric L cx cy = pointCompressedDialogGeneric L cx cy := by
  simp only [cachedGeneric, cachedArithmetic_eq, pointCompressedDialogGeneric]

theorem cachedFinite_eq (L : ControlledPointLayout) (C : Point) (cx cy : Fp) :
    cachedFinite L C cx cy = pointCompressedDialogFinite L C cx cy := by
  simp only [cachedFinite, cachedGeneric_eq, pointCompressedDialogFinite]

theorem cachedGenerator_eq :
    cachedFinite layout G (generatorX : Fp) (generatorY : Fp) = skywalk G := by
  rw [cachedFinite_eq]
  rfl

end ECDSAAdd.Baselines
