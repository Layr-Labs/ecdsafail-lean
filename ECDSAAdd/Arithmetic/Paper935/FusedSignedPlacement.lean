import ECDSAAdd.Arithmetic.Paper935.FusedPlacementViews

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

private theorem value_map (xs : List Wire) (f : Wire → Wire) (s : BasisState) :
    regValue (xs.map f) s = regValue xs (fun q => s (f q)) := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    change (if s (f q) then 1 else 0)+2*regValue (qs.map f) s =
      (if s (f q) then 1 else 0)+2*regValue qs (fun q => s (f q))
    rw [ih]

/-- A physical signed row supplies the lift encoding, including its sign bit. -/
theorem placedMagnitude_encoding (r : WindowRow) (pool : List Wire)
    (s : BasisState) (z : Int) (len : r.payload.length=280)
    (encoded : r.value s=z) :
    MagnitudeEncodes z (fun q => s (fusedPlacementMap (r.sign::r.payload++pool) q)) := by
  have sign := signedRegValue_sign r.payload r.sign s
  change s r.sign=SkywalkRails.neg (r.value s) at sign
  rw [encoded] at sign
  have val := signedRegValue_msb r.payload r.sign s
  change r.value s = _ at val
  rw [encoded,regValue_append] at val
  have single : regValue [r.sign] s = if s r.sign then 1 else 0 := by simp [regValue]
  rw [single,len] at val
  have payload : regValue magnitudePayload
      (fun q => s (fusedPlacementMap (r.sign::r.payload++pool) q)) =
      regValue r.payload s := by
    rw [←value_map,fusedLiftPlacement_payload r.sign r.payload pool len]
  unfold MagnitudeEncodes
  constructor
  · simpa [fusedPlacementMap,SkywalkRails.neg] using sign
  · rw [payload]
    by_cases hz : z<0
    · have hs : s r.sign=true := by simpa [SkywalkRails.neg,hz] using sign
      simp only [hs, ite_true, Nat.mul_one, Nat.cast_add] at val
      rw [if_pos hz]
      have habs := Int.ofNat_natAbs_of_nonpos (le_of_lt hz)
      omega
    · have hs : s r.sign=false := by simpa [SkywalkRails.neg,hz] using sign
      simp only [hs, Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero, sub_zero] at val
      rw [if_neg hz]
      have habs := Int.ofNat_natAbs_of_nonneg (le_of_not_gt hz)
      omega

/-- The physical signed-row invariant suffices for the actual lift-to-fold call. -/
theorem placedSignedLift_fold_encoding (A B : Arena) (r : WindowRow)
    (word pool : List Wire) (len : r.payload.length=280)
    (distinct : (r.sign::r.payload).Nodup)
    (owned : (r.sign::r.payload).toFinset⊆A.live)
    (allocated : A.borrowMany 24=some (B,pool)) (call : FusedCall)
    (s : State) (m : List Bool) (ready : A.Ready s.basis)
    (encoded : r.value s.basis=call.coefficient) (good : call.LiftGood) :
    regValue ((fusedFoldLow++fusedFoldHigh).map
      (fusedPlacementMap (fusedFoldPlacement r.payload word pool)))
      (run (placedMagnitude (fusedPlacementMap (r.sign::r.payload++pool)) false) m s).basis =
      call.coefficient.natAbs :=
  placedLift_fold_encoding A B r.payload word pool r.sign len distinct owned allocated
    call s m ready (placedMagnitude_encoding r pool s.basis call.coefficient len encoded) good

end ECDSAAdd.Arithmetic.Paper935
