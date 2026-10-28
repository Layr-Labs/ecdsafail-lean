import ECDSAAdd.Baselines.SlotMapped

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem signComplement_gateSlots (q : Wire) (xs : List Wire) :
    gateSlots (signComplement q xs) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [signComplement, List.map_cons, gateSlots_cons,
      instructionSlots, List.length_cons] at *; omega

theorem signedWord_gateSlots_le (q : Wire) (xs ys cs : List Wire) :
    gateSlots (signedAdd q xs ys cs) ≤ 14*xs.length ∧
    gateSlots (signedSub q xs ys cs) ≤ 14*xs.length+2*ys.length := by
  have h := addInPlace_gateSlots_le xs ys cs q
  simp only [signedAdd, signedSub, gateSlots_append, signComplement_gateSlots,
    notRegister_gateSlots]; omega

theorem signedRecord_gateSlots_le (sx sy q : Wire) (xs ys cs : List Wire) :
    gateSlots (signedRecord sx sy q xs ys cs) ≤ 14*xs.length+6 ∧
    gateSlots (signedUnrecord sx sy q xs ys cs) ≤ 14*xs.length+2*ys.length+6 := by
  have h := signedWord_gateSlots_le q xs ys cs
  simp only [signedRecord, signedUnrecord, skywalkSignToggle, gateSlots_append,
    gateSlots_cons, gateSlots_nil, instructionSlots]; omega

theorem narrowRecord_gateSlots_le (L : NarrowSignedRecordLayout) (n : Nat) :
    gateSlots (narrowSignedRecord L n) ≤ 14*L.x.length+L.y.length+6 ∧
    gateSlots (narrowSignedUnrecord L n) ≤ 14*L.x.length+3*L.y.length+6 := by
  have h := signedRecord_gateSlots_le L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1))
  simp only [List.length_take] at h
  simp only [narrowSignedRecord,narrowSignedUnrecord,gateSlots_append,
    signComplement_gateSlots,List.length_drop]
  omega

theorem narrowTick_gateSlots_le (L : SkywalkIntegerLayout) (n : Nat) :
    gateSlots (narrowSkywalkTick L n) ≤ 3*L.ah.length+14*L.half.length+3*L.b.length+26 ∧
    gateSlots (narrowSkywalkUntick L n) ≤ 3*L.ah.length+14*L.half.length+3*L.b.length+26 := by
  have h := narrowRecord_gateSlots_le (narrowSkywalkRecordLayout L n) n
  have hx : (narrowSkywalkRecordLayout L n).x.length ≤ L.half.length+1 := by
    simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.x,NarrowSignedRecordLayout.xp,
      List.length_append,List.length_take,List.length_drop,List.length_singleton]; omega
  have hy : (narrowSkywalkRecordLayout L n).y.length ≤ L.b.length+1 := by
    simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.y,NarrowSignedRecordLayout.yp,
      List.length_append,List.length_take,List.length_drop,List.length_singleton]; omega
  have hm := Nat.min_le_left L.ah.length L.bh.length
  simp only [narrowSkywalkTick,narrowSkywalkUntick,skywalkRoute,skywalkSignedHalf,
    gateSlots_append,swapRegisters_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

theorem compactTick_gateSlots_le (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    gateSlots (compactSkywalkTick w i) ≤ 6000 ∧
    gateSlots (compactSkywalkReverseTick w i) ≤ 6000 := by
  have h := narrowTick_gateSlots_le (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)
  have hb := compactSkywalkTick_width_bounds i hi
  rw [compactSkywalkTick_ah w i hi, compactSkywalkTick_half w i hi,
    compactSkywalkTick_b w i hi, wireBlock_length, wireBlock_length, wireBlock_length] at h
  have hc : gateSlots (compactSkywalkTickCleanup w i) ≤ 516 := by
    simp only [compactSkywalkTickCleanup,compactSkywalkTickARelease,compactSkywalkTickBRelease,
      compactSkywalkSignRelease,compactSkywalkSignWord,gateSlots_append,signComplement_gateSlots,
      List.length_drop,compactSkywalkTick_half w i hi,compactSkywalkTick_b w i hi,wireBlock_length]
    omega
  have he : gateSlots (compactSkywalkReverseExpand w i) = gateSlots (compactSkywalkTickCleanup w i) := by
    simp only [compactSkywalkReverseExpand,compactSkywalkTickCleanup,compactSkywalkSignExpand,
      compactSkywalkSignRelease,gateSlots_append,signComplement_gateSlots]; omega
  simp only [compactSkywalkTick,compactSkywalkReverseTick,gateSlots_append]
  omega

end ECDSAAdd.Baselines
